-- |Record core support.
module Data.Record (

    -- * Record basics
    -- $RecordBasics
    X        (X),
    (:&)     ((:&)),
    (:::)    ((:=)),
    Name     (name),
    Record   (fold),
    Expander (Expander),

    -- * Record conversion
    -- $RecordConversion
    Convertible (convert),

    -- * Field separation
    Separation (separate)

) where

    import Data.Kind    as Kind
    import Data.TypeFun as TypeFun

    -- * Record basics
    infixl 2 :&
    infix  3 :::, :=

    {-$RecordBasics
        A record is a list of name-value pairs. Such pairs are called fields and are constructed
        using the data constructor&#xA0;@(:=)@. Records are built from fields using the data
        constructors&#xA0;@X@ (for the empty record) and&#xA0;@(:&)@ (for non-empty records that
        consist of an initial record and a last field each). For example, the following expression
        denotes a record that contains some information about the author of these lines:

@
X :& Surname := \"Jeltsch\" :& Age := 33 :& Room := \"HG/2.39\"
@

        The type of a record has the form @/r/ /s/@ where @/r/@&#xA0;is a record scheme and
        @/s/@&#xA0;is a representation of a type-level function, called the record style. A record
        scheme is a list of name-sort pairs, which correspond to the name-value pairs of the record.
        The type constructors @X@&#xA0;and&#xA0;@(:&)@ are used to form record schemes. Name-sort
        pairs are constructed using the type constructor&#xA0;@(:::)@.

        The name of a name-sort pair equals the name of the corresponding record field. Applying the
        style to the sort yields the type of the corresponding field value. For example, the above
        record has the following type:

@
(X :& Surname ::: String :& Age ::: Int :& Room ::: String) ('Id' 'KindStar')
@

        If we replace the type @Id KindStar@ by @Id KindStar :-> Id KindStar@, we get a type that
        covers all records with a @Surname@, an @Age@, and a @Room@ field that contain values of
        type @String -> String@, @Int -> Int@, and @String -> String@, respectively. So by varying
        the style, we can generate a family of related record types from a single record scheme.
    -}

    -- |The empty record scheme.
    data X style = X
                   -- ^The empty record.
         deriving (Show)

    {-|
        Non-empty record schemes.
    -}
    data (rec :& field)  style = !(rec style) :& !(field style)
                                 -- ^Non-empty records.

    {-
        We use an explicit instance declaration to avoid parantheses around the first arguments of
        (:&). Our instance declaration will lead to missing parantheses if a first argument of (:&)
        is an application of an operator that has the same fixity as :& and is right- or
        non-associative.
    -}
    instance (Show (rec style), Show name, Show (App style sort)) =>
             Show ((rec :& name ::: sort) style) where

        showsPrec enclPrec (rec :& field) = showParen (enclPrec > snocPrec) $
                                            showsPrec snocPrec rec          .
                                            showString " :& "               .
                                            showsPrec (succ snocPrec) field where

            snocPrec = 2

    -- |The type of record fields.
    data (name ::: sort) style = !name := App style sort
                                 -- ^Constructs a record field from a name and a value.

    {-
        We use an explicit instance declaration because the use of the type synonym family App
        makes deriving (currently) impossible.
    -}
    instance (Show name, Show (App style sort)) => Show ((name ::: sort) style) where

        showsPrec enclPrec (name := val) = showParen (enclPrec > assignPrec) $
                                           showsPrec (succ assignPrec) name .
                                           showString " := "                .
                                           showsPrec (succ assignPrec) val where

            assignPrec = 3

    {-|
        The class of name types. For each field name&#xA0;@/N/@, there should be a declaration of
        the following form:

@
data /N/ = /N/ deriving (Show)
@

        That way, the name can be represented in types by the type constructor&#xA0;@/N/@, and in
        expressions and patterns by the data constructor&#xA0;@/N/@. Furthermore, the following
        instance declaration should be added:

@
instance Name /N/ where
&#xA0;
    name = /N/
@

        Such instance declarations allow record combinators to construct value-level representations
        of names from type-level representations.
    -}
    class Name name where

        -- |The sole inhabitant of the name type.
        name :: name

    {-|
        An instance @Record /k/ /r/@ exists if and only if @/r/@&#xA0;is a record scheme whose sorts
        are of the subkind represented by&#xA0;@/k/@.
    -}
    class (Kind kind) => Record kind rec where

        {-|
            Folding of record schemes. This function can be used to define combinators whose types
            have the form @(Record rec) => /t/ rec@ by induction on the @rec@ parameter.
        -}
        fold :: thing X
                -- ^ the definition of the combinator for the empty record scheme
             -> (forall rec name. (Record kind rec, Name name) =>
                                  All kind (Expander thing rec name))
                {-^
                    turns the definition of the combinator for a record scheme&#xA0;@/r/@ into the
                    definition for any record scheme @/r/ :& /n/ ::: /s/@
                -}
             -> thing rec
                -- ^ the resulting combinator that works for all record schemes

    {-|
        Transformations from the definition of a record combinator for some record scheme into its
        definition for an expanded record scheme.
    -}
    newtype Expander thing rec name sort = Expander (thing rec -> thing (rec :& name ::: sort))

    instance (Kind kind) => Record kind X where

        fold nilAlt _ = nilAlt

    instance (Record kind rec, Name name, Inhabitant kind sort) =>
             Record kind (rec :& name ::: sort) where

        fold nilAlt expander = let

                                   Expander snocAlt = specialize expander

                               in snocAlt (fold nilAlt expander)

    -- * Record conversion
    {-$RecordConversion
        Records are lists, so their fields are totally ordered. This order can be used to
        distinguish fields that have the same name. For each name, we index the fields of this name
        from right to left. We identify a field by its name and its index. However, the order of
        fields with different names is superfluous. Therefore, it is worthwhile that it can be
        modified. Furthermore, it is often beneficial if unnecessary fields can be ignored. That
        way, record operations can be made more general since they can also work with records that
        contain more than the expected fields.

        Record conversion reorders and drops fields in such a way that all remaining fields keep
        their identification. So record conversion keeps the order of fields that share a common
        name, and it drops a field only if all preceding fields of the same name are also dropped.
        The scheme of the destination record is generated from the scheme of the source record by
        applying the same reorderings and droppings that are used to transform the source record
        into the destination record. The style is not changed.
    -}

    -- NOTE: Convertible does not ensure that all names in the source record are instances of Name.
    {-|
        An instance @Convertible /r/ /r'/@ exists if and only if @/r/@&#xA0;and&#xA0;@/r'/@ are
        record schemes, and records of a type @/r/ /s/@ can be converted into records of the type
        @/r'/ /s/@.
    -}
    class Convertible rec rec' where

        -- |Converts a record into another record.
        convert :: rec style -> rec' style

    instance Convertible rec X where

        convert _ = X

    instance (Separation rec remain name' sort', Convertible remain rec') =>
             Convertible rec (rec' :& name' ::: sort') where

        convert rec = convert remain :& field' where

            (remain,field') = separate rec

    -- * Field separation
    -- NOTE: Separate does not ensure that all names in the source record are instances of Name.
    {-|
        An instance @Separation /r/ /r'/ /n/ /s/@ exists if and only if the following conditions are
        met:

        * @/r/@&#xA0;is a record scheme that contains the name&#xA0;@/n/@.

        * The last name-sort pair with the name&#xA0;@/n/@ contains the sort&#xA0;@/s/@.

        * Removing that name-sort pair from&#xA0;@/r/@ yields&#xA0;@/r'/@.
    -}
    class (Name sepName) =>
          Separation rec remain sepName sepSort | rec sepName -> remain sepSort where

        {-|
            Extracts the last field of the respective name and returns the remaining record and the
            extracted field.
        -}
        separate :: rec style -> (remain style,(sepName ::: sepSort) style)

    instance (Name name, sort ~ sepSort) =>
             Separation (rec :& name ::: sort) rec name sepSort where

        separate (rec :& field) = (rec,field)

    instance (Separation rec remain sepName sepSort, (remain :& name ::: sort) ~ extRemain) =>
             Separation (rec :& name ::: sort) extRemain sepName sepSort where

        separate (rec :& field) = (remain :& field,sepField) where

            (remain,sepField) = separate rec
