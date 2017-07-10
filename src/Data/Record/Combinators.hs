{-# LANGUAGE PackageImports #-}
-- |Record combinators built on top of the record core that "Data.Record" provides.

module Data.Record.Combinators (

    -- * Record styles
    withStyle,

    -- * Field operations
    (!!!),
    (\\\),

    -- * Catenation
    Cat,
    cat,

    -- * Applicative functor operations
    repeat,
    (<<*>>),
    map,
    zipWith,

    -- * Modification of fields
    {-FIXME:
        Actually, all applicative functor operations except repeat are also about modification of
        fields.
    -}
    modify,
    (///),

    -- * Conversion
    -- FIXME: maybe don’t use the term “conversion” because of “record conversion”
    toList

) where

    -- Prelude
    import           Prelude hiding (repeat, map, zipWith)
    import qualified Prelude -- only for documentation

    -- Data
    import "kinds" Data.Kind    as Kind
    import Data.TypeFun as TypeFun
    import Data.Record  as Record

    -- Control
    import Control.Applicative as Applicative hiding (Const) -- only for documentation

    -- * Record styles
    infixl 2 `withStyle`

    --FIXME: There is punctuation missing at the end of certain code blocks.
    {-|
        Fixes the style of a record. When a record is constructed using @X@, @(:&)@, and @(:=)@,
        the style of this record is not fixed. For example, the most general type of the record

@
X :& Surname := \"Jeltsch\" :& Age := 33 :& Room := \"HG/2.39\"
@

        is

@
('App' style sortSurname ~ String, Num ('App' style sortAge), 'App' style sortRoom ~ String) =>
(X :& Surname ::: sortSurname :& Age ::: sortAge :& Room ::: sortRoom) style
@

        We can fix the style of that record using the expression

@
X :& Surname := \"Jeltsch\" :& Age := 33 :& Room := \"HG/2.39\" \`withStyle\` 'Id' 'KindStar'
@

        which has the most general type

@
(Num age) =>
(X :& Surname ::: String :& Age ::: age :& Room ::: String) ('Id' 'KindStar')
@

        The @withStyle@ combinator is similar to 'asTypeOf'.
    -}
    withStyle :: (Record (Domain style) rec) => rec style -> style -> rec style
    withStyle = const

    -- * Field operations
    infixl 2 !!!, \\\

    -- |Looks up the value of a record field.
    (!!!) :: (Separation rec remain sepName sepSort) => rec style -> sepName -> App style sepSort
    rec !!! name = let

                       _ := sepVal = snd (separate rec) `asTypeOf` (name := undefined)

                   in sepVal

    -- |Removes a record field.
    (\\\) :: (Separation rec remain sepName sepSort) => rec style -> sepName -> remain style
    rec \\\ name = let

                       (remain,_) = separate rec `asTypeOf` (undefined,name := undefined)

                   in remain

    -- * Catenation
    -- |Catenation of two record schemes.
    type family   Cat (rec1 :: * -> *) (rec2 :: * -> *)          :: * -> *
    type instance Cat rec1             X                         =  rec1
    type instance Cat rec1             (rec2 :& name2 ::: sort2) =  Cat rec1 rec2 :& name2 ::: sort2

    -- |Catenation of two records.
    cat :: (TypeFun style, Record (Domain style) rec1, Record (Domain style) rec2)
        => rec1 style
           -- ^
        -> rec2 style
           -- ^
        -> Cat rec1 rec2 style
           -- ^
    cat = let

              CatThing cat = fold catNilAlt catExpander

          in cat

    newtype CatThing style rec1 rec2 = CatThing (rec1 style -> rec2 style -> Cat rec1 rec2 style)

    catNilAlt:: (TypeFun style, Record (Domain style) rec1) => CatThing style rec1 X
    catNilAlt = CatThing nilCat where

        nilCat rec1 X = rec1

    catSnocAlt :: (TypeFun style, Record (Domain style) rec1,
                   Record (Domain style) rec2, Name name, Inhabitant (Domain style) sort) =>
                  CatThing style rec1 rec2 -> CatThing style rec1 (rec2 :& name ::: sort)
    catSnocAlt (CatThing cat) = CatThing snocCat where

        snocCat rec1 (rec2 :& field2) = cat rec1 rec2 :& field2

    catExpander :: (TypeFun style, Record (Domain style) rec1,
                    Record (Domain style) rec2, Name name) =>
                   All (Domain style) (Expander (CatThing style rec1) rec2 name)
    catExpander = closed (Expander catSnocAlt)

    -- * Record schemes as a kind of applicative functor
    {-|
        Generates a record whose fields all contain the same value. In contrast to the
        'Prelude.repeat' function from the Prelude, this function generates a finite data structure.
        Thereby, the size of the generated record is determined by its type. @repeat@ is almost a
        proper implementation of 'pure' from the 'Applicative' class.
    -}
    repeat :: (TypeFun style, Record (Domain style) rec)
           => Universal style
              -- ^
           -> rec style
              -- ^
    repeat = let

                 RepeatThing repeat = fold repeatNilAlt repeatExpander

             in repeat

    newtype RepeatThing style rec = RepeatThing (Universal style -> rec style)

    repeatNilAlt :: (TypeFun style) => RepeatThing style X
    repeatNilAlt = RepeatThing nilRepeat where

        nilRepeat :: Universal style -> X style
        nilRepeat _ = X

    repeatSnocAlt :: forall style rec name sort. (TypeFun style,
                                                  Record (Domain style) rec,
                                                  Name name,
                                                  Inhabitant (Domain style) sort) =>
                     RepeatThing style rec -> RepeatThing style (rec :& name ::: sort)
    repeatSnocAlt (RepeatThing repeat) = RepeatThing snocRepeat where

        snocRepeat :: Universal style -> (rec :& name ::: sort) style
        snocRepeat wrappedVal = repeat wrappedVal :&
                                name := unwrapApp (wrappedVal :: WrappedApp style sort)

    repeatExpander :: (TypeFun style, Record (Domain style) rec, Name name) =>
                      All (Domain style) (Expander (RepeatThing style) rec name)
    repeatExpander = closed (Expander repeatSnocAlt)

    zipWithApp :: (TypeFun style, TypeFun style', Domain style ~ Domain style',
                  Record (Domain (style :-> style')) rec) =>
                  rec (style :-> style') -> rec style -> rec style'
    zipWithApp = let

                     ZipWithAppThing zipWithApp = fold zipWithAppNilAlt zipWithAppExpander

                 in zipWithApp

    newtype ZipWithAppThing style style' rec = ZipWithAppThing (rec (style :-> style') ->
                                                                rec style              ->
                                                                rec style')

    zipWithAppNilAlt :: (TypeFun style, TypeFun style', Domain style ~ Domain style') =>
                        ZipWithAppThing style style' X
    zipWithAppNilAlt = ZipWithAppThing nilZipWithApp where

        nilZipWithApp X X = X

    zipWithAppSnocAlt :: (TypeFun style, TypeFun style', Domain style ~ Domain style',
                          Record (Domain (style :-> style')) rec,
                          Name name,
                          Inhabitant (Domain style) sort) =>
                         ZipWithAppThing style style' rec ->
                         ZipWithAppThing style style' (rec :& name ::: sort)
    zipWithAppSnocAlt (ZipWithAppThing zipWithApp) = ZipWithAppThing snocZipWithApp where

        snocZipWithApp (funRec :& name := fun)
                       (argRec :& _    := arg) = zipWithApp funRec argRec :& name := fun arg

    zipWithAppExpander :: (TypeFun style, TypeFun style', Domain style ~ Domain style',
                           Record (Domain (style :-> style')) rec, Name name) =>
                           All (Domain style) (Expander (ZipWithAppThing style style') rec name)
    zipWithAppExpander = closed (Expander zipWithAppSnocAlt)

    infixl 4 <<*>>
    {-|
        Merges a record of functions and a record of arguments by applying the functions to the
        corresponding arguments. The @(\<\<*\>\>)@&#xA0;function is almost a proper implementation
        of&#xA0;@(\<*\>)@ from the 'Applicative' class.
    -}
    (<<*>>) :: (TypeFun style, TypeFun style', Domain style ~ Domain style',
                Record (Domain (style :-> style')) rec)
            => rec (style :-> style')
               -- ^
            -> rec style
               -- ^
            -> rec style'
               -- ^
    (<<*>>) = zipWithApp

    -- ** Derived combinators
    -- |Transforms a record by applying a function to all its field values.
    map :: (TypeFun style, TypeFun style', Domain style ~ Domain style',
            Record (Domain (style :-> style')) rec)
        => Universal (style :-> style')
           -- ^
        -> rec style
           -- ^
        -> rec style'
           -- ^
    map fun argRec = repeat fun <<*>> argRec

    -- |Merges two records by applying a function to each pair of corresponding field values.
    zipWith :: (TypeFun style1, TypeFun style2, TypeFun style',
                Domain style1 ~ Domain style2, Domain style2 ~ Domain style',
                Record (Domain (style1 :-> style2 :-> style')) rec)
            => Universal (style1 :-> style2 :-> style')
               -- ^
            -> rec style1
               -- ^
            -> rec style2
               -- ^
            -> rec style'
               -- ^
    zipWith fun argRec1 argRec2 = repeat fun <<*>> argRec1 <<*>> argRec2

    -- * Modification of multiple fields
    infixl 1 ///

    {-|
        Modifies a record by changing some of its field values. The first argument of @modify@ is
        called the modification record, and the second argument is called the data record. The
        result is formed by applying each field value of the modification record to the
        corresponding field value of the data record and replacing the latter by the result of the
        application. Data record fields that have no corresponding field in the modification record
        are left unchanged.
    -}
    modify :: (TypeFun style,
               Record (Domain style) rec,
               Record (Domain style) modRec,
               Convertible rec modRec)
           => modRec (style :-> style)
              -- ^
           -> rec style
              -- ^
           -> rec style
              -- ^
    modify modRec = foldr (.) id $ toList (convert updateFuns <<*>> modRec)

    type UpdateFunStyle rec style = (style :-> style)                             :->
                                    Const (Domain style) (rec style -> rec style)

    updateFuns :: (TypeFun style, Record (Domain style) rec) => rec (UpdateFunStyle rec style)
    updateFuns = let

                     UpdateFunsThing updateFuns = fold updateFunsNilAlt updateFunsExpander

                 in updateFuns

    newtype UpdateFunsThing style rec = UpdateFunsThing (rec (UpdateFunStyle rec style))

    updateFunsNilAlt :: (TypeFun style) => UpdateFunsThing style X
    updateFunsNilAlt = UpdateFunsThing nilUpdateFuns where

        nilUpdateFuns = X

    updateFunsSnocAlt :: (TypeFun style,
                          Record (Domain style) rec, Name name, Inhabitant (Domain style) sort) =>
                         UpdateFunsThing style rec ->
                         UpdateFunsThing style (rec :& name ::: sort)
    updateFunsSnocAlt (UpdateFunsThing updateFuns) = UpdateFunsThing snocUpdateFuns where

        snocUpdateFuns                     = map (WrapApp (onInit .)) updateFuns :&
                                             name := updateFun

        updateFun mod (rec :& name := val) = rec :& name := mod val

    updateFunsExpander :: (TypeFun style, Record (Domain style) rec, Name name) =>
                          All (Domain style) (Expander (UpdateFunsThing style) rec name)
    updateFunsExpander = closed (Expander updateFunsSnocAlt)

    onInit :: (rec                    style -> rec                    style) ->
              ((rec :& name ::: sort) style -> (rec :& name ::: sort) style)
    onInit fun (rec :& field) = fun rec :& field

    {-|
        Overwrites the values of multiple record fields. The first argument is the source record,
        and the second argument lists the names of the fields to be modified together with their new
        values.
    -}
    (///) :: (TypeFun style,
              Record (Domain style) rec,
              Record (Domain style) replRec,
              Convertible rec replRec)
          => rec style
             -- ^
          -> replRec style
             -- ^
          -> rec style
             -- ^
    rec /// replRec = modify (map (WrapApp const) replRec) rec

    -- * Conversion
    -- |Converts a record whose style is a constant function into the list of its field values.
    toList :: (Kind kind, Record kind rec) => rec (Const kind val) -> [val]
    toList = reverse . toRevList

    toRevList :: (Kind kind, Record kind rec) => rec (Const kind val) -> [val]
    toRevList = let

                    ToRevListThing toRevList = fold toRevListNilAlt toRevListExpander

                in toRevList

    newtype ToRevListThing kind val rec = ToRevListThing (rec (Const kind val) -> [val])

    toRevListNilAlt :: (Kind kind) => ToRevListThing kind val X
    toRevListNilAlt = ToRevListThing nilToRevList where

        nilToRevList X = []

    toRevListSnocAlt :: (Kind kind, Record kind rec, Name name, Inhabitant kind sort) =>
                        ToRevListThing kind val rec ->
                        ToRevListThing kind val (rec :& name ::: sort)
    toRevListSnocAlt (ToRevListThing toRevList) = ToRevListThing snocToRevList where

        snocToRevList (rec :& _ := val) = val : toRevList rec

    toRevListExpander :: (Kind kind, Record kind rec, Name name) =>
                         All kind (Expander (ToRevListThing kind val) rec name)
    toRevListExpander = closed (Expander toRevListSnocAlt)
