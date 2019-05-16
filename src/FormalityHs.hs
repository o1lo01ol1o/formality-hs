{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
module FormalityHs where


import           Data.Aeson
import           Data.Aeson.Types               ( emptyArray )

import           Data.Text                      ( Text
                                                , pack
                                                )
import qualified Data.Text.Lazy                as TL
                                                ( fromStrict
                                                , unpack
                                                )
import qualified Data.ByteString.Lazy          as BSL
                                                ( toChunks )
import qualified Data.ByteString.Lazy.Char8    as C
                                                ( fromChunks
                                                , unpack
                                                )

import qualified Data.HashMap.Lazy             as HML
                                                ( lookup )

import           Control.Applicative            ( empty
                                                , pure
                                                )
import           Control.Monad                  ( void
                                                , mzero
                                                )
import           Control.Monad.Combinators.Expr -- from parser-combinators
import           Data.Void
import           GHC.Generics                   ( Generic )
import           Text.Megaparsec
import           Text.Megaparsec.Char
import           Data.Text                     as T
                                         hiding ( empty
                                                , length
                                                , unlines
                                                )
import qualified Text.Megaparsec.Char.Lexer    as L
import           Data.Maybe                     ( isNothing
                                                , fromJust
                                                )
import           Data.Map                      as M
                                         hiding ( empty )
import           Control.Lens                   ( (^.)
                                                , (&)
                                                , (.~)
                                                , (^?)
                                                , at
                                                , ix
                                                , non
                                                , _Just
                                                , (^?!)
                                                )
import           Control.Lens.TH                ( makeLenses )
import           Control.Exception.Safe         ( Exception(..)
                                                , MonadThrow
                                                , throwM
                                                , catch
                                                )
data Formality =
    Var Integer
    | Typ
    | All {allEras :: Bool
          , allName :: Text
          , allBind ::  Formality
          , allBody ::  Formality}
    | Lam {lamEras :: Bool
          , lamName :: Text
          , lamBind :: Maybe Formality
          , lamBody :: Formality}
    | App {appEras :: Bool
        ,  appFunc :: Formality
        , appArgm :: Formality}
    | Ref Text
    deriving (Show, Eq, Ord, Generic)

toTerm :: Formality -> Text
toTerm (Var i)             = T.pack $ "#" <> show i
toTerm Typ                 = "*"
toTerm (All _ _ bind body) = "&" <> toTerm bind <> toTerm body
toTerm (Lam _ _ bind body) = "^" <> maybe "" toTerm bind <> toTerm body
toTerm (App _ func argm  ) = "@" <> toTerm func <> toTerm argm
toTerm (Ref name         ) = bracket name where bracket n = "{" <> n <> "}"

-- TODO: fix complexity
erasNameBodyBindToJson :: Bool -> Text -> Maybe Formality -> Formality -> Value
erasNameBodyBindToJson eras name body bind = object
    [ "eras" .= toJSON eras
    , "name" .= toJSON name
    , "body" .= toJSON body
    , "bind" .= toJSON bind
    ]

instance ToJSON Formality where
    toJSON Typ = toJSON [String "Typ", object [], toJSON $ toTerm Typ]
    toJSON a@(All eras name body bind) = toJSON
        [ String "All"
        , erasNameBodyBindToJson eras name (Just body) bind
        , String $ toTerm a
        ]
    toJSON a@(Lam eras name body bind) = toJSON
        [ String "Lam"
        , erasNameBodyBindToJson eras name body bind
        , String $ toTerm a
        ]
    toJSON a@(Ref name) =
        toJSON [String "Ref", object ["name" .= toJSON name], toJSON $ toTerm a]
    toJSON a@(App eras func argm) = toJSON
        [ String "App"
        , object
            [ "eras" .= toJSON eras
            , "func" .= toJSON func
            , "argm" .= toJSON argm
            ]
        , String $ toTerm a
        ]
    toJSON a@(Var idx) =
        toJSON [String "Var", object ["index" .= toJSON idx], String $ toTerm a]

instance FromJSON Formality where
    parseJSON o' = case fromJSON o' of
        Success [c, Object o, _]
            | Success (String "Typ") <- fromJSON c
            -> pure Typ
            | Success (String "Var") <- fromJSON c
            -> Var <$> o .: "index"
            | Success (String "All") <- fromJSON c
            -> All
                <$> o
                .:  "eras"
                <*> o
                .:  "name"
                <*> o
                .:  "bind"
                <*> o
                .:  "body"
            | Success (String "Lam") <- fromJSON c
            -> Lam
                <$> o
                .:  "eras"
                <*> o
                .:  "name"
                <*> o
                .:  "bind"
                <*> o
                .:  "body"
            | Success (String "App") <- fromJSON c
            -> App <$> o .: "eras" <*> o .: "func" <*> o .: "argm"
            | Success (String "Ref") <- fromJSON c
            -> Ref <$> o .: "name"
            | otherwise
            -> mzero
        _ -> mzero

data Ctx = Ctx
    {ctxHead :: (Text, Formality)
    , ctxTail :: Maybe Ctx}
    deriving (Show, Eq, Ord, Generic)

extend :: Maybe Ctx -> (Text, Formality) -> Ctx
extend ctx bind = Ctx bind ctx

getTerm ctx i = case getBind ctx i 0 of
    (Just n, Just t) -> Just t
    _                -> Nothing

indexOf :: (Ord t, Num t, Num a) => Maybe Ctx -> Text -> t -> a -> Maybe a
indexOf ctx name skip i
    | isNothing ctx = Nothing
    | (fst . ctxHead <$> ctx) == Just name && skip > 0 = indexOf
        (ctxTail =<< ctx)
        name
        (skip - 1)
        (i + 1)
    | (fst . ctxHead <$> ctx) /= Just name = indexOf (ctxTail =<< ctx)
                                                     name
                                                     skip
                                                     (i + 1)
    | otherwise = Just i

getBind :: Maybe Ctx -> Integer -> Integer -> (Maybe Text, Maybe Formality)
getBind ctx i j
    | isNothing ctx
    = (Nothing, Nothing)
    | j < i
    = getBind (ctxTail =<< ctx) i (j + 1)
    | otherwise
    = let t = snd . ctxHead <$> ctx
          n = fst . ctxHead <$> ctx
      in  case t of
              Just v  -> (n, Just $ shift i 0 v)
              Nothing -> (n, Nothing)

shift :: Integer -> Integer -> Formality -> Formality
shift inc depth ctor = case ctor of
    Var i | i < depth -> Var i
          | otherwise -> Var $ i + inc
    All eras name bind body -> All eras name (goP1 bind) (goP1 body)
    Lam eras name bind body -> Lam eras name (goP1 <$> bind) body
    App eras func argm      -> App eras (go func) (go argm)
    a                       -> a
  where
    goP1 = shift inc (depth + 1)
    go   = shift inc depth


subst :: Formality -> Maybe Formality -> Integer -> Formality
subst ctor val depth = case ctor of
    Var i | i == depth -> fromJust val
          | i > depth  -> Var (i - 1)
          | otherwise  -> Var i
    All eras name bind body -> All eras name (go bind val) (go body val)
    Lam eras name bind body ->
        Lam eras name (flip go val <$> bind) (go body val)
    App eras func argm ->
        App eras (subst func val depth) (subst argm val depth)
    a -> a
    where go b v = subst b (shift 1 0 <$> v) (depth + 1)

erase :: Formality -> Formality
erase = \case
    All eras name bind body -> All eras name (erase bind) (erase body)
    Lam eras name _ body | eras      -> subst (erase body) (Just Typ) 0
                         | otherwise -> Lam eras name Nothing (erase body)
    App eras func argm | eras      -> erase func
                       | otherwise -> App eras (erase func) (erase argm)
    a -> a
data TEq =
    Eql Formality Formality
    | Bop Bool TEq TEq
    | Val Bool
    deriving (Show, Eq, Ord, Generic)

data Def = Def
    { _defName :: Text
    , _defTerm :: Formality
    , _defType :: Maybe Formality
    , _defSeen :: Bool
    , _defDone :: Bool}
    deriving (Show, Eq, Ord, Generic)

makeLenses ''Def

norm :: Formality -> M.Map Text Def -> Bool -> Formality
norm ctor defs isFull = case ctor of
    All eras name bind body ->
        All eras name (cont defs False bind) (cont defs isFull body)
    Lam eras name bind body ->
        Lam eras name (cont defs False <$> bind) (cont defs isFull body)
    App eras func argm -> apply eras func argm
    Ref n              -> dereference n
    a                  -> a
  where
    cont d i b | isFull    = norm b d i
               | otherwise = b
    apply eras func argm
        | Lam _ _ _ body <- norm func defs False = norm
            (subst body (Just argm) 0)
            defs
            isFull
        | otherwise = App eras (cont defs isFull func) (cont defs isFull argm)
    dereference name
        | Just False <- defs ^? at name . _Just . defSeen = norm
            (defs ^?! at name . _Just . defTerm)
            defs
            isFull
        | otherwise = Ref name

getFuncArgm :: Formality -> Maybe (Formality, Formality)
getFuncArgm (App _ func argm) = Just (func, argm)
getFuncArgm _                 = Nothing

getBindBody :: Formality -> Maybe (Formality, Formality)
getBindBody (All _ _ bind body) = Just (bind, body)
getBindBody _                   = Nothing

getBody :: Formality -> Maybe Formality
getBody (Lam _ _ _ body) = Just body
getBody _                = Nothing

getIndex :: Formality -> Maybe Integer
getIndex (Var i) = Just i
getIndex _       = Nothing

-- If non-deref whnfs are app and fields are equal, then a == b
xBop :: Formality -> Formality -> Maybe TEq
xBop ax' bx'
    | Just (axfunc, axarg) <- getFuncArgm ax'
    , Just (bxfunc, bxarg) <- getFuncArgm bx'
    = Just $ Bop False (Eql axfunc bxfunc) (Eql axarg bxarg)
    | otherwise
    = Nothing

-- If whnfs are equal and fields are equal, then a == b
yBop :: Formality -> Formality -> TEq
yBop ay' by'
    | ay' == Typ && by' == Typ
    = Val True
    | Just (aybind, aybody) <- getBindBody ay'
    , Just (bybind, bybody) <- getBindBody by'
    = Bop False (Eql aybind bybind) (Eql aybody bybody)
    | Just aybody <- getBody ay'
    , Just bybody <- getBody by'
    = Eql aybody bybody
    | Just (ayfunc, ayarg) <- getFuncArgm ay'
    , Just (byfunc, byarg) <- getFuncArgm by'
    = Bop False (Eql ayfunc byfunc) (Eql ayarg byarg)
    | otherwise
    = Val False

stepEq :: Map Text Def -> TEq -> TEq
stepEq defs (Eql a b) | a == b || ax == bx || ay == by = Val True
                      | Just x <- xBop ax bx           = Bop True x (yBop ay by)
                      | Nothing <- xBop ax bx          = yBop ay by
  where
    ax = norm a mempty False
    bx = norm b mempty False
    ay = norm a defs False
    by = norm b defs False

stepEq _ _ = error "impossible"

equals :: Formality -> Formality -> Map Text Def -> Bool
equals a b defs = loop (Eql a b)
  where
    go (Bop v (Val x) y) | x == v    = Val v
                         | otherwise = y
    go (Bop v x (Val y)) | y == v    = Val v
                         | otherwise = x
    go (  Bop v x y) = Bop v (go x) (go y)
    go (  Eql a' b') = stepEq defs (Eql a' b')
    go v@(Val _    ) = v
    loop n = case go n of
        Val v -> v
        n'    -> loop n'
-- FIXME: may need State to handl updates to defs
infer
    :: MonadThrow m
    => Formality
    -> Map Text Def
    -> Ctx
    -> m (Maybe Formality)
infer term defs ctx = case term of
    Typ -> pure $ Just Typ
    All eras name bind body -> do
        let ex_ctx = extend (Just ctx) (name, bind)
        bind_t <- infer bind defs ex_ctx
        body_t <- infer body defs ex_ctx
        case (bind_t, body_t) of  -- fixme:  meh?  
            (Just bind_t', Just body_t') -> 
                if not (equals bind_t' Typ defs)
                        || not (equals body_t' Typ defs)
                    then
                        throwM $ ForallNotAType term ctx
                    else
                        pure $ Just Typ
            _ -> throwM $ ForallNotAType term ctx
    Lam eras name bind body -> if isNothing bind
        then throwM $ NonAnnotatedLambda term ctx
        else
            let (Just bind') = bind 
                ex_ctx = extend (Just ctx) (name, bind')
                body_t = infer body defs ex_ctx
            in  fmap (All eras name bind') <$> body_t -- FIXME need to `infer term_t defs ctx`

    App eras func argm
        | func_t@(All eras' _ _ body') <- norm (infer func defs ctx) defs False
        -> let bind_t = subst bind argm 0
               argm_v = check
                   argm
                   bind_t
                   defs
                   ctx
                   (\_ -> "`" show term <> show ctx <> "`'s argument ")
           in  if eras /= eras'
                   then throwM $ ErasureNoMatch term ctx
                   else pure . Just $ subst body' argm_v 0
        | otherwise
        -> throwM $ NonFunctionApplication term ctx
    Ref name
        | Just def <- defs ^. at name -> if def ^. defDone
            then pure $ def ^. defType
            else if not . isNothing $ def ^. defType
                then check (def ^. defTerm)
                           (def ^?! defType)
                           defs
                           ctx
                           (\_ -> "`" <> name <> "`'s annotated type")
                else
                    pure
                    $  def
                    &  defType
                    .~ infer (def ^. defTerm) defs ctx
                    &  defType
        | otherwise -> throwM $ UndefinedReference name
    Var i -> pure $ getTerm (Just ctx) i

data InferenceException =
    UndefinedReference Text
    | NonFunctionApplication Formality Ctx
    | ErasureNoMatch Formality Ctx
    | NonAnnotatedLambda Formality Ctx
    | ForallNotAType Formality Ctx
    | EqualityUndecideable Formality Formality Ctx
    | TypeMismatch Formality Formality (() -> Text) (Maybe Ctx)
    deriving (Generic)

instance Show InferenceException where
    show (UndefinedReference name) =
        "Undefined reference: `" <> show name <> "`."
    show (NonFunctionApplication term ctx) =
        "Non-function application on `" <> show term <> show ctx <> "`."
    show (ErasureNoMatch term ctx) =
        "Erasure doesn't match on application `"
            <> show term
            <> show ctx
            <> "`."
    show (NonAnnotatedLambda term ctx) =
        "Can't infer non-annotated lambda `" <> show term <> show ctx <> "`."
    show (ForallNotAType term ctx) =
        "Forall not a type: " <> show term <> show ctx <> "`."
    show (EqualityUndecideable terma termb ctx) =
        "Couldn't decide if terms are equal "
            <> unlines [show terma, show termb, show ctx]
    show (TypeMismatch expect actual expr ctx) = unlines
        [ "Type mismatch on " <> T.unpack (expr ())
        , "- Expect = " <> show (norm expect mempty True) <> show ctx
        , "- Actual =  " <> show (norm expect mempty True) <> show ctx
        ]

instance Exception InferenceException


check term typ defs mctx expr = case (typ', term) of
    (All aeras aname abind abody, Lam leras lname Nothing lbody) -> do
        infer typ' defs ctx
        let ex_ctx = extend ctx (aname, abind)
        let body_v = check
                lbody
                abody
                defs
                ex_ctx
                (\_ -> T.pack $ "`" <> show (term, ctx) <> "`'s body")
        pure $ Lam aeras aname abind body_v
    (_, Lam _ (Just _) _) -> do
        let term_t  = infer term defs ctx
        let checked = equals typ' term_t defs ctx
        checks <- catch checked
                        (\_ -> thowM $ EqualityUndecideable typ' term_t ctx)
        if checks
            then pure term
            else throwM $ TypeMismatch typ' (norm term_t defs False) expr crx
  where
    typ' = norm typ defs False
    ctx  = fromMaybe mempty mctx

type Parser = Parsec Void Text

sc :: Parser ()
sc = L.space space1 lineCmnt empty where lineCmnt = L.skipLineComment "//"

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser Text
symbol = L.symbol sc

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

braces :: Parser a -> Parser a
braces = between (symbol "{") (symbol "}")

brackets :: Parser a -> Parser a
brackets = between (symbol "[") (symbol "]")

eql :: Parser Text
eql = symbol "="

colon :: Parser Text
colon = symbol ":"

rword :: Text -> Parser ()
rword w = (lexeme . try) (string w *> notFollowedBy alphaNumChar)

era :: Parser Bool
era = do
    eras <- try (symbol "-")
    pure $ check eras
    where check x = x == "-"

parseApp :: Maybe Ctx -> Parser Formality
parseApp ctx = do
    func <- parens (parseTerm ctx)
    eras <- era
    App eras func <$> parseTerm ctx

parseType :: Parser Formality
parseType = do
    rword "Type"
    pure Typ

parseForall :: Maybe Ctx -> Parser Formality
parseForall ctx = do
    (eras, name, bind) <- braces forall
    body               <- parseTerm (Just $ extend ctx (name, Var 0))
    pure $ All eras name bind body
  where
    forall = do
        eras <- era
        name <- T.pack <$> many letterChar
        _    <- colon
        bind <- parseTerm (Just $ extend ctx (name, Var 0))
        pure (eras, name, bind)

parseLambda :: Maybe Ctx -> Parser Formality
parseLambda ctx = do
    (eras, name, bind) <- brackets lambda
    body               <- parseTerm (Just $ extend ctx (name, Var 0))
    pure $ Lam eras name bind body
  where
    lambda = do
        eras <- era
        name <- T.pack <$> many letterChar
        bind <- try (colonParseTerm name)
        pure (eras, name, bind)
    colonParseTerm n = do
        _    <- colon
        bind <- parseTerm (Just $ extend ctx (n, Var 0))
        pure $ Just bind

parseLet :: Maybe Ctx -> Parser Formality
parseLet ctx = do
    name <- T.pack <$> many letterChar
    copy <- optional $ parseTerm ctx
    body <- parseTerm (Just $ extend ctx (name, Var 0))
    pure $ subst body copy 0

parseVarRef :: Maybe Ctx -> Parser Formality
parseVarRef ctx = do
    name  <- T.pack <$> many letterChar
    ticks <- many (symbol "'")
    case indexOf ctx name (length ticks) 0 of
        Nothing -> pure $ Ref name
        Just v  -> pure . fromJust . snd $ getBind ctx v 0

parseTerm :: Maybe Ctx -> Parser Formality
parseTerm ctx =
    parseApp ctx
        <|> parseForall ctx
        <|> parseType
        <|> parseLet ctx
        <|> parseLambda ctx
        <|> parseVarRef ctx



