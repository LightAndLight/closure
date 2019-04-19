{-# language BangPatterns, FlexibleContexts, TypeFamilies #-}
{-# language OverloadedStrings #-}
module Closure where

import Control.Applicative ((<|>), (<**>), many, some, optional)
import Data.String (IsString)
import Data.Void (Void)
import Data.Word (Word32)
import Text.Megaparsec (MonadParsec, Tokens, Token, sepBy, between, try)
import Text.Megaparsec.Char (char, digitChar, space1, string)

data Exp
  = VZ
  | VS !Exp
  | AppF !Exp !Exp
  | AppT !Exp !Exp
  | Lam !Exp !Exp
  | Nil
  | Cons !Exp !Exp
  | Unit
  | Ann !Exp !Ty
  | Nat32 !Word32
  | AddNat32 Exp Exp
  deriving (Eq, Show)

data Ty
  = TyArr !Ty !Ty
  | TyUnit
  | TyNat32
  deriving (Eq, Show)

fromInt :: Int -> Exp
fromInt !n =
  case compare n 0 of
    LT -> error $ "fromInt: invalid input: " <> show n
    EQ -> VZ
    GT -> VS $! fromInt (n-1)

toInt :: Exp -> Maybe Int
toInt VZ = Just 0
toInt (VS n) = (+1) <$> toInt n
toInt _ = Nothing

fromList :: [Exp] -> Exp
fromList [] = Nil
fromList (a:as) = Cons a $! fromList as

toList :: Exp -> Maybe [Exp]
toList Nil = Just []
toList (Cons a b) = (a :) <$> toList b
toList _ = Nothing

chainl1 :: MonadParsec e s m => m a -> m (a -> a -> a) -> m a
chainl1 p op = scan where
  scan = p <**> rst
  rst = try ((\f y g x -> g (f x y)) <$> op <*> p) <*> rst <|> pure id
{-# INLINE chainl1 #-}

token :: (IsString (Tokens s), MonadParsec Void s m, Token s ~ Char) => m a -> m a
token m = m <* many space1

parseTy :: (IsString (Tokens s), MonadParsec Void s m, Token s ~ Char) => m Ty
parseTy = token ty
  where
    ty = tyArr
    atom =
      unit <|>
      nat <|>
      between (token $ char '(') (char ')') (token ty)
    unit = TyUnit <$ string "Unit"
    nat = TyNat32 <$ string "Nat32"
    tyArr =
      (\a -> maybe a (TyArr a)) <$>
      atom <*>
      optional (try (many space1 *> token (string "->")) *> tyArr)

parseExp :: (IsString (Tokens s), MonadParsec Void s m, Token s ~ Char) => m Exp
parseExp = token expr
  where
    expr = ann <|> lam
    lam = Lam <$ token (char '\\') <*> token ctx <* token (string "->") <*> expr
    ann =
      (\a -> maybe a (Ann a)) <$>
      appF <*>
      optional (try (many space1 *> token (char ':')) *> parseTy)
    appF = chainl1 (token appT) (AppF <$ token (char '@'))
    appT = chainl1 atom (AppT <$ some space1)
    atom =
      unit <|>
      nat32 <|>
      var <|>
      ctx <|>
      between (token $ char '(') (char ')') (token expr)
    unit = Unit <$ string "unit"
    nat32 = Nat32 . read <$> some digitChar
    ctx =
      fromList <$>
      between
        (token $ char '[')
        (char ']')
        (sepBy (token expr) (token $ char ','))
    var = fromInt . read <$ char '#' <*> some digitChar

isCtx :: Exp -> Bool
isCtx Nil = True
isCtx Cons{} = True
isCtx _ = False

step :: Exp -> Maybe Exp
step (AppT a b) =
  (\a' -> AppT a' b) <$> step a <|>
  -- this is a call-by-value kind of thing

  -- but we could also get a call-by-name kind of thing by only
  -- reducing `b` when we're composing substitutions

  -- a behaviour that we wouldn't carry over to compilation is the
  -- duplication of subtitutions. when `(a, b)(x @ y) ~> (a, b)x (a, b)y`, that closure on both
  -- sides should be the same pointer. then we can hopefully get a call-by-need thing going
  (\b' -> AppT a b') <$> step b <|>
  case a of
    VZ -> pure $ AppF VZ b
    VS{} -> pure $ AppF a b
    AppF x y -> pure $ AppF (AppF x y) b
    Lam x y -> pure $ AppT (Cons b x) y
    Nil -> pure b
    Cons x _ | VZ <- b -> pure x
    Cons _ x | VS y <- b -> pure $ AppT x y
    Cons{} | AppF z w <- b -> pure $ AppT (a `AppT` z) (a `AppT` w)
    Cons{} | Lam z w <- b -> pure $ Lam (a `AppT` z) w
    Cons{} | Nil <- b -> pure Nil
    Cons{} | Cons z w <- b -> pure $ Cons (a `AppT` z) (a `AppT` w)
    Ann e t ->
      (\e' -> Ann e' t) <$> step e <|>
      pure e
    _ -> Nothing
step (VS a) = VS <$> step a
step (AppF a b ) =
  (\a' -> AppF a' b) <$> step a <|>
  (\b' -> AppF a b') <$> step b
step (Lam a b) =
  (\a' -> Lam a' b) <$> step a <|>
  (\b' -> Lam a b') <$> step b
step (Cons a b) =
  (\a' -> Cons a' b) <$> step a <|>
  (\b' -> Cons a b') <$> step b
step _ = Nothing

eval :: Exp -> Exp
eval = go where go a = maybe a go $ step a

data TypeError
  = TypeMismatch Ty Ty
  | ExpectedFunction Exp
  | ExpectedArrow Exp Ty
  | Can'tInfer Exp
  | ExpectedContext Exp
  | ScopeError
  deriving (Eq, Show)

check :: [Ty] -> Exp -> Ty -> Either TypeError ()
check ctx e ty =
  case e of
    Lam a b ->
      case ty of
        TyArr u t -> do
          ctx' <- inferCtx ctx a
          check (u : ctx') b t
        _ -> Left $ ExpectedArrow e ty
    AppT a b | isCtx a -> do
      ctx' <- inferCtx ctx a
      check ctx' b ty
    _ -> do
      eTy <- infer ctx e
      if eTy == ty
        then pure ()
        else Left $ TypeMismatch ty eTy

inferCtx :: [Ty] -> Exp -> Either TypeError [Ty]
inferCtx ctx e =
  case e of
    Nil -> pure []
    Cons a b -> do
      aTy <- infer ctx a
      ctx' <- inferCtx ctx b
      pure $ aTy : ctx'
    AppT a b | isCtx b -> do
      ctx' <- inferCtx ctx a
      inferCtx ctx' b
    _ -> Left $ ExpectedContext e

infer :: [Ty] -> Exp -> Either TypeError Ty
infer ctx e =
  case e of
    Unit -> pure TyUnit
    VZ ->
      case ctx of
        [] -> Left ScopeError
        t:_ -> pure t
    VS n ->
      case ctx of
        [] -> Left ScopeError
        _:ts -> infer ts n
    Nat32{} -> pure TyNat32
    AppF a b -> do
      aTy <- infer ctx a
      case aTy of
        TyArr bTy retTy -> do
          check ctx b bTy
          pure retTy
        _ -> Left $ ExpectedFunction a
    AppT a b | not (isCtx a), not (isCtx b) -> do
      aTy <- infer ctx a
      case aTy of
        TyArr bTy retTy -> do
          check ctx b bTy
          pure retTy
        _ -> Left $ ExpectedFunction a
    Ann a b -> b <$ check ctx a b
    AddNat32 a b -> do
      check ctx a TyNat32
      check ctx b TyNat32
      pure TyNat32
    _ -> Left $ Can'tInfer e

omega :: Exp
omega =
  Lam Nil $
  Lam (Cons VZ Nil) $
  AppF VZ (AppT (AppT (VS VZ) (VS VZ)) VZ)
