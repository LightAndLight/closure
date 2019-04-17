{-# language BangPatterns, FlexibleContexts, TypeFamilies #-}
{-# language OverloadedStrings #-}
module Closure where

import Control.Applicative (Alternative, (<|>), (<**>), many, some)
import Data.String (IsString)
import Data.Void (Void)
import Text.Megaparsec (MonadParsec, Tokens, Token, sepBy, between, eof, parse, try)
import Text.Megaparsec.Char (char, digitChar, space1, string)

data Exp
  = Z
  | S Exp
  | AppF Exp Exp
  | AppT Exp Exp
  | Lam Exp Exp
  | Nil
  | Cons Exp Exp
  | Unit
  deriving (Eq, Show)

fromInt :: Int -> Exp
fromInt !n =
  case compare n 0 of
    LT -> error $ "fromInt: invalid input: " <> show n
    EQ -> Z
    GT -> S $! fromInt (n-1)

fromList :: [Exp] -> Exp
fromList [] = Nil
fromList (a:as) = Cons a $! fromList as

chainl1 :: MonadParsec e s m => m a -> m (a -> a -> a) -> m a
chainl1 p op = scan where
  scan = p <**> rst
  rst = try ((\f y g x -> g (f x y)) <$> op <*> p) <*> rst <|> pure id
{-# INLINE chainl1 #-}

parseExp :: (IsString (Tokens s), MonadParsec Void s m, Token s ~ Char) => m Exp
parseExp = token exp <* eof
  where
    token m = m <* many space1
    exp = appF <|> lam
    lam = Lam <$ token (char '\\') <*> token ctx <* token (string "->") <*> exp
    appF = chainl1 (token appT) (AppF <$ token (char '@'))
    appT = chainl1 atom (AppT <$ some space1)
    atom =
      unit <|>
      var <|>
      ctx <|>
      between (token $ char '(') (char ')') (token exp)
    unit = Unit <$ string "unit"
    ctx =
      fromList <$>
      between
        (token $ char '[')
        (char ']')
        (sepBy (token exp) (token $ char ','))
    var = fromInt . read <$> some digitChar

isCtx :: Exp -> Bool
isCtx Nil = True
isCtx Cons{} = True
isCtx _ = False

step :: Exp -> Maybe Exp
step (AppT a b) =
  (\a' -> AppT a' b) <$> step a <|>
  (\b' -> AppT a b') <$> step b <|>
  case a of
    Z -> pure $ AppF Z a
    S n -> pure $ AppF (S a) b
    AppF x y -> pure $ AppF (AppF x y) b
    Lam x y -> pure $ AppT (Cons b x) y
    Nil -> pure b
    Cons x _ | Z <- b -> pure x
    Cons _ x | S y <- b -> pure $ AppT x y
    Cons{} | AppF z w <- b -> pure $ AppT (a `AppT` z) (a `AppT` w)
    Cons{} | Lam z w <- b -> pure $ Lam (a `AppT` z) w
    Cons{} | Nil <- b -> pure Nil
    Cons x y | Cons z w <- b -> pure $ Cons (a `AppT` z) (a `AppT` w)
    _ -> Nothing
step (S a) = S <$> step a
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

data Ty
  = TyArr Ty Ty
  | TyUnit
  deriving (Eq, Show)

data TypeError
  = TypeMismatch Ty Ty
  | ExpectedFunction Exp
  | ExpectedArrow Exp Ty
  | Can'tInfer Exp
  | ExpectedContext Exp
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
    Z ->
      case ctx of
        [] -> error "stuck"
        t:_ -> pure t
    S n ->
      case ctx of
        [] -> error "stuck"
        _:ts -> infer ts n
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
    _ -> Left $ Can'tInfer e

omega :: Exp
omega =
  Lam Nil $
  Lam (Cons Z Nil) $
  AppF Z (AppT (AppT (S Z) (S Z)) Z)
