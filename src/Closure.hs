{-# language BangPatterns, FlexibleContexts, TypeFamilies #-}
{-# language OverloadedStrings #-}
{-# language DeriveFunctor #-}
module Closure where

import Control.Applicative ((<|>), (<**>), many, some, optional)
import Control.Monad (void)
import Data.String (IsString)
import Data.Void (Void)
import Data.Word (Word32)
import Text.Megaparsec (MonadParsec, Tokens, Token, sepBy, between, try)
import Text.Megaparsec.Char (char, digitChar, space1, string)

data Exp t
  = VZ t
  | VS t !(Exp t)
  | AppF t !(Exp t) !(Exp t)
  | AppT t !(Exp t) !(Exp t)
  | Subst t !(Exp t) !(Exp t)
  | Lam t !(Exp t) !(Exp t)
  | Nil t
  | Cons t !(Exp t) !(Exp t)
  | Unit t
  | Nat32 t !Word32
  | AddNat32 t (Exp t) (Exp t)
  deriving (Eq, Show, Functor)

vz_ :: Exp ()
vz_ = VZ ()

nil_ :: Exp ()
nil_ = Nil ()

unit_ :: Exp ()
unit_ = Unit ()

vs_ :: Exp () -> Exp ()
vs_ = VS ()

nat32_ :: Word32 -> Exp ()
nat32_ = Nat32 ()

appF_ :: Exp () -> Exp () -> Exp ()
appF_ = AppF ()

appT_ :: Exp () -> Exp () -> Exp ()
appT_ = AppT ()

subst_ :: Exp () -> Exp () -> Exp ()
subst_ = Subst ()

lam_ :: Exp () -> Exp () -> Exp ()
lam_ = Lam ()

cons_ :: Exp () -> Exp () -> Exp ()
cons_ = Cons ()

addNat32_ :: Exp () -> Exp () -> Exp ()
addNat32_ = AddNat32 ()

data Ty
  = TyArr !Ty !Ty
  | TyUnit
  | TyNat32
  | TySub [Ty]
  deriving (Eq, Show)

fromInt :: Int -> Exp ()
fromInt !n =
  case compare n 0 of
    LT -> error $ "fromInt: invalid input: " <> show n
    EQ -> VZ ()
    GT -> VS () $! fromInt (n-1)

toInt :: Exp a -> Maybe Int
toInt (VZ _) = Just 0
toInt (VS _ n) = (+1) <$> toInt n
toInt _ = Nothing

fromList :: [Exp ()] -> Exp ()
fromList [] = Nil ()
fromList (a:as) = Cons () a $! fromList as

toList :: Exp a -> Maybe [Exp a]
toList (Nil _) = Just []
toList (Cons _ a b) = (a :) <$> toList b
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

parseExp :: (IsString (Tokens s), MonadParsec Void s m, Token s ~ Char) => m (Exp ())
parseExp = token expr
  where
    expr = lam <|> appF
    lam = Lam () <$ token (char '\\') <*> token ctx <* token (string "->") <*> expr
    appF = chainl1 (token appT) (AppF () <$ token (char '@'))
    appT = chainl1 atom (AppT () <$ some space1)
    atom =
      unit <|>
      nat32 <|>
      var <|>
      ctx <|>
      between (token $ char '(') (char ')') (token expr)
    unit = Unit () <$ string "unit"
    nat32 = Nat32 () . read <$> some digitChar
    ctx =
      fromList <$>
      between
        (token $ char '[')
        (char ']')
        (sepBy (token expr) (token $ char ','))
    var = fromInt . read <$ char '#' <*> some digitChar

isCtx :: Exp a -> Bool
isCtx Nil{} = True
isCtx Cons{} = True
isCtx _ = False

step :: Exp () -> Maybe (Exp ())
step (AppT _ a b) =
  (\a' -> AppT () a' b) <$> step a <|>
  -- this is a call-by-value kind of thing

  -- but we could also get a call-by-name kind of thing by only
  -- reducing `b` when we're composing substitutions

  -- a behaviour that we wouldn't carry over to compilation is the
  -- duplication of subtitutions. when `(a, b)(x @ y) ~> (a, b)x (a, b)y`, that closure on both
  -- sides should be the same pointer. then we can hopefully get a call-by-need thing going
  (\b' -> AppT () a b') <$> step b <|>
  case a of
    VZ{} -> pure $ AppF () (VZ ()) b
    VS{} -> pure $ AppF () a b
    AppF _ x y -> pure $ AppF () (AppF () x y) b
    Lam () x y -> pure $ Subst () (Cons () b x) y
    _ -> Nothing
step (Subst _ a b) =
  (\a' -> Subst () a' b) <$> step a <|>
  (\b' -> Subst () a b') <$> step b <|>
  case a of
    Nil{} -> pure b
    Cons _ x _ | VZ{} <- b -> pure x
    Cons _ _ x | VS _ y <- b -> pure $ Subst () x y
    Cons{} | AppF _ z w <- b -> pure $ AppT () (Subst () a z) (Subst () a w)
    Cons{} | Lam _ z w <- b -> pure $ Lam () (Subst () a z) w
    Cons{} | Nil{} <- b -> pure $ Nil ()
    Cons{} | Cons _ z w <- b -> pure $ Cons () (Subst () a z) (Subst () a w)
    _ -> Nothing
step (VS _ a) = VS () <$> step a
step (AppF _ a b) =
  (\a' -> AppF () a' b) <$> step a <|>
  (\b' -> AppF () a b') <$> step b
step (Lam _ a b) =
  (\a' -> Lam () a' b) <$> step a <|>
  (\b' -> Lam () a b') <$> step b
step (Cons _ a b) =
  (\a' -> Cons () a' b) <$> step a <|>
  (\b' -> Cons () a b') <$> step b
step _ = Nothing

eval :: Exp () -> Exp ()
eval = go where go a = maybe a go $ step a

data TypeError
  = TypeMismatch Ty Ty
  | ExpectedFunction (Exp ())
  | ExpectedArrow (Exp ()) Ty
  | Can'tInfer (Exp ())
  | ExpectedTySub (Exp ())
  | ScopeError
  deriving (Eq, Show)

check ::
  [Ty] ->
  Exp a ->
  Ty ->
  Either TypeError (Exp Ty)
check ctx e ty =
  case e of
    Lam _ a b ->
      case ty of
        TyArr u t -> do
          (a', aTy) <- infer ctx a
          case aTy of
            TySub ctx' -> do
              b' <- check (u : ctx') b t
              pure $ Lam ty a' b'
            _ -> Left $ ExpectedTySub $ void a
        _ -> Left $ ExpectedArrow (void e) ty
    _ -> do
      (e', eTy) <- infer ctx e
      if eTy == ty
        then pure e'
        else Left $ TypeMismatch ty eTy

infer ::
  [Ty] ->
  Exp a ->
  Either TypeError (Exp Ty, Ty)
infer ctx e =
  case e of
    Nil{} -> do
      let t = TySub []
      pure $ (Nil t, t)
    Cons _ a b -> do
      (a', aTy) <- infer ctx a
      (b', bTy) <- infer ctx b
      case bTy of
        TySub bs -> do
          let t = TySub $ aTy : bs
          pure (Cons t a' b', t)
        _ -> Left $ ExpectedTySub $ void b
    Unit{} -> do
      let t = TyUnit
      pure (Unit t, t)
    VZ{} ->
      case ctx of
        [] -> Left ScopeError
        t:_ -> pure (VZ t, t)
    VS _ n ->
      case ctx of
        [] -> Left ScopeError
        _:ts -> do
          (n', nTy) <- infer ts n
          pure (VS nTy n', nTy)
    Nat32 _ a -> do
      let t = TyNat32
      pure (Nat32 t a, t)
    AppF _ a b -> do
      (a', aTy) <- infer ctx a
      case aTy of
        TyArr bTy retTy -> do
          b' <- check ctx b bTy
          pure (AppF retTy a' b', retTy)
        _ -> Left $ ExpectedFunction $ void a
    AppT _ a b -> do
      (a', aTy) <- infer ctx a
      case aTy of
        TyArr bTy retTy -> do
          b' <- check ctx b bTy
          pure (AppF retTy a' b', retTy)
        _ -> Left $ ExpectedFunction $ void a
    Subst _ a b -> do
      (a', aTy) <- infer ctx a
      case aTy of
        TySub ctx' -> do
          (b', bTy) <- infer ctx' b
          pure (Subst bTy a' b', bTy)
        _ -> Left $ ExpectedTySub $ void a
    AddNat32 _ a b -> do
      a' <- check ctx a TyNat32
      b' <- check ctx b TyNat32
      let t = TyNat32
      pure (AddNat32 t a' b', t)
    _ -> Left $ Can'tInfer $ void e