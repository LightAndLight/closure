module Closure where

import Control.Monad (guard)
import Control.Monad.Writer (Writer)
import Data.Vector (Vector)

import qualified Data.Vector as Vector

data CC
  = Ann CC TCC
  | Var !Int
  | Product (Vector CC)
  | Lam CC CC
  | AppFun CC CC
  | AppSubst (Vector CC) CC
  deriving (Eq, Ord, Show)

data TCC
  = TProduct (Vector TCC)
  | TFun TCC TCC
  deriving (Eq, Ord, Show)

check :: Vector TCC -> CC -> TCC -> Maybe ()
check env tm ty =
  case tm of
    Lam a b ->
      case ty of
        TFun x y -> do
          aTy <- infer env a
          case aTy of
            TProduct ts -> check (Vector.cons x ts) b y
            _ -> Nothing
        _ -> Nothing
    _ -> do
      ty' <- infer env tm
      guard (ty == ty')

infer :: Vector TCC -> CC -> Maybe TCC
infer env tm =
  case tm of
    Var n ->
      if Vector.null env
      then Nothing
      else pure $ env Vector.! n
    Ann a t -> t <$ check env a t
    Product ts -> TProduct <$> traverse (infer env) ts
    AppFun a b -> do
      aTy <- infer env a
      case aTy of
        TFun x y -> y <$ check env b x
        _ -> Nothing
    AppSubst as b -> do
      env' <- traverse (infer env) as
      infer env' b
    _ -> Nothing

eval :: CC -> CC
eval tm =
  case tm of
    Ann a _ -> eval a
    Var{} -> error "stuck: var"
    Product as -> Product $ eval <$> as
    Lam a b -> Lam (eval a) b
    AppFun a b ->
      case eval a of
        Lam (Product s) t -> eval $ AppSubst (Vector.cons b s) t
        _ -> error "stuck: appfun"
    AppSubst a b ->
      case b of
        Var n -> eval $ a Vector.! n
        Product ys -> eval $ Product (AppSubst a <$> ys)
        Lam x y -> eval $ Lam (AppSubst a x) y
        AppSubst x y -> eval $ AppSubst (AppSubst a <$> x) (AppSubst a y)
        AppFun x y -> eval $ AppFun (AppSubst a x) (AppSubst a y)
        Ann x t -> eval $ Ann (AppSubst a x) t

data Inst
data Loc
newtype Code a = Code { unCode :: Writer [Inst] a }

compile_lam :: Loc -> CC -> Code ()
compile_lam env tm =
  case tm of
    Var n -> _
    _ -> compile tm

compile :: CC -> Code Loc
compile tm =
  case tm of
    Ann x _ -> compile x
    Var{} -> error "unbound variable"
    Product as -> _
    Lam a b -> _
    AppFun a b -> _
    AppSubst as b -> _