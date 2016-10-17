{-
Contributors: Liam O'Connor-Davis and Constantinos Paraskevopoulos
Last Updated: October 2016
Description: Implements a type inference pass for the Haskell subset MinHS.
-}

module MinHS.TyInfer where

import qualified MinHS.Env as E
import MinHS.Syntax
import MinHS.Subst
import MinHS.TCMonad

import Data.Monoid (Monoid (..), (<>))
import Data.Foldable (foldMap)
import Data.List (nub, union, (\\))

-- returns the type of a given primop
primOpType :: Op -> QType
primOpType Gt   = Ty $ Base Bool --Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Ge   = Ty $ Base Bool --Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Lt   = Ty $ Base Bool --Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Le   = Ty $ Base Bool --Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Eq   = Ty $ Base Bool --Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Ne   = Ty $ Base Bool --Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Neg  = Ty $ Base Int  --Base Int `Arrow` Base Int
primOpType Fst  = Forall "a"
                $ Forall "b"
                $ Ty
                $ (TypeVar "a" `Prod` TypeVar "b") `Arrow` TypeVar "a"
primOpType Snd  = Forall "a"
                $ Forall "b"
                $ Ty
                $ (TypeVar "a" `Prod` TypeVar "b") `Arrow` TypeVar "b"
primOpType _    = Ty $ Base Int  --Base Int `Arrow` (Base Int `Arrow` Base Int)

-- returns the type of a constructor
constType :: Id -> Maybe QType
constType "True"  = Just $ Ty $ Base Bool
constType "False" = Just $ Ty $ Base Bool
constType "()"    = Just $ Ty $ Base Unit
constType "Pair"  = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "a" `Arrow` (TypeVar "b" `Arrow` (TypeVar "a" `Prod` TypeVar "b"))
constType "Inl"   = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "a" `Arrow` (TypeVar "a" `Sum` TypeVar "b")
constType "Inr"   = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "b" `Arrow` (TypeVar "a" `Sum` TypeVar "b")
constType _       = Nothing

type Gamma = E.Env QType

initialGamma :: Gamma
initialGamma = E.empty

tv :: Type -> [Id]
tv = tv'
  where
    tv' (TypeVar x) = [x]
    tv' (Prod  a b) = tv a `union` tv b
    tv' (Sum   a b) = tv a `union` tv b
    tv' (Arrow a b) = tv a `union` tv b
    tv' (Base c   ) = []

tvQ :: QType -> [Id]
tvQ (Forall x t) = filter (/= x) $ tvQ t
tvQ (Ty t) = tv t

tvGamma :: Gamma -> [Id]
tvGamma = nub . foldMap tvQ

-- implements the type inference pass for the MinHS program
infer :: Program -> Either TypeError Program
infer program =
  do
    (p', tau, s) <- runTC $ inferProgram initialGamma program
    return p'

-- replaces forall quantifiers with fresh type variables in a given type
unquantify :: QType -> TC Type
{-
Normally this implementation would be possible:

unquantify (Ty t) = return t
unquantify (Forall x t) = do x' <- fresh
                             unquantify (substQType (x =:x') t)

However as our "fresh" names are not checked for collisions with names bound in the type
we avoid capture entirely by first replacing each bound
variable with a guaranteed non-colliding variable with a numeric name,
and then substituting those numeric names for our normal fresh variables
-}
unquantify = unquantify' 0 emptySubst
unquantify' :: Int -> Subst -> QType -> TC Type
unquantify' i s (Ty t) = return $ substitute s t
unquantify' i s (Forall x t) =
  do x' <- fresh
     unquantify' (i + 1)
                 ((show i =: x') <> s)
                 (substQType (x =:TypeVar (show i)) t)

-- computes the most general unifier of two types
unify :: Type -> Type -> TC Subst

-- unifies type variables
unify (TypeVar v1) (TypeVar v2) | v1 == v2 = return emptySubst
unify (TypeVar v1) (TypeVar v2) | v1 /= v2 = return (v2 =: TypeVar v1)

-- unifies primitive types
unify (Base a) (Base b) =
  if a == b
  then return emptySubst
  else error "primitive types differ"

-- unifies product types
-- TODO
-- unifies function types
-- TODO
-- unifies sum types
-- TODO
-- unifies a type variable with an arbitrary term
-- TODO

-- terminates in error for all other combinations
unify _ _ = error "no unifier"

-- reintroduces forall quantifiers
generalise :: Gamma -> Type -> QType
generalise g t = Ty t
-- TODO

-- inferExp infers the type of the expression in the binding
-- allTypes runs the resulting substitution on the entire expression
inferProgram :: Gamma -> Program -> TC (Program, Type, Subst)
inferProgram g [Bind id Nothing [] exp] =
  do
    (exp', t, subst) <- inferExp g exp
    return (([Bind id (Just (generalise g t)) [] (allTypes (substQType subst) exp')]), t, subst)

-- infers the type of an expression under an environment
-- returns the expression, its type and a substitution
inferExp :: Gamma -> Exp -> TC (Exp, Type, Subst)

-- infers the type of numeric constants
-- Num n :: Int; empty subst
inferExp g e@(Num n) = return (e, Base Int, emptySubst)

-- infers the type of variables
-- Var x :: tau with foralls replaced with fresh type variables; empty subst
inferExp g e@(Var x) =
  case (E.lookup g x) of
    Just t ->
      do
        t' <- unquantify t -- replaces foralls with fresh type variables
        return (e, t', emptySubst)
    _ -> error $ "undefined variable " ++ (show x)

-- infers the type of constructors
-- Con c :: tau with forall replaced with fresh type variables; empty subst
inferExp g e@(Con c) =
  case (constType c) of
    Just t ->
      do
        t' <- unquantify t -- replaces foralls with fresh type variables
        return (e, t', emptySubst)
    _ -> error $ "unknown constructor " ++ (show c)

-- infers the type of the unary negation operator
-- Neg x :: Int; empty subst
inferExp g e@(App (Prim Neg) x) = return (e, Base Int, emptySubst)

-- infers the type of other primops
-- Prim o x y :: tau with forall replaced with fresh type variables; empty subst
inferExp g e@(App (App (Prim o) x) y) =
  do
-- TODO: fix primOpType if needed
    t <- unquantify $ primOpType o -- replaces foralls with fresh type variables
    return (e, t, emptySubst)

-- infers the type of function applications
-- ::

-- infers the type of if statements
-- If e e1 e2 :: mgu applied to the else branch
inferExp g exp@(If e e1 e2) =
  do
    (e', tau, t)    <- inferExp g e
    u               <- unify tau (Base Bool)
    (e1', tau1, t1) <- inferExp (substGamma u (substGamma t g)) e1
    (e2', tau2, t2) <- inferExp (substGamma t1 (substGamma u (substGamma t g))) e2
    u' <- unify (substitute t2 tau1) tau2
    return (exp, substitute u' tau2, u' <> t2 <> t1 <> u <> t)

-- infers the type of case expressions
-- ::
--inferExp g (Case e [Alt "Inl" [x] e1, Alt "Inr" [y] e2]) = error ""
--inferExp g (Case e _) = typeError MalformedAlternatives

--infers the type of recursive functions
-- ::

--infers the type of let bindings
-- ::

-- terminates in error for all other expressions
inferExp _ e = error $ "runtime error: " ++ (show e)
