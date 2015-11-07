module UnifyProofs

import Data.Fin
import Unify

%default total

-- starting the proof

Property : (m : Nat) -> Type
Property m = (n : Nat) -> (Fin m -> Term n) -> Type

Unifies : Term m -> Term m -> Property m
Unifies s t _ f = bind f s = bind f t

-- combining properties

infixl 4 .&.

(.&.) : Property m -> Property m -> Property m
P .&. Q = \ n => \ f =>  Pair (P n f) (Q n f)

infix 4 .=.

(.=.) : Property m -> Property m -> Type
(.=.) {m = m} P Q = (n : Nat) -> (f : Fin m -> Term n) -> Pair (P n f -> Q n f) 
                                                               (Q n f -> P n f)

-- unifies is symmetric

unifiesSym : Unifies s t .=. Unifies t s
unifiesSym _ f = (sym , sym)

-- unifies and application

appInv : (s :@: t) = (s' :@: t') -> (s = s' , t = t')
appInv Refl = (Refl , Refl)

appBack : (s = s' , t = t') -> (s :@: t) = (s' :@: t')
appBack (Refl , Refl) = Refl

unifiesApp : Unifies (s :@: t) (s' :@: t') .=. (Unifies s s' .&. Unifies t t')
unifiesApp _ f = (appInv , appBack)

-- failing properties

Nothing : Property m -> Type
Nothing {m = m} p = (n : Nat) -> (f : Fin m -> Term n) -> Not (p n f)

nothingEquiv : p .=. q -> Nothing p -> Nothing q
nothingEquiv pr pr' n f qf with (pr n f)
  nothingEquiv pr pr' n f qf | (pnf' , qnf') = void (pr' n f (qnf' qf))

-- extending properties

Ext : Property m -> (f : Fin m -> Term n) -> Property n
Ext P f n' g = P _ (compose g f)


extVar : (p : Property m) -> p .=. (Ext p Var) 
extVar p = \n => \f => (?rhs , ?rhs2)
