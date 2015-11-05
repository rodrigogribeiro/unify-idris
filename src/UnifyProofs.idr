module UnifyProofs

import Data.Fin
import Unify

%default total

-- starting the proof

Property : (m : Nat) -> Type
Property m = {n : Nat} -> (Fin m -> Term n) -> Type

Unifies : Term m -> Term m -> Property m
Unifies s t f = bind f s = bind f t

-- combining properties

infixl 4 .&.

(.&.) : Property m -> Property m -> Property m
P .&. Q = \f =>  ((P f) , (Q f))

infix 4 .=.

(.=.) : Property m -> Property m -> Type
(.=.) {m = m} P Q = (n : Nat) -> (f : Fin m -> Term n) -> Pair (P f -> Q f) (Q f -> P f)


-- unifies is symmetric

UnifiesSym : Unifies s t .=. Unifies t s
UnifiesSym _ f = (sym , sym)

-- unifies and application

UnifiesApp : Unifies (s :@: t) (s' :@: t') .=. (Unifies s s' .&. Unifies t t')
UnifiesApp _ f = ?rhs
