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

cong2 : (f : a -> b -> c) -> x = y -> u = v -> f x u = f y v
cong2 _ Refl Refl = Refl

infix 4 +=

(+=) : (f : Fin m -> Term n) -> (g : Fin m -> Term n) -> Type
(+=) {m = m} f g = (x : Fin m) -> f x = g x

bindId : (t : Term m) -> bind Var t = t
bindId (Var v) = Refl
bindId Leaf = Refl
bindId (l :@: r) =  cong2 (:@:) (bindId l) (bindId r)
                   
bindCompose : (t : Term m) -> bind (compose f g) t = bind f (bind g t)
bindCompose (Var v) = Refl
bindCompose Leaf = Refl
bindCompose (l :@: r) = cong2 (:@:) (bindCompose l) (bindCompose r)

composeId : (f : Fin m -> Term n) -> compose f Var += f
composeId f _ = Refl

composeAssoc : (f : Fin m2 -> Term n) -> 
               (g : Fin m1 -> Term m2) -> 
               (h : Fin m -> Term m1) -> 
               compose (compose f g) h += compose f (compose g h)
composeAssoc f g h x = bindCompose (h x)

Ext : Property m -> (f : Fin m -> Term n) -> Property n
Ext P f n' g = P _ (compose g f)

extVar : (x : Fin m) -> (p : Property m) -> p .=. (Ext p Var) 
extVar x p s f = (\ a => ?rhs  , \ a => ?rhs)

nothingExt : Nothing p -> Nothing (Ext p f)
nothingExt {f = f} np n pr arg = np n (compose pr f) arg

composeExt : Ext (Ext p g) f .=. Ext p (compose f g)
composeExt n f = (?rhs , ?rhs1) 

unifiesExt : Ext (Unifies s t) (compose f g) .=. Ext (Unifies (bind g s) (bind g t)) f
unifiesExt = ?rhs

-- optimizing properties

infix 4 .<

(.<) : (f : Fin m -> Term n) -> (g : Fin m -> Term n') -> Type
f .< g = Exists (\ f' => f += compose f' g) 
