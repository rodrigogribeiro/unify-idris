module UnifyProofs

import Data.Fin
import Unify
import BasicFacts

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

infix 4 +=

(+=) : (f : Fin m -> Term n) -> (g : Fin m -> Term n) -> Type
(+=) {m = m} f g = (x : Fin m) -> f x = g x

postulate coerce : f += g -> f = g  -- cheating...

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
extVar x p s f = (replace (sym (coerce (composeId f))) , replace (coerce (composeId f)) )

nothingExt : Nothing p -> Nothing (Ext p f)
nothingExt {f = f} np n pr arg = np n (compose pr f) arg

composeExt : Ext (Ext p g) f .=. Ext p (compose f g)
composeExt {f = f} {g = g} n h = (replace (coerce (composeAssoc h f g)) , 
                                  replace (sym (coerce (composeAssoc h f g))))

unifiesExt : Ext (Unifies s t) (compose f g) .=. Ext (Unifies (bind g s) (bind g t)) f
unifiesExt {f = f}{g = g}{s = s}{t = t} n h = ( trans2 (bindCompose2 s) 
                                                       (bindCompose2 t) 
                                              , trans2 (sym (bindCompose2 s))
                                                       (sym (bindCompose2 t)))

-- optimizing properties

infix 4 .<

(.<) : (f : Fin m -> Term n) -> (g : Fin m -> Term n') -> Type
f .< g = Exists (\ f' => f += compose f' g) 

subRefl : f .< f
subRefl {f = f} = Evidence Var (\ v => sym (bindId (f v)))

subTrans : f .< g -> g .< h -> f .< h
subTrans {h = h}(Evidence x pf) (Evidence x' pf') 
            = Evidence (compose x x') 
                       (\ v => trans (pf v)
                                     (trans (cong (pf' v)) 
                                            (sym (bindCompose (h v)))))
                                            
subId : f .< Var
subId {f = f} = Evidence f (\ v => Refl)

subExtVar : (t : Term n) -> f += g -> bind f t = bind g t
subExtVar (Var v) pr = pr v
subExtVar Leaf pr = Refl
subExtVar (l :@: r) pr = cong2 (:@:) (subExtVar l pr) (subExtVar r pr)

subCompose : f .< g -> (compose f h) .< (compose g h)                                            
subCompose {f = f}{g = g}{h = h}(Evidence x pf)  
           = Evidence x (\v => sym (trans (sym (bindCompose {f = x}{g = g}(h v))) 
                                          (sym (subExtVar (h v) pf))))

 
-- maximal properties

Max : (p : Property m) -> Property m
Max {m = m} p = \n => \f => (p n f , (k : Nat) -> (f' : Fin m -> Term k) -> p k f' -> f' .< f)

applySnd : Max {m = m} p n f -> (k : Nat) -> (f' : Fin m -> Term k) -> p k f' -> f' .< f
applySnd = snd

maxEquiv : p .=. q -> Max p .=. Max q 
maxEquiv pr n f = ( \ a => ( fst (pr n f) (fst a) 
                           , \ n1 => \ g => \pr1 => (applySnd a) n1 g (snd (pr n1 g) pr1))
                  , \ a' => (snd (pr n f) (fst a')
                            , \ n2 => \ g' => \ pr2 => (applySnd a') n2 g' (fst (pr n2 g') pr2)))

-- downward closedness

DClosed : (p : Property m) -> Type
DClosed {m = m} p = (n : Nat) -> (n' : Nat) -> (f : Fin m -> Term n) -> 
                                               (g : Fin m -> Term n') -> 
                                               f .< g -> p n' g -> p n f
                                               
dClosedUnifies : (s : Term m) -> (t : Term m) -> DClosed (Unifies s t)
dClosedUnifies s t n n' f g (Evidence f' pr) eq 
               = trans (subExtVar {g = compose f' g} s pr) 
                       (trans (bindCompose {f = f'} {g = g} s) 
                              (trans (cong {f = bind f'} eq) 
                                     (trans (sym (bindCompose {f = f'}{g = g} t)) 
                                            (sym (subExtVar {g = compose f' g} t pr)))))
 
  
-- optmistic lemma

optmisticLemma : DClosed p -> Max {m = m} (Ext p a) n f -> 
                              Max (Ext q (compose f a)) n g -> 
                              Max (Ext (p .&. q) (compose f a)) n g
optmisticLemma {n = n}{f = f}{g = g}{a = a} dClo (pPa, pMax) (Qqpa, qMax) 
                    = (( dClo _ _ (compose g (compose f a)) 
                                   (compose f a) 
                                   (Evidence g (\ x => Refl))
                                   pPa
                       , Qqpa)
                      , \ n' => \ f' => \ pr' => qMax _ f' (snd pr')) 


-- failure propagation lemma

failurePropagation1 : Nothing (Ext p f) -> Nothing (Ext (p .&. q) f)
failurePropagation1 nf n g contra = nf _ g (fst contra)

failurePropagation2 : Max {m = m}(Ext p a) n f     -> 
                      Nothing (Ext q (compose f a)) -> 
                      Nothing (Ext (p .&. q) a)
failurePropagation2 {m = m}{n = n}{f = f} (pf, ff) nQfa _ h (pa , qa) with (ff _ h pa)
  failurePropagation2 {m = m}{n = n}{f = f} (pf, ff) nQfa _ h (pa , qa) | (Evidence x y) 
                      = nQfa _ x ?rhs


