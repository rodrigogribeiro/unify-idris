module Unify

import Data.Fin

%default total

-- Term syntax

data Term : (n : Nat) -> Type where
  Var   : (v : Fin n) -> Term n
  Leaf  : Term n
  (:@:) : (l : Term n) -> (r : Term n) -> Term n 

infixl 4 :@:
      
map : (Fin m -> Fin n) -> Fin m -> Term n
map f v = Var (f v)

bind : (Fin m -> Term n) -> Term m -> Term n
bind f (Var v) = f v
bind f Leaf = Leaf
bind f (l :@: r) = (bind f l) :@: (bind f r)

compose : (Fin m -> Term n) -> (Fin l -> Term m) -> Fin l -> Term n
compose f g v = bind f (g v)

-- thin

thin : Fin (S n) -> Fin n -> Fin (S n)
thin FZ y = FS y
thin (FS x) FZ = FZ
thin (FS x) (FS y) = FS (thin x y)

-- thick

data Thick : (x : Fin (S n)) -> Fin (S n) -> Type where
  Ok    : (y : Fin n) -> Thick x (thin x y)
  NotOk : Thick x x


thick : (x : Fin (S n)) -> (y : Fin (S n)) -> Thick x y
thick FZ FZ = NotOk 
thick FZ (FS y) = Ok y 
thick {n = Z} (FS x) y = FinZElim x
thick {n = (S k)} (FS x) FZ = Ok FZ
thick {n = (S k)} (FS x) (FS y) with (thick x y)
  thick {n = (S k)} (FS x) (FS (thin x z)) | (Ok z) = Ok (FS z)
  thick {n = (S k)} (FS x) (FS x) | NotOk = NotOk
  
forr : Term n -> Fin (S n) -> Fin (S n) -> Term n
forr t x y  with (thick x y)
  forr t x (thin x z)  | (Ok z) = Var z
  forr t x x           | NotOk  = t
  
-- Occurs

data Occurs : (x : Fin (S n)) -> Term (S n) -> Type where
  OccVar  : Occurs x (Var x)
  OccAppL : (s : Occurs x l) -> Occurs x (l :@: r)
  OccAppR : (s : Occurs x r) -> Occurs x (l :@: r) 

-- Check

data Check : (x : Fin (S n)) -> Term (S n) -> Type where
  CheckOk    : (c : Term n) -> Check x (bind (map (thin x)) c)
  CheckNotOk : (p : Occurs x t) -> Check x t
  
  
check : (x : Fin (S n)) -> (t : Term (S n)) -> Check x t
check x (Var v) with (thick x v)
  check x (Var (thin x y)) | (Ok y) = CheckOk (Var y)
  check x (Var x) | NotOk = CheckNotOk OccVar
check x Leaf = CheckOk Leaf
check x (l :@: r) with (check x l)
  check x ((bind (map (thin x)) c) :@: r) | (CheckOk c) with (check x r)
    check x ((bind (map (thin x)) c) :@: (bind (map (thin x)) y)) | (CheckOk c) | (CheckOk y) 
      = CheckOk (c :@: y)
    check x ((bind (map (thin x)) c) :@: r) | (CheckOk c) | (CheckNotOk p) 
      = CheckNotOk (OccAppR p)
  check x (l :@: r) | (CheckNotOk p) = CheckNotOk (OccAppL p)


-- substitution definition

data AList : (n : Nat) -> (m : Nat) -> Type where
  Nil  : AList n n
  Snoc : (as : AList m n) -> 
         (t : Term m) -> 
         (v : Fin (S m)) -> AList (S m) n


comp : AList m n -> AList l m -> AList l n
comp as [] = as
comp as (Snoc bs t v) = Snoc (comp as bs) t v


sub : AList m n -> Fin m -> Term n
sub [] = Var
sub (Snoc as t v) = compose (sub as) (forr t v)


-- unification

flexFlex : (x : Fin m) -> (y : Fin m) -> Sigma Nat (\n => AList m n)
flexFlex {m = Z} x y = FinZElim x
flexFlex {m = (S k)} x y with (thick x y)
  flexFlex {m = (S k)} x (thin x z) | (Ok z) = MkSigma _ (Snoc [] (Var z) x)
  flexFlex {m = (S k)} x x          | NotOk  = MkSigma _ [] 


flexRigid : Fin m -> Term m -> Maybe (Sigma Nat (\n => AList m n))
flexRigid {m = Z} v t = FinZElim v
flexRigid {m = (S k)} v t with (check v t)
  flexRigid {m = (S k)} v (bind (map (thin v)) c) | (CheckOk c) = Just (MkSigma _ (Snoc [] c v))
  flexRigid {m = (S k)} v t | (CheckNotOk p)                    = Nothing


amgu : Term m -> Term m -> Sigma Nat (\n => AList m n) -> Maybe (Sigma Nat (\n => AList m n))
amgu Leaf Leaf xs = Just xs
amgu Leaf (t :@: t') xs = Nothing
amgu (s :@: s') Leaf xs = Nothing
amgu (s :@: s') (t :@: t') xs = amgu s t xs >>= amgu s' t'
amgu (Var x) (Var y) (n ** ps) = Just (flexFlex x y)
amgu (Var x) t (m ** []) = flexRigid x t
amgu s (Var y) (m ** []) = flexRigid y s
amgu {m = S m'} s t (n ** (Snoc xs x v)) with (amgu (bind (forr x v) s)
                                                    (bind (forr x v) t)
                                                    (MkSigma _ xs))
  amgu {m = S m'} s t (n ** (Snoc xs x v)) | Nothing = Nothing
  amgu {m = S m'} s t (n ** (Snoc xs x v)) | (Just (MkSigma _ k)) 
                      = Just (MkSigma _ (Snoc k x v))
                                 

mgu : Term m -> Term m -> Maybe (Sigma Nat (\n => AList m n))
mgu s t = amgu s t (MkSigma _ []) 
