module Unify

import Data.Fin

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
