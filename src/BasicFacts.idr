module BasicFacts

import Data.Fin
import Unify

%default total

cong2 : (f : a -> b -> c) -> x = y -> u = v -> f x u = f y v
cong2 _ Refl Refl = Refl

bindId : (t : Term m) -> bind Var t = t
bindId (Var v) = Refl
bindId Leaf = Refl
bindId (l :@: r) =  cong2 (:@:) (bindId l) (bindId r)
                   
bindCompose : (t : Term m) -> bind (compose f g) t = bind f (bind g t)
bindCompose (Var v) = Refl
bindCompose Leaf = Refl
bindCompose (l :@: r) = cong2 (:@:) (bindCompose l) (bindCompose r)

bindCompose2 : (t : Term m) -> bind (compose h (compose f g)) t = bind (compose h f) (bind g t)
bindCompose2 {g = g} (Var v) = sym (bindCompose (g v))
bindCompose2 Leaf = Refl
bindCompose2 (l :@: r) = cong2 (:@:) (bindCompose2 l) (bindCompose2 r)

trans2 : a = a'-> b = b' -> a = b -> a' = b'
trans2 Refl Refl Refl = Refl
