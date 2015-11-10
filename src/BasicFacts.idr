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
