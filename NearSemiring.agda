module NearSemiring where 

open import Data.Nat hiding (_≟_)
open import Basics
open import Data.Empty
open import Data.Product

open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

data ListT (A : Set) : Set where
  Last : A -> A -> ListT A
  _∷_ : A -> ListT A -> ListT A

_++_ : forall {A : Set} -> ListT A -> ListT A -> ListT A
(Last a b) ++ y = a ∷ (b ∷ y)
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

data NSR (A : Set) : Set where
  nil : NSR A
  cons : A -> NSR A -> NSR A
  br : ListT (NSR A) -> NSR A

consEnd : forall {A : Set} -> ListT A -> A -> ListT A
consEnd (Last x y) z = x ∷ (Last y z)
consEnd (x ∷ xs)   z = x ∷ (consEnd xs z)

mutual
  _•_ : forall {A : Set} -> NSR A -> NSR A -> NSR A
  nil • x = x
  cons x xs • ys = cons x (xs • ys)
  br bs • y = br (lmap bs y)   

  lmap : forall {A : Set} -> ListT (NSR A) -> NSR A -> ListT (NSR A)
  lmap (Last nil nil) (br b) = b ++ b
  lmap (Last nil y)   (br b) = consEnd b (y • (br b))
  lmap (Last x nil)   (br b) = (x • (br b)) ∷ b
  lmap (Last x y)     b      = Last (x • b) (y • b)
  lmap (nil ∷ xs) (br b)     = b ++ (lmap xs (br b))
  lmap (x ∷ xs) b            = (x • b) ∷ (lmap xs b)

klist_assoc : forall {A : Set} {x y z : ListT A} -> (x ++ (y ++ z)) ≡ ((x ++ y) ++ z)
klist_assoc {x = Last a b} = refl
klist_assoc {x = x ∷ xs} {y} {z} rewrite klist_assoc {x = xs} {y = y} {z = z} = refl 



consEndDistrib : forall {A : Set} {x y : ListT A} {z : A} -> consEnd (x ++ y) z ≡ x ++ (consEnd y z)
consEndDistrib {x = Last x y} = refl
consEndDistrib {x = x ∷ xs} = cong (\w -> x ∷ w) (consEndDistrib {x = xs})

consDoub : forall {A : Set} {xs : ListT A} {a b : A} -> consEnd (consEnd xs a) b ≡ xs ++ Last a b
consDoub {xs = Last x xy} = refl
consDoub {xs = x ∷ xs} = cong (\w -> x ∷ w) (consDoub {xs = xs})



postulate
  brInj : ∀ {A : Set} {x y : ListT (NSR A)} -> (br x ≡ br y) -> (x ≡ y)

_⊕_ : forall {A : Set} -> NSR A -> NSR A -> NSR A
(br x) ⊕ (br y) = br (x ++ y) -- (Last (br x) (br y)) -- (x ++ y) 
(br x) ⊕ y      = br (consEnd x y)
x      ⊕ (br y) = br (x ∷ y)
x ⊕ y           = br (Last x y)



mutual 

  lmapUnit : forall {A : Set} {l : ListT (NSR A)} -> lmap l nil ≡ l
  lmapUnit {l = Last nil nil} = refl
  lmapUnit {l = Last nil (cons x y)} rewrite (unitR {f = y}) = refl
  lmapUnit {l = Last nil (br x)} rewrite lmapUnit {l = x} = refl
  lmapUnit {l = Last (cons x xs) nil} rewrite (unitR {f = xs}) = refl
  lmapUnit {l = Last (cons x xs) (cons y ys)} rewrite (unitR {f = xs}) | (unitR {f = ys}) = refl
  lmapUnit {l = Last (cons x xs) (br y)} rewrite (unitR {f = xs}) | (lmapUnit {l = y}) = refl
  lmapUnit {l = Last (br x) nil} rewrite lmapUnit {l = x} = refl
  lmapUnit {l = Last (br x) (cons y ys)} rewrite (unitR {f = ys}) | (lmapUnit {l = x}) = refl
  lmapUnit {l = Last (br x) (br y)} rewrite (unitR {f = br x}) | unitR {f = br y} = refl 
  lmapUnit {l = nil ∷ xs} rewrite lmapUnit {l = xs} = refl
  lmapUnit {l = (cons x xs) ∷ ys} rewrite (unitR {f = xs}) | lmapUnit {l = ys} = refl
  lmapUnit {l = br x ∷ xs} rewrite (lmapUnit {l = x}) | lmapUnit {l = xs} = refl

--  lmapAppendDistrib : forall {bs : ListT (NSR A)   lmap (x ∷ (f ++ gs)) (br 

  unitR : forall {A : Set} {f : NSR A} -> f • nil ≡ f
  unitR {f = nil} = refl
  unitR {f = cons x xs} = cong (\z -> cons x z) (unitR {f = xs})
  unitR {f = br xs} rewrite lmapUnit {l = xs} = refl

lemma : forall {A : Set} {x : ListT (NSR A)} -> lmap (consEnd x nil) nil ≡ (consEnd (lmap x nil) nil)
lemma {_} {x} rewrite (lmapUnit {l = consEnd x nil}) | lmapUnit {l = x} = refl

lemma2 : forall {A : Set} {x : ListT (NSR A)} {y : A} {ys : NSR A} -> lmap (consEnd x nil) (cons y ys) ≡ consEnd (lmap x (cons y ys)) (cons y ys)
lemma2 {x = Last nil nil} = refl
lemma2 {x = Last nil (cons x b)} {ys = nil} = refl
lemma2 {x = Last nil (cons x b)} {ys = cons x₁ ys} = refl
lemma2 {x = Last nil (cons x b)} {ys = br x₁} = refl
lemma2 {x = Last nil (br x)} = refl
lemma2 {x = Last (cons x a) nil} = refl
lemma2 {x = Last (cons x a) (cons x₁ b)} = refl
lemma2 {x = Last (cons x a) (br x₁)} = refl
lemma2 {x = Last (br x) nil} = refl
lemma2 {x = Last (br x) (cons x₁ b)} = refl
lemma2 {x = Last (br x) (br x₁)} = refl
lemma2 {x = nil ∷ xs} {y} {ys} rewrite lemma2 {x = xs} {y} {ys} = refl 
lemma2 {x = (cons z zs) ∷ xs} {y} {ys} rewrite lemma2 {x = xs} {y} {ys} = refl
lemma2 {x = br x ∷ xs} {y} {ys } rewrite lemma2 {x = xs} {y} {ys} = refl

consEndLemma : forall {A : Set} {y : NSR A} {b : ListT (NSR A)} {c : ListT (NSR A)} -> b ++ (y ∷ c) ≡ ((consEnd b y) ++ c)
consEndLemma {b = Last x x₁} = refl
consEndLemma {y = y} {b = x ∷ xs} {c} rewrite consEndLemma {y = y} {b = xs} {c = c} = refl


distribR : {A : Set} {f h : ListT (NSR A)} -> (((br f) ⊕ nil) • (br h)) ≡ ((br f) • (br h)) ⊕ (br h)
distribR {f = Last nil nil} {h = h} rewrite klist_assoc {x = h} {y = h} {z = h} = refl
distribR {f = Last nil (cons x b)} {h = h} rewrite consEndLemma {y = cons x (b • br h)} {b = h} {c = h} = refl
distribR {f = Last nil (br x)} {h = h} rewrite consEndLemma {y = br (lmap x (br h))} {b = h} {c = h} = refl
distribR {f = Last (cons x a) nil} = refl
distribR {f = Last (cons x a) (cons x₁ b)} = refl
distribR {f = Last (cons x a) (br x₁)} = refl
distribR {f = Last (br x) nil} = refl
distribR {f = Last (br x) (cons x₁ b)} = refl
distribR {f = Last (br x) (br y)} = refl
distribR {f = nil ∷ xs} {Last x y} = let ih = distribR {f = xs} {h = Last x y} 
                                         ih' = cong (\z -> br (x ∷ (y ∷ z))) (brInj ih)
                                     in ih'
distribR {f = cons x xs ∷ ys} {Last y z} = let ih = distribR {f = ys} {h = Last y z}
                                             in cong (\w -> br ((cons x (xs • br (Last y z))) ∷ w)) (brInj ih)
distribR {f = br x ∷ xs} {Last y z} = let ih = distribR {f = xs} {h = Last y z}
                                      in cong (\w -> br (br (lmap x (br (Last y z))) ∷ w)) (brInj ih)

distribR {f = nil ∷ xs} {h ∷ hs} rewrite symm (klist_assoc {x = hs} {y = lmap xs (br (h ∷ hs))} {z = (h ∷ hs)})
                                 = let ih = distribR {f = xs} {h = h ∷ hs} 
                                       ih' = cong (\w -> br (h ∷ (hs ++ w))) (brInj ih)
                                   in ih'
distribR {f = cons y ys ∷ xs} {h ∷ hs} = let ih = distribR {f = xs} {h = h ∷ hs}
                                             ih' = cong (\w -> br (cons y (ys • br (h ∷ hs)) ∷ w)) (brInj ih)
                                         in ih'
distribR {f = br x ∷ xs} {h ∷ hs} = let ih = distribR {f = xs} {h = h ∷ hs}
                                        ih' = cong (\w -> br (br (lmap x (br (h ∷ hs))) ∷ w)) (brInj ih)
                                    in ih'

distribR2 : {A : Set} {f : ListT (NSR A)} {g h : NSR A} -> (((br f) ⊕ g) • h) ≡ ((br f) • h) ⊕ (g • h)
distribR2 {f = f} {g} {h = nil} rewrite (unitR {f = br f ⊕ g}) | (unitR {f = g}) | (lmapUnit {l = f}) = refl
distribR2 {f = Last nil nil} {nil} {cons x xs} = refl
distribR2 {f = Last nil (cons x b)} {nil} {cons x₁ xs} = refl
distribR2 {f = Last nil (br x)} {nil} {cons x₁ xs} = refl
distribR2 {f = Last (cons x a) nil} {nil} {cons x₁ xs} = refl
distribR2 {f = Last (cons x a) (cons x₁ b)} {nil} {cons x₂ xs} = refl
distribR2 {f = Last (cons x a) (br x₁)} {nil} {cons x₂ xs} = refl
distribR2 {f = Last (br x) nil} {nil} {cons x₁ xs} = refl
distribR2 {f = Last (br x) (cons x₁ b)} {nil} {cons x₂ xs} = refl
distribR2 {f = Last (br x) (br x₁)} {nil} {cons x₂ xs} = refl
distribR2 {f = Last nil nil} {cons y ys} {cons x xs} = refl
distribR2 {f = Last nil (cons x b)} {cons y ys} {cons x₁ xs} = refl
distribR2 {f = Last nil (br x)} {cons y ys} {cons x₁ xs} = refl
distribR2 {f = Last (cons x a) nil} {cons y ys} {cons x₁ xs} = refl
distribR2 {f = Last (cons x a) (cons x₁ b)} {cons y ys} {cons x₂ xs} = refl
distribR2 {f = Last (cons x a) (br x₁)} {cons y ys} {cons x₂ xs} = refl
distribR2 {f = Last (br x) nil} {cons y ys} {cons x₁ xs} = refl
distribR2 {f = Last (br x) (cons x₁ b)} {cons y ys} {cons x₂ xs} = refl
distribR2 {f = Last (br x) (br x₁)} {cons y ys} {cons x₂ xs} = refl
distribR2 {f = Last nil nil} {br bs} {cons x xs} = refl
distribR2 {f = Last nil (cons x b)} {br bs} {cons x₁ xs} = refl
distribR2 {f = Last nil (br x)} {br bs} {cons x₁ xs} = refl
distribR2 {f = Last (cons x a) nil} {br bs} {cons x₁ xs} = refl
distribR2 {f = Last (cons x a) (cons x₁ b)} {br bs} {cons x₂ xs} = refl
distribR2 {f = Last (cons x a) (br x₁)} {br bs} {cons x₂ xs} = refl
distribR2 {f = Last (br x) nil} {br bs} {cons x₁ xs} = refl
distribR2 {f = Last (br x) (cons x₁ b)} {br bs} {cons x₂ xs} = refl
distribR2 {f = Last (br x) (br x₁)} {br bs} {cons x₂ xs} = refl
distribR2 {f = nil ∷ f} {nil} {cons y ys} rewrite lemma2 {x = f} {y = y} {ys = ys} = refl 
distribR2 {f = nil ∷ f} {cons x xs} {cons y ys} = let ih2 = distribR2 {f = f} {g = cons x xs} {h = cons y ys} 
                                                  in cong (\z -> br (cons y ys ∷ z)) (brInj ih2)
distribR2 {f = nil ∷ f} {br x} {cons y ys} = let ih2 = distribR2 {f = f} {g = br x} {h = cons y ys} 
                                             in cong (\z -> br (cons y ys ∷ z)) (brInj ih2)
distribR2 {f = cons x xs ∷ f} {nil} {cons y ys} = let ih = distribR2 {f = f} {g = nil} {h = cons y ys}
                                                  in cong (\z -> br (cons x (xs • cons y ys) ∷ z)) (brInj ih)
distribR2 {f = cons x xs ∷ f} {cons g gs} {cons y ys} = 
                                                  let ih = distribR2 {f = f} {g = cons g gs} {h = cons y ys}
                                                  in cong (\z -> br (cons x (xs • cons y ys) ∷ z)) (brInj ih)
distribR2 {f = cons x xs ∷ f} {br bs} {cons y ys} = let ih = distribR2 {f = f} {g = br bs} {h = cons y ys}
                                                    in cong (\z -> br (cons x (xs • cons y ys) ∷ z)) (brInj ih)
distribR2 {f = br x ∷ f} {nil} {cons y ys} rewrite lemma2 {x = f} {y = y} {ys = ys} = refl
distribR2 {f = br x ∷ f} {cons g gs} {cons y ys} = let ih = distribR2 {f = f} {g = cons g gs} {cons y ys} 
                                                   in cong (\z -> br (br (lmap x (cons y ys)) ∷ z)) (brInj ih)
distribR2 {f = br a ∷ f} {br b} {cons y ys} = let ih = distribR2 {f = f} {g = br b} {cons y ys}
                                              in cong (\z -> br (br (lmap a (cons y ys)) ∷ z)) (brInj ih)
distribR2 {f = Last nil nil} {nil} {br (Last a b)} = refl
distribR2 {f = Last nil (cons x v)} {nil} {br (Last a b)} = refl
distribR2 {f = Last nil (br x)} {nil} {br (Last a b)} = refl
distribR2 {f = Last (cons x u) nil} {nil} {br (Last a b)} = refl
distribR2 {f = Last (cons x u) (cons x₁ v)} {nil} {br (Last a b)} = refl
distribR2 {f = Last (cons x u) (br x₁)} {nil} {br (Last a b)} = refl
distribR2 {f = Last (br x) nil} {nil} {br (Last a b)} = refl
distribR2 {f = Last (br x) (cons x₁ v)} {nil} {br (Last a b)} = refl
distribR2 {f = Last (br x) (br x₁)} {nil} {br (Last a b)} = refl
distribR2 {f = Last nil nil} {cons x₂ g} {br (Last a b)} = refl
distribR2 {f = Last nil (cons x v)} {cons x₂ g} {br (Last a b)} = refl
distribR2 {f = Last nil (br x)} {cons x₂ g} {br (Last a b)} = refl
distribR2 {f = Last (cons x u) nil} {cons x₂ g} {br (Last a b)} = refl
distribR2 {f = Last (cons x u) (cons x₁ v)} {cons x₂ g} {br (Last a b)} = refl
distribR2 {f = Last (cons x u) (br x₁)} {cons x₂ g} {br (Last a b)} = refl
distribR2 {f = Last (br x) nil} {cons x₂ g} {br (Last a b)} = refl
distribR2 {f = Last (br x) (cons x₁ v)} {cons x₂ g} {br (Last a b)} = refl
distribR2 {f = Last (br x) (br x₁)} {cons x₂ g} {br (Last a b)} = refl
distribR2 {f = Last nil nil} {br x₂} {br (Last a b)} = refl
distribR2 {f = Last nil (cons x v)} {br x₂} {br (Last a b)} = refl
distribR2 {f = Last nil (br x)} {br x₂} {br (Last a b)} = refl
distribR2 {f = Last (cons x u) nil} {br x₂} {br (Last a b)} = refl
distribR2 {f = Last (cons x u) (cons x₁ v)} {br x₂} {br (Last a b)} = refl
distribR2 {f = Last (cons x u) (br x₁)} {br x₂} {br (Last a b)} = refl
distribR2 {f = Last (br x) nil} {br x₂} {br (Last a b)} = refl
distribR2 {f = Last (br x) (cons x₁ v)} {br x₂} {br (Last a b)} = refl
distribR2 {f = Last (br x) (br x₁)} {br x₂} {br (Last a b)} = refl
distribR2 {f = nil ∷ f} {nil} {br (Last y z)} = let ih = distribR2 {f = f} {g = nil} {h = br (Last y z)}
                                                in cong (\w -> br (y ∷ (z ∷ w))) (brInj ih)
distribR2 {f = (cons x xs) ∷ f} {nil} {br (Last a b)} = let ih = distribR2 {f = f} {g = nil} {h = br (Last a b)}
                                                        in cong (\w -> br (cons x (xs • br (Last a b)) ∷ w)) (brInj ih)
distribR2 {f = br x ∷ f} {nil} {br (Last a b)} = let ih = distribR2 {f = f} {g = nil} {h = br (Last a b)}
                                                 in cong (\w -> br (br (lmap x (br (Last a b))) ∷ w)) (brInj ih)

distribR2 {f = nil ∷ f} {cons x xs} {br (Last a b)} = let ih = distribR2 {f = f} {g = cons x xs} {h = br (Last a b)}
                                                      in cong (\w -> br (a ∷ (b ∷ w))) (brInj ih)
distribR2 {f = (cons y ys) ∷ f} {cons x xs} {br (Last a b)} = let ih = distribR2 {f = f} {g = cons x xs} {h = br (Last a b)}
                                                              in cong (\w -> br (cons y (ys • br (Last a b)) ∷ w)) (brInj ih)
distribR2 {f = br bs ∷ f} {cons x xs} {br (Last a b)} = let ih = distribR2 {f = f} {g = cons x xs} {h = br (Last a b)}
                                                        in cong (\w -> br (br (lmap bs (br (Last a b))) ∷ w)) (brInj ih)

distribR2 {f = nil ∷ f} {br bs} {br (Last a b)} = let ih = distribR2 {f = f} {g = br bs} {h = br (Last a b)}
                                                  in cong (\w -> br (a ∷ (b ∷ w))) (brInj ih)
distribR2 {f = cons y ys ∷ f} {br bs} {br (Last a b)} = let ih = distribR2 {f = f} {g = br bs} {h = br (Last a b)}
                                                        in cong (\w -> br (cons y (ys • br (Last a b)) ∷ w)) (brInj ih)
distribR2 {f = br bs ∷ f} {br gbs} {br (Last a b)} = let ih = distribR2 {f = f} {g = br gbs} {h = br (Last a b)}
                                                     in cong (\w -> br (br (lmap bs (br (Last a b))) ∷ w)) (brInj ih)
distribR2 {f = Last nil nil} {nil} {br (h ∷ hs)} rewrite klist_assoc {x = hs} {y = h ∷ hs} {z = h ∷ hs} = refl
distribR2 {f = Last nil (cons x b)} {nil} {br (h ∷ hs)} rewrite consEndLemma {y = cons x (b • br (h ∷ hs))} {b = hs} {c = h ∷ hs} = refl
distribR2 {f = Last nil (br x)} {nil} {br (h ∷ hs)} rewrite consEndLemma {y = br (lmap x (br (h ∷ hs)))} {b = hs} {c = h ∷ hs} = refl
distribR2 {f = Last (cons x a) nil} {nil} {br (h ∷ hs)} = refl
distribR2 {f = Last (cons x a) (cons x₁ b)} {nil} {br (h ∷ hs)} = refl
distribR2 {f = Last (cons x a) (br x₁)} {nil} {br (h ∷ hs)} = refl
distribR2 {f = Last (br x) nil} {nil} {br (h ∷ hs)} = refl
distribR2 {f = Last (br x) (cons x₁ b)} {nil} {br (h ∷ hs)} = refl
distribR2 {f = Last (br x) (br x₁)} {nil} {br (h ∷ hs)} = refl
distribR2 {f = Last nil nil} {cons g gs} {br (nil ∷ hs)} rewrite consEndDistrib {x = hs} {y = nil ∷ hs} {z = cons g (gs • br (nil ∷ hs))} = refl
distribR2 {f = Last nil (cons x b)} {cons g gs} {br (nil ∷ hs)} rewrite consDoub {xs = hs} {a = cons x (b • br (nil ∷ hs))} {b = cons g (gs • br (nil ∷ hs))} = refl
distribR2 {f = Last nil (br x)} {cons g gs} {br (nil ∷ hs)} rewrite consDoub {xs = hs} {a = br (lmap x (br (nil ∷ hs)))} {b = cons g (gs • br (nil ∷ hs))} = refl
distribR2 {f = Last (cons x a) nil} {cons g gs} {br (nil ∷ hs)} = refl
distribR2 {f = Last (cons x a) (cons x₁ b)} {cons g gs} {br (nil ∷ hs)} = refl
distribR2 {f = Last (cons x a) (br x₁)} {cons g gs} {br (nil ∷ hs)} = refl
distribR2 {f = Last (br x) nil} {cons g gs} {br (nil ∷ hs)} = refl
distribR2 {f = Last (br x) (cons x₁ b)} {cons g gs} {br (nil ∷ hs)} = refl
distribR2 {f = Last (br x) (br x₁)} {cons g gs} {br (nil ∷ hs)} = refl
distribR2 {f = Last nil nil} {cons g gs} {br (cons x h ∷ hs)} rewrite consEndDistrib {x = hs} {y = cons x h ∷ hs} {z = cons g (gs • br (cons x h ∷ hs))} = refl
distribR2 {f = Last nil (cons x b)} {cons g gs} {br (cons x₁ h ∷ hs)} rewrite consDoub {xs = hs} {a = cons x (b • br (cons x₁ h ∷ hs))} {b = cons g (gs • br (cons x₁ h ∷ hs))} = refl
distribR2 {f = Last nil (br x)} {cons g gs} {br (cons x₁ h ∷ hs)} rewrite consDoub {xs = hs} {a = br (lmap x (br (cons x₁ h ∷ hs)))} {b = cons g (gs • br (cons x₁ h ∷ hs))} = refl
distribR2 {f = Last (cons x a) nil} {cons g gs} {br (cons x₁ h ∷ hs)} = refl
distribR2 {f = Last (cons x a) (cons x₁ b)} {cons g gs} {br (cons x₂ h ∷ hs)} = refl
distribR2 {f = Last (cons x a) (br x₁)} {cons g gs} {br (cons x₂ h ∷ hs)} = refl
distribR2 {f = Last (br x) nil} {cons g gs} {br (cons x₁ h ∷ hs)} = refl
distribR2 {f = Last (br x) (cons x₁ b)} {cons g gs} {br (cons x₂ h ∷ hs)} = refl
distribR2 {f = Last (br x) (br x₁)} {cons g gs} {br (cons x₂ h ∷ hs)} = refl
distribR2 {f = Last nil nil} {cons g gs} {br (br x ∷ hs)} rewrite consEndDistrib {x = hs} {y = (br x ∷ hs)} {z = cons g (gs • br (br x ∷ hs))} = refl
distribR2 {f = Last nil (cons x b)} {cons g gs} {br (br x₁ ∷ hs)} rewrite consDoub {xs = hs} {a = cons x (b • br (br x₁ ∷ hs))} {b = cons g (gs • br (br x₁ ∷ hs))} = refl
distribR2 {f = Last nil (br x)} {cons g gs} {br (br x₁ ∷ hs)} rewrite consDoub {xs = hs} {a = br (lmap x (br (br x₁ ∷ hs)))} {b = cons g (gs • br (br x₁ ∷ hs))} = refl
distribR2 {f = Last (cons x a) nil} {cons g gs} {br (br x₁ ∷ hs)} = refl
distribR2 {f = Last (cons x a) (cons x₁ b)} {cons g gs} {br (br x₂ ∷ hs)} = refl
distribR2 {f = Last (cons x a) (br x₁)} {cons g gs} {br (br x₂ ∷ hs)} = refl
distribR2 {f = Last (br x) nil} {cons g gs} {br (br x₁ ∷ hs)} = refl
distribR2 {f = Last (br x) (cons x₁ b)} {cons g gs} {br (br x₂ ∷ hs)} = refl
distribR2 {f = Last (br x) (br x₁)} {cons g gs} {br (br x₂ ∷ hs)} = refl
distribR2 {f = Last nil nil} {br gs} {br (h ∷ hs)} rewrite klist_assoc {x = hs} {y = h ∷ hs} {z = lmap gs (br (h ∷ hs))} = refl
distribR2 {f = Last nil (cons x b)} {br gs} {br (h ∷ hs)} rewrite consEndLemma {y = cons x (b • br (h ∷ hs))} {b = hs} {c = lmap gs (br (h ∷ hs))} = refl
distribR2 {f = Last nil (br x)} {br gs} {br (h ∷ hs)} rewrite consEndLemma {y = br (lmap x (br (h ∷ hs)))} {b = hs} {c = lmap gs (br (h ∷ hs))} = refl
distribR2 {f = Last (cons x a) nil} {br gs} {br (h ∷ hs)} = refl
distribR2 {f = Last (cons x a) (cons x₁ b)} {br gs} {br (h ∷ hs)} = refl
distribR2 {f = Last (cons x a) (br x₁)} {br gs} {br (h ∷ hs)} = refl
distribR2 {f = Last (br x) nil} {br gs} {br (h ∷ hs)} = refl
distribR2 {f = Last (br x) (cons x₁ b)} {br gs} {br (h ∷ hs)} = refl
distribR2 {f = Last (br x) (br x₁)} {br gs} {br (h ∷ hs)} = refl
distribR2 {f = nil ∷ f} {nil} {br (h ∷ hs)} rewrite (symm (klist_assoc {x = hs} {y = lmap f (br (h ∷ hs))} {z = h ∷ hs}))
             = let ih = distribR2 {f = f} {g = nil} {h = br (h ∷ hs)}
               in cong (\w -> br (h ∷ (hs ++ w))) (brInj ih)
distribR2 {f = (cons x xs) ∷ f} {nil} {br (h ∷ hs)} 
             = let ih = distribR2 {f = f} {g = nil} {h = br (h ∷ hs)}
               in cong (\w -> br (cons x (xs • br (h ∷ hs)) ∷ w)) (brInj ih)
distribR2 {f = br x ∷ f} {nil} {br (h ∷ hs)} 
             = let ih = distribR2 {f = f} {g = nil} {h = br (h ∷ hs)}
               in cong (\w -> br (br (lmap x (br (h ∷ hs))) ∷ w)) (brInj ih)
distribR2 {f = nil ∷ f} {cons x₁ g} {br (h ∷ hs)} rewrite consEndDistrib {x = hs} {y = lmap f (br (h ∷ hs))} {z = cons x₁ (g • (br (h ∷ hs)))} = let ih = distribR2 {f = f} {g = cons x₁ g} {h = br (h ∷ hs)}
                      in cong (\w -> br (h ∷ (hs ++ w))) (brInj ih)

distribR2 {f = cons x x₁ ∷ f} {cons x₂ g} {br (h ∷ hs)} = let ih = distribR2 {f = f} {g = cons x₂ g} {h = br (h ∷ hs)}
                                                          in cong (\w -> br (cons x (x₁ • br (h ∷ hs)) ∷ w)) (brInj ih)
distribR2 {f = br x ∷ f} {cons x₁ g} {br (h ∷ hs)} = let ih = distribR2 {f = f} {g = cons x₁ g} {h = br (h ∷ hs)}
                                                     in cong (\w -> br (br (lmap x (br (h ∷ hs))) ∷ w)) (brInj ih)
distribR2 {f = nil ∷ f} {br gs} {br (h ∷ hs)} rewrite symm (klist_assoc {x = hs} {y = lmap f (br (h ∷ hs))} {z = lmap gs (br (h ∷ hs))}) = let ih = distribR2 {f = f} {g = br gs} {h = br (h ∷ hs)} in cong (\w -> br (h ∷ (hs ++ w))) (brInj ih) 
distribR2 {f = cons x x₁ ∷ f} {br gs} {br (h ∷ hs)} = let ih = distribR2 {f = f} {g = br gs} {h = br (h ∷ hs)} 
                                                      in cong (\w -> br (cons x (x₁ • br (h ∷ hs)) ∷ w)) (brInj ih)
distribR2 {f = br x ∷ f} {br gs} {br (h ∷ hs)} = let ih = distribR2 {f = f} {g = br gs} {h = br (h ∷ hs)}
                                                 in cong (\w -> br (br (lmap x (br (h ∷ hs))) ∷ w)) (brInj ih)

distrib : {A : Set} {f g h : NSR A} -> ((f ⊕ g) • h) ≡ (f • h) ⊕ (g • h)
distrib {f = nil} {nil} {nil} = refl
distrib {f = nil} {nil} {cons x xs} rewrite unitR {f = cons x xs} = refl
distrib {f = nil} {nil} {br x} = refl -- rewrite lmapUnit {l = x} = {!!} -- refl 
distrib {f = nil} {cons x xs} {nil} rewrite (unitR {f = xs}) = refl
distrib {f = nil} {cons x xs} {cons y ys} = refl
distrib {f = nil} {cons x xs} {br (Last a b)} = refl
distrib {f = nil} {cons x xs} {br (y ∷ ys)} = refl
distrib {f = nil} {br x} {nil} = refl
distrib {f = nil} {br x} {cons x₁ h} = refl
distrib {f = nil} {br x} {br x₁} = refl
distrib {f = cons x f} {nil} {nil} = refl
distrib {f = cons x f} {nil} {cons x₁ h} = refl
distrib {f = cons x f} {nil} {br x₁} = refl
distrib {f = cons x f} {cons x₁ g} {nil} = refl
distrib {f = cons x f} {cons x₁ g} {cons x₂ h} = refl
distrib {f = cons x f} {cons x₁ g} {br x₂} = refl
distrib {f = cons x f} {br x₁} {nil} = refl
distrib {f = cons x f} {br x₁} {cons x₂ h} = refl
distrib {f = cons x f} {br x₁} {br x₂} = refl
distrib {f = br f} {nil} {br h} = distribR {f = f} {h = h}
distrib {f = br x} {nil} {nil} rewrite lemma {x = x} = refl
distrib {f = br x} {nil} {cons y ys} rewrite lemma2 {x = x} {y = y} {ys = ys} = refl
distrib {f = br x} {g = g} {h = h} = distribR2 {f = x} {g = g} {h = h}

{-
lmap_assoc : {A : Set} {x : ListT (NSR A)} {y z : NSR A} -> lmap (lmap x y) z ≡ lmap x (y • z)
lmap_assoc {x = Last nil nil} {nil} {nil} = refl
lmap_assoc {x = Last nil nil} {nil} {cons x z} = refl
lmap_assoc {x = Last nil nil} {nil} {br x} = refl
lmap_assoc {x = Last nil nil} {cons x y} {nil} = refl
lmap_assoc {x = Last nil nil} {cons x y} {cons x₁ z} = refl
lmap_assoc {x = Last nil nil} {cons x y} {br x₁} = refl
lmap_assoc {x = Last nil nil} {br (Last nil nil)} {nil} = refl
lmap_assoc {x = Last nil nil} {br (Last nil (cons x b))} {nil} = refl
lmap_assoc {x = Last nil nil} {br (Last nil (br x))} {nil} = refl
lmap_assoc {x = Last nil nil} {br (Last (cons x a) nil)} {nil} = refl
lmap_assoc {x = Last nil nil} {br (Last (cons x a) (cons x₁ b))} {nil} = refl
lmap_assoc {x = Last nil nil} {br (Last (cons x a) (br x₁))} {nil} = refl
lmap_assoc {x = Last nil nil} {br (Last (br x) nil)} {nil} = refl
lmap_assoc {x = Last nil nil} {br (Last (br x) (cons x₁ b))} {nil} = refl
lmap_assoc {x = Last nil nil} {br (Last (br x) (br x₁))} {nil} = refl
lmap_assoc {x = Last nil nil} {br (nil ∷ xs)} {nil} = let ih = lmap_assoc {x = Last nil nil} {y = br xs} {z = nil} 
                                                      in {!!}
lmap_assoc {x = Last nil nil} {br (cons x x₁ ∷ xs)} {nil} = {!!}
lmap_assoc {x = Last nil nil} {br (br x ∷ xs)} {nil} = {!!}
lmap_assoc {x = Last nil nil} {br x} {cons x₁ z} = {!!}
lmap_assoc {x = Last nil nil} {br x} {br x₁} = {!!}
lmap_assoc {x = Last nil (cons x b)} {nil} {nil} = {!!}
lmap_assoc {x = Last nil (cons x b)} {nil} {cons x₁ z} = {!!}
lmap_assoc {x = Last nil (cons x b)} {nil} {br x₁} = {!!}
lmap_assoc {x = Last nil (cons x b)} {cons x₁ y} {nil} = {!!}
lmap_assoc {x = Last nil (cons x b)} {cons x₁ y} {cons x₂ z} = {!!}
lmap_assoc {x = Last nil (cons x b)} {cons x₁ y} {br x₂} = {!!}
lmap_assoc {x = Last nil (cons x b)} {br x₁} {nil} = {!!}
lmap_assoc {x = Last nil (cons x b)} {br x₁} {cons x₂ z} = {!!}
lmap_assoc {x = Last nil (cons x b)} {br x₁} {br x₂} = {!!}
lmap_assoc {x = Last nil (br x)} {nil} {nil} = {!!}
lmap_assoc {x = Last nil (br x)} {nil} {cons x₁ z} = {!!}
lmap_assoc {x = Last nil (br x)} {nil} {br x₁} = {!!}
lmap_assoc {x = Last nil (br x)} {cons x₁ y} {nil} = {!!}
lmap_assoc {x = Last nil (br x)} {cons x₁ y} {cons x₂ z} = {!!}
lmap_assoc {x = Last nil (br x)} {cons x₁ y} {br x₂} = {!!}
lmap_assoc {x = Last nil (br x)} {br x₁} {nil} = {!!}
lmap_assoc {x = Last nil (br x)} {br x₁} {cons x₂ z} = {!!}
lmap_assoc {x = Last nil (br x)} {br x₁} {br x₂} = {!!}
lmap_assoc {x = Last (cons x a) nil} {nil} {nil} = {!!}
lmap_assoc {x = Last (cons x a) nil} {nil} {cons x₁ z} = {!!}
lmap_assoc {x = Last (cons x a) nil} {nil} {br x₁} = {!!}
lmap_assoc {x = Last (cons x a) nil} {cons x₁ y} {nil} = {!!}
lmap_assoc {x = Last (cons x a) nil} {cons x₁ y} {cons x₂ z} = {!!}
lmap_assoc {x = Last (cons x a) nil} {cons x₁ y} {br x₂} = {!!}
lmap_assoc {x = Last (cons x a) nil} {br x₁} {nil} = {!!}
lmap_assoc {x = Last (cons x a) nil} {br x₁} {cons x₂ z} = {!!}
lmap_assoc {x = Last (cons x a) nil} {br x₁} {br x₂} = {!!}
lmap_assoc {x = Last (cons x a) (cons x₁ b)} {nil} {nil} = {!!}
lmap_assoc {x = Last (cons x a) (cons x₁ b)} {nil} {cons x₂ z} = {!!}
lmap_assoc {x = Last (cons x a) (cons x₁ b)} {nil} {br x₂} = {!!}
lmap_assoc {x = Last (cons x a) (cons x₁ b)} {cons x₂ y} {nil} = {!!}
lmap_assoc {x = Last (cons x a) (cons x₁ b)} {cons x₂ y} {cons x₃ z} = {!!}
lmap_assoc {x = Last (cons x a) (cons x₁ b)} {cons x₂ y} {br x₃} = {!!}
lmap_assoc {x = Last (cons x a) (cons x₁ b)} {br x₂} {nil} = {!!}
lmap_assoc {x = Last (cons x a) (cons x₁ b)} {br x₂} {cons x₃ z} = {!!}
lmap_assoc {x = Last (cons x a) (cons x₁ b)} {br x₂} {br x₃} = {!!}
lmap_assoc {x = Last (cons x a) (br x₁)} {nil} {nil} = {!!}
lmap_assoc {x = Last (cons x a) (br x₁)} {nil} {cons x₂ z} = {!!}
lmap_assoc {x = Last (cons x a) (br x₁)} {nil} {br x₂} = {!!}
lmap_assoc {x = Last (cons x a) (br x₁)} {cons x₂ y} {nil} = {!!}
lmap_assoc {x = Last (cons x a) (br x₁)} {cons x₂ y} {cons x₃ z} = {!!}
lmap_assoc {x = Last (cons x a) (br x₁)} {cons x₂ y} {br x₃} = {!!}
lmap_assoc {x = Last (cons x a) (br x₁)} {br x₂} {nil} = {!!}
lmap_assoc {x = Last (cons x a) (br x₁)} {br x₂} {cons x₃ z} = {!!}
lmap_assoc {x = Last (cons x a) (br x₁)} {br x₂} {br x₃} = {!!}
lmap_assoc {x = Last (br x) nil} {nil} {nil} = {!!}
lmap_assoc {x = Last (br x) nil} {nil} {cons x₁ z} = {!!}
lmap_assoc {x = Last (br x) nil} {nil} {br x₁} = {!!}
lmap_assoc {x = Last (br x) nil} {cons x₁ y} {nil} = {!!}
lmap_assoc {x = Last (br x) nil} {cons x₁ y} {cons x₂ z} = {!!}
lmap_assoc {x = Last (br x) nil} {cons x₁ y} {br x₂} = {!!}
lmap_assoc {x = Last (br x) nil} {br x₁} {nil} = {!!}
lmap_assoc {x = Last (br x) nil} {br x₁} {cons x₂ z} = {!!}
lmap_assoc {x = Last (br x) nil} {br x₁} {br x₂} = {!!}
lmap_assoc {x = Last (br x) (cons x₁ b)} {nil} {nil} = {!!}
lmap_assoc {x = Last (br x) (cons x₁ b)} {nil} {cons x₂ z} = {!!}
lmap_assoc {x = Last (br x) (cons x₁ b)} {nil} {br x₂} = {!!}
lmap_assoc {x = Last (br x) (cons x₁ b)} {cons x₂ y} {nil} = {!!}
lmap_assoc {x = Last (br x) (cons x₁ b)} {cons x₂ y} {cons x₃ z} = {!!}
lmap_assoc {x = Last (br x) (cons x₁ b)} {cons x₂ y} {br x₃} = {!!}
lmap_assoc {x = Last (br x) (cons x₁ b)} {br x₂} {nil} = {!!}
lmap_assoc {x = Last (br x) (cons x₁ b)} {br x₂} {cons x₃ z} = {!!}
lmap_assoc {x = Last (br x) (cons x₁ b)} {br x₂} {br x₃} = {!!}
lmap_assoc {x = Last (br x) (br x₁)} {nil} {nil} = {!!}
lmap_assoc {x = Last (br x) (br x₁)} {nil} {cons x₂ z} = {!!}
lmap_assoc {x = Last (br x) (br x₁)} {nil} {br x₂} = {!!}
lmap_assoc {x = Last (br x) (br x₁)} {cons x₂ y} {nil} = {!!}
lmap_assoc {x = Last (br x) (br x₁)} {cons x₂ y} {cons x₃ z} = {!!}
lmap_assoc {x = Last (br x) (br x₁)} {cons x₂ y} {br x₃} = {!!}
lmap_assoc {x = Last (br x) (br x₁)} {br x₂} {nil} = {!!}
lmap_assoc {x = Last (br x) (br x₁)} {br x₂} {cons x₃ z} = {!!}
lmap_assoc {x = Last (br x) (br x₁)} {br x₂} {br x₃} = {!!}
lmap_assoc {x = x ∷ x₁} = {!!}
-}

{-
assoc : {A : Set} {x y z : NSR A} -> (x • y) • z ≡ x • (y • z)
assoc {x = nil} = refl
assoc {x = cons x xs} = cong (\w -> cons x w) (assoc {x = xs})
assoc {x = br x} = {!!}

-}

postulate 
  assoc : {A : Set} {a b c : NSR A} -> a • (b • c) ≡ (a • b) • c

pureInverseL : {A : Set} {f g : NSR A} -> (f • g ≡ nil) -> (f ≡ nil)
pureInverseL {f = nil} refl = refl
pureInverseL {f = cons x f} ()
pureInverseL {f = br x} ()

pureInverseR : {A : Set} {f g : NSR A} -> (f • g ≡ nil) -> (g ≡ nil)
pureInverseR {f = nil} refl = refl
pureInverseR {f = cons x f} ()
pureInverseR {f = br x} ()