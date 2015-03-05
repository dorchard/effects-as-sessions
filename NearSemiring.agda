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

klist_assoc : forall {A : Set} {x y z : ListT A} -> (x ++ (y ++ z)) ≡ ((x ++ y) ++ z)
klist_assoc {x = Last a b} = refl
klist_assoc {x = x ∷ xs} {y} {z} rewrite klist_assoc {x = xs} {y = y} {z = z} = refl 

--klist_assoc_cons : forall {A : Set} {x 

consEnd : forall {A : Set} -> ListT A -> A -> ListT A
consEnd (Last x y) z = x ∷ (Last y z)
consEnd (x ∷ xs)   z = x ∷ (consEnd xs z)


data NSR (A : Set) : Set where
  nil : NSR A
  cons : A -> NSR A -> NSR A
  br : ListT (NSR A) -> NSR A

postulate
  brInj : ∀ {A : Set} {x y : ListT (NSR A)} -> (br x ≡ br y) -> (x ≡ y)

_⊕_ : forall {A : Set} -> NSR A -> NSR A -> NSR A
(br x) ⊕ (br y) = br (x ++ y) -- (Last (br x) (br y)) -- (x ++ y) 
(br x) ⊕ y      = br (consEnd x y)
x      ⊕ (br y) = br (x ∷ y)
x ⊕ y           = br (Last x y)



mutual 
  _•_ : forall {A : Set} -> NSR A -> NSR A -> NSR A
  nil • x = x
  cons x xs • ys = cons x (xs • ys)
  br bs • y = br (lmap bs y)   


  lmap : forall {A : Set} -> ListT (NSR A) -> NSR A -> ListT (NSR A)
  lmap (Last nil nil) (br b) = b ++ b
  lmap (Last nil y) (br b) = consEnd b (y • (br b))
  lmap (Last x nil) (br b) = (x • (br b)) ∷ b
  lmap (nil ∷ xs) (br b)   = b ++ (lmap xs (br b))
  lmap (Last x y) b = Last (x • b) (y • b)
  lmap (x ∷ xs) b = (x • b) ∷ (lmap xs b)

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

lemma3 : forall {A : Set} {x : ListT (NSR A)} {b : ListT (NSR A)} -> lmap (consEnd x nil) (br b) ≡ consEnd (lmap x (br b)) (br b)
lemma3 = {!!}


consEndLemma : forall {A : Set} {y : NSR A} {b : ListT (NSR A)} {c : ListT (NSR A)} -> b ++ (y ∷ c) ≡ ((consEnd b y) ++ c)
consEndLemma {b = Last x x₁} = refl
consEndLemma {y = y} {b = x ∷ xs} {c} rewrite consEndLemma {y = y} {b = xs} {c = c} = refl

{-
consEndLemma2 : forall {A : Set} {x : NSR A} {xs b : ListT (NSR A)} -> lmap (x ∷ consEnd xs nil) (br b) ≡ lmap (x ∷ xs) (br b) ++ b
consEndLemma2 {x = nil} {Last nil nil} {Last c d} = refl
consEndLemma2 {x = nil} {Last nil (cons x z)} {Last c d} = refl
consEndLemma2 {x = nil} {Last nil (br x)} {Last c d} = refl
consEndLemma2 {x = nil} {Last (cons x y) nil} {Last c d} = refl
consEndLemma2 {x = nil} {Last (cons x y) (cons x₁ z)} {Last c d} = refl
consEndLemma2 {x = nil} {Last (cons x y) (br x₁)} {Last c d} = refl
consEndLemma2 {x = nil} {Last (br x) nil} {Last c d} = refl
consEndLemma2 {x = nil} {Last (br x) (cons x₁ z)} {Last c d} = refl
consEndLemma2 {x = nil} {Last (br x) (br x₁)} {Last c d} = refl
consEndLemma2 {x = nil} {Last nil nil} {x ∷ Last x₁ x₂} = refl
consEndLemma2 {x = nil} {Last nil nil} {x ∷ (x₁ ∷ b)} rewrite consEndLemma2 {x = nil} {xs = Last nil nil} {b = (x₁ ∷ b)} = {!!}
{- 
(b ++ (x :: (b ++ (x :: (b ++ (x :: b))))))



((b ++ (x :: (b ++ (x :: b)))) ++ (x :: b))
-}

consEndLemma2 {x = nil} {Last nil (cons x z)} {x₁ ∷ b} = {!!}
consEndLemma2 {x = nil} {Last nil (br x)} {x₁ ∷ b} = {!!}
consEndLemma2 {x = nil} {Last (cons x y) z} {x₁ ∷ b} = {!!}
consEndLemma2 {x = nil} {Last (br x) z} {x₁ ∷ b} = {!!}
consEndLemma2 {x = cons x x₁} {Last a b} = {!!}
consEndLemma2 {x = br x} {Last a b} = {!!}
consEndLemma2 {xs = x₁ ∷ xs} = {!!}
-}

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

postulate
  distribR2 : {A : Set} {f : ListT (NSR A)} {g h : NSR A} -> (((br f) ⊕ g) • h) ≡ ((br f) • h) ⊕ (g • h)

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
distrib {f = br x} {cons y ys} {nil} = let ih = distrib {f = br x} {g = ys} {h = nil}
                                       in {!!}
distrib {f = br x} {cons x₁ g} {cons x₂ h} = {!!}
distrib {f = br x} {cons x₁ g} {br x₂} = {!!}
distrib {f = br x} {br x₁} {nil} = {!!}
distrib {f = br x} {br x₁} {cons x₂ h} = {!!}
distrib {f = br x} {br x₁} {br x₂} = {!!}
-}
