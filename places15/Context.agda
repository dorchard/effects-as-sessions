module Context where

open import Basics
open import Data.Nat
open import Relation.Binary.PropositionalEquality using (trans;cong;inspect) 

-- Contexts are essentially (snoc) lists
data Context (a : Set) : Set where
     Em   : Context a
     _,_  : (Gam : Context a) (sig : a) -> Context a

{- Standard functions -}
map : forall {a b} -> (a -> b) -> Context a -> Context b
map f Em = Em
map f (xs , x) = (map f xs) , (f x)

length : forall {a} -> Context a -> ℕ
length Em = 0
length (g , _) = 1 + length g

-- Concatentation
_+++_ : forall {a : Set} -> Context a -> Context a -> Context a
xs +++ Em = xs
xs +++ (ys , y) = (xs +++ ys) , y

-- Membership witness
infixr 3 _<:_
data _<:_ {a : Set} (tau : a) : Context a -> Set where
  here  : forall {Gam}                        -> tau <: (Gam , tau)
  there : forall {Gam sig}  (x : tau <: Gam)  -> tau <: (Gam , sig)

-- Shorthand 
th : forall {a : Set} {Gam : Context a} {sig tau : a} (x : tau <: Gam)  -> tau <: (Gam , sig)
th = there

-- Deletie member
_\\_ : forall {a x} (xs : Context a) -> (mem : x <: xs) -> Context a
_\\_ (xs , x) here = xs
_\\_ (Em , x) (there ())
_\\_ (xs , x) (there m) = (xs \\ m) , x

-- A useful property of deletion
\\-cons-distrib : forall {A} {Γ : Context A} {σ τ : A} {x : τ <: Γ} ->
                  (Γ , σ) \\ there x ≡ ((Γ \\ x) , σ)

\\-cons-distrib {_} {Em} {x = ()}
\\-cons-distrib {_} {Γ , τ} {x = here} = refl
\\-cons-distrib {_} {Gam , sig} {x = there x} = refl

{- Various useful lemmas about contexts -}
unit-lem : forall {A}{Γ : Context A} -> (Em +++ Γ) ≡ Γ
unit-lem {_} {Em} = refl
unit-lem {_} {Γ , sig} rewrite (unit-lem {_} {Γ}) = refl

assoc-lem : forall {A}{Γ1 Γ2 Γ3 : Context A} -> (Γ1 +++ (Γ2 +++ Γ3)) ≡ ((Γ1 +++ Γ2) +++ Γ3)
assoc-lem {Γ1 = Γ1} {Γ2} {Em} = refl
assoc-lem {Γ1 = Em} {Em} {Γ3 , sig} rewrite (unit-lem {Γ = Em +++ Γ3}) = refl
assoc-lem {Γ1 = Em} {Γ2 , sig} {Γ3 , sig1} rewrite unit-lem {Γ = ((Γ2 , sig) +++ Γ3)} | unit-lem {Γ = Γ2} = refl
assoc-lem {Γ1 = Γ1 , sig} {Em} {Γ3 , sig1} rewrite unit-lem {Γ = Γ3} = refl
assoc-lem {Γ1 = Γ1 , sig} {Γ2 , sig1} {Γ3 , sig2} rewrite assoc-lem {Γ1 = Γ1 , sig} {Γ2 = Γ2 , sig1} {Γ3 = Γ3} = refl

assoc-cons-lem : forall {A} {Γ Γ' : Context A} {τ : A} -> ((Γ +++ Γ') , τ) ≡ (Γ +++ (Γ' , τ))
assoc-cons-lem = refl

assoc-cons-lem2 : forall {A} {Γ Γ' : Context A} {τ : A} -> ((Γ , τ) +++ Γ') ≡ (Γ +++ ((Em , τ) +++ Γ'))
assoc-cons-lem2 {Γ = Em} {Γ'} {τ} rewrite unit-lem {Γ = ((Em , τ) +++ Γ')} = refl
assoc-cons-lem2 {Γ = Γ , sig} {Em} = refl
assoc-cons-lem2 {Γ = Γ , sig} {Γ' , sig1} {τ} rewrite (assoc-cons-lem2 {Γ = Γ , sig} {Γ' = Γ'} {τ = τ}) = refl

