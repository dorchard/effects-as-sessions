module Effects where

{-

  This file defines the 'effect calculus'. A simple imperative 
  language that is parameterised by an effect algebra and
  effectful operations. 

-}


open import Basics
open import Relation.Binary.PropositionalEquality using (trans;cong;inspect) 
open import Data.Nat
open import Data.List 
open import Context
open import Data.Maybe

import NearSemiring 

-- Value type
data Type : Set where
  nat   : Type
  unit  : Type

-- Effect algebra
record Effect : Set₁ where
    infixl 7 _•_
    field
      {- Monoid -}
      Carrier  : Set 
      _•_      : Carrier -> Carrier -> Carrier
      _⊕_      : Carrier -> Carrier -> Carrier
      --_*       : Carrier -> Carrier
      I        : Carrier

      -- Efectful operations
      operations : Maybe (Pair (Context Type) Type) -> Context Type -> Type -> Carrier -> Set

      right-unit : forall {e : Carrier} -> (e • I) ≡ e
      left-unit  : forall {e : Carrier} -> (I • e) ≡ e
      assoc      : (a b c : Carrier) -> (a • (b • c)) ≡ ((a • b) • c)
      dist       : (f g h : Carrier) -> (f ⊕ g) • h ≡ (f • h) ⊕ (g • h)
      --fixy       : forall {f : Carrier} -> f * ≡ f • (f *)

      {- The following two lemmas are used in the pure embedding -}
      -- If the composition of two effects is pure, then each effect is also pure.
      pureInverseL : (f g : Carrier) -> (f • g ≡ I) -> f ≡ I
      pureInverseR : (f g : Carrier) -> (f • g ≡ I) -> g ≡ I

open Effect

{- The data type of well-typed effect calculus terms -}
infixr 3 _,_!-_,_
data _,_!-_,_ (eff : Effect) : (Gam : Context Type) -> Type -> (Carrier eff) -> Set where
  
  var : forall {Γ τ}   (x : τ <: Γ) 
                   -> ------------------------
                       eff , Γ !- τ , (I eff)


  letb : forall {Γ σ τ f g}  (e :  eff ,     Γ    !- σ , f)
                             (e' : eff , (Γ , σ)  !- τ , g)
                         -> -------------------------------------------
                                   eff ,        Γ !- τ , ((_•_ eff) f g)

  case : forall {Γ τ f g h}
                (m  : eff , Γ         !- nat , f)
                (n1 : eff , Γ         !- τ   , g)
                (n2 : eff , (Γ , nat) !- τ   , h)
             -> -----------------------------------------------
                   eff , Γ !- τ , ((_•_ eff) f ((_⊕_ eff) g h))


  {- Default constants and operations -}

  unit : forall {Γ} -> ---------------------------
                        eff , Γ !- unit , (I eff)


  nzero : forall {Γ}  -> -------------------------
                          eff , Γ !- nat , (I eff)


  nsucc : forall {Γ}      (e : eff , Γ !- nat , (I eff)) 
                      -> ---------------------------------
                               eff , Γ !- nat , (I eff)


{- State Effects -}
mutual

  NSR = NearSemiring.NSR

  data StateEff : Set where
    Get  : (t : Type) -> StateEff
    Put  : (t : Type) -> StateEff

  stEff : Effect 
  stEff = record
    { Carrier    = NSR StateEff;
      _•_        = NearSemiring._•_;
      _⊕_        = NearSemiring._⊕_;
      I          = NearSemiring.nil;
      operations = STOps;

      left-unit = refl;
      right-unit = NearSemiring.unitR;
      dist = \a b c -> NearSemiring.distrib {f = a} {g = b} {h = c};
      assoc = \a b c -> NearSemiring.assoc {a = a} {b} {c};
      pureInverseL = \f g -> NearSemiring.pureInverseL {f = f} {g = g};
      pureInverseR = \f g -> NearSemiring.pureInverseR {f = f} {g = g}
     }

  single : StateEff -> NSR StateEff
  single x = NearSemiring.cons x NearSemiring.nil

  pure : NSR StateEff
  pure = NearSemiring.nil

  data STOps : Maybe (Pair (Context Type) Type)  -> Context Type -> Type -> NSR StateEff -> Set where
    Get  : forall {Γ t} -> STOps nothing Γ t (single (Get t))
    Put  : forall {Γ t} -> STOps (just (Γ , t)) Γ unit (single (Put t))
