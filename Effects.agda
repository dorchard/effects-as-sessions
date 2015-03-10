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
      assoc      : forall {a b c : Carrier} -> (a • (b • c)) ≡ ((a • b) • c)
      dist       : forall {f g h : Carrier} -> (f ⊕ g) • h ≡ (f • h) ⊕ (g • h)
      --fixy       : forall {f : Carrier} -> f * ≡ f • (f *)

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


  op : forall {Γ τ f Γ' τ'} 
                (op : operations eff (just (Γ' , τ')) Γ τ f) (x : eff , Γ' !- τ' , (I eff))
             -> --------------------------------------------------------------------------
                     eff , Γ !- τ , f

  const : forall {Γ τ f} 
                (op : operations eff nothing Γ τ f)
             -> --------------------------------------
                     eff , Γ !- τ , f

  case : forall {Γ τ f g h}
                (m  : eff , Γ !- nat , f)
                (n1 : eff , Γ !- τ   , g)
                (n2 : eff , Γ !- τ   , h)
             -> -----------------------------
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

  stEff = record
    { Carrier    = NSR StateEff;
      _•_        = NearSemiring._•_;
      _⊕_        = NearSemiring._⊕_;
      I          = NearSemiring.nil;
      operations = STOps;

      left-unit = refl;
      right-unit = NearSemiring.unitR;
      dist = NearSemiring.distrib;
      assoc = assocy
     }

  assocy : {A : Set} {a b c : NearSemiring.NSR A} -> NearSemiring._•_ a (NearSemiring._•_ b c) ≡ NearSemiring._•_ (NearSemiring._•_ a b) c
  assocy {A} {a} {b} {c} = NearSemiring.assoc {A} {a} {b} {c}

  data StateEff : Set where
    Get  : (t : Type) -> StateEff
    Put  : (t : Type) -> StateEff

  single : StateEff -> NSR StateEff
  single x = NearSemiring.cons x NearSemiring.nil

  pure : NSR StateEff
  pure = NearSemiring.nil

  data STOps : Maybe (Pair (Context Type) Type)  -> Context Type -> Type -> NSR StateEff -> Set where
    Get  : forall {Γ t} -> STOps nothing Γ t (single (Get t))
    Put  : forall {Γ t} -> STOps (just (Γ , t)) Γ unit (single (Put t))
