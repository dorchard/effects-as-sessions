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

mutual
  -- Value type
  data Type (E : Set) : Set where
    nat   : Type E
    unit  : Type E
    _-[_]->_ : Type E -> E -> Type E -> Type E

  -- Effect algebra
  record Effect : Set₁ where
      infixl 7 _•_
      field
        {- Monoid -}
        Carrier  : Set 
        _•_      : Carrier -> Carrier -> Carrier
        _⊕_      : Carrier -> Carrier -> Carrier
        _*       : Carrier -> Carrier
        I        : Carrier

        -- Efectful operations
        operations : Maybe (Pair (Context (Type Carrier)) (Type Carrier)) -> Context (Type Carrier) -> (Type Carrier) -> Carrier -> Set

        right-unit : forall {e : Carrier} -> (e • I) ≡ e
        left-unit  : forall {e : Carrier} -> (I • e) ≡ e
        assoc      : (a b c : Carrier) -> (a • (b • c)) ≡ ((a • b) • c)
        dist       : (f g h : Carrier) -> (f ⊕ g) • h ≡ (f • h) ⊕ (g • h)
        fixy       : (f : Carrier) -> f * ≡ f • (f *)

        {- The following two lemmas are used in the pure embedding -}
        -- If the composition of two effects is pure, then each effect is also pure.
        pureInverseL : (f g : Carrier) -> (f • g ≡ I) -> f ≡ I
        pureInverseR : (f g : Carrier) -> (f • g ≡ I) -> g ≡ I
  
open Effect

{- The data type of well-typed effect calculus terms -}
infixr 3 _,_!-_,_
data _,_!-_,_ (eff : Effect) : (Gam : Context (Type (Carrier eff))) -> Type (Carrier eff) -> (Carrier eff) -> Set where
  
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

  abs : forall {Γ σ τ f} 
                (m : eff , (Γ , σ) !- τ , f)
             -> ------------------------------------
                 eff , Γ !- σ -[ f ]-> τ , (I eff)


  fix : forall {Γ τ f g}
               (m : eff , Γ !- τ -[ f ]-> τ , g)
            -> -------------------------------------
                 eff , Γ !- τ , (_* eff (_•_ eff f g))


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
    Get  : (t : Type (NearSemiring.NSR StateEff)) -> StateEff
    Put  : (t : Type (NearSemiring.NSR StateEff)) -> StateEff

  nsrfix : {A : Set} (f : NearSemiring.NSR A) -> NearSemiring.NSR A
  nsrfix f  = NearSemiring.nil

  NS =  NearSemiring.NSR StateEff

  stEff : Effect 
  stEff = record
    { Carrier    = NS;
      _•_        = NearSemiring._•_;
      _⊕_        = NearSemiring._⊕_;
      _*         = \x -> NearSemiring.nil;
      I          = NearSemiring.nil;
      operations = STOps;

      left-unit = refl;
      right-unit = NearSemiring.unitR;
      dist = \a b c -> NearSemiring.distrib {f = a} {g = b} {h = c};
      assoc = \a b c -> NearSemiring.assoc {a = a} {b} {c};
      pureInverseL = \f g -> NearSemiring.pureInverseL {f = f} {g = g};
      pureInverseR = \f g -> NearSemiring.pureInverseR {f = f} {g = g};
      fixy = nsrFixy 
     }

  postulate -- LIE
    nsrFixy : (f : NearSemiring.NSR StateEff) -> nsrfix {A = StateEff} f ≡ NearSemiring._•_ f (nsrfix {A = StateEff} f)

  single : StateEff -> NearSemiring.NSR StateEff
  single x = NearSemiring.cons x NearSemiring.nil

  pure : NearSemiring.NSR StateEff
  pure = NearSemiring.nil

  data STOps : Maybe (Pair (Context (Type NS)) (Type NS))  -> Context (Type NS) -> Type NS -> NS -> Set where
    Get  : forall {Γ t} -> STOps nothing Γ t (single (Get t))
    Put  : forall {Γ t} -> STOps (just (Γ , t)) Γ unit (single (Put t))
