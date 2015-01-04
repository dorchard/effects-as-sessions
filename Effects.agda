module Effects where

open import Basics
open import Relation.Binary.PropositionalEquality using (trans;cong;inspect) -- hiding (subst)
open import Data.Nat
open import Data.List 
open import Context
open import Data.Maybe

infixr 3 _,_!-_,_

data Type : Set where
  nat   : Type
  unit  : Type

record Effect : Set₁ where
    infixl 7 _•_
    field
      Carrier  : Set
      _•_      : Carrier -> Carrier -> Carrier
      I        : Carrier
      operations : Maybe (Pair (Context Type) Type) -> Context Type -> Type -> Carrier -> Set

      right-unit : forall {e : Carrier} -> (e • I) ≡ e
      left-unit  : forall {e : Carrier} -> (I • e) ≡ e
      --assoc      : forall {a b c : Carrier} -> (a • (b • c)) ≡ ((a • b) • c)

open Effect


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

  nullary-op : forall {Γ τ f} 
                           (op : operations eff nothing Γ τ f)
                     -> --------------------------------------
                            eff , Γ !- τ , f


  unit : forall {Γ} -> ---------------------------
                        eff , Γ !- unit , (I eff)


  nzero : forall {Γ}  -> -------------------------
                          eff , Γ !- nat , (I eff)


  nsucc : forall {Γ}      (e : eff , Γ !- nat , (I eff)) 
                      -> ---------------------------------
                               eff , Γ !- nat , (I eff)


{- IO Effects -}

mutual
  ioEff = record
    { Carrier    = List IOEff;
      _•_        = _++_;
      I          = [];
      operations = IOOps;

      left-unit = refl;
      right-unit = right-unit-list
      --assoc = assoc-list
     }

  data IOEff : Set where
    In  : (t : Type) -> IOEff
    Out  : (t : Type) -> IOEff

  right-unit-list : forall {e : List IOEff} -> (e ++ []) ≡ e
  right-unit-list {[]} = refl
  right-unit-list {x ∷ xs} = cong (\xs -> x ∷ xs) (right-unit-list {xs})

  assoc-list : forall {a b c : Carrier ioEff} -> ((_•_ ioEff) a ((_•_ ioEff) b c)) ≡ ((_•_ ioEff) ((_•_ ioEff) a b) c)
  assoc-list {[]} = refl
  assoc-list {x ∷ xs} = cong (\xs -> x ∷ xs) (assoc-list {xs})

  single : IOEff -> List IOEff
  single x = Data.List.[ x ]

  pure : List IOEff
  pure = Data.List.[]

  data IOOps : Maybe (Pair (Context Type) Type)  -> Context Type -> Type -> List IOEff -> Set where
    Inp  : forall {Γ t} -> IOOps nothing Γ t (single (In t))
    Outp : forall {Γ t} -> IOOps (just (Γ , t)) Γ unit (single (Out t))
