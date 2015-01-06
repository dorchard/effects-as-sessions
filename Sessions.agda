module Sessions where

{-

  This file defines the session calculus: first-order 
  pi-calculus with recursion, sessions, and branching.

-}

open import Basics
open import Size
open import Data.Nat
open import Context
open import Data.Vec
open import Data.String
open import Data.Fin using (Fin; zero; suc)

mutual 
  {- Value types -}
  data VType : Set where
    unit : VType
    nat  : VType
    sess : forall {i : Size} -> SType {i} -> VType

  {- (Sized) session types. The size is used to prove termination
     of dual -}
  data SType : {i : Size} -> Set where
    [_]!∙_ : {i : Size} -> VType -> SType {i} -> SType {↑ i}
    [_]?∙_ : {i : Size} -> VType -> SType {i} -> SType {↑ i}
    ⊕_     : {n : ℕ} {i : Size} (vs : Vec (Pair String (SType {i})) n) -> SType {↑ i}
    &_     : {n : ℕ} {i : Size} (vs : Vec (Pair String (SType {i})) n) -> SType {↑ i}
    !_     : {i : Size} -> SType {i} -> SType {↑ i}
    end    : {i : Size} -> SType {↑ i}

-- Process types
data PType : Set where
  val : VType -> PType
  proc : PType
  
-- Session duality
dual : {i : Size} -> SType {i} → SType {i}
dual ([ V ]!∙ P) = [ V ]?∙ (dual P)
dual ([ V ]?∙ P) = [ V ]!∙ (dual P)
dual (⊕_ vs) = &_ (Data.Vec.map (\x -> ( pi1 x , dual (pi2 x))) vs)
dual (&_ vs) = ⊕_ (Data.Vec.map (\x -> ( pi1 x , dual (pi2 x))) vs)
dual (! P) = !(dual P)
dual end = end

-- Construct a session environment of size n, where each channel has type 'end'
allEnd : {n : ℕ} -> Context SType
allEnd {zero} = Em
allEnd {suc n} = (allEnd {n}) , end

mutual

  {- Vector or derivations, each sharing the same value typing environment -}
  data DerivVec : (Γ : Context VType) (Σ : Context SType) (n : ℕ) (vs : Vec SType n) (T : PType) -> Set where
    [] : forall {Γ Σ T} -> DerivVec Γ Σ zero [] T
    Cons : forall {Γ Σ n ss T k} (x : Γ * (Σ , k) |- proc) (xs : DerivVec Γ Σ n ss T) -> DerivVec Γ Σ  (suc n) (k ∷ ss) T

  {- Well-typed session terms -}
  data _*_|-_ : (Γ : Context VType) -> (Σ : Context SType) -> (t : PType) -> Set where
  
       -- Value receive
      _?[-]∙_ : forall {Γ Σ S t}

                        (k : S <: Σ) 
                        (P : ( Γ , t ) * Σ |- proc) 
                      -> ---------------------------------------------
                           Γ * ((Σ \\ k) , ([ t ]?∙ S)) |- proc

      -- Channel receive
      _[_]∙_ : forall {Γ Σ S T}

                        (k : T <: Σ) 
                        (x : S <: (Σ \\ k))
                        (P : Γ * Σ |- proc) 
                      -> ---------------------------------------------
                           Γ * (((Σ \\ k) \\ x) , ([ sess S ]?∙ T)) |- proc

      -- Value send
      _!<_>∙_ : forall {Γ Σ1 Σ2 S t}
                        (k : Either (S <: Σ1) (S <: Σ2))
                        (V : Γ * Σ2 |- val t)
                        (P : Γ * Σ1 |- proc)
                      -> ------------------------------------------------------------- 
                         Γ * (Case (\k -> (Σ1 \\ k) +++ Σ2) 
                                   (\k -> Σ1 +++ (Σ2 \\ k)) k) , ([ t ]!∙ S) |- proc

      -- Channel send
      _<->∙_ : forall {Γ Σ S T} (k : T <: Σ)
                                (p : Γ * Σ |- proc)
                             -> ----------------------------------------------
                                 Γ * (((Σ \\ k) , [ sess S ]!∙ T) , S) |- proc

      -- Branch
      _▷[_]  : forall {Γ Σ n} {Si : Vec (Pair String SType) n} 
 
                         (k : (& Si) <: Σ) 
                         (pi : DerivVec Γ (Σ \\ k) n (Data.Vec.map pi2 Si) proc) 
                      -> -----------------------------------------------
                          Γ * Σ |- proc 

      -- Select
      _◁_∙_ : forall {Γ Σ S n} {Si : Vec (Pair String SType) n}

                         (k : (pi2 S) <: Σ) (mem : S ∈ Si) 
                         (p : Γ * Σ |- proc) 
                      -> -----------------------------------------------
                          Γ * ((Σ \\ k) , ⊕ Si) |- proc

      -- End the process
      nil : forall {Γ n}  -> --------------------------
                              Γ * (allEnd {n}) |- proc


      -- Value variable
      var : forall {Γ Σ t}     (x : t <: Γ)  
                           -> ----------------
                               Γ * Σ |- val t

      -- Parallel compose
      par : forall {Γ Σ1 Σ2} (p : Γ * Σ1 |- proc)
                             (q : Γ * Σ2 |- proc)
                          -> -----------------------
                             Γ * (Σ1 +++ Σ2) |- proc

      -- Session restriction
      restrict : forall {Γ Σ s sbar t}  (p : Γ * Σ |- t)
                                        (x : s <: Σ)
                                        (xbar : sbar <: (Σ \\ x))
                                        {prf : (dual s) ≡ sbar}
                                      -> --------------------------
                                          Γ * (Σ \\ x) \\ xbar |- t

      -- Value constants and operations

      unit : forall {Γ Σ} -> --------------------------
                               Γ * Σ |- val unit

      nzero : forall {Γ Σ} -> -----------------------
                                 Γ * Σ |- val nat

      nsucc : forall {Γ Σ}     (p : Γ * Σ |- val nat)
                           -> ------------------------ 
                                Γ * Σ |- val nat

