module FirstOrder where

open import Basics
open import Size
open import Data.Nat
open import Context
open import Data.Vec
open import Data.String
open import Data.Fin using (Fin; zero; suc)

mutual 
  data VType : Set where
    unit : VType
    nat  : VType
    sess : forall {i : Size} -> SType {i} -> VType

  data SType : {i : Size} -> Set where
    [_]!∙_ : {i : Size} -> VType -> SType {i} -> SType {↑ i}
    [_]?∙_ : {i : Size} -> VType -> SType {i} -> SType {↑ i}
    ⊕_     : {n : ℕ} {i : Size} (vs : Vec (Pair String (SType {i})) n) -> SType {↑ i}
    &_     : {n : ℕ} {i : Size} (vs : Vec (Pair String (SType {i})) n) -> SType {↑ i}
    !_     : {i : Size} -> SType {i} -> SType {↑ i}
    end    : {i : Size} -> SType {↑ i}

data PType : Set where
  val : VType -> PType
  proc : PType
  
dual : {i : Size} -> SType {i} → SType {i}
dual ([ V ]!∙ P) = [ V ]?∙ (dual P)
dual ([ V ]?∙ P) = [ V ]!∙ (dual P)
dual (⊕_ vs) = &_ (Data.Vec.map (\x -> ( pi1 x , dual (pi2 x))) vs)
dual (&_ vs) = ⊕_ (Data.Vec.map (\x -> ( pi1 x , dual (pi2 x))) vs)
dual (! P) = !(dual P)
dual end = end


allEnd : {n : ℕ} -> Context SType
allEnd {zero} = Em
allEnd {suc n} = (allEnd {n}) , end

mutual

  data DerivVec : (Γ : Context VType) (Σ : Context SType) (n : ℕ) (vs : Vec SType n) (T : PType) -> Set where
    [] : forall {Γ Σ T} -> DerivVec Γ Σ zero [] T
    Cons : forall {Γ Σ n ss T k} (x : Γ * (Σ , k) |- proc) (xs : DerivVec Γ Σ n ss T) -> DerivVec Γ Σ  (suc n) (k ∷ ss) T

  data _*_|-_ : (Γ : Context VType) -> (Σ : Context SType) -> (t : PType) -> Set where

      _?[-]∙_ : forall {Γ Σ S t}

                        (k : S <: Σ) 
                        (P : ( Γ , t ) * Σ |- proc) 
                      -> ---------------------------------------------
                           Γ * ((Σ \\ k) , ([ t ]?∙ S)) |- proc

      _[_]∙_ : forall {Γ Σ S T}

                        (k : T <: Σ) 
                        (x : S <: (Σ \\ k))
                        (P : Γ * Σ |- proc) 
                      -> ---------------------------------------------
                           Γ * (((Σ \\ k) \\ x) , ([ sess S ]?∙ T)) |- proc

      _!<_>∙_ : forall {Γ Σ1 Σ2 S t}
                        (k : Either (S <: Σ1) (S <: Σ2))
                        (V : Γ * Σ2 |- val t)
                        (P : Γ * Σ1 |- proc)
                      -> ------------------------------------------------------------- 
                         Γ * (Case (\k -> (Σ1 \\ k) +++ Σ2) 
                                   (\k -> Σ1 +++ (Σ2 \\ k)) k) , ([ t ]!∙ S) |- proc

      _<->∙_ : forall {Γ Σ S T} (k : T <: Σ)
                                (p : Γ * Σ |- proc)
                             -> ----------------------------------------------
                                 Γ * (((Σ \\ k) , [ sess S ]!∙ T) , S) |- proc

      _▷[_]  : forall {Γ Σ n} {Si : Vec (Pair String SType) n} 
 
                         (k : (& Si) <: Σ) 
                         (pi : DerivVec Γ (Σ \\ k) n (Data.Vec.map pi2 Si) proc) 
                      -> -----------------------------------------------
                          Γ * Σ |- proc 

      _◁_∙_ : forall {Γ Σ S n} {Si : Vec (Pair String SType) n}

                         --(k : (pi2 S) <: Σ) (j : Fin n) 
                         --(p : Γ * Σ |- proc) {mem : Si [ j ]= S}
                         (k : (pi2 S) <: Σ) (mem : S ∈ Si) 
                         (p : Γ * Σ |- proc) 
                      -> -----------------------------------------------
                          Γ * ((Σ \\ k) , ⊕ Si) |- proc

      nil : forall {Γ n}  -> --------------------------
                              Γ * (allEnd {n}) |- proc


      var : forall {Γ Σ t}     (x : t <: Γ)  
                           -> ----------------
                               Γ * Σ |- val t

--      svar : forall {Γ Σ s}   (x : s <: Σ)
--                           -> ---------------------
--                              Γ * Σ |- val (sess s)

      par : forall {Γ Σ1 Σ2} (p : Γ * Σ1 |- proc)
                             (q : Γ * Σ2 |- proc)
                          -> -----------------------
                             Γ * (Σ1 +++ Σ2) |- proc

      -- Constants

      unit : forall {Γ Σ} -> --------------------------
                               Γ * Σ |- val unit

      nzero : forall {Γ Σ} -> -----------------------
                                 Γ * Σ |- val nat

      nsucc : forall {Γ Σ}     (p : Γ * Σ |- val nat)
                           -> ------------------------ 
                                Γ * Σ |- val nat

      restrict : forall {Γ Σ s sbar t}  (p : Γ * Σ |- t)
                                        (x : s <: Σ)
                                        (xbar : sbar <: (Σ \\ x))
                                        {prf : (dual s) ≡ sbar}
                                      -> --------------------------
                                          Γ * (Σ \\ x) \\ xbar |- t

      repInp : forall {Γ S}  

                        (p : Γ * (Em , S) |- proc)                        
                      -> -------------------------
                           Γ * (Em , ! S) |- proc



