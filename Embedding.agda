module Embedding where

open import Sessions
open import Effects
open import Context

open import Data.List hiding (map)

open import Basics
open import Data.Nat
open import Data.Fin
open import Data.Vec hiding (map;_++_)
open import Relation.Binary.PropositionalEquality using (trans;cong;inspect;[_]) 

-- [[ let x = M in N ]]r = new q . ([[ M ]]q | q(x).[[ N ]]r

interpT : Type -> VType
interpT nat = nat
interpT unit = unit

interpMem : forall {Γ τ} -> (mem : τ <: Γ) -> (interpT τ <: (map interpT Γ))
interpMem here = here
interpMem (there mem) = there (interpMem mem)

postulate
  emptyInverseL : forall {f g} -> (f ++ g ≡ pure) -> f ≡ pure
  emptyInverseR : forall {f g} -> (f ++ g ≡ pure) -> g ≡ pure
  weaken : forall {Γ Σ S pt} -> (e : Γ * Σ |- pt) -> Γ * (Σ , S) |- pt
  exchg : forall {Γ Σ S T pt} -> (e : Γ * ((Σ , S), T) |- pt) -> Γ * ((Σ , T) , S) |- pt

{- Specialised embedding for a pure a term -}
embedPure' : forall {Γ τ f}
                  (e : ioEff , Γ !- τ , f) -> (purity : f ≡ pure)
               -> (map interpT Γ * Em , [ interpT τ ]!∙ end |- proc)

embedPure' (var x) refl = (inl here) !< var {Σ = Em} (interpMem x) >∙ (nil {n = 1})
embedPure' {f = .(F ++ G)} (letb {σ = σ} {τ} {F} {G} m n) p =

      let m0 = embedPure' m (emptyInverseL p)
          n0 = embedPure' n (emptyInverseR {f = F} {g = G} p)
          n1 = weaken {S = end} n0
          n2 = here ?[-]∙ n1
          e0 = par m0 n2
          e1 = restrict {Σ = ((Em , ([ interpT σ ]!∙ end)) , ([ interpT τ ]!∙ end)) , ([ interpT σ ]?∙ end)} e0 here (there here) {refl}
      in e1

embedPure' (op Outp e) ()
embedPure' (nullary-op Inp) ()
embedPure' unit p = (inl here) !< unit {Σ = Em} >∙ (nil {n = 1})
embedPure' nzero p = (inl here) !< nzero {Σ = Em} >∙ (nil {n = 1})
embedPure' {Γ} (nsucc e) p = 
                        let e0 = embedPure' e p 
                            e1 = (inl here) !< nsucc {Σ = Em , end} (var {Γ = map interpT Γ , nat} here) >∙ (nil {n = 1}) 
                            e2 = (there here) ?[-]∙ e1
                            ep = par e0 e2
                            ep' = restrict ep here (there here) {refl}
                        in ep'

embedPure : forall {Γ τ} -> (e : ioEff , Γ !- τ , []) 
                         -> (map interpT Γ * Em , [ interpT τ ]!∙ end |- proc)
embedPure e = embedPure' e refl

{- Impure embedding -}

interpEff : List IOEff -> SType
interpEff [] = end
interpEff (In t ∷ xs) = ⊕ (("in" , ([ interpT t ]?∙ (interpEff xs))) ∷ []) 
interpEff (Out t ∷ xs) = ⊕ (("out" , ([ interpT t ]!∙ (interpEff xs))) ∷ [])


liftPure : forall {Γ Σ G S τ} ->
   (p :  Γ * (Σ , S) |- proc → (Γ * (Σ , interpEff G) , ([ τ ]!∙ S) |- proc))
     -> (Γ * ((Σ , [ τ ]!∙ S) , ([ sess (interpEff G) ]?∙ [ sess (interpEff G) ]!∙ end)) |- proc)
liftPure = {!!}

{- This definition is very explicit in parts to make it easier to understand -} 
embedN : forall {Γ τ F G} 
                -> (e : ioEff , Γ !- τ , F)
                -> (map interpT Γ * ((Em , [ interpT τ ]!∙ end) , [ sess (interpEff (F ++ G)) ]?∙ [ sess (interpEff G) ]!∙ end) |- proc)
embedN {G = G} (var {τ = τ} x) = 
  let e = \p -> (inl here) !< var {Σ = Em , interpEff G} (interpMem x) >∙ p
  in liftPure {G = G} {S = end} {τ = interpT τ} e

-- nu q . ( [ m ]q | q(x) . [N]r) 
embedN {Γ} {F = .(f ++ g)} {G} (letb {σ = σ} {τ} {f = f} {g = g} m n) rewrite (symm (assoc-list {a = f} {b = g} {c = G})) = 
  let m0 = embedN {G = (g ++ G)} m 
      
      n0 = embedN {G = G} n
      n1 = weaken {S = end} n0
      n2 = here ?[-]∙ n1

      j0 = _<->∙_ {S = interpEff G} here (nil {n = 3})
      j1 = (there (there here)) [ here ]∙ j0
      j2 = _<->∙_ {S = interpEff (g ++ G)} here j1
      j3 = (there (there (there here))) [ here ]∙ j2
      j4 = _<->∙_ {S = interpEff (f ++ g ++ G)} here j3
      j5 = (there (there (there here))) [ here ]∙ j4

      e0 = par (par m0 n2) j5

      Σ0 = (((((((Em , ([ interpT σ ]!∙ end))
                     , ([ sess (interpEff (f ++ g ++ G)) ]?∙ ([ sess (interpEff (g ++ G)) ]!∙ end)))
                     , ([ interpT τ ]!∙ end))
                     , ([ sess (interpEff (g ++ G)) ]?∙ ([ sess (interpEff G) ]!∙ end)))
                     , ([ interpT σ ]?∙ end))
                     , ([ sess (interpEff (g ++ G)) ]!∙ ([ sess (interpEff G) ]?∙ end)))
                     , ([ sess (interpEff (f ++ g ++ G)) ]!∙ ([ sess (interpEff (g ++ G)) ]?∙ end)))
                     , ([ sess (interpEff (f ++ g ++ G)) ]?∙ ([ sess (interpEff G) ]!∙ end))
      
      e1 = restrict {Σ = Σ0} e0 (th (th (th (th (th (th (th here)))))))
                                (th (th (th here))) {refl}
      Σ1 = (((((Em , ([ sess (interpEff (f ++ g ++ G)) ]?∙ ([ sess (interpEff (g ++ G)) ]!∙ end)))
                   , ([ interpT τ ]!∙ end))
                   , ([ sess (interpEff (g ++ G)) ]?∙ ([ sess (interpEff G) ]!∙ end)))
                   , ([ sess (interpEff (g ++ G)) ]!∙ ([ sess (interpEff G) ]?∙ end)))
                   , ([ sess (interpEff (f ++ g ++ G)) ]!∙ ([ sess (interpEff (g ++ G)) ]?∙ end)))
                   , ([ sess (interpEff (f ++ g ++ G)) ]?∙ ([ sess (interpEff G) ]!∙ end))

      e2 = restrict {Σ = Σ1} e1 (th (th (th (th (th here))))) (th here) {refl}
      e3 = restrict e2 (th (th here)) (th here) {refl}

  in e3
  
embedN (op Outp e) = {!!}

embedN {Γ} {G = g} (nullary-op {τ = τ} Inp) = 
       let esB = _<->∙_ {Γ = map interpT (Γ , τ)} {S = interpEff g} {T = end} here (nil {n = 1}) 
           e0 = (inr here) !< var {Γ = map interpT (Γ , τ)} {Σ = Em , end} here >∙ esB
           e1 = (there here) ?[-]∙ e0
           S = [ interpT τ ]?∙ (interpEff g)
           e2 = _◁_∙_ {Si = ("in" , S) ∷ []} here here e1
           esA = (there (there here)) [ here ]∙ e2
       in esA

embedN {Γ} {F = .[]} {G = g} unit rewrite right-unit-list {e = g} = 
      let esB = _<->∙_ {Γ = map interpT Γ} {S = interpEff g} {T = end} here (nil {n = 1}) 
          e = (inr here) !< unit {Σ = Em , end} >∙ esB
          esA = (there (there here)) [ there here ]∙ e
      in esA

embedN {Γ} {G = g} nzero = 
   let e = embedPure nzero
       e' = weaken {S = end} e
       esB = _<->∙_ {Γ = map interpT Γ} {S = interpEff g} {T = end} here e'
       
   in {!!}
embedN (nsucc e) = {!!}

{- 
embedN : forall {Γ τ F G} 
                -> (e : ioEff , Γ !- τ , F)
                -> (map interpT Γ * ((Em , [ interpT τ ]!∙ end) , [ sess (interpEff (F ++ G)) ]?∙ [ sess (interpEff G) ]!∙ end) |- proc)
-}

embed : forall {Γ τ F}
               -> (e : ioEff , Γ !- τ , F)
               -> (map interpT Γ) * ((Em , [ interpT τ ]!∙ end) , interpEff F) |- proc
embed {Γ} {τ} {F} e = 
          let p = cong-coerce (\f -> map interpT Γ * ((Em , ([ interpT τ ]!∙ end)) , ([ sess (interpEff f) ]?∙ ([ sess end ]!∙ end))) |- proc) ((Effect.right-unit ioEff) {e = F}) (embedN {G = []} e) 
              j0 = nil {n = 2}
              j1 = here [ here ]∙ j0
              j2 = _<->∙_ {S = interpEff F} here j1
              e0 = par p j2
              e1 = restrict e0 (there (there here)) (there here) {refl}
          in e1

{- OLD

embed : forall {Γ τ f} -> (e : ioEff , Γ !- τ , f) 
                       -> (map interpT Γ * ((Em , interpEff f ), [ interpT τ ]!∙ end) |- proc)
embed (var x) = (inl here) !< var {Σ = Em , interpEff []} (interpMem x) >∙ (nil {n = 1})
embed (letb m n) = {!!}
embed {Γ} (op {τ' = τ'} Outp e) = 

  let e0 = (inl here) !< unit {Σ = (Em , end) , interpEff []} >∙ (nil {n = 1})
      e1 = (inl (there here)) !< var {Γ = map interpT (Γ , τ')} {Σ = Em} here >∙ e0
      S = [ interpT τ' ]!∙ end
      e2 = _◁_∙_ {Si = ("out" , S) ∷ []} here here e1 
      e3 = (there (there here)) ?[-]∙ e2
      e' = embedPure e 
      en = par e3 e'
      en' = restrict en here here {refl}
  
  in exchg en'

embed {Γ} (nullary-op {τ = τ} Inp) = 
  let e0 = (inl here) !< var {Γ = map interpT (Γ , τ)} {Σ = Em , interpEff []} here >∙ (nil {n = 1})
      e1 = (there here) ?[-]∙ e0
      S = [ interpT τ ]?∙ end
      e2 = _◁_∙_ {Si = ("in" , S) ∷ []} here here e1 
  in exchg e2

embed unit = (inl here) !< unit {Σ = Em , interpEff []} >∙ (nil {n = 1})
embed nzero = (inl here) !< nzero {Σ = Em , interpEff []} >∙ (nil {n = 1})
embed {Γ} (nsucc e) = let e0 = embedPure e  
                          e1 = (inl here) !< nsucc {Σ = (Em , end) , end} (var {Γ = map interpT Γ , nat} here) >∙ (nil {n = 1}) 
                          e2 = (there here) ?[-]∙ e1
                          ep = par e0 e2
                          ep' = restrict ep here (there (there here)) {refl}
                      in ep'

-}