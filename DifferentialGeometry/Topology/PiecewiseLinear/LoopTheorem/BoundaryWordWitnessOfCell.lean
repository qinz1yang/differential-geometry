/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.LoopSpace.InjectivePathReparam
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryWordWitness

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u v

namespace BoundaryWordWitness

section Lift

variable {M : Type u} [TopologicalSpace M] {X : Type v} [TopologicalSpace X] {ρ : X → M}

noncomputable def liftPath (hρ : IsEmbedding ρ) {a b : X} (γ : Path (ρ a) (ρ b))
    (hγ : ∀ t, γ t ∈ Set.range ρ) : Path a b where
  toFun t := Classical.choose (Set.mem_range.mp (hγ t))
  continuous_toFun := hρ.isInducing.continuous_iff.mpr <| by
    have hspec : (ρ ∘ fun t => Classical.choose (Set.mem_range.mp (hγ t))) = ⇑γ :=
      funext fun t => Classical.choose_spec (Set.mem_range.mp (hγ t))
    rw [hspec]
    exact γ.continuous
  source' := hρ.injective ((Classical.choose_spec (Set.mem_range.mp (hγ 0))).trans γ.source)
  target' := hρ.injective ((Classical.choose_spec (Set.mem_range.mp (hγ 1))).trans γ.target)

theorem liftPath_apply (hρ : IsEmbedding ρ) {a b : X} (γ : Path (ρ a) (ρ b))
    (hγ : ∀ t, γ t ∈ Set.range ρ) (t : unitInterval) : ρ (liftPath hρ γ hγ t) = γ t :=
  Classical.choose_spec (Set.mem_range.mp (hγ t))

theorem range_liftPath (hρ : IsEmbedding ρ) {a b : X} (γ : Path (ρ a) (ρ b))
    (hγ : ∀ t, γ t ∈ Set.range ρ) {S : Set X} (hS : Set.range ⇑γ = ρ '' S) :
    Set.range ⇑(liftPath hρ γ hγ) = S := by
  refine hρ.injective.image_injective ?_
  rw [← hS, ← Set.range_comp]
  exact congrArg Set.range (funext fun t => liftPath_apply hρ γ hγ t)

end Lift

section Word

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {X : Type v} [TopologicalSpace X] {G : SingularTwoCell M} {ρ : X → M}

def ofHomotopicWord {w₁ w₂ : freeLoop X} (W : BoundaryWordWitness G ρ w₁)
    (h : w₁.Homotopic w₂) : BoundaryWordWitness G ρ w₂ where
  param := W.param
  loop := W.loop
  realizes := W.realizes
  homotopic := W.homotopic.trans h

end Word

section Match

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {X : Type v} [TopologicalSpace X] {G : SingularTwoCell M} {ρ : X → M}

theorem exists_of_twoArcMatch [T2Space M] (hρ : IsEmbedding ρ)
    (e : loopCircle ≃ₜ frontier G.domain) {a b : X} {P : Path a b} {Q : Path b a}
    (hP : Function.Injective ⇑P) (hQ : Function.Injective ⇑Q)
    {α : Path (ρ a) (ρ b)} {ω : Path (ρ b) (ρ a)}
    (hparam : ∀ θ, G (e θ) = pathToCircle (α.trans ω) θ)
    (hα : Set.range ⇑α = ρ '' Set.range ⇑P) (hω : Set.range ⇑ω = ρ '' Set.range ⇑Q) :
    Nonempty (BoundaryWordWitness G ρ (pathToCircle (P.trans Q))) := by
  have : T2Space X := hρ.t2Space
  have hαmem : ∀ t, α t ∈ Set.range ρ := by
    intro t
    have ht : α t ∈ Set.range ⇑α := Set.mem_range_self t
    rw [hα] at ht
    obtain ⟨y, -, hy⟩ := ht
    exact ⟨y, hy⟩
  have hωmem : ∀ t, ω t ∈ Set.range ρ := by
    intro t
    have ht : ω t ∈ Set.range ⇑ω := Set.mem_range_self t
    rw [hω] at ht
    obtain ⟨y, -, hy⟩ := ht
    exact ⟨y, hy⟩
  have hPhom : (liftPath hρ α hαmem).Homotopic P :=
    Path.Homotopic.of_injective_of_range_eq hP (range_liftPath hρ α hαmem hα)
  have hQhom : (liftPath hρ ω hωmem).Homotopic Q :=
    Path.Homotopic.of_injective_of_range_eq hQ (range_liftPath hρ ω hωmem hω)
  refine ⟨{ param := e
            loop := pathToCircle ((liftPath hρ α hαmem).trans (liftPath hρ ω hωmem))
            realizes := fun θ => ?_
            homotopic := pathToCircle_homotopic (hPhom.hcomp hQhom) }⟩
  rw [hparam θ]
  exact (pathToCircle_eq_of_forall ((liftPath hρ α hαmem).trans (liftPath hρ ω hωmem))
    (α.trans ω) (trans_apply_eq_map (fun t => (liftPath_apply hρ α hαmem t).symm)
      (fun t => (liftPath_apply hρ ω hωmem t).symm)) θ).symm

theorem exists_of_twoArcMatch_reversing [T2Space M] (hρ : IsEmbedding ρ)
    (e : loopCircle ≃ₜ frontier G.domain) {a b : X} {σ υ : Path a b}
    (hσ : Function.Injective ⇑σ) (hυ : Function.Injective ⇑υ)
    {α : Path (ρ a) (ρ b)} {ω : Path (ρ b) (ρ a)}
    (hparam : ∀ θ, G (e θ) = pathToCircle (α.trans ω) θ)
    (hα : Set.range ⇑α = ρ '' Set.range ⇑σ) (hω : Set.range ⇑ω = ρ '' Set.range ⇑υ) :
    Nonempty (BoundaryWordWitness G ρ (pathToCircle (σ.trans υ.symm))) := by
  refine exists_of_twoArcMatch hρ e hσ ?_ hparam hα ?_
  · intro s t hst
    have h : υ (unitInterval.symm s) = υ (unitInterval.symm t) := hst
    exact unitInterval.symm_bijective.injective (hυ h)
  · rwa [Path.symm_range]

theorem exists_of_twoArcMatch_self [T2Space M] (e : loopCircle ≃ₜ frontier G.domain)
    {y z : M} {α : Path y z} {ω : Path z y} (hα : Function.Injective ⇑α)
    (hω : Function.Injective ⇑ω) (hparam : ∀ θ, G (e θ) = pathToCircle (α.trans ω) θ) :
    Nonempty (BoundaryWordWitness G (id : M → M) (pathToCircle (α.trans ω))) :=
  exists_of_twoArcMatch (X := M) (ρ := id) _root_.Topology.IsEmbedding.id e hα hω hparam
    (Set.image_id _).symm (Set.image_id _).symm

end Match

end BoundaryWordWitness

end DifferentialGeometry.Topology.PiecewiseLinear
