/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryWordWitness
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchInjection

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u v w

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

theorem exists_descendingSurgery_not_loopClassMeets_reversing_witness_of_injection
    {U : Set M} {hD : NormalSingularCellData D BdM B} {c : hD.singularSet.Branch}
    {Gd : SingularTwoCell M} (hGd : NormalSingularCellData Gd BdM B)
    (origin : hGd.singularSet.Branch → hD.singularSet.Branch)
    (hinj : Function.Injective origin) (hmiss : ∀ b, origin b ≠ c)
    (R : CrossSeamResolutionData hD c U)
    {Q : Type w} [TopologicalSpace Q] {p' q' u' v' : Q}
    (σ₀ : Path p' q') (τ₀ : Path q' u') (υ₀ : Path u' v') (φ₀ : Path v' p')
    (ev : loopCircle → Q)
    (hev : ∀ θ, ev θ = pathToCircle (σ₀.trans (τ₀.trans (υ₀.trans φ₀))) θ)
    {X : Type v} [TopologicalSpace X] [PathConnectedSpace X] {f : Q → X} {x a b : X}
    {σ υ : Path a b} {τ φ : Path b a}
    (hσ : ∀ t, σ t = f (σ₀ t)) (hτ : ∀ t, τ t = f (τ₀ t)) (hυ : ∀ t, υ t = f (υ₀ t))
    (hφ : ∀ t, φ t = f (φ₀ t)) (γ : freeLoop X) (hγ : ∀ θ, γ θ = f (ev θ))
    {N : Subgroup (FundamentalGroup X x)} [N.Normal] (hγN : ¬loopClassMeets γ x N)
    {ρ : X → M} (Wdirect : BoundaryWordWitness Gd ρ (pathToCircle (σ.trans υ.symm)))
    (Wcross : BoundaryWordWitness R.cell ρ (pathToCircle (σ.trans (φ.trans (υ.trans τ))))) :
    ∃ (S : hD.DescendingSurgery) (e : loopCircle ≃ₜ frontier S.cell.domain) (δ : freeLoop X),
      (∀ θ, ρ (δ θ) = S.cell (e θ)) ∧ ¬loopClassMeets δ x N := by
  refine exists_descendingSurgery_of_not_loopClassMeets_or_witness
    (S₁ := DescendingSurgery.ofBranchInjection hD hGd origin hinj hmiss)
    (S₂ := R.toDescendingSurgery)
    (w₁ := pathToCircle (σ.trans υ.symm))
    (w₂ := pathToCircle (σ.trans (φ.trans (υ.trans τ))))
    Wdirect Wcross ?_
  exact not_loopClassMeets_or_not_loopClassMeets_of_four_boundary_arcs_reversing σ₀ τ₀ υ₀ φ₀
    ev hev (PathConnectedSpace.somePath x a) (PathConnectedSpace.somePath a b) hσ hτ hυ hφ γ hγ
    N hγN

theorem exists_descendingSurgery_not_loopClassMeets_preserving_witness_of_injection
    {U : Set M} {hD : NormalSingularCellData D BdM B} {c : hD.singularSet.Branch}
    {Gd : SingularTwoCell M} (hGd : NormalSingularCellData Gd BdM B)
    (origin : hGd.singularSet.Branch → hD.singularSet.Branch)
    (hinj : Function.Injective origin) (hmiss : ∀ b, origin b ≠ c)
    (R : CrossSeamResolutionData hD c U)
    {Q : Type w} [TopologicalSpace Q] {p' q' u' v' : Q}
    (σ₀ : Path p' q') (τ₀ : Path q' u') (υ₀ : Path u' v') (φ₀ : Path v' p')
    (ev : loopCircle → Q)
    (hev : ∀ θ, ev θ = pathToCircle (σ₀.trans (τ₀.trans (υ₀.trans φ₀))) θ)
    {X : Type v} [TopologicalSpace X] [PathConnectedSpace X] {f : Q → X} {x a b : X}
    {σ : Path a b} {τ : Path b b} {υ : Path b a} {φ : Path a a}
    (hσ : ∀ t, σ t = f (σ₀ t)) (hτ : ∀ t, τ t = f (τ₀ t)) (hυ : ∀ t, υ t = f (υ₀ t))
    (hφ : ∀ t, φ t = f (φ₀ t)) (γ : freeLoop X) (hγ : ∀ θ, γ θ = f (ev θ))
    {N : Subgroup (FundamentalGroup X x)} [N.Normal] (hγN : ¬loopClassMeets γ x N)
    {ρ : X → M} (Wdirect : BoundaryWordWitness Gd ρ (pathToCircle (σ.trans υ)))
    (Wcross :
      BoundaryWordWitness R.cell ρ (pathToCircle (σ.trans (τ.symm.trans (υ.trans φ.symm))))) :
    ∃ (S : hD.DescendingSurgery) (e : loopCircle ≃ₜ frontier S.cell.domain) (δ : freeLoop X),
      (∀ θ, ρ (δ θ) = S.cell (e θ)) ∧ ¬loopClassMeets δ x N := by
  refine exists_descendingSurgery_of_not_loopClassMeets_or_witness
    (S₁ := DescendingSurgery.ofBranchInjection hD hGd origin hinj hmiss)
    (S₂ := R.toDescendingSurgery)
    (w₁ := pathToCircle (σ.trans υ))
    (w₂ := pathToCircle (σ.trans (τ.symm.trans (υ.trans φ.symm))))
    Wdirect Wcross ?_
  exact not_loopClassMeets_or_not_loopClassMeets_of_four_boundary_arcs_preserving σ₀ τ₀ υ₀ φ₀
    ev hev (PathConnectedSpace.somePath x a) (PathConnectedSpace.somePath a b) hσ hτ hυ hφ γ hγ
    N hγN

theorem exists_descendingSurgery_not_loopClassMeets_reversing_witness_of_equiv
    {U : Set M} {hD : NormalSingularCellData D BdM B} {c : hD.singularSet.Branch}
    {Gd : SingularTwoCell M} (hGd : NormalSingularCellData Gd BdM B)
    (ebranch : hGd.singularSet.Branch ≃ {b : hD.singularSet.Branch // b ≠ c})
    (R : CrossSeamResolutionData hD c U)
    {Q : Type w} [TopologicalSpace Q] {p' q' u' v' : Q}
    (σ₀ : Path p' q') (τ₀ : Path q' u') (υ₀ : Path u' v') (φ₀ : Path v' p')
    (ev : loopCircle → Q)
    (hev : ∀ θ, ev θ = pathToCircle (σ₀.trans (τ₀.trans (υ₀.trans φ₀))) θ)
    {X : Type v} [TopologicalSpace X] [PathConnectedSpace X] {f : Q → X} {x a b : X}
    {σ υ : Path a b} {τ φ : Path b a}
    (hσ : ∀ t, σ t = f (σ₀ t)) (hτ : ∀ t, τ t = f (τ₀ t)) (hυ : ∀ t, υ t = f (υ₀ t))
    (hφ : ∀ t, φ t = f (φ₀ t)) (γ : freeLoop X) (hγ : ∀ θ, γ θ = f (ev θ))
    {N : Subgroup (FundamentalGroup X x)} [N.Normal] (hγN : ¬loopClassMeets γ x N)
    {ρ : X → M} (Wdirect : BoundaryWordWitness Gd ρ (pathToCircle (σ.trans υ.symm)))
    (Wcross : BoundaryWordWitness R.cell ρ (pathToCircle (σ.trans (φ.trans (υ.trans τ))))) :
    ∃ (S : hD.DescendingSurgery) (e : loopCircle ≃ₜ frontier S.cell.domain) (δ : freeLoop X),
      (∀ θ, ρ (δ θ) = S.cell (e θ)) ∧ ¬loopClassMeets δ x N :=
  exists_descendingSurgery_not_loopClassMeets_reversing_witness_of_injection hGd
    (fun b => (ebranch b).1) (Subtype.val_injective.comp ebranch.injective)
    (fun b => (ebranch b).2) R σ₀ τ₀ υ₀ φ₀ ev hev hσ hτ hυ hφ γ hγ hγN Wdirect Wcross

theorem exists_descendingSurgery_not_loopClassMeets_preserving_witness_of_equiv
    {U : Set M} {hD : NormalSingularCellData D BdM B} {c : hD.singularSet.Branch}
    {Gd : SingularTwoCell M} (hGd : NormalSingularCellData Gd BdM B)
    (ebranch : hGd.singularSet.Branch ≃ {b : hD.singularSet.Branch // b ≠ c})
    (R : CrossSeamResolutionData hD c U)
    {Q : Type w} [TopologicalSpace Q] {p' q' u' v' : Q}
    (σ₀ : Path p' q') (τ₀ : Path q' u') (υ₀ : Path u' v') (φ₀ : Path v' p')
    (ev : loopCircle → Q)
    (hev : ∀ θ, ev θ = pathToCircle (σ₀.trans (τ₀.trans (υ₀.trans φ₀))) θ)
    {X : Type v} [TopologicalSpace X] [PathConnectedSpace X] {f : Q → X} {x a b : X}
    {σ : Path a b} {τ : Path b b} {υ : Path b a} {φ : Path a a}
    (hσ : ∀ t, σ t = f (σ₀ t)) (hτ : ∀ t, τ t = f (τ₀ t)) (hυ : ∀ t, υ t = f (υ₀ t))
    (hφ : ∀ t, φ t = f (φ₀ t)) (γ : freeLoop X) (hγ : ∀ θ, γ θ = f (ev θ))
    {N : Subgroup (FundamentalGroup X x)} [N.Normal] (hγN : ¬loopClassMeets γ x N)
    {ρ : X → M} (Wdirect : BoundaryWordWitness Gd ρ (pathToCircle (σ.trans υ)))
    (Wcross :
      BoundaryWordWitness R.cell ρ (pathToCircle (σ.trans (τ.symm.trans (υ.trans φ.symm))))) :
    ∃ (S : hD.DescendingSurgery) (e : loopCircle ≃ₜ frontier S.cell.domain) (δ : freeLoop X),
      (∀ θ, ρ (δ θ) = S.cell (e θ)) ∧ ¬loopClassMeets δ x N :=
  exists_descendingSurgery_not_loopClassMeets_preserving_witness_of_injection hGd
    (fun b => (ebranch b).1) (Subtype.val_injective.comp ebranch.injective)
    (fun b => (ebranch b).2) R σ₀ τ₀ υ₀ φ₀ ev hev hσ hτ hυ hφ γ hγ hγN Wdirect Wcross

end NormalSingularCellData

namespace BoundaryWordWitness

section Lift

variable {M : Type u} [TopologicalSpace M] {X : Type v} [TopologicalSpace X] {ρ : X → M}

noncomputable def liftFreeLoop (hρ : IsEmbedding ρ) (w : freeLoop M)
    (hw : ∀ θ, w θ ∈ Set.range ρ) : freeLoop X :=
  ⟨fun θ => Classical.choose (Set.mem_range.mp (hw θ)),
    hρ.isInducing.continuous_iff.mpr <| by
      have hspec : (ρ ∘ fun θ => Classical.choose (Set.mem_range.mp (hw θ))) = ⇑w :=
        funext fun θ => Classical.choose_spec (Set.mem_range.mp (hw θ))
      rw [hspec]
      exact w.continuous⟩

theorem liftFreeLoop_apply (hρ : IsEmbedding ρ) (w : freeLoop M)
    (hw : ∀ θ, w θ ∈ Set.range ρ) (θ : loopCircle) :
    ρ (liftFreeLoop hρ w hw θ) = w θ :=
  Classical.choose_spec (Set.mem_range.mp (hw θ))

end Lift

section Manifold

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {X : Type v} [TopologicalSpace X] {G : SingularTwoCell M} {ρ : X → M}

noncomputable def ofManifoldRealization (hρ : IsEmbedding ρ)
    (e : loopCircle ≃ₜ frontier G.domain) {w : freeLoop M} (h : ∀ θ, G (e θ) = w θ)
    (hw : ∀ θ, w θ ∈ Set.range ρ) : BoundaryWordWitness G ρ (liftFreeLoop hρ w hw) :=
  ofRealization e fun θ => (liftFreeLoop_apply hρ w hw θ).trans (h θ).symm

@[simp]
theorem ofManifoldRealization_param (hρ : IsEmbedding ρ)
    (e : loopCircle ≃ₜ frontier G.domain) {w : freeLoop M} (h : ∀ θ, G (e θ) = w θ)
    (hw : ∀ θ, w θ ∈ Set.range ρ) : (ofManifoldRealization hρ e h hw).param = e :=
  rfl

@[simp]
theorem ofManifoldRealization_loop (hρ : IsEmbedding ρ)
    (e : loopCircle ≃ₜ frontier G.domain) {w : freeLoop M} (h : ∀ θ, G (e θ) = w θ)
    (hw : ∀ θ, w θ ∈ Set.range ρ) :
    (ofManifoldRealization hρ e h hw).loop = liftFreeLoop hρ w hw :=
  rfl

theorem exists_of_twoArcParametrization (hρ : IsEmbedding ρ)
    (hrange : Set.range ⇑G.boundary ⊆ Set.range ρ)
    (e : loopCircle ≃ₜ frontier G.domain) {y z : M} (α : Path y z) (ω : Path z y)
    (hparam : ∀ θ, G (e θ) = pathToCircle (α.trans ω) θ) :
    ∃ w : freeLoop X, Nonempty (BoundaryWordWitness G ρ w) ∧
      ∀ θ, ρ (w θ) = pathToCircle (α.trans ω) θ := by
  have hw : ∀ θ, pathToCircle (α.trans ω) θ ∈ Set.range ρ := fun θ =>
    hrange ⟨e θ, (G.boundary_apply (e θ)).trans (hparam θ)⟩
  exact ⟨liftFreeLoop hρ (pathToCircle (α.trans ω)) hw,
    ⟨ofManifoldRealization (w := pathToCircle (α.trans ω)) hρ e hparam hw⟩,
    fun θ => liftFreeLoop_apply hρ (pathToCircle (α.trans ω)) hw θ⟩

end Manifold

end BoundaryWordWitness

section NonVacuity

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem exists_boundaryWordWitness_image_subtypeVal (G : SingularTwoCell M)
    (param : loopCircle ≃ₜ frontier G.domain) :
    ∃ w : freeLoop ↥(⇑G '' G.domain),
      Nonempty (BoundaryWordWitness G (Subtype.val : ↥(⇑G '' G.domain) → M) w) ∧
        ∀ θ, (w θ : M) = G (param θ) := by
  have hρ : IsEmbedding (Subtype.val : ↥(⇑G '' G.domain) → M) :=
    _root_.Topology.IsEmbedding.subtypeVal
  have hw : ∀ θ, boundaryFreeLoop G param θ ∈
      Set.range (Subtype.val : ↥(⇑G '' G.domain) → M) := fun θ =>
    ⟨⟨G (param θ), (param θ : EuclideanSpace ℝ (Fin 2)),
      G.frontier_subset_domain (param θ).2, rfl⟩, rfl⟩
  exact ⟨BoundaryWordWitness.liftFreeLoop hρ (boundaryFreeLoop G param) hw,
    ⟨BoundaryWordWitness.ofManifoldRealization (w := boundaryFreeLoop G param) hρ param
      (fun _ => rfl) hw⟩,
    fun θ => BoundaryWordWitness.liftFreeLoop_apply hρ (boundaryFreeLoop G param) hw θ⟩

theorem range_subtypeVal_image_ne_univ (G : SingularTwoCell M)
    (h : ⇑G '' G.domain ≠ Set.univ) :
    Set.range (Subtype.val : ↥(⇑G '' G.domain) → M) ≠ Set.univ := by
  rwa [Subtype.range_val]

end NonVacuity

end DifferentialGeometry.Topology.PiecewiseLinear
