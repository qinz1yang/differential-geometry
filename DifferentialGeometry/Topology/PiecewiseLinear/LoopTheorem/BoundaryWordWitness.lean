/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallHomotopy
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryBranchDescent

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u v w

structure BoundaryWordWitness {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {X : Type v} [TopologicalSpace X]
    (G : SingularTwoCell M) (ρ : X → M) (word : freeLoop X) where
  param : loopCircle ≃ₜ frontier G.domain
  loop : freeLoop X
  realizes : ∀ θ, ρ (loop θ) = G (param θ)
  homotopic : loop.Homotopic word

theorem loopClassMeets_iff_of_homotopic {X : Type v} [TopologicalSpace X]
    [PathConnectedSpace X] {γ δ : freeLoop X} (h : γ.Homotopic δ) (x : X)
    (N : Subgroup (FundamentalGroup X x)) :
    loopClassMeets γ x N ↔ loopClassMeets δ x N := by
  unfold loopClassMeets
  rw [FreeLoop.conjugacyClass_eq_of_homotopic h x]

namespace BoundaryWordWitness

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {X : Type v} [TopologicalSpace X] {G : SingularTwoCell M} {ρ : X → M} {word : freeLoop X}

def ofRealization (e : loopCircle ≃ₜ frontier G.domain) (h : ∀ θ, ρ (word θ) = G (e θ)) :
    BoundaryWordWitness G ρ word where
  param := e
  loop := word
  realizes := h
  homotopic := ContinuousMap.Homotopic.refl word

theorem loopClassMeets_iff [PathConnectedSpace X] (W : BoundaryWordWitness G ρ word) (x : X)
    (N : Subgroup (FundamentalGroup X x)) :
    loopClassMeets W.loop x N ↔ loopClassMeets word x N :=
  loopClassMeets_iff_of_homotopic W.homotopic x N

end BoundaryWordWitness

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

theorem exists_descendingSurgery_of_not_loopClassMeets_or_witness
    {hD : NormalSingularCellData D BdM B} {X : Type v} [TopologicalSpace X]
    [PathConnectedSpace X] {x : X} {N : Subgroup (FundamentalGroup X x)} {ρ : X → M}
    {S₁ S₂ : hD.DescendingSurgery} {w₁ w₂ : freeLoop X}
    (W₁ : BoundaryWordWitness S₁.cell ρ w₁) (W₂ : BoundaryWordWitness S₂.cell ρ w₂)
    (hdichotomy : ¬loopClassMeets w₁ x N ∨ ¬loopClassMeets w₂ x N) :
    ∃ (S : hD.DescendingSurgery) (e : loopCircle ≃ₜ frontier S.cell.domain) (δ : freeLoop X),
      (∀ θ, ρ (δ θ) = S.cell (e θ)) ∧ ¬loopClassMeets δ x N := by
  rcases hdichotomy with h | h
  · exact ⟨S₁, W₁.param, W₁.loop, W₁.realizes, fun hc => h ((W₁.loopClassMeets_iff x N).mp hc)⟩
  · exact ⟨S₂, W₂.param, W₂.loop, W₂.realizes, fun hc => h ((W₂.loopClassMeets_iff x N).mp hc)⟩

theorem exists_descendingSurgery_not_loopClassMeets_reversing_witness
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
      (∀ θ, ρ (δ θ) = S.cell (e θ)) ∧ ¬loopClassMeets δ x N := by
  refine exists_descendingSurgery_of_not_loopClassMeets_or_witness
    (S₁ := DescendingSurgery.ofBranchEquiv hD hGd ebranch) (S₂ := R.toDescendingSurgery)
    (w₁ := pathToCircle (σ.trans υ.symm))
    (w₂ := pathToCircle (σ.trans (φ.trans (υ.trans τ))))
    Wdirect Wcross ?_
  exact not_loopClassMeets_or_not_loopClassMeets_of_four_boundary_arcs_reversing σ₀ τ₀ υ₀ φ₀
    ev hev (PathConnectedSpace.somePath x a) (PathConnectedSpace.somePath a b) hσ hτ hυ hφ γ hγ
    N hγN

theorem exists_descendingSurgery_not_loopClassMeets_preserving_witness
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
      (∀ θ, ρ (δ θ) = S.cell (e θ)) ∧ ¬loopClassMeets δ x N := by
  refine exists_descendingSurgery_of_not_loopClassMeets_or_witness
    (S₁ := DescendingSurgery.ofBranchEquiv hD hGd ebranch) (S₂ := R.toDescendingSurgery)
    (w₁ := pathToCircle (σ.trans υ))
    (w₂ := pathToCircle (σ.trans (τ.symm.trans (υ.trans φ.symm))))
    Wdirect Wcross ?_
  exact not_loopClassMeets_or_not_loopClassMeets_of_four_boundary_arcs_preserving σ₀ τ₀ υ₀ φ₀
    ev hev (PathConnectedSpace.somePath x a) (PathConnectedSpace.somePath a b) hσ hτ hυ hφ γ hγ
    N hγN

theorem exists_descendingSurgery_of_not_loopClassMeets_or_of_realizations
    {hD : NormalSingularCellData D BdM B} {X : Type v} [TopologicalSpace X]
    [PathConnectedSpace X] {x : X} {N : Subgroup (FundamentalGroup X x)} {ρ : X → M}
    {S₁ S₂ : hD.DescendingSurgery} {δ₁ δ₂ : freeLoop X}
    (e₁ : loopCircle ≃ₜ frontier S₁.cell.domain)
    (e₂ : loopCircle ≃ₜ frontier S₂.cell.domain)
    (h₁ : ∀ θ, ρ (δ₁ θ) = S₁.cell (e₁ θ)) (h₂ : ∀ θ, ρ (δ₂ θ) = S₂.cell (e₂ θ))
    (hdichotomy : ¬loopClassMeets δ₁ x N ∨ ¬loopClassMeets δ₂ x N) :
    ∃ (S : hD.DescendingSurgery) (e : loopCircle ≃ₜ frontier S.cell.domain) (δ : freeLoop X),
      (∀ θ, ρ (δ θ) = S.cell (e θ)) ∧ ¬loopClassMeets δ x N :=
  exists_descendingSurgery_of_not_loopClassMeets_or_witness
    (BoundaryWordWitness.ofRealization e₁ h₁) (BoundaryWordWitness.ofRealization e₂ h₂)
    hdichotomy

theorem exists_descendingSurgery_not_loopClassMeets_reversing_of_realizations
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
    {ρ : X → M} (edirect : loopCircle ≃ₜ frontier Gd.domain)
    (hdirect : ∀ θ, ρ (pathToCircle (σ.trans υ.symm) θ) = Gd (edirect θ))
    (ecross : loopCircle ≃ₜ frontier R.cell.domain)
    (hcross : ∀ θ, ρ (pathToCircle (σ.trans (φ.trans (υ.trans τ))) θ) = R.cell (ecross θ)) :
    ∃ (S : hD.DescendingSurgery) (e : loopCircle ≃ₜ frontier S.cell.domain) (δ : freeLoop X),
      (∀ θ, ρ (δ θ) = S.cell (e θ)) ∧ ¬loopClassMeets δ x N :=
  exists_descendingSurgery_not_loopClassMeets_reversing_witness hGd ebranch R σ₀ τ₀ υ₀ φ₀ ev
    hev hσ hτ hυ hφ γ hγ hγN (BoundaryWordWitness.ofRealization edirect hdirect)
    (BoundaryWordWitness.ofRealization ecross hcross)

theorem exists_descendingSurgery_not_loopClassMeets_preserving_of_realizations
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
    {ρ : X → M} (edirect : loopCircle ≃ₜ frontier Gd.domain)
    (hdirect : ∀ θ, ρ (pathToCircle (σ.trans υ) θ) = Gd (edirect θ))
    (ecross : loopCircle ≃ₜ frontier R.cell.domain)
    (hcross : ∀ θ,
      ρ (pathToCircle (σ.trans (τ.symm.trans (υ.trans φ.symm))) θ) = R.cell (ecross θ)) :
    ∃ (S : hD.DescendingSurgery) (e : loopCircle ≃ₜ frontier S.cell.domain) (δ : freeLoop X),
      (∀ θ, ρ (δ θ) = S.cell (e θ)) ∧ ¬loopClassMeets δ x N :=
  exists_descendingSurgery_not_loopClassMeets_preserving_witness hGd ebranch R σ₀ τ₀ υ₀ φ₀ ev
    hev hσ hτ hυ hφ γ hγ hγN (BoundaryWordWitness.ofRealization edirect hdirect)
    (BoundaryWordWitness.ofRealization ecross hcross)

end NormalSingularCellData

section NonVacuity

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

def boundaryFreeLoop (G : SingularTwoCell M) (param : loopCircle ≃ₜ frontier G.domain) :
    freeLoop M :=
  G.boundary.comp ⟨fun θ => param θ, param.continuous⟩

@[simp]
theorem boundaryFreeLoop_apply (G : SingularTwoCell M)
    (param : loopCircle ≃ₜ frontier G.domain) (θ : loopCircle) :
    boundaryFreeLoop G param θ = G (param θ) :=
  rfl

def BoundaryWordWitness.ofBoundary (G : SingularTwoCell M)
    (param : loopCircle ≃ₜ frontier G.domain) :
    BoundaryWordWitness G (id : M → M) (boundaryFreeLoop G param) where
  param := param
  loop := boundaryFreeLoop G param
  realizes := fun _ => rfl
  homotopic := ContinuousMap.Homotopic.refl _

theorem mem_doublePointSet_of_boundary_realization {X : Type v} [TopologicalSpace X]
    {G : SingularTwoCell M} {ρ : X → M} {word : freeLoop X}
    (e : loopCircle ≃ₜ frontier G.domain) (h : ∀ θ, ρ (word θ) = G (e θ))
    {θ₁ θ₂ : loopCircle} (hne : θ₁ ≠ θ₂) (hword : word θ₁ = word θ₂) :
    ρ (word θ₁) ∈ doublePointSet G (frontier G.domain) := by
  refine ⟨(e θ₁ : EuclideanSpace ℝ (Fin 2)), (e θ₁).2,
    (e θ₂ : EuclideanSpace ℝ (Fin 2)), (e θ₂).2, ?_, (h θ₁).symm, ?_⟩
  · exact fun hcoe => hne (e.injective (Subtype.ext hcoe))
  · rw [← h θ₂, ← hword]

theorem not_exists_realization_of_injOn_frontier {X : Type v} [TopologicalSpace X]
    {G : SingularTwoCell M} {ρ : X → M} {word : freeLoop X}
    (hinj : InjOn G (frontier G.domain)) {θ₁ θ₂ : loopCircle} (hne : θ₁ ≠ θ₂)
    (hword : word θ₁ = word θ₂) :
    ¬∃ e : loopCircle ≃ₜ frontier G.domain, ∀ θ, ρ (word θ) = G (e θ) := by
  rintro ⟨e, h⟩
  obtain ⟨p, hp, q, hq, hpq, hfp, hfq⟩ :=
    mem_doublePointSet_of_boundary_realization e h hne hword
  exact hpq (hinj hp hq (hfp.trans hfq.symm))

theorem nullhomotopic_boundaryFreeLoop (G : SingularTwoCell M)
    (param : loopCircle ≃ₜ frontier G.domain) : (boundaryFreeLoop G param).Nullhomotopic := by
  have := G.isPLBall_domain.contractibleSpace
  let d : C(G.domain, M) :=
    ⟨fun y => G y, continuousOn_iff_continuous_domRestrict.mp G.continuousOn⟩
  let pcd : C(loopCircle, G.domain) :=
    ⟨fun θ => ⟨(param θ : EuclideanSpace ℝ (Fin 2)),
        G.frontier_subset_domain (param θ).2⟩,
      (continuous_subtype_val.comp param.continuous).subtype_mk _⟩
  have hpcd : pcd.Nullhomotopic := by
    simpa only [ContinuousMap.id_comp] using (id_nullhomotopic G.domain).comp_left pcd
  have heq : boundaryFreeLoop G param = d.comp pcd := ContinuousMap.ext fun _ => rfl
  rw [heq]
  exact hpcd.comp_right d

theorem exists_boundaryWordWitness_const (G : SingularTwoCell M)
    (param : loopCircle ≃ₜ frontier G.domain) :
    ∃ y : M,
      Nonempty (BoundaryWordWitness G (id : M → M) (ContinuousMap.const loopCircle y)) := by
  obtain ⟨y, hy⟩ := nullhomotopic_boundaryFreeLoop G param
  exact ⟨y, ⟨⟨param, boundaryFreeLoop G param, fun _ => rfl, hy⟩⟩⟩

theorem nonempty_boundaryWordWitness_iff_nullhomotopic [PathConnectedSpace M]
    (G : SingularTwoCell M) (param : loopCircle ≃ₜ frontier G.domain) (word : freeLoop M) :
    Nonempty (BoundaryWordWitness G (id : M → M) word) ↔ word.Nullhomotopic := by
  have hne : Nonempty loopCircle := ⟨0⟩
  constructor
  · rintro ⟨W⟩
    have hloop : W.loop = boundaryFreeLoop G W.param := ContinuousMap.ext fun θ => W.realizes θ
    obtain ⟨y, hy⟩ := nullhomotopic_boundaryFreeLoop G W.param
    have hy' : W.loop.Homotopic (ContinuousMap.const loopCircle y) := by rw [hloop]; exact hy
    exact ⟨y, W.homotopic.symm.trans hy'⟩
  · rintro ⟨y, hy⟩
    obtain ⟨y', hy'⟩ := nullhomotopic_boundaryFreeLoop G param
    have hconst : (ContinuousMap.const loopCircle y').Homotopic
        (ContinuousMap.const loopCircle y) :=
      ContinuousMap.homotopic_const_iff.mpr (PathConnectedSpace.joined y' y)
    exact ⟨⟨param, boundaryFreeLoop G param, fun _ => rfl,
      hy'.trans (hconst.trans hy.symm)⟩⟩

theorem loopCircle_zero_ne_half : ((0 : ℝ) : loopCircle) ≠ ((1 / 2 : ℝ) : loopCircle) := by
  intro hcontra
  have hzero : (0 : ℝ) ∈ Ico (0 : ℝ) (0 + 1) := Set.mem_Ico.mpr ⟨le_rfl, by norm_num⟩
  have hhalf : (1 / 2 : ℝ) ∈ Ico (0 : ℝ) (0 + 1) := Set.mem_Ico.mpr ⟨by norm_num, by norm_num⟩
  have := (AddCircle.coe_eq_coe_iff_of_mem_Ico hzero hhalf).mp hcontra
  norm_num at this

theorem exists_boundaryWordWitness_not_exists_realization (G : SingularTwoCell M)
    (param : loopCircle ≃ₜ frontier G.domain) (hinj : InjOn G (frontier G.domain)) :
    ∃ word : freeLoop M,
      (∃ θ₁ θ₂ : loopCircle, θ₁ ≠ θ₂ ∧ word θ₁ = word θ₂) ∧
        Nonempty (BoundaryWordWitness G (id : M → M) word) ∧
        ¬∃ e : loopCircle ≃ₜ frontier G.domain, ∀ θ, (id : M → M) (word θ) = G (e θ) := by
  obtain ⟨y, hW⟩ := exists_boundaryWordWitness_const G param
  refine ⟨ContinuousMap.const loopCircle y,
    ⟨((0 : ℝ) : loopCircle), ((1 / 2 : ℝ) : loopCircle), loopCircle_zero_ne_half, rfl⟩, hW, ?_⟩
  exact not_exists_realization_of_injOn_frontier (ρ := (id : M → M))
    (word := ContinuousMap.const loopCircle y) hinj loopCircle_zero_ne_half rfl

end NonVacuity

end DifferentialGeometry.Topology.PiecewiseLinear
