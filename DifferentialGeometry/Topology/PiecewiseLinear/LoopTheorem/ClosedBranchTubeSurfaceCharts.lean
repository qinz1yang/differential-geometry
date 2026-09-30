/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CrossHalfPlaneCharts
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryBranchTubeCharts
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchDeletion

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_branchSurface_disks
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hL : IsCombinatorialManifold 3 L) :
    letI := combinatorialChartedSpace L hL
    ∀ {D : SingularTwoCell L.space} {BdM B : Set L.space}
      (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch},
      ¬hD.singularSet.IsBoundaryBranch c → ∀ y ∈ hD.singularSet.branchCarrier c,
        ∃ (ψ : (ℝ × ℝ) × ℝ → E) (V : Set ((ℝ × ℝ) × ℝ)) (Ω W : Set E)
          (P : Fin 4 → Set E) (q : Fin 4 → (Fin 3 → ℝ) → E),
          IsOpen V ∧ IsOpen Ω ∧ IsOpen W ∧ (y : E) ∈ W ∧ W ⊆ Ω ∧
          IsPLHomeomorphOn ψ V (L.space ∩ Ω) ∧
          (∀ p ∈ V, ψ p ∈ Subtype.val '' (D '' D.domain) ↔ p ∈ crossPlanes) ∧
          (∀ p ∈ V, ψ p ∈ Subtype.val '' hD.singularSet.branchCarrier c ↔ p.1 = 0) ∧
          (∀ i, IsPLHomeomorphOn (q i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (P i)) ∧
          (∀ i, P i ⊆ L.space ∩ Subtype.val '' (D '' D.domain)) ∧
          (∀ x ∈ L.space ∩ W, ∀ i,
            x ∈ P i ↔ Function.invFunOn ψ V x ∈ crossHalfPlane i) ∧
          ∀ x ∈ L.space ∩ W, ∀ i,
            x ∈ q i '' stdSimplexBoundary 2 ↔
              x ∈ Subtype.val '' hD.singularSet.branchCarrier c := by
  let _ := combinatorialChartedSpace L hL
  intro D BdM B hD c hc y hy
  let T := hD.singularSet
  let _ : Finite T.Branch := T.finite_branch
  let O : Set L.space := (doublePointSet D D.domain \ T.branchCarrier c)ᶜ
  have hclosed : IsClosed (doublePointSet D D.domain \ T.branchCarrier c) := by
    rw [← T.iUnion_branchCarrier_ne c]
    exact isClosed_iUnion_of_finite fun b => T.isClosed_branchCarrier b.1
  have hO : IsOpen O := hclosed.isOpen_compl
  have hyO : y ∈ O := fun h => h.2 hy
  have hyDP : y ∈ doublePointSet D D.domain := T.branchCarrier_subset_doublePointSet c hy
  have hyBd : y ∉ BdM :=
    disjoint_left.mp (T.branchCarrier_disjoint_boundary_of_not_isBoundaryBranch hc) hy
  obtain ⟨ψ, V, Ω, hV, hΩ, hψ, hyΩ, hF, hDP, hψO⟩ :=
    exists_straighteningChart_of_notMem_boundary L hL hD hyDP hyBd hO hyO
  have hΓ : ∀ p ∈ V, ψ p ∈ Subtype.val '' T.branchCarrier c ↔ p.1 = 0 := by
    intro p hp
    have hiff : ψ p ∈ Subtype.val '' T.branchCarrier c ↔
        ψ p ∈ Subtype.val '' doublePointSet D D.domain := by
      constructor
      · intro hx
        exact image_mono (T.branchCarrier_subset_doublePointSet c) hx
      · intro hmem
        obtain ⟨u, huO, hu⟩ := hψO p hp
        have huDP : u ∈ doublePointSet D D.domain := by
          rwa [← hu, Subtype.val_injective.mem_set_image] at hmem
        refine ⟨u, ?_, hu⟩
        by_contra hnot
        exact huO ⟨huDP, hnot⟩
    exact hiff.trans (hDP p hp)
  obtain ⟨W, P, q, hW, hyW, hWΩ, hq, hP, hread, hbd⟩ :=
    hψ.exists_crossHalfPlane_disks hV hΩ hF hΓ ⟨y.2, hyΩ⟩ ⟨y, hy, rfl⟩
  exact ⟨ψ, V, Ω, W, P, q, hV, hΩ, hW, hyW, hWΩ, hψ, hF, hΓ, hq, hP, hread, hbd⟩

end DifferentialGeometry.Topology.PiecewiseLinear
