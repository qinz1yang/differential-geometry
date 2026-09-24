import DifferentialGeometry.Topology.Diffeomorph.Radial
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Geometry.Manifold.LocalDiffeomorph

noncomputable section

open Set Metric
open scoped Manifold ContDiff

namespace PartialDiffeomorph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞}

theorem exists_closedBall_subset_source_of_unit_closedBall
    (B : PartialDiffeomorph 𝓘(ℝ, E) J E M n)
    (hB : closedBall (0 : E) 1 ⊆ B.source) (r : ℝ) :
    ∃ B' : PartialDiffeomorph 𝓘(ℝ, E) J E M n,
      closedBall (0 : E) r ⊆ B'.source ∧
      EqOn B' B (sphere (0 : E) 1) ∧
      B' '' ball (0 : E) 1 = B '' ball (0 : E) 1 ∧
      B' '' closedBall (0 : E) 1 = B '' closedBall (0 : E) 1 ∧
      B' '' sphere (0 : E) 1 = B '' sphere (0 : E) 1 := by
  obtain ⟨δ, hδ, hδsub⟩ :=
    (isCompact_closedBall (0 : E) 1).exists_cthickening_subset_open B.open_source hB
  have hsub : closedBall (0 : E) (δ + 1) ⊆ B.source := by
    rwa [cthickening_closedBall hδ.le (by norm_num : (0 : ℝ) ≤ 1)] at hδsub
  obtain ⟨G, hGfix, hGb, hGc, hGs, hGsource⟩ :=
    Diffeomorph.exists_diffeomorph_image_closedBall_subset_ball (E := E) r
      (lt_add_of_pos_left 1 hδ)
  let G' : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E n :=
    { G with
      contMDiff_toFun := G.contMDiff.of_le (by simp)
      contMDiff_invFun := G.symm.contMDiff.of_le (by simp) }
  let B' := G'.toPartialDiffeomorph.trans B
  refine ⟨B', ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨mem_univ _, hsub (ball_subset_closedBall (hGsource ⟨x, hx, rfl⟩))⟩
  · intro x hx
    change B (G x) = B x
    rw [hGfix hx]
    rfl
  · change (B ∘ G) '' ball (0 : E) 1 = _
    rw [Set.image_comp, hGb]
  · change (B ∘ G) '' closedBall (0 : E) 1 = _
    rw [Set.image_comp, hGc]
  · change (B ∘ G) '' sphere (0 : E) 1 = _
    rw [Set.image_comp, hGs]

end PartialDiffeomorph
