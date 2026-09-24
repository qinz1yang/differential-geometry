import DifferentialGeometry.Topology.Manifold.ClosedBall.Coordinates
import Mathlib.Topology.Algebra.ContinuousAffineEquiv
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Calculus.FDeriv.Affine

noncomputable section

open Set Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

open DifferentialGeometry.Topology.Handle

variable {m : ℕ}
local notation "EuN" => EuclideanSpace ℝ (Fin (m + 1))
local instance : ChartedSpace (EuclideanHalfSpace (m + 1)) (ClosedCell (m + 1)) :=
  closedCellChartedSpaceSucc m
local instance : IsManifold (𝓡∂ (m + 1)) ∞ (ClosedCell (m + 1)) := closedCellIsManifold m

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

theorem contMDiff_extChartAt_symm_comp_affine_closedCell
    {k : ℕ∞} [IsManifold I k M] (α : M) (e : EuN ≃ᴬ[ℝ] E)
    (he : ∀ x : ClosedCell (m + 1), e x.val ∈ interior (extChartAt I α).target) :
    ContMDiff (𝓡∂ (m + 1)) I k
      (fun x : ClosedCell (m + 1) => (extChartAt I α).symm (e x.val)) := by
  have hi : ContMDiff (𝓡∂ (m + 1)) (𝓡 (m + 1)) k
      (Subtype.val : ClosedCell (m + 1) → EuN) :=
    (closedCellInclusion_contMDiff m).of_le (WithTop.coe_le_coe.mpr le_top)
  have ha : ContMDiff (𝓡 (m + 1)) 𝓘(ℝ, E) k e := e.toContinuousAffineMap.contDiff.contMDiff
  intro x
  have hc := (contMDiffWithinAt_extChartAt_symm_target (I := I) (n := (k : ℕ∞ω)) α
    (interior_subset (he x))).contMDiffAt (mem_interior_iff_mem_nhds.mp (he x))
  exact hc.comp x (ha.comp hi x)

theorem injective_mfderiv_extChartAt_symm_comp_affine_closedCell
    [IsManifold I 1 M] (α : M) (e : EuN ≃ᴬ[ℝ] E)
    {x : ClosedCell (m + 1)} (he : e x.val ∈ interior (extChartAt I α).target) :
    Function.Injective (mfderiv (𝓡∂ (m + 1)) I
      (fun y : ClosedCell (m + 1) => (extChartAt I α).symm (e y.val)) x) := by
  have hrange : range I ∈ 𝓝 (e x.val) := Filter.mem_of_superset
    (mem_interior_iff_mem_nhds.mp he) (extChartAt_target_subset_range α)
  have hc := (mdifferentiableWithinAt_extChartAt_symm (I := I)
    (interior_subset he)).mdifferentiableAt hrange
  have ha : MDifferentiableAt (𝓡 (m + 1)) 𝓘(ℝ, E) e x.val :=
    e.toContinuousAffineMap.differentiableAt.mdifferentiableAt
  have hi := (closedCellInclusion_contMDiff m).mdifferentiableAt (by simp) (x := x)
  have hchain := mfderiv_comp x hc (ha.comp x hi)
  have hinner := mfderiv_comp x ha hi
  change Function.Injective (mfderiv (𝓡∂ (m + 1)) I
    ((extChartAt I α).symm ∘ e ∘ Subtype.val) x)
  rw [hchain, hinner]
  have hccomp := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I) (interior_subset he)
  rw [mfderivWithin_of_mem_nhds hrange] at hccomp
  have hci : Function.Injective (mfderiv 𝓘(ℝ, E) I (extChartAt I α).symm (e x.val)) := by
    apply Function.LeftInverse.injective (g := mfderiv I 𝓘(ℝ, E)
      (extChartAt I α) ((extChartAt I α).symm (e x.val)))
    intro v
    exact congrArg (fun L => L v) hccomp
  have hai : Function.Injective (mfderiv (𝓡 (m + 1)) 𝓘(ℝ, E) e x.val) := by
    rw [mfderiv_eq_fderiv]
    have hd : fderiv ℝ (e : EuN → E) x.val = e.toContinuousAffineMap.contLinear :=
      e.toContinuousAffineMap.fderiv
    rw [hd]
    exact e.toAffineEquiv.linear.injective
  exact hci.comp (hai.comp (injective_mfderiv_closedCell_inclusion x))

theorem mfderiv_extChartAt_symm_comp_affine_closedCell_of_norm_lt_one
    [IsManifold I 1 M] (α : M) (e : EuN ≃ᴬ[ℝ] E)
    {x : ClosedCell (m + 1)} (he : e x.val ∈ interior (extChartAt I α).target)
    (hx : ‖x.val‖ < 1) :
    mfderiv (𝓡∂ (m + 1)) I
      (fun y : ClosedCell (m + 1) => (extChartAt I α).symm (e y.val)) x =
      (mfderiv 𝓘(ℝ, E) I (extChartAt I α).symm (e x.val)).comp
        e.toContinuousAffineMap.contLinear := by
  have hrange : range I ∈ 𝓝 (e x.val) := Filter.mem_of_superset
    (mem_interior_iff_mem_nhds.mp he) (extChartAt_target_subset_range α)
  have hc := (mdifferentiableWithinAt_extChartAt_symm (I := I)
    (interior_subset he)).mdifferentiableAt hrange
  have ha : MDifferentiableAt (𝓡 (m + 1)) 𝓘(ℝ, E) e x.val :=
    e.toContinuousAffineMap.differentiableAt.mdifferentiableAt
  have hi := (closedCellInclusion_contMDiff m).mdifferentiableAt (by simp) (x := x)
  have hchain := mfderiv_comp x hc (ha.comp x hi)
  have hinner := mfderiv_comp x ha hi
  change mfderiv (𝓡∂ (m + 1)) I ((extChartAt I α).symm ∘ e ∘ Subtype.val) x = _
  rw [hchain, hinner, mfderiv_closedCell_inclusion_of_norm_lt_one hx]
  ext v
  change mfderiv 𝓘(ℝ, E) I (extChartAt I α).symm (e x.val)
    (mfderiv (𝓡 (m + 1)) 𝓘(ℝ, E) e x.val v) = _
  rw [mfderiv_eq_fderiv]
  have hd : fderiv ℝ (e : EuN → E) x.val = e.toContinuousAffineMap.contLinear :=
    e.toContinuousAffineMap.fderiv
  rw [hd]
  rfl

end DifferentialGeometry.Topology.Manifold
