import DifferentialGeometry.Analysis.Elliptic.MetricExtension.ClosedCellDensity
import DifferentialGeometry.Geometry.Metric.Pullback.AffineCoefficients
import DifferentialGeometry.Analysis.Matrix.SqrtDeterminantScaling
import Mathlib.Tactic.Abel

noncomputable section

open Manifold Set
open scoped ContDiff Manifold Matrix Topology

namespace DifferentialGeometry.Analysis.Laplacian.MetricExtension

open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology
open DifferentialGeometry.Topology.Handle

private local instance (m : ℕ) :
    ChartedSpace (EuclideanHalfSpace (m + 1)) (ClosedCell (m + 1)) :=
  closedCellChartedSpaceSucc m

private local instance (m : ℕ) :
    IsManifold (𝓡∂ (m + 1)) ∞ (ClosedCell (m + 1)) :=
  closedCellIsManifold m

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "V" => EuclideanSpace ℝ (Fin (m + 1))
local notation "W" => EuclideanSpace ℝ (Fin (Module.finrank ℝ V))

private local instance : T2Space V := inferInstance

private theorem closedCell_affine_argument_eq (c : V) (r : ℝ) (y : W) :
    (toEuclidean (E := V)).symm
        ((toEuclidean (E := V)) c -
          r • (toEuclidean (E := V)) (EuclideanSpace.basisFun (Fin (m + 1)) ℝ 0) +
          r • y) =
      c + r • closedCellShiftSucc m (-1) ((toEuclidean (E := V)).symm y) := by
  simp only [map_add, map_sub, map_smul, (toEuclidean (E := V)).symm_apply_apply,
    closedCellShiftSucc_eq_add, neg_one_smul, smul_add, smul_neg]
  abel

theorem gramOnEuclid_closedCellPullbackMetricFamily_affine
    (D : RealTimeInterval) (g : ℝ → SmoothRiemannianMetric I M)
    (Φ : PartialDiffeomorph (𝓡 (m + 1)) I V M ∞)
    (c : V) {r : ℝ} (hr : 0 < r)
    (hsource : Metric.closedBall c r ⊆ Φ.source)
    (t : ℝ) (α : ClosedCell (m + 1)) (hα : ‖α.val‖ < 1) {y : W}
    (hy : y ∈ toEuclidean (E := V) '' interior (extChartAt (𝓡∂ (m + 1)) α).target) :
    let b : W := (toEuclidean (E := V)) c -
      r • (toEuclidean (E := V)) (EuclideanSpace.basisFun (Fin (m + 1)) ℝ 0)
    let Ψ : W → M := fun z => Φ ((toEuclidean (E := V)).symm z)
    Matrix.of (fun i j => gramOnEuclid
        ((closedCellPullbackMetricFamily D g Φ c hr hsource).metric t) α i j y) =
      r ^ 2 • Matrix.of (fun i j => pullbackMetricCoefficients (g t) Ψ (b + r • y)
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) := by
  intro b Ψ
  have htarget : (toEuclidean (E := V)).symm y ∈
      (extChartAt (𝓡∂ (m + 1)) α).target :=
    toEuclidean_symm_mem_target ((image_mono interior_subset) hy)
  have hnorm : ‖closedCellShiftSucc m (-1) ((toEuclidean (E := V)).symm y)‖ ≤ 1 :=
    ((mem_closedCell_extChartAt_target_iff_of_norm_lt_one α hα
      ((toEuclidean (E := V)).symm y)).mp htarget).le
  have hmem : (toEuclidean (E := V)).symm (b + r • y) ∈ Φ.source := by
    change (toEuclidean (E := V)).symm
      ((toEuclidean (E := V)) c -
        r • (toEuclidean (E := V)) (EuclideanSpace.basisFun (Fin (m + 1)) ℝ 0) +
        r • y) ∈ Φ.source
    rw [closedCell_affine_argument_eq]
    apply hsource
    change dist (c + r • closedCellShiftSucc m (-1)
      ((toEuclidean (E := V)).symm y)) c ≤ r
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hr]
    exact (mul_le_mul_of_nonneg_left hnorm hr.le).trans_eq (mul_one r)
  have hΦ : MDifferentiableAt (𝓡 (m + 1)) I Φ
      ((toEuclidean (E := V)).symm (b + r • y)) :=
    (Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds hmem)).mdifferentiableAt
      (by simp)
  have hP : MDifferentiableAt 𝓘(ℝ, W) (𝓡 (m + 1))
      (toEuclidean (E := V)).symm (b + r • y) :=
    mdifferentiableAt_iff_differentiableAt.mpr (toEuclidean (E := V)).symm.differentiableAt
  have hΨ : MDifferentiableAt 𝓘(ℝ, W) I Ψ (b + r • y) :=
    hΦ.comp (b + r • y) hP
  have hfun :
      (fun z : W => Φ (c + r • closedCellShiftSucc m (-1)
        ((toEuclidean (E := V)).symm z))) = (fun z => Ψ (b + r • z)) := by
    funext z
    exact congrArg Φ (closedCell_affine_argument_eq c r z).symm
  funext i j
  change gramOnEuclid
      ((closedCellPullbackMetricFamily D g Φ c hr hsource).metric t) α i j y =
    r ^ 2 * pullbackMetricCoefficients (g t) Ψ (b + r • y)
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  rw [gramOnEuclid_closedCellPullbackMetricFamily D g Φ c hr hsource t α hα hy i j,
    hfun]
  exact pullbackMetricCoefficients_comp_add_smul (g t) b r hΨ
    (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

theorem densityOnEuclid_closedCellPullbackMetricFamily_affine
    (D : RealTimeInterval) (g : ℝ → SmoothRiemannianMetric I M)
    (Φ : PartialDiffeomorph (𝓡 (m + 1)) I V M ∞)
    (c : V) {r : ℝ} (hr : 0 < r)
    (hsource : Metric.closedBall c r ⊆ Φ.source)
    (t : ℝ) (α : ClosedCell (m + 1)) (hα : ‖α.val‖ < 1) {y : W}
    (hy : y ∈ toEuclidean (E := V) '' interior (extChartAt (𝓡∂ (m + 1)) α).target) :
    let b : W := (toEuclidean (E := V)) c -
      r • (toEuclidean (E := V)) (EuclideanSpace.basisFun (Fin (m + 1)) ℝ 0)
    let Ψ : W → M := fun z => Φ ((toEuclidean (E := V)).symm z)
    let G : Matrix (Fin (Module.finrank ℝ V)) (Fin (Module.finrank ℝ V)) ℝ :=
      Matrix.of (fun i j => pullbackMetricCoefficients (g t) Ψ (b + r • y)
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
    densityOnEuclid
        ((closedCellPullbackMetricFamily D g Φ c hr hsource).metric t) α y =
      r ^ Module.finrank ℝ V * Real.sqrt G.det := by
  intro b Ψ G
  have hgram := gramOnEuclid_closedCellPullbackMetricFamily_affine
    D g Φ c hr hsource t α hα hy
  change Matrix.of (fun i j => gramOnEuclid
    ((closedCellPullbackMetricFamily D g Φ c hr hsource).metric t) α i j y) = r ^ 2 • G
    at hgram
  rw [densityOnEuclid_eq_sqrt_det, hgram]
  simpa only [Fintype.card_fin] using Matrix.sqrt_det_sq_smul_of_nonneg G hr.le

theorem weightedInvGramOnEuclid_closedCellPullbackMetricFamily_affine
    (D : RealTimeInterval) (g : ℝ → SmoothRiemannianMetric I M)
    (Φ : PartialDiffeomorph (𝓡 (m + 1)) I V M ∞)
    (c : V) {r : ℝ} (hr : 0 < r)
    (hsource : Metric.closedBall c r ⊆ Φ.source)
    (t : ℝ) (α : ClosedCell (m + 1)) (hα : ‖α.val‖ < 1) {y : W}
    (hy : y ∈ toEuclidean (E := V) '' interior (extChartAt (𝓡∂ (m + 1)) α).target)
    (i j : Fin (Module.finrank ℝ V)) :
    let b : W := (toEuclidean (E := V)) c -
      r • (toEuclidean (E := V)) (EuclideanSpace.basisFun (Fin (m + 1)) ℝ 0)
    let Ψ : W → M := fun z => Φ ((toEuclidean (E := V)).symm z)
    let G : Matrix (Fin (Module.finrank ℝ V)) (Fin (Module.finrank ℝ V)) ℝ :=
      Matrix.of (fun k l => pullbackMetricCoefficients (g t) Ψ (b + r • y)
        (EuclideanSpace.single k 1) (EuclideanSpace.single l 1))
    weightedInvGramOnEuclid
        ((closedCellPullbackMetricFamily D g Φ c hr hsource).metric t) α i j y =
      (r ^ Module.finrank ℝ V / r ^ 2) * (Real.sqrt G.det * G⁻¹ i j) := by
  intro b Ψ G
  have hgram := gramOnEuclid_closedCellPullbackMetricFamily_affine
    D g Φ c hr hsource t α hα hy
  change Matrix.of (fun k l => gramOnEuclid
    ((closedCellPullbackMetricFamily D g Φ c hr hsource).metric t) α k l y) = r ^ 2 • G
    at hgram
  rw [weightedInvGramOnEuclid_eq_sqrt_det_mul_inv, hgram]
  simpa only [Fintype.card_fin] using
    Matrix.sqrt_det_mul_inv_sq_smul_of_nonneg G hr.le i j

end DifferentialGeometry.Analysis.Laplacian.MetricExtension
