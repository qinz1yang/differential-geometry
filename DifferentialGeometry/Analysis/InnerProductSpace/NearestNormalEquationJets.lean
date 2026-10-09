import DifferentialGeometry.Analysis.InnerProductSpace.NormalGraphAffineRemainderJets
import DifferentialGeometry.Analysis.InnerProductSpace.OrthogonalErrorCoordinates

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff

namespace DifferentialGeometry.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem norm_iteratedFDeriv_nearest_normal_equation_remainder_le
    (L : Submodule ℝ H) [CompleteSpace L] [CompleteSpace Lᗮ]
    (o : H) (g : L → Lᗮ) (R a : ℝ) (hR : 0 < R)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (j : ℕ)
    (hg : ContDiffOn ℝ (j + 1 : ℕ) g (ball (0 : L) (4 * R)))
    (hjet : ∀ i ≤ j + 1, ∀ t ∈ ball (0 : L) (4 * R),
      ‖iteratedFDeriv ℝ i g t‖ ≤ a * R * (R⁻¹) ^ i)
    (p : H × L) (hp : p ∈ ball o (2 * R) ×ˢ ball (0 : L) (2 * R)) :
    ‖iteratedFDeriv ℝ j (fun y : H × L =>
      (ContinuousLinearMap.adjoint
        (fderiv ℝ g (L.orthogonalProjectionOnto (y.1 - o) + y.2)))
          (g (L.orthogonalProjectionOnto (y.1 - o) + y.2) -
            Lᗮ.orthogonalProjectionOnto (y.1 - o))) p‖ ≤
      (3 * (4 : ℝ) ^ j) * a * R * (R⁻¹) ^ j := by
  let A : (H × L) →L[ℝ] L :=
    L.orthogonalProjectionOnto.coprod (ContinuousLinearMap.id ℝ L)
  let B : (H × L) →L[ℝ] Lᗮ :=
    Lᗮ.orthogonalProjectionOnto.comp (ContinuousLinearMap.fst ℝ H L)
  let a₀ : L := -L.orthogonalProjectionOnto o
  let b₀ : Lᗮ := -Lᗮ.orthogonalProjectionOnto o
  have hq (y : H × L) :
      a₀ + A y = L.orthogonalProjectionOnto (y.1 - o) + y.2 := by
    change -L.orthogonalProjectionOnto o +
      (L.orthogonalProjectionOnto y.1 + y.2) = _
    rw [map_sub]
    abel
  have hv (y : H × L) : b₀ + B y = Lᗮ.orthogonalProjectionOnto (y.1 - o) := by
    change -Lᗮ.orthogonalProjectionOnto o + Lᗮ.orthogonalProjectionOnto y.1 = _
    rw [map_sub]
    abel
  have hA : ‖A‖ ≤ 2 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro y
    change ‖L.orthogonalProjectionOnto y.1 + y.2‖ ≤ 2 * ‖y‖
    have h1 := L.norm_orthogonalProjectionOnto_apply_le y.1
    have h2 : ‖y.1‖ ≤ ‖y‖ := le_max_left _ _
    have h3 : ‖y.2‖ ≤ ‖y‖ := le_max_right _ _
    have h4 := norm_add_le (L.orthogonalProjectionOnto y.1) y.2
    linarith
  have hB : ‖B‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro y
    change ‖Lᗮ.orthogonalProjectionOnto y.1‖ ≤ 1 * ‖y‖
    simpa only [one_mul] using
      (Lᗮ.norm_orthogonalProjectionOnto_apply_le y.1).trans (norm_fst_le y)
  have hp1 : ‖p.1 - o‖ < 2 * R := by
    simpa only [mem_ball, dist_eq_norm] using hp.1
  have hp2 : ‖p.2‖ < 2 * R := by
    simpa only [mem_ball, dist_zero_right] using hp.2
  have hmem : a₀ + A p ∈ ball (0 : L) (4 * R) := by
    rw [hq, mem_ball, dist_zero_right]
    have h1 := (L.norm_orthogonalProjectionOnto_apply_le (p.1 - o)).trans_lt hp1
    exact (norm_add_le _ _).trans_lt (by linarith)
  have hvnorm : ‖b₀ + B p‖ ≤ 2 * R := by
    rw [hv]
    exact (Lᗮ.norm_orthogonalProjectionOnto_apply_le (p.1 - o)).trans hp1.le
  have h := norm_iteratedFDeriv_affine_normal_graph_remainder_le_scaled
    g a₀ A b₀ B (ball (0 : L) (4 * R)) isOpen_ball j hg p hmem
    R a 2 hR ha0 ha1 (by norm_num) hA hB hvnorm
    (fun i hi => hjet i hi _ hmem)
  simpa only [hq, hv, show (2 : ℝ) * 2 = 4 by norm_num] using h

end DifferentialGeometry.Analysis
