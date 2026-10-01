import DifferentialGeometry.Analysis.InnerProductSpace.ProjectionGap
import DifferentialGeometry.Analysis.InnerProductSpace.AffineProjectionDistance
import Mathlib.Topology.MetricSpace.HausdorffDistance

set_option autoImplicit false
noncomputable section
open Set Metric

namespace GC.MetricGeometry
section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem normal_offset_and_projection_gap_le_of_large_affine_hausdorffEDist
    (P Q : Submodule ℝ H) [FiniteDimensional ℝ P] [FiniteDimensional ℝ Q]
    (hdim : Module.finrank ℝ P = Module.finrank ℝ Q)
    (T : Set H) (o i : H) (hi : i ∈ T)
    {r₀ rᵢ A L δ : ℝ} (hr₀ : 0 < r₀) (hA : 1 ≤ A)
    (hlower : r₀ / A ≤ rᵢ) (hupper : rᵢ ≤ A * r₀)
    (hcenter : ‖i - o‖ ≤ L * r₀) (hδ : 0 < δ)
    (hδsmall : δ < 1 / (4 * (A + 1)))
    (hinterior : δ * (L + 2) < 1)
    (hcloud₀ : hausdorffEDist (T ∩ ball o (r₀ / δ))
      ((AffineSubspace.mk' o P : Set H) ∩ ball o (r₀ / δ)) ≤ ENNReal.ofReal (δ * r₀))
    (hcloudᵢ : hausdorffEDist (T ∩ ball i (rᵢ / δ))
      ((AffineSubspace.mk' i Q : Set H) ∩ ball i (rᵢ / δ)) ≤ ENNReal.ofReal (δ * rᵢ)) :
    ‖Pᗮ.starProjection (i - o)‖ ≤ δ * r₀ ∧
      ‖Pᗮ.starProjection - Qᗮ.starProjection‖ ≤ 6 * (A + 1) * δ := by
  have hApos : 0 < A := by linarith
  have hrᵢ : 0 < rᵢ := (div_pos hr₀ hApos).trans_le hlower
  have hbudget : δ * (4 * (A + 1)) < 1 :=
    (lt_div_iff₀ (by positivity)).mp hδsmall
  have hAδ : A * δ < 1 / 4 := by nlinarith
  have htestlarge : (L + 2) * r₀ < r₀ / δ := by
    apply (lt_div_iff₀ hδ).mpr
    have hh := mul_lt_mul_of_pos_right hinterior hr₀
    nlinarith
  have hradius : r₀ < rᵢ / δ := by
    apply (lt_div_iff₀ hδ).mpr
    have hlo : r₀ ≤ A * rᵢ := by
      have h := (div_le_iff₀ hApos).mp hlower
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hlo hδ.le
    have hsmall := mul_lt_mul_of_pos_right hAδ hrᵢ
    nlinarith
  let N : H →L[ℝ] H := Pᗮ.starProjection
  have hnormal (z : H) (hz : z ∈ T) (hnear : dist z o < r₀ / δ) :
      ‖N (z - o)‖ ≤ δ * r₀ := by
    have he : infEDist z (AffineSubspace.mk' o P : Set H) ≤ ENNReal.ofReal (δ * r₀) :=
      (infEDist_anti inter_subset_left).trans
        ((infEDist_le_hausdorffEDist_of_mem
          (show z ∈ T ∩ ball o (r₀ / δ) from ⟨hz, hnear⟩)).trans hcloud₀)
    have hreal : infDist z (AffineSubspace.mk' o P : Set H) ≤ δ * r₀ := by
      simpa only [Metric.infDist, ENNReal.toReal_ofReal (mul_pos hδ hr₀).le] using
        (ENNReal.toReal_mono ENNReal.ofReal_ne_top he)
    rw [← P.norm_sub_starProjection_eq_infDist_affine] at hreal
    simpa only [N, Submodule.starProjection_orthogonal_val] using hreal
  have hnormalᵢ : ‖N (i - o)‖ ≤ δ * r₀ := by
    apply hnormal i hi
    have hdist : dist i o ≤ L * r₀ := by simpa only [dist_eq_norm] using hcenter
    exact hdist.trans_lt ((by nlinarith : L * r₀ < (L + 2) * r₀).trans htestlarge)
  have hunit (u : H) (hu : u ∈ Q) (hnorm : ‖u‖ = 1) :
      ‖N u‖ ≤ (2 * A + 2) * δ := by
    let y : H := i + r₀ • u
    have hydist : dist y i = r₀ := by
      simp only [y, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos hr₀, hnorm, mul_one]
    have hyplane : y ∈ (AffineSubspace.mk' i Q : Set H) := by
      change y - i ∈ Q
      simpa only [y, add_sub_cancel_left] using Q.smul_mem r₀ hu
    have hy : y ∈ (AffineSubspace.mk' i Q : Set H) ∩ ball i (rᵢ / δ) :=
      ⟨hyplane, by simpa only [mem_ball, hydist] using hradius⟩
    have hstrict : ENNReal.ofReal (δ * rᵢ) < ENNReal.ofReal (2 * δ * rᵢ) := by
      apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
      nlinarith [mul_pos hδ hrᵢ]
    have hswap : hausdorffEDist
        ((AffineSubspace.mk' i Q : Set H) ∩ ball i (rᵢ / δ))
        (T ∩ ball i (rᵢ / δ)) < ENNReal.ofReal (2 * δ * rᵢ) := by
      rw [hausdorffEDist_comm]
      exact hcloudᵢ.trans_lt hstrict
    obtain ⟨z, hz, hyz⟩ := exists_edist_lt_of_hausdorffEDist_lt hy hswap
    have hclose : dist y z < 2 * δ * rᵢ := edist_lt_ofReal.mp hyz
    have hsmall : 2 * δ * rᵢ < r₀ / 2 := by
      have h := mul_le_mul_of_nonneg_left hupper (by positivity : 0 ≤ 2 * δ)
      have h' := mul_lt_mul_of_pos_right hAδ hr₀
      nlinarith
    have hzdist : dist z o < (L + 2) * r₀ := by
      have ht := dist_triangle z y o
      have ht' := dist_triangle y i o
      have hi0 : dist i o ≤ L * r₀ := by simpa only [dist_eq_norm] using hcenter
      rw [dist_comm z y] at ht
      rw [hydist] at ht'
      linarith
    have hnz := hnormal z hz.1 (hzdist.trans htestlarge)
    have hNy : ‖N (y - o)‖ ≤ δ * r₀ + 2 * δ * rᵢ := by
      have heq : N (y - o) = N (z - o) + N (y - z) := by
        rw [← map_add]
        congr 1
        abel
      rw [heq]
      apply (norm_add_le _ _).trans
      apply add_le_add hnz
      have hn := Pᗮ.norm_starProjection_apply_le (y - z)
      exact hn.trans (by simpa only [dist_eq_norm] using hclose.le)
    have hscale : r₀ • N u = N (y - o) - N (i - o) := by
      rw [← map_sub]
      have heq : y - o - (i - o) = r₀ • u := by dsimp [y]; abel
      rw [heq, map_smul]
    have hnormscale : r₀ * ‖N u‖ ≤ ‖N (y - o)‖ + ‖N (i - o)‖ := by
      calc
        r₀ * ‖N u‖ = ‖r₀ • N u‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr₀]
        _ = ‖N (y - o) - N (i - o)‖ := congrArg norm hscale
        _ ≤ _ := norm_sub_le _ _
    have hlarge := mul_le_mul_of_nonneg_left hupper (by positivity : 0 ≤ 2 * δ)
    apply (mul_le_mul_iff_right₀ hr₀).mp
    nlinarith
  let R : Q →L[ℝ] H := N.comp Q.subtypeL
  have hR : ‖R‖ ≤ (2 * A + 2) * δ := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro u hu
    exact hunit u u.property hu
  have hbound (u : H) (hu : u ∈ Q) :
      ‖u - P.starProjection u‖ ≤ ((2 * A + 2) * δ) * ‖u‖ := by
    have h := R.le_opNorm (⟨u, hu⟩ : Q)
    have h' := h.trans (mul_le_mul_of_nonneg_right hR (norm_nonneg (⟨u, hu⟩ : Q)))
    change ‖N u‖ ≤ ((2 * A + 2) * δ) * ‖u‖ at h'
    simpa only [N, Submodule.starProjection_orthogonal_val] using h'
  have hb : 0 ≤ (2 * A + 2) * δ := by positivity
  have hbhalf : (2 * A + 2) * δ ≤ 1 / 2 := by nlinarith
  have h := Q.norm_starProjection_sub_le_three_mul_of_one_sided_bound P hdim.symm hb hbhalf hbound
  rw [norm_sub_rev] at h
  have htangent : ‖P.starProjection - Q.starProjection‖ ≤ 6 * (A + 1) * δ := by
    convert h using 1
    ring
  refine ⟨hnormalᵢ,?_⟩
  have heq : Pᗮ.starProjection - Qᗮ.starProjection = Q.starProjection - P.starProjection := by
    rw [Submodule.starProjection_orthogonal,Submodule.starProjection_orthogonal]
    abel
  rw [heq,norm_sub_rev]
  exact htangent

end
end GC.MetricGeometry

namespace GC.MetricGeometry
section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem norm_starProjection_sub_le_of_local_affine_hausdorffEDist
    (P Q : Submodule ℝ H) [FiniteDimensional ℝ P] [FiniteDimensional ℝ Q]
    (hdim : Module.finrank ℝ P = Module.finrank ℝ Q)
    (T : Set H) (o i : H) (hi : i ∈ T)
    {r₀ rᵢ A δ : ℝ} (hr₀ : 0 < r₀) (hA : 1 ≤ A)
    (hlower : r₀ / A ≤ rᵢ) (hupper : rᵢ ≤ A * r₀)
    (hcenter : ‖i - o‖ ≤ r₀ / 2) (hδ : 0 < δ)
    (hδsmall : δ < 1 / (4 * (A + 1)))
    (hcloud₀ : hausdorffEDist (T ∩ ball o (r₀ / δ))
      ((AffineSubspace.mk' o P : Set H) ∩ ball o (r₀ / δ)) ≤ ENNReal.ofReal (δ * r₀))
    (hcloudᵢ : hausdorffEDist (T ∩ ball i (rᵢ / δ))
      ((AffineSubspace.mk' i Q : Set H) ∩ ball i (rᵢ / δ)) ≤ ENNReal.ofReal (δ * rᵢ)) :
    ‖P.starProjection - Q.starProjection‖ ≤ 6 * (A + 1) * δ := by
  have hbudget : δ * (4 * (A + 1)) < 1 :=
    (lt_div_iff₀ (by positivity)).mp hδsmall
  have hδA := mul_le_mul_of_nonneg_left hA hδ.le
  have hinterior : δ * ((1 / 2 : ℝ) + 2) < 1 := by
    nlinarith
  have hc : ‖i - o‖ ≤ (1 / 2 : ℝ) * r₀ := by
    nlinarith
  have hp := (normal_offset_and_projection_gap_le_of_large_affine_hausdorffEDist
    P Q hdim T o i hi hr₀ hA hlower hupper hc hδ hδsmall hinterior hcloud₀ hcloudᵢ).2
  have heq : Pᗮ.starProjection - Qᗮ.starProjection = Q.starProjection - P.starProjection := by
    rw [Submodule.starProjection_orthogonal, Submodule.starProjection_orthogonal]
    abel
  rwa [heq, norm_sub_rev] at hp

end
end GC.MetricGeometry
