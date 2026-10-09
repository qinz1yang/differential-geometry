import DifferentialGeometry.Geometry.Metric.AffinePlaneCoherence
import DifferentialGeometry.Topology.MetricSpace.CoarseScaleComparison
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
noncomputable section
open Set Metric

namespace GC.MetricGeometry
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem normal_projection_coherence_of_cloud_support_meeting
    (S T : Set H) (hST : S ⊆ T) (r : H → ℝ)
    (P : S → Submodule ℝ H) [∀ x : S, FiniteDimensional ℝ (P x)]
    (C : ℝ) (hC : 0 ≤ C) (δ : ℝ) (hδ : 0 < δ)
    (hr : ∀ x ∈ S, 0 < r x)
    (hscale : ∀ x ∈ S, ∀ y ∈ S, |r y - r x| ≤ C * (dist x y + r x))
    (hcloud : ∀ x : S,
      hausdorffEDist (T ∩ ball (x : H) (r x / δ))
        ((AffineSubspace.mk' (x : H) (P x) : Set H) ∩ ball (x : H) (r x / δ)) ≤
          ENNReal.ofReal (δ * r x)) :
    let ℓ : ℝ := 1 / (100 * (C + 1))
    let A : ℝ := 2 * (C + 1)
    δ ≤ ℓ / (2 * A) →
    ∀ x₀ xᵢ : S, Module.finrank ℝ (P x₀) = Module.finrank ℝ (P xᵢ) →
    ∀ v ∈ ball (x₀ : H) (5 * ℓ * r x₀),
      (closedBall (xᵢ : H) (20 * ℓ * r xᵢ) ∩ ball v (ℓ * r x₀)).Nonempty →
      ‖(P x₀)ᗮ.starProjection ((xᵢ : H) - (x₀ : H))‖ ≤ δ * r x₀ ∧
      ‖(P xᵢ)ᗮ.starProjection - (P x₀)ᗮ.starProjection‖ ≤ 6 * (A + 1) * δ := by
  dsimp only
  let ℓ : ℝ := 1 / (100 * (C + 1))
  let A : ℝ := 2 * (C + 1)
  let D : ℝ := 20 * A + 6
  intro hδsmall x₀ xᵢ hdim v hv hmeet
  have hr₀ := hr x₀ x₀.property
  have hrᵢ := hr xᵢ xᵢ.property
  have hden : 0 < 100 * (C + 1) := by positivity
  have hℓ : 0 < ℓ := one_div_pos.mpr hden
  have hA : 2 ≤ A := by dsimp [A]; linarith
  have hApos : 0 < A := by linarith
  have hbudget : C * ℓ ≤ 1 / 100 := by
    dsimp [ℓ]
    rw [← mul_div_assoc, mul_one]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hℓsmall : ℓ ≤ 1 / 100 := by
    dsimp [ℓ]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hδbudget : δ * (2 * A) ≤ ℓ :=
    (le_div_iff₀ (by positivity : 0 < 2 * A)).mp hδsmall
  have hδstrict : δ < 1 / (4 * (A + 1)) := by
    apply (lt_div_iff₀ (by positivity : 0 < 4 * (A + 1))).mpr
    have hfactor : 4 * (A + 1) ≤ 3 * (2 * A) := by linarith
    have h := mul_le_mul_of_nonneg_left hfactor hδ.le
    nlinarith
  have hδone : δ < 1 := by
    have hmul := mul_le_mul_of_nonneg_left hA hδ.le
    nlinarith
  have hDℓ : D * ℓ < 1 / 2 := by
    dsimp [D, A, ℓ]
    rw [← mul_div_assoc, mul_one]
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  have hlocal : r x₀ / A ≤ r xᵢ ∧ r xᵢ ≤ A * r x₀ ∧
      dist (xᵢ : H) (x₀ : H) ≤ D * ℓ * r x₀ := by
    apply Metric.coarse_scale_comparison_of_support_meeting hr₀ hrᵢ hC hℓ.le hbudget
    · have h := (abs_le.mp (hscale x₀ x₀.property xᵢ xᵢ.property)).2
      simpa only [dist_comm (x₀ : H) (xᵢ : H)] using h
    · exact (abs_le.mp (hscale xᵢ xᵢ.property x₀ x₀.property)).2
    · exact hv
    · exact hmeet
  have hcenter : ‖(xᵢ : H) - (x₀ : H)‖ ≤ r x₀ / 2 := by
    have h := mul_lt_mul_of_pos_right hDℓ hr₀
    rw [dist_eq_norm] at hlocal
    nlinarith [hlocal.2.2]
  have hnear : dist (xᵢ : H) (x₀ : H) < r x₀ / δ := by
    rw [dist_eq_norm]
    apply hcenter.trans_lt
    apply (lt_div_iff₀ hδ).mpr
    nlinarith
  have he : infEDist (xᵢ : H) (AffineSubspace.mk' (x₀ : H) (P x₀) : Set H) ≤
      ENNReal.ofReal (δ * r x₀) :=
    (infEDist_anti inter_subset_left).trans
      ((infEDist_le_hausdorffEDist_of_mem
        (show (xᵢ : H) ∈ T ∩ ball (x₀ : H) (r x₀ / δ) from
          ⟨hST xᵢ.property, hnear⟩)).trans (hcloud x₀))
  have hoffset : ‖(P x₀)ᗮ.starProjection ((xᵢ : H) - (x₀ : H))‖ ≤ δ * r x₀ := by
    have hreal : infDist (xᵢ : H) (AffineSubspace.mk' (x₀ : H) (P x₀) : Set H) ≤
        δ * r x₀ := by
      simpa only [Metric.infDist, ENNReal.toReal_ofReal (mul_pos hδ hr₀).le] using
        (ENNReal.toReal_mono ENNReal.ofReal_ne_top he)
    rw [← (P x₀).norm_sub_starProjection_eq_infDist_affine] at hreal
    simpa only [Submodule.starProjection_orthogonal_val] using hreal
  refine ⟨hoffset, ?_⟩
  have ht := norm_starProjection_sub_le_of_local_affine_hausdorffEDist
    (P x₀) (P xᵢ) hdim T (x₀ : H) (xᵢ : H) (hST xᵢ.property)
    hr₀ (by linarith : 1 ≤ A) hlocal.1 hlocal.2.1 hcenter hδ hδstrict
    (hcloud x₀) (hcloud xᵢ)
  have heq : (P xᵢ)ᗮ.starProjection - (P x₀)ᗮ.starProjection =
      (P x₀).starProjection - (P xᵢ).starProjection := by
    rw [Submodule.starProjection_orthogonal, Submodule.starProjection_orthogonal]
    abel
  rw [heq]
  exact ht

end GC.MetricGeometry
