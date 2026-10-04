import DifferentialGeometry.Analysis.InnerProductSpace.NormalSpectralSection
import Mathlib.Analysis.Normed.Module.Convex

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped BigOperators
namespace GC.MetricGeometry

theorem spectral_zero_coordinate_of_nearest_value_bound
    {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    (V : Submodule ℝ H) (S : Finset I) (L : I → Submodule ℝ H)
    (center : I → H) (w : I → H → ℝ) (x : H) (Lx : Submodule ℝ H)
    {b r ε : ℝ} (hb : 1 ≤ b) (hr : 0 < r) (hε : ε ≤ 1 / 10)
    (hw : ∀ z ∈ ball x (8 * b * r), ∑ i ∈ S, w i z = 1)
    (hL : ∀ z ∈ ball x (8 * b * r), ∀ i ∈ S, w i z ≠ 0 → L i ≤ Vᗮ)
    (hcenter : ∀ z ∈ ball x (8 * b * r), ∀ i ∈ S, w i z ≠ 0 → center i ∈ Vᗮ) :
    let Q : H → H →L[ℝ] H := fun y =>
      (⨆ a ∈ ball (1 : ℝ) (1 / 2), Module.End.eigenspace
        (∑ i ∈ S, w i y • (L i)ᗮ.starProjection).toLinearMap a).starProjection
    let Z : Set H := {y | Q y (y - ∑ i ∈ S, w i y • center i) = 0}
    ∀ p : ball x r → Z,
      (∀ z, ‖(p z : H) - (x + Lx.starProjection ((z : H) - x))‖ ≤ ε * r) →
      ∀ z : ball x r, V.starProjection (p z : H) = 0 ∧
        (V.starProjection (z : H) = 0 → ∀ ψ : ℝ,
          V.starProjection ((z : H) + ψ • ((p z : H) - z)) = 0) := by
  dsimp only
  intro p hvalue z
  have hloc : ‖(p z : H) - x‖ < 3 * b * r := by
    have htri := norm_sub_le ((p z : H) - (x + Lx.starProjection ((z : H) - x)))
      (x - (x + Lx.starProjection ((z : H) - x)))
    rw [sub_sub_sub_cancel_right] at htri
    have heq : x - (x + Lx.starProjection ((z : H) - x)) =
        - Lx.starProjection ((z : H) - x) := by abel
    rw [heq, norm_neg] at htri
    have hz : ‖(z : H) - x‖ < r := by simpa only [mem_ball, dist_eq_norm] using z.property
    have hc := Lx.norm_starProjection_apply_le ((z : H) - x)
    have hbr := mul_le_mul_of_nonneg_right hb hr.le
    nlinarith [hvalue z]
  have hyball : (p z : H) ∈ ball x (8 * b * r) := by
    rw [mem_ball, dist_eq_norm]
    exact hloc.trans (by nlinarith [mul_pos (zero_lt_one.trans_le hb) hr])
  let Q := ((⨆ a ∈ ball (1 : ℝ) (1 / 2), Module.End.eigenspace
    (∑ i ∈ S, w i (p z) • (L i)ᗮ.starProjection).toLinearMap a).starProjection)
  have hsection := Submodule.starProjection_weighted_normal_section V S L center
    (fun i => w i (p z)) (hw (p z) hyball) (hL (p z) hyball)
    (hcenter (p z) hyball) (ball (1 : ℝ) (1 / 2)) (by simp) (p z : H)
  have heq : (∑ i ∈ S, w i (p z) • Q ((p z : H) - center i)) =
      Q ((p z : H) - ∑ i ∈ S, w i (p z) • center i) := by
    simp only [map_sub, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul,
      hw (p z) hyball, one_smul, map_sum, map_smul]
  change V.starProjection (∑ i ∈ S, w i (p z) • Q ((p z : H) - center i)) = _ at hsection
  have hzero : Q ((p z : H) - ∑ i ∈ S, w i (p z) • center i) = 0 := (p z).property
  rw [heq, hzero, map_zero] at hsection
  have hv : V.starProjection (p z : H) = 0 := hsection.symm
  refine ⟨hv, ?_⟩
  intro hz ψ
  simp only [map_add, map_smul, map_sub, hv, hz, sub_zero, smul_zero, add_zero]

end GC.MetricGeometry
