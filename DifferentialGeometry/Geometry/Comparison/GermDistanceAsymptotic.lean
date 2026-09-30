import DifferentialGeometry.Geometry.Comparison.ModelSide
import Mathlib.Topology.Bases

set_option autoImplicit false

open Set Filter Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem comparisonAngleNegCurvature_mul_scale {κ t : ℝ} (hκ : 0 ≤ κ)
    (ht : 0 < t) (a b c : ℝ) :
    comparisonAngleNegCurvature κ (a * t) (b * t) c =
      comparisonAngleNegCurvature (κ * t ^ 2) a b (c / t) := by
  by_cases hk : κ = 0
  · subst κ
    simp only [zero_mul, comparisonAngleNegCurvature_zero]
    have hcancel : t * (c / t) = c := by field_simp
    simpa only [mul_comm t a, mul_comm t b, hcancel] using
      comparisonAngle_scale a b (c / t) ht
  · have hkt : κ * t ^ 2 ≠ 0 := mul_ne_zero hk (pow_ne_zero _ ht.ne')
    have hs : Real.sqrt (κ * t ^ 2) = Real.sqrt κ * t := by
      rw [Real.sqrt_mul hκ, Real.sqrt_sq ht.le]
    have hcancel : Real.sqrt κ * t * (c / t) = Real.sqrt κ * c := by
      field_simp
    simp only [comparisonAngleNegCurvature, ite_eq_right hk, ite_eq_right hkt, hs,
      hcancel]
    simp only [mul_assoc, mul_left_comm, mul_comm]

theorem dist_div_tendsto_of_joint_comparisonAngle
    {X : Type*} [MetricSpace X] {κ R S α : ℝ}
    (hκ : 0 ≤ κ) (hR : 0 < R) (hS : 0 < S)
    (p : X) (γ β : ℝ → X)
    (hγrad : ∀ s ∈ Ioc 0 R, dist p (γ s) = s)
    (hβrad : ∀ s ∈ Ioc 0 S, dist p (β s) = s)
    (hangle : Tendsto (fun z : ℝ × ℝ =>
      comparisonAngleNegCurvature κ z.1 z.2 (dist (γ z.1) (β z.2)))
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 α))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun t : ℝ => dist (γ (a * t)) (β (b * t)) / t)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Real.sqrt (a ^ 2 + b ^ 2 - 2 * a * b * Real.cos α))) := by
  have htpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have htzero : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hatzero : Tendsto (fun t : ℝ => a * t) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using tendsto_const_nhds.mul htzero
  have hbtzero : Tendsto (fun t : ℝ => b * t) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using tendsto_const_nhds.mul htzero
  have hat : Tendsto (fun t : ℝ => a * t) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hatzero, htpos.mono (fun _ ht => mul_pos ha ht)⟩
  have hbt : Tendsto (fun t : ℝ => b * t) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hbtzero, htpos.mono (fun _ ht => mul_pos hb ht)⟩
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), a * t ∈ Ioc 0 R ∧ b * t ∈ Ioc 0 S := by
    filter_upwards [htpos, hatzero.eventually (gt_mem_nhds hR),
      hbtzero.eventually (gt_mem_nhds hS)] with t ht haR hbS
    exact ⟨⟨mul_pos ha ht, haR.le⟩, ⟨mul_pos hb ht, hbS.le⟩⟩
  let d : ℝ → ℝ := fun t => dist (γ (a * t)) (β (b * t)) / t
  have hbound : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), d t ∈ Icc |a - b| (a + b) := by
    filter_upwards [htpos, hsmall] with t ht hsmallt
    have hg := hγrad _ hsmallt.1
    have hb' := hβrad _ hsmallt.2
    have hlo := abs_dist_sub_le (γ (a * t)) (β (b * t)) p
    rw [dist_comm _ p, dist_comm _ p, hg, hb', ← sub_mul, abs_mul,
      abs_of_pos ht] at hlo
    have hup := dist_triangle (γ (a * t)) p (β (b * t))
    rw [dist_comm _ p, hg, hb', ← add_mul] at hup
    exact ⟨(le_div_iff₀ ht).mpr hlo, (div_le_iff₀ ht).mpr hup⟩
  apply isCompact_Icc.tendsto_nhds_of_unique_mapClusterPt hbound
  intro c hc hcluster
  obtain ⟨τ, hdτ, hτ⟩ := hcluster.exists_seq_tendsto
  have hτzero := htzero.comp hτ
  have hkτ : Tendsto (fun i => κ * (τ i) ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa using tendsto_const_nhds.mul (hτzero.pow 2)
  have hmodel := tendsto_comparisonAngleNegCurvature_zero hkτ tendsto_const_nhds
    tendsto_const_nhds hdτ (Filter.Eventually.of_forall (fun i => mul_nonneg hκ (sq_nonneg _))) ha hb
  have hactual := (hangle.comp (hat.prodMk hbt)).comp hτ
  have hscaled : Tendsto (fun i => comparisonAngleNegCurvature (κ * (τ i) ^ 2) a b
      (dist (γ (a * τ i)) (β (b * τ i)) / τ i)) atTop (𝓝 α) := by
    apply hactual.congr'
    filter_upwards [hτ.eventually htpos] with i hi
    exact comparisonAngleNegCurvature_mul_scale hκ hi a b _
  have heq : comparisonAngle a b c = α := tendsto_nhds_unique hmodel hscaled
  have hinv := modelSideNegCurvature_comparisonAngle (κ := 0) (by rfl : (0 : ℝ) ≤ 0)
    ha hb hc.1 hc.2
  simpa only [comparisonAngleNegCurvature_zero, heq, modelSideNegCurvature, ite_true] using hinv.symm

end DifferentialGeometry.Geometry.Comparison.Toponogov
