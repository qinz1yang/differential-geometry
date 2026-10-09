import DifferentialGeometry.Geometry.Comparison.FourPointClosure
import DifferentialGeometry.Geometry.Metric.TangentConeDensity
import DifferentialGeometry.Geometry.Comparison.LocalGeodesicDirections
import DifferentialGeometry.Geometry.Comparison.GermDistanceAsymptotic

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

private theorem eventually_representative_path_mem {X : Type*} [MetricSpace X] {q : X}
    {Ω : Set X} (hΩ : IsOpen Ω) (hq : q ∈ Ω)
    (σ : GeodesicRepresentative q) (r : ℝ≥0) :
    ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), σ.path ((r : ℝ) * t) ∈ Ω := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΩ q hq
  have hid : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hr : Tendsto (fun t : ℝ => (r : ℝ) * t) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using hid.const_mul (r : ℝ)
  filter_upwards [self_mem_nhdsWithin, hr.eventually (gt_mem_nhds σ.length_pos),
    hr.eventually (gt_mem_nhds hε)] with t ht hlen hsmall
  apply hball
  change dist (σ.path ((r : ℝ) * t)) q < ε
  rw [dist_comm]
  exact (σ.dist_base_path (t := (r : ℝ) * t)
    ⟨mul_nonneg r.property ht.le, hlen.le⟩).trans_lt hsmall

private theorem comparison_zero_representative_vectors {X : Type*} [MetricSpace X]
    {q : X} [HasAnglesAt q] {κ : ℝ} (hκ : 0 ≤ κ) {Ω : Set X}
    (hΩ : IsOpen Ω) (hcomp : fourPointComparison κ Ω) (hq : q ∈ Ω) :
    fourPointComparison 0 (Set.range
      (fun z : ℝ≥0 × GeodesicRepresentative q => z.2.tangentVector z.1)) := by
  rintro _ ⟨⟨r, σ⟩, rfl⟩ _ ⟨⟨s, τ⟩, rfl⟩ _ ⟨⟨u, υ⟩, rfl⟩ _ ⟨⟨v, ω⟩, rfl⟩
    hax hbx hcx
  have hxa := dist_pos.mpr hax.symm
  have hxb := dist_pos.mpr hbx.symm
  have hxc := dist_pos.mpr hcx.symm
  have hdist (α β : GeodesicRepresentative q) (a b : ℝ≥0) :=
    α.dist_div_tendsto_tangentVector β a b
  have hscale (t : ℝ) (ht : 0 < t) (a b c : ℝ) :
      comparisonAngleNegCurvature κ a b c =
        comparisonAngleNegCurvature (κ * t ^ 2) (a / t) (b / t) (c / t) := by
    simpa only [div_mul_cancel₀ _ ht.ne'] using
      comparisonAngleNegCurvature_mul_scale hκ ht (a / t) (b / t) c
  have hsource : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      comparisonAngleNegCurvature (κ * t ^ 2)
          (dist (σ.path (r * t)) (τ.path (s * t)) / t)
          (dist (σ.path (r * t)) (υ.path (u * t)) / t)
          (dist (τ.path (s * t)) (υ.path (u * t)) / t) +
        comparisonAngleNegCurvature (κ * t ^ 2)
          (dist (σ.path (r * t)) (υ.path (u * t)) / t)
          (dist (σ.path (r * t)) (ω.path (v * t)) / t)
          (dist (υ.path (u * t)) (ω.path (v * t)) / t) +
        comparisonAngleNegCurvature (κ * t ^ 2)
          (dist (σ.path (r * t)) (ω.path (v * t)) / t)
          (dist (σ.path (r * t)) (τ.path (s * t)) / t)
          (dist (ω.path (v * t)) (τ.path (s * t)) / t) ≤ 2 * Real.pi := by
    filter_upwards [self_mem_nhdsWithin,
      eventually_representative_path_mem hΩ hq σ r,
      eventually_representative_path_mem hΩ hq τ s,
      eventually_representative_path_mem hΩ hq υ u,
      eventually_representative_path_mem hΩ hq ω v,
      (hdist σ τ r s).eventually (Ioi_mem_nhds hxa),
      (hdist σ υ r u).eventually (Ioi_mem_nhds hxb),
      (hdist σ ω r v).eventually (Ioi_mem_nhds hxc)] with t ht hx ha hb hc h1 h2 h3
    have hh := hcomp _ hx _ ha _ hb _ hc
      (dist_pos.mp ((div_pos_iff_of_pos_right ht).mp h1)).symm
      (dist_pos.mp ((div_pos_iff_of_pos_right ht).mp h2)).symm
      (dist_pos.mp ((div_pos_iff_of_pos_right ht).mp h3)).symm
    simpa only [hscale t ht] using hh
  have hid : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hk : Tendsto (fun t : ℝ => κ * t ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using (hid.pow 2).const_mul κ
  have hnonneg : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 ≤ κ * t ^ 2 :=
    Eventually.of_forall fun t => mul_nonneg hκ (sq_nonneg t)
  have hang12 := tendsto_comparisonAngleNegCurvature_zero hk
    (hdist σ τ r s) (hdist σ υ r u) (hdist τ υ s u) hnonneg hxa hxb
  have hang23 := tendsto_comparisonAngleNegCurvature_zero hk
    (hdist σ υ r u) (hdist σ ω r v) (hdist υ ω u v) hnonneg hxb hxc
  have hang31 := tendsto_comparisonAngleNegCurvature_zero hk
    (hdist σ ω r v) (hdist σ τ r s) (hdist ω τ v s) hnonneg hxc hxa
  simpa only [comparisonAngleNegCurvature_zero] using
    le_of_tendsto ((hang12.add hang23).add hang31) hsource

theorem tangentCone_fourPointComparison_zero_of_local_fourPointComparison
    {X : Type*} [MetricSpace X] {q : X} {κ : ℝ} (hκ : 0 ≤ κ) {Ω : Set X}
    (hΩ : IsOpen Ω) (hcomp : fourPointComparison κ Ω) (hq : q ∈ Ω) :
    letI : HasAnglesAt q := hasAnglesAt_of_local_fourPointComparison hκ hΩ hcomp hq
    fourPointComparison 0 (univ : Set (TangentCone q)) := by
  let : HasAnglesAt q := hasAnglesAt_of_local_fourPointComparison hκ hΩ hcomp hq
  classical
  by_cases hn : Nonempty (GeodesicRepresentative q)
  · obtain ⟨σ⟩ := hn
    have htip : (EuclideanCone.tip : TangentCone q) ∈ Set.range
        (fun z : ℝ≥0 × GeodesicRepresentative q => z.2.tangentVector z.1) := by
      exact ⟨(0, σ), by simp [GeodesicRepresentative.tangentVector]⟩
    have hd := TangentCone.dense_representative_vectors (q := q)
    rw [union_eq_right.mpr (singleton_subset_iff.mpr htip)] at hd
    have h := (comparison_zero_representative_vectors hκ hΩ hcomp hq).closure_zero
    rwa [hd.closure_eq] at h
  · let : IsEmpty (GeodesicRepresentative q) := not_nonempty_iff.mp hn
    have hs : Subsingleton (TangentCone q) :=
      inferInstanceAs (Subsingleton (Option ({r : ℝ // 0 < r} × SpaceOfDirections q)))
    intro x _ a _ _ _ _ _ hax
    exact (hax (hs.elim a x)).elim

end DifferentialGeometry.Geometry.Comparison.Toponogov
