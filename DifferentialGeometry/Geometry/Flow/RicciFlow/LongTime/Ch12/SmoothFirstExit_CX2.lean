import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.CurvatureMetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.CurvatureBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData
import DifferentialGeometry.Geometry.Comparison.DistanceHessianLocal

set_option autoImplicit false

noncomputable section

open Set Manifold MeasureTheory DifferentialGeometry
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
  DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- A compact family cannot first reach the outer threshold if control after
that time improves it to a strictly smaller threshold. -/
theorem compact_backward_first_exit_CX2 {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {a b : ℝ} {f : ℝ × X → ℝ≥0∞} {L R : ℝ≥0∞}
    (hcont : ContinuousOn f (Icc a b ×ˢ (univ : Set X))) (hLR : L < R)
    (hfinal : ∀ x, f (b, x) < R)
    (hboost : ∀ v ∈ Icc a b,
      (∀ w ∈ Icc v b, ∀ x, f (w, x) < R) → ∀ x, f (v, x) ≤ L) :
    ∀ v ∈ Icc a b, ∀ x, f (v, x) < R := by
  by_contra hfail
  push Not at hfail
  obtain ⟨v, hv, x, hx⟩ := hfail
  let A := {q : ℝ × X | q ∈ Icc a b ×ˢ (univ : Set X) ∧ R ≤ f q}
  have hAc : IsCompact A :=
    (isCompact_Icc.prod isCompact_univ).of_isClosed_subset
      ((isClosed_Icc.prod isClosed_univ).isClosed_le continuousOn_const hcont)
      (fun q hq => hq.1)
  obtain ⟨q, hq, hmax⟩ := hAc.exists_isMaxOn ⟨(v, x), ⟨hv, mem_univ _⟩, hx⟩
    continuous_fst.continuousOn
  have hqb : q.1 < b := lt_of_le_of_ne hq.1.1.2 (by
    intro heq
    exact (not_le_of_gt (hfinal q.2)) (heq ▸ hq.2))
  have hafter : ∀ w ∈ Ioc q.1 b, ∀ z, f (w, z) < R := by
    intro w hw z
    by_contra hbad
    have hmem : (w, z) ∈ A := ⟨⟨⟨hq.1.1.1.trans hw.1.le, hw.2⟩, mem_univ _⟩,
      le_of_not_gt hbad⟩
    exact (not_le_of_gt hw.1) (hmax hmem)
  have hle : ∀ w ∈ Ioc q.1 b, f (w, q.2) ≤ L := by
    intro w hw
    exact hboost w ⟨hq.1.1.1.trans hw.1.le, hw.2⟩
      (fun z hz => hafter z ⟨hw.1.trans_le hz.1, hz.2⟩) q.2
  have hc : ContinuousOn (fun w => f (w, q.2)) (closure (Ioc q.1 b)) := by
    rw [closure_Ioc hqb.ne]
    exact hcont.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun w hw => ⟨⟨hq.1.1.1.trans hw.1, hw.2⟩, mem_univ _⟩)
  have hqL : f q ≤ L := le_on_closure hle hc continuousOn_const (by
    rw [closure_Ioc hqb.ne]
    exact ⟨le_rfl, hqb.le⟩)
  exact (not_le_of_gt hLR) (hq.2.trans hqL)

/-- A quadratic comparison along a path compares its length without a
nonvanishing-velocity hypothesis. -/
theorem path_length_le_of_quad_CX2 (P : OrientedThreeStage.{u}) (g h : P.Metric)
    (γ : ℝ → P.Carrier) {L : ℝ} (hL : 0 ≤ L)
    (hquad : ∀ s ∈ Ioo (0 : ℝ) 1, ∀ v : TangentSpace ThreeModel (γ s),
      g.inner (γ s) v v ≤ L ^ 2 * h.inner (γ s) v v) :
    metricPathELength g γ 0 1 ≤ ENNReal.ofReal L * metricPathELength h γ 0 1 := by
  rw [metricPathELength_eq, metricPathELength_eq,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' measurableSet_Ioo
  intro s hs
  have hroot := Real.sqrt_le_sqrt
    (hquad s hs (mfderiv 𝓘(ℝ, ℝ) ThreeModel γ s 1))
  rw [Real.sqrt_mul (sq_nonneg L), Real.sqrt_sq hL] at hroot
  simpa only [ENNReal.ofReal_mul hL] using ENNReal.ofReal_le_ofReal hroot

/-- On a smooth compact stage, G3a's bound only inside the moving buffer
already prevents first exit of the whole path. -/
theorem smooth_path_first_exit_CX2 (P : OrientedThreeStage.{u}) {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := P.Carrier) D) (hS : IsSolutionOn S)
    {a b K ℓ R : ℝ} (hab : a ≤ b) (hK : 0 ≤ K) (hℓ : 0 ≤ ℓ)
    (hcarrier : Icc a b ⊆ D.carrier) (hregular : Ioo a b ⊆ D.regular)
    (γ : ℝ → P.Carrier) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 γ (Icc (0 : ℝ) 1))
    (hlen : metricPathELength (S.base.metric b) γ 0 1 ≤ ENNReal.ofReal ℓ)
    (hroom : Real.exp (9 * K * (b - a)) * ℓ < R)
    (hRm : ∀ t ∈ Icc a b, ∀ x ∈ riemannianBallOf (S.base.metric t) (γ 0) R,
      Real.sqrt (normSq0S (S.base.metric t) x 4 (S.base.rm04 t x)) ≤ K) :
    ∀ t ∈ Icc a b, ∀ s ∈ Icc (0 : ℝ) 1,
      γ s ∈ riemannianBallOf (S.base.metric t) (γ 0) R := by
  let B := Real.exp (9 * K * (b - a))
  have hB : 0 < B := Real.exp_pos _
  have hB1 : 1 ≤ B := Real.one_le_exp (mul_nonneg (by positivity) (sub_nonneg.mpr hab))
  have hℓR : ℓ < R := (le_mul_of_one_le_left hℓ hB1).trans_lt hroom
  have hR : 0 < R := hℓ.trans_lt hℓR
  obtain ⟨C, _, hC⟩ := exists_curvature_bound_on_carrier_interval_of_isSolutionOn S hS hcarrier
  have hric : ∀ t ∈ Icc a b, ∀ x : P.Carrier, ∀ v : TangentSpace ThreeModel x,
      |ricciTensor (S.base.metric t) x v v| ≤
        ((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt C) * (S.base.metric t).inner x v v := by
    intro t ht x v
    exact ricci_quadratic_form_bound_of_solution_curvature_bound S x v (hC t ht x)
  have hdist := edistCont_Icc S hS hcarrier hregular hric (γ 0)
  let J := Icc (0 : ℝ) 1
  let : CompactSpace J := isCompact_iff_compactSpace.mp isCompact_Icc
  let f : ℝ × J → ℝ≥0∞ := fun q => riemannianEDistOf (S.base.metric q.1) (γ 0) (γ q.2)
  have hfc : ContinuousOn f (Icc a b ×ˢ (univ : Set J)) := by
    have hγc : Continuous (fun s : J => γ s) := hγ.continuousOn.domRestrict
    exact hdist.comp (continuous_fst.prodMk (hγc.comp continuous_snd)).continuousOn
      (fun q hq => ⟨hq.1, mem_univ _⟩)
  have hfinal : ∀ s : J, f (b, s) < ENNReal.ofReal R := by
    intro s
    have hp := edistOf_le_metricPathELength (S.base.metric b) s.property.1
      (hγ.mono (Icc_subset_Icc le_rfl s.property.2))
    exact (hp.trans ((metricPathELength_mono _ γ le_rfl s.property.2).trans hlen)).trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff hR).mpr hℓR)
  suffices h : ∀ t ∈ Icc a b, ∀ s : J, f (t, s) < ENNReal.ofReal R by
    intro t ht s hs
    exact h t ht ⟨s, hs⟩
  apply compact_backward_first_exit_CX2 hfc
    ((ENNReal.ofReal_lt_ofReal_iff hR).mpr hroom) hfinal
  intro v hv hstay s
  have hquad : ∀ z ∈ Ioo (0 : ℝ) 1, ∀ V : TangentSpace ThreeModel (γ z),
      (S.base.metric v).inner (γ z) V V ≤ B ^ 2 * (S.base.metric b).inner (γ z) V V := by
    intro z hz V
    have hzJ : z ∈ J := ⟨hz.1.le, hz.2.le⟩
    have hcurv : ∀ w ∈ Icc v b,
        normSq0S (S.base.metric w) (γ z) 4 (S.base.rm04 w (γ z)) ≤ K ^ 2 := by
      intro w hw
      exact (Real.sqrt_le_iff.mp (hRm w ⟨hv.1.trans hw.1, hw.2⟩ (γ z)
        (hstay w hw ⟨z, hzJ⟩))).2
    have hm := (metric_inner_exp_bounds_of_curvature_bound S hS
      (fun w hw => hcarrier ⟨hv.1.trans hw.1, hw.2⟩)
      (fun w hw => hregular ⟨hv.1.trans_lt hw.1, hw.2⟩)
      (γ z) hcurv ⟨le_rfl, hv.2⟩ ⟨hv.2, le_rfl⟩ V).2
    have hexp : Real.exp (2 * (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt (K ^ 2) * |v - b|) ≤ B ^ 2 := by
      rw [Real.sqrt_sq hK, abs_of_nonpos (sub_nonpos.mpr hv.2)]
      change Real.exp (2 * (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * K * -(v - b)) ≤
        Real.exp (9 * K * (b - a)) ^ 2
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      norm_num [ThreeSpace]
      nlinarith [mul_nonneg hK (sub_nonneg.mpr hv.1)]
    exact hm.trans (mul_le_mul_of_nonneg_right hexp (metric_inner_self_nonneg _ _ _))
  have hlength := path_length_le_of_quad_CX2 P (S.base.metric v) (S.base.metric b) γ hB.le hquad
  have hp := edistOf_le_metricPathELength (S.base.metric v) s.property.1
    (hγ.mono (Icc_subset_Icc le_rfl s.property.2))
  have hb := hp.trans ((metricPathELength_mono _ γ le_rfl s.property.2).trans
    (hlength.trans (mul_le_mul' le_rfl hlen)))
  simpa only [← ENNReal.ofReal_mul hB.le] using hb

end GC.LongTime.Ch12
