import DifferentialGeometry.Geometry.Comparison.OpenEmbeddingBallCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.CurvatureMetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySlices
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

theorem exists_uniform_stage_window_protection (K : ℝ) :
    ∃ τ : ℝ, 0 < τ ∧
      ∀ (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon)
        (p : (H.stageAt t).Carrier) (r : ℝ), 0 < r →
        τ * r ^ 2 ≤ (t : ℝ) - H.time (H.activeStage t) →
        (∀ s ∈ Icc ((t : ℝ) - τ * r ^ 2) t.val,
          ∀ x ∈ riemannianClosedBallOf (H.stageMetric (H.activeStage t) t) p (3 * r),
            normSq0S (H.stageMetric (H.activeStage t) s) x 4
              (metricRm04At (H.stageMetric (H.activeStage t) s) x) ≤ K / r ^ 4) →
        ∀ s ∈ Icc ((t : ℝ) - τ * r ^ 2) t.val,
          s ∈ H.stageDomain (H.activeStage t) ∧
          riemannianClosedBallOf (H.stageMetric (H.activeStage t) s) p (2 * r) ⊆
            riemannianBallOf (H.stageMetric (H.activeStage t) t) p (3 * r) ∧
          IsCompact (riemannianClosedBallOf
            (H.stageMetric (H.activeStage t) s) p (2 * r)) := by
  have hcont : ContinuousAt (fun d : ℝ => Real.exp (9 * Real.sqrt K * d) * 2) 0 := by
    fun_prop
  have hnear : {d : ℝ | Real.exp (9 * Real.sqrt K * d) * 2 < 5 / 2} ∈ 𝓝 0 :=
    hcont.eventually (Iio_mem_nhds (by norm_num))
  obtain ⟨ε, hε, hεball⟩ := Metric.mem_nhds_iff.mp hnear
  let τ : ℝ := ε / 2
  have hτ : 0 < τ := half_pos hε
  have hτfit : Real.exp (9 * Real.sqrt K * τ) * 2 < 5 / 2 := by
    apply hεball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hτ]
    dsimp only [τ]
    linarith
  refine ⟨τ, hτ, ?_⟩
  intro H t p r hr hage hRm s hs
  let k := H.activeStage t
  let birth : ℝ := H.time k
  let a : ℝ := (t : ℝ) - τ * r ^ 2
  have hδ : 0 < τ * r ^ 2 := mul_pos hτ (sq_pos_of_pos hr)
  have htreg : H.time (H.activeStage t) < (t : ℝ) := by linarith
  have hab : a < (t : ℝ) := sub_lt_self _ hδ
  have hba : birth ≤ a := by dsimp only [birth, k, a]; linarith
  let S := (H.closedPrefixAt t htreg).flow
  have hS : IsSolutionOn S := (H.closedPrefixAt t htreg).equation
  have hmetric (v : ℝ) : S.base.metric v = H.stageMetric k v :=
    H.closedPrefixAt_metric t htreg v
  have hcarrier : Icc a t.val ⊆
      (RealTimeInterval.closed birth t.val htreg.le).carrier :=
    fun v hv => ⟨hba.trans hv.1, hv.2⟩
  have hregular : Ioo a t.val ⊆
      (RealTimeInterval.closed birth t.val htreg.le).regular :=
    fun v hv => ⟨hba.trans_lt hv.1, hv.2⟩
  have hsab : s ∈ Icc a t.val := hs
  have hbs : birth ≤ s := hba.trans hsab.1
  let v : Icc (0 : ℝ) H.horizon :=
    ⟨s, (H.time_nonneg k).trans hbs, hs.2.trans t.property.2⟩
  have hstage : H.activeStage v = k := le_antisymm
    (H.activeStage_mono (show v ≤ t from hs.2)) (H.le_activeStage v k hbs)
  have hdom : s ∈ H.stageDomain k := by
    have hh := H.activeStage_mem v
    simpa only [hstage] using hh
  let V : Opens (H.stageAt t).Carrier :=
    ⟨riemannianBallOf (S.base.metric t) p (3 * r),
      isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist _ p) continuous_const⟩
  let pV : V := ⟨p, by
    change riemannianEDistOf (S.base.metric t) p p < ENNReal.ofReal (3 * r)
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (by positivity)⟩
  let R : ℝ := 5 * r / 2
  have hR : 0 < R := by dsimp only [R]; positivity
  have hR3 : R < 3 * r := by dsimp only [R]; linarith
  have hsource : riemannianClosedBallOf (S.base.metric t) p R ⊆ V := by
    intro x hx
    exact hx.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hR3)
  have hclosed (u ρ : ℝ) : IsClosed (riemannianClosedBallOf (S.base.metric u) p ρ) :=
    isClosed_le (Geometry.Riemannian.continuous_riemannianEDist (S.base.metric u) p)
      continuous_const
  have hcpt : IsCompact (riemannianClosedBallOf (S.base.metric t) p R) :=
    (hclosed t R).isCompact
  have hsqrt : Real.sqrt (K / r ^ 4) = Real.sqrt K / r ^ 2 := by
    rw [Real.sqrt_div' K (pow_nonneg hr.le 4),
      show r ^ 4 = (r ^ 2) ^ 2 by ring, Real.sqrt_sq (sq_nonneg r)]
  have htime : |(t : ℝ) - s| ≤ τ * r ^ 2 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hs.2)]
    linarith [hs.1]
  let L : ℝ := Real.exp (9 * Real.sqrt (K / r ^ 4) * |(t : ℝ) - s|)
  have hL : 0 < L := Real.exp_pos _
  have hLle : L ≤ Real.exp (9 * Real.sqrt K * τ) := by
    apply Real.exp_le_exp.mpr
    calc
      9 * Real.sqrt (K / r ^ 4) * |(t : ℝ) - s| ≤
          9 * Real.sqrt (K / r ^ 4) * (τ * r ^ 2) :=
        mul_le_mul_of_nonneg_left htime (by positivity)
      _ = 9 * Real.sqrt K * τ := by rw [hsqrt]; field_simp [(sq_pos_of_pos hr).ne']
  have hfit : L * (2 * r) < R := by
    have hLfit : L * 2 < 5 / 2 :=
      (mul_le_mul_of_nonneg_right hLle (by norm_num)).trans_lt hτfit
    have hh := mul_lt_mul_of_pos_right hLfit hr
    dsimp only [R]
    nlinarith
  have hsmall : 2 * r < R / L := (lt_div_iff₀ hL).mpr (by simpa only [mul_comm] using hfit)
  have hlower (x : V) (hx : x.val ∈ riemannianClosedBallOf (S.base.metric t) p R)
      (w : TangentSpace ThreeModel x) :
      (S.base.metric t).inner x.val w w ≤ L ^ 2 *
        (S.base.metric s).inner x.val
          (mfderiv ThreeModel ThreeModel (Subtype.val : V → (H.stageAt t).Carrier) x w)
          (mfderiv ThreeModel ThreeModel (Subtype.val : V → (H.stageAt t).Carrier) x w) := by
    rw [mfderiv_subtype_val_apply]
    have hx3 : x.val ∈ riemannianClosedBallOf
        (H.stageMetric (H.activeStage t) t) p (3 * r) := by
      rw [← hmetric]
      have hxV : riemannianEDistOf (S.base.metric t) p x.val < ENNReal.ofReal (3 * r) :=
        hsource hx
      exact hxV.le
    have hRm' (u : ℝ) (hu : u ∈ Icc a t.val) :
        normSq0S (S.base.metric u) x.val 4 (S.base.rm04 u x.val) ≤ K / r ^ 4 := by
      change normSq0S (S.base.metric u) x.val 4 (metricRm04At (S.base.metric u) x.val) ≤ _
      rw [hmetric]
      exact hRm u hu x.val hx3
    have hh := (metric_inner_exp_bounds_of_curvature_bound S hS hcarrier hregular x.val
      hRm' ⟨hab.le, le_rfl⟩ hsab w).2
    have hexp : Real.exp (2 * (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 *
        Real.sqrt (K / r ^ 4) * |(t : ℝ) - s|) = L ^ 2 := by
      dsimp only [L]
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num [ThreeSpace]
      ring
    simpa only [hexp] using hh
  have hcapture := Geometry.Metric.ball_subset_image_of_metric_lower_on_opens
    (S.base.metric s) (S.base.metric t) V (Subtype.val : V → (H.stageAt t).Carrier)
    (isLocalDiffeomorph_subtype_val V) Subtype.val_injective pV
    hR hL hcpt hsource hlower
  have hstay : riemannianClosedBallOf (S.base.metric s) p (2 * r) ⊆
      riemannianClosedBallOf (S.base.metric t) p R := by
    intro x hx
    have hx' : x ∈ riemannianBallOf (S.base.metric s) p (R / L) :=
      hx.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (div_pos hR hL)).mpr hsmall)
    obtain ⟨y, hy, hyx⟩ := hcapture hx'
    exact hyx ▸ hy
  refine ⟨hdom, ?_, ?_⟩
  · have hinside : riemannianClosedBallOf (S.base.metric s) p (2 * r) ⊆
        riemannianBallOf (S.base.metric t) p (3 * r) := hstay.trans hsource
    simpa only [hmetric] using hinside
  · rw [← hmetric]
    exact hcpt.of_isClosed_subset (hclosed s (2 * r)) hstay

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
