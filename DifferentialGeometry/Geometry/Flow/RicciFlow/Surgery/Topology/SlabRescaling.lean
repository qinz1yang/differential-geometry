import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.IntervalTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.MetricJetScaling

noncomputable section
open Bundle Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage

universe u
variable {P : OrientedThreeStage.{u}}

private local instance stageC1 : IsManifold ThreeModel 1 P.Carrier :=
  IsManifold.of_le (I := ThreeModel) (M := P.Carrier) (n := ∞) (by decide)

private theorem rescale_time (a μ t : ℝ) (hμ : 0 < μ) :
    parabolicTime a μ⁻¹ (t + (-a / μ)) = μ * t := by
  dsimp [parabolicTime]
  field_simp [hμ.ne']
  ring

private def scaledFlow {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := P.Carrier) D)
    (μ : ℝ) (hμ : 0 < μ) (D' : RealTimeInterval) :
    SolutionOn (I := ThreeModel) (M := P.Carrier) D' :=
  ((parabolicSolution S D.initial μ⁻¹ (inv_pos.mpr hμ) D.initial_mem).timeShift
    (-D.initial / μ)).cast D'

private theorem scaledFlow_metric {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := P.Carrier) D)
    (μ : ℝ) (hμ : 0 < μ) (D' : RealTimeInterval) (t : ℝ) :
    (scaledFlow S μ hμ D').base.metric t =
      scaleMetric μ⁻¹ (inv_pos.mpr hμ) (S.base.metric (μ * t)) := by
  simp only [scaledFlow, SolutionOn.cast_metric, SolutionOn.timeShift_base,
    SolutionFamily.timeShift_metric, parabolicSolution_metric, rescale_time _ _ _ hμ]

private theorem scaledFlow_metric_eq {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := P.Carrier) D)
    (μ : ℝ) (hμ : 0 < μ) (D' : RealTimeInterval) :
    (scaledFlow S μ hμ D').base.metric =
      fun t => scaleMetric μ⁻¹ (inv_pos.mpr hμ) (S.base.metric (μ * t)) :=
  funext (scaledFlow_metric S μ hμ D')

private theorem scaledFlow_equation {D D' : RealTimeInterval}
    {S : SolutionOn (I := ThreeModel) (M := P.Carrier) D}
    (hS : IsSolutionOn S) (μ : ℝ) (hμ : 0 < μ)
    (hcarrier : D'.carrier = {t | μ * t ∈ D.carrier})
    (hregular : D'.regular = {t | μ * t ∈ D.regular}) :
    IsSolutionOn (scaledFlow S μ hμ D') := by
  apply isSolutionOn_cast
    (isSolutionOn_timeShift (parabolicSolution_isSolutionOn S hS D.initial μ⁻¹ (inv_pos.mpr hμ)
      D.initial_mem) (-D.initial / μ))
  · rw [hcarrier]
    ext t
    simp only [RealTimeInterval.timeShift_carrier, mem_ofPred_eq, parabolicInterval_carrier,
      rescale_time _ _ _ hμ]
  · rw [hregular]
    ext t
    simp only [RealTimeInterval.timeShift_regular, mem_ofPred_eq, parabolicInterval_regular,
      rescale_time _ _ _ hμ]

theorem MetricSmoothUpTo.rescale {g : ℝ → P.Metric} {J J' : Set ℝ}
    (hg : P.MetricSmoothUpTo g J) (μ : ℝ) (hμ : 0 < μ)
    (hJ : MapsTo (fun t => μ * t) J' J) :
    P.MetricSmoothUpTo (fun t => scaleMetric μ⁻¹ (inv_pos.mpr hμ) (g (μ * t))) J' := by
  intro p t ht
  obtain ⟨U, hU, hp, hUb, V, hV, htV, A, hA, hEq⟩ := hg p (μ * t) (hJ ht)
  refine ⟨U, hU, hp, hUb, (fun s : ℝ => μ * s) ⁻¹' V,
    hV.preimage (continuous_const.mul continuous_id), htV,
    (fun z i j => μ⁻¹ * A (μ * z.1, z.2) i j), ?_, ?_⟩
  · intro i j
    have hmap : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) (𝓘(ℝ, ℝ).prod ThreeModel) ∞
        (fun z : ℝ × P.Carrier => (μ * z.1, z.2)) :=
      (contMDiff_const.mul contMDiff_fst).prodMk contMDiff_snd
    exact contMDiffOn_const.mul ((hA i j).comp hmap.contMDiffOn
      (fun z hz => ⟨hz.1, hz.2⟩))
  · intro s hs x hx i j
    change μ⁻¹ * A (μ * s, x) i j = _
    rw [hEq (μ * s) ⟨hs.1, hJ hs.2⟩ x hx i j, scaleMetric_inner]

private theorem preimage_Ico_scale (a b μ : ℝ) (hμ : 0 < μ) :
    Ico (a / μ) (b / μ) = {t | μ * t ∈ Ico a b} := by
  ext t
  simp only [mem_Ico, mem_ofPred_eq, div_le_iff₀ hμ, lt_div_iff₀ hμ, mul_comm t μ]

private theorem preimage_Ioo_scale (a b μ : ℝ) (hμ : 0 < μ) :
    Ioo (a / μ) (b / μ) = {t | μ * t ∈ Ioo a b} := by
  ext t
  simp only [mem_Ioo, mem_ofPred_eq, div_lt_iff₀ hμ, lt_div_iff₀ hμ, mul_comm t μ]

private theorem preimage_Icc_scale (a b μ : ℝ) (hμ : 0 < μ) :
    Icc (a / μ) (b / μ) = {t | μ * t ∈ Icc a b} := by
  ext t
  simp only [mem_Icc, mem_ofPred_eq, div_le_iff₀ hμ, le_div_iff₀ hμ, mul_comm t μ]

def IncomingSlab.rescale {a b : ℝ} (G : P.IncomingSlab a b) (μ : ℝ) (hμ : 0 < μ) :
    P.IncomingSlab (a / μ) (b / μ) where
  lt := div_lt_div_of_pos_right G.lt hμ
  flow := scaledFlow G.flow μ hμ _
  equation := scaledFlow_equation G.equation μ hμ
    (preimage_Ico_scale a b μ hμ) (preimage_Ioo_scale a b μ hμ)
  smoothUpTo := by
    simpa only [scaledFlow_metric_eq] using G.smoothUpTo.rescale μ hμ
      (show MapsTo (fun t => μ * t) (Ico (a / μ) (b / μ)) (Ico a b) from
        fun t ht => by rwa [preimage_Ico_scale a b μ hμ] at ht)

def ClosedSlab.rescale {a b : ℝ} (G : P.ClosedSlab a b) (μ : ℝ) (hμ : 0 < μ) :
    P.ClosedSlab (a / μ) (b / μ) where
  lt := div_lt_div_of_pos_right G.lt hμ
  flow := scaledFlow G.flow μ hμ _
  equation := scaledFlow_equation G.equation μ hμ
    (preimage_Icc_scale a b μ hμ) (preimage_Ioo_scale a b μ hμ)
  smoothUpTo := by
    simpa only [scaledFlow_metric_eq] using G.smoothUpTo.rescale μ hμ
      (show MapsTo (fun t => μ * t) (Icc (a / μ) (b / μ)) (Icc a b) from
        fun t ht => by rwa [preimage_Icc_scale a b μ hμ] at ht)

@[simp] theorem IncomingSlab.rescale_metric {a b : ℝ} (G : P.IncomingSlab a b)
    (μ : ℝ) (hμ : 0 < μ) (t : ℝ) :
    (G.rescale μ hμ).flow.base.metric t =
      scaleMetric μ⁻¹ (inv_pos.mpr hμ) (G.flow.base.metric (μ * t)) :=
  scaledFlow_metric G.flow μ hμ _ t

@[simp] theorem ClosedSlab.rescale_metric {a b : ℝ} (G : P.ClosedSlab a b)
    (μ : ℝ) (hμ : 0 < μ) (t : ℝ) :
    (G.rescale μ hμ).flow.base.metric t =
      scaleMetric μ⁻¹ (inv_pos.mpr hμ) (G.flow.base.metric (μ * t)) :=
  scaledFlow_metric G.flow μ hμ _ t

theorem IncomingSlab.rescale_riemannNorm {a b : ℝ} (G : P.IncomingSlab a b)
    (μ : ℝ) (hμ : 0 < μ) (t : ℝ) (x : P.Carrier) :
    (G.rescale μ hμ).riemannNorm t x = μ * G.riemannNorm (μ * t) x := by
  have hsq := parabolicRmNormSq G.flow a μ⁻¹ (inv_pos.mpr hμ)
    (show a ∈ (RealTimeInterval.closedOpen a b G.lt).carrier from ⟨le_rfl, G.lt⟩)
    (t + (-a / μ)) x
  simp only [inv_inv, rescale_time _ _ _ hμ] at hsq
  change Real.sqrt (normSq0S ((G.rescale μ hμ).flow.base.metric t) x 4
    ((G.rescale μ hμ).flow.base.rm04 t x)) =
      μ * Real.sqrt (normSq0S (G.flow.base.metric (μ * t)) x 4 (G.flow.base.rm04 (μ * t) x))
  rw [show normSq0S ((G.rescale μ hμ).flow.base.metric t) x 4
      ((G.rescale μ hμ).flow.base.rm04 t x) =
      μ ^ 2 * normSq0S (G.flow.base.metric (μ * t)) x 4 (G.flow.base.rm04 (μ * t) x)
      from hsq,
    Real.sqrt_mul (sq_nonneg μ), Real.sqrt_sq hμ.le]

theorem IncomingSlab.rescale_terminalRegularRegion {a b : ℝ} (G : P.IncomingSlab a b)
    (μ : ℝ) (hμ : 0 < μ) :
    (G.rescale μ hμ).terminalRegularRegion = G.terminalRegularRegion := by
  ext x
  constructor
  · rintro ⟨U, hU, hx, d, hd, K, hK, hbound⟩
    have hd' : μ * d ∈ Ico a b := by
      rwa [preimage_Ico_scale a b μ hμ] at hd
    refine ⟨U, hU, hx, μ * d, hd', K / μ, div_nonneg hK hμ.le, ?_⟩
    intro y hy t ht
    have ht' : t / μ ∈ Ico d (b / μ) := by
      constructor
      · exact (le_div_iff₀ hμ).mpr (by simpa only [mul_comm d μ] using ht.1)
      · exact (div_lt_div_iff_of_pos_right hμ).mpr ht.2
    have hb := hbound y hy (t / μ) ht'
    rw [rescale_riemannNorm, mul_div_cancel₀ t hμ.ne'] at hb
    exact (le_div_iff₀ hμ).mpr (by simpa only [mul_comm μ] using hb)
  · rintro ⟨U, hU, hx, d, hd, K, hK, hbound⟩
    refine ⟨U, hU, hx, d / μ,
      ⟨(div_le_div_iff_of_pos_right hμ).mpr hd.1,
        (div_lt_div_iff_of_pos_right hμ).mpr hd.2⟩,
      μ * K, mul_nonneg hμ.le hK, ?_⟩
    intro y hy t ht
    rw [rescale_riemannNorm]
    have ht' : μ * t ∈ Ico d b := by
      rwa [preimage_Ico_scale d b μ hμ] at ht
    exact mul_le_mul_of_nonneg_left (hbound y hy (μ * t) ht') hμ.le

theorem IncomingSlab.rescale_terminalRegularOpen {a b : ℝ} (G : P.IncomingSlab a b)
    (μ : ℝ) (hμ : 0 < μ) :
    (G.rescale μ hμ).terminalRegularOpen = G.terminalRegularOpen := by
  apply TopologicalSpace.Opens.ext
  exact G.rescale_terminalRegularRegion μ hμ

private theorem restrictOpen_scaleMetric (g : P.Metric) (U : TopologicalSpace.Opens P.Carrier)
    (c : ℝ) (hc : 0 < c) :
    (scaleMetric c hc g).restrictOpen U = scaleMetric c hc (g.restrictOpen U) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rfl

theorem IncomingSlab.TerminalLimitMetric.rescale_converges {a b : ℝ}
    {G : P.IncomingSlab a b} (L : G.TerminalLimitMetric) (μ : ℝ) (hμ : 0 < μ) :
    ∀ K : Set G.terminalRegularOpen, IsCompact K → ∀ j : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ d ∈ Ico (a / μ) (b / μ), ∀ t ∈ Ioo d (b / μ), ∀ x ∈ K,
        metricDerivNorm j (((G.rescale μ hμ).flow.base.metric t).restrictOpen
          G.terminalRegularOpen)
          (scaleMetric μ⁻¹ (inv_pos.mpr hμ) L.metric)
          (scaleMetric μ⁻¹ (inv_pos.mpr hμ) L.metric) x < ε := by
  intro K hK j ε hε
  let w : ℝ := Real.sqrt (μ ^ j)
  have hw : 0 < w := Real.sqrt_pos.mpr (pow_pos hμ j)
  obtain ⟨d, hd, hbound⟩ := L.converges K hK j (ε / w) (div_pos hε hw)
  refine ⟨d / μ, ⟨(div_le_div_iff_of_pos_right hμ).mpr hd.1,
    (div_lt_div_iff_of_pos_right hμ).mpr hd.2⟩, ?_⟩
  intro t ht x hx
  have ht' : μ * t ∈ Ioo d b := by
    rwa [preimage_Ioo_scale d b μ hμ] at ht
  rw [IncomingSlab.rescale_metric, restrictOpen_scaleMetric,
    Perelman.KappaSolutions.metricDerivNorm_scale_all, inv_inv]
  exact (mul_lt_mul_of_pos_left (hbound (μ * t) ht' x hx) hw).trans_eq
    (by field_simp [hw.ne'])

def IncomingSlab.TerminalLimitMetric.rescale {a b : ℝ}
    {G : P.IncomingSlab a b} (L : G.TerminalLimitMetric) (μ : ℝ) (hμ : 0 < μ) :
    (G.rescale μ hμ).TerminalLimitMetric := by
  let T (U : TopologicalSpace.Opens P.Carrier) :=
    {gbar : SmoothRiemannianMetric ThreeModel U //
      ∀ K : Set U, IsCompact K → ∀ j : ℕ, ∀ ε : ℝ, 0 < ε →
        ∃ d ∈ Ico (a / μ) (b / μ), ∀ t ∈ Ioo d (b / μ), ∀ x ∈ K,
          metricDerivNorm j (((G.rescale μ hμ).flow.base.metric t).restrictOpen U)
            gbar gbar x < ε}
  let old : T G.terminalRegularOpen :=
    ⟨scaleMetric μ⁻¹ (inv_pos.mpr hμ) L.metric, L.rescale_converges μ hμ⟩
  let new : T (G.rescale μ hμ).terminalRegularOpen :=
    (G.rescale_terminalRegularOpen μ hμ).symm ▸ old
  exact ⟨new.1, new.2⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage
