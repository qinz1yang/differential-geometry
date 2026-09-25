import DifferentialGeometry.Analysis.Integration.Measure.VolumeDensityContinuity
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties

noncomputable section
open Set Filter MeasureTheory Bundle
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {P : Type*} [TopologicalSpace P]
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem eventually_mul_riemannianVolumeMeasure_le_on_compact
    (g : P → SmoothRiemannianMetric I M) {J : Set P}
    (hg : ∀ (z : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn (fun p : P × M => chartGramMatrix (g p.1) z p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) z).baseSet))
    {p : P} (hp : J ∈ 𝓝 p) {K : Set M} (hK : IsCompact K) {a : ℝ} (ha : a < 1) :
    ∀ᶠ q in 𝓝 p, ENNReal.ofReal a * riemannianVolumeMeasure I M (g p) K ≤
      riemannianVolumeMeasure I M (g q) K := by
  have hρ := riemannianVolumeDensity_family_continuousOn (g p) g hg
  have hev : ∀ᶠ q in 𝓝 p, ∀ z ∈ K, a < riemannianVolumeDensity (g p) (g q) z := by
    apply hK.eventually_forall_of_forall_eventually
    intro z _
    have hc : ContinuousAt (fun q : P × M => riemannianVolumeDensity (g p) (g q.1) q.2) (p,z) :=
      hρ.continuousAt (prod_mem_nhds hp univ_mem)
    have hless : a < riemannianVolumeDensity (g p) (g p) z := by
      simpa only [riemannianVolumeDensity_self] using ha
    exact hc.eventually (Ioi_mem_nhds hless)
  filter_upwards [hev] with q hq
  rw [riemannianVolumeMeasure_eq_withDensity (g p) (g q), withDensity_apply _ hK.isClosed.measurableSet]
  have hh : (∫⁻ z in K, ENNReal.ofReal a ∂riemannianVolumeMeasure I M (g p)) ≤
      ∫⁻ z in K, ENNReal.ofReal (riemannianVolumeDensity (g p) (g q) z) ∂riemannianVolumeMeasure I M (g p) := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem hK.isClosed.measurableSet] with z hz
    exact ENNReal.ofReal_le_ofReal (hq z hz).le
  simpa only [lintegral_const, Measure.restrict_apply_univ] using hh


theorem eventually_lt_riemannianVolumeMeasure_on_compact
    (g : P → SmoothRiemannianMetric I M) {J : Set P}
    (hg : ∀ (z : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn (fun p : P × M => chartGramMatrix (g p.1) z p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) z).baseSet))
    {p : P} (hp : J ∈ 𝓝 p) {K : Set M} (hK : IsCompact K)
    {b : ℝ≥0∞} (hb : b < riemannianVolumeMeasure I M (g p) K) :
    ∀ᶠ q in 𝓝 p, b < riemannianVolumeMeasure I M (g q) K := by
  let μ := riemannianVolumeMeasure I M (g p)
  let _ : IsLocallyFiniteMeasure μ := riemannianVolumeMeasure_isLocallyFiniteMeasure (g p)
  have hfinite : μ K ≠ ⊤ := hK.measure_lt_top.ne
  have hbfinite : b ≠ ⊤ := ne_top_of_lt hb
  have hpos : 0 < (μ K).toReal := ENNReal.toReal_pos (ne_of_gt (bot_le.trans_lt hb)) hfinite
  have hb_lt : b.toReal < (μ K).toReal := (ENNReal.toReal_lt_toReal hbfinite hfinite).mpr hb
  let a := (b.toReal / (μ K).toReal + 1) / 2
  have ha : a < 1 := by
    have hh := (div_lt_one hpos).mpr hb_lt
    dsimp only [a]
    linarith
  have ha0 : 0 ≤ a := by dsimp only [a]; positivity
  have hba : b.toReal < a * (μ K).toReal := by
    have he : a * (μ K).toReal = (b.toReal + (μ K).toReal) / 2 := by
      dsimp only [a]
      field_simp
    rw [he]
    linarith
  have hstrict : b < ENNReal.ofReal a * μ K := by
    rw [← ENNReal.ofReal_toReal hbfinite, ← ENNReal.ofReal_toReal hfinite,
      ← ENNReal.ofReal_mul ha0]
    exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt ENNReal.toReal_nonneg hba)).mpr hba
  filter_upwards [eventually_mul_riemannianVolumeMeasure_le_on_compact g hg hp hK ha] with q hq
  exact hstrict.trans_le hq


theorem eventually_lt_riemannianVolumeMeasure_on_compact_of_continuousAt
    (g : P → SmoothRiemannianMetric I M) {J : Set P}
    (hg : ∀ (z : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn (fun p : P × M => chartGramMatrix (g p.1) z p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) z).baseSet))
    {p : P} (hp : J ∈ 𝓝 p) {K : Set M} (hK : IsCompact K)
    {b : P → ℝ≥0∞} (hb : ContinuousAt b p)
    (hbound : b p < riemannianVolumeMeasure I M (g p) K) :
    ∀ᶠ q in 𝓝 p, b q < riemannianVolumeMeasure I M (g q) K := by
  obtain ⟨c, hbc, hc⟩ := exists_between hbound
  filter_upwards [hb.eventually (Iio_mem_nhds hbc),
    eventually_lt_riemannianVolumeMeasure_on_compact g hg hp hK hc] with q hq hqc
  exact hq.trans hqc

end DifferentialGeometry.Integral.Measure

end
