import DifferentialGeometry.Geometry.Measure.PartialDiffeomorphComparison
import DifferentialGeometry.Geometry.Metric.Comparison.PartialDiffeomorphBalls
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.BallContinuity
import DifferentialGeometry.Bundle.FiberBundleHausdorff
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import Mathlib.Topology.UniformSpace.HeineCantor

noncomputable section

open Manifold MeasureTheory Set
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Measure

open Integral.Measure (riemannianVolumeMeasure)

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [T2Space N] [SigmaCompactSpace N]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace N := borel N
private local instance : BorelSpace N := ⟨rfl⟩

theorem riemannianVolumeMeasure_ball_bounds_of_partialDiffeomorph_metric_bounds
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (Φ : PartialDiffeomorph I J M N ∞) (p : M)
    {R r a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hsmall : r / a < R) (hlarge : b * r < R)
    (hcpt : IsCompact (riemannianClosedBallOf g p R))
    (hsource : riemannianClosedBallOf g p R ⊆ Φ.source)
    (hlower : ∀ x ∈ riemannianClosedBallOf g p R, ∀ v : TangentSpace I x,
      g.inner x v v ≤ b ^ 2 * h.inner (Φ x)
        (mfderiv I J (Φ : M → N) x v) (mfderiv I J (Φ : M → N) x v))
    (hupper : ∀ x ∈ riemannianClosedBallOf g p R, ∀ v : TangentSpace I x,
      h.inner (Φ x) (mfderiv I J (Φ : M → N) x v)
        (mfderiv I J (Φ : M → N) x v) ≤ a ^ 2 * g.inner x v v) :
    riemannianVolumeMeasure I M g (riemannianBallOf g p (r / a)) ≤
        ENNReal.ofReal (b ^ Module.finrank ℝ E) *
          riemannianVolumeMeasure J N h (riemannianBallOf h (Φ p) r) ∧
      riemannianVolumeMeasure J N h (riemannianBallOf h (Φ p) r) ≤
        ENNReal.ofReal (a ^ Module.finrank ℝ E) *
          riemannianVolumeMeasure I M g (riemannianBallOf g p (b * r)) := by
  have hmeas (s : ℝ) : MeasurableSet (riemannianBallOf g p s) :=
    (isOpen_lt (Riemannian.continuous_riemannianEDist g p) continuous_const).measurableSet
  have hsub (s : ℝ) (hs : s < R) :
      riemannianBallOf g p s ⊆ riemannianClosedBallOf g p R :=
    fun _ hx => hx.le.trans (ENNReal.ofReal_le_ofReal hs.le)
  have hsqrt (c : ℝ) (hc : 0 ≤ c) :
      Real.sqrt ((c ^ 2) ^ Module.finrank ℝ E) = c ^ Module.finrank ℝ E := by
    rw [← pow_mul, mul_comm 2 (Module.finrank ℝ E), pow_mul,
      Real.sqrt_sq (pow_nonneg hc _)]
  constructor
  · have himage := PartialDiffeomorph.image_riemannianBall_subset_of_metric_upper
      g h Φ p ha hsmall hsource hupper
    have hcancel : a * (r / a) = r := mul_div_cancel₀ r ha.ne'
    rw [hcancel] at himage
    have hvol := riemannianVolumeMeasure_le_image_of_partialDiffeomorph_metric_le
      g h Φ (hmeas (r / a)) ((hsub (r / a) hsmall).trans hsource)
      (sq_pos_of_pos hb) (fun x hx => hlower x (hsub (r / a) hsmall hx))
    rw [hsqrt b hb.le] at hvol
    exact hvol.trans (mul_le_mul' le_rfl (measure_mono himage))
  · have hcapture := PartialDiffeomorph.riemannianBall_subset_image_of_metric_lower
      g h Φ p hb hlarge hcpt hsource hlower
    have hvol := riemannianVolumeMeasure_image_le_of_partialDiffeomorph_metric_le
      g h Φ (hmeas (b * r)) ((hsub (b * r) hlarge).trans hsource)
      (sq_pos_of_pos ha) (fun x hx => hupper x (hsub (b * r) hlarge hx))
    rw [hsqrt a ha.le] at hvol
    exact (measure_mono hcapture).trans hvol

end DifferentialGeometry.Geometry.Measure

namespace DifferentialGeometry.Geometry.Measure

open Integral.Measure (riemannianVolumeMeasure continuousAt_riemannianBallOf_realVolume)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [PreconnectedSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private theorem riemannianBallOf_realVolume_uniform_scale
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    (K : Set M) (hK : IsCompact K) {r₀ ε : ℝ} (hr₀ : 0 < r₀) (hε : 0 < ε) :
    ∃ δ > 0, δ ≤ 1 / 2 ∧ δ ≤ r₀ / 2 ∧
      ∀ p ∈ K, ∀ a b s : ℝ, |a - 1| < δ → |b - 1| < δ → |s - r₀| < δ →
        |(riemannianVolumeMeasure I M g (riemannianBallOf g p (s / a))).toReal /
            b ^ Module.finrank ℝ E -
          (riemannianVolumeMeasure I M g (riemannianBallOf g p r₀)).toReal| < ε ∧
        |a ^ Module.finrank ℝ E *
            (riemannianVolumeMeasure I M g (riemannianBallOf g p (b * s))).toReal -
          (riemannianVolumeMeasure I M g (riemannianBallOf g p r₀)).toReal| < ε := by
  let _ : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  let _ : PseudoMetricSpace M := g.toPseudoMetricSpace
  let V : M × ℝ → ℝ := fun z =>
    (riemannianVolumeMeasure I M g (riemannianBallOf g z.1 z.2)).toReal
  let f : M × (ℝ × ℝ × ℝ) → ℝ × ℝ := fun z =>
    (V (z.1, z.2.2.2 / z.2.1) / z.2.2.1 ^ Module.finrank ℝ E,
      z.2.1 ^ Module.finrank ℝ E * V (z.1, z.2.2.1 * z.2.2.2))
  have hc : IsCompact (K ×ˢ ({(1, 1, r₀)} : Set (ℝ × ℝ × ℝ))) :=
    hK.prod isCompact_singleton
  have hf : ∀ z ∈ K ×ˢ ({(1, 1, r₀)} : Set (ℝ × ℝ × ℝ)), ContinuousAt f z := by
    rintro ⟨p, t⟩ ⟨_, ht⟩
    have ht' : t = (1, 1, r₀) := ht
    subst t
    have hp : ContinuousAt (fun z : M × (ℝ × ℝ × ℝ) => z.1) (p, (1, 1, r₀)) :=
      continuousAt_fst
    have ha : ContinuousAt (fun z : M × (ℝ × ℝ × ℝ) => z.2.1) (p, (1, 1, r₀)) :=
      continuousAt_snd.fst
    have hb : ContinuousAt (fun z : M × (ℝ × ℝ × ℝ) => z.2.2.1) (p, (1, 1, r₀)) :=
      continuousAt_snd.snd.fst
    have hs : ContinuousAt (fun z : M × (ℝ × ℝ × ℝ) => z.2.2.2) (p, (1, 1, r₀)) :=
      continuousAt_snd.snd.snd
    have hv : ContinuousAt V (p, r₀) :=
      continuousAt_riemannianBallOf_realVolume g hcomplete p hr₀
    have hdiv : ContinuousAt (fun z : M × (ℝ × ℝ × ℝ) => z.2.2.2 / z.2.1)
        (p, (1, 1, r₀)) := hs.div₀ ha one_ne_zero
    have hmul : ContinuousAt (fun z : M × (ℝ × ℝ × ℝ) => z.2.2.1 * z.2.2.2)
        (p, (1, 1, r₀)) := by
      simpa only [Pi.mul_def] using hb.mul hs
    have hvlo : ContinuousAt (fun z : M × (ℝ × ℝ × ℝ) =>
        V (z.1, z.2.2.2 / z.2.1)) (p, (1, 1, r₀)) :=
      hv.comp_of_eq (hp.prodMk hdiv) (by simp only [div_one])
    have hvhi : ContinuousAt (fun z : M × (ℝ × ℝ × ℝ) =>
        V (z.1, z.2.2.1 * z.2.2.2)) (p, (1, 1, r₀)) :=
      hv.comp_of_eq (hp.prodMk hmul) (by simp only [one_mul])
    have hpa : ContinuousAt (fun z : M × (ℝ × ℝ × ℝ) => z.2.1 ^ Module.finrank ℝ E)
        (p, (1, 1, r₀)) := by
      simpa only [Pi.pow_def] using ha.pow (Module.finrank ℝ E)
    have hpb : ContinuousAt (fun z : M × (ℝ × ℝ × ℝ) => z.2.2.1 ^ Module.finrank ℝ E)
        (p, (1, 1, r₀)) := by
      simpa only [Pi.pow_def] using hb.pow (Module.finrank ℝ E)
    have hlo := hvlo.div₀ hpb (pow_ne_zero _ one_ne_zero)
    have hhi : ContinuousAt (fun z : M × (ℝ × ℝ × ℝ) =>
        z.2.1 ^ Module.finrank ℝ E * V (z.1, z.2.2.1 * z.2.2.2))
        (p, (1, 1, r₀)) := by
      simpa only [Pi.mul_def] using hpa.mul hvhi
    exact hlo.prodMk hhi
  have hunif := hc.uniformContinuousAt_of_continuousAt f hf
    (Metric.dist_mem_uniformity hε)
  obtain ⟨η, hη, hηbound⟩ := Metric.mem_uniformity_dist.mp hunif
  let δ := min η (min (1 / 2) (r₀ / 2))
  have hδη : δ ≤ η := min_le_left _ _
  have hδhalf : δ ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδr : δ ≤ r₀ / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ, lt_min hη (lt_min (by norm_num) (half_pos hr₀)), hδhalf, hδr, ?_⟩
  intro p hp a b s ha hb hs
  have ha' : dist (1 : ℝ) a < η := by
    rw [Real.dist_eq, abs_sub_comm]
    exact ha.trans_le hδη
  have hb' : dist (1 : ℝ) b < η := by
    rw [Real.dist_eq, abs_sub_comm]
    exact hb.trans_le hδη
  have hs' : dist r₀ s < η := by
    rw [Real.dist_eq, abs_sub_comm]
    exact hs.trans_le hδη
  have hprod : dist (p, (1, 1, r₀)) (p, (a, b, s)) < η := by
    simp only [Prod.dist_eq, dist_self]
    exact max_lt hη (max_lt ha' (max_lt hb' hs'))
  have hout := hηbound hprod ⟨hp, mem_singleton (1, 1, r₀)⟩
  change dist (f (p, (1, 1, r₀))) (f (p, (a, b, s))) < ε at hout
  rw [dist_comm, Prod.dist_eq] at hout
  simpa only [f, V, one_pow, div_one, one_mul, Real.dist_eq] using max_lt_iff.mp hout

private theorem riemannianClosedBallOf_isCompact_of_complete
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    (p : M) (R : ℝ) : IsCompact (riemannianClosedBallOf g p R) := by
  by_cases hdim : Module.finrank ℝ E = 0
  · let _ : Subsingleton E := Module.finrank_zero_iff.mp hdim
    let _ : Subsingleton H := I.injective.subsingleton
    let _ : DiscreteTopology M := ChartedSpace.discreteTopology H M
    let _ : Subsingleton M := subsingleton_of_preconnected_totallyDisconnected
    exact (Set.subsingleton_of_subsingleton (s := riemannianClosedBallOf g p R)).isCompact
  · let _ : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
    let _ : IsManifold I 1 M := IsManifold.of_le (I := I) (n := ∞) (by decide)
    let _ : T2Space (TangentBundle I M) := inferInstance
    exact hcomplete.closedEBall_isCompact p R

universe u' v' w'

theorem exists_riemannianBallOf_realVolume_close_of_partialDiffeomorph_metric_bounds
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    (K : Set M) (hK : IsCompact K) {r₀ ε : ℝ} (hr₀ : 0 < r₀) (hε : 0 < ε) :
    ∃ δ > 0,
      ∀ (F : Type u') [NormedAddCommGroup F] [NormedSpace ℝ F]
        [FiniteDimensional ℝ F] (H' : Type v') [TopologicalSpace H']
        (J : ModelWithCorners ℝ F H') [J.Boundaryless]
        (N : Type w') [TopologicalSpace N] [ChartedSpace H' N]
        [IsManifold J ∞ N] [T2Space N] [SigmaCompactSpace N]
        (h : SmoothRiemannianMetric J N) (Φ : PartialDiffeomorph I J M N ∞)
        (p : M), p ∈ K → ∀ a b s R : ℝ,
        |a - 1| < δ → |b - 1| < δ → |s - r₀| < δ →
        s / a < R → b * s < R →
        riemannianClosedBallOf g p R ⊆ Φ.source →
        (∀ x ∈ riemannianClosedBallOf g p R, ∀ v : TangentSpace I x,
          g.inner x v v ≤ b ^ 2 * h.inner (Φ x)
            (mfderiv I J (Φ : M → N) x v) (mfderiv I J (Φ : M → N) x v)) →
        (∀ x ∈ riemannianClosedBallOf g p R, ∀ v : TangentSpace I x,
          h.inner (Φ x) (mfderiv I J (Φ : M → N) x v)
            (mfderiv I J (Φ : M → N) x v) ≤ a ^ 2 * g.inner x v v) →
        |(riemannianVolumeMeasure J N h (riemannianBallOf h (Φ p) s)).toReal -
          (riemannianVolumeMeasure I M g (riemannianBallOf g p r₀)).toReal| < ε := by
  obtain ⟨δ, hδ, hδhalf, _, hbound⟩ :=
    riemannianBallOf_realVolume_uniform_scale g hcomplete K hK hr₀ hε
  refine ⟨δ, hδ, ?_⟩
  intro F _ _ _ H' _ J _ N _ _ _ _ _ h Φ p hp a b s R ha hb hs hsmall hlarge
    hsource hlower hupper
  have hapos : 0 < a := by have := (abs_lt.mp ha).1; linarith
  have hbpos : 0 < b := by have := (abs_lt.mp hb).1; linarith
  have hcpt : IsCompact (riemannianClosedBallOf g p R) :=
    riemannianClosedBallOf_isCompact_of_complete g hcomplete p R
  let _ : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure I M g) :=
    Integral.Measure.riemannianVolumeMeasure_isFiniteMeasureOnCompacts g
  have hsub (r : ℝ) (hr : r < R) :
      riemannianBallOf g p r ⊆ riemannianClosedBallOf g p R :=
    fun _ hx => hx.le.trans (ENNReal.ofReal_le_ofReal hr.le)
  have hfinite (r : ℝ) (hr : r < R) :
      riemannianVolumeMeasure I M g (riemannianBallOf g p r) ≠ ⊤ :=
    ne_top_of_le_ne_top hcpt.measure_lt_top.ne (measure_mono (hsub r hr))
  obtain ⟨hlo, hhi⟩ := riemannianVolumeMeasure_ball_bounds_of_partialDiffeomorph_metric_bounds
    g h Φ p hapos hbpos hsmall hlarge hcpt hsource hlower hupper
  have hAfin : ENNReal.ofReal (a ^ Module.finrank ℝ E) *
      riemannianVolumeMeasure I M g (riemannianBallOf g p (b * s)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfinite _ hlarge)
  have htarget : riemannianVolumeMeasure J N h (riemannianBallOf h (Φ p) s) ≠ ⊤ :=
    ne_top_of_le_ne_top hAfin hhi
  have hBfin : ENNReal.ofReal (b ^ Module.finrank ℝ E) *
      riemannianVolumeMeasure J N h (riemannianBallOf h (Φ p) s) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top htarget
  have hloreal := ENNReal.toReal_mono hBfin hlo
  have hhireal := ENNReal.toReal_mono hAfin hhi
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hbpos.le _)] at hloreal
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hapos.le _)] at hhireal
  have hdivide :
      (riemannianVolumeMeasure I M g (riemannianBallOf g p (s / a))).toReal /
        b ^ Module.finrank ℝ E ≤
          (riemannianVolumeMeasure J N h (riemannianBallOf h (Φ p) s)).toReal := by
    apply (div_le_iff₀ (pow_pos hbpos _)).mpr
    simpa only [mul_comm] using hloreal
  obtain ⟨hloclose, hhiclose⟩ := hbound p hp a b s ha hb hs
  rcases abs_lt.mp hloclose with ⟨hlocl, _⟩
  rcases abs_lt.mp hhiclose with ⟨_, hhicr⟩
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

end DifferentialGeometry.Geometry.Measure
