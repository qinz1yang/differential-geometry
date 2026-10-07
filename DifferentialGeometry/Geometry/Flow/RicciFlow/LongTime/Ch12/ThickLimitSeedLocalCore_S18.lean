import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitSeedLocalCurv_S18

/-!
# CH12-S18 / V1a, group V: the generic seed at a limit point

For a pointed smooth convergence with canonical domains (no completeness of the limit), every
limit point `x` has a seed `(a, v)` of fixed constants at `Φ_i x` for large `i`:
`sec ≥ -a⁻²` on `B(Φ_i x, a)` and `vol B(Φ_i x, a) ≥ v a³`.
-/

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set _root_.MeasureTheory Integral.Measure
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

private local instance coreS18Meas (P : PointedRiemannianManifold.{u, uE, uH} I) :
    MeasurableSpace P.M := borel P.M
private local instance coreS18Borel (P : PointedRiemannianManifold.{u, uE, uH} I) :
    BorelSpace P.M := ⟨rfl⟩

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

theorem exists_seed_at_limit_point_S18
    (F : PointedRiemannianConvergenceMaps X P phi) (C : MetricConvergenceData F)
    (hcan : ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData F i)
    (x : P.M) :
    ∃ a v : ℝ, 0 < a ∧ 0 < v ∧ ∀ᶠ i in atTop,
      (∀ q ∈ riemannianBallOf (X.obj (phi i)).metric (F.map i x) a,
        SectionalBoundedBelowAt (X.obj (phi i)).metric q (-(a ^ 2)⁻¹)) ∧
      ENNReal.ofReal (v * a ^ 3) ≤ ballVolume (X.obj (phi i)).metric (F.map i x) a := by
  have href : ∀ i, (C.domain i).referenceMetric = (C.domain i).limitMetric := by
    intro i; rw [hcan i]; rfl
  have hdomain : C.domain = CanonicalMetricCompactness.canonicalSourceData F := funext hcan
  have hconv : ∀ K : Set P.M, IsCompact K →
      metricSourceConvergesOn (I := I) F (CanonicalMetricCompactness.canonicalSourceData F) K 2 := by
    intro K hK
    have h := C.converges K hK 2
    rwa [hdomain] at h
  obtain ⟨R0, hR0, hcpt0, -⟩ :=
    Geometry.Metric.exists_pos_isCompact_riemannianClosedBallOf_subset_of_mem_nhds
      P.metric x (univ_mem : (univ : Set P.M) ∈ 𝓝 x)
  obtain ⟨Λ, hΛ, hsec⟩ := exists_eventually_sectional_lower_on_compact_S18 hconv hcpt0
  let a : ℝ := min (R0 / 3) (1 / (Λ + 1))
  have hΛ1 : 0 < Λ + 1 := by linarith
  have ha : 0 < a := lt_min (by linarith) (by positivity)
  have haR : a ≤ R0 / 3 := min_le_left _ _
  have haΛ : a ≤ 1 / (Λ + 1) := min_le_right _ _
  have ha1 : a ≤ 1 := haΛ.trans (by rw [div_le_one hΛ1]; linarith)
  have hΛa : Λ ≤ (a ^ 2)⁻¹ := by
    have ha2 : a ^ 2 ≤ 1 / (Λ + 1) := by nlinarith
    have hpos : 0 < a ^ 2 := by positivity
    have : Λ + 1 ≤ (a ^ 2)⁻¹ := by
      rw [le_inv_comm₀ hΛ1 hpos, ← one_div]
      exact ha2
    linarith
  -- ball image and local Lipschitz bound
  have hball := F.eventually_ball_subset_image_local_S18 C href x (A := a) (R := R0) (L := 2)
    one_lt_two (by linarith) hcpt0
  have hedist := F.eventually_edist_map_le_local_S18 C href x (r := a / 4) (R := R0) (L := 2)
    (by positivity) (by linarith) one_lt_two hcpt0
  -- the volume of the image of a small closed ball
  let K1 := riemannianClosedBallOf P.metric x (a / 4)
  have hK1 : IsCompact K1 :=
    hcpt0.of_isClosed_subset (Geometry.Metric.isClosed_riemannianClosedBallOf P.metric x _)
      (fun y hy => hy.trans (ENNReal.ofReal_le_ofReal (by linarith)))
  let ν := riemannianVolumeMeasure (I := I) (M := P.M) P.metric
  have hopen : IsOpen (riemannianBallOf P.metric x (a / 4)) :=
    isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist P.metric x) continuous_const
  have hxball : x ∈ riemannianBallOf P.metric x (a / 4) := by
    change riemannianEDistOf P.metric x x < ENNReal.ofReal (a / 4)
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  have hballK1 : riemannianBallOf P.metric x (a / 4) ⊆ K1 := fun y hy => (show riemannianEDistOf P.metric x y < ENNReal.ofReal (a / 4) from hy).le
  have hνpos : 0 < ν K1 := by
    have hpos := (riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := P.M) P.metric).open_pos
      _ hopen ⟨x, hxball⟩
    exact lt_of_lt_of_le (pos_iff_ne_zero.mpr hpos) (measure_mono hballK1)
  have hνfin : ν K1 ≠ ⊤ := by
    have : IsFiniteMeasureOnCompacts ν :=
      riemannianVolumeMeasure_isFiniteMeasureOnCompacts P.metric
    exact hK1.measure_lt_top.ne
  have hT : Tendsto (fun i => riemannianVolumeMeasure (I := I) (M := (X.obj (phi i)).M)
      (X.obj (phi i)).metric (F.map i '' K1)) atTop (𝓝 (ν K1)) := by
    have h := F.tendsto_setLIntegral_image C hcan hK1
      (fun i _ => (1 : ℝ≥0∞)) (fun i => measurable_const) (f := fun _ => 1) (B := 1)
      ENNReal.one_ne_top (Eventually.of_forall fun i y _ => le_rfl)
      (fun y _ => tendsto_const_nhds)
    simpa only [setLIntegral_const, one_mul] using h
  have hhalf : ν K1 / 2 < ν K1 := ENNReal.half_lt_self hνpos.ne' hνfin
  have hev := hT.eventually (lt_mem_nhds hhalf)
  refine ⟨a, (ν K1 / 2).toReal / a ^ 3, ha, ?_, ?_⟩
  · apply div_pos _ (by positivity)
    exact ENNReal.toReal_pos (by simpa using hνpos.ne') (ne_top_of_le_ne_top hνfin (ENNReal.half_le_self))
  filter_upwards [hball, hedist, hsec, hev] with i hb he hs hv
  refine ⟨fun q hq => ?_, ?_⟩
  · obtain ⟨y, hy, rfl⟩ := hb.2 hq
    exact (hs.2 y hy).mono (by linarith [hΛa])
  · have hsub : F.map i '' K1 ⊆ riemannianBallOf (X.obj (phi i)).metric (F.map i x) a := by
      rintro _ ⟨y, hy, rfl⟩
      have hx1 : x ∈ K1 := by
        change riemannianEDistOf P.metric x x ≤ _
        rw [riemannianEDistOf_self]; exact bot_le
      have h1 := he.2 x hx1 y hy
      change riemannianEDistOf (X.obj (phi i)).metric (F.map i x) (F.map i y) < ENNReal.ofReal a
      calc _ ≤ ENNReal.ofReal 2 * riemannianEDistOf P.metric x y := h1
        _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (a / 4) := mul_le_mul' le_rfl hy
        _ = ENNReal.ofReal (2 * (a / 4)) := (ENNReal.ofReal_mul (by norm_num)).symm
        _ < ENNReal.ofReal a := (ENNReal.ofReal_lt_ofReal_iff ha).2 (by linarith)
    have h3 : ENNReal.ofReal ((ν K1 / 2).toReal / a ^ 3 * a ^ 3) = ν K1 / 2 := by
      rw [div_mul_cancel₀ _ (by positivity : a ^ 3 ≠ 0),
        ENNReal.ofReal_toReal (ne_top_of_le_ne_top hνfin ENNReal.half_le_self)]
    rw [h3]
    exact hv.le.trans (measure_mono hsub)

end DifferentialGeometry.CheegerGromovCompactness
