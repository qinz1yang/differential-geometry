import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SliceLocalCG_O55
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedSectionalCurvature
import DifferentialGeometry.Geometry.Metric.Comparison.PartialDiffeomorphDistance
import DifferentialGeometry.Geometry.Metric.Comparison.IntrinsicBallImage
import DifferentialGeometry.Geometry.Metric.Distance.LocalBall
import DifferentialGeometry.Geometry.Metric.Distance.MetricLocality
import DifferentialGeometry.Geometry.Comparison.RadialHessianLowerBound

/-!
# CH12-O59, group 1: slice-form local Cheeger–Gromov extraction with distance and curvature
clauses (`[FROZEN] CH12-O59 G1`)

Copy-extension of `sliceLocalCG_O55`: the same engine run, with the additional output clauses
* RADIAL: `d_gs(y, φ x) → d_L(x₀, x)` uniformly on compact sets;
* PAIR: `d_gs(φ x, φ x') → d_L(x, x')` uniformly on compact sets inside `B_L(x₀, Rb/3)`
  (lead ruling O59 (1), `[FROZEN v3] CH12-O59 LIMP`);
* SEC: the limit has nonnegative sectional curvature, from an almost-nonnegative input `hsec`;
* SCB: the limit scalar curvature is bounded on the balls `B_L(x₀, r)`, `r < Rb`.

The two distance clauses come from the generic two-sided comparison `dist_two_sided_O59`
(`edistOf_map_le_of_metric_upper_on_ball` + `riemannianBallOf_subset_image_of_metric_lower`
+ injectivity of the partial diffeomorphism on its source).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace GC.LongTime.Ch12

universe u

section Generic

variable {LM : Type*} [TopologicalSpace LM] [ChartedSpace ThreeSpace LM]
  [IsManifold ThreeModel ∞ LM] [T2Space LM]
  {N : Type*} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
  [IsManifold ThreeModel ∞ N] [T2Space N]

/-- Closed balls inside a compact closed ball of larger radius are compact. -/
theorem isCompact_closedBall_of_le_O59 (gL : SmoothRiemannianMetric ThreeModel LM) {O : LM}
    {R R' : ℝ} (hcpt : IsCompact (riemannianClosedBallOf gL O R)) (hR : R' ≤ R) :
    IsCompact (riemannianClosedBallOf gL O R') :=
  hcpt.of_isClosed_subset
    (DifferentialGeometry.Geometry.Metric.isClosed_riemannianClosedBallOf gL O R')
    (fun _ hz => le_trans hz (ENNReal.ofReal_le_ofReal hR))

/-- **Two-sided distance comparison** through a partial diffeomorphism with
`(1 - ε) gL ≤ Φ^* h ≤ (1 + ε) gL` on its source. -/
theorem dist_two_sided_O59 (gL : SmoothRiemannianMetric ThreeModel LM)
    (h : SmoothRiemannianMetric ThreeModel N)
    (Φ : PartialDiffeomorph ThreeModel ThreeModel LM N ∞) {O x : LM} {ε R D : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1)
    (hcpt : IsCompact (riemannianClosedBallOf gL O R))
    (hsub : riemannianClosedBallOf gL O R ⊆ Φ.source)
    (hmet : ∀ z ∈ Φ.source, ∀ v : TangentSpace ThreeModel z,
      (1 - ε) * gL.inner z v v ≤
          h.inner (Φ z) (mfderiv ThreeModel ThreeModel Φ z v)
            (mfderiv ThreeModel ThreeModel Φ z v) ∧
        h.inner (Φ z) (mfderiv ThreeModel ThreeModel Φ z v)
            (mfderiv ThreeModel ThreeModel Φ z v) ≤ (1 + ε) * gL.inner z v v)
    (hx : x ∈ Φ.source) (hfin : riemannianEDistOf gL O x ≠ ⊤)
    (hD : (riemannianEDistOf gL O x).toReal ≤ D) (hDR : (1 + ε) * D < (1 - ε) * R) :
    riemannianEDistOf h (Φ O) (Φ x) ≠ ⊤ ∧
      |(riemannianEDistOf h (Φ O) (Φ x)).toReal - (riemannianEDistOf gL O x).toReal| ≤
        ε * D := by
  have : LocallyCompactSpace LM := Manifold.locallyCompact_of_finiteDimensional ThreeModel
  have : LocallyCompactSpace N := Manifold.locallyCompact_of_finiteDimensional ThreeModel
  set d := (riemannianEDistOf gL O x).toReal with hd_def
  have hd0 : 0 ≤ d := ENNReal.toReal_nonneg
  have hD0 : 0 ≤ D := hd0.trans hD
  have hR0 : 0 < R := by nlinarith
  have hDR' : D < R := by nlinarith
  have hdR : riemannianEDistOf gL O x < ENNReal.ofReal R := by
    rw [← ENNReal.ofReal_toReal hfin]
    exact (ENNReal.ofReal_lt_ofReal_iff hR0).mpr (lt_of_le_of_lt hD hDR')
  -- upper bound
  have hU := PDE.RicciFlow.Perelman.KappaSolutions.edistOf_map_le_of_metric_upper_on_ball
    gL h Φ O x hR0 (Real.sqrt_pos.mpr (by linarith : (0 : ℝ) < 1 + ε)) hsub
    (fun z hz v => by
      rw [Real.sq_sqrt (by linarith)]
      exact (hmet z (hsub hz) v).2) hdR
  have hfinh : riemannianEDistOf h (Φ O) (Φ x) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hU
  set a := (riemannianEDistOf h (Φ O) (Φ x)).toReal with ha_def
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have hsq1 : Real.sqrt (1 + ε) ≤ 1 + ε := by
    calc Real.sqrt (1 + ε) ≤ Real.sqrt ((1 + ε) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = 1 + ε := Real.sqrt_sq (by linarith)
  have hsq2 : 1 - ε ≤ Real.sqrt (1 - ε) := by
    calc 1 - ε = Real.sqrt ((1 - ε) ^ 2) := (Real.sqrt_sq (by linarith)).symm
      _ ≤ Real.sqrt (1 - ε) := Real.sqrt_le_sqrt (by nlinarith)
  have hau : a ≤ Real.sqrt (1 + ε) * d := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hU
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at this
  -- lower bound: `√(1-ε) d ≤ a`
  set c := Real.sqrt (1 - ε) with hc_def
  have hc0 : 0 < c := Real.sqrt_pos.mpr (by linarith)
  have hstep : ∀ η : ℝ, 0 < η → (a + η) / c + 2 * η ≤ R → d ≤ (a + η) / c + 2 * η := by
    intro η hη hηR
    set R' := (a + η) / c + 2 * η with hR'_def
    have hcpt' := isCompact_closedBall_of_le_O59 gL hcpt hηR
    have hsub' : riemannianClosedBallOf gL O R' ⊆ Φ.source :=
      fun z hz => hsub (le_trans hz (ENNReal.ofReal_le_ofReal hηR))
    have hlower : ∀ z ∈ riemannianClosedBallOf gL O R', ∀ v : TangentSpace ThreeModel z,
        gL.inner z v v ≤ (1 / c) ^ 2 * h.inner (Φ z)
          (mfderiv ThreeModel ThreeModel (Φ : LM → N) z v)
          (mfderiv ThreeModel ThreeModel (Φ : LM → N) z v) := by
      intro z hz v
      have h1 := (hmet z (hsub' hz) v).1
      rw [div_pow, one_pow, hc_def, Real.sq_sqrt (by linarith), one_div_mul_eq_div,
        le_div_iff₀ (by linarith)]
      linarith
    have hO : O ∈ riemannianBallOf gL O η := by
      change riemannianEDistOf gL O O < ENNReal.ofReal η
      rw [riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr hη
    have himg := DifferentialGeometry.PartialDiffeomorph.riemannianBallOf_subset_image_of_metric_lower
      gL h Φ (C := 1 / c) (A := a + η) (by positivity) hcpt' hsub' hlower hO
      (by rw [hR'_def, one_div_mul_eq_div]; linarith)
    have hmem : Φ x ∈ riemannianBallOf h (Φ O) (a + η) := by
      change riemannianEDistOf h (Φ O) (Φ x) < ENNReal.ofReal (a + η)
      rw [← ENNReal.ofReal_toReal hfinh]
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
    obtain ⟨z, hz, hzx⟩ := himg hmem
    have hzx' : z = x := Φ.toPartialEquiv.injOn (hsub' hz) hx hzx
    subst hzx'
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hz
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  have hac : a / c < R := by
    have h1 : a ≤ (1 + ε) * D := by nlinarith
    have h2 : (1 + ε) * D < c * R := by nlinarith
    rw [div_lt_iff₀ hc0]
    linarith
  have hlow : c * d ≤ a := by
    have hle : d ≤ a / c := by
      apply le_of_forall_pos_le_add
      intro δ hδ
      set K := 1 / c + 2 with hK
      have hKpos : 0 < K := by positivity
      set η := min δ (R - a / c) / K with hη_def
      have hmin : 0 < min δ (R - a / c) := lt_min hδ (by linarith)
      have hη : 0 < η := div_pos hmin hKpos
      have hexp : (a + η) / c + 2 * η = a / c + min δ (R - a / c) := by
        rw [hη_def, hK]; field_simp; ring
      have := hstep η hη (by rw [hexp]; linarith [min_le_right δ (R - a / c)])
      rw [hexp] at this
      linarith [min_le_left δ (R - a / c)]
    rwa [le_div_iff₀ hc0, mul_comm] at hle
  refine ⟨hfinh, abs_sub_le_iff.mpr ⟨?_, ?_⟩⟩
  · nlinarith
  · nlinarith

/-- The supremum radius of a compact set inside an open ball. -/
theorem exists_radius_of_compact_O59 (gL : SmoothRiemannianMetric ThreeModel LM) (x₀ : LM)
    {K : Set LM} (hK : IsCompact K) {ρ : ℝ} (hρ : 0 < ρ)
    (hKρ : ∀ x ∈ K, riemannianEDistOf gL x₀ x < ENNReal.ofReal ρ) :
    ∃ r₁ : ℝ, 0 ≤ r₁ ∧ r₁ < ρ ∧ ∀ x ∈ K, riemannianEDistOf gL x₀ x ≤ ENNReal.ofReal r₁ := by
  rcases K.eq_empty_or_nonempty with hKe | hne
  · exact ⟨0, le_rfl, hρ, by simp [hKe]⟩
  have hc : Continuous (fun q => riemannianEDistOf gL x₀ q) :=
    DifferentialGeometry.Geometry.Riemannian.continuous_riemannianEDist gL x₀
  obtain ⟨xs, hxs, hmax⟩ := hK.exists_isMaxOn hne hc.continuousOn
  have hlt := hKρ xs hxs
  have hfin : riemannianEDistOf gL x₀ xs ≠ ⊤ := ne_top_of_lt hlt
  refine ⟨(riemannianEDistOf gL x₀ xs).toReal, ENNReal.toReal_nonneg, ?_, fun x hx => ?_⟩
  · rw [← ENNReal.ofReal_toReal hfin] at hlt
    exact (ENNReal.ofReal_lt_ofReal_iff hρ).mp hlt
  · rw [ENNReal.ofReal_toReal hfin]
    exact hmax hx

/-- Choice of the metric-comparison constant. -/
theorem exists_eps_O59 {r R ε' : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hε' : 0 < ε') :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ (1 + ε) * r < (1 - ε) * R ∧ ε * r < ε' := by
  have hR : 0 < R := lt_of_le_of_lt hr hrR
  set ε := min (min (1 / 2) (ε' / (r + 1))) ((R - r) / (2 * (R + r) + 1)) with hε
  have h1 : ε ≤ 1 / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have h2 : ε ≤ ε' / (r + 1) := (min_le_left _ _).trans (min_le_right _ _)
  have h3 : ε ≤ (R - r) / (2 * (R + r) + 1) := min_le_right _ _
  have hpos : 0 < ε := lt_min (lt_min (by norm_num) (div_pos hε' (by linarith)))
    (div_pos (by linarith) (by linarith))
  refine ⟨ε, hpos, by linarith, ?_, ?_⟩
  · rw [le_div_iff₀ (by linarith)] at h3
    nlinarith
  · rw [le_div_iff₀ (by linarith)] at h2
    nlinarith

end Generic

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

/-- **Slice-form local Cheeger–Gromov extraction with distance and curvature clauses**
(`[FROZEN] CH12-O59 G1`). -/
theorem sliceLocalCGv3_O59 (M : ℕ → Type u) [∀ n, TopologicalSpace (M n)]
    [∀ n, ChartedSpace ThreeSpace (M n)] [∀ n, IsManifold ThreeModel ∞ (M n)]
    [∀ n, SigmaCompactSpace (M n)] [∀ n, T2Space (M n)]
    [∀ n, T2Space (TangentBundle ThreeModel (M n))]
    (g : ∀ n, SmoothRiemannianMetric ThreeModel (M n)) (y : ∀ n, M n) (Q : ℕ → ℝ)
    (hQ : ∀ n, 0 < Q n) {Rb : ℝ} (hRb : 0 < Rb)
    (hcompact : ∀ R : ℝ, 0 < R → R < Rb → ∀ᶠ n in atTop,
      IsCompact (riemannianClosedBallOf (scaleMetric (Q n) (hQ n) (g n)) (y n) R))
    (hjets : ∀ R : ℝ, 0 < R → R < Rb → ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
      ∀ w : M n, riemannianEDistOf (scaleMetric (Q n) (hQ n) (g n)) (y n) w ≤
          ENNReal.ofReal R →
        curvDerivNorm p (scaleMetric (Q n) (hQ n) (g n)) w ≤ C)
    (hvol : ∀ r R : ℝ, 0 < r → r < R → R < Rb → ∀ C : ℝ, 0 ≤ C →
      ∃ a κ : ℝ, 0 < a ∧ 0 < κ ∧ r + a ≤ R ∧ a ^ 4 * C ^ 2 ≤ 1 ∧
      ∀ᶠ n in atTop, ∀ x ∈ riemannianClosedBallOf (scaleMetric (Q n) (hQ n) (g n)) (y n) r,
        ENNReal.ofReal (κ * a ^ 3) ≤
          riemannianVolumeMeasure ThreeModel (M n) (scaleMetric (Q n) (hQ n) (g n))
            (riemannianBallOf (scaleMetric (Q n) (hQ n) (g n)) x a))
    (hsec : ∀ r : ℝ, r < Rb → ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ w : M n,
      riemannianEDistOf (scaleMetric (Q n) (hQ n) (g n)) (y n) w < ENNReal.ofReal r →
        SectionalBoundedBelowAt (scaleMetric (Q n) (hQ n) (g n)) w (-ε)) :
    ∃ (LM : Type u) (_ : TopologicalSpace LM) (_ : ChartedSpace ThreeSpace LM)
      (_ : IsManifold ThreeModel ∞ LM) (_ : T2Space LM) (_ : SigmaCompactSpace LM)
      (gL : SmoothRiemannianMetric ThreeModel LM) (x₀ : LM) (f : ℕ → ℕ), StrictMono f ∧
      ∃ (φ : ∀ k, LM → M (f k)) (src : ℕ → Set LM),
        ((∀ k, IsOpen (src k)) ∧
          (∀ K : Set LM, IsCompact K → ∀ᶠ k in atTop, K ⊆ src k) ∧
          (∀ k, x₀ ∈ src k) ∧ (∀ k, ContMDiffOn ThreeModel ThreeModel ∞ (φ k) (src k))) ∧
        (∀ k, φ k x₀ = y (f k)) ∧
        (∀ x : LM, riemannianEDistOf gL x₀ x < ENNReal.ofReal Rb) ∧
        (∀ r : ℝ, r < Rb → IsCompact (riemannianClosedBallOf gL x₀ r)) ∧
        (∀ r : ℝ, r < Rb → ∀ᶠ k in atTop, ∀ w : M (f k),
          riemannianEDistOf (scaleMetric (Q (f k)) (hQ (f k)) (g (f k))) (y (f k)) w ≤
              ENNReal.ofReal r →
            ∃ x ∈ src k, φ k x = w) ∧
        (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ x ∈ src k, ∀ v : TangentSpace ThreeModel x,
          (1 - ε) * gL.inner x v v ≤
              (scaleMetric (Q (f k)) (hQ (f k)) (g (f k))).inner (φ k x)
                (mfderiv ThreeModel ThreeModel (φ k) x v)
                (mfderiv ThreeModel ThreeModel (φ k) x v) ∧
            (scaleMetric (Q (f k)) (hQ (f k)) (g (f k))).inner (φ k x)
                (mfderiv ThreeModel ThreeModel (φ k) x v)
                (mfderiv ThreeModel ThreeModel (φ k) x v) ≤
              (1 + ε) * gL.inner x v v) ∧
        (∀ K : Set LM, IsCompact K → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ x ∈ K,
          |metricScalarAt (g (f k)) (φ k x) / Q (f k) - metricScalarAt gL x| < ε) ∧
        (∀ K : Set LM, IsCompact K → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ x ∈ K,
          |(riemannianEDistOf (scaleMetric (Q (f k)) (hQ (f k)) (g (f k))) (y (f k))
              (φ k x)).toReal - (riemannianEDistOf gL x₀ x).toReal| < ε) ∧
        (∀ K : Set LM, IsCompact K →
          (∀ x ∈ K, riemannianEDistOf gL x₀ x < ENNReal.ofReal (Rb / 3)) →
          ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ x ∈ K, ∀ x' ∈ K,
            |(riemannianEDistOf (scaleMetric (Q (f k)) (hQ (f k)) (g (f k))) (φ k x)
                (φ k x')).toReal - (riemannianEDistOf gL x x').toReal| < ε) ∧
        (∀ x : LM, SectionalBoundedBelowAt gL x 0) ∧
        (∀ r : ℝ, r < Rb → ∃ C : ℝ, ∀ x : LM,
          riemannianEDistOf gL x₀ x < ENNReal.ofReal r → metricScalarAt gL x ≤ C) := by
  have : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
    { obj := fun n =>
        { M := M n
          basepoint := y n
          metric := scaleMetric (Q n) (hQ n) (g n) } }
  have hvolX : ∀ r R : ℝ, 0 < r → r < R → R < Rb → ∀ C : ℝ, 0 ≤ C →
      ∃ a κ : ℝ, 0 < a ∧ 0 < κ ∧ r + a ≤ R ∧ a ^ 4 * C ^ 2 ≤ 1 ∧
      ∀ᶠ n in atTop, ∀ x ∈ riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint r,
        ENNReal.ofReal (κ * a ^ Module.finrank ℝ ThreeSpace) ≤
          riemannianVolumeMeasure ThreeModel (X.obj n).M (X.obj n).metric
            (riemannianBallOf (X.obj n).metric x a) := by
    simpa only [ThreeSpace, finrank_euclideanSpace, Fintype.card_fin] using hvol
  obtain ⟨f, hf, r, hr, hrlim, L, F, C, hdomain, hradial, hcompactL, hcapture, hbounds⟩ :=
    exists_pointed_convergence_with_uniform_metric_bounds_on_base_components X hRb hcompact
      hjets hvolX
  try dsimp only at hcapture hbounds
  let U := fun i => connectedComponentOpen (I := ThreeModel) (X.obj i).basepoint
  let hp := fun i => (mem_connectedComponent : (X.obj i).basepoint ∈ U i)
  let F' := F.liftTargetOpen U hp
  have hcl : ∀ R : ℝ, R < Rb → IsCompact (riemannianClosedBallOf L.metric L.basepoint R) := by
    intro R hR
    by_cases h0 : 0 ≤ R
    · exact hcompactL R h0 hR
    · have hset : riemannianClosedBallOf L.metric L.basepoint R =
          riemannianClosedBallOf L.metric L.basepoint 0 := by
        ext z
        simp only [riemannianClosedBallOf, Set.mem_ofPred_eq,
          ENNReal.ofReal_of_nonpos (le_of_lt (not_le.mp h0)), ENNReal.ofReal_zero]
      rw [hset]
      exact hcompactL 0 le_rfl hRb
  have hsrc : ∀ K : Set L.M, IsCompact K → ∀ᶠ k in atTop, K ⊆ F'.source k := by
    intro K hK
    obtain ⟨k0, hk0⟩ := F'.source_subset hK
    exact eventually_atTop.mpr ⟨k0, hk0⟩
  -- the radial comparison, with finiteness
  have hrad : ∀ K : Set L.M, IsCompact K → ∀ ε' : ℝ, 0 < ε' → ∀ᶠ k in atTop, ∀ x ∈ K,
      riemannianEDistOf (scaleMetric (Q (f k)) (hQ (f k)) (g (f k))) (y (f k))
          (F'.map k x) ≠ ⊤ ∧
        |(riemannianEDistOf (scaleMetric (Q (f k)) (hQ (f k)) (g (f k))) (y (f k))
            (F'.map k x)).toReal - (riemannianEDistOf L.metric L.basepoint x).toReal| < ε' := by
    intro K hK ε' hε'
    obtain ⟨r₁, hr₁0, hr₁, hKr⟩ :=
      exists_radius_of_compact_O59 L.metric L.basepoint hK hRb (fun x _ => hradial x)
    obtain ⟨ε, hε0, hε1, hεR, hεr⟩ :=
      exists_eps_O59 hr₁0 (by linarith : r₁ < (r₁ + Rb) / 2) hε'
    filter_upwards [hsrc _ (hcl ((r₁ + Rb) / 2) (by linarith)), hbounds ε hε0] with k hk hkb
    intro x hx
    have hxs : x ∈ F'.source k :=
      hk (le_trans (hKr x hx) (ENNReal.ofReal_le_ofReal (by linarith)))
    have hfin : riemannianEDistOf L.metric L.basepoint x ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hKr x hx)
    have hle : (riemannianEDistOf L.metric L.basepoint x).toReal ≤ r₁ := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hKr x hx)
      rwa [ENNReal.toReal_ofReal hr₁0] at this
    have key := dist_two_sided_O59 L.metric (scaleMetric (Q (f k)) (hQ (f k)) (g (f k)))
      (F'.partialDiffeomorph k) hε0 hε1 (hcl ((r₁ + Rb) / 2) (by linarith)) hk
      (fun z hz v => hkb z hz v) hxs hfin hle hεR
    have hb : (F'.partialDiffeomorph k) L.basepoint = y (f k) := F'.basepoint_map k
    rw [hb] at key
    exact ⟨key.1, lt_of_le_of_lt key.2 hεr⟩
  refine ⟨L.M, L.topology, L.charted, L.smooth, L.t2, L.sigmaCompact, L.metric, L.basepoint,
    f, hf, fun k => F'.map k, fun k => F'.source k, ⟨fun k => F'.source_open k, hsrc,
      fun k => F'.base_mem k, fun k => (F'.partialDiffeomorph k).contMDiffOn⟩,
    fun k => F'.basepoint_map k, hradial, hcl, ?_, hbounds, ?_, ?_, ?_, ?_, ?_⟩
  · -- CAPTURE
    intro R hR
    have hev : ∀ᶠ k in atTop, R < r k :=
      (tendsto_order.mp hrlim).1 R hR
    filter_upwards [hev] with k hk
    intro w hw
    have hwt : w ∈ F'.target k := by
      apply hcapture k
      exact hw.trans (ENNReal.ofReal_le_ofReal hk.le)
    exact ⟨(F'.partialDiffeomorph k).symm w,
      (F'.partialDiffeomorph k).toPartialEquiv.map_target hwt,
      (F'.partialDiffeomorph k).toPartialEquiv.right_inv hwt⟩
  · -- SCALAR
    intro K hK ε hε
    obtain ⟨k0, hk0⟩ :=
    DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalar_uniform_on_compact_of_canonical_domains C hdomain K hK ε hε
    refine eventually_atTop.mpr ⟨k0, fun k hk x hx => ?_⟩
    have h := (hk0 k hk).2 x hx
    change |metricScalarAt (scaleMetric (Q (f k)) (hQ (f k)) (g (f k))) (F'.map k x) -
      metricScalarAt L.metric x| < ε at h
    rw [metricScalarAt_scaleMetric] at h
    rwa [div_eq_inv_mul]
  · -- RADIAL
    intro K hK ε hε
    filter_upwards [hrad K hK ε hε] with k hk x hx
    exact (hk x hx).2
  · -- PAIR
    intro K hK hK3 ε' hε'
    obtain ⟨r₁, hr₁0, hr₁, hKr⟩ :=
      exists_radius_of_compact_O59 L.metric L.basepoint hK (by linarith) hK3
    set R := (r₁ + Rb) / 2 with hR_def
    set R₂ := (3 * r₁ + Rb) / 2 with hR₂_def
    obtain ⟨ε, hε0, hε1, hεR, hεr⟩ :=
      exists_eps_O59 (by linarith : 0 ≤ 2 * r₁) (by linarith : 2 * r₁ < R) hε'
    filter_upwards [hsrc _ (hcl R₂ (by linarith)), hbounds ε hε0] with k hk hkb
    intro x hx x' hx'
    have hball : riemannianClosedBallOf L.metric x R ⊆
        riemannianClosedBallOf L.metric L.basepoint R₂ :=
      riemannianClosedBallOf_subset_of_add_radius_le L.metric hr₁0 (by linarith)
        (by linarith) (hKr x hx)
    have hcpt : IsCompact (riemannianClosedBallOf L.metric x R) :=
      (hcl R₂ (by linarith)).of_isClosed_subset
        (DifferentialGeometry.Geometry.Metric.isClosed_riemannianClosedBallOf L.metric x R) hball
    have hxs' : x' ∈ F'.source k :=
      hk (le_trans (hKr x' hx') (ENNReal.ofReal_le_ofReal (by linarith)))
    have htri : riemannianEDistOf L.metric x x' ≤ ENNReal.ofReal (2 * r₁) := by
      calc riemannianEDistOf L.metric x x' ≤
            riemannianEDistOf L.metric x L.basepoint + riemannianEDistOf L.metric L.basepoint x' :=
            riemannianEDistOf_triangle _ _ _ _
        _ ≤ ENNReal.ofReal r₁ + ENNReal.ofReal r₁ := by
            rw [riemannianEDistOf_comm L.metric x L.basepoint]
            exact add_le_add (hKr x hx) (hKr x' hx')
        _ = ENNReal.ofReal (2 * r₁) := by
            rw [← ENNReal.ofReal_add hr₁0 hr₁0, two_mul]
    have hfin : riemannianEDistOf L.metric x x' ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top htri
    have hle : (riemannianEDistOf L.metric x x').toReal ≤ 2 * r₁ := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top htri
      rwa [ENNReal.toReal_ofReal (by linarith)] at this
    have key := dist_two_sided_O59 L.metric (scaleMetric (Q (f k)) (hQ (f k)) (g (f k)))
      (F'.partialDiffeomorph k) hε0 hε1 hcpt (hball.trans hk)
      (fun z hz v => hkb z hz v) hxs' hfin hle hεR
    exact lt_of_le_of_lt key.2 hεr
  · -- SEC
    intro x v w
    have hconv : ∀ K : Set L.M, IsCompact K →
        metricSourceConvergesOn (I := ThreeModel) F'
          (CanonicalMetricCompactness.canonicalSourceData F') K 2 := by
      intro K hK
      have hD : C.domain = fun n => CanonicalMetricCompactness.canonicalSourceData F' n :=
        funext hdomain
      have := C.converges K hK 2
      rwa [hD] at this
    have hlim := PDE.RicciFlow.Perelman.KappaSolutions.pointedRm04_tendsto_of_canonical_metric_convergence
      hconv x v w w v
    set d := (riemannianEDistOf L.metric L.basepoint x).toReal with hd_def
    have hfx : riemannianEDistOf L.metric L.basepoint x ≠ ⊤ := ne_top_of_lt (hradial x)
    have hdRb : d < Rb := by
      have h := hradial x
      rw [← ENNReal.ofReal_toReal hfx] at h
      exact (ENNReal.ofReal_lt_ofReal_iff hRb).mp h
    have hd0 : 0 ≤ d := ENNReal.toReal_nonneg
    have hpos : ∀ u : TangentSpace ThreeModel x, 0 ≤ L.metric.inner x u u := by
      intro u
      rcases eq_or_ne u 0 with hu | hu
      · subst hu; simp
      · exact (L.metric.pos x u hu).le
    have hgram : 0 ≤ L.metric.inner x v v * L.metric.inner x w w :=
      mul_nonneg (hpos v) (hpos w)
    have hge : ∀ η : ℝ, 0 < η →
        -(4 * η * (L.metric.inner x v v * L.metric.inner x w w)) ≤
          metricRm04StandardAt L.metric x v w w v := by
      intro η hη
      apply ge_of_tendsto hlim
      have hf' : Tendsto f atTop atTop := hf.tendsto_atTop
      filter_upwards [hrad {x} isCompact_singleton ((Rb - d) / 2) (by linarith),
        hf'.eventually (hsec ((Rb + d) / 2) (by linarith) η hη), hbounds 1 one_pos,
        hsrc {x} isCompact_singleton] with k hk hks hkb hkx
      obtain ⟨hk1, hk2⟩ := hk x (Set.mem_singleton x)
      have hxs : x ∈ F'.source k := hkx (Set.mem_singleton x)
      have hdist : riemannianEDistOf (scaleMetric (Q (f k)) (hQ (f k)) (g (f k))) (y (f k))
          (F'.map k x) < ENNReal.ofReal ((Rb + d) / 2) := by
        rw [← ENNReal.ofReal_toReal hk1]
        exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr
          (by have := (abs_lt.mp hk2).2; linarith)
      have hs := hks (F'.map k x) hdist
        (mfderiv ThreeModel ThreeModel (F'.map k) x v) (mfderiv ThreeModel ThreeModel (F'.map k) x w)
      have hv := hkb x hxs v
      have hw := hkb x hxs w
      have hsq := sq_nonneg ((scaleMetric (Q (f k)) (hQ (f k)) (g (f k))).inner (F'.map k x)
        (mfderiv ThreeModel ThreeModel (F'.map k) x v) (mfderiv ThreeModel ThreeModel (F'.map k) x w))
      have hv0 := hv.1
      have hw0 := hw.1
      have hv1 := hv.2
      have hw1 := hw.2
      norm_num at hv0 hw0 hv1 hw1
      have hprod := mul_le_mul hv1 hw1 hw0 (by linarith [hpos v])
      nlinarith [hpos v, hpos w]
    have h0 : 0 ≤ metricRm04StandardAt L.metric x v w w v := by
      apply le_of_forall_pos_le_add
      intro δ hδ
      set P := L.metric.inner x v v * L.metric.inner x w w
      have hη : 0 < δ / (4 * (P + 1)) := div_pos hδ (by linarith)
      have h1 := hge _ hη
      have h2 : 4 * (δ / (4 * (P + 1))) * P ≤ δ := by
        rw [show 4 * (δ / (4 * (P + 1))) * P = δ * (P / (P + 1)) by field_simp]
        have : P / (P + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
        nlinarith
      linarith
    rw [zero_mul]
    exact h0
  · -- SCB
    intro r₀ hr₀
    have hcont : Continuous (fun x : L.M => metricScalarAt L.metric x) :=
      (metricScalar_smooth L.metric).continuous
    obtain ⟨Cb, hCb⟩ := (hcl r₀ hr₀).exists_bound_of_continuousOn hcont.continuousOn
    refine ⟨Cb, fun x hx => ?_⟩
    have := hCb x (le_of_lt hx)
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using this)

end GC.LongTime.Ch12

end
