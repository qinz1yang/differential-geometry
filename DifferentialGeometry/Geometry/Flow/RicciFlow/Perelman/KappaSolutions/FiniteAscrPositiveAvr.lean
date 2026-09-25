import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticScalarDecay
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticVolumeRatio
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NonnegativeCurvatureScalarNorm
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle _root_.Manifold Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor0SBundle
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff ENNReal

private theorem finiteAscr_alpha_bounds {C B : ℝ} (hC : 0 < C) (hB : 0 < B) :
    let a := min (1 / 2 : ℝ) (1 / (2 * Real.sqrt (C * B)))
    0 < a ∧ a ≤ 1 / 2 ∧ 4 * a ^ 2 * C * B ≤ 1 := by
  let a := min (1 / 2 : ℝ) (1 / (2 * Real.sqrt (C * B)))
  have hs : 0 < Real.sqrt (C * B) := Real.sqrt_pos.mpr (mul_pos hC hB)
  have ha : 0 < a := lt_min (by norm_num) (div_pos zero_lt_one (by positivity))
  have hhalf : a ≤ 1 / 2 := min_le_left _ _
  have hsmall : a ≤ 1 / (2 * Real.sqrt (C * B)) := min_le_right _ _
  have hmul : a * (2 * Real.sqrt (C * B)) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp hsmall
  have hsquare := (sq_le_sq₀ (mul_nonneg ha.le (by positivity)) zero_le_one).mpr hmul
  have hsqrt := Real.sq_sqrt (mul_pos hC hB).le
  refine ⟨ha, hhalf, ?_⟩
  calc
    4 * a ^ 2 * C * B = (a * (2 * Real.sqrt (C * B))) ^ 2 := by
      rw [mul_pow, mul_pow, hsqrt]
      ring
    _ ≤ 1 := by simpa only [one_pow] using hsquare

private theorem finiteAscr_normalized_lower_identity
    (n : ℕ) (kappa a D : ℝ) (ha : 0 < a) (hD : 0 < D) :
    (ENNReal.ofReal kappa * ENNReal.ofReal (a * D) ^ n) /
        (euclideanUnitBallVolume n * ENNReal.ofReal (((1 + a) * D) ^ n)) =
      (ENNReal.ofReal kappa / euclideanUnitBallVolume n) *
        ENNReal.ofReal (a / (1 + a)) ^ n := by
  have hb : 0 < 1 + a := by positivity
  rw [← ENNReal.ofReal_pow (mul_pos ha hD).le]
  rw [ENNReal.mul_div_mul_comm
    (Or.inl (euclideanUnitBallVolume_pos n).ne')
    (Or.inl (euclideanUnitBallVolume_ne_top n))]
  rw [← ENNReal.ofReal_div_of_pos (pow_pos (mul_pos hb hD) n)]
  rw [← div_pow, mul_div_mul_right a (1 + a) hD.ne',
    ENNReal.ofReal_pow (div_pos ha hb).le]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance finiteAscrMeasurable : MeasurableSpace M := borel M
private local instance finiteAscrBorel : BorelSpace M := ⟨rfl⟩
private local instance finiteAscrC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

section Distance

variable [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional ℝ E] in
private theorem finiteAscr_edist_ne_top (g : SmoothRiemannianMetric I M) (p x : M) :
    riemannianEDistOf g p x ≠ ⊤ := by
  let _ : RiemannianBundle (fun y : M => TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro y v w; rfl⟩⟩
  exact riemannianEDist_ne_top (I := I) p x

omit [FiniteDimensional ℝ E] in
private theorem finiteAscr_mem_ball_iff (g : SmoothRiemannianMetric I M)
    (p x : M) (r : ℝ) :
    x ∈ riemannianBallOf g p r ↔ (riemannianEDistOf g p x).toReal < r := by
  change riemannianEDistOf g p x < ENNReal.ofReal r ↔ _
  constructor
  · exact ENNReal.toReal_lt_of_lt_ofReal
  · intro hx
    rw [← ENNReal.ofReal_toReal (finiteAscr_edist_ne_top g p x)]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).mpr hx

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional ℝ E] in
private theorem finiteAscr_distance_triangle (g : SmoothRiemannianMetric I M)
    (p q x : M) :
    (riemannianEDistOf g p x).toReal ≤
      (riemannianEDistOf g p q).toReal + (riemannianEDistOf g q x).toReal := by
  let _ : RiemannianBundle (fun y : M => TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro y v w; rfl⟩⟩
  change (riemannianEDist I p x).toReal ≤
    (riemannianEDist I p q).toReal + (riemannianEDist I q x).toReal
  have h := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨riemannianEDist_ne_top (I := I) p q,
      riemannianEDist_ne_top (I := I) q x⟩)
    (riemannianEDist_triangle (I := I) (x := p) (y := q) (z := x))
  simpa only [ENNReal.toReal_add (riemannianEDist_ne_top (I := I) p q)
    (riemannianEDist_ne_top (I := I) q x)] using h

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [ConnectedSpace M] [FiniteDimensional ℝ E] in
private theorem finiteAscr_distance_comm (g : SmoothRiemannianMetric I M) (p x : M) :
    (riemannianEDistOf g p x).toReal = (riemannianEDistOf g x p).toReal := by
  let _ : RiemannianBundle (fun y : M => TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  exact congrArg ENNReal.toReal (Manifold.riemannianEDist_comm (I := I) (x := p) (y := x))

end Distance

variable [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)]
  [ConnectedSpace M] [NoncompactSpace M]

private theorem finiteAscr_exists_far_point
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    (p : M) (r : ℝ) : ∃ x : M, r < (riemannianEDistOf g p x).toReal := by
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem _).mp
    (hcomplete.closedEBall_isCompact p r).ne_univ
  refine ⟨x, lt_of_not_ge ?_⟩
  intro hle
  apply hx
  change riemannianEDistOf g p x ≤ ENNReal.ofReal r
  rw [← ENNReal.ofReal_toReal (finiteAscr_edist_ne_top g p x)]
  exact ENNReal.ofReal_le_ofReal hle

theorem finite_ascr_positive_avr
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    (hoperator : ∀ x : M, metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (kappa : ℝ) (hkappa : 0 < kappa)
    (hnoncollapse : ∀ (x : M) (r : ℝ), 0 < r →
      (∀ y ∈ riemannianBallOf (I := I) g x r,
        r ^ 4 * normSq0S (I := I) g y 4 (metricRm04At (I := I) g y) ≤ 1) →
      ENNReal.ofReal kappa * ENNReal.ofReal r ^ Module.finrank ℝ E ≤
        riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g x r))
    (p : M) (hfinite : asymptoticScalarCurvatureRatio g p ≠ ⊤) :
    let A := (asymptoticScalarCurvatureRatio g p).toReal
    let C := (Module.finrank ℝ E : ℝ) ^ 2
    let alpha := min (1 / 2 : ℝ) (1 / (2 * Real.sqrt (C * (A + 1))))
    0 < alpha ∧
      (ENNReal.ofReal kappa / euclideanUnitBallVolume (Module.finrank ℝ E)) *
          ENNReal.ofReal (alpha / (1 + alpha)) ^ Module.finrank ℝ E ≤
        asymptoticVolumeRatio g p ∧
      0 < (ENNReal.ofReal kappa / euclideanUnitBallVolume (Module.finrank ℝ E)) *
        ENNReal.ofReal (alpha / (1 + alpha)) ^ Module.finrank ℝ E ∧
      0 < asymptoticVolumeRatio g p := by
  let A := (asymptoticScalarCurvatureRatio g p).toReal
  let C := (Module.finrank ℝ E : ℝ) ^ 2
  let alpha := min (1 / 2 : ℝ) (1 / (2 * Real.sqrt (C * (A + 1))))
  let L : ℝ≥0∞ :=
    (ENNReal.ofReal kappa / euclideanUnitBallVolume (Module.finrank ℝ E)) *
      ENNReal.ofReal (alpha / (1 + alpha)) ^ Module.finrank ℝ E
  change 0 < alpha ∧ L ≤ asymptoticVolumeRatio g p ∧ 0 < L ∧
    0 < asymptoticVolumeRatio g p
  have hn : 0 < (Module.finrank ℝ E : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne _))
  have hC : 0 < C := sq_pos_of_pos hn
  have hA : 0 ≤ A := ENNReal.toReal_nonneg
  obtain ⟨ha, hhalf, hscale⟩ := finiteAscr_alpha_bounds hC
    (by linarith : 0 < A + 1)
  change 0 < alpha at ha
  change alpha ≤ 1 / 2 at hhalf
  change 4 * alpha ^ 2 * C * (A + 1) ≤ 1 at hscale
  have hb : 0 < 1 + alpha := by positivity
  have hL : 0 < L := ENNReal.mul_pos_iff.mpr
    ⟨ENNReal.div_pos_iff.mpr ⟨(ENNReal.ofReal_pos.mpr hkappa).ne',
      euclideanUnitBallVolume_ne_top _⟩,
      ENNReal.pow_pos (ENNReal.ofReal_pos.mpr (div_pos ha hb)) _⟩
  have hRic : RicciBoundedBelow (I := I) g 0 := by
    intro x v
    rw [zero_mul, ← metricRicciAt_apply_eq_ricciTensor]
    exact metricRicciAt_nonnegative_of_curvatureOperator_nonnegative g x (hoperator x) v
  obtain ⟨rho, hrho, htail⟩ := exists_scalar_distance_tail_bound_of_ascr_ne_top g p hfinite
  have hbound : L ≤ asymptoticVolumeRatio g p := by
    refine le_iInf fun r => le_iInf fun hr => ?_
    obtain ⟨x, hx⟩ := finiteAscr_exists_far_point g hcomplete p (2 * rho + r + 1)
    let D := (riemannianEDistOf g p x).toReal
    change 2 * rho + r + 1 < D at hx
    have hD : 0 < D := by linarith
    have hrhoD : 2 * rho ≤ D := by linarith
    have hrD : r ≤ D := by linarith
    have hrad : 0 < alpha * D := mul_pos ha hD
    have houter : 0 < (1 + alpha) * D := mul_pos hb hD
    have hrout : r ≤ (1 + alpha) * D := by nlinarith
    have hcurvature : ∀ y ∈ riemannianBallOf g x (alpha * D),
        (alpha * D) ^ 4 * normSq0S (I := I) g y 4 (metricRm04At (I := I) g y) ≤ 1 := by
      intro y hy
      let d := (riemannianEDistOf g p y).toReal
      have hd : 0 ≤ d := ENNReal.toReal_nonneg
      have hxy := (finiteAscr_mem_ball_iff g x y (alpha * D)).mp hy
      have htriangle := finiteAscr_distance_triangle g p y x
      rw [finiteAscr_distance_comm g y x] at htriangle
      change D ≤ d + (riemannianEDistOf g x y).toReal at htriangle
      have hhalfD : alpha * D ≤ D / 2 := by nlinarith
      have hdlarge : D / 2 ≤ d := by linarith
      have htailY := htail y (by change rho ≤ d; linarith)
      change metricScalarAt (I := I) g y * d ^ 2 ≤ A + 1 at htailY
      have hscalar : 0 ≤ metricScalarAt (I := I) g y :=
        metricScalarAt_nonnegative_of_curvatureOperator_nonnegative g y (hoperator y)
      have hnorm := sqrt_metricRm_normSq_le_finrank_sq_mul_scalar g y (hoperator y)
      change Real.sqrt (normSq0S (I := I) g y 4 (metricRm04At (I := I) g y)) ≤
        C * metricScalarAt (I := I) g y at hnorm
      have hDsq : D ^ 2 ≤ 4 * d ^ 2 := by
        calc
          D ^ 2 ≤ (2 * d) ^ 2 :=
            (sq_le_sq₀ hD.le (by positivity)).mpr (by linarith)
          _ = 4 * d ^ 2 := by ring
      have hroot : (alpha * D) ^ 2 *
          Real.sqrt (normSq0S (I := I) g y 4 (metricRm04At (I := I) g y)) ≤ 1 := by
        calc
          _ ≤ (alpha * D) ^ 2 * (C * metricScalarAt (I := I) g y) :=
            mul_le_mul_of_nonneg_left hnorm (sq_nonneg _)
          _ = (alpha ^ 2 * C * metricScalarAt (I := I) g y) * D ^ 2 := by ring
          _ ≤ (alpha ^ 2 * C * metricScalarAt (I := I) g y) * (4 * d ^ 2) :=
            mul_le_mul_of_nonneg_left hDsq (by positivity)
          _ = (4 * alpha ^ 2 * C) * (metricScalarAt (I := I) g y * d ^ 2) := by ring
          _ ≤ (4 * alpha ^ 2 * C) * (A + 1) :=
            mul_le_mul_of_nonneg_left htailY (by positivity)
          _ ≤ 1 := hscale
      have hnormnonneg := normSq0S_nonneg (I := I) g y 4 (metricRm04At (I := I) g y)
      have hrootsq := (sq_le_sq₀
        (mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)) zero_le_one).mpr hroot
      calc
        _ = ((alpha * D) ^ 2 *
            Real.sqrt (normSq0S (I := I) g y 4 (metricRm04At (I := I) g y))) ^ 2 := by
          rw [mul_pow ((alpha * D) ^ 2)
            (Real.sqrt (normSq0S (I := I) g y 4 (metricRm04At (I := I) g y))) 2,
            Real.sq_sqrt hnormnonneg]
          ring
        _ ≤ 1 := by simpa only [one_pow] using hrootsq
    have hvol := hnoncollapse x (alpha * D) hrad hcurvature
    have hballs : riemannianBallOf g x (alpha * D) ⊆
        riemannianBallOf g p ((1 + alpha) * D) := by
      have h := riemannianBallOf_subset_add_distance g p x (alpha * D)
      change riemannianBallOf g x (alpha * D) ⊆ riemannianBallOf g p (alpha * D + D) at h
      have hradius : alpha * D + D = (1 + alpha) * D := by ring
      rw [hradius] at h
      exact h
    have houtervol := hvol.trans (measure_mono hballs)
    have hnormalized : L ≤ normalizedBallVolumeRatio g p ((1 + alpha) * D) := by
      change L ≤ riemannianVolumeMeasure (I := I) (M := M) g
        (riemannianBallOf g p ((1 + alpha) * D)) /
        (euclideanUnitBallVolume (Module.finrank ℝ E) *
          ENNReal.ofReal (((1 + alpha) * D) ^ Module.finrank ℝ E))
      calc
        L = (ENNReal.ofReal kappa * ENNReal.ofReal (alpha * D) ^ Module.finrank ℝ E) /
            (euclideanUnitBallVolume (Module.finrank ℝ E) *
              ENNReal.ofReal (((1 + alpha) * D) ^ Module.finrank ℝ E)) :=
          (finiteAscr_normalized_lower_identity (Module.finrank ℝ E) kappa alpha D ha hD).symm
        _ ≤ _ := mul_le_mul_left houtervol _
    exact hnormalized.trans
      (normalizedBallVolumeRatio_antitoneOn g hcomplete hRic p hr houter hrout)
  exact ⟨ha, hbound, hL, hL.trans_le hbound⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
