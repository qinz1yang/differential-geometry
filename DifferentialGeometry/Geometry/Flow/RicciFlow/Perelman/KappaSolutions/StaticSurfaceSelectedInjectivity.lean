import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.HarnackSelectedInjectivity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RescaledPointedSequence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticVolumeRatio
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceEntropyBasic
import DifferentialGeometry.Geometry.Comparison.BonnetMyers.SectionalRicci
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Manifold MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Integral.Measure
open CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance staticSelectedC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance staticSelectedMeasurable : MeasurableSpace M := borel M
private local instance staticSelectedBorel : BorelSpace M := ⟨rfl⟩

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem staticSelected_edist_comm (g : SmoothRiemannianMetric I M) (y z : M) :
    riemannianEDistOf (I := I) g y z = riemannianEDistOf (I := I) g z y := by
  let _ : RiemannianBundle (fun y : M => TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  change Manifold.riemannianEDist I y z = Manifold.riemannianEDist I z y
  exact Manifold.riemannianEDist_comm (I := I) (x := y) (y := z)

omit [I.Boundaryless] in
theorem staticScalarNormalized_rmNormSq_le
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 2)
    (hnonneg : ∀ z, 0 ≤ metricScalarAt (I := I) g z)
    (x : ℕ → M) (hQ : ∀ i, 0 < metricScalarAt (I := I) g (x i))
    (i : ℕ) (r : ℝ)
    (hlocal : ∀ z, (riemannianEDistOf (I := I) g z (x i)).toReal < r →
      metricScalarAt (I := I) g z ≤ 4 * metricScalarAt (I := I) g (x i))
    (z : M)
    (hz : (riemannianEDistOf (I := I)
      ((spatialRescaledPointedSeq g x
        (fun j => Real.sqrt (metricScalarAt (I := I) g (x j)))
        (fun j => Real.sqrt_pos.mpr (hQ j))).obj i).metric z (x i)).toReal <
      r * Real.sqrt (metricScalarAt (I := I) g (x i))) :
    Tensor0SBundle.normSq0S (I := I)
      ((spatialRescaledPointedSeq g x
        (fun j => Real.sqrt (metricScalarAt (I := I) g (x j)))
        (fun j => Real.sqrt_pos.mpr (hQ j))).obj i).metric z 4
      (metricRm04At (I := I)
        ((spatialRescaledPointedSeq g x
          (fun j => Real.sqrt (metricScalarAt (I := I) g (x j)))
          (fun j => Real.sqrt_pos.mpr (hQ j))).obj i).metric z) ≤ 16 := by
  rw [spatialRescaledPointedSeq_dist, mul_comm r] at hz
  have hz0 := (mul_lt_mul_iff_right₀ (Real.sqrt_pos.mpr (hQ i))).mp hz
  have hscalar := hlocal z hz0
  rw [metricRm_normSq_eq_scalar_sq_of_finrank_two _ hdim]
  change metricScalarAt (I := I)
    (scaleMetric (Real.sqrt (metricScalarAt (I := I) g (x i)) ^ 2)
      (sq_pos_of_pos (Real.sqrt_pos.mpr (hQ i))) g) z ^ 2 ≤ 16
  rw [metricScalarAt_scaleMetric, Real.sq_sqrt (hQ i).le]
  have hlo : 0 ≤ (metricScalarAt (I := I) g (x i))⁻¹ * metricScalarAt (I := I) g z :=
    mul_nonneg (inv_nonneg.mpr (hQ i).le) (hnonneg z)
  have hhi : (metricScalarAt (I := I) g (x i))⁻¹ * metricScalarAt (I := I) g z ≤ 4 := by
    rw [← div_eq_inv_mul]
    exact (div_le_iff₀ (hQ i)).mpr (by nlinarith)
  nlinarith

omit [I.Boundaryless] in
theorem staticScalarNormalized_smallBall_volume
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 2)
    (hnonneg : ∀ z, 0 ≤ metricScalarAt (I := I) g z)
    (kappa : ℝ)
    (hnc : ∀ (p : M) (rho : ℝ), 0 < rho →
      (∀ z ∈ riemannianBallOf (I := I) g p rho,
        rho ^ 4 * Tensor0SBundle.normSq0S (I := I) g z 4
          (metricRm04At (I := I) g z) ≤ 1) →
      ENNReal.ofReal kappa * ENNReal.ofReal rho ^ Module.finrank ℝ E ≤
        riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf (I := I) g p rho))
    (x : ℕ → M) (hQ : ∀ i, 0 < metricScalarAt (I := I) g (x i))
    (i : ℕ) (r : ℝ)
    (hlocal : ∀ z, (riemannianEDistOf (I := I) g z (x i)).toReal < r →
      metricScalarAt (I := I) g z ≤ 4 * metricScalarAt (I := I) g (x i))
    (hlarge : 1 / 2 < r * Real.sqrt (metricScalarAt (I := I) g (x i)))
    {s : ℝ} (hs : 0 < s) (hsHalf : s ≤ 1 / 2) :
    ENNReal.ofReal kappa * ENNReal.ofReal s ^ Module.finrank ℝ E ≤
      riemannianVolumeMeasure (I := I) (M := M)
        ((spatialRescaledPointedSeq g x
          (fun j => Real.sqrt (metricScalarAt (I := I) g (x j)))
          (fun j => Real.sqrt_pos.mpr (hQ j))).obj i).metric
        (riemannianBallOf (I := I)
          ((spatialRescaledPointedSeq g x
            (fun j => Real.sqrt (metricScalarAt (I := I) g (x j)))
            (fun j => Real.sqrt_pos.mpr (hQ j))).obj i).metric (x i) s) := by
  let Q := metricScalarAt (I := I) g (x i)
  let a := Real.sqrt Q
  let u := s / a
  have hQpos : 0 < Q := hQ i
  have ha : 0 < a := Real.sqrt_pos.mpr hQpos
  have hu : 0 < u := div_pos hs ha
  have hur : u < r := (div_lt_iff₀ ha).mpr (hsHalf.trans_lt hlarge)
  have hcontrol : ∀ z ∈ riemannianBallOf (I := I) g (x i) u,
      u ^ 4 * Tensor0SBundle.normSq0S (I := I) g z 4
        (metricRm04At (I := I) g z) ≤ 1 := by
    intro z hz
    have hdist : (riemannianEDistOf (I := I) g z (x i)).toReal < u := by
      rw [staticSelected_edist_comm]
      exact ENNReal.toReal_lt_of_lt_ofReal hz
    have hR := hlocal z (hdist.trans hur)
    have hR0 := hnonneg z
    have hsq : metricScalarAt (I := I) g z ^ 2 ≤ 16 * Q ^ 2 := by
      dsimp [Q]
      nlinarith
    have ha4 : a ^ 4 = Q ^ 2 := by
      calc
        a ^ 4 = (a ^ 2) ^ 2 := by ring
        _ = Q ^ 2 := by rw [Real.sq_sqrt hQpos.le]
    have hcancel : u ^ 4 * (16 * Q ^ 2) = 16 * s ^ 4 := by
      dsimp [u]
      rw [div_pow, ha4]
      field_simp [hQpos.ne']
    have hmul := mul_le_mul_of_nonneg_left hsq (pow_nonneg hu.le 4)
    rw [hcancel] at hmul
    have hpow := pow_le_pow_left₀ hs.le hsHalf 4
    rw [metricRm_normSq_eq_scalar_sq_of_finrank_two g hdim]
    nlinarith
  have hvol := hnc (x i) u hu hcontrol
  have hau : a * u = s := by dsimp [u]; field_simp
  have hball : riemannianBallOf (I := I) (scaleMetric (a ^ 2) (sq_pos_of_pos ha) g)
      (x i) s = riemannianBallOf (I := I) g (x i) u := by
    have h := riemannianBallOf_scaleMetric g (a ^ 2) (sq_pos_of_pos ha) (x i) u
    rw [Real.sqrt_sq ha.le, hau] at h
    exact h
  change ENNReal.ofReal kappa * ENNReal.ofReal s ^ Module.finrank ℝ E ≤
    riemannianVolumeMeasure (I := I) (M := M) (scaleMetric (a ^ 2) (sq_pos_of_pos ha) g)
      (riemannianBallOf (I := I) (scaleMetric (a ^ 2) (sq_pos_of_pos ha) g) (x i) s)
  rw [hball, volume_scale_apply, Real.sqrt_sq ha.le]
  have hprod : ENNReal.ofReal s = ENNReal.ofReal a * ENNReal.ofReal u := by
    rw [← ENNReal.ofReal_mul ha.le, hau]
  calc
    ENNReal.ofReal kappa * ENNReal.ofReal s ^ Module.finrank ℝ E =
        ENNReal.ofReal a ^ Module.finrank ℝ E *
          (ENNReal.ofReal kappa * ENNReal.ofReal u ^ Module.finrank ℝ E) := by
      rw [hprod, mul_pow]
      ac_rfl
    _ ≤ _ := mul_le_mul_right hvol _

variable [NeZero (Module.finrank ℝ E)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def staticScalarNormalized_baseInjBound [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 2)
    (hnonneg : ∀ z, 0 ≤ metricScalarAt (I := I) g z)
    (hsec : ∀ z, metricRm04At (I := I) g z ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (kappa : ℝ) (hkappa : 0 < kappa)
    (hnc : ∀ (p : M) (rho : ℝ), 0 < rho →
      (∀ z ∈ riemannianBallOf (I := I) g p rho,
        rho ^ 4 * Tensor0SBundle.normSq0S (I := I) g z 4
          (metricRm04At (I := I) g z) ≤ 1) →
      ENNReal.ofReal kappa * ENNReal.ofReal rho ^ Module.finrank ℝ E ≤
        riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf (I := I) g p rho))
    (x : ℕ → M) (r : ℕ → ℝ) (hQ : ∀ i, 0 < metricScalarAt (I := I) g (x i))
    (hlocal : ∀ i z, (riemannianEDistOf (I := I) g z (x i)).toReal < r i →
      metricScalarAt (I := I) g z ≤ 4 * metricScalarAt (I := I) g (x i))
    (hlarge : ∀ i, 1 / 2 < r i * Real.sqrt (metricScalarAt (I := I) g (x i))) :
    BaseInjBound (I := I)
      (spatialRescaledPointedSeq g x
        (fun i => Real.sqrt (metricScalarAt (I := I) g (x i)))
        (fun i => Real.sqrt_pos.mpr (hQ i))) := by
  classical
  let hscale := exists_uniform_local_jacobi_scale
    (Module.finrank ℝ E) (R := (1 / 2 : ℝ)) (K := 4) (by norm_num) (by norm_num)
  let rJ : ℝ := hscale.choose
  have hrJ : 0 < rJ := hscale.choose_spec.1
  have hrJHalf : rJ ≤ 1 / 2 := hscale.choose_spec.2.1
  have herror := hscale.choose_spec.2.2
  let R : ℝ := min rJ (Real.pi / Real.sqrt 4)
  have hR : 0 < R := lt_min hrJ (div_pos Real.pi_pos (by positivity))
  have hRj : R ≤ rJ := min_le_left _ _
  have hRHalf : R ≤ 1 / 2 := hRj.trans hrJHalf
  have hRpi : R ≤ Real.pi / Real.sqrt 4 := min_le_right _ _
  have hs : 0 < R / 8 := by positivity
  have hsHalf : R / 8 ≤ 1 / 2 := by linarith
  have hη : 0 < selectedCGTInjRadius E kappa R :=
    selectedCGTInjRadius_pos (E := E) hkappa hR
  let Y := spatialRescaledPointedSeq g x
    (fun i => Real.sqrt (metricScalarAt (I := I) g (x i)))
    (fun i => Real.sqrt_pos.mpr (hQ i))
  have hconn : ConnectedSpace M := inferInstance
  refine { ρ := selectedCGTInjRadius E kappa R, pos := hη, bound := ?_ }
  intro i
  refine ⟨hη, ?_⟩
  intro hcomplete
  let _ : TopologicalSpace (Y.obj i).M := (Y.obj i).topology
  let _ : ChartedSpace H (Y.obj i).M := (Y.obj i).charted
  let _ : IsManifold I ∞ (Y.obj i).M := (Y.obj i).smooth
  let _ : IsManifold I 1 (Y.obj i).M :=
    IsManifold.of_le (I := I) (M := (Y.obj i).M) (n := ∞) (by decide)
  let _ : T2Space (Y.obj i).M := (Y.obj i).t2
  let _ : SigmaCompactSpace (Y.obj i).M := (Y.obj i).sigmaCompact
  let _ : T2Space (TangentBundle I (Y.obj i).M) := (Y.obj i).t2TangentBundle
  let _ : RiemannianBundle (fun y : (Y.obj i).M => TangentSpace I y) :=
    (Y.obj i).riemBundle (I := I)
  let _ : (y : (Y.obj i).M) → InnerProductSpace ℝ (TangentSpace I y) :=
    (Y.obj i).riemInner (I := I)
  let _ : IsContinuousRiemannianBundle E (fun y : (Y.obj i).M => TangentSpace I y) :=
    (Y.obj i).riemBundle_cont (I := I)
  let _ : EMetricSpace (Y.obj i).M := (Y.obj i).emetricSpace (I := I)
  have : IsRiemannianManifold I (Y.obj i).M := ⟨fun _ _ => rfl⟩
  let _ : CompleteSpace (Y.obj i).M := MetricComplete.complete (I := I) (Y.obj i) hcomplete
  let _ : ConnectedSpace (Y.obj i).M := hconn
  let hEnorm : IsMetricNorm (I := I) (Y.obj i).metric := by
    intro y v
    with_unfolding_all
      exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) (Y.obj i).metric y v
  have hRm : ∀ y : (Y.obj i).M,
      riemannianEDist I (Y.obj i).basepoint y < ENNReal.ofReal (1 / 2) →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) (Y.obj i).metric y 4
        (metricRm04At (I := I) (Y.obj i).metric y)) ≤ 4 := by
    intro y hy
    have hyOf : riemannianEDistOf (I := I) (Y.obj i).metric (Y.obj i).basepoint y <
        ENNReal.ofReal (1 / 2) := by
      rw [riemannianEDistOf_eq_riemannianEDist (I := I) (Y.obj i).metric hEnorm]
      exact hy
    have hyreal : (riemannianEDistOf (I := I) (Y.obj i).metric y (x i)).toReal <
        r i * Real.sqrt (metricScalarAt (I := I) g (x i)) := by
      rw [staticSelected_edist_comm]
      exact (ENNReal.toReal_lt_of_lt_ofReal hyOf).trans (hlarge i)
    have hsq := staticScalarNormalized_rmNormSq_le g hdim hnonneg x hQ i (r i)
      (hlocal i) y hyreal
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have hfour : (4 : ℝ) ^ 2 = 16 := by norm_num
    rw [hfour]
    exact hsq
  have hRic : RicciBoundedBelow (I := I) (Y.obj i).metric
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (0 : ℝ) ^ 2)) := by
    intro y v
    have hscaled : metricRm04At (I := I) (Y.obj i).metric y ∈
        tensor04SectionalNonnegativeCone (I := I) := by
      apply (metricRm04At_mem_tensor04SectionalNonnegativeCone_iff (I := I) _ y).mpr
      intro a b
      change 0 ≤ metricRm04StandardAt (I := I)
        (scaleMetric (Real.sqrt (metricScalarAt (I := I) g (x i)) ^ 2)
          (sq_pos_of_pos (Real.sqrt_pos.mpr (hQ i))) g) y a b b a
      rw [metricRmStandard_scale]
      exact mul_nonneg (sq_nonneg _)
        (((metricRm04At_mem_tensor04SectionalNonnegativeCone_iff (I := I) g y).mp
          (hsec y)) a b)
    have h := ricci_nonneg_of_sec (Y.obj i).metric y hscaled v
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, neg_zero, zero_mul] using h
  have hvolOf := staticScalarNormalized_smallBall_volume
    g hdim hnonneg kappa hnc x hQ i (r i) (hlocal i) (hlarge i) hs hsHalf
  have hvol : ENNReal.ofReal kappa * ENNReal.ofReal (R / 8) ^ Module.finrank ℝ E ≤
      riemannianVolumeMeasure (I := I) (M := (Y.obj i).M) (Y.obj i).metric
        {y : (Y.obj i).M | riemannianEDist I (Y.obj i).basepoint y <
          ENNReal.ofReal (R / 8)} := by
    change ENNReal.ofReal kappa * ENNReal.ofReal (R / 8) ^ Module.finrank ℝ E ≤
      riemannianVolumeMeasure (I := I) (M := (Y.obj i).M) (Y.obj i).metric
        {y : (Y.obj i).M | riemannianEDistOf (I := I) (Y.obj i).metric
          (Y.obj i).basepoint y < ENNReal.ofReal (R / 8)} at hvolOf
    simpa only [riemannianEDistOf_eq_riemannianEDist (I := I) (Y.obj i).metric hEnorm]
      using hvolOf
  have hcgt := intrInj_ge_vol_of_ball (I := I) (Y.obj i).metric hEnorm
    (Y.obj i).basepoint (K := 4) (ρ := (1 / 2 : ℝ)) (R := R)
    (by norm_num) hR hRHalf hRpi hRm
    (fun a ha haR => herror a ha (haR.trans hRj))
    (r₀ := R / 8) (s := R / 8) hs hs (by linarith) (by linarith)
    (q := 0) (by norm_num) hRic hvol
  have hhalf : R / 8 / 2 = R / 16 := by ring
  have hadd : R / 8 + R / 8 = R / 4 := by ring
  rw [hhalf, hadd] at hcgt
  have hinj := (selectedCGTInjRadius_le_quotient (E := E) hkappa.le hR).trans hcgt
  simpa only [Y, PointedRiemannianManifold.intrinsicInjRadius] using hinj


theorem exists_static_surface_blowup_with_baseInjBound [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g)
    (hdim : Module.finrank ℝ E = 2)
    (hnonneg : ∀ z, 0 ≤ metricScalarAt (I := I) g z)
    (hsec : ∀ z, metricRm04At (I := I) g z ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (kappa : ℝ) (hkappa : 0 < kappa)
    (hnc : ∀ (p : M) (rho : ℝ), 0 < rho →
      (∀ z ∈ riemannianBallOf (I := I) g p rho,
        rho ^ 4 * Tensor0SBundle.normSq0S (I := I) g z 4
          (metricRm04At (I := I) g z) ≤ 1) →
      ENNReal.ofReal kappa * ENNReal.ofReal rho ^ Module.finrank ℝ E ≤
        riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf (I := I) g p rho))
    (hunbounded : ¬ BddAbove (Set.range (metricScalarAt (I := I) g))) (p : M) :
    ∃ (x : ℕ → M) (r : ℕ → ℝ) (hQ : ∀ i, 0 < metricScalarAt (I := I) g (x i)),
      (∀ i, 0 < r i ∧ r i ≤ 1 / 2) ∧
      Tendsto (fun i => metricScalarAt (I := I) g (x i)) atTop atTop ∧
      Tendsto (fun i => r i * Real.sqrt (metricScalarAt (I := I) g (x i))) atTop atTop ∧
      Tendsto (fun i => (riemannianEDistOf (I := I) g p (x i)).toReal) atTop atTop ∧
      Tendsto (fun i => Real.sqrt (metricScalarAt (I := I) g (x i)) *
        (riemannianEDistOf (I := I) g p (x i)).toReal) atTop atTop ∧
      (∀ i z, (riemannianEDistOf (I := I) g z (x i)).toReal < r i →
        metricScalarAt (I := I) g z ≤ 4 * metricScalarAt (I := I) g (x i)) ∧
      Nonempty (BaseInjBound (I := I)
        (spatialRescaledPointedSeq g x
          (fun i => Real.sqrt (metricScalarAt (I := I) g (x i)))
          (fun i => Real.sqrt_pos.mpr (hQ i)))) ∧
      (∀ i, metricScalarAt (I := I)
        ((spatialRescaledPointedSeq g x
          (fun j => Real.sqrt (metricScalarAt (I := I) g (x j)))
          (fun j => Real.sqrt_pos.mpr (hQ j))).obj i).metric (x i) = 1) := by
  obtain ⟨x, r, hr, hQescape, hQr, hdist, _hratio, hlocal⟩ :=
    exists_scalarSpatialPointSelection g hg hnonneg hunbounded p
  let hQ : ∀ i, 0 < metricScalarAt (I := I) g (x i) := fun i => (hr i).2.2
  have hsqrt : Tendsto (fun i => Real.sqrt (metricScalarAt (I := I) g (x i)))
      atTop atTop := Real.tendsto_sqrt_atTop.comp hQescape
  have hexpand : Tendsto (fun i => r i * Real.sqrt (metricScalarAt (I := I) g (x i)))
      atTop atTop := by
    have h : Tendsto (fun i => Real.sqrt (metricScalarAt (I := I) g (x i) * r i ^ 2))
        atTop atTop := Real.tendsto_sqrt_atTop.comp hQr
    have heq : (fun i => Real.sqrt (metricScalarAt (I := I) g (x i) * r i ^ 2)) =
        (fun i => r i * Real.sqrt (metricScalarAt (I := I) g (x i))) := by
      funext i
      rw [Real.sqrt_mul (hQ i).le, Real.sqrt_sq (hr i).1.le, mul_comm]
    rw [heq] at h
    exact h
  have hscaled := hsqrt.atTop_mul_atTop₀ hdist
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hexpand (eventually_gt_atTop (1 / 2)))
  have hshift : Tendsto (fun i : ℕ => N + i) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat N
  refine ⟨(fun i => x (N + i)), (fun i => r (N + i)), (fun i => hQ (N + i)),
    (fun i => ⟨(hr (N + i)).1, (hr (N + i)).2.1⟩), ?_, ?_, ?_, ?_,
    (fun i => hlocal (N + i)), ?_, ?_⟩
  · simpa only [Function.comp_def] using hQescape.comp hshift
  · simpa only [Function.comp_def] using hexpand.comp hshift
  · simpa only [Function.comp_def] using hdist.comp hshift
  · simpa only [Function.comp_def] using hscaled.comp hshift
  · exact ⟨staticScalarNormalized_baseInjBound g hdim hnonneg hsec kappa hkappa hnc
      (fun i => x (N + i)) (fun i => r (N + i)) (fun i => hQ (N + i))
      (fun i => hlocal (N + i)) (fun i => hN (N + i) (Nat.le_add_right N i))⟩
  · intro i
    change metricScalarAt (I := I)
      (scaleMetric (Real.sqrt (metricScalarAt (I := I) g (x (N + i))) ^ 2)
        (sq_pos_of_pos (Real.sqrt_pos.mpr (hQ (N + i)))) g) (x (N + i)) = 1
    rw [metricScalarAt_scaleMetric, Real.sq_sqrt (hQ (N + i)).le]
    exact inv_mul_cancel₀ (hQ (N + i)).ne'

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
