import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalConjugateRadius
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticVolumeRatio
import DifferentialGeometry.Geometry.Comparison.CheegerGromovTaylor.InjectivityRadius.VolumeLowerBound

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.Integral.Measure
open CanonicalNeighborhood
open scoped Manifold ContDiff ENNReal _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M]

private local instance flatMeasurableE : MeasurableSpace E := borel E
private local instance flatBorelE : BorelSpace E := ⟨rfl⟩
private local instance flatMeasurableM : MeasurableSpace M := borel M
private local instance flatBorelM : BorelSpace M := ⟨rfl⟩
private local instance flatIsManifoldOne : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

private lemma flat_euclidean_sphere_model (n : ℕ) (hn : 0 < n) (r : ℝ) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere univ *
        ENNReal.ofReal (hyperbolicRadialVolume 0 (n - 1) r) =
      euclideanUnitBallVolume n * ENNReal.ofReal (r ^ n) := by
  have hnreal : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
  have hncast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
    rw [Nat.cast_sub hn]
    norm_num
  rw [Measure.toSphere_apply_univ, finrank_euclideanSpace, Fintype.card_fin,
    hyperbolicRadialVolume_zero, Nat.sub_add_cancel hn, hncast,
    ENNReal.ofReal_div_of_pos hnreal, ENNReal.ofReal_natCast]
  change ((n : ℝ≥0∞) * euclideanUnitBallVolume n) *
    (ENNReal.ofReal (r ^ n) / n) = _
  calc
    _ = euclideanUnitBallVolume n *
        ((n : ℝ≥0∞) * (ENNReal.ofReal (r ^ n) / n)) := by ac_rfl
    _ = _ := by rw [ENNReal.mul_div_cancel hn0 (by simp)]

private lemma flat_model_ball_volume {r : ℝ} (hr : 0 < r) :
    (volume : Measure E) (Metric.ball (0 : E) r) =
      euclideanUnitBallVolume (Module.finrank ℝ E) *
        ENNReal.ofReal (r ^ Module.finrank ℝ E) := by
  let _ : Nontrivial E := Module.nontrivial_of_finrank_pos
    (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  let _ : Nonempty (Fin (Module.finrank ℝ E)) := Fin.pos_iff_nonempty.mp
    (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  have hunit : (volume : Measure E) (Metric.ball (0 : E) 1) =
      euclideanUnitBallVolume (Module.finrank ℝ E) := by
    simp only [euclideanUnitBallVolume, InnerProductSpace.volume_ball,
      finrank_euclideanSpace, Fintype.card_fin]
  rw [Measure.addHaar_ball_of_pos volume (0 : E) hr, hunit, mul_comm]

section Intrinsic

variable [PseudoEMetricSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

omit [T2Space (TangentBundle I M)] [ConnectedSpace M] in
private lemma flat_intrFrameMetric_diag
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hflat : ∀ y : M, Tensor0SBundle.normSq0S (I := I) g y 4
      (metricRm04At (I := I) g y) = 0) (p : M) (z v : E) :
    intrinsicFrameMetric (I := I) g hEnorm p z v v = ‖v‖ ^ 2 := by
  let u : TangentSpace I p := normalFrame (I := I) g p z
  let w : TangentSpace I p := normalFrame (I := I) g p v
  have hRm : IntrinsicRm04Bound (I := I) g hEnorm p u 0 := by
    intro t _ht
    simp only [hflat, Real.sqrt_zero, le_refl]
  have hODE := intrinsicJacobi_ode (I := I) g hEnorm p u w (le_refl 0) hRm
  obtain ⟨hupper, hlower⟩ := intrinsicJacobi_bounds (I := I) g hEnorm p u w
    (K := 0) (b := 1) (le_refl 0) zero_lt_one
    (by simpa only [mul_zero, zero_mul] using hODE)
  have hupper1 := hupper 1 (by norm_num)
  have hlower1 := hlower 1 (by norm_num)
  have hwNorm : Real.sqrt (g.inner p w w) = ‖v‖ := by
    simpa only [w] using normalFrame_sqrt (I := I) g p v
  simp only [one_mul, zero_mul, gronwallBound_ε0_δ0, add_zero, sub_zero,
    hwNorm] at hupper1 hlower1
  let q : M := intrinsicGeodesic (I := I) g hEnorm p u 1
  let J : TangentSpace I q := intrinsicJacobi (I := I) g hEnorm p u w 1
  have hsqrt : Real.sqrt (g.inner q J J) = ‖v‖ :=
    le_antisymm hupper1 hlower1
  have hnonneg : 0 ≤ g.inner q J J := by
    rcases eq_or_ne J 0 with hJ | hJ
    · simp [hJ]
    · exact (g.pos q J hJ).le
  have hmetric : intrinsicFrameMetric (I := I) g hEnorm p z v v =
      g.inner q J J := by
    rw [intrinsic_metric_jacobi (I := I) g hEnorm p z v v]
    dsimp only [q, J, u, w, intrinsicFramedExp, expMapIntrinsic]
    rw [intrinsicFrameCLM_apply]
    rfl
  calc
    _ = g.inner q J J := hmetric
    _ = Real.sqrt (g.inner q J J) ^ 2 := (Real.sq_sqrt hnonneg).symm
    _ = ‖v‖ ^ 2 := by rw [hsqrt]

omit [T2Space (TangentBundle I M)] [ConnectedSpace M] in
private lemma flat_intrFrameMetric_inner
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hflat : ∀ y : M, Tensor0SBundle.normSq0S (I := I) g y 4
      (metricRm04At (I := I) g y) = 0) (p : M) (z v w : E) :
    intrinsicFrameMetric (I := I) g hEnorm p z v w = Inner.inner ℝ v w := by
  have hsymm : intrinsicFrameMetric (I := I) g hEnorm p z w v =
      intrinsicFrameMetric (I := I) g hEnorm p z v w := by
    erw [intrinsicFrameMetric_apply, intrinsicFrameMetric_apply]
    exact g.symm _ _ _
  have hadd := flat_intrFrameMetric_diag g hEnorm hflat p z (v + w)
  simp only [map_add, add_apply] at hadd
  rw [hsymm, flat_intrFrameMetric_diag g hEnorm hflat p z v,
    flat_intrFrameMetric_diag g hEnorm hflat p z w] at hadd
  have hnorm : ‖v + w‖ ^ 2 =
      ‖v‖ ^ 2 + 2 * Inner.inner ℝ v w + ‖w‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, real_inner_add_add_self,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  rw [hnorm] at hadd
  linarith

omit [T2Space (TangentBundle I M)] [ConnectedSpace M] in
private lemma flat_intrFrame_localOn
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hflat : ∀ y : M, Tensor0SBundle.normSq0S (I := I) g y 4
      (metricRm04At (I := I) g y) = 0) (p : M) (R : ℝ) :
    IsLocalDiffeomorphOn (modelWithCornersSelf ℝ E) I ∞
      (intrinsicFramedExp (I := I) g hEnorm p) (Metric.ball (0 : E) R) := by
  apply intrinsicFrame_localOn (I := I) g hEnorm p
  intro z _hz
  exact branch_of_not_conj (I := I) g hEnorm
    (intrinsicFrame_not_conj (I := I) g hEnorm p z zero_lt_one (fun v => by
      rw [flat_intrFrameMetric_diag g hEnorm hflat p z v, one_mul]))

theorem intrInjRadius_eq_top_of_flat_volume_growth
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hflat : ∀ y : M, Tensor0SBundle.normSq0S (I := I) g y 4
      (metricRm04At (I := I) g y) = 0)
    {κ : ℝ} (hκ : 0 < κ) (p : M)
    (hvol : ∀ s : ℝ, 0 < s → ENNReal.ofReal (κ * s ^ Module.finrank ℝ E) ≤
      riemannianVolumeMeasure (I := I) (M := M) g
        {y : M | riemannianEDist I p y < ENNReal.ofReal s}) :
    intrinsicInjRadius (I := I) g hEnorm p = ⊤ := by
  let n : ℕ := Module.finrank ℝ E
  let omega : ℝ := (euclideanUnitBallVolume n).toReal
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have homega : 0 < omega := ENNReal.toReal_pos
    (euclideanUnitBallVolume_pos n).ne' (euclideanUnitBallVolume_ne_top n)
  have homegaeq : euclideanUnitBallVolume n = ENNReal.ofReal omega :=
    (ENNReal.ofReal_toReal (euclideanUnitBallVolume_ne_top n)).symm
  let c : ℝ := κ / (2 * omega * (1 + 2 ^ n))
  have hc : 0 < c := by dsimp only [c]; positivity
  have hRic : RicciBoundedBelow (I := I) g 0 := by
    have h := ricciLower_of_rm (I := I) g (Rm := 0)
      (fun y => by simp only [hflat, Real.sqrt_zero, le_refl])
    simpa only [mul_zero, neg_zero] using h
  have hbound : ∀ s : ℝ, 0 < s → ENNReal.ofReal (c * s) ≤
      intrinsicInjRadius (I := I) g hEnorm p := by
    intro s hs
    have hR : 0 < 8 * s := by positivity
    have hK : 0 < (1 / (8 * s)) ^ 2 := by positivity
    have hRpi : 8 * s ≤ Real.pi / Real.sqrt ((1 / (8 * s)) ^ 2) := by
      rw [Real.sqrt_sq (div_nonneg zero_le_one hR.le)]
      apply (le_div_iff₀ (div_pos zero_lt_one hR)).2
      have hprod : (8 * s) * (1 / (8 * s)) = 1 := by field_simp [hs.ne']
      rw [hprod]
      linarith [Real.one_le_pi_div_two]
    have hCGT := intrinsicInj_ge_vol (I := I) g hEnorm p
      (K := (1 / (8 * s)) ^ 2) (R := 8 * s) (r₀ := s) (s := s) (q := 0)
      (v := ENNReal.ofReal (κ * s ^ n)) hK hR hRpi
      (fun y _hy => by simpa only [hflat, Real.sqrt_zero] using hK.le)
      (flat_intrFrame_localOn g hEnorm hflat p (8 * s)) hs hs
      (by linarith) (by linarith) (le_refl 0)
      (by simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero, neg_zero] using hRic)
      (hvol s hs)
    have hden :
        (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere univ *
            ENNReal.ofReal (hyperbolicRadialVolume 0 (n - 1) s) +
          (volume : Measure E).toSphere univ *
            ENNReal.ofReal (hyperbolicRadialVolume 0 (n - 1) (s + s)) =
        ENNReal.ofReal (omega * (1 + 2 ^ n) * s ^ n) := by
      rw [volSphere_finrank (E := E), flat_euclidean_sphere_model n hn s,
        flat_euclidean_sphere_model n hn (s + s), homegaeq,
        ← ENNReal.ofReal_mul homega.le, ← ENNReal.ofReal_mul homega.le,
        ← ENNReal.ofReal_add (mul_nonneg homega.le (pow_nonneg hs.le n))
          (mul_nonneg homega.le (pow_nonneg (add_nonneg hs.le hs.le) n))]
      congr 1
      rw [← two_mul s, mul_pow]
      ring
    have hdenpos : 0 < omega * (1 + (2 : ℝ) ^ n) * s ^ n := by positivity
    have hratio :
        ENNReal.ofReal (s / 2) * ENNReal.ofReal (κ * s ^ n) /
            ENNReal.ofReal (omega * (1 + 2 ^ n) * s ^ n) =
          ENNReal.ofReal (c * s) := by
      rw [← ENNReal.ofReal_mul (div_nonneg hs.le (by norm_num)),
        ← ENNReal.ofReal_div_of_pos hdenpos]
      congr 1
      apply (div_eq_iff hdenpos.ne').2
      dsimp only [c]
      have hpow : (1 + (2 : ℝ) ^ n) ≠ 0 := ne_of_gt (by positivity)
      field_simp [homega.ne', hpow]
    rw [hden, hratio] at hCGT
    exact hCGT
  by_contra hfinite
  let s : ℝ := ((intrinsicInjRadius (I := I) g hEnorm p).toReal + 1) / c
  have hs : 0 < s := div_pos (by positivity) hc
  have hreal := (ENNReal.ofReal_le_iff_le_toReal hfinite).1 (hbound s hs)
  have hcs : c * s = (intrinsicInjRadius (I := I) g hEnorm p).toReal + 1 := by
    dsimp only [s]
    field_simp [hc.ne']
  rw [hcs] at hreal
  linarith

omit [T2Space (TangentBundle I M)] [ConnectedSpace M] in
private lemma flat_exp_injective_of_infinite_inj
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (p : M) (hinf : intrinsicInjRadius (I := I) g hEnorm p = ⊤) :
    Function.Injective (fun v : E =>
      expMapIntrinsic (I := I) g hEnorm p (v : TangentSpace I p)) := by
  intro u v huv
  let a : E := (normalFrame (I := I) g p).symm u
  let b : E := (normalFrame (I := I) g p).symm v
  let R : ℝ := max ‖a‖ ‖b‖ + 1
  have hR : ENNReal.ofReal R < intrinsicInjRadius (I := I) g hEnorm p := by
    rw [hinf]
    exact ENNReal.ofReal_lt_top
  have ha : a ∈ Metric.ball (0 : E) R := by
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)
  have hb : b ∈ Metric.ball (0 : E) R := by
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt (le_max_right _ _) (lt_add_one _)
  have hab : intrinsicFramedExp (I := I) g hEnorm p a =
      intrinsicFramedExp (I := I) g hEnorm p b := by
    erw [intrinsicFrame_apply, intrinsicFrame_apply]
    have haU : normalFrame (I := I) g p a = u :=
      (normalFrame (I := I) g p).apply_symm_apply u
    have hbV : normalFrame (I := I) g p b = v :=
      (normalFrame (I := I) g p).apply_symm_apply v
    rw [haU, hbV]
    exact huv
  have heq := intrinsicInjOn_ball (I := I) g hEnorm p hR ha hb hab
  have heqModel : (normalFrame (I := I) g p).symm u =
      (normalFrame (I := I) g p).symm v := heq
  exact (normalFrame (I := I) g p).symm.injective heqModel

omit [T2Space (TangentBundle I M)] [ConnectedSpace M] in
private lemma flat_normalJacobi_density_one
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hflat : ∀ y : M, Tensor0SBundle.normSq0S (I := I) g y 4
      (metricRm04At (I := I) g y) = 0) (p : M) (z : E) :
    curveDensity (I := I) g
      (intrinsicGeodesic (I := I) g hEnorm p (normalFrame (I := I) g p z))
      (fun i t => intrinsicJacobi (I := I) g hEnorm p
        (normalFrame (I := I) g p z) ((normalBasis (I := I) g p) i) t) 1 = 1 := by
  classical
  have hgram : curveGram (I := I) g
      (intrinsicGeodesic (I := I) g hEnorm p (normalFrame (I := I) g p z))
      (fun i t => intrinsicJacobi (I := I) g hEnorm p
        (normalFrame (I := I) g p z) ((normalBasis (I := I) g p) i) t) 1 = 1 := by
    ext i j
    have hmetric := flat_intrFrameMetric_inner g hEnorm hflat p z
      ((stdOrthonormalBasis ℝ E) i) ((stdOrthonormalBasis ℝ E) j)
    erw [intrinsic_metric_jacobi (I := I) g hEnorm p z
      ((stdOrthonormalBasis ℝ E) i) ((stdOrthonormalBasis ℝ E) j),
      normalFrame_basis (I := I) g p i, normalFrame_basis (I := I) g p j,
      (stdOrthonormalBasis ℝ E).inner_eq_ite] at hmetric
    erw [intrinsicFrame_apply (I := I) g hEnorm p z] at hmetric
    simp only [curveGram, Matrix.of_apply, Matrix.one_apply,
      expMapIntrinsic] at hmetric ⊢
    convert hmetric using 1
    rfl
  rw [curveDensity, hgram, Matrix.det_one, Real.sqrt_one]

private lemma flat_exp_ball_image
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (p : M) {r : ℝ} (hr : 0 < r) :
    (fun v : E => expMapIntrinsic (I := I) g hEnorm p (v : TangentSpace I p)) ''
        gBall (I := I) g p r =
      {y : M | riemannianEDist I p y < ENNReal.ofReal r} := by
  ext y
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hdist := intrinsicGeodesic_riemannianEDist_le (I := I) g hEnorm p
      (v : TangentSpace I p) (s := 0) (t := 1) zero_le_one
    have hbound : riemannianEDist I p (expMapIntrinsic (I := I) g hEnorm p v) ≤
        ENNReal.ofReal (Real.sqrt (g.inner p v v)) := by
      erw [intrinsicGeodesic_zero, ← expMapIntrinsic_def] at hdist
      simpa only [sub_zero, mul_one] using hdist
    exact hbound.trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Real.sqrt_nonneg _)).2 hv)
  · intro hy
    obtain ⟨v, hv, hnorm⟩ :=
      hopf_rinow_expMapIntrinsic_surjective_minimizing (I := I) g hEnorm p y
    refine ⟨v, ?_, hv⟩
    change Real.sqrt (g.inner p v v) < r
    rw [hnorm]
    have hlt := (ENNReal.toReal_lt_toReal (riemannianEDist_ne_top (I := I) p y)
      ENNReal.ofReal_ne_top).2 hy
    simpa only [ENNReal.toReal_ofReal hr.le] using hlt

private lemma flat_ball_volume_of_infinite_inj
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hflat : ∀ y : M, Tensor0SBundle.normSq0S (I := I) g y 4
      (metricRm04At (I := I) g y) = 0)
    (p : M) (hinf : intrinsicInjRadius (I := I) g hEnorm p = ⊤)
    {r : ℝ} (hr : 0 < r) :
    riemannianVolumeMeasure (I := I) (M := M) g
        {y : M | riemannianEDist I p y < ENNReal.ofReal r} =
      euclideanUnitBallVolume (Module.finrank ℝ E) *
        ENNReal.ofReal (r ^ Module.finrank ℝ E) := by
  erw [← flat_exp_ball_image g hEnorm p hr,
    riemVol_exp_image_eq g hEnorm p (measurableSet_gBall (I := I) g p r)
      (flat_exp_injective_of_infinite_inj g hEnorm p hinf).injOn,
    expJacobian_normal_int, preimage_gBall]
  calc
    _ = ∫⁻ _z in Metric.ball (0 : E) r, (1 : ℝ≥0∞) ∂volume := by
      apply setLIntegral_congr_fun measurableSet_ball
      intro z _hz
      simpa only [ENNReal.ofReal_one] using
        congrArg ENNReal.ofReal (flat_normalJacobi_density_one g hEnorm hflat p z)
    _ = (volume : Measure E) (Metric.ball (0 : E) r) := by simp
    _ = _ := flat_model_ball_volume hr

end Intrinsic

theorem riemannianBallOf_volume_eq_euclidean_of_flat_noncollapsed
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    (hflat : ∀ y : M, Tensor0SBundle.normSq0S (I := I) g y 4
      (metricRm04At (I := I) g y) = 0)
    {κ : ℝ} (hκ : 0 < κ)
    (hNC : ∀ (p : M) (r : ℝ), 0 < r →
      (∀ y ∈ riemannianBallOf g p r, r ^ 4 *
        Tensor0SBundle.normSq0S (I := I) g y 4 (metricRm04At (I := I) g y) ≤ 1) →
      ENNReal.ofReal (κ * r ^ Module.finrank ℝ E) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p r))
    (p : M) {r : ℝ} (hr : 0 < r) :
    riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p r) =
      euclideanUnitBallVolume (Module.finrank ℝ E) *
        ENNReal.ofReal (r ^ Module.finrank ℝ E) := by
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let _ : IsRiemannianManifold I M := ⟨fun _ _ => rfl⟩
  let _ : CompleteSpace M := hcomplete.complete
  have hEnorm : IsMetricNorm (I := I) g :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  have hinf := intrInjRadius_eq_top_of_flat_volume_growth g hEnorm hflat hκ p
    (fun s hs => hNC p s hs (fun y _hy => by simp only [hflat, mul_zero]; norm_num))
  exact flat_ball_volume_of_infinite_inj g hEnorm hflat p hinf hr

theorem flowMetricBall_volume_eq_euclidean_of_flat_noncollapsed
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (time : D.FlowTime)
    (hcomplete : RiemannianMetricComplete (S.base.metric (time : ℝ)))
    (hflat : ∀ y : M, FlowMetricBall.rmNormSq S (time : ℝ) y = 0)
    {κ : ℝ} (hκ : 0 < κ)
    (hNC : ∀ B : FlowMetricBall S time, B.IsSpatiallyKappaNoncollapsed κ)
    (B : FlowMetricBall S time) :
    B.volume = euclideanUnitBallVolume (Module.finrank ℝ E) *
      ENNReal.ofReal (B.radius ^ Module.finrank ℝ E) := by
  have hflatMetric : ∀ y : M, Tensor0SBundle.normSq0S (I := I)
      (S.base.metric (time : ℝ)) y 4
      (metricRm04At (I := I) (S.base.metric (time : ℝ)) y) = 0 := hflat
  change riemannianVolumeMeasure (I := I) (M := M) (S.base.metric (time : ℝ))
      (riemannianBallOf (S.base.metric (time : ℝ)) B.center B.radius) = _
  apply riemannianBallOf_volume_eq_euclidean_of_flat_noncollapsed
    (S.base.metric (time : ℝ)) hcomplete hflatMetric hκ _ B.center B.radius_pos
  intro p r hr hcurv
  let ball : FlowMetricBall S time := ⟨p, r, hr⟩
  have hcontrolled : ball.IsSpatiallyRmControlled := hcurv
  have hvolume : ENNReal.ofReal κ * ENNReal.ofReal r ^ Module.finrank ℝ E ≤
      riemannianVolumeMeasure (I := I) (M := M) (S.base.metric (time : ℝ))
        (riemannianBallOf (S.base.metric (time : ℝ)) p r) := (hNC ball hcontrolled).2
  simpa only [ENNReal.ofReal_mul hκ.le, ENNReal.ofReal_pow hr.le] using hvolume

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
