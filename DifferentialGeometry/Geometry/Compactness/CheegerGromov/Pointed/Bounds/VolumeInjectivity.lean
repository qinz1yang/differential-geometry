import DifferentialGeometry.Geometry.Comparison.CheegerGromovTaylor.InjectivityRadius.Local
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Bounds.InjectivityRadius








set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Topology Manifold ContDiff ENNReal
open DifferentialGeometry
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Integral.Measure

namespace DifferentialGeometry.CheegerGromovCompactness

universe u

section

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem volume_ratio_on_component
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete g)
    (x : M) {q b D : ℝ} (hq : 0 ≤ q) (hb : 0 < b) (hbD : b ≤ D)
    (hRic : ∀ y ∈ riemannianBallOf g x D, ∀ w : TangentSpace I y,
      -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2) * g.inner y w w ≤
        ricciTensor g y w w) :
    riemannianVolumeMeasure I M g (riemannianBallOf g x D) *
        ENNReal.ofReal (hyperbolicRadialVolume q (Module.finrank ℝ E - 1) b) ≤
      ENNReal.ofReal (hyperbolicRadialVolume q (Module.finrank ℝ E - 1) D) *
        riemannianVolumeMeasure I M g (riemannianBallOf g x b) := by
  let : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun y : M => TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro y v w; rfl⟩⟩
  let metricM : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : PseudoEMetricSpace M := metricM.toPseudoEMetricSpace
  let : IsRiemannianManifold I M := ⟨fun _ _ => rfl⟩
  let : @CompleteSpace M metricM.toUniformSpace := hg.complete
  let U : TopologicalSpace.Opens M := connectedComponentOpen (I := I) x
  let gU : SmoothRiemannianMetric I U := g.restrictOpen U
  let : SigmaCompactSpace U := (isClosed_connectedComponent (x := x)).sigmaCompactSpace
  let : ConnectedSpace U := connectedComponentOpen_connectedSpace (I := I) x
  let : IsManifold I 1 U := IsManifold.of_le (n := ∞) (by decide)
  let : TopologicalSpace.MetrizableSpace U := Manifold.metrizableSpace I U
  let : T3Space U := inferInstance
  let : RiemannianBundle (fun y : U => TangentSpace I y) := ⟨gU.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun y : U => TangentSpace I y) :=
    ⟨⟨gU.inner, gU.contMDiff.continuous, by intro y v w; rfl⟩⟩
  let metricU : EMetricSpace U := EMetricSpace.ofRiemannianMetric I U
  let : PseudoEMetricSpace U := metricU.toPseudoEMetricSpace
  let : IsRiemannianManifold I U := ⟨fun _ _ => rfl⟩
  have hgU : RiemannianMetricComplete gU :=
    DifferentialGeometry.Geometry.Metric.riemannianMetricComplete_restrictOpen_connCompOpen
      g x hg
  let : @CompleteSpace U metricU.toUniformSpace := hgU.complete
  have hEnormU : IsMetricNorm gU :=
    fun y v => tensor0SBundle_enorm_eq_riemannianBundle_enorm gU y v
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  let xU : U := connectedComponentPoint (I := I) x
  have hEdist : ∀ y : U, riemannianEDistOf g x (y : M) =
      riemannianEDist I xU y := by
    intro y
    exact (DifferentialGeometry.Geometry.Metric.edistOf_restrictOpen_connCompOpen
      g x xU y).symm
  have hRicU : ricciBoundedBelowOn gU
      {y : U | riemannianEDist I xU y < ENNReal.ofReal D}
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2)) := by
    intro y hy w
    have hyM : y.1 ∈ riemannianBallOf g x D := by
      change riemannianEDistOf g x y.1 < ENNReal.ofReal D
      rwa [hEdist]
    have h := hRic y.1 hyM w
    rw [SmoothRiemannianMetric.restrictOpen_inner g U y w w,
      DifferentialGeometry.Geometry.Curvature.ricciTensor_restrictOpen g U y w w,
      mfderiv_subtype_val_apply]
    exact h
  have hvol : ∀ t : ℝ, riemannianVolumeMeasure I U gU
      {y : U | riemannianEDist I xU y < ENNReal.ofReal t} =
      riemannianVolumeMeasure I M g (riemannianBallOf g x t) := by
    intro t
    have hmeas : MeasurableSet (riemannianBallOf g x t) := by
      have hd : Continuous (fun y : M => riemannianEDistOf g x y) := by
        simpa only [riemannianEDistOf] using continuous_riemannianEDist g x
      exact (isOpen_lt hd continuous_const).measurableSet
    have hsub : riemannianBallOf g x t ⊆ (U : Set M) :=
      DifferentialGeometry.Geometry.Metric.edistOf_ball_subset_connCompOpen g x t
    have hpre : (Subtype.val ⁻¹' riemannianBallOf g x t : Set U) =
        {y : U | riemannianEDist I xU y < ENNReal.ofReal t} := by
      ext y
      simp only [Set.mem_preimage, riemannianBallOf, Set.mem_ofPred_eq, hEdist]
    rw [← hpre]
    exact DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_restrictOpen_preimage_of_subset
      g U hmeas hsub
  have h := segmentBall_vol_rel_endpoint_of_ricciBoundedBelowOn
    gU hEnormU xU hq hb hbD hRicU
  simpa only [hvol] using h

private theorem volume_lower_of_base_volume
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete g)
    (p x : M) {r v S A b : ℝ} (hr : 0 < r) (hS : 0 < S)
    (hA : 0 < A) (hb : 0 < b) (hb1 : b ≤ 1)
    (hn : 0 < Module.finrank ℝ E)
    (hx : x ∈ riemannianBallOf g p S)
    (hvol : ENNReal.ofReal v ≤
      riemannianVolumeMeasure I M g (riemannianBallOf g p r))
    (hRm : ∀ y ∈ riemannianBallOf g p (2 * S + r + 2),
      Real.sqrt (Tensor0SBundle.normSq0S g y 4 (metricRm04At g y)) ≤ A) :
    ENNReal.ofReal (v *
        hyperbolicRadialVolume ((Module.finrank ℝ E : ℝ) * Real.sqrt A)
          (Module.finrank ℝ E - 1) b /
        hyperbolicRadialVolume ((Module.finrank ℝ E : ℝ) * Real.sqrt A)
          (Module.finrank ℝ E - 1) (S + r + 1)) ≤
      riemannianVolumeMeasure I M g (riemannianBallOf g x b) := by
  let D : ℝ := S + r + 1
  let q : ℝ := (Module.finrank ℝ E : ℝ) * Real.sqrt A
  have hD : 0 < D := by dsimp [D]; positivity
  have hq : 0 ≤ q := mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  have hlarge : riemannianBallOf g p r ⊆ riemannianBallOf g x D := by
    intro y hy
    change riemannianEDistOf g x y < ENNReal.ofReal D
    calc
      riemannianEDistOf g x y ≤
          riemannianEDistOf g x p + riemannianEDistOf g p y :=
        riemannianEDistOf_triangle g x p y
      _ ≤ ENNReal.ofReal S + ENNReal.ofReal r := by
        rw [riemannianEDistOf_comm g x p]
        exact add_le_add hx.le hy.le
      _ = ENNReal.ofReal (S + r) := (ENNReal.ofReal_add hS.le hr.le).symm
      _ < ENNReal.ofReal D := (ENNReal.ofReal_lt_ofReal_iff hD).mpr (by dsimp [D]; linarith)
  have hbuffer : riemannianBallOf g x D ⊆ riemannianBallOf g p (2 * S + r + 2) := by
    intro y hy
    change riemannianEDistOf g p y < ENNReal.ofReal (2 * S + r + 2)
    calc
      riemannianEDistOf g p y ≤
          riemannianEDistOf g p x + riemannianEDistOf g x y :=
        riemannianEDistOf_triangle g p x y
      _ ≤ ENNReal.ofReal S + ENNReal.ofReal D := add_le_add hx.le hy.le
      _ = ENNReal.ofReal (S + D) := (ENNReal.ofReal_add hS.le hD.le).symm
      _ < ENNReal.ofReal (2 * S + r + 2) :=
        (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by dsimp [D]; linarith)
  have hRic : ∀ y ∈ riemannianBallOf g x D, ∀ w : TangentSpace I y,
      -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2) * g.inner y w w ≤
        ricciTensor g y w w := by
    intro y hy w
    rcases eq_or_ne (Module.finrank ℝ E) 1 with hn1 | hn1
    · have hz : metricRm04At (I := I) g y = 0 :=
        metricRm04At_eq_zero_of_finrank_le_one g (by omega) y
      have hb0 : Real.sqrt (Tensor0SBundle.normSq0S g y 4 (metricRm04At g y)) ≤ 0 := by
        have hzero : (Tensor0SBundle.tensor0SMetricData (I := I) g y 4).inner
            (0 : Tensor0SBundle.Tensor0SSpace 4 I y) 0 = 0 :=
          (Tensor0SBundle.MetricFiberData.inner_self_eq_zero_iff _ _).mpr rfl
        rw [hz, Tensor0SBundle.normSq0S, Tensor0SBundle.inner0S, hzero, Real.sqrt_zero]
      have h := BonnetMyers.ricciLowerAt_of_rm g hb0 w
      simpa [hn1] using h
    · have hn : 2 ≤ Module.finrank ℝ E := by omega
      have h := BonnetMyers.ricciLowerAt_of_rm g (hRm y (hbuffer hy)) w
      have hinner : 0 ≤ g.inner y w w := by
        rcases eq_or_ne w 0 with rfl | hw
        · simp
        · exact (g.pos y w hw).le
      have hn1 : (1 : ℝ) ≤ ((Module.finrank ℝ E - 1 : ℕ) : ℝ) := by
        exact_mod_cast (show 1 ≤ Module.finrank ℝ E - 1 by omega)
      have hq2 : q ^ 2 = (Module.finrank ℝ E : ℝ) ^ 2 * A := by
        dsimp only [q]
        rw [mul_pow, Real.sq_sqrt hA.le]
      have hcoef : (Module.finrank ℝ E : ℝ) ^ 2 * A ≤
          ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2 := by
        rw [hq2]
        exact le_mul_of_one_le_left (by positivity) hn1
      exact (mul_le_mul_of_nonneg_right (neg_le_neg hcoef) hinner).trans h
  have hratio := volume_ratio_on_component g hg x hq hb
    (hb1.trans (by dsimp [D]; linarith)) hRic
  have hlow : ENNReal.ofReal v ≤
      riemannianVolumeMeasure I M g (riemannianBallOf g x D) :=
    hvol.trans (measure_mono hlarge)
  have hcombined : ENNReal.ofReal v *
        ENNReal.ofReal (hyperbolicRadialVolume q (Module.finrank ℝ E - 1) b) ≤
      ENNReal.ofReal (hyperbolicRadialVolume q (Module.finrank ℝ E - 1) D) *
        riemannianVolumeMeasure I M g (riemannianBallOf g x b) := by
    refine le_trans ?_ hratio
    gcongr
  have hden : 0 < hyperbolicRadialVolume q (Module.finrank ℝ E - 1) D :=
    hyperbolicRadialVolume_pos hq hD
  have hden0 : ENNReal.ofReal
      (hyperbolicRadialVolume q (Module.finrank ℝ E - 1) D) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hden)
  have heq : ENNReal.ofReal (hyperbolicRadialVolume q (Module.finrank ℝ E - 1) D) *
      ENNReal.ofReal (v * hyperbolicRadialVolume q (Module.finrank ℝ E - 1) b /
        hyperbolicRadialVolume q (Module.finrank ℝ E - 1) D) =
      ENNReal.ofReal v *
        ENNReal.ofReal (hyperbolicRadialVolume q (Module.finrank ℝ E - 1) b) := by
    rw [← ENNReal.ofReal_mul hden.le,
      ← ENNReal.ofReal_mul' (hyperbolicRadialVolume_pos hq hb).le]
    congr 1
    field_simp [hden.ne']
  exact (ENNReal.mul_le_mul_iff_right hden0 ENNReal.ofReal_ne_top).mp
    (by rw [heq]; exact hcombined)

end

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle




theorem exists_uniform_injRadius_of_pointed_bounds
    (n : ℕ) (hn : 0 < n) {r v S A : ℝ}
    (hr : 0 < r) (hv : 0 < v) (hS : 0 < S) (hA : 0 < A) :
    letI : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) :=
      ⟨by simpa using (show n ≠ 0 by omega)⟩
    ∃ iota : ℝ, 0 < iota ∧
      ∀ X : PointedRiemannianManifold.{u} (𝓘(ℝ, EuclideanSpace ℝ (Fin n))),
        MetricComplete X →
        ENNReal.ofReal v ≤ riemannianVolumeMeasure _ X.M X.metric
          (riemannianBallOf X.metric X.basepoint r) →
        (∀ y ∈ riemannianBallOf X.metric X.basepoint (2 * S + r + 2),
          Real.sqrt (Tensor0SBundle.normSq0S X.metric y 4
            (metricRm04At X.metric y)) ≤ A) →
        ∀ x ∈ riemannianBallOf X.metric X.basepoint S, HasInjRadiusAt X x iota := by
  let E := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, E)
  have hdim : Module.finrank ℝ E = n := by simp [E]
  let : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; omega⟩
  let b : ℝ := min 1 (1 / A)
  have hb : 0 < b := lt_min zero_lt_one (by positivity)
  have hb1 : b ≤ 1 := min_le_left _ _
  have hbA : b * A ≤ 1 := (le_div_iff₀ hA).mp (min_le_right _ _)
  have hb2A : b ^ 2 * A ≤ 1 := by
    calc
      b ^ 2 * A = b * (b * A) := by ring
      _ ≤ b * 1 := mul_le_mul_of_nonneg_left hbA hb.le
      _ ≤ 1 := by simpa only [mul_one] using hb1
  have hb4A : b ^ 4 * A ^ 2 ≤ 1 := by
    calc
      b ^ 4 * A ^ 2 = (b ^ 2 * A) ^ 2 := by ring
      _ ≤ 1 ^ 2 := pow_le_pow_left₀ (by positivity) hb2A 2
      _ = 1 := by norm_num
  let q : ℝ := (n : ℝ) * Real.sqrt A
  let D : ℝ := S + r + 1
  let w : ℝ := v * hyperbolicRadialVolume q (n - 1) b /
    hyperbolicRadialVolume q (n - 1) D
  have hq : 0 ≤ q := mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  have hD : 0 < D := by dsimp [D]; positivity
  have hw : 0 < w := div_pos (mul_pos hv (hyperbolicRadialVolume_pos hq hb))
    (hyperbolicRadialVolume_pos hq hD)
  let kappa : ℝ := w / b ^ n
  have hkappa : 0 < kappa := div_pos hw (pow_pos hb _)
  obtain ⟨eta, heta, hinj⟩ :=
    DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.local_metric_injectivity
      (I := I) hkappa
  refine ⟨eta * b, mul_pos heta hb, ?_⟩
  intro X hcomplete hvol hRm x hx
  have hg : RiemannianMetricComplete X.metric := ⟨MetricComplete.complete X hcomplete⟩
  have hvolx : ENNReal.ofReal w ≤ riemannianVolumeMeasure I X.M X.metric
      (riemannianBallOf X.metric x b) := by
    simpa only [w, q, D, E, finrank_euclideanSpace, Fintype.card_fin] using
      volume_lower_of_base_volume X.metric hg X.basepoint x hr hS hA hb hb1
        (by rwa [hdim]) hx hvol hRm
  have hnormalized : ∀ y ∈ riemannianBallOf X.metric x b,
      b ^ 4 * Tensor0SBundle.normSq0S X.metric y 4 (metricRm04At X.metric y) ≤ 1 := by
    intro y hy
    have hybig : y ∈ riemannianBallOf X.metric X.basepoint (2 * S + r + 2) := by
      change riemannianEDistOf X.metric X.basepoint y < ENNReal.ofReal (2 * S + r + 2)
      calc
        riemannianEDistOf X.metric X.basepoint y ≤
            riemannianEDistOf X.metric X.basepoint x + riemannianEDistOf X.metric x y :=
          riemannianEDistOf_triangle _ _ _ _
        _ ≤ ENNReal.ofReal S + ENNReal.ofReal b := add_le_add hx.le hy.le
        _ = ENNReal.ofReal (S + b) := (ENNReal.ofReal_add hS.le hb.le).symm
        _ < ENNReal.ofReal (2 * S + r + 2) := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)
    have hnorm := (sq_le_sq₀ (Real.sqrt_nonneg _) hA.le).mpr (hRm y hybig)
    rw [Real.sq_sqrt (Tensor0SBundle.normSq0S_nonneg _ _ _ _)] at hnorm
    exact (mul_le_mul_of_nonneg_left hnorm (pow_nonneg hb.le 4)).trans hb4A
  have hvolscaled : ENNReal.ofReal (kappa * b ^ Module.finrank ℝ E) ≤
      riemannianVolumeMeasure I X.M X.metric (riemannianBallOf X.metric x b) := by
    simpa only [hdim, kappa, div_mul_cancel₀ _ (pow_ne_zero _ hb.ne')] using hvolx
  exact hasInjRadiusAt_of_expMap_injOn X x (mul_pos heta hb)
    (hinj X.M X.metric hg x b hb hnormalized hvolscaled)



theorem exists_uniform_injRadius_of_base_volume
    (n : ℕ) (hn : 2 ≤ n) {r v S A : ℝ}
    (hr : 0 < r) (hv : 0 < v) (hS : 0 < S) (hA : 0 < A) :
    letI : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) :=
      ⟨by simpa using (show n ≠ 0 by omega)⟩
    ∃ iota : ℝ, 0 < iota ∧
      ∀ X : PointedRiemannianManifold.{u} (𝓘(ℝ, EuclideanSpace ℝ (Fin n))),
        MetricComplete X →
        ENNReal.ofReal v ≤ riemannianVolumeMeasure _ X.M X.metric
          (riemannianBallOf X.metric X.basepoint r) →
        (∀ y ∈ riemannianBallOf X.metric X.basepoint (2 * S + r + 2),
          Real.sqrt (Tensor0SBundle.normSq0S X.metric y 4
            (metricRm04At X.metric y)) ≤ A) →
        ∀ x ∈ riemannianBallOf X.metric X.basepoint S, HasInjRadiusAt X x iota := by
  exact exists_uniform_injRadius_of_pointed_bounds n (by omega) hr hv hS hA

end DifferentialGeometry.CheegerGromovCompactness
