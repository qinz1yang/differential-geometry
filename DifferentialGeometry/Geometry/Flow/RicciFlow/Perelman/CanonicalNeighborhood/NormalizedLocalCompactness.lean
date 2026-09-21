import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CurvatureEscape
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedTerminalDerivatives
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.EntropyBounds
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.LocalCurvatureInjectivity

noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Integral.Measure
universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

private theorem terminal_local_injectivity
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (hkappa : 0 < kappa) (hsigma : 0 < sigma)
    {r R C : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hbound : ∀ i y, metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y < R →
      curvDerivNorm 0 ((X.term i).S.base.metric 0) y ≤ C) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ᶠ i in atTop, ∀ y : (X.term i).M,
      riemannianEDistOf ((X.term i).S.base.metric 0) (X.term i).basepoint y ≤ ENNReal.ofReal r →
        HasInjRadiusAt ((X.term i).atTime 0) y eta := by
  obtain ⟨iota, hiota, hinj⟩ := local_metric_injectivity (I := I3) hkappa
  let a : ℝ := min ((C ^ 2 + 1)⁻¹) (R - r)
  have ha : 0 < a := lt_min (by positivity) (sub_pos.mpr hrR)
  have haC : a ≤ (C ^ 2 + 1)⁻¹ := min_le_left _ _
  have habuffer : a ≤ R - r := min_le_right _ _
  have haone : a ≤ 1 := haC.trans
    ((inv_le_one₀ (by positivity : 0 < C ^ 2 + 1)).mpr (by nlinarith))
  have hac : a * C ^ 2 ≤ 1 := by
    calc
      _ ≤ (C ^ 2 + 1)⁻¹ * (C ^ 2 + 1) :=
        mul_le_mul haC (by linarith) (sq_nonneg _) (by positivity)
      _ = 1 := inv_mul_cancel₀ (by positivity)
  have hascaled : a ^ 4 * C ^ 2 ≤ 1 := by
    calc
      _ = a ^ 3 * (a * C ^ 2) := by ring
      _ ≤ 1 ^ 3 * 1 := mul_le_mul (pow_le_pow_left₀ ha.le haone 3) hac
        (by positivity) (by norm_num)
      _ = 1 := by norm_num
  have hscale := (Real.tendsto_sqrt_atTop.comp X.scale_tendsto).atTop_mul_const hsigma
  refine ⟨iota * a, mul_pos hiota ha, ?_⟩
  filter_upwards [hscale.eventually_ge_atTop 1] with i hi y hy
  have hzero : (0 : ℝ) ∈ (X.interval i).carrier := by
    rw [X.carrier_eq]
    exact ⟨by linarith [X.depth_pos i], le_rfl⟩
  have hcurv : ∀ z ∈ riemannianBallOf ((X.term i).S.base.metric 0) y a,
      a ^ 4 * Tensor0SBundle.normSq0S ((X.term i).S.base.metric 0) z 4
        (metricRm04At ((X.term i).S.base.metric 0) z) ≤ 1 := by
    intro z hz
    have hz' : metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint z < R := by
      have hd : riemannianEDistOf ((X.term i).S.base.metric 0) (X.term i).basepoint z <
          ENNReal.ofReal R := by
        calc
          _ ≤ riemannianEDistOf ((X.term i).S.base.metric 0) (X.term i).basepoint y +
              riemannianEDistOf ((X.term i).S.base.metric 0) y z :=
            riemannianEDistOf_triangle _ _ _ _
          _ < ENNReal.ofReal r + ENNReal.ofReal a :=
            ENNReal.add_lt_add_of_le_of_lt (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hy) hy hz
          _ = ENNReal.ofReal (r + a) := (ENNReal.ofReal_add hr ha.le).symm
          _ ≤ ENNReal.ofReal R := ENNReal.ofReal_le_ofReal (by linarith)
      exact (ENNReal.toReal_lt_toReal hd.ne_top ENNReal.ofReal_ne_top).mpr hd |>.trans_eq
        (ENNReal.toReal_ofReal (hr.trans hrR.le))
    have hj := hbound i z hz'
    have hsq : Tensor0SBundle.normSq0S ((X.term i).S.base.metric 0) z 4
        (metricRm04At ((X.term i).S.base.metric 0) z) ≤ C ^ 2 := by
      apply le_sq_of_sqrt_le (Tensor0SBundle.normSq0S_nonneg _ _ _ _)
      change Real.sqrt (Tensor0SBundle.normSq0S ((X.term i).S.base.metric 0) z 4
        (metricRm04 ((X.term i).S.base.metric 0) z)) ≤ C at hj
      rwa [metricRm04_apply] at hj
    exact (mul_le_mul_of_nonneg_left hsq (pow_nonneg ha.le 4)).trans hascaled
  let B : FlowMetricBall (X.term i).S ⟨0, hzero⟩ := ⟨y, a, ha⟩
  have hvol := ((X.noncollapse i).2 _ B (haone.trans hi) hcurv).2
  have hvol' : ENNReal.ofReal (kappa * a ^ Module.finrank ℝ ThreeSpace) ≤
      riemannianVolumeMeasure I3 (X.term i).M ((X.term i).S.base.metric 0)
        (riemannianBallOf ((X.term i).S.base.metric 0) y a) := by
    rw [ENNReal.ofReal_mul hkappa.le, ENNReal.ofReal_pow ha.le]
    exact hvol
  exact hasInjRadiusAt_of_expMap_injOn ((X.term i).atTime 0) y (mul_pos hiota ha)
    (hinj _ _ ⟨X.complete i 0 hzero⟩ y a ha hcurv hvol')

theorem exists_terminal_pairwise_metric_approximation_within_radius
    {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            ∀ rho : ℝ, 0 < rho →
              (∀ r : ℝ, 0 < r → r < rho → CurvatureBoundedWithin X r) →
              ∃ f : ℕ → ℕ, StrictMono f ∧
                ∀ r : ℝ, 0 < r → r < rho → ∀ eta : ℝ, 0 < eta → eta < 1 → ∀ p : ℕ,
                  ∃ N : ℕ, ∀ k l : ℕ, N ≤ k → N ≤ l →
                    ∃ Ψ : PartialDiffeomorph I3 I3 (X.term (f k)).M (X.term (f l)).M ∞,
                      Ψ (X.term (f k)).basepoint = (X.term (f l)).basepoint ∧
                      Nonempty (PartialDiffeomorphMetricApproximation
                        (riemannianClosedBallOf ((X.term (f k)).S.base.metric 0)
                          (X.term (f k)).basepoint r)
                        eta p Ψ ((X.term (f k)).S.base.metric 0)
                          ((X.term (f l)).S.base.metric 0)) := by
  obtain ⟨epsStar, hepsStar, hsublevel⟩ := exists_curvDerivNorm_le_on_scalar_sublevel hkappa
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X rho hrho hinner
  have hb : ∀ r : ℝ, 0 < r → r < rho → ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ i y, metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y < r →
        curvDerivNorm m ((X.term i).S.base.metric 0) y ≤ C := by
    intro r hr hrho m
    obtain ⟨A, hA⟩ := hinner r hr hrho
    obtain ⟨C, hC, hc⟩ := hsublevel eps heps hle sigma hsigma Phi hPhi X A m
    exact ⟨C, hC, fun i y hy => hc i y (hA i y hy)⟩
  let Y := X.toFlowSequence.atTime 0
  have hcomplete : SeqMetricComplete Y := by
    constructor
    intro i
    apply X.complete i 0
    rw [X.carrier_eq]
    exact ⟨by linarith [X.depth_pos i], le_rfl⟩
  apply exists_subsequence_pairwise_metric_approximation_within_radius
    Y hcomplete X.connected hrho
  · intro r hr hrrho m
    obtain ⟨C, hC, hc⟩ := hb ((r + rho) / 2) (by linarith) (by linarith) m
    refine ⟨C, hC, Filter.Eventually.of_forall fun i y hy => hc i y ?_⟩
    exact (ENNReal.toReal_le_of_le_ofReal hr.le hy).trans_lt (by linarith)
  · intro r hr hrrho
    obtain ⟨C, _, hc⟩ := hb ((r + rho) / 2) (by linarith) (by linarith) 0
    exact terminal_local_injectivity X hkappa hsigma hr.le (by linarith) hc

theorem exists_terminal_pairwise_metric_approximation_of_not_boundedAtDistance
    {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            ¬ BoundedAtDistance X → ∃ f : ℕ → ℕ, ∃ hf : StrictMono f,
              ∃ F : FiniteControlledRadius (X.reindex f hf),
                ∀ r : ℝ, 0 < r → r < F.radius → ∀ eta : ℝ, 0 < eta → eta < 1 → ∀ p : ℕ,
                  ∃ N : ℕ, ∀ k l : ℕ, N ≤ k → N ≤ l →
                    ∃ Ψ : PartialDiffeomorph I3 I3 (X.term (f k)).M (X.term (f l)).M ∞,
                      Ψ (X.term (f k)).basepoint = (X.term (f l)).basepoint ∧
                      Nonempty (PartialDiffeomorphMetricApproximation
                        (riemannianClosedBallOf ((X.term (f k)).S.base.metric 0)
                          (X.term (f k)).basepoint r)
                        eta p Ψ ((X.term (f k)).S.base.metric 0)
                          ((X.term (f l)).S.base.metric 0)) := by
  obtain ⟨e₁, he₁, hpairs⟩ := exists_terminal_pairwise_metric_approximation_within_radius hkappa
  obtain ⟨e₂, r₀, he₂, hr₀, hsmall⟩ := exists_curvDerivNorm_bound_on_terminal_ball hkappa
  refine ⟨min e₁ e₂, lt_min he₁ he₂, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X hnot
  obtain ⟨C, _, hc⟩ := hsmall eps heps (hle.trans (min_le_right _ _))
    sigma hsigma Phi hPhi X 0
  have hbounded : CurvatureBoundedWithin X r₀ := by
    refine ⟨(Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * C, fun i y hy => ?_⟩
    have hj := hc i y hy.le
    change Real.sqrt (Tensor0SBundle.normSq0S ((X.term i).S.base.metric 0) y 4
      (metricRm04 ((X.term i).S.base.metric 0) y)) ≤ C at hj
    rw [metricRm04_apply] at hj
    exact (le_abs_self _).trans ((scalar_abs_le_rm (I := I3)
      ((X.term i).S.base.metric 0) y).trans
        (mul_le_mul_of_nonneg_left hj (by positivity)))
  obtain ⟨f, hf, ⟨F⟩⟩ := exists_reindex_nonempty_finiteControlledRadius_of_subsequenceCurvatureEscape
    (subsequenceCurvatureEscape_of_positiveDistanceCurvatureEscape X
      (positiveDistanceCurvatureEscape_of_curvatureBoundedWithin X hnot hr₀ hbounded))
  obtain ⟨g, hg, hp⟩ := hpairs eps heps (hle.trans (min_le_left _ _)) sigma hsigma Phi hPhi
    (X.reindex f hf) F.radius F.radius_pos F.inner_bound
  let F' : FiniteControlledRadius (X.reindex (f ∘ g) (hf.comp hg)) :=
    { radius := F.radius
      radius_pos := F.radius_pos
      inner_bound := fun r hr hrrho => by
        obtain ⟨A, hA⟩ := F.inner_bound r hr hrrho
        exact ⟨A, fun i y hy => hA (g i) y hy⟩
      points := fun i => F.points (g i)
      distance_limit := F.distance_limit.comp hg.tendsto_atTop
      curvature_limit := F.curvature_limit.comp hg.tendsto_atTop }
  exact ⟨f ∘ g, hf.comp hg, F', hp⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
