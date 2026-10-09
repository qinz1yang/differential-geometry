import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ScalarHarnack
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardScalarControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardScalarLower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCylinderLimitRicci
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.TerminalFromJets
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.SpatialNoncollapse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCurvatureBounds
import DifferentialGeometry.Geometry.Comparison.CheegerGromovTaylor.InjectivityRadius.Local
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Bounds.InjectivityRadius
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Metric.Balls
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.LocalCurvatureInjectivity
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.Local
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.LocalProperness

set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

private theorem PartialStandardSolution.terminal_edist_le
    (S : PartialStandardSolution) {a t : ℝ} (ha : 0 ≤ a) (hat : a ≤ t)
    (ht : t ∈ S.domain) (x y : E3) :
    riemannianEDistOf (S.metric t) x y ≤ riemannianEDistOf (S.metric a) x y := by
  have htime := (mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos t).mp ht
  have hslab : Icc a t ⊆ S.domain := by
    intro s hs
    exact (mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos s).mpr
      ⟨ha.trans hs.1, (ENNReal.ofReal_le_ofReal hs.2).trans_lt htime.2⟩
  have hreg : Ioo a t ⊆ (lifetimeInterval S.lifetime S.lifetime_pos).regular := by
    intro s hs
    exact (mem_lifetimeInterval_regular S.lifetime S.lifetime_pos s).mpr
      ⟨ha.trans_lt hs.1, (ENNReal.ofReal_le_ofReal hs.2.le).trans_lt htime.2⟩
  have hquad : ∀ z : E3, ∀ v : TangentSpace (𝓡 3) z,
      (S.metric t).inner z v v ≤ (1 : ℝ) * (S.metric a).inner z v v := by
    intro z v
    have hanti := Perelman.CanonicalNeighborhood.metric_inner_antitoneOn_of_ricci_nonnegative_interior
      S.toSolutionOn S.isSolutionOn hslab hreg (fun s hs z v => by
        change 0 ≤ metricRicciAt (S.metric s) z (vec2 v v)
        rw [metricRicciAt_apply_eq_ricciTensor]
        exact S.ricciTensor_nonnegative s (hslab ⟨hs.1.le, hs.2.le⟩) z v) z v
    simpa only [PartialStandardSolution.toSolutionOn_metric, one_mul] using
      hanti ⟨le_rfl, hat⟩ ⟨hat, le_rfl⟩ hat
  have h := edistOf_le_of_quad (S.metric a) (S.metric t) zero_lt_one hquad x y
  simpa only [Real.sqrt_one, ENNReal.ofReal_one, one_mul] using h

theorem standard_curvature_derivative_bounds_of_terminal_scalar_bound
    {tau T r R : ℝ} (htau : 0 < tau) (hT : 0 < T)
    (hr : 0 ≤ r) (hrR : r < R) (A : ℝ) :
    ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧ ∀ (S : PartialStandardSolution)
      (t : ℝ), t ∈ S.domain → 2 * tau ≤ t → t ≤ T → ∀ p : E3,
        (∀ y ∈ riemannianClosedBallOf (S.metric t) p R,
          metricScalarAt (S.metric t) y ≤ A) →
        ∀ m : ℕ, ∀ s ∈ Icc (t - tau / 2) t,
          ∀ y ∈ riemannianClosedBallOf (S.metric t) p r,
            curvDerivNorm (I := 𝓡 3) m (S.metric s) y ≤ C m := by
  let B := max A 1
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let K := 100 * (T * B / tau)
  have hK : 0 < K := by dsimp [K]; positivity
  let rho := (R - r) / 2
  have hrho : 0 < rho := by dsimp [rho]; linarith
  let rad := rho * Real.sqrt K
  have hrad : 0 < rad := mul_pos hrho (Real.sqrt_pos.mpr hK)
  let C : ℕ → ℝ := fun m => max 0
    (shiLocalUniformBound 3 m (K * tau) rad * K / Real.sqrt (tau / 2) ^ m)
  refine ⟨C, fun m => le_max_left _ _, ?_⟩
  intro S t ht htau_t htT p hscalar m s hs y hy
  let a := t - tau
  have ha : 0 < a := by dsimp [a]; linarith
  have hat : a < t := by dsimp [a]; linarith
  have htime := (mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos t).mp ht
  have hdom : Icc a t ⊆ S.domain := by
    intro v hv
    exact (mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos v).mpr
      ⟨ha.le.trans hv.1, (ENNReal.ofReal_le_ofReal hv.2).trans_lt htime.2⟩
  have hreg : Ico a t ⊆ (lifetimeInterval S.lifetime S.lifetime_pos).regular := by
    intro v hv
    exact (mem_lifetimeInterval_regular S.lifetime S.lifetime_pos v).mpr
      ⟨ha.trans_le hv.1, (ENNReal.ofReal_le_ofReal hv.2.le).trans_lt htime.2⟩
  have hrad_eq : rad / Real.sqrt K = rho :=
    mul_div_cancel_right₀ _ (Real.sqrt_pos.mpr hK).ne'
  have hball : IsCompact {z : E3 | riemannianEDistOf (S.metric a) y z ≤
      ENNReal.ofReal (rad / Real.sqrt K)} := by
    rw [hrad_eq]
    exact (S.complete a (hdom ⟨le_rfl, hat.le⟩)).closedEBall_isCompact y rho
  have hcurv : ∀ v ∈ Icc a t, ∀ z : E3,
      riemannianEDistOf (S.metric a) y z ≤ ENNReal.ofReal (rad / Real.sqrt K) →
        curvDerivNormSq (I := 𝓡 3) 0 (S.metric v) z ≤ K ^ 2 := by
    intro v hv z hz
    rw [hrad_eq] at hz
    have hzR : z ∈ riemannianClosedBallOf (S.metric t) p R := by
      calc
        _ ≤ riemannianEDistOf (S.metric t) p y + riemannianEDistOf (S.metric t) y z :=
          riemannianEDistOf_triangle _ _ _ _
        _ ≤ ENNReal.ofReal r + ENNReal.ofReal rho :=
          add_le_add hy ((S.terminal_edist_le ha.le hat.le ht y z).trans hz)
        _ = ENNReal.ofReal (r + rho) := (ENNReal.ofReal_add hr hrho.le).symm
        _ ≤ ENNReal.ofReal R := ENNReal.ofReal_le_ofReal (by dsimp [rho]; linarith)
    have hRz : metricScalarAt (S.metric t) z ≤ B := (hscalar z hzR).trans (le_max_left _ _)
    have hhn := S.scalar_time_mul_le (ha.le.trans hv.1) hv.2 ht z
    have hlow := S.one_le_scalar v (hdom hv) z
    have hvTau : tau ≤ v := by dsimp [a] at hv; linarith [hv.1]
    have hupper : metricScalarAt (S.metric v) z ≤ T * B / tau := by
      apply (le_div_iff₀ htau).mpr
      have hh : t * metricScalarAt (S.metric t) z ≤ T * B :=
        (mul_le_mul_of_nonneg_left hRz htime.1).trans
          (mul_le_mul_of_nonneg_right htT hB.le)
      have hl : tau * metricScalarAt (S.metric v) z ≤ v * metricScalarAt (S.metric v) z :=
        mul_le_mul_of_nonneg_right hvTau (by linarith)
      nlinarith only [hl, hhn, hh]
    have hRm := S.normSq_rm_le_scalar_sq v (hdom hv) z
    change normSq0S (S.metric v) z 4 (metricRm04 (S.metric v) z) ≤ _
    dsimp only [K]
    nlinarith [sq_le_sq₀ (by linarith : 0 ≤ metricScalarAt (S.metric v) z)
      (by positivity : 0 ≤ T * B / tau) |>.mpr hupper]
  have hshi := Perelman.KappaSolutions.shi_local_curvDerivNorm_terminal_of_solution_jets
    S.toSolutionOn S.isSolutionOn (by simp) hat hK hrad hdom hreg y hball hcurv
    m s ⟨by dsimp [a]; linarith [hs.1], hs.2⟩ y
    (by rw [riemannianEDistOf_self]; exact bot_le)
  have ht_a : t - a = tau := by dsimp [a]; ring
  have hs_a : tau / 2 ≤ s - a := by dsimp [a]; linarith [hs.1]
  norm_num only [ht_a, finrank_euclideanSpace, Fintype.card_fin] at hshi
  apply hshi.trans
  apply le_trans _ (le_max_right 0 _)
  apply div_le_div_of_nonneg_left
  · exact mul_nonneg (shiLocalUniformBound_nonneg _ _ _ _) hK.le
  · exact pow_pos (Real.sqrt_pos.mpr (half_pos htau)) _
  · exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hs_a) _

end DifferentialGeometry.PDE.RicciFlow
end

set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

theorem standard_injectivity_radius_lower_of_terminal_scalar_bound
    {tau r R : ℝ} (htau : 0 < tau) (hr : 0 ≤ r) (hrR : r < R) (A : ℝ) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ (S : PartialStandardSolution) (t : ℝ),
      t ∈ S.domain → tau ≤ t → t < 1 → ∀ p : E3,
        (∀ y ∈ riemannianClosedBallOf (S.metric t) p R,
          metricScalarAt (S.metric t) y ≤ A) →
        ∀ y ∈ riemannianClosedBallOf (S.metric t) p r,
          HasInjRadiusAt (S.pointedFlow.atTime t) y eta := by
  let B := max A 1
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let K := 100 ^ 2 * B ^ 2
  have hK : 0 < K := by dsimp [K]; positivity
  let rho := min (R - r) (min 1 (min (K + 1)⁻¹ (Real.sqrt (5000 * tau))))
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hrhoR : rho ≤ R - r := min_le_left _ _
  have hrho1 : rho ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hrhoK : rho ≤ (K + 1)⁻¹ :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrhotau : rho ≤ Real.sqrt (5000 * tau) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hmul : rho * (K + 1) ≤ 1 := by
    calc
      _ ≤ (K + 1)⁻¹ * (K + 1) := mul_le_mul_of_nonneg_right hrhoK (by linarith)
      _ = 1 := inv_mul_cancel₀ (by linarith)
  have hrho_mul : rho * K ≤ 1 := by nlinarith
  have hscaled : rho ^ 4 * K ≤ 1 := by
    calc
      _ = rho ^ 3 * (rho * K) := by ring
      _ ≤ 1 ^ 3 * 1 := mul_le_mul (pow_le_pow_left₀ hrho.le hrho1 3) hrho_mul
        (mul_nonneg hrho.le hK.le) (by norm_num)
      _ = 1 := by norm_num
  have hkappa : 0 < standardParabolicNoncollapseCoeff / 1000000 :=
    div_pos standardParabolicNoncollapseCoeff_pos (by norm_num)
  obtain ⟨iota, hiota, hinj⟩ := Perelman.CanonicalNeighborhood.FiniteHorn.local_metric_injectivity
    (I := 𝓡 3) hkappa
  refine ⟨iota * rho, mul_pos hiota hrho, ?_⟩
  intro S t ht htaut ht1 p hscalar y hy
  have hcurv : ∀ z ∈ riemannianBallOf (S.metric t) y rho,
      rho ^ 4 * normSq0S (S.metric t) z 4 (metricRm04At (S.metric t) z) ≤ 1 := by
    intro z hz
    have hzR : z ∈ riemannianClosedBallOf (S.metric t) p R := by
      calc
        _ ≤ riemannianEDistOf (S.metric t) p y + riemannianEDistOf (S.metric t) y z :=
          riemannianEDistOf_triangle _ _ _ _
        _ ≤ ENNReal.ofReal r + ENNReal.ofReal rho := add_le_add hy hz.le
        _ = ENNReal.ofReal (r + rho) := (ENNReal.ofReal_add hr hrho.le).symm
        _ ≤ ENNReal.ofReal R := ENNReal.ofReal_le_ofReal (by linarith)
    have hRz : metricScalarAt (S.metric t) z ≤ B := (hscalar z hzR).trans (le_max_left _ _)
    have hlow := S.one_le_scalar t ht z
    have hbound : normSq0S (S.metric t) z 4 (metricRm04At (S.metric t) z) ≤ K := by
      have hh := S.normSq_rm_le_scalar_sq t ht z
      dsimp only [K]
      exact hh.trans (mul_le_mul_of_nonneg_left
        (sq_le_sq₀ (by linarith : 0 ≤ metricScalarAt (S.metric t) z) hB.le |>.mpr hRz)
        (by positivity))
    exact (mul_le_mul_of_nonneg_left hbound (pow_nonneg hrho.le 4)).trans hscaled
  let ball : FlowMetricBall S.toSolutionOn ⟨t, ht⟩ := ⟨y, rho, hrho⟩
  have hvol := (S.spatially_noncollapsed_of_time_ge ⟨t, ht⟩ htaut ht1 ball hrhotau hcurv).2
  have hvol' : ENNReal.ofReal ((standardParabolicNoncollapseCoeff / 1000000) *
      rho ^ Module.finrank ℝ E3) ≤ riemannianVolumeMeasure (𝓡 3) E3
      (S.metric t) (riemannianBallOf (S.metric t) y rho) := by
    rw [ENNReal.ofReal_mul hkappa.le, ENNReal.ofReal_pow hrho.le]
    exact hvol
  exact hasInjRadiusAt_of_expMap_injOn (S.pointedFlow.atTime t) y (mul_pos hiota hrho)
    (hinj E3 (S.metric t) (S.complete t ht) y rho hrho hcurv hvol')

end DifferentialGeometry.PDE.RicciFlow
end

set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

private def standardTerminalMetricSequence (S : ℕ → PartialStandardSolution)
    (time : ℕ → ℝ) (point : ℕ → E3) : PointedRiemannianSeq (𝓡 3) :=
  ⟨fun i => ((S i).pointedFlow.atTime (time i)).repoint (point i)⟩

theorem exists_standard_terminal_pairwise_metric_approximation_within_radius
    (S : ℕ → PartialStandardSolution) (time : ℕ → ℝ) (point : ℕ → E3)
    {tau rho : ℝ} (htau : 0 < tau) (hrho : 0 < rho)
    (htime : ∀ i, time i ∈ (S i).domain ∧ tau ≤ time i ∧ time i < 1)
    (hscalar : ∀ r : ℝ, 0 < r → r < rho → ∃ A : ℝ, ∀ᶠ i in atTop,
      ∀ y ∈ riemannianClosedBallOf ((S i).metric (time i)) (point i) r,
        metricScalarAt ((S i).metric (time i)) y ≤ A) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∀ r : ℝ, 0 < r → r < rho → ∀ eps : ℝ, 0 < eps → eps < 1 → ∀ m : ℕ,
        ∃ N : ℕ, ∀ k l : ℕ, N ≤ k → N ≤ l →
          ∃ F : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
            F (point (phi k)) = point (phi l) ∧
            Nonempty (PartialDiffeomorphMetricApproximation
              (riemannianClosedBallOf ((S (phi k)).metric (time (phi k))) (point (phi k)) r)
              eps m F ((S (phi k)).metric (time (phi k))) ((S (phi l)).metric (time (phi l)))) ∧
            Nonempty (PartialDiffeomorphMetricApproximation
              (riemannianClosedBallOf ((S (phi l)).metric (time (phi l))) (point (phi l)) r)
              eps m F.symm ((S (phi l)).metric (time (phi l))) ((S (phi k)).metric (time (phi k)))) := by
  let Y := standardTerminalMetricSequence S time point
  have hc : SeqMetricComplete Y := ⟨fun i => (S i).pointedFlow_complete (time i) (htime i).1⟩
  have hconn : ∀ i, ConnectedSpace (Y.obj i).M := fun _ => by
    change ConnectedSpace E3
    infer_instance
  apply exists_subsequence_bidirectional_pairwise_metric_approximation_within_radius Y hc hconn hrho
  · intro r hr hrrho m
    let R := (r + rho) / 2
    have hrR : r < R := by dsimp [R]; linarith
    have hRrho : R < rho := by dsimp [R]; linarith
    obtain ⟨A, hA⟩ := hscalar R (hr.trans hrR) hRrho
    obtain ⟨C, hC, hb⟩ := standard_curvature_derivative_bounds_of_terminal_scalar_bound
      (half_pos htau) (by norm_num : (0 : ℝ) < 1) hr.le hrR A
    refine ⟨C m, hC m, ?_⟩
    filter_upwards [hA] with i hi y hy
    exact hb (S i) (time i) (htime i).1 (by linarith [(htime i).2.1])
      (htime i).2.2.le (point i) hi m (time i)
      ⟨by linarith, le_rfl⟩ y hy
  · intro r hr hrrho
    let R := (r + rho) / 2
    have hrR : r < R := by dsimp [R]; linarith
    have hRrho : R < rho := by dsimp [R]; linarith
    obtain ⟨A, hA⟩ := hscalar R (hr.trans hrR) hRrho
    obtain ⟨eta, heta, hb⟩ := standard_injectivity_radius_lower_of_terminal_scalar_bound
      htau hr.le hrR A
    refine ⟨eta, heta, ?_⟩
    filter_upwards [hA] with i hi y hy
    exact hb (S i) (time i) (htime i).1 (htime i).2.1 (htime i).2.2 (point i) hi y hy

theorem exists_standard_terminal_pointed_convergence_within_radius
    (S : ℕ → PartialStandardSolution) (time : ℕ → ℝ) (point : ℕ → E3)
    {tau rho : ℝ} (htau : 0 < tau) (hrho : 0 < rho)
    (htime : ∀ i, time i ∈ (S i).domain ∧ tau ≤ time i ∧ time i < 1)
    (hscalar : ∀ r : ℝ, 0 < r → r < rho → ∃ A : ℝ, ∀ᶠ i in atTop,
      ∀ y ∈ riemannianClosedBallOf ((S i).metric (time i)) (point i) r,
        metricScalarAt ((S i).metric (time i)) y ≤ A) :
    let X : PointedRiemannianSeq (𝓡 3) :=
      ⟨fun i => ((S i).pointedFlow.atTime (time i)).repoint (point i)⟩
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ radius : ℕ → ℝ,
      (∀ k, 0 < radius k ∧ radius k < rho) ∧ Tendsto radius atTop (𝓝 rho) ∧
      ∃ L : PointedRiemannianManifold (𝓡 3),
      ∃ maps : PointedRiemannianConvergenceMaps X L phi,
      ∃ C : PointedRiemannianConverges X L phi maps,
        (∀ k, C.metrics.domain k = CanonicalMetricCompactness.canonicalSourceData maps k) ∧
        (∀ k, maps.target k = riemannianBallOf ((S (phi k)).metric (time (phi k)))
          (point (phi k)) (radius k)) ∧
        (∀ x : L.M, riemannianEDistOf L.metric L.basepoint x < ENNReal.ofReal rho) ∧
        (∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
          ∀ x ∈ maps.source k, ∀ v : TangentSpace (𝓡 3) x,
            (1 - eps) * L.metric.inner x v v ≤
              ((S (phi k)).metric (time (phi k))).inner (maps.partialDiffeomorph k x)
                (mfderiv (𝓡 3) (𝓡 3) (maps.partialDiffeomorph k) x v)
                (mfderiv (𝓡 3) (𝓡 3) (maps.partialDiffeomorph k) x v) ∧
              ((S (phi k)).metric (time (phi k))).inner (maps.partialDiffeomorph k x)
                (mfderiv (𝓡 3) (𝓡 3) (maps.partialDiffeomorph k) x v)
                (mfderiv (𝓡 3) (𝓡 3) (maps.partialDiffeomorph k) x v) ≤
              (1 + eps) * L.metric.inner x v v) ∧
        ∀ r : ℝ, 0 ≤ r → r < rho →
          IsCompact (riemannianClosedBallOf L.metric L.basepoint r) := by
  let X := standardTerminalMetricSequence S time point
  obtain ⟨f, hf, hp⟩ := exists_standard_terminal_pairwise_metric_approximation_within_radius
    S time point htau hrho htime hscalar
  let Y := X.subseq f
  have hc : SeqMetricComplete Y := ⟨fun k => (S (f k)).pointedFlow_complete
    (time (f k)) (htime (f k)).1⟩
  have hconn : ∀ k, ConnectedSpace (Y.obj k).M := fun _ => by
    change ConnectedSpace E3
    infer_instance
  let P : ∀ k, ProperMetricOn (Y.obj k) := fun k =>
    properMetricOn (Y.obj k) (hc.complete k) (hconn k)
  obtain ⟨g, hg, radius, hrad, hradlim, L, maps, C, hcanonical, htargets, hradial, hmetrics⟩ :=
    exists_pointed_convergence_within_radius_and_radial_bound (I := 𝓡 3) P hrho (by
      intro r hr hrrho eps heps heps1 m
      obtain ⟨N, hN⟩ := hp r hr hrrho eps heps heps1 m
      refine ⟨N, fun k l hk hl => ?_⟩
      let : MetricSpace (Y.obj k).M := (P k).ms
      let : MetricSpace (Y.obj l).M := (P l).ms
      obtain ⟨F, hbase, ⟨D⟩, _⟩ := hN k l hk hl
      refine ⟨F, hbase, ⟨D.mono ?_ le_rfl heps1⟩⟩
      intro y hy
      have hh := (P k).riemannianClosedBallOf_eq_closedBall (Y.obj k).basepoint hr.le
      change y ∈ riemannianClosedBallOf (Y.obj k).metric (Y.obj k).basepoint r
      rw [hh]
      exact hy)
  refine ⟨f ∘ g, hf.comp hg, radius, hrad, hradlim, L,
    maps.ofSeqSubseq f, C.ofSeqSubseq f, ?_, ?_, hradial, hmetrics, ?_⟩
  · intro k
    change (C.metrics.domain k).ofSeqSubseq f k = _
    rw [hcanonical k]
    rfl
  · intro k
    let : MetricSpace (Y.obj (g k)).M := (P (g k)).ms
    change maps.target k = riemannianBallOf (Y.obj (g k)).metric (Y.obj (g k)).basepoint (radius k)
    rw [htargets k]
    ext y
    change dist y (Y.obj (g k)).basepoint < radius k ↔
      riemannianEDistOf (Y.obj (g k)).metric (Y.obj (g k)).basepoint y < ENNReal.ofReal (radius k)
    have hreal : riemannianEDistOf (Y.obj (g k)).metric (Y.obj (g k)).basepoint y =
        ENNReal.ofReal (dist (Y.obj (g k)).basepoint y) := (P (g k)).realizes _ _
    rw [hreal, ENNReal.ofReal_lt_ofReal_iff (hrad k).1, dist_comm]
  · intro r hr hrrho
    apply maps.isCompact_closed_ball_of_target_coverage (fun k => P (g k))
      (rho := rho) ?_ ?_ hr hrrho
    · intro s hs hsrho
      filter_upwards [hradlim.eventually_const_lt hsrho] with k hk
      let : MetricSpace (Y.obj (g k)).M := (P (g k)).ms
      rw [htargets k]
      intro y hy
      have hreal : riemannianEDistOf (Y.obj (g k)).metric (Y.obj (g k)).basepoint y =
          ENNReal.ofReal (dist (Y.obj (g k)).basepoint y) := (P (g k)).realizes _ _
      change riemannianEDistOf (Y.obj (g k)).metric (Y.obj (g k)).basepoint y ≤
        ENNReal.ofReal s at hy
      rw [hreal, ENNReal.ofReal_le_ofReal_iff hs.le] at hy
      change dist y (Y.obj (g k)).basepoint < radius k
      rw [dist_comm]
      exact hy.trans_lt hk
    · intro eps heps
      obtain ⟨N, hN⟩ := hmetrics eps heps
      filter_upwards [eventually_ge_atTop N] with k hk
      exact fun x hx v => (hN k hk x hx v).2

end DifferentialGeometry.PDE.RicciFlow
end
