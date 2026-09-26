import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Parabolic
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.TerminalScalar
import DifferentialGeometry.Geometry.Curvature.ScalarControlsRm
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciUpper
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Set DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold ContDiff ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [IsManifold I 1 M]
  [T2Space M] [SigmaCompactSpace M] {D : RealTimeInterval}

namespace FlowMetricBall

theorem rmNormSq_le_of_le_of_curvatureOperator_nonnegative
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hcomplete : ∀ t ∈ D.regular, RiemannianMetricComplete (I := I) (S.base.metric t))
    (hcurv : ∀ a b : ℝ, Icc a b ⊆ D.regular →
      ∃ C : ℝ, ∀ t ∈ Icc a b, ∀ x : M,
        normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (hR : ∀ t ∈ D.regular, ∀ x : M,
      metricAlgebraicCurvatureTensorAt (I := I) (S.base.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hdim : Module.finrank ℝ E = 3) {s t : ℝ} (ht : t ∈ D.carrier)
    (hback : Iio t ⊆ D.regular) (hst : s ≤ t) (x : M) :
    rmNormSq S s x ≤ 30 ^ 4 * rmNormSq S t x := by
  have hnorm_t : 0 ≤ rmNormSq S t x := normSq0S_nonneg _ _ _ _
  rcases hst.eq_or_lt with rfl | hlt
  · nlinarith
  have : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  have hsreg : s ∈ D.regular := hback hlt
  have hR0 : 0 ≤ S.scalar s x :=
    metricScalarAt_nonnegative_of_curvatureOperator_nonnegative _ x (hR s hsreg x)
  have hmono : S.scalar s x ≤ S.scalar t x :=
    hamilton_ancient_scalar_le_terminal S hS hcomplete hcurv hR hst ht hback x
  have hdimx : Module.finrank ℝ (TangentSpace I x) = 3 := hdim
  have habs := scalar_abs_le_rm (I := I) (S.base.metric t) x
  rw [hdimx] at habs
  have hsqrt : Real.sqrt (rmNormSq S t x) ^ 2 = rmNormSq S t x := Real.sq_sqrt hnorm_t
  have hRt : S.scalar t x ≤ 9 * Real.sqrt (rmNormSq S t x) := by
    have h := (le_abs_self _).trans habs
    norm_num at h
    exact h
  have hsq : S.scalar s x ^ 2 ≤ (9 * Real.sqrt (rmNormSq S t x)) ^ 2 :=
    pow_le_pow_left₀ hR0 (hmono.trans hRt) 2
  have hbound := normSq_metricRm04_le_scalar_sq_of_curvatureOperator_nonnegative
    (S.base.metric s) x hdim (hR s hsreg x)
  change rmNormSq S s x ≤ 100 ^ 2 * S.scalar s x ^ 2 at hbound
  nlinarith

theorem isParabolicallyRmControlled_of_isSpatiallyRmControlled_of_curvatureOperator_nonnegative
    {S : SolutionOn (I := I) (M := M) D} (hS : IsSolutionOn S)
    (hcomplete : ∀ t ∈ D.regular, RiemannianMetricComplete (I := I) (S.base.metric t))
    (hcurv : ∀ a b : ℝ, Icc a b ⊆ D.regular →
      ∃ C : ℝ, ∀ t ∈ Icc a b, ∀ x : M,
        normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (hR : ∀ t ∈ D.regular, ∀ x : M,
      metricAlgebraicCurvatureTensorAt (I := I) (S.base.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hdim : Module.finrank ℝ E = 3) {time : D.FlowTime} (hback : Iio (time : ℝ) ⊆ D.regular)
    {B B' : FlowMetricBall S time} (hcenter : B'.center = B.center)
    (hradius : 30 * B'.radius ≤ B.radius) (hB : B.IsSpatiallyRmControlled) :
    B'.IsParabolicallyRmControlled := by
  have hr' := B'.radius_pos
  have hle : B'.radius ≤ B.radius := by linarith
  refine ⟨fun s hs => ?_, fun s hs x hx => ?_⟩
  · rcases hs.2.eq_or_lt with h | h
    · exact h ▸ time.property
    · exact D.regular_subset (hback h)
  · have hx' : x ∈ B.set := by
      change riemannianEDistOf (S.base.metric time) B.center x < ENNReal.ofReal B.radius
      change riemannianEDistOf (S.base.metric time) B'.center x < ENNReal.ofReal B'.radius at hx
      rw [hcenter] at hx
      exact hx.trans_le (ENNReal.ofReal_le_ofReal hle)
    have hpt := rmNormSq_le_of_le_of_curvatureOperator_nonnegative S hS hcomplete hcurv hR hdim
      time.property hback hs.2 x
    have hctrl := hB x hx'
    have hnorm : 0 ≤ rmNormSq S time x := normSq0S_nonneg _ _ _ _
    have hpow : (30 * B'.radius) ^ 4 ≤ B.radius ^ 4 := pow_le_pow_left₀ (by positivity) hradius 4
    calc B'.radius ^ 4 * rmNormSq S s x ≤ B'.radius ^ 4 * (30 ^ 4 * rmNormSq S time x) :=
          mul_le_mul_of_nonneg_left hpt (by positivity)
      _ = (30 * B'.radius) ^ 4 * rmNormSq S time x := by ring
      _ ≤ B.radius ^ 4 * rmNormSq S time x := mul_le_mul_of_nonneg_right hpow hnorm
      _ ≤ 1 := hctrl

end FlowMetricBall

open FlowMetricBall in
theorem spatiallyKappaNoncollapsedBelowScale_of_parabolically_of_curvatureOperator_nonnegative
    {S : SolutionOn (I := I) (M := M) D} (hS : IsSolutionOn S)
    (hcomplete : ∀ t ∈ D.regular, RiemannianMetricComplete (I := I) (S.base.metric t))
    (hcurv : ∀ a b : ℝ, Icc a b ⊆ D.regular →
      ∃ C : ℝ, ∀ t ∈ Icc a b, ∀ x : M,
        normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (hR : ∀ t ∈ D.regular, ∀ x : M,
      metricAlgebraicCurvatureTensorAt (I := I) (S.base.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hdim : Module.finrank ℝ E = 3) (hback : ∀ t ∈ D.carrier, Iio t ⊆ D.regular)
    {kappa rho : ℝ} (hP : ParabolicallyKappaNoncollapsedBelowScale S kappa rho) :
    SpatiallyKappaNoncollapsedBelowScale S (kappa / 30 ^ 3) (30 * rho) := by
  refine ⟨by linarith [hP.1], fun time B hr hB => ?_⟩
  have hq : (0 : ℝ) < 1 / 30 := by norm_num
  let B' := B.shrink (1 / 30) hq
  have hB' : B'.IsParabolicallyRmControlled :=
    isParabolicallyRmControlled_of_isSpatiallyRmControlled_of_curvatureOperator_nonnegative
      hS hcomplete hcurv hR hdim (hback time time.property) (B := B) rfl
      (by change 30 * (1 / 30 * B.radius) ≤ B.radius; linarith) hB
  have hk := hP.2 time B' (by change 1 / 30 * B.radius ≤ rho; linarith) hB'
  refine ⟨div_pos hk.1 (by norm_num), ?_⟩
  have hvol := volume_mono (shrink_nested B hq (by norm_num))
  refine le_trans (le_of_eq ?_) (hk.2.trans hvol)
  change ENNReal.ofReal (kappa / 30 ^ 3) * ENNReal.ofReal B.radius ^ Module.finrank ℝ E =
    ENNReal.ofReal kappa * ENNReal.ofReal (1 / 30 * B.radius) ^ Module.finrank ℝ E
  rw [hdim, ← ENNReal.ofReal_pow B.radius_pos.le, ← ENNReal.ofReal_pow (by linarith [B.radius_pos]),
    ← ENNReal.ofReal_mul (by linarith [hk.1]), ← ENNReal.ofReal_mul hk.1.le]
  congr 1
  ring

end DifferentialGeometry.PDE.RicciFlow.Perelman

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

open Set DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold ContDiff ENNReal

universe u uE uH

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem pointedFlowNoncollapsedAllScales_of_parabolic_of_curvatureOperator_nonnegative
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D) {kappa : ℝ}
    (hdim : Module.finrank ℝ E = 3) (hcarrier : D.carrier = Iic 0)
    (hregular : D.regular = Iio 0)
    (hcomplete : ∀ t ∈ D.carrier, MetricComplete (I := I) (F.atTime (I := I) t))
    (hnonneg : ∀ t ∈ D.carrier, PointedFlowNonnegativeCurvatureOperator (I := I) F t)
    (hscalar : ∃ C : ℝ, PointedFlowScalarBounded (I := I) F C)
    (hP : ∀ rho : ℝ, 0 < rho → ParabolicallyKappaNoncollapsedBelowScale F.S kappa rho) :
    PointedFlowNoncollapsedAllScales (I := I) F (kappa / 30 ^ 3) := by
  have hR : ∀ t ∈ D.regular, ∀ x : F.M,
      metricAlgebraicCurvatureTensorAt (I := I) (F.S.base.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
    intro t ht x
    refine mem_algebraicCurvatureOperatorNonnegativeCone.mpr fun n c v w => ?_
    have h := hnonneg t (D.regular_subset ht) x n c v w
    with_unfolding_all exact h
  have hcurv : ∀ a b : ℝ, Icc a b ⊆ D.regular →
      ∃ C : ℝ, ∀ t ∈ Icc a b, ∀ x : F.M,
        normSq0S (I := I) (F.S.base.metric t) x 4 (F.S.base.rm04 t x) ≤ C := by
    obtain ⟨C, hC⟩ := hscalar
    refine fun a b hab => ⟨100 ^ 2 * C ^ 2, fun t ht x => ?_⟩
    have htc : t ∈ D.carrier := D.regular_subset (hab ht)
    have hbound := normSq_metricRm04_le_scalar_sq_of_curvatureOperator_nonnegative
      (F.S.base.metric t) x hdim (hR t (hab ht) x)
    have hRC := hC t htc x
    change normSq0S (I := I) (F.S.base.metric t) x 4 (F.S.base.rm04 t x) ≤
      100 ^ 2 * F.S.scalar t x ^ 2 at hbound
    exact hbound.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hRC.1 hRC.2 2)
      (by norm_num))
  have hcompleteR : ∀ t ∈ D.regular, RiemannianMetricComplete (I := I) (F.S.base.metric t) :=
    fun t ht => ⟨(hcomplete t (D.regular_subset ht)).complete⟩
  have hback : ∀ t ∈ D.carrier, Iio t ⊆ D.regular := by
    intro t ht s hs
    rw [hregular]
    rw [hcarrier] at ht
    exact show s < 0 from lt_of_lt_of_le hs (show t ≤ 0 from ht)
  intro time B
  exact (spatiallyKappaNoncollapsedBelowScale_of_parabolically_of_curvatureOperator_nonnegative
    F.isSolution hcompleteR hcurv hR hdim hback (hP B.radius B.radius_pos)).2 time B
    (by linarith [B.radius_pos])

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
