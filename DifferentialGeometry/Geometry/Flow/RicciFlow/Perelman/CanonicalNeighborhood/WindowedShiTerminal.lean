import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedSourceCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalLocalBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalCurvatureJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.CurvatureMetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.TerminalFromJets
import DifferentialGeometry.Geometry.Curvature.ScalarGradientNorm
import DifferentialGeometry.Geometry.Metric.SmoothLipschitz


set_option autoImplicit false
noncomputable section
open Bundle Manifold Filter Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Integral.Measure

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

private local instance shiTerminalC1 : IsManifold I3 1 M :=
  IsManifold.of_le (n := ∞) (by decide)


def windowedShiConstant (K : ℝ) (m : ℕ) : ℝ :=
  shiLocalUniformBound 3 m (sourceCurvatureBound 3 K) (Real.sqrt (sourceCurvatureBound 3 K)) *
    sourceCurvatureBound 3 K

omit [T2Space M] [SigmaCompactSpace M] in
theorem WindowedModelWitness.normalized_window
    {eps kappa : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness eps kappa S x t)
    (hregular : interior D.carrier ⊆ D.regular) :
    Icc (-modelDepth eps) 0 ⊆ (parabolicInterval D t (S.scalar t x) W.time_mem).carrier ∧
      Ioo (-modelDepth eps) 0 ⊆ (parabolicInterval D t (S.scalar t x) W.time_mem).regular := by
  have hmaps : MapsTo (parabolicTime t (S.scalar t x)) (Icc (-modelDepth eps) 0)
      (Icc (t - (eps * S.scalar t x)⁻¹) t) := by
    intro s hs
    constructor
    · simpa only [parabolicTime, modelDepth, div_eq_mul_inv, mul_inv, neg_mul, sub_eq_add_neg, add_comm]
        using add_le_add_right (div_le_div_of_nonneg_right hs.1 W.scalar_pos.le) t
    · exact add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hs.2 W.scalar_pos.le)
  constructor
  · intro s hs
    exact W.window_mem (hmaps hs)
  · intro s hs
    apply hregular
    apply interior_mono W.window_mem
    rw [interior_Icc]
    constructor
    · simpa only [parabolicTime, modelDepth, div_eq_mul_inv, mul_inv, neg_mul, sub_eq_add_neg, add_comm]
        using add_lt_add_right (div_lt_div_of_pos_right hs.1 W.scalar_pos) t
    · have hh := div_neg_of_neg_of_pos hs.2 W.scalar_pos
      change t + s / S.scalar t x < t
      linarith


omit [T2Space M] [SigmaCompactSpace M] in
theorem WindowedModelWitness.normalized_fixed_window
    {eps kappa : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness eps kappa S x t) (heps4 : eps ≤ 1 / 4)
    (hregular : interior D.carrier ⊆ D.regular) :
    Icc (-(4 : ℝ)) 0 ⊆ (parabolicInterval D t (S.scalar t x) W.time_mem).carrier ∧
      Ioo (-(4 : ℝ)) 0 ⊆ (parabolicInterval D t (S.scalar t x) W.time_mem).regular := by
  have hdepth : 4 ≤ modelDepth eps := by
    have hh := modelDepth_anti W.eps_pos heps4
    norm_num [modelDepth] at hh ⊢
    exact hh
  obtain ⟨hcarrier, hreg⟩ := W.normalized_window hregular
  exact ⟨(Icc_subset_Icc (neg_le_neg hdepth) le_rfl).trans hcarrier,
    (Ioo_subset_Ioo (neg_le_neg hdepth) le_rfl).trans hreg⟩


theorem WindowedModelWitness.normalized_curvDerivNorm_bound_on_model_ball
    (hS : IsSolutionOn S) {eps kappa K R a b : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness eps kappa S x t) (heps4 : eps ≤ 1 / 4) (hK : 0 ≤ K)
    (hR : 0 ≤ R) (hbuffer : R + 1 ≤ modelRadius eps)
    (hregular : interior D.carrier ⊆ D.regular)
    (ha : -modelDepth eps < a) (hab : a < b) (hb : b ≤ 0)
    (hmodel : ∀ s ∈ Icc a b, ∀ y ∈
      riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint (R + 1),
        W.model.rmNormSq s y ≤ K ^ 2)
    (m : ℕ) {s : ℝ} (hs : s ∈ Ioc a b)
    {y : W.model.M} (hy : y ∈
      riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint R) :
    curvDerivNorm m (rescaledMetric S t (S.scalar t x) W.scalar_pos s) (W.embedding y) ≤
      shiLocalUniformBound 3 m (sourceCurvatureBound 3 K * (b - a))
        (Real.sqrt (sourceCurvatureBound 3 K) / 2) * sourceCurvatureBound 3 K /
          Real.sqrt (s - a) ^ m := by
  let P := parabolicSolution S t (S.scalar t x) W.scalar_pos W.time_mem
  have hP : IsSolutionOn P := parabolicSolution_isSolutionOn S hS t _ W.scalar_pos W.time_mem
  let K0 := sourceCurvatureBound 3 K
  have hK0 : 0 < K0 := sourceCurvatureBound_pos 3 hK
  have hsqrt : 0 < Real.sqrt K0 := Real.sqrt_pos.mpr hK0
  have hhalf : (Real.sqrt K0 / 2) / Real.sqrt K0 = (1 : ℝ) / 2 := by
    field_simp
  have hroot : (1 / 2 : ℝ) < Real.sqrt (1 - eps) := by
    apply (Real.lt_sqrt (by norm_num)).mpr
    linarith
  have hsub : riemannianClosedBallOf (W.model.S.base.metric 0) y 1 ⊆
      riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint (R + 1) := by
    intro z hz
    calc
      _ ≤ riemannianEDistOf (W.model.S.base.metric 0) W.model.basepoint y +
          riemannianEDistOf (W.model.S.base.metric 0) y z :=
        riemannianEDistOf_triangle _ _ _ _
      _ ≤ ENNReal.ofReal R + ENNReal.ofReal 1 := add_le_add hy hz
      _ = ENNReal.ofReal (R + 1) := (ENNReal.ofReal_add hR zero_le_one).symm
  have hfull := hsub.trans (riemannianClosedBallOf_mono _ _ hbuffer)
  obtain ⟨hball, hcapture⟩ := W.source_closedBall_compact_subset_image y zero_lt_one hfull
    (by simpa only [mul_one] using hroot) (s := a) ⟨ha.le, hab.le.trans hb⟩
  obtain ⟨hcarrier, hreg⟩ := W.normalized_window hregular
  have hslab : Icc a b ⊆ (parabolicInterval D t (S.scalar t x) W.time_mem).carrier :=
    (Icc_subset_Icc ha.le hb).trans hcarrier
  have hregular' : Ico a b ⊆
      (parabolicInterval D t (S.scalar t x) W.time_mem).regular := by
    intro v hv
    exact hreg ⟨ha.trans_le hv.1, hv.2.trans_le hb⟩
  have hball' : IsCompact {z : M | riemannianEDistOf (P.base.metric a) (W.embedding y) z ≤
      ENNReal.ofReal ((Real.sqrt K0 / 2) / Real.sqrt K0)} := by
    rw [hhalf]
    exact hball
  have hcurv : ∀ v ∈ Icc a b, ∀ z : M,
      riemannianEDistOf (P.base.metric a) (W.embedding y) z ≤
        ENNReal.ofReal ((Real.sqrt K0 / 2) / Real.sqrt K0) →
      curvDerivNormSq 0 (P.base.metric v) z ≤ K0 ^ 2 := by
    intro v hv z hz
    rw [hhalf] at hz
    obtain ⟨q, hq, rfl⟩ := hcapture hz
    exact W.source_curvature_bound_at_of_model heps4 hK
      ⟨ha.le.trans hv.1, hv.2.trans hb⟩ (hfull hq) (hmodel v hv q (hsub hq))
  have hcenter : riemannianEDistOf (P.base.metric a) (W.embedding y) (W.embedding y) ≤
      ENNReal.ofReal ((Real.sqrt K0 / 2) / (2 * Real.sqrt K0)) := by
    rw [riemannianEDistOf_self]
    exact zero_le
  have h := KappaSolutions.shi_local_curvDerivNorm_terminal_of_solution_jets P hP
    (by simp [ThreeSpace]) hab hK0 (half_pos hsqrt) hslab hregular'
    (W.embedding y) hball' hcurv m s hs (W.embedding y) hcenter
  change curvDerivNorm m (P.base.metric s) (W.embedding y) ≤ _
  simpa only [show Module.finrank ℝ ThreeSpace = 3 by simp [ThreeSpace], K0] using h


theorem WindowedModelWitness.normalized_interior_curvature_derivative_bound
    (hS : IsSolutionOn S) {eps kappa K : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness eps kappa S x t) (heps4 : eps ≤ 1 / 4) (hK : 0 ≤ K)
    (hregular : interior D.carrier ⊆ D.regular)
    (hmodel : ∀ s ∈ Icc (-(4 : ℝ)) 0, ∀ y ∈
      riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint 2,
        W.model.rmNormSq s y ≤ K ^ 2) (m : ℕ) {r : ℝ} (hr : r ∈ Ioo (-1 : ℝ) 0) :
    Real.sqrt (nablaKRm04NormSqIntrinsic
      (parabolicSolution S t (S.scalar t x) W.scalar_pos W.time_mem) m r x) ≤
      windowedShiConstant K m := by
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let P := parabolicSolution S t (S.scalar t x) W.scalar_pos W.time_mem
  have hP : IsSolutionOn P := parabolicSolution_isSolutionOn S hS t _ W.scalar_pos W.time_mem
  let K0 := sourceCurvatureBound 3 K
  have hK0 : 0 < K0 := sourceCurvatureBound_pos 3 hK
  have hsqrt : 0 < Real.sqrt K0 := Real.sqrt_pos.mpr hK0
  obtain ⟨hslab, hreg⟩ := W.normalized_fixed_window heps4 hregular
  have ha : r - 1 ∈ Icc (-(4 : ℝ)) 0 := ⟨by linarith [hr.1], by linarith [hr.2]⟩
  obtain ⟨hball, hcurv⟩ := W.unitBall_compact_curvature_bound heps4 hK hmodel ha
  have hball' : IsCompact {y : M | riemannianEDistOf (P.base.metric (r - 1)) x y ≤
      ENNReal.ofReal (Real.sqrt K0 / Real.sqrt K0)} := by
    rw [div_self hsqrt.ne']
    exact hball
  have hcurv' : ∀ s ∈ Icc (r - 1) r, ∀ y : M,
      riemannianEDistOf (P.base.metric (r - 1)) x y ≤
        ENNReal.ofReal (Real.sqrt K0 / Real.sqrt K0) →
      nablaKRm04NormSqIntrinsic P 0 s y ≤ K0 ^ 2 := by
    intro s hs y hy
    have hy' : y ∈ riemannianClosedBallOf
        (rescaledMetric S t (S.scalar t x) W.scalar_pos (r - 1)) x 1 := by
      rw [div_self hsqrt.ne'] at hy
      exact hy
    exact hcurv s ⟨by linarith [hs.1, hr.1], by linarith [hs.2, hr.2]⟩ y hy'
  have hb := shi_bound_on_sliding_regular_window P hP
    (a := -4) (b := 0) (tau := 1) (K := K0) (R := Real.sqrt K0) (t := r)
    (by norm_num) zero_lt_one hK0 hsqrt hslab hreg
    ⟨by linarith [hr.1], hr.2⟩ x hball' hcurv' m x (by
      rw [riemannianEDistOf_self]
      exact zero_le)
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hb' : Real.sqrt (nablaKRm04NormSqIntrinsic P m r x) ≤ windowedShiConstant K m := by
    simpa only [mul_one, Real.sqrt_one, one_pow, div_one, hdim,
      windowedShiConstant, K0] using hb
  exact hb'


theorem WindowedModelWitness.normalized_terminal_curvature_derivative_bound
    (hS : IsSolutionOn S) {eps kappa K : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness eps kappa S x t) (heps4 : eps ≤ 1 / 4) (hK : 0 ≤ K)
    (hregular : interior D.carrier ⊆ D.regular)
    (hmodel : ∀ s ∈ Icc (-(4 : ℝ)) 0, ∀ y ∈
      riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint 2,
        W.model.rmNormSq s y ≤ K ^ 2) (m : ℕ) :
    nablaKRm04NormSqIntrinsic
      (parabolicSolution S t (S.scalar t x) W.scalar_pos W.time_mem) m 0 x ≤
      windowedShiConstant K m ^ 2 := by
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let P := parabolicSolution S t (S.scalar t x) W.scalar_pos W.time_mem
  have hP : IsSolutionOn P := parabolicSolution_isSolutionOn S hS t _ W.scalar_pos W.time_mem
  obtain ⟨hslab, hreg⟩ := W.normalized_fixed_window heps4 hregular
  apply solution_nablaKRm04NormSqIntrinsic_le_terminal P hP
    (a := -4) (b := 0) (by norm_num) hslab hreg m x
  filter_upwards [Ioo_mem_nhdsLT (show (-1 : ℝ) < 0 by norm_num)] with r hr
  exact le_sq_of_sqrt_le (normSq0S_nonneg _ _ _ _)
    (W.normalized_interior_curvature_derivative_bound hS heps4 hK hregular hmodel m hr)


theorem WindowedModelWitness.terminal_curvature_derivative_bound
    (hS : IsSolutionOn S) {eps kappa K : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness eps kappa S x t) (heps4 : eps ≤ 1 / 4) (hK : 0 ≤ K)
    (hregular : interior D.carrier ⊆ D.regular)
    (hmodel : ∀ s ∈ Icc (-(4 : ℝ)) 0, ∀ y ∈
      riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint 2,
        W.model.rmNormSq s y ≤ K ^ 2) (m : ℕ) :
    nablaKRm04NormSqIntrinsic S m t x ≤
      S.scalar t x ^ (2 + m) * windowedShiConstant K m ^ 2 := by
  let P := parabolicSolution S t (S.scalar t x) W.scalar_pos W.time_mem
  have hbound := W.normalized_terminal_curvature_derivative_bound hS heps4 hK hregular hmodel m
  have hpara := parabolicNablaKRmNormSq S t (S.scalar t x) W.scalar_pos W.time_mem m 0 x
  rw [parabolicTime_zero] at hpara
  have hunscale : S.scalar t x ^ (2 + m) * nablaKRm04NormSqIntrinsic P m 0 x =
      nablaKRm04NormSqIntrinsic S m t x := by
    rw [hpara, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ W.scalar_pos.ne', one_pow, one_mul]
  rw [← hunscale]
  exact mul_le_mul_of_nonneg_left hbound (pow_nonneg W.scalar_pos.le _)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

noncomputable section

open Set
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

theorem WindowedModelWitness.terminal_ball_isCompact_subset_inner_ball
    (hS : IsSolutionOn S) {eps kappa K : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness eps kappa S x t) (heps : eps ≤ 1 / 4) (hK : 0 ≤ K)
    (hregular : interior D.carrier ⊆ D.regular)
    (hmodel : ∀ s ∈ Icc (-(4 : ℝ)) 0, ∀ y ∈
      riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint 2,
        W.model.rmNormSq s y ≤ K ^ 2) :
    IsCompact (riemannianClosedBallOf
      (rescaledMetric S t (S.scalar t x) W.scalar_pos 0) x
      (1 / (4 * Real.exp (9 * sourceCurvatureBound 3 K)))) ∧
    riemannianClosedBallOf (rescaledMetric S t (S.scalar t x) W.scalar_pos 0) x
      (1 / (4 * Real.exp (9 * sourceCurvatureBound 3 K))) ⊆
      riemannianClosedBallOf (rescaledMetric S t (S.scalar t x) W.scalar_pos (-1)) x
        (1 / 2) := by
  let P := parabolicSolution S t (S.scalar t x) W.scalar_pos W.time_mem
  have hP : IsSolutionOn P := parabolicSolution_isSolutionOn S hS t _ W.scalar_pos W.time_mem
  let K0 := sourceCurvatureBound 3 K
  have hK0 : 0 < K0 := sourceCurvatureBound_pos 3 hK
  let L := Real.exp (9 * K0)
  have hL : 0 < L := Real.exp_pos _
  obtain ⟨hslab, hreg⟩ := W.normalized_fixed_window heps hregular
  have hslab' : Icc (-1 : ℝ) 0 ⊆ (parabolicInterval D t (S.scalar t x) W.time_mem).carrier :=
    (Icc_subset_Icc (by norm_num) le_rfl).trans hslab
  have hreg' : Ioo (-1 : ℝ) 0 ⊆ (parabolicInterval D t (S.scalar t x) W.time_mem).regular :=
    (Ioo_subset_Ioo (by norm_num) le_rfl).trans hreg
  obtain ⟨hball, hcurv⟩ := W.unitBall_compact_curvature_bound heps hK hmodel
    (a := -1) (by norm_num)
  have hhalfsub : riemannianClosedBallOf (P.base.metric (-1)) x (1 / 2) ⊆
      riemannianClosedBallOf (P.base.metric (-1)) x 1 := by
    intro y hy
    exact hy.trans (ENNReal.ofReal_le_ofReal (by norm_num))
  have hhalf : IsCompact (riemannianClosedBallOf (P.base.metric (-1)) x (1 / 2)) :=
    hball.of_isClosed_subset
      (isClosed_le (continuous_riemannianEDist (P.base.metric (-1)) x) continuous_const) hhalfsub
  have hlower : ∀ y ∈ riemannianClosedBallOf (P.base.metric (-1)) x (1 / 2),
      ∀ v : TangentSpace I3 y,
        (P.base.metric (-1)).inner y v v ≤ L ^ 2 * (P.base.metric 0).inner y v v := by
    intro y hy v
    have hRm : ∀ r ∈ Icc (-1 : ℝ) 0,
        normSq0S (P.base.metric r) y 4 (P.base.rm04 r y) ≤ K0 ^ 2 := by
      intro r hr
      exact hcurv r ⟨by linarith [hr.1], hr.2⟩ y (hhalfsub hy)
    have hh := (metric_inner_exp_bounds_of_curvature_bound P hP hslab' hreg' y hRm
      (s := -1) (t := 0) (by norm_num) (by norm_num) v).2
    have hpower : L ^ 2 = Real.exp (18 * K0) := by
      dsimp only [L]
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    rw [hpower]
    norm_num [ThreeSpace, Real.sqrt_sq hK0.le] at hh
    exact hh
  have hr : (1 : ℝ) / (4 * L) < (1 / 2) / L := by
    rw [div_div]
    apply div_lt_div_of_pos_left zero_lt_one (by positivity)
    nlinarith
  exact closedBall_isCompact_subset_of_local_metric_lower (P.base.metric (-1))
    (P.base.metric 0) x (by norm_num) hL hr hhalf hlower

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

noncomputable section

open Set
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Operator

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

theorem WindowedModelWitness.normalized_terminal_curvDerivNorm_bound_on_inner_ball
    (hS : IsSolutionOn S) {eps kappa K : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness eps kappa S x t) (heps : eps ≤ 1 / 4) (hK : 0 ≤ K)
    (hregular : interior D.carrier ⊆ D.regular)
    (hmodel : ∀ s ∈ Icc (-(4 : ℝ)) 0, ∀ y ∈
      riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint 2,
        W.model.rmNormSq s y ≤ K ^ 2)
    (m : ℕ) {y : M} (hy : y ∈ riemannianClosedBallOf
      (rescaledMetric S t (S.scalar t x) W.scalar_pos (-1)) x (1 / 2)) :
    curvDerivNorm m (rescaledMetric S t (S.scalar t x) W.scalar_pos 0) y ≤
      windowedShiConstant K m := by
  let P := parabolicSolution S t (S.scalar t x) W.scalar_pos W.time_mem
  have hP : IsSolutionOn P := parabolicSolution_isSolutionOn S hS t _ W.scalar_pos W.time_mem
  let K0 := sourceCurvatureBound 3 K
  have hK0 : 0 < K0 := sourceCurvatureBound_pos 3 hK
  have hsqrt : 0 < Real.sqrt K0 := Real.sqrt_pos.mpr hK0
  obtain ⟨hslab, hreg⟩ := W.normalized_fixed_window heps hregular
  have hslab' : Icc (-1 : ℝ) 0 ⊆ (parabolicInterval D t (S.scalar t x) W.time_mem).carrier :=
    (Icc_subset_Icc (by norm_num) le_rfl).trans hslab
  have hreg' : Ico (-1 : ℝ) 0 ⊆ (parabolicInterval D t (S.scalar t x) W.time_mem).regular := by
    intro r hr
    exact hreg ⟨by linarith [hr.1], hr.2⟩
  obtain ⟨hball, hcurv⟩ := W.unitBall_compact_curvature_bound heps hK hmodel
    (a := -1) (by norm_num)
  have hball' : IsCompact {z : M | riemannianEDistOf (P.base.metric (-1)) x z ≤
      ENNReal.ofReal (Real.sqrt K0 / Real.sqrt K0)} := by
    rw [div_self hsqrt.ne']
    exact hball
  have hcurv' : ∀ s ∈ Icc (-1 : ℝ) 0, ∀ z : M,
      riemannianEDistOf (P.base.metric (-1)) x z ≤
        ENNReal.ofReal (Real.sqrt K0 / Real.sqrt K0) →
      curvDerivNormSq 0 (P.base.metric s) z ≤ K0 ^ 2 := by
    intro s hs z hz
    rw [div_self hsqrt.ne'] at hz
    exact hcurv s ⟨by linarith [hs.1], hs.2⟩ z hz
  have hhalf : Real.sqrt K0 / (2 * Real.sqrt K0) = (1 : ℝ) / 2 := by
    field_simp
  have hy' : riemannianEDistOf (P.base.metric (-1)) x y ≤
      ENNReal.ofReal (Real.sqrt K0 / (2 * Real.sqrt K0)) := by
    rw [hhalf]
    exact hy
  have hh := KappaSolutions.shi_local_curvDerivNorm_terminal_of_solution_jets P hP
    (by simp [ThreeSpace]) (a := -1) (b := 0) (by norm_num) hK0 hsqrt hslab' hreg'
    x hball' hcurv' m 0 (by norm_num) y hy'
  change curvDerivNorm m (P.base.metric 0) y ≤ windowedShiConstant K m
  simpa [windowedShiConstant, ThreeSpace, K0] using hh

theorem WindowedModelWitness.normalized_terminal_scalar_gradient_bound_on_inner_ball
    (hS : IsSolutionOn S) {eps kappa K : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness eps kappa S x t) (heps : eps ≤ 1 / 4) (hK : 0 ≤ K)
    (hregular : interior D.carrier ⊆ D.regular)
    (hmodel : ∀ s ∈ Icc (-(4 : ℝ)) 0, ∀ y ∈
      riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint 2,
        W.model.rmNormSq s y ≤ K ^ 2)
    {y : M} (hy : y ∈ riemannianClosedBallOf
      (rescaledMetric S t (S.scalar t x) W.scalar_pos (-1)) x (1 / 2))
    (v : TangentSpace I3 y) :
    |(rescaledMetric S t (S.scalar t x) W.scalar_pos 0).inner y
      (gradientFun (rescaledMetric S t (S.scalar t x) W.scalar_pos 0)
        (metricScalarAt (rescaledMetric S t (S.scalar t x) W.scalar_pos 0)) y) v| ≤
      (27 * windowedShiConstant K 1) *
        Real.sqrt ((rescaledMetric S t (S.scalar t x) W.scalar_pos 0).inner y v v) := by
  let g := rescaledMetric S t (S.scalar t x) W.scalar_pos 0
  have hh := scalar_gradient_inner_le_nablaRm g y v
  have hb := W.normalized_terminal_curvDerivNorm_bound_on_inner_ball hS heps hK hregular hmodel 1 hy
  have hnorm : Real.sqrt (normSq0S g y 5 (iterCov g 4 (metricRm04 g) 1 y)) =
      curvDerivNorm 1 g y := rfl
  rw [hnorm] at hh
  have hstep := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb
    (by norm_num : (0 : ℝ) ≤ 27)) (Real.sqrt_nonneg (g.inner y v v))
  apply hh.trans
  norm_num [ThreeSpace] at hstep ⊢
  exact hstep

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

noncomputable section

open Set
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Operator

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

theorem exists_windowedModelWitness_normalized_terminal_scalar_lower_bound
    (K : ℝ) (hK : 0 ≤ K) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ 1 / (4 * Real.exp (9 * sourceCurvatureBound 3 K)) ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D},
        IsSolutionOn S → ∀ {eps kappa : ℝ} {x : M} {t : ℝ}
        (W : WindowedModelWitness eps kappa S x t), eps ≤ 1 / 4 →
        interior D.carrier ⊆ D.regular →
        (∀ s ∈ Icc (-(4 : ℝ)) 0, ∀ y ∈
          riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint 2,
            W.model.rmNormSq s y ≤ K ^ 2) →
        ∀ y ∈ riemannianClosedBallOf
          (rescaledMetric S t (S.scalar t x) W.scalar_pos 0) x rho,
          (1 / 2 : ℝ) ≤ metricScalarAt
            (rescaledMetric S t (S.scalar t x) W.scalar_pos 0) y := by
  let rho0 := 1 / (4 * Real.exp (9 * sourceCurvatureBound 3 K))
  have hrho0 : 0 < rho0 := by dsimp only [rho0]; positivity
  let B := 1 + 27 * windowedShiConstant K 1
  have hShi : 0 ≤ windowedShiConstant K 1 :=
    mul_nonneg (shiLocalUniformBound_nonneg _ _ _ _) (sourceCurvatureBound_pos 3 hK).le
  have hB : 0 < B := by dsimp only [B]; positivity
  let rho := min (rho0 / 4) (1 / (4 * B))
  have hrho : 0 < rho := lt_min (by positivity) (by positivity)
  have hrhole : rho ≤ rho0 := (min_le_left _ _).trans (by linarith)
  refine ⟨rho, hrho, hrhole, ?_⟩
  intro M _ _ _ _ _ D S hS eps kappa x t W heps hregular hmodel y hy
  let g := rescaledMetric S t (S.scalar t x) W.scalar_pos 0
  have hcenter : metricScalarAt g x = 1 := by
    change (parabolicSolution S t (S.scalar t x) W.scalar_pos W.time_mem).scalar 0 x = 1
    simp only [parabolicSolution_scalar, parabolicTime_zero, inv_mul_cancel₀ W.scalar_pos.ne']
  have hcapture := (W.terminal_ball_isCompact_subset_inner_ball hS heps hK hregular hmodel).2
  have hbound : ∀ z, riemannianEDistOf g x z < ENNReal.ofReal rho0 →
      ∀ v : TangentSpace I3 z,
        |(show ℝ from mfderiv I3 𝓘(ℝ) (metricScalarAt g) z v)| ≤ B * Real.sqrt (g.inner z v v) := by
    intro z hz v
    have hzin : z ∈ riemannianClosedBallOf
        (rescaledMetric S t (S.scalar t x) W.scalar_pos (-1)) x (1 / 2) :=
      hcapture hz.le
    have hgrad := W.normalized_terminal_scalar_gradient_bound_on_inner_ball
      hS heps hK hregular hmodel hzin v
    rw [inner_gradientFun] at hgrad
    change |(show ℝ from mfderiv I3 𝓘(ℝ) (metricScalarAt g) z v)| ≤
      (27 * windowedShiConstant K 1) * Real.sqrt (g.inner z v v) at hgrad
    exact hgrad.trans (mul_le_mul_of_nonneg_right (by dsimp only [B]; linarith)
      (Real.sqrt_nonneg _))
  have hrhosmall : rho < rho0 :=
    (min_le_left _ _).trans_lt (by linarith)
  have hdiff := DifferentialGeometry.Geometry.abs_sub_le_mul_of_mfderiv_bound_on_ball
    g ((metricScalar_smooth g).of_le (by simp)) x hB.le hbound hrho.le hrhosmall hy
  have hBrho : B * rho ≤ 1 / 4 := by
    have hh := min_le_right (rho0 / 4) (1 / (4 * B))
    have hmul := mul_le_mul_of_nonneg_left hh hB.le
    have hcancel : B * (1 / (4 * B)) = (1 : ℝ) / 4 := by field_simp
    rw [hcancel] at hmul
    exact hmul
  rw [hcenter] at hdiff
  have hsub := (abs_le.mp (hdiff.trans hBrho)).1
  change (1 / 2 : ℝ) ≤ metricScalarAt g y
  linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
