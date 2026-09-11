import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedSourceCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalLocalBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalCurvatureJets


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
  have hmaps : MapsTo (parabolicTime t (S.scalar t x)) (Icc (-modelDepth eps) 0)
      (Icc (t - (eps * S.scalar t x)⁻¹) t) := by
    intro s hs
    constructor
    · simpa only [parabolicTime, modelDepth, div_eq_mul_inv, mul_inv, neg_mul, sub_eq_add_neg, add_comm]
        using add_le_add_right (div_le_div_of_nonneg_right hs.1 W.scalar_pos.le) t
    · exact add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hs.2 W.scalar_pos.le)
  constructor
  · intro s hs
    exact W.window_mem (hmaps ⟨by linarith [hs.1], hs.2⟩)
  · intro s hs
    apply hregular
    apply interior_mono W.window_mem
    rw [interior_Icc]
    have hl : -modelDepth eps < s := by linarith [hs.1]
    constructor
    · simpa only [parabolicTime, modelDepth, div_eq_mul_inv, mul_inv, neg_mul, sub_eq_add_neg, add_comm]
        using add_lt_add_right (div_lt_div_of_pos_right hl W.scalar_pos) t
    · have hh := div_neg_of_neg_of_pos hs.2 W.scalar_pos
      change t + s / S.scalar t x < t
      linarith


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
