import DifferentialGeometry.Geometry.Connection.LeviCivita.Scaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.RicciNorm
import DifferentialGeometry.Geometry.Operator.Scaling
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Scaling


open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [SigmaCompactSpace M] [T2Space M]

def parabolicTime (τ R s : Real) : Real :=
  τ + s / R

def parabolicBackward (τ R t : Real) : Real :=
  R * (t - τ)

@[simp] theorem parabolicTime_zero (τ R : Real) :
    parabolicTime τ R 0 = τ := by
  simp [parabolicTime]

@[simp] theorem parabolicBackward_self (τ R : Real) :
    parabolicBackward τ R τ = 0 := by
  simp [parabolicBackward]

theorem parabolicTime_back {τ R t : Real} (hR : R ≠ 0) :
    parabolicTime τ R (parabolicBackward τ R t) = t := by
  unfold parabolicTime parabolicBackward
  field_simp [hR]
  ring

theorem parabolicBackward_time {τ R s : Real} (hR : R ≠ 0) :
    parabolicBackward τ R (parabolicTime τ R s) = s := by
  unfold parabolicTime parabolicBackward
  field_simp [hR]
  ring

private theorem mul_parabolicTime_eq {τ R s : Real} (hR : R ≠ 0) :
    R * parabolicTime τ R s = R * τ + s := by
  unfold parabolicTime
  field_simp [hR]

def parabolicInterval
    (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval) (τ R : Real) (hτ : τ ∈ D.carrier) : DifferentialGeometry.Geometry.Curvature.RealTimeInterval where
  carrier := {s : Real | parabolicTime τ R s ∈ D.carrier}
  regular := {s : Real | parabolicTime τ R s ∈ D.regular}
  initial := 0
  initial_mem := by
    simpa [parabolicTime] using hτ
  regular_subset := by
    intro s hs
    exact D.regular_subset hs
  regular_isOpen := by
    have hcont : Continuous (fun r : Real => parabolicTime τ R r) := by
      unfold parabolicTime
      fun_prop
    exact hcont.isOpen_preimage _ D.regular_isOpen
  regular_mem_nhds := by
    intro s hs
    have hcont : ContinuousAt (fun r : Real => parabolicTime τ R r) s := by
      unfold parabolicTime
      fun_prop
    simpa [Set.preimage] using hcont.preimage_mem_nhds (D.regular_mem_nhds hs)

@[simp] theorem parabolicInterval_carrier
    (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval) (τ R : Real)
    (hτ : τ ∈ D.carrier) :
    (parabolicInterval D τ R hτ).carrier =
      {s : Real | parabolicTime τ R s ∈ D.carrier} := by
  rfl

@[simp] theorem parabolicInterval_regular
    (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval) (τ R : Real)
    (hτ : τ ∈ D.carrier) :
    (parabolicInterval D τ R hτ).regular =
      {s : Real | parabolicTime τ R s ∈ D.regular} := by
  rfl

theorem parabolicInterval_closedOpen_carrier
    {T τ R : Real} (hT : 0 < T) (hR : 0 < R)
    (hτ : τ ∈ (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 T
      hT).carrier) :
    (parabolicInterval (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 T hT)
        τ R hτ).carrier =
      Set.Ico (-(R * τ)) (R * (T - τ)) := by
  ext s
  constructor
  · intro hs
    rcases hs with ⟨hlo, hhi⟩
    dsimp [parabolicTime] at hlo hhi
    have heq : R * parabolicTime τ R s = R * τ + s :=
      mul_parabolicTime_eq (τ := τ) (R := R) (s := s) (ne_of_gt hR)
    have hlo' : 0 <= R * parabolicTime τ R s := by
      exact mul_nonneg (le_of_lt hR) hlo
    have hhi' : R * parabolicTime τ R s < R * T := by
      exact mul_lt_mul_of_pos_left hhi hR
    constructor <;> nlinarith
  · intro hs
    rcases hs with ⟨hlo, hhi⟩
    have heq : R * parabolicTime τ R s = R * τ + s :=
      mul_parabolicTime_eq (τ := τ) (R := R) (s := s) (ne_of_gt hR)
    have hlo' : 0 <= R * parabolicTime τ R s := by
      rw [heq]
      nlinarith
    have hhi' : R * parabolicTime τ R s < R * T := by
      rw [heq]
      nlinarith
    constructor
    · have hdiv : 0 <= (R * parabolicTime τ R s) / R := div_nonneg hlo' (le_of_lt hR)
      rwa [mul_div_cancel_left₀ (parabolicTime τ R s) (ne_of_gt hR)] at hdiv
    · have hdiv : (R * parabolicTime τ R s) / R < (R * T) / R :=
        div_lt_div_of_pos_right hhi' hR
      rwa [mul_div_cancel_left₀ (parabolicTime τ R s) (ne_of_gt hR),
        mul_div_cancel_left₀ T (ne_of_gt hR)] at hdiv

theorem parabolicInterval_closedOpen_regular
    {T τ R : Real} (hT : 0 < T) (hR : 0 < R)
    (hτ : τ ∈ (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 T
      hT).carrier) :
    (parabolicInterval (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 T hT)
        τ R hτ).regular =
      Set.Ioo (-(R * τ)) (R * (T - τ)) := by
  ext s
  constructor
  · intro hs
    rcases hs with ⟨hlo, hhi⟩
    dsimp [parabolicTime] at hlo hhi
    have heq : R * parabolicTime τ R s = R * τ + s :=
      mul_parabolicTime_eq (τ := τ) (R := R) (s := s) (ne_of_gt hR)
    have hlo' : 0 < R * parabolicTime τ R s := by
      exact mul_pos hR hlo
    have hhi' : R * parabolicTime τ R s < R * T := by
      exact mul_lt_mul_of_pos_left hhi hR
    constructor <;> nlinarith
  · intro hs
    rcases hs with ⟨hlo, hhi⟩
    have heq : R * parabolicTime τ R s = R * τ + s :=
      mul_parabolicTime_eq (τ := τ) (R := R) (s := s) (ne_of_gt hR)
    have hlo' : 0 < R * parabolicTime τ R s := by
      rw [heq]
      nlinarith
    have hhi' : R * parabolicTime τ R s < R * T := by
      rw [heq]
      nlinarith
    constructor
    · have hdiv : 0 < (R * parabolicTime τ R s) / R := div_pos hlo' hR
      rwa [mul_div_cancel_left₀ (parabolicTime τ R s) (ne_of_gt hR)] at hdiv
    · have hdiv : (R * parabolicTime τ R s) / R < (R * T) / R :=
        div_lt_div_of_pos_right hhi' hR
      rwa [mul_div_cancel_left₀ (parabolicTime τ R s) (ne_of_gt hR),
        mul_div_cancel_left₀ T (ne_of_gt hR)] at hdiv

def parabolicFamily
    (G : SolutionFamily (I := I) (M := M)) (τ R : Real) (hR : 0 < R) :
    SolutionFamily (I := I) (M := M) where
  metric s := scaleMetric (I := I) R hR (G.metric (parabolicTime τ R s))

def parabolicBackwardFamily
    (G : SolutionFamily (I := I) (M := M)) (τ R : Real) (hR : 0 < R) :
    SolutionFamily (I := I) (M := M) where
  metric t := scaleMetric (I := I) R⁻¹ (inv_pos.mpr hR)
    (G.metric (parabolicBackward τ R t))

def parabolicSolution
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier) :
    SolutionOn (I := I) (M := M) (parabolicInterval D τ R hτ) where
  base := parabolicFamily (I := I) S.base τ R hR

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [SigmaCompactSpace M]
    [T2Space M] in
@[simp] theorem parabolicSolution_metric
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier) :
    (parabolicSolution (I := I) S τ R hR hτ).base.metric =
      fun s => scaleMetric (I := I) R hR (S.base.metric (parabolicTime τ R s)) := by
  rfl

omit [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem parabolicSolution_connection
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier) :
    (parabolicSolution (I := I) S τ R hR hτ).base.connection =
      fun s => S.base.connection (parabolicTime τ R s) := by
  funext s
  simp [parabolicSolution, parabolicFamily, SolutionFamily.connection,
    DifferentialGeometry.Geometry.Connection.lcConn_scaleMetric]

omit [SigmaCompactSpace M] in
@[simp] theorem parabolicSolution_ricci
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier) :
    (parabolicSolution (I := I) S τ R hR hτ).base.ricci =
      fun s => S.base.ricci (parabolicTime τ R s) := by
  funext s
  simp [parabolicSolution, parabolicFamily, SolutionFamily.ricci, metricRicci,
    DifferentialGeometry.Geometry.Curvature.metricRicci,
      DifferentialGeometry.Geometry.Curvature.metricCov,
      DifferentialGeometry.Geometry.Connection.lcConn_scaleMetric]

omit [SigmaCompactSpace M] in
private theorem metricRm04_scaleMetric
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x : M) :
    DifferentialGeometry.Geometry.Curvature.metricRm04 (I := I) (M := M)
      (scaleMetric (I := I) c hc g) x =
      c • DifferentialGeometry.Geometry.Curvature.metricRm04 (I := I) (M := M) g x := by
  ext v
  have hv :
      v = DifferentialGeometry.Geometry.Curvature.vec4 (I := I) (v 0) (v 1) (v 2) (v 3) := by
    funext i
    fin_cases i <;> simp [DifferentialGeometry.Geometry.Curvature.vec4]
  rw [hv]
  simp [DifferentialGeometry.Geometry.Curvature.metricRm04,
    DifferentialGeometry.Geometry.Curvature.metricCov, scaleMetric_inner,
    DifferentialGeometry.Geometry.Connection.lcConn_scaleMetric, smul_eq_mul]

omit [SigmaCompactSpace M] in
@[simp] theorem parabolicSolution_rm04
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier)
    (s : Real) (x : M) :
    (parabolicSolution (I := I) S τ R hR hτ).base.rm04 s x =
      R • S.base.rm04 (parabolicTime τ R s) x := by
  simpa [parabolicSolution, parabolicFamily, SolutionFamily.rm04] using
    metricRm04_scaleMetric (I := I) R hR (S.base.metric (parabolicTime τ R s)) x

omit [SigmaCompactSpace M] in
theorem parabolicRmNormSq
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier)
    (s : Real) (x : M) :
    Tensor0SBundle.normSq0S (I := I)
        ((parabolicSolution (I := I) S τ R hR hτ).base.metric s) x 4
        ((parabolicSolution (I := I) S τ R hR hτ).base.rm04 s x) =
      (R⁻¹) ^ 2 * Tensor0SBundle.normSq0S (I := I)
        (S.base.metric (parabolicTime τ R s)) x 4
        (S.base.rm04 (parabolicTime τ R s) x) := by
  rw [parabolicSolution_rm04, show
    (parabolicSolution (I := I) S τ R hR hτ).base.metric s =
      scaleMetric (I := I) R hR (S.base.metric (parabolicTime τ R s)) by rfl,
    Tensor0SBundle.normSq0S_scale, Tensor0SBundle.normSq0S_smul]
  field_simp [ne_of_gt hR]

omit [SigmaCompactSpace M] in
private theorem parabolicNablaRic_eq
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier)
    (s : Real) (x : M) :
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 ((parabolicSolution (I := I) S τ R hR hτ).family.connection s)
        ((parabolicSolution (I := I) S τ R hR hτ).ricci s) x =
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 (S.family.connection (parabolicTime τ R s))
        (S.ricci (parabolicTime τ R s)) x := by
  refine totalNabla0SFun_congr (𝕜 := Real) (E := E) (H := H)
    (I := I) (M := M) 2 ?_ ?_ x
  · have h := congrFun (parabolicSolution_connection (I := I) S τ R hR hτ) s
    simp [SolutionOn.family] at h ⊢
  · have h := congrFun (parabolicSolution_ricci (I := I) S τ R hR hτ) s
    simp [SolutionOn.ricci] at h ⊢

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem metricTensorField_scaleMetric
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x : M) :
    metricTensorField (I := I) (scaleMetric (I := I) c hc g) x =
      c • metricTensorField (I := I) g x := by
  ext v
  simp [metricTensorField_apply, scaleMetric_inner, smul_eq_mul]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem metricTracePair0SAt_scaleMetric
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    {x : M} (B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 x) :
    DifferentialGeometry.Geometry.Operator.metricTracePair0SAt (I := I)
      (scaleMetric (I := I) c hc g) B =
      c⁻¹ * DifferentialGeometry.Geometry.Operator.metricTracePair0SAt (I := I) g B := by
  classical
  let basis : Module.Basis (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E)
    Real
      (TangentSpace I x) := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis
        (I := I) x
  let gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
    fun k l =>
      DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChartComponent (I := I) g x k
        l
        (extChartAt I x x)
  have hinv : MetricInverseInBasis (I := I) g x basis gInv :=
    Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
      (I := I) g x
  have hinvScale :
      MetricInverseInBasis (I := I) (scaleMetric (I := I) c hc g) x basis
        (fun i j => c⁻¹ * gInv i j) :=
    metricInvBasis_scale (I := I) c hc g basis gInv hinv
  rw [DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_eq_sum_basis (I := I)
      (scaleMetric (I := I) c hc g) basis (fun i j => c⁻¹ * gInv i j) hinvScale,
    DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_eq_sum_basis (I := I) g basis gInv
      hinv]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  ring

omit [SigmaCompactSpace M] [T2Space M] in
theorem parabolicSolution_scalar
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier) :
    (parabolicSolution (I := I) S τ R hR hτ).scalar =
      fun s x => R⁻¹ * S.scalar (parabolicTime τ R s) x := by
  funext s x
  simp [SolutionOn.scalar, SolutionFamily.scalar_apply, parabolicSolution, parabolicFamily,
    SolutionFamily.ricciAt, metricRicciAt, DifferentialGeometry.Geometry.Curvature.metricRicciAt,
    DifferentialGeometry.Geometry.Curvature.metricCov,
      DifferentialGeometry.Geometry.Connection.lcConn_scaleMetric,
    metricTracePair0SAt_scaleMetric]

omit [SigmaCompactSpace M] in
@[simp] theorem parabolicSolution_ricciNorm
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier) :
    ricciNorm (I := I) (parabolicSolution (I := I) S τ R hR hτ) =
      fun s x => R⁻¹ * R⁻¹ * ricciNorm (I := I) S (parabolicTime τ R s) x := by
  funext s x
  have hRic :
      (parabolicSolution (I := I) S τ R hR hτ).ricci s x =
        S.ricci (parabolicTime τ R s) x := by
    have h := parabolicSolution_ricci (I := I) S τ R hR hτ
    change ((parabolicSolution (I := I) S τ R hR hτ).base.ricci s) x =
      (S.base.ricci (parabolicTime τ R s)) x
    exact congrArg (fun A => A x) (congrFun h s)
  rw [ricciNorm, hRic]
  simpa [SolutionOn.family, parabolicSolution, parabolicFamily, ricciNorm, mul_assoc] using
    (normSq0S_two_scale (I := I) R hR (S.family.metric (parabolicTime τ R s))
      (x := x) (A := S.ricci (parabolicTime τ R s) x))

omit [SigmaCompactSpace M] in
private theorem parabolicRicciNormGrad_eq
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier)
    {s : Real} (hs : s ∈ (parabolicInterval D τ R hτ).carrier) (x : M) :
    DifferentialGeometry.Geometry.Operator.gradientFun (I := I)
        ((parabolicSolution (I := I) S τ R hR hτ).family.metric s)
        (ricciNorm (I := I) (parabolicSolution (I := I) S τ R hR hτ) s) x =
      (R⁻¹ * R⁻¹ * R⁻¹) •
        DifferentialGeometry.Geometry.Operator.gradientFun (I := I)
          (S.family.metric (parabolicTime τ R s))
          (ricciNorm (I := I) S (parabolicTime τ R s)) x := by
  have hdiff :
      MDifferentiableAt I 𝓘(Real, Real)
        (ricciNorm (I := I) S (parabolicTime τ R s)) x :=
    hS.ricciNormSpace (parabolicTime τ R s) hs x
  calc
    DifferentialGeometry.Geometry.Operator.gradientFun (I := I)
        ((parabolicSolution (I := I) S τ R hR hτ).family.metric s)
        (ricciNorm (I := I) (parabolicSolution (I := I) S τ R hR hτ) s) x =
        DifferentialGeometry.Geometry.Operator.gradientFun (I := I)
          (scaleMetric (I := I) R hR (S.family.metric (parabolicTime τ R s)))
          ((R⁻¹ * R⁻¹) • ricciNorm (I := I) S (parabolicTime τ R s)) x := by
          have hfun :
              ricciNorm (I := I) (parabolicSolution (I := I) S τ R hR hτ) s =
                (R⁻¹ * R⁻¹) • ricciNorm (I := I) S (parabolicTime τ R s) := by
            funext y
            have h := congrFun
              (congrFun (parabolicSolution_ricciNorm (I := I) S τ R hR hτ) s) y
            rw [h]
            simp [Pi.smul_apply, smul_eq_mul, mul_assoc]
          rw [hfun]
          simp [SolutionOn.family, parabolicSolution, parabolicFamily]
    _ =
        R⁻¹ • DifferentialGeometry.Geometry.Operator.gradientFun (I := I)
          (S.family.metric (parabolicTime τ R s))
          ((R⁻¹ * R⁻¹) • ricciNorm (I := I) S (parabolicTime τ R s)) x := by
          rw [DifferentialGeometry.Geometry.Operator.gradientFun_scale]
    _ =
        R⁻¹ • ((R⁻¹ * R⁻¹) •
          DifferentialGeometry.Geometry.Operator.gradientFun (I := I)
            (S.family.metric (parabolicTime τ R s))
            (ricciNorm (I := I) S (parabolicTime τ R s)) x) := by
          rw [DifferentialGeometry.Geometry.Operator.gradientFun_const_smul (I := I)
            (S.family.metric (parabolicTime τ R s)) (a := R⁻¹ * R⁻¹) hdiff]
    _ =
        (R⁻¹ * R⁻¹ * R⁻¹) •
          DifferentialGeometry.Geometry.Operator.gradientFun (I := I)
            (S.family.metric (parabolicTime τ R s))
            (ricciNorm (I := I) S (parabolicTime τ R s)) x := by
          simp [smul_smul, mul_comm]

omit [SigmaCompactSpace M] [T2Space M] in
private theorem lcConnectionSmooth
    (g : SmoothRiemannianMetric I M) :
    CovariantDerivative.ContMDiffCovariantDerivative
      (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I) g) ∞ := by
  exact
    ⟨DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) g (u := Set.univ) isOpen_univ⟩

omit [SigmaCompactSpace M] in
theorem metricFamilySmooth_parabolic
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier) :
    DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn (I := I) (M := M)
      (parabolicInterval D τ R hτ)
      (parabolicSolution (I := I) S τ R hR hτ).family.metric := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x X Y
    have hOld := hS.smoothMetric.coeff x X Y
    have haff_global : ContDiff Real ∞ (fun s : Real => parabolicTime τ R s) := by
      unfold parabolicTime
      exact contDiff_const.add (contDiff_id.div_const R)
    have hmaps :
        Set.MapsTo (fun s : Real => parabolicTime τ R s)
          (parabolicInterval D τ R hτ).regular D.regular := by
      intro s hs
      exact hs
    have hcomp :
        ContDiffOn Real ∞
          (fun s : Real => (S.base.metric (parabolicTime τ R s)).inner x X Y)
          (parabolicInterval D τ R hτ).regular := by
      simpa [Function.comp_def] using
        hOld.comp haff_global.contDiffOn hmaps
    simpa [SolutionOn.family, parabolicSolution, parabolicFamily, scaleMetric_inner, smul_eq_mul]
      using ContDiffOn.const_smul R hcomp
  · intro x X Y
    have hOld := hS.smoothMetric.coeff_cont x X Y
    have htime : Continuous (fun s : Real => parabolicTime τ R s) := by
      unfold parabolicTime
      exact continuous_const.add (continuous_id.div_const R)
    have hmaps :
        Set.MapsTo (fun s : Real => parabolicTime τ R s)
          (parabolicInterval D τ R hτ).carrier D.carrier := by
      intro s hs
      exact hs
    have hcomp :
        ContinuousOn
          (fun s : Real => (S.base.metric (parabolicTime τ R s)).inner x X Y)
          (parabolicInterval D τ R hτ).carrier := by
      simpa [Function.comp_def] using
        hOld.comp htime.continuousOn hmaps
    change ContinuousOn
      (fun t : Real => R * (S.base.metric (parabolicTime τ R t)).inner x X Y)
      (parabolicInterval D τ R hτ).carrier
    rw [show (fun t : Real =>
        R * (S.base.metric (parabolicTime τ R t)).inner x X Y) =
        R • fun t : Real => (S.base.metric (parabolicTime τ R t)).inner x X Y by
      funext t
      rfl]
    exact hcomp.const_smul R
  · have hmaps :
        Set.MapsTo (fun s : Real => parabolicTime τ R s)
          (parabolicInterval D τ R hτ).carrier D.carrier := by
      intro s hs
      exact hs
    have htime : Continuous (fun s : Real => parabolicTime τ R s) := by
      unfold parabolicTime
      exact continuous_const.add (continuous_id.div_const R)
    have hcomp :=
      DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.comp_time (I := I)
        (M := M)
        hS.smoothMetric.metricTensor_cont htime hmaps
    have hscale :=
      DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.const_smul (I := I)
        (M := M)
        R hcomp
    simpa [SolutionOn.family, parabolicSolution, parabolicFamily, metricTensorField_scaleMetric]
      using hscale
  · intro Idx _ frame u hframe i j
    have hOld :
        ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
          (fun p : Real × M =>
            (S.family.metric p.1).inner p.2 (frame i p.2) (frame j p.2))
          (D.regular ×ˢ u) :=
      hS.smoothMetric.frameCompSmooth frame hframe i j
    have htime :
        ContMDiff (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
          (fun p : Real × M => parabolicTime τ R p.1) := by
      unfold parabolicTime
      exact contMDiff_const.add (contMDiff_fst.div_const R)
    have hmapSmooth :
        ContMDiff (𝓘(Real, Real).prod I) (𝓘(Real, Real).prod I) ∞
          (fun p : Real × M => (parabolicTime τ R p.1, p.2)) :=
      htime.prodMk contMDiff_snd
    have hmaps :
        Set.MapsTo (fun p : Real × M => (parabolicTime τ R p.1, p.2))
          ((parabolicInterval D τ R hτ).regular ×ˢ u) (D.regular ×ˢ u) := by
      intro p hp
      exact ⟨hp.1, hp.2⟩
    have hcomp :
        ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
          (fun p : Real × M =>
            (S.base.metric (parabolicTime τ R p.1)).inner p.2
              (frame i p.2) (frame j p.2))
          ((parabolicInterval D τ R hτ).regular ×ˢ u) := by
      simpa [SolutionOn.family, Function.comp_def] using
        hOld.comp hmapSmooth.contMDiffOn hmaps
    have hscale :
        ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
          (fun p : Real × M =>
            R * (S.base.metric (parabolicTime τ R p.1)).inner p.2
              (frame i p.2) (frame j p.2))
          ((parabolicInterval D τ R hτ).regular ×ˢ u) :=
      (contMDiffOn_const (c := R)).mul hcomp
    simpa [SolutionOn.family, parabolicSolution, parabolicFamily, scaleMetric_inner,
      smul_eq_mul] using hscale

omit [SigmaCompactSpace M] in
omit [T2Space M] in
theorem connectionFamilySmooth_parabolic
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier) :
    DifferentialGeometry.Geometry.Connection.ConnectionFamilySmoothOn (I := I) (M := M)
      (parabolicSolution (I := I) S τ R hR hτ).family := by
  intro t
  simpa [SolutionOn.family, parabolicSolution, parabolicFamily, SolutionFamily.connection,
    DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.connectionAt]
    using lcConnectionSmooth (I := I)
      ((parabolicSolution (I := I) S τ R hR hτ).base.metric (t : Real))

omit [SigmaCompactSpace M] in
omit [T2Space M] in
theorem leviCivita_parabolic
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier) :
    DifferentialGeometry.Geometry.Connection.IsLeviCivitaFamilyOn (I := I)
      (parabolicSolution (I := I) S τ R hR hτ).family := by
  intro t
  refine ⟨(parabolicSolution (I := I) S τ R hR hτ).metricCompatible t, ?_⟩
  simpa [SolutionOn.family, parabolicSolution, parabolicFamily, SolutionFamily.connection,
    DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.connectionAt]
    using DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_isTorsionFree
      (I := I) ((parabolicSolution (I := I) S τ R hR hτ).base.metric (t : Real))

omit [SigmaCompactSpace M] in
theorem metricVariation_parabolic
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier) :
    MetricVariationEquationOn (I := I)
      (parabolicSolution (I := I) S τ R hR hτ) := by
  intro t x X Y
  let tOld : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D :=
    ⟨parabolicTime τ R (t : Real), t.2⟩
  have hOld := hS.equation tOld x X Y
  have htime :
      HasDerivWithinAt (fun s : Real => parabolicTime τ R s) R⁻¹
        (parabolicInterval D τ R hτ).carrier (t : Real) := by
    simpa [parabolicTime, one_div] using
      (((hasDerivWithinAt_id (t : Real)
        (parabolicInterval D τ R hτ).carrier).div_const R).const_add τ)
  have hmaps :
      Set.MapsTo (fun s : Real => parabolicTime τ R s)
        (parabolicInterval D τ R hτ).carrier D.carrier := by
    intro s hs
    exact hs
  have hcomp := hOld.comp (x := (t : Real)) htime hmaps
  have hscaled := hcomp.const_mul R
  simpa [MetricVariationEquationOn,
    DifferentialGeometry.PDE.RicciFlow.MetricVariationEquationOn,
    SolutionOn.family, parabolicSolution, parabolicFamily, RicciAtFamily.toTensorField,
    SolutionFamily.ricciAt, metricRicciAt, DifferentialGeometry.Geometry.Curvature.metricRicciAt,
    DifferentialGeometry.Geometry.Curvature.metricCov, scaleMetric_inner,
      DifferentialGeometry.Geometry.Connection.lcConn_scaleMetric,
    tOld]
    using
      (hscaled.congr_deriv (by
        simp [tOld, SolutionFamily.ricciAt, metricRicciAt,
          DifferentialGeometry.Geometry.Curvature.metricRicciAt,
          DifferentialGeometry.Geometry.Curvature.metricCov]
        field_simp [ne_of_gt hR]))

omit [SigmaCompactSpace M] in
theorem parabolicSolution_isSolutionOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier) :
    IsSolutionOn (I := I) (parabolicSolution (I := I) S τ R hR hτ) where
  smoothMetric := metricFamilySmooth_parabolic (I := I) S hS τ R hR hτ
  smoothConnection := connectionFamilySmooth_parabolic (I := I) S τ R hR hτ
  equation := metricVariation_parabolic (I := I) S hS τ R hR hτ
  scalarCont := by
    have htime : Continuous (fun q : Real × M => parabolicTime τ R q.1) := by
      unfold parabolicTime
      exact continuous_const.add (continuous_fst.div_const R)
    have hmap : Continuous (fun q : Real × M => (parabolicTime τ R q.1, q.2)) :=
      htime.prodMk continuous_snd
    have hmapOn : ContinuousOn (fun q : Real × M => (parabolicTime τ R q.1, q.2))
        ((parabolicInterval D τ R hτ).carrier ×ˢ (Set.univ : Set M)) :=
      hmap.continuousOn
    have hmaps : Set.MapsTo (fun q : Real × M => (parabolicTime τ R q.1, q.2))
        ((parabolicInterval D τ R hτ).carrier ×ˢ (Set.univ : Set M))
        (D.carrier ×ˢ (Set.univ : Set M)) := by
      intro q hq
      exact ⟨hq.1, trivial⟩
    have hcomp :
        ContinuousOn
          (fun q : Real × M => S.scalar (parabolicTime τ R q.1) q.2)
          ((parabolicInterval D τ R hτ).carrier ×ˢ (Set.univ : Set M)) := by
      have h := hS.scalarCont.comp hmapOn hmaps
      simpa [Function.comp_def] using h
    have hscale :
        ContinuousOn
          (fun q : Real × M => R⁻¹ * S.scalar (parabolicTime τ R q.1) q.2)
          ((parabolicInterval D τ R hτ).carrier ×ˢ (Set.univ : Set M)) :=
      continuousOn_const.mul hcomp
    have hscalar_fun :
        (fun q : Real × M =>
          (parabolicSolution (I := I) S τ R hR hτ).scalar q.1 q.2) =
            fun q : Real × M => R⁻¹ * S.scalar (parabolicTime τ R q.1) q.2 := by
      funext q
      rw [parabolicSolution_scalar (I := I) S τ R hR hτ]
    rw [hscalar_fun]
    exact hscale
  scalarTime := by
    intro K t ht hK x
    let shift : Real -> Real := fun s => parabolicTime τ R s
    have ht' : shift t ∈ shift '' K := ⟨t, ht, rfl⟩
    have hK' : shift '' K ⊆ D.carrier := by
      intro r hr
      rcases hr with ⟨s, hs, rfl⟩
      exact hK hs
    have hOld := hS.scalarTime (K := shift '' K) (t := shift t) ht' hK' x
    have hshift : DifferentiableWithinAt Real shift K t := by
      simpa [shift, parabolicTime] using
        ((differentiableWithinAt_fun_id (𝕜 := Real) (s := K) (x := t)).div_const R).const_add τ
    have hmaps : Set.MapsTo shift K (shift '' K) := by
      intro s hs
      exact ⟨s, hs, rfl⟩
    have hcomp := hOld.comp t hshift hmaps
    have hscaled := hcomp.const_mul R⁻¹
    have hscalar :
        (fun s : Real => (parabolicSolution (I := I) S τ R hR hτ).scalar s x) =
          fun s : Real => R⁻¹ * S.scalar (parabolicTime τ R s) x := by
      funext s
      exact congrFun (congrFun (parabolicSolution_scalar (I := I) S τ R hR hτ) s) x
    rw [hscalar]
    simpa [shift, Function.comp_def] using hscaled
  ricciCont := by
    have hmaps :
        Set.MapsTo (fun s : Real => parabolicTime τ R s)
          (parabolicInterval D τ R hτ).carrier D.carrier := by
      intro s hs
      exact hs
    have htime : Continuous (fun s : Real => parabolicTime τ R s) := by
      unfold parabolicTime
      exact continuous_const.add (continuous_id.div_const R)
    have hcont :=
      DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.comp_time (I := I)
        (M := M)
        hS.ricciCont htime hmaps
    simpa [SolutionOn.ricci, parabolicSolution_ricci (I := I) S τ R hR hτ] using hcont
  rm04Cont := by
    have hmaps :
        Set.MapsTo (fun s : Real => parabolicTime τ R s)
          (parabolicInterval D τ R hτ).carrier D.carrier := by
      intro s hs
      exact hs
    have htime : Continuous (fun s : Real => parabolicTime τ R s) := by
      unfold parabolicTime
      exact continuous_const.add (continuous_id.div_const R)
    have hcomp :=
      DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.comp_time (I := I)
        (M := M)
        hS.rm04Cont htime hmaps
    have hscale :=
      DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet.const_smul (I := I)
        (M := M)
        R hcomp
    simpa [parabolicSolution_rm04 (I := I) S τ R hR hτ] using hscale
  ricciNormSpace := by
    intro t ht x
    have hOld :
        MDifferentiableAt I 𝓘(Real, Real)
          (ricciNorm (I := I) S (parabolicTime τ R t)) x :=
      hS.ricciNormSpace (parabolicTime τ R t) ht x
    have hscaled := hOld.const_smul (R⁻¹ * R⁻¹)
    have hfun :
        ricciNorm (I := I) (parabolicSolution (I := I) S τ R hR hτ) t =
          (R⁻¹ * R⁻¹) • ricciNorm (I := I) S (parabolicTime τ R t) := by
      funext y
      have h := congrFun
        (congrFun (parabolicSolution_ricciNorm (I := I) S τ R hR hτ) t) y
      rw [h]
      simp [Pi.smul_apply, smul_eq_mul, mul_assoc]
    simpa [hfun] using hscaled
  ricciNormGrad := by
    intro t ht x
    have hOld :
        MDiffAt (T% fun y : M =>
          DifferentialGeometry.Geometry.Operator.gradientFun (I := I)
            (S.family.metric (parabolicTime τ R t))
            (ricciNorm (I := I) S (parabolicTime τ R t)) y) x :=
      hS.ricciNormGrad (parabolicTime τ R t) ht x
    have hscaled :
        MDiffAt (T% fun y : M =>
          (R⁻¹ * R⁻¹ * R⁻¹) •
            DifferentialGeometry.Geometry.Operator.gradientFun (I := I)
              (S.family.metric (parabolicTime τ R t))
              (ricciNorm (I := I) S (parabolicTime τ R t)) y) x := by
      simpa [Pi.smul_apply] using
        (mdifferentiableAt_const (I := I) (c := R⁻¹ * R⁻¹ * R⁻¹)).smul_section hOld
    have hpt : ∀ y : M,
        DifferentialGeometry.Geometry.Operator.gradientFun (I := I)
          ((parabolicSolution (I := I) S τ R hR hτ).family.metric t)
          (ricciNorm (I := I) (parabolicSolution (I := I) S τ R hR hτ) t) y =
          (R⁻¹ * R⁻¹ * R⁻¹) •
            DifferentialGeometry.Geometry.Operator.gradientFun (I := I)
              (S.family.metric (parabolicTime τ R t))
              (ricciNorm (I := I) S (parabolicTime τ R t)) y := by
      intro y
      exact parabolicRicciNormGrad_eq (I := I) S hS τ R hR hτ ht y
    have htotal :
        (T% fun y : M =>
          DifferentialGeometry.Geometry.Operator.gradientFun (I := I)
            ((parabolicSolution (I := I) S τ R hR hτ).family.metric t)
            (ricciNorm (I := I) (parabolicSolution (I := I) S τ R hR hτ) t) y) =
          (T% fun y : M =>
            (R⁻¹ * R⁻¹ * R⁻¹) •
              DifferentialGeometry.Geometry.Operator.gradientFun (I := I)
                (S.family.metric (parabolicTime τ R t))
              (ricciNorm (I := I) S (parabolicTime τ R t)) y) := by
      funext y
      rw [hpt y]
    rw [htotal]
    exact hscaled

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [SigmaCompactSpace M]
    [T2Space M] in
theorem parabolicBackward_parabolic_metric
    (G : SolutionFamily (I := I) (M := M))
    (τ R : Real) (hR : 0 < R) (t : Real) :
    ((parabolicBackwardFamily (I := I) (parabolicFamily (I := I) G τ R hR)
      τ R hR).metric t).inner = (G.metric t).inner := by
  funext x
  ext v w
  simp only [parabolicBackwardFamily, parabolicFamily, scaleMetric_inner]
  rw [parabolicTime_back (τ := τ) (R := R) (t := t) (ne_of_gt hR)]
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hR), one_mul]

omit [SigmaCompactSpace M] [T2Space M] in
theorem parabolicBackward_parabolic_connection
    (G : SolutionFamily (I := I) (M := M))
    (τ R : Real) (hR : 0 < R) (t : Real) :
    (parabolicBackwardFamily (I := I) (parabolicFamily (I := I) G τ R hR)
      τ R hR).connection t = G.connection t := by
  simp [parabolicBackwardFamily, parabolicFamily, SolutionFamily.connection,
    DifferentialGeometry.Geometry.Connection.lcConn_scaleMetric, parabolicTime_back (τ := τ) (R := R)
      (t := t)
      (ne_of_gt hR)]

omit [SigmaCompactSpace M] in
theorem parabolicBackward_parabolic_ricci
    (G : SolutionFamily (I := I) (M := M))
    (τ R : Real) (hR : 0 < R) (t : Real) :
    (parabolicBackwardFamily (I := I) (parabolicFamily (I := I) G τ R hR)
      τ R hR).ricci t = G.ricci t := by
  simp [parabolicBackwardFamily, parabolicFamily, SolutionFamily.ricci, metricRicci,
    DifferentialGeometry.Geometry.Curvature.metricRicci,
      DifferentialGeometry.Geometry.Curvature.metricCov,
      DifferentialGeometry.Geometry.Connection.lcConn_scaleMetric,
    parabolicTime_back (τ := τ) (R := R) (t := t) (ne_of_gt hR)]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [SigmaCompactSpace M]
    [T2Space M] in
theorem parabolic_parabolicBackward_metric
    (G : SolutionFamily (I := I) (M := M))
    (τ R : Real) (hR : 0 < R) (s : Real) :
    ((parabolicFamily (I := I) (parabolicBackwardFamily (I := I) G τ R hR)
      τ R hR).metric s).inner = (G.metric s).inner := by
  funext x
  ext v w
  simp only [parabolicFamily, parabolicBackwardFamily, scaleMetric_inner]
  rw [parabolicBackward_time (τ := τ) (R := R) (s := s) (ne_of_gt hR)]
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hR), one_mul]

omit [SigmaCompactSpace M] [T2Space M] in
theorem parabolic_parabolicBackward_connection
    (G : SolutionFamily (I := I) (M := M))
    (τ R : Real) (hR : 0 < R) (s : Real) :
    (parabolicFamily (I := I) (parabolicBackwardFamily (I := I) G τ R hR)
      τ R hR).connection s = G.connection s := by
  simp [parabolicFamily, parabolicBackwardFamily, SolutionFamily.connection,
    DifferentialGeometry.Geometry.Connection.lcConn_scaleMetric, parabolicBackward_time (τ := τ) (R := R)
      (s := s)
      (ne_of_gt hR)]

omit [SigmaCompactSpace M] in
theorem parabolic_parabolicBackward_ricci
    (G : SolutionFamily (I := I) (M := M))
    (τ R : Real) (hR : 0 < R) (s : Real) :
    (parabolicFamily (I := I) (parabolicBackwardFamily (I := I) G τ R hR)
      τ R hR).ricci s = G.ricci s := by
  simp [parabolicFamily, parabolicBackwardFamily, SolutionFamily.ricci, metricRicci,
    DifferentialGeometry.Geometry.Curvature.metricRicci,
      DifferentialGeometry.Geometry.Curvature.metricCov,
      DifferentialGeometry.Geometry.Connection.lcConn_scaleMetric,
    parabolicBackward_time (τ := τ) (R := R) (s := s) (ne_of_gt hR)]

def ParabolicScalarCurvatureScaling
    (scalar scalarR : Real -> M -> Real) (τ R : Real) : Prop :=
  forall s x, scalarR s x = R⁻¹ * scalar (parabolicTime τ R s) x

def ParabolicTraceFreeRicciNormSqScaling
    (q qR : Real -> M -> Real) (τ R : Real) : Prop :=
  forall s x, qR s x = (R⁻¹) ^ 2 * q (parabolicTime τ R s) x

omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] in
theorem parabolic_tracefree_ratio_invariant
    {scalar scalarR q qR : Real -> M -> Real}
    {τ R : Real} (hR : 0 < R)
    (hscalar : ParabolicScalarCurvatureScaling (M := M) scalar scalarR τ R)
    (hq : ParabolicTraceFreeRicciNormSqScaling (M := M) q qR τ R)
    (s : Real) (x : M) :
    qR s x / (scalarR s x) ^ 2 =
      q (parabolicTime τ R s) x / (scalar (parabolicTime τ R s) x) ^ 2 := by
  rw [hq s x, hscalar s x]
  field_simp [ne_of_gt hR]

end DifferentialGeometry.PDE.RicciFlow
