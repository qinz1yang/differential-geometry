import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.PositiveRicci.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Maximal.Flow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.FiniteTime.Scalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.Existence
import DifferentialGeometry.Geometry.Curvature.DimensionThree.Reconstruction.RicciControlsRiemann
import DifferentialGeometry.Topology.ThreeManifold.Closed
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Topology.ThreeManifold

set_option autoImplicit false

noncomputable section

universe u

namespace DifferentialGeometry.PDE.RicciFlow
namespace HamiltonPositiveRicci

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_hamilton_finite_time_flow_on_closed_open
    (hM : isClosedThreeManifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : positiveRicciMetric (I := I) (M := M) g0) :
    exists omega : Real, exists h0ω : 0 < omega,
      exists P : HamiltonFiniteTimeFlow (I := I) (M := M) g0,
        P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω := by
  let : CompactSpace M := hM.1
  let : ConnectedSpace M := hM.2.1
  let : I.Boundaryless := hM.2.2.1
  let : NeZero (Module.finrank Real E) := ⟨by
    rw [hM.2.2.2]; norm_num⟩
  have hdim : Module.finrank Real E = 3 := hM.2.2.2
  have hscalar_pos : ∀ x : M,
      0 < metricScalarAt (I := I) (M := M) g0 x :=
    scalar_pos_of_ricci (I := I) (M := M) g0 hdim hpos
  rcases exists_max_flow (I := I) (M := M) g0 hdim hscalar_pos with
    ⟨omega, h0ω, Smax, hSmax, hstart, hmax⟩
  have hcurv : Rm04NormSqUnboundedAt (I := I) Smax Smax.base.rm04 :=
    rmUnbounded_of_maximal (I := I) hdim hSmax hmax
      (rm04Realizes_metric (I := I) Smax)
  let P : HamiltonFiniteTimeFlow (I := I) (M := M) g0 :=
    { D := DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω
      S := Smax
      isSmooth := smoothOfSolution (I := I) Smax hSmax
      startsAt := by
        rw [show (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen
          0 omega h0ω).initial = 0 by rfl]
        exact hstart
      curvUnbounded := by
        intro K
        rcases hcurv K with ⟨t, x, ht0, htω, hK⟩
        exact ⟨t, x, ⟨ht0, htω⟩, by simpa [curvatureNormSq] using hK⟩ }
  exact ⟨omega, h0ω, P, rfl⟩

def hamiltonMetricConnectionFamily
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0) :
    DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real :=
  hamiltonMetricConnectionFamilyCore (I := I) P.S g0

def hamiltonRicciNormSq
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0) :
    Real -> M -> Real :=
  fun t x =>
    Tensor0SBundle.normSq0S (I := I) (P.S.family.metric t) x 2 (P.S.ricciAt t x)

def hamiltonScalarLaplacian
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0) :
    Real -> M -> Real :=
  fun t x =>
    DifferentialGeometry.Geometry.Curvature.laplacianAt (I := I) (hamiltonMetricConnectionFamily (I := I) P) t
      (hamiltonScalar (I := I) P t) x

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_scalar_weak_maximum_principle_regularity_on_interval
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (c0 : Real) (K : Real -> NNReal) (T : Real)
    (hsubset : ∀ t : Real, t ∈ Set.Icc 0 T -> t ∈ P.D.carrier)
    (hden : ∀ t : Real, t ∈ Set.Icc 0 T ->
      1 - (2 / (3 : Real)) * c0 * t ≠ 0) :
    DifferentialGeometry.PDE.RicciFlow.ScalarLowerBoundWeakMaximumPrincipleRegularity
      (I := I) (hamiltonMetricConnectionFamily (I := I) P) T 3 c0
      (hamiltonScalar (I := I) P) (K T) := by
  simpa [hamiltonScalar, hamiltonSolution] using
    (DifferentialGeometry.PDE.RicciFlow.scalarRegularityOfSmooth (I := I) (M := M)
      P.S P.isSmooth (hamiltonMetricConnectionFamily (I := I) P) T 3 c0 (K T)
      hsubset
      (by
        intro t ht
        have htD : t ∈ P.D.carrier := hsubset t ht
        simp [hamiltonMetricConnectionFamily, hamiltonMetricConnectionFamilyCore, htD])
      hden)


omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem hamilton_initial_scalar_continuous
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0) :
    Continuous (fun x : M => hamiltonScalar (I := I) P 0 x) := by
  rw [continuous_iff_continuousAt]
  intro x
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    simpa using (inferInstance : IsManifold I (∞ : WithTop ℕ∞) M)
  have hmdiff :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M =>
          Tensor0SBundle.inner0S (I := I) (P.S.family.metric 0) y 2
            (Tensor0SBundle.metricTensorField (I := I) (P.S.family.metric 0) y)
            (P.S.ricci 0 y)) x :=
    Tensor0SBundle.inner0S_two_mdiff
      (I := I) (P.S.family.metric 0)
      (Tensor0SBundle.metricTensorField (I := I) (P.S.family.metric 0))
      (P.S.ricci 0) x
  have hfun :
      (fun y : M =>
          Tensor0SBundle.inner0S (I := I) (P.S.family.metric 0) y 2
            (Tensor0SBundle.metricTensorField (I := I) (P.S.family.metric 0) y)
            (P.S.ricci 0 y)) =
        fun y : M => hamiltonScalar (I := I) P 0 y := by
    funext y
    have hmetric :
        Tensor0SBundle.metricTensorField (I := I) (P.S.family.metric 0) y =
          DifferentialGeometry.Geometry.Operator.metricTensor0S (I := I) (P.S.family.metric 0)
            y := by
      ext v
      rw [Tensor0SBundle.metricTensorField_apply,
        DifferentialGeometry.Geometry.Operator.metricTensor0S_apply]
    change
      Tensor0SBundle.inner0S (I := I) (P.S.family.metric 0) y 2
          (Tensor0SBundle.metricTensorField (I := I) (P.S.family.metric 0) y)
          (P.S.ricci 0 y) =
        DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar (I := I) (hamiltonSolution (I := I) P) 0 y
    rw [DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar_eq_metricTrace,
      DifferentialGeometry.Geometry.Operator.metricTracePair0SAt, hmetric]
    simp [DifferentialGeometry.PDE.RicciFlow.SolutionOn.ricci,
      DifferentialGeometry.PDE.RicciFlow.SolutionOn.ricciAt,
      DifferentialGeometry.PDE.RicciFlow.SolutionFamily.ricci_apply]
  exact (hfun ▸ hmdiff.continuousAt)

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_initial_ricci_positive
    {omega : Real} (h0ω : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (hpos : positiveRicciMetric (I := I) (M := M) g0)
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω) :
    DifferentialGeometry.PDE.RicciFlow.RicciPosInitial (I := I) (M := M)
      (DifferentialGeometry.PDE.RicciFlow.twoTensorSecToFamily (I := I) (M := M)
        P.S.ricci) := by
  intro x v hv
  have hmetric0 : P.S.family.metric 0 = g0 := by
    have hinit : P.D.initial = 0 := by
      rw [hD]
      rfl
    simpa [hinit] using P.startsAt
  have hpos0 :
      0 < DifferentialGeometry.Geometry.Curvature.metricRicciAt (I := I) (M := M)
        (P.S.family.metric 0) x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v) := by
    rw [hmetric0]
    exact hpos x v hv
  simpa [DifferentialGeometry.PDE.RicciFlow.twoTensorSecToFamily,
    DifferentialGeometry.PDE.RicciFlow.SolutionOn.ricci,
    DifferentialGeometry.PDE.RicciFlow.SolutionOn.ricciAt,
      DifferentialGeometry.PDE.RicciFlow.SolutionFamily.ricci,
    DifferentialGeometry.PDE.RicciFlow.SolutionFamily.ricciAt] using hpos0

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_initial_scalar_positive
    (hdim : Module.finrank Real E = 3)
    {omega : Real} (h0ω : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (hpos : positiveRicciMetric (I := I) (M := M) g0)
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω) :
    forall x : M, 0 < hamiltonScalar (I := I) P 0 x := by
  intro x
  have hmetric0 : P.S.family.metric 0 = g0 := by
    have hinit : P.D.initial = 0 := by
      rw [hD]
      rfl
    simpa [hinit] using P.startsAt
  have hdimx : Module.finrank Real (TangentSpace I x) = 3 := by
    rw [show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl]
    exact hdim
  have hpos0 :
      forall v : TangentSpace I x, v ≠ 0 ->
        0 < P.S.ricciAt 0 x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v) := by
    intro v hv
    change
      0 < DifferentialGeometry.Geometry.Curvature.metricRicciAt (I := I) (M := M)
        (P.S.family.metric 0) x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v)
    rw [hmetric0]
    exact hpos x v hv
  exact
    DifferentialGeometry.Geometry.Curvature.metricTrace_pos_of_posDef
      (I := I) (M := M) (P.S.family.metric 0) (P.S.ricciAt 0 x)
      hdimx hpos0

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_initial_scalar_minimum
    [CompactSpace M] [Nonempty M]
    (hdim : Module.finrank Real E = 3)
    {omega : Real} (h0ω : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (hpos : positiveRicciMetric (I := I) (M := M) g0)
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω) :
    exists c0 : Real,
      DifferentialGeometry.PDE.RicciFlow.InitialScalarMinimum (M := M) (hamiltonScalar (I := I) P) c0 ∧
        forall x : M, 0 < hamiltonScalar (I := I) P 0 x := by
  have hcont : Continuous (fun x : M => hamiltonScalar (I := I) P 0 x) :=
    hamilton_initial_scalar_continuous (I := I) (M := M) P
  rcases DifferentialGeometry.PDE.RicciFlow.exists_initialScalarMinimum_of_continuous
      (M := M) (hamiltonScalar (I := I) P) hcont with
    ⟨c0, hmin⟩
  exact ⟨c0, hmin, hamilton_initial_scalar_positive (I := I) (M := M) hdim h0ω hpos P hD⟩

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_scalar_slab_continuous_on
    {omega : Real} (h0ω : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω)
    (T : Real) (hTω : T < omega) :
    ContinuousOn
      (fun p : Real × M => hamiltonScalar (I := I) P p.1 p.2)
      (DifferentialGeometry.Analysis.Parabolic.spacetimeSlab (M := M) T) := by
  have hreg :
      DifferentialGeometry.PDE.RicciFlow.ScalarSTContOn
        (I := I) (M := M) (hamiltonSolution (I := I) P) :=
    hamilton_scalar_space_time_continuous (I := I) (M := M) P
  change ContinuousOn
    (fun p : Real × M => (hamiltonSolution (I := I) P).scalar p.1 p.2)
    ((Set.Icc 0 T).prod Set.univ)
  exact DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar_continuousOn
      (I := I) (M := M) (hamiltonSolution (I := I) P)
      hreg
      T
      (by
        intro t ht
        rw [hD]
        exact ⟨ht.1, lt_of_le_of_lt ht.2 hTω⟩)

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_scalar_evolution_equation
    {omega : Real} (h0ω : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω) :
    DifferentialGeometry.PDE.RicciFlow.ScalarEvolutionEquationOn
      (D := DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω)
      (hamiltonScalar (I := I) P)
      (hamiltonScalarLaplacian (I := I) P)
      (hamiltonRicciNormSq (I := I) P) := by
  rw [← hD]
  have h :
      DifferentialGeometry.PDE.RicciFlow.ScalarEvolutionEquationOn
        (D := P.D)
        (hamiltonSolution (I := I) P).scalar
        (fun t x =>
          DifferentialGeometry.Geometry.Curvature.laplacianAt (I := I) (hamiltonMetricConnectionFamily (I := I) P)
            t
            ((hamiltonSolution (I := I) P).scalar t) x)
        (fun t x =>
          Tensor0SBundle.normSq0S (I := I)
            ((hamiltonSolution (I := I) P).family.metric t) x 2
            ((hamiltonSolution (I := I) P).ricci t x)) := by
    refine
      DifferentialGeometry.PDE.RicciFlow.scalar_evolution_of_smooth_solution
        (I := I) (M := M) (hamiltonSolution (I := I) P) P.isSmooth
        (hamiltonMetricConnectionFamily (I := I) P) ?_ ?_
    · intro t
      have ht : (t : Real) ∈ P.D.carrier := P.D.regular_subset t.2
      simp [hamiltonMetricConnectionFamily, hamiltonMetricConnectionFamilyCore, ht]
    · intro t
      have ht : (t : Real) ∈ P.D.carrier := P.D.regular_subset t.2
      simp [hamiltonMetricConnectionFamily, hamiltonMetricConnectionFamilyCore, ht]
  have hscalar : hamiltonScalar (I := I) P =
      (hamiltonSolution (I := I) P).scalar := rfl
  have hlap : hamiltonScalarLaplacian (I := I) P = fun t x =>
      DifferentialGeometry.Geometry.Curvature.laplacianAt (I := I)
        (hamiltonMetricConnectionFamily (I := I) P) t
        ((hamiltonSolution (I := I) P).scalar t) x := rfl
  have hnorm : hamiltonRicciNormSq (I := I) P = fun t x =>
      Tensor0SBundle.normSq0S (I := I)
        ((hamiltonSolution (I := I) P).family.metric t) x 2
        ((hamiltonSolution (I := I) P).ricci t x) := rfl
  rw [hscalar, hlap, hnorm]
  exact h

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_scalar_laplacian_realizes_heat
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0) (T : Real) :
    DifferentialGeometry.PDE.RicciFlow.ScalarLaplacianRealizesHeatOperatorOn
      (I := I) (hamiltonMetricConnectionFamily (I := I) P) T
      (hamiltonScalar (I := I) P)
      (hamiltonScalarLaplacian (I := I) P) := by
  exact
    DifferentialGeometry.PDE.RicciFlow.ScalarLaplacianRealizesHeatOperatorOn.of_laplacianAt
      (I := I) (G := hamiltonMetricConnectionFamily (I := I) P)
      (T := T) (scalar := hamiltonScalar (I := I) P)
      (scalarLap := hamiltonScalarLaplacian (I := I) P)
      (by
        intro t _ht x
        rfl)

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_scalar_weak_maximum_principle_regularity
    {omega : Real} (h0ω : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω)
    (c0 : Real) (hc0 : 0 < c0) (K : Real -> NNReal) :
    forall T : Real, T < omega ->
      T < DifferentialGeometry.PDE.RicciFlow.scalarBlowupTime 3 c0 ->
        DifferentialGeometry.PDE.RicciFlow.ScalarLowerBoundWeakMaximumPrincipleRegularity
          (I := I) (hamiltonMetricConnectionFamily (I := I) P) T 3 c0
          (hamiltonScalar (I := I) P) (K T) := by
  intro T hTω hPole
  have hsubset : ∀ t : Real, t ∈ Set.Icc 0 T -> t ∈ P.D.carrier := by
    intro t ht
    rw [hD]
    exact ⟨ht.1, lt_of_le_of_lt ht.2 hTω⟩
  have hden_pos :
      ∀ t : Real, t ∈ Set.Icc 0 T ->
        0 < 1 - (2 / (3 : Real)) * c0 * t :=
    DifferentialGeometry.PDE.RicciFlow.scalarLowerBarrier_denominator_pos_on_Icc_of_lt_blowup
      (n := 3) (c0 := c0) (by norm_num) hc0 hPole
  have hden :
      ∀ t : Real, t ∈ Set.Icc 0 T ->
        1 - (2 / (3 : Real)) * c0 * t ≠ 0 := by
    intro t ht
    exact ne_of_gt (hden_pos t ht)
  simpa [hamiltonMetricConnectionFamily, hamiltonScalar, hamiltonSolution] using
    hamilton_scalar_weak_maximum_principle_regularity_on_interval (I := I) (M := M) P c0 K T hsubset hden

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_scalar_sq_le_three_ricci_norm_sq
    (hdim : Module.finrank Real E = 3)
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (t : Real) (x : M) :
    (1 / 3 : Real) * (hamiltonScalar (I := I) P t x) ^ 2 <=
      hamiltonRicciNormSq (I := I) P t x := by
  classical
  let : Nonempty (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E) :=
    ⟨⟨0, by simp [hdim]⟩⟩
  let basis : Module.Basis (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E)
    Real
      (TangentSpace I x) :=
    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis (I := I) x
  let gInv :
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
        DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
    fun k l =>
      DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChartComponent
        (I := I) (P.S.family.metric t) x k l (extChartAt I x x)
  have hinv :
      Tensor0SBundle.MetricInverseInBasis (I := I) (P.S.family.metric t) x
        basis gInv := by
    simpa [basis, gInv] using
      Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
        (I := I) (P.S.family.metric t) x
  have h :=
    DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_sq_div_rank_le_normSq0S
      (I := I) (g := P.S.family.metric t) (basis := basis)
      (gInv := gInv) hinv (P.S.ricciAt t x)
  have hcard :
      (1 / (Fintype.card (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E) :
        Real)) =
        (1 / 3 : Real) := by
    simp [DifferentialGeometry.Tensor.Coordinates.CoordinateIdx, hdim]
  have hcoef : ((Module.finrank Real E : Real)⁻¹) = (3⁻¹ : Real) := by
    simp [hdim]
  simpa [hamiltonScalar, hamiltonRicciNormSq, DifferentialGeometry.Tensor.Coordinates.CoordinateIdx, hcard,
    hcoef]
    using h

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_scalar_slab_lipschitz
    [CompactSpace M]
    {omega : Real}
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (c0 : Real)
    (hc0 : 0 < c0)
    (hcont : forall T : Real, 0 <= T -> T < omega ->
      ContinuousOn (fun p : Real × M => hamiltonScalar (I := I) P p.1 p.2)
        (DifferentialGeometry.Analysis.Parabolic.spacetimeSlab (M := M) T)) :
    exists K : Real -> NNReal,
      forall T : Real, 0 < T -> T < omega ->
        T < DifferentialGeometry.PDE.RicciFlow.scalarBlowupTime 3 c0 ->
          forall t : Real, t ∈ Set.Icc 0 T ->
            LipschitzOnWith (K T)
              (fun a : Real => DifferentialGeometry.PDE.RicciFlow.scalarLowerReaction 3 a)
              (DifferentialGeometry.Analysis.Parabolic.scalarWeakMaximumPrincipleValueSet (M := M) T
                (hamiltonScalar (I := I) P)
                (DifferentialGeometry.PDE.RicciFlow.scalarLowerBarrier 3 c0)) := by
  classical
  have hExists :
      ∀ T : Real, 0 < T -> T < omega ->
        T < DifferentialGeometry.PDE.RicciFlow.scalarBlowupTime 3 c0 ->
        ∃ K : NNReal,
          ∀ t : Real, t ∈ Set.Icc 0 T ->
            LipschitzOnWith K
              (fun a : Real => DifferentialGeometry.PDE.RicciFlow.scalarLowerReaction 3 a)
              (DifferentialGeometry.Analysis.Parabolic.scalarWeakMaximumPrincipleValueSet (M := M) T
                (hamiltonScalar (I := I) P)
                (DifferentialGeometry.PDE.RicciFlow.scalarLowerBarrier 3 c0)) := by
    intro T hT hTω hPole
    have hscalar_cont_T :
        ContinuousOn
          (fun p : Real × M => hamiltonScalar (I := I) P p.1 p.2)
          (DifferentialGeometry.Analysis.Parabolic.spacetimeSlab (M := M) T) :=
      hcont T (le_of_lt hT) hTω
    have hden :
        ∀ t : Real, t ∈ Set.Icc 0 T ->
          0 < 1 - (2 / 3 : Real) * c0 * t :=
      DifferentialGeometry.PDE.RicciFlow.scalarLowerBarrier_denominator_pos_on_Icc_of_lt_blowup
        (n := 3) (c0 := c0) (by norm_num) hc0 hPole
    have hbar_cont :
        ContinuousOn (DifferentialGeometry.PDE.RicciFlow.scalarLowerBarrier 3 c0)
          (Set.Icc 0 T) := by
      unfold DifferentialGeometry.PDE.RicciFlow.scalarLowerBarrier
      have hden_cont :
          ContinuousOn (fun t : Real => 1 - (2 / 3 : Real) * c0 * t)
            (Set.Icc 0 T) := by
        fun_prop
      exact continuousOn_const.div hden_cont (fun t ht => ne_of_gt (hden t ht))
    have hcompact :
        IsCompact
          (DifferentialGeometry.Analysis.Parabolic.scalarWeakMaximumPrincipleValueSet (M := M) T
            (hamiltonScalar (I := I) P)
            (DifferentialGeometry.PDE.RicciFlow.scalarLowerBarrier 3 c0)) :=
      DifferentialGeometry.Analysis.Parabolic.scalarWeakMaximumPrincipleValueSet_isCompact
        (M := M) T (hamiltonScalar (I := I) P)
        (DifferentialGeometry.PDE.RicciFlow.scalarLowerBarrier 3 c0) hscalar_cont_T hbar_cont
    exact
      DifferentialGeometry.PDE.RicciFlow.exists_scalarLowerReaction_lipschitzOn_valueSet
        (M := M) 3 T (hamiltonScalar (I := I) P)
        (DifferentialGeometry.PDE.RicciFlow.scalarLowerBarrier 3 c0) hcompact
  let K : Real -> NNReal := fun T =>
    if h : 0 < T ∧ T < omega ∧
        T < DifferentialGeometry.PDE.RicciFlow.scalarBlowupTime 3 c0 then
      Classical.choose (hExists T h.1 h.2.1 h.2.2)
    else 0
  refine ⟨K, ?_⟩
  intro T hT hTω hPole t ht
  dsimp [K]
  rw [dif_pos ⟨hT, hTω, hPole⟩]
  exact Classical.choose_spec (hExists T hT hTω hPole) t ht

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem exists_hamilton_scalar_evolution_system
    {omega : Real} (h0ω : 0 < omega)
    (hM : isClosedThreeManifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : positiveRicciMetric (I := I) (M := M) g0)
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω) :
    exists G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real,
      exists c0 : Real,
      exists scalar scalarLap ricciNormSq : Real -> M -> Real,
      exists K : Real -> NNReal,
        DifferentialGeometry.PDE.RicciFlow.InitialScalarMinimum (M := M) scalar c0 /\
        (forall x : M, 0 < scalar 0 x) /\
        (forall T : Real, 0 <= T -> T < omega ->
          ContinuousOn (fun p : Real × M => scalar p.1 p.2)
            (DifferentialGeometry.Analysis.Parabolic.spacetimeSlab (M := M) T)) /\
        (forall T : Real, 0 < T -> T < omega ->
          T < DifferentialGeometry.PDE.RicciFlow.scalarBlowupTime 3 c0 ->
            DifferentialGeometry.PDE.RicciFlow.ScalarLowerBoundWeakMaximumPrincipleRegularity
              (I := I) G T 3 c0 scalar (K T)) /\
        DifferentialGeometry.PDE.RicciFlow.ScalarEvolutionEquationOn
          (D := DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω)
          scalar scalarLap ricciNormSq /\
        (forall T : Real, 0 < T -> T < omega ->
          T < DifferentialGeometry.PDE.RicciFlow.scalarBlowupTime 3 c0 ->
            DifferentialGeometry.PDE.RicciFlow.ScalarLaplacianRealizesHeatOperatorOn
              (I := I) G T scalar scalarLap) /\
        (forall T : Real, 0 < T -> T < omega ->
          T < DifferentialGeometry.PDE.RicciFlow.scalarBlowupTime 3 c0 ->
            forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
              (1 / 3 : Real) * (scalar t x) ^ 2 <= ricciNormSq t x) /\
        (forall T : Real, 0 < T -> T < omega ->
          T < DifferentialGeometry.PDE.RicciFlow.scalarBlowupTime 3 c0 ->
            forall t : Real, t ∈ Set.Icc 0 T ->
              LipschitzOnWith (K T)
                (fun a : Real => DifferentialGeometry.PDE.RicciFlow.scalarLowerReaction 3 a)
                (DifferentialGeometry.Analysis.Parabolic.scalarWeakMaximumPrincipleValueSet
                  (M := M) T scalar
                  (DifferentialGeometry.PDE.RicciFlow.scalarLowerBarrier 3 c0))) := by
  rcases hM with ⟨hcompact, _hconnected, _hboundaryless, hdim⟩
  let : CompactSpace M := hcompact
  let : Nonempty M := inferInstance
  rcases hamilton_initial_scalar_minimum (I := I) (M := M) hdim h0ω hpos P hD with
    ⟨c0, hinit_min, hinit_pos⟩
  have hcont :
      forall T : Real, 0 <= T -> T < omega ->
        ContinuousOn (fun p : Real × M => hamiltonScalar (I := I) P p.1 p.2)
          (DifferentialGeometry.Analysis.Parabolic.spacetimeSlab (M := M) T) := by
    intro T _hT hTω
    exact hamilton_scalar_slab_continuous_on (I := I) (M := M) h0ω P hD T hTω
  have hc0 : 0 < c0 :=
    DifferentialGeometry.PDE.RicciFlow.InitialScalarMinimum.pos_of_forall_pos
      (M := M) hinit_min hinit_pos
  rcases hamilton_scalar_slab_lipschitz (I := I) (M := M) (omega := omega) P c0 hc0 hcont with
    ⟨K, hK⟩
  refine ⟨hamiltonMetricConnectionFamily (I := I) P, c0,
    hamiltonScalar (I := I) P, hamiltonScalarLaplacian (I := I) P,
    hamiltonRicciNormSq (I := I) P, K, hinit_min, hinit_pos, hcont, ?_, ?_, ?_, ?_, ?_⟩
  · intro T _hT hTω hPole
    exact hamilton_scalar_weak_maximum_principle_regularity
      (I := I) (M := M) h0ω P hD c0 hc0 K T hTω hPole
  · exact hamilton_scalar_evolution_equation (I := I) (M := M) h0ω P hD
  · intro T _hT _hTω _hPole
    exact hamilton_scalar_laplacian_realizes_heat (I := I) (M := M) P T
  · intro _T _hT _hTω _hPole t _ht x
    exact hamilton_scalar_sq_le_three_ricci_norm_sq (I := I) (M := M) hdim P t x
  · intro T hT hTω hPole
    exact hK T hT hTω hPole

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_extinction_time_bound
    {omega : Real} (h0ω : 0 < omega)
    (hM : isClosedThreeManifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : positiveRicciMetric (I := I) (M := M) g0)
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω) :
    exists c0 : Real, 0 < c0 /\ omega <= 3 / (2 * c0) := by
  have hMcopy := hM
  rcases hM with ⟨hcompact, hconnected, hboundaryless, _hdim⟩
  let : CompactSpace M := hcompact
  let : ConnectedSpace M := hconnected
  let : I.Boundaryless := hboundaryless
  let : Nonempty M := inferInstance
  rcases exists_hamilton_scalar_evolution_system (I := I) (M := M) h0ω hMcopy g0 hpos P hD with
    ⟨G, c0, scalar, scalarLap, ricciNormSq, K,
      hinit_min, hinit_pos, hscalar_cont, hreg, hevol, hlap, hricci, hF_lip⟩
  have hfinite :
      0 < c0 ∧ omega <= 3 / (2 * c0) :=
    DifferentialGeometry.PDE.RicciFlow.finiteTime3D (I := I) (M := M) h0ω G c0 scalar scalarLap
      ricciNormSq K hinit_min hinit_pos hscalar_cont hreg hevol hlap
      hricci hF_lip
  exact ⟨c0, hfinite.1, hfinite.2⟩

end HamiltonPositiveRicci
end DifferentialGeometry.PDE.RicciFlow
