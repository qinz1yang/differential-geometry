import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.FiniteTime.Scalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Regularity
import DifferentialGeometry.Geometry.Curvature.DimensionThree.RicciControlsRm

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [SigmaCompactSpace M] [T2Space M]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] in
theorem scalar_pos_of_ricci
    (g0 : SmoothRiemannianMetric I M)
    (hdim : Module.finrank Real E = 3)
    (hpos : ∀ x : M, ∀ v : TangentSpace I x, v ≠ 0 →
      0 < metricRicciAt (I := I) (M := M) g0 x
        (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v)) :
    ∀ x : M, 0 < metricScalarAt (I := I) (M := M) g0 x := by
  intro x
  have hdimx : Module.finrank Real (TangentSpace I x) = 3 := by
    change Module.finrank Real E = 3
    exact hdim
  simpa [metricScalarAt, DifferentialGeometry.Geometry.Curvature.metricScalarAt] using
    (DifferentialGeometry.Geometry.Curvature.metricTrace_pos_of_posDef
      (I := I) (M := M) g0 (metricRicciAt (I := I) (M := M) g0 x)
      hdimx (hpos x))

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] in
private theorem initMin_of_start
    {T c0 : Real} {hT : 0 < T}
    (g0 : SmoothRiemannianMetric I M)
    (S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 T hT))
    (hstart : S.family.metric 0 = g0)
    (hmin : InitialScalarMinimum (M := M)
      (fun _t x => metricScalarAt (I := I) (M := M) g0 x) c0) :
    InitialScalarMinimum (M := M) S.scalar c0 := by
  have hstart_base : S.base.metric 0 = g0 := by
    simpa using hstart
  rcases hmin with ⟨x0, hx0, hlower⟩
  refine ⟨x0, ?_, ?_⟩
  · simpa [SolutionOn.scalar, SolutionFamily.scalar, hstart_base] using hx0
  · intro x
    simpa [SolutionOn.scalar, SolutionFamily.scalar, hstart_base] using hlower x

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private theorem scalar_sq_le_ric
    (hdim : Module.finrank Real E = 3)
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) :
    (1 / 3 : Real) * (S.scalar t x) ^ 2 ≤ ricciNorm (I := I) S t x := by
  classical
  let : Nonempty (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E) :=
    ⟨⟨0, by simp [hdim]⟩⟩
  let basis : Module.Basis
      (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E) Real
      (TangentSpace I x) :=
    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis (I := I) x
  let gInv :
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E →
        DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E → Real :=
    fun k l =>
      DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChartComponent
        (I := I) (S.family.metric t) x k l (extChartAt I x x)
  have hinv :
      Tensor0SBundle.MetricInverseInBasisGen (I := I) (S.family.metric t) x
        basis gInv := by
    simpa [basis, gInv] using
      DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
        (I := I) (S.family.metric t) x
  have h :=
    DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_sq_div_rank_le_normSq0S
      (I := I) (g := S.family.metric t) (basis := basis)
      (gInv := gInv) hinv (S.ricciAt t x)
  have hcard :
      (1 / (Fintype.card
        (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E) : Real)) =
        (1 / 3 : Real) := by
    simp [DifferentialGeometry.Tensor.Coordinates.CoordinateIdx, hdim]
  have hcoef : ((Module.finrank Real E : Real)⁻¹) = (3⁻¹ : Real) := by
    simp [hdim]
  rw [SolutionOn.scalar_eq_metricTrace]
  simpa [SolutionOn.scalar, SolutionFamily.scalar, ricciNorm,
    DifferentialGeometry.Tensor.Coordinates.CoordinateIdx, hcard, hcoef] using h

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem flow_end_le
    [CompactSpace M] [Nonempty M] [I.Boundaryless]
    (g0 : SmoothRiemannianMetric I M)
    (hdim : Module.finrank Real E = 3)
    (hscalar_pos : ∀ x : M,
      0 < metricScalarAt (I := I) (M := M) g0 x)
    {c0 T : Real} (hT : 0 < T)
    (hmin : InitialScalarMinimum (M := M)
      (fun _t x => metricScalarAt (I := I) (M := M) g0 x) c0)
    (S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn (I := I) S)
    (hstart : S.family.metric 0 = g0) :
    T ≤ 3 / (2 * c0) := by
  classical
  let G := flowG (I := I) S
  let scalarLap : Real → M → Real := fun t x =>
    DifferentialGeometry.Geometry.Curvature.laplacianAt (I := I) G t (S.scalar t) x
  have hSmooth : IsSmoothSolutionOn (I := I) (M := M) S :=
    smoothOfSol (I := I) S hS
  have hinit_min : InitialScalarMinimum (M := M) S.scalar c0 :=
    initMin_of_start (I := I) (M := M) g0 S hstart hmin
  have hstart_base : S.base.metric 0 = g0 := by
    simpa using hstart
  have hinit_pos : ∀ x : M, 0 < S.scalar 0 x := by
    intro x
    simpa [SolutionOn.scalar, SolutionFamily.scalar, hstart_base] using
      hscalar_pos x
  have hc0 : 0 < c0 :=
    InitialScalarMinimum.pos_of_forall_pos (M := M) hinit_min hinit_pos
  have hscalar_cont : ∀ U : Real, 0 ≤ U → U < T →
      ContinuousOn (fun p : Real × M => S.scalar p.1 p.2)
        (DifferentialGeometry.Integral.Connection.spacetimeSlab (M := M) U) := by
    intro U _hU hUT
    convert! SolutionOn.scalar_continuousOn (I := I) (M := M) S hSmooth.scalarSTCont U
      (fun t ht => ⟨ht.1, lt_of_le_of_lt ht.2 hUT⟩) using 1
  have hevol : ScalarEvolutionEquationOn
      (D := DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 T hT)
      S.scalar scalarLap (ricciNorm (I := I) S) := by
    have hricci : ricciNorm (I := I) S = fun t x =>
        Tensor0SBundle.inner0S (I := I) (S.base.metric t) x 2
          (S.base.ricciAt t x) (S.base.ricciAt t x) := by
      funext t x
      rw [ricciNorm, Tensor0SBundle.normSq0S_eq_inner]
      rfl
    rw [hricci]
    simpa [G, scalarLap] using
      (scalar_evolution_of_smooth_solution (I := I) (M := M) S hSmooth
        (flowG (I := I) S)
        (by intro t; rfl) (by intro t; rfl))
  have hKExists : ∀ U : Real, 0 < U → U < T →
      U < scalarBlowupTime 3 c0 →
      ∃ K : NNReal, ∀ t : Real, t ∈ Set.Icc 0 U →
        LipschitzOnWith K (fun a : Real => scalarLowerReaction 3 a)
          (DifferentialGeometry.Integral.Connection.scalarWMPValueSet (M := M) U
            S.scalar (scalarLowerBarrier 3 c0)) := by
    intro U hU hUT hPole
    have hden : ∀ t : Real, t ∈ Set.Icc 0 U →
        0 < 1 - (2 / 3 : Real) * c0 * t :=
      scalarLowerBarrier_denominator_pos_on_Icc_of_lt_blowup
        (n := 3) (c0 := c0) (by norm_num) hc0 hPole
    have hbar_cont : ContinuousOn (scalarLowerBarrier 3 c0) (Set.Icc 0 U) := by
      unfold scalarLowerBarrier
      have hden_cont : ContinuousOn (fun t : Real => 1 - (2 / 3 : Real) * c0 * t)
          (Set.Icc 0 U) := by
        fun_prop
      exact continuousOn_const.div hden_cont (fun t ht => ne_of_gt (hden t ht))
    have hcompact : IsCompact
        (DifferentialGeometry.Integral.Connection.scalarWMPValueSet (M := M) U
          S.scalar (scalarLowerBarrier 3 c0)) :=
      DifferentialGeometry.Integral.Connection.scalarWMPValueSet_isCompact
        (M := M) U S.scalar (scalarLowerBarrier 3 c0)
        (hscalar_cont U (le_of_lt hU) hUT) hbar_cont
    exact exists_scalarLowerReaction_lipschitzOn_valueSet
      (M := M) 3 U S.scalar (scalarLowerBarrier 3 c0) hcompact
  let K : Real → NNReal := fun U =>
    if h : 0 < U ∧ U < T ∧ U < scalarBlowupTime 3 c0 then
      Classical.choose (hKExists U h.1 h.2.1 h.2.2)
    else 0
  have hreg : ∀ U : Real, 0 < U → U < T →
      U < scalarBlowupTime 3 c0 →
      ScalarLowerBoundWMPRegularity (I := I) G U 3 c0 S.scalar (K U) := by
    intro U hU hUT hPole
    have hsubset : ∀ t : Real, t ∈ Set.Icc 0 U →
        t ∈ (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 T hT).carrier := by
      intro t ht
      exact ⟨ht.1, lt_of_le_of_lt ht.2 hUT⟩
    have hden : ∀ t : Real, t ∈ Set.Icc 0 U →
        1 - (2 / 3 : Real) * c0 * t ≠ 0 := by
      intro t ht
      exact ne_of_gt (scalarLowerBarrier_denominator_pos_on_Icc_of_lt_blowup
        (n := 3) (c0 := c0) (by norm_num) hc0 hPole t ht)
    exact scalarRegOfSmooth (I := I) (M := M) S hSmooth G U 3 c0 (K U)
      hsubset (by intro t _ht; rfl) hden
  have hlap : ∀ U : Real, 0 < U → U < T →
      U < scalarBlowupTime 3 c0 →
      ScalarLaplacianRealizesHeatOperatorOn (I := I) G U S.scalar scalarLap := by
    intro U _hU _hUT _hPole
    exact ScalarLaplacianRealizesHeatOperatorOn.of_laplacianAt
      (I := I) (by intro t _ht x; rfl)
  have hricci : ∀ U : Real, 0 < U → U < T →
      U < scalarBlowupTime 3 c0 →
      ∀ t : Real, t ∈ Set.Icc 0 U → ∀ x : M,
        (1 / 3 : Real) * (S.scalar t x) ^ 2 ≤ ricciNorm (I := I) S t x := by
    intro _U _hU _hUT _hPole t _ht x
    exact scalar_sq_le_ric (I := I) (M := M) hdim S t x
  have hF_lip : ∀ U : Real, 0 < U → U < T →
      U < scalarBlowupTime 3 c0 →
      ∀ t : Real, t ∈ Set.Icc 0 U →
        LipschitzOnWith (K U) (fun a : Real => scalarLowerReaction 3 a)
          (DifferentialGeometry.Integral.Connection.scalarWMPValueSet (M := M) U
            S.scalar (scalarLowerBarrier 3 c0)) := by
    intro U hU hUT hPole t ht
    dsimp [K]
    rw [dif_pos ⟨hU, hUT, hPole⟩]
    exact Classical.choose_spec (hKExists U hU hUT hPole) t ht
  exact (finiteTime3D (I := I) (M := M) hT G c0 S.scalar scalarLap
    (ricciNorm (I := I) S) K hinit_min hinit_pos hscalar_cont hreg hevol hlap
    hricci hF_lip).2

end DifferentialGeometry.PDE.RicciFlow
