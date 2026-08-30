import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.PhaseExistenceAtTime

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_lRegCurve_at
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T s0 : Real) (x : M) (A0 : TangentSpace I x)
    (hT : T - s0 ^ 2 ∈ D.regular) :
    ∃ (epsilon : Real) (_ : 0 < epsilon) (alpha : Real → M),
      alpha s0 = x ∧
        lVelocity (I := I) alpha s0 = A0 ∧
        ∀ s ∈ Ioo (s0 - epsilon) (s0 + epsilon),
          MDifferentiableAt (modelWithCornersSelf Real Real) I alpha s ∧
            DifferentiableAt Real
              (chartRepAt (I := I) alpha
                (fun r : Real ↦ lVelocity (I := I) alpha r) s) s ∧
            covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha
                (fun r : Real ↦ lVelocity (I := I) alpha r) s =
              lRegAccel S T s (alpha s) (lVelocity (I := I) alpha s) := by
  let z0 : E × E :=
    (extChartAt I x x, trivToE (I := I) x x A0)
  have hz0pos : z0.1 ∈ interior (extChartAt I x).target := by
    apply mem_interior_iff_mem_nhds.mpr
    simpa only [z0] using extChartAt_target_mem_nhds (I := I) x
  obtain ⟨epsilon0, hepsilon0, z, hz0, hsol⟩ :=
    exists_lPhaseSol_at S hS T x s0 z0 hT hz0pos
  have hs00 : s0 ∈ Ioo (s0 - epsilon0) (s0 + epsilon0) := by
    constructor <;> linarith
  have hzder0 := hsol s0 hs00
  have hpos0 : (z s0).1 ∈ interior (extChartAt I x).target := by
    rw [hz0]
    exact hz0pos
  have hinterval : ∀ᶠ s in nhds s0,
      s ∈ Ioo (s0 - epsilon0) (s0 + epsilon0) :=
    isOpen_Ioo.mem_nhds hs00
  have hpos : ∀ᶠ s in nhds s0,
      (z s).1 ∈ interior (extChartAt I x).target :=
    hzder0.continuousAt.fst.eventually (isOpen_interior.mem_nhds hpos0)
  have hgood : ∀ᶠ s in nhds s0,
      s ∈ Ioo (s0 - epsilon0) (s0 + epsilon0) ∧
        (z s).1 ∈ interior (extChartAt I x).target := by
    filter_upwards [hinterval, hpos] with s hs hsp
    exact ⟨hs, hsp⟩
  obtain ⟨epsilon, hepsilon, hsmall⟩ :=
    Metric.eventually_nhds_iff.mp hgood
  let alpha : Real → M := lPhaseCurve (I := I) x z
  let A : ∀ s, TangentSpace I (alpha s) := lPhaseVel (I := I) x z
  have hdata : ∀ s ∈ Ioo (s0 - epsilon) (s0 + epsilon),
      s ∈ Ioo (s0 - epsilon0) (s0 + epsilon0) ∧
        (z s).1 ∈ interior (extChartAt I x).target := by
    intro s hs
    apply hsmall
    rw [Real.dist_eq]
    exact abs_lt.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hvel : EqOn (fun s ↦ lVelocity (I := I) alpha s) A
      (Ioo (s0 - epsilon) (s0 + epsilon)) := by
    intro s hs
    have hsdata := hdata s hs
    have hzs := hsol s hsdata.1
    have hq : HasDerivAt (fun r : Real ↦ (z r).1) (z s).2 s := by
      have h := hasFDerivAt_fst.comp_hasDerivAt s hzs
      simpa [lPhaseField, Function.comp_def] using h
    with_unfolding_all exact
      (lPhase_velocity (I := I) x z s hq hsdata.2)
  have hs0 : s0 ∈ Ioo (s0 - epsilon) (s0 + epsilon) := by
    constructor <;> linarith
  have halpha0 : alpha s0 = x := by
    simp only [alpha, lPhaseCurve, hz0, z0]
    exact (extChartAt I x).left_inv (mem_extChartAt_source (I := I) x)
  refine ⟨epsilon, hepsilon, alpha, halpha0, ?_, ?_⟩
  · have hvel0 : lVelocity (I := I) alpha s0 = A s0 := hvel hs0
    rw [hvel0]
    change trivFromE (I := I) x (alpha s0) (z s0).2 = A0
    rw [halpha0, hz0]
    simp only [z0]
    exact trivFromE_trivToE (I := I) x
      (FiberBundle.mem_baseSet_trivializationAt' x) A0
  · intro s hs
    have hsdata := hdata s hs
    have hzs := hsol s hsdata.1
    have hq : HasDerivAt (fun r : Real ↦ (z r).1) (z s).2 s := by
      have h := hasFDerivAt_fst.comp_hasDerivAt s hzs
      simpa [lPhaseField, Function.comp_def] using h
    have hv : HasDerivAt (fun r : Real ↦ (z r).2)
        (lPhaseField S T x s (z s)).2 s := by
      have h := hasFDerivAt_snd.comp_hasDerivAt s hzs
      simpa [Function.comp_def] using h
    have hfield : (fun r ↦ lVelocity (I := I) alpha r) =ᶠ[nhds s] A :=
      hvel.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hs)
    have halpha : MDifferentiableAt
        (modelWithCornersSelf Real Real) I alpha s := by
      simpa only [alpha] using
        lPhaseCurve_mdiff (I := I) x z s hq.differentiableAt hsdata.2
    have hAdiff : DifferentiableAt Real
        (chartRepAt (I := I) alpha A s) s := by
      simpa only [alpha, A] using lPhaseVel_diff (I := I) x z s
        hq.differentiableAt hv.differentiableAt hsdata.2
    have hveldiff : DifferentiableAt Real
        (chartRepAt (I := I) alpha
          (fun r : Real ↦ lVelocity (I := I) alpha r) s) s :=
      hAdiff.congr_of_eventuallyEq
        (chartRepAt_eventuallyEq_of_eventuallyEq (I := I) alpha hfield)
    refine ⟨halpha, hveldiff, ?_⟩
    calc
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha
          (fun r : Real ↦ lVelocity (I := I) alpha r) s =
        covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha A s :=
          covDerivAlong_congr_of_eventuallyEq
            (I := I) (S.base.metric (T - s ^ 2)) alpha hfield
      _ = lRegAccel S T s (alpha s) (A s) := by
        simpa only [alpha, A] using
          lPhase_accel S T x z s hzs hsdata.2
      _ = lRegAccel S T s (alpha s)
          (lVelocity (I := I) alpha s) := by
        rw [hfield.eq_of_nhds]

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
