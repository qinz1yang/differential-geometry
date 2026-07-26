import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.Basic
import DifferentialGeometry.Geometry.Curvature.MetricLeviCivitaReconcile
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.Connection
import DifferentialGeometry.Tensor.RSTensor.MetricTrace.Connection
import DifferentialGeometry.Geometry.Operator.GradientRegularity

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# P4 Brick 6 — the limit-flow term (`L`) packaging

The MSM135 Thm 3.10 ⇐ 3.9 upgrade needs the limit flow `L : PointedFlowData X.D`
whose metric family is the Arzelà--Ascoli limit `gInf` (Brick 5) and whose
`isSolution : IsSolutionOn` is discharged.  This file provides:

* `isSolutionOn_of_reg` — the 9-field `IsSolutionOn` package for the metric-only
  candidate `{ base := { metric := g } }` on a GENERAL `RealTimeInterval D`, from
  honest analytic inputs about `g` (per-time facts are discharged internally;
  the joint-regularity inputs are the named hypotheses — see the route note in
  `FlowLimitBuild.md`).
* `flowOfMetric` — the `PointedFlowData` constructor: manifold/point data copied
  from a `PointedRiemannianManifold P` (definitionally, so downstream
  `(L, rmaps)`-parametrized bricks compute), `S := { base := { metric := g } }`.
* `flowOfMetric_atTime` — the Brick-7 `hL0` producer:
  `g t = P.metric → (flowOfMetric D P g hsol).atTime t = P`.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

open DifferentialGeometry.Integral.Connection

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
variable [BoundarylessManifold I M]
variable [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-- **`IsSolutionOn` for a metric-only candidate from family regularity**
(P4 Brick 6 core).  On a general real time interval `D`, the candidate
`{ base := { metric := g } }` is a Ricci-flow solution provided:

* `hsmooth` — the canonical joint metric-family regularity package
  (`MetricFamilySmoothOn`; the honest hard input — the AA window limit gives
  per-time smoothness plus time-Lipschitz control only, and the joint upgrade
  is a separate brick);
* `hpde` — the Ricci-flow equation as a genuine time derivative at regular
  times, in the canonical-curvature (`ricciTensor`) vocabulary — exactly what
  `metricLimit_pdeOn` on a neighborhood window inside `D.carrier` produces;
* `hscalarCont`/`hscalarTime`/`hricciCont`/`hrm04Cont` — carrier-local
  continuity/time-differentiability of the canonical curvature of `g`.

The per-time fields (`smoothConnection`, `ricciNormSpace`, `ricciNormGrad`) are
discharged internally from smoothness of each `g t`. -/
theorem isSolutionOn_of_reg
    {D : RealTimeInterval}
    (g : Real -> SmoothRiemannianMetric I M)
    (hsmooth : MetricFamilySmoothOn (I := I) (M := M) D
      ({ base := { metric := g } } : SolutionOn (I := I) (M := M) D).family)
    (hpde : ∀ t ∈ D.regular, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivAt (fun s : Real => (g s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (g t) x v w) t)
    (hscalarCont : ContinuousOn
      (fun q : Real × M => metricScalarAt (I := I) (g q.1) q.2)
      (D.carrier ×ˢ (Set.univ : Set M)))
    (hscalarTime : ∀ t ∈ D.carrier, ∀ x : M,
      DifferentiableWithinAt Real (fun s : Real => metricScalarAt (I := I) (g s) x)
        D.carrier t)
    (hricciCont : Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 D.carrier
      (fun t x => metricRicciAt (I := I) (g t) x))
    (hrm04Cont : Tensor0SFamilyContinuousOnSet (I := I) (M := M) 4 D.carrier
      (fun t x => metricRm04At (I := I) (g t) x)) :
    IsSolutionOn (I := I)
      ({ base := { metric := g } } : SolutionOn (I := I) (M := M) D) := by
  refine
    { smoothMetric := hsmooth
      smoothConnection := ?_
      equation := ?_
      scalarCont := ?_
      scalarTime := ?_
      ricciCont := ?_
      rm04Cont := ?_
      ricciNormSpace := ?_
      ricciNormGrad := ?_ }
  · -- smoothConnection: per-time Levi-Civita covariant-derivative smoothness
    intro t
    simpa [SolutionOn.family, SolutionFamily.connection,
      RealizedMetricFamilyOn.connectionAt]
      using leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I)
        (g (t : Real))
  · -- equation: restrict the full derivative to the carrier and convert the
    -- canonical `ricciTensor` to the data-field Ricci vocabulary
    intro t x X Y
    have h : HasDerivWithinAt (fun s : Real => (g s).inner x X Y)
        ((-2 : Real) * ricciTensor (I := I) (g (t : Real)) x X Y)
        D.carrier (t : Real) :=
      (hpde (t : Real) t.2 x X Y).hasDerivWithinAt
    simpa [SolutionFamily.ricciAt, metricRicciAt,
      metricRicciAt_apply_eq_ricciTensor] using h
  · -- scalarCont
    exact hscalarCont.congr (fun q _ => rfl)
  · -- scalarTime
    intro K t htK hKsub x
    exact (hscalarTime t (hKsub htK) x).mono hKsub
  · -- ricciCont
    refine Tensor0SFamilyContinuousOnSet.congr hricciCont (fun t _ x => ?_)
    simp only [SolutionOn.ricci, SolutionFamily.ricci_apply, SolutionFamily.ricciAt]
  · -- rm04Cont
    refine Tensor0SFamilyContinuousOnSet.congr hrm04Cont (fun t _ x => ?_)
    simp only [SolutionFamily.rm04, metricRm04_apply]
  · -- ricciNormSpace: per-time spatial differentiability of |Ric|²
    intro t ht x
    have h := (normSq02_smooth (I := I) (M := M)
      (g (t : Real)) (metricRicci (I := I) (M := M) (g (t : Real)))).mdifferentiableAt
      (by simp) (x := x)
    refine h.congr_of_eventuallyEq ?_
    filter_upwards with y
    simp only [ricciNorm, SolutionOn.ricci, SolutionOn.family,
      SolutionFamily.ricci_apply, SolutionFamily.ricciAt, metricRicci_apply]
  · -- ricciNormGrad: per-time smoothness of the |Ric|² gradient field
    intro t ht x
    have hsm : ContMDiff I 𝓘(Real, Real) ∞
        (ricciNorm (I := I)
          ({ base := { metric := g } } : SolutionOn (I := I) (M := M) D)
          (t : Real)) := by
      refine (normSq02_smooth (I := I) (M := M)
        (g (t : Real)) (metricRicci (I := I) (M := M) (g (t : Real)))).congr ?_
      intro y
      simp only [ricciNorm, SolutionOn.ricci, SolutionOn.family,
        SolutionFamily.ricci_apply, SolutionFamily.ricciAt, metricRicci_apply]
    exact gradientFun_mdiffAt (I := I) (g (t : Real)) hsm x

end RicciFlow
end PDE

namespace HCGCompactness

open DifferentialGeometry.Integral.Connection

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

/-- **The limit-flow constructor** (P4 Brick 6 term).  A `PointedFlowData` on
the time interval `D` whose manifold and basepoint data are copied — field for
field, hence definitionally — from the pointed Riemannian manifold `P`, whose
metric family is `g`, and whose solution certificate is the supplied `hsol`
(produced by `isSolutionOn_of_reg`).

Because the copy is definitional, `(flowOfMetric D P g hsol).M` unfolds to
`P.M`, so the `(L, rmaps)`-parametrized Bricks 4–5 compute on it, and
`flowOfMetric_atTime` reduces the Brick-7 `hL0` obligation to the Brick-5
time-`0` metric identification. -/
def flowOfMetric
    (D : DifferentialGeometry.Integral.Connection.RealTimeInterval)
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (g :
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      Real -> SmoothRiemannianMetric I P.M)
    (hsol :
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      letI : SigmaCompactSpace P.M := P.sigmaCompact
      letI : T2Space P.M := P.t2
      letI : IsManifold I 1 P.M :=
        IsManifold.of_le (I := I) (M := P.M) (n := ∞)
          (by decide : (1 : WithTop ℕ∞) ≤ ∞)
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) P.M := by
        change IsManifold I ∞ P.M
        infer_instance
      DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I)
        ({ base := { metric := g } } :
          DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := P.M) D)) :
    PointedFlowData.{u, uE, uH} (I := I) D where
  M := P.M
  topology := P.topology
  charted := P.charted
  smooth := P.smooth
  sigmaCompact := P.sigmaCompact
  t2 := P.t2
  t2TangentBundle := P.t2TangentBundle
  basepoint := P.basepoint
  S :=
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : T2Space P.M := P.t2
    letI : IsManifold I 1 P.M :=
      IsManifold.of_le (I := I) (M := P.M) (n := ∞)
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) P.M := by
      change IsManifold I ∞ P.M
      infer_instance
    ({ base := { metric := g } } :
      DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := P.M) D)
  isSolution := hsol

/-- The metric family of the constructed limit flow is the supplied family
(definitional; the Brick-5 `conv` identification hard-wires against this). -/
theorem flowOfMetric_metric
    (D : DifferentialGeometry.Integral.Connection.RealTimeInterval)
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (g :
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      Real -> SmoothRiemannianMetric I P.M)
    (hsol :
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      letI : SigmaCompactSpace P.M := P.sigmaCompact
      letI : T2Space P.M := P.t2
      letI : IsManifold I 1 P.M :=
        IsManifold.of_le (I := I) (M := P.M) (n := ∞)
          (by decide : (1 : WithTop ℕ∞) ≤ ∞)
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) P.M := by
        change IsManifold I ∞ P.M
        infer_instance
      DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I)
        ({ base := { metric := g } } :
          DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := P.M) D)) :
    letI : TopologicalSpace (flowOfMetric (I := I) D P g hsol).M :=
      (flowOfMetric (I := I) D P g hsol).topology
    letI : ChartedSpace H (flowOfMetric (I := I) D P g hsol).M :=
      (flowOfMetric (I := I) D P g hsol).charted
    letI : IsManifold I ∞ (flowOfMetric (I := I) D P g hsol).M :=
      (flowOfMetric (I := I) D P g hsol).smooth
    letI : SigmaCompactSpace (flowOfMetric (I := I) D P g hsol).M :=
      (flowOfMetric (I := I) D P g hsol).sigmaCompact
    letI : T2Space (flowOfMetric (I := I) D P g hsol).M :=
      (flowOfMetric (I := I) D P g hsol).t2
    letI : IsManifold I 1 (flowOfMetric (I := I) D P g hsol).M :=
      IsManifold.of_le (I := I) (M := (flowOfMetric (I := I) D P g hsol).M) (n := ∞)
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (flowOfMetric (I := I) D P g hsol).M := by
      change IsManifold I ∞ (flowOfMetric (I := I) D P g hsol).M
      infer_instance
    (flowOfMetric (I := I) D P g hsol).S.base.metric = g := by
  rfl

/-- **Time-slice reduction** (the Brick-7 `hL0` producer): if the metric family
agrees with `P.metric` at time `t`, the time-`t` slice of the constructed limit
flow is `P` itself.  With `P := mc.limit`, `t := 0` and the Brick-5
identification `gInf 0 = mc.limit.metric`, this is `hL0 : L.atTime 0 = mc.limit`. -/
theorem flowOfMetric_atTime
    (D : DifferentialGeometry.Integral.Connection.RealTimeInterval)
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (g :
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      Real -> SmoothRiemannianMetric I P.M)
    (hsol :
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      letI : SigmaCompactSpace P.M := P.sigmaCompact
      letI : T2Space P.M := P.t2
      letI : IsManifold I 1 P.M :=
        IsManifold.of_le (I := I) (M := P.M) (n := ∞)
          (by decide : (1 : WithTop ℕ∞) ≤ ∞)
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) P.M := by
        change IsManifold I ∞ P.M
        infer_instance
      DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I)
        ({ base := { metric := g } } :
          DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := P.M) D))
    (t : Real)
    (h : g t = P.metric) :
    (flowOfMetric (I := I) D P g hsol).atTime t = P := by
  exact congrArg
    (fun m =>
      ({ M := P.M
         topology := P.topology
         charted := P.charted
         smooth := P.smooth
         sigmaCompact := P.sigmaCompact
         t2 := P.t2
         t2TangentBundle := P.t2TangentBundle
         basepoint := P.basepoint
         metric := m } : PointedRiemannianManifold.{u, uE, uH} (I := I)))
    h

end HCGCompactness
end DifferentialGeometry
