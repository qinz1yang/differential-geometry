import DifferentialGeometry.Geometry.Connection.LeviCivita.Variation.Connection
import DifferentialGeometry.Geometry.Connection.LeviCivita.Basic
import DifferentialGeometry.Geometry.Curvature.Realized.MetricFamily

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable {Idx : Type*} [Fintype Idx]
variable {u : Set M}




def RealizedMetricFamilyOn.toRealizedMetricFamily
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hLC : ∀ s : Real, IsLeviCivita (I := I) (G.connection s) (G.metric s)) :
    RealizedMetricFamily (I := I) (M := M) Real where
  metric := G.metric
  connection := G.connection
  metricCompatible := fun t => (hLC t).1

@[simp] theorem RealizedMetricFamilyOn.toRealizedMetricFamily_metric
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hLC : ∀ s : Real, IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (s : Real) :
    (G.toRealizedMetricFamily hLC).metric s = G.metric s := rfl

@[simp] theorem RealizedMetricFamilyOn.toRealizedMetricFamily_connection
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hLC : ∀ s : Real, IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (s : Real) :
    (G.toRealizedMetricFamily hLC).connection s = G.connection s := rfl




def connectionPairingTimeDeriv
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (base : Real) (x : M) (i j l : Idx) : Real :=
  deriv
    (fun s : Real =>
      (G.metric base).inner x (frame l x)
        ((G.connection s (frame j) x) (frame i x)))
    base




theorem lowerPairDeriv_of_metricFamilySmoothOn
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hLC : ∀ s : Real, IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (hsmooth : MetricFamilySmoothOn (I := I) (M := M) D G)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (frameSmooth : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u)
    (base : Real)
    (hbase : D.regular ∈ nhds base) :
    lowerPairDerivOn (I := I) (G.toRealizedMetricFamily hLC) frame base u
      (connectionPairingTimeDeriv (I := I) (G.toRealizedMetricFamily hLC) frame base) :=
  sorry




theorem gammaDerivOn_of_metricFamilySmoothOn [DecidableEq Idx]
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hLC : ∀ s : Real, IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (hsmooth : MetricFamilySmoothOn (I := I) (M := M) D G)
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (frameSmooth : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u)
    (base : Real)
    (hbase : D.regular ∈ nhds base)
    (hinv :
      InverseMetricComponentsInFrame (I := I)
        ((G.toRealizedMetricFamily hLC).metric base) gInv frame) :
    gammaDerivOn (I := I) (G.toRealizedMetricFamily hLC) frame hframe base u
      (fun x k i j =>
        gammaFromLower gInv
          (connectionPairingTimeDeriv (I := I) (G.toRealizedMetricFamily hLC) frame base)
          x i j k) :=
  gammaDerivOfLower (I := I) (G.toRealizedMetricFamily hLC) gInv frame hframe base
    (connectionPairingTimeDeriv (I := I) (G.toRealizedMetricFamily hLC) frame base) hinv
    (lowerPairDeriv_of_metricFamilySmoothOn (I := I) G hLC hsmooth frame frameSmooth hu base
      hbase)




theorem metricCovVarOn_of_ricciFlow
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (base : Real)
    (ricComp : M -> Idx -> Idx -> Real)
    (hflow :
      metricVarOn (I := I) G frame base u
        (fun x a b => (-2 : Real) * ricComp x a b))
    (hExt :
      metricExtDtOn (I := I) G frame base u
        (fun x a b => (-2 : Real) * ricComp x a b)) :
    metricCovVarOn (I := I) G frame base u
      (dotCovAt (I := I) (G.connection base) frame hframe
        (fun x a b => (-2 : Real) * ricComp x a b)) :=
  metricCovVar_ext (I := I) G frame hframe base
    (fun x a b => (-2 : Real) * ricComp x a b) hflow hExt

end DifferentialGeometry.Integral.Connection
