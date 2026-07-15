import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCStageMap
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCSupportCapstone

set_option autoImplicit false

/-!
# Local identification of the finite-stage comparison map

This file connects the chart-independent map from `StepCStageMap` to the
source-local center branches.  Every local construction is identified through
the same unique global energy minimizer; local limit weights are never compared
across source charts.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Set Bundle Manifold
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Riemannian

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

/-- A center input for the active-filled direct targets proves uniqueness of
the original finite-stage energy, hence supplies the proof branch used by the
global stage comparison map. -/
theorem uniqueStage_of_fill
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) (s : Real) (hs : 0 ≤ s)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (k l : Nat)
    (qstar : (X.obj (L.φ k)).M → (X.obj (L.φ l)).M)
    (join : (X.obj (L.φ l)).M → (X.obj (L.φ l)).M → Real →
      (X.obj (L.φ l)).M)
    (p : (X.obj (L.φ k)).M → (X.obj (L.φ l)).M)
    (rad : (X.obj (L.φ k)).M → Real)
    (x : (X.obj (L.φ k)).M)
    (hcm :
      let Y := X.obj (L.φ l)
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : SigmaCompactSpace Y.M := Y.sigmaCompact
      letI : T2Space Y.M := Y.t2
      letI : ConnectedSpace Y.M := hconn (L.φ l)
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      letI : TopologicalSpace.MetrizableSpace Y.M :=
        Manifold.metrizableSpace I Y.M
      letI : T3Space Y.M := inferInstance
      let i0 := baseIndex inp.decay inp.realizes inp.pack hs
      let mu := fun (y : (X.obj (L.φ k)).M) (gamma : Fin (inp.pack.A s)) =>
        rawWeights
          (cutRaw
            (seqAtom inp.decay inp.hD P L inp.pack s k i0)
            (seqAtom inp.decay inp.hD P L inp.pack s k) i0)
          y gamma
      CenterInput (I := I) Y.metric (mu x)
        (centerAverage.activeFill mu (stageTarget inp P L s k l) qstar x)
        join (p x) (rad x)) :
    HasUniqueStageCenter inp P L s hs hconn k l x := by
  let Y := X.obj (L.φ l)
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : ConnectedSpace Y.M := hconn (L.φ l)
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  letI : T3Space Y.M := inferInstance
  let i0 := baseIndex inp.decay inp.realizes inp.pack hs
  let mu := fun (y : (X.obj (L.φ k)).M) (gamma : Fin (inp.pack.A s)) =>
    rawWeights
      (cutRaw
        (seqAtom inp.decay inp.hD P L inp.pack s k i0)
        (seqAtom inp.decay inp.hD P L inp.pack s k) i0)
      y gamma
  have huniq := centerAverage.uniqueMin_activeFill (I := I) Y.metric mu
    (stageTarget inp P L s k l) qstar join p rad x hcm
  simpa only [HasUniqueStageCenter, i0, mu] using huniq

/-- On the controlled source ball, the global stage comparison map is exactly
the center selected from any active-filled local `CenterInput`. -/
theorem stageCompare_eq_cm
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) (s : Real) (hs : 0 ≤ s)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (k l : Nat)
    (qstar : (X.obj (L.φ k)).M → (X.obj (L.φ l)).M)
    (join : (X.obj (L.φ l)).M → (X.obj (L.φ l)).M → Real →
      (X.obj (L.φ l)).M)
    (p : (X.obj (L.φ k)).M → (X.obj (L.φ l)).M)
    (rad : (X.obj (L.φ k)).M → Real)
    (x : (X.obj (L.φ k)).M)
    (hx : x ∈ L.hatSourceBall inp.decay P s k)
    (hcm :
      let Y := X.obj (L.φ l)
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : SigmaCompactSpace Y.M := Y.sigmaCompact
      letI : T2Space Y.M := Y.t2
      letI : ConnectedSpace Y.M := hconn (L.φ l)
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      letI : TopologicalSpace.MetrizableSpace Y.M :=
        Manifold.metrizableSpace I Y.M
      letI : T3Space Y.M := inferInstance
      let i0 := baseIndex inp.decay inp.realizes inp.pack hs
      let mu := fun (y : (X.obj (L.φ k)).M) (gamma : Fin (inp.pack.A s)) =>
        rawWeights
          (cutRaw
            (seqAtom inp.decay inp.hD P L inp.pack s k i0)
            (seqAtom inp.decay inp.hD P L inp.pack s k) i0)
          y gamma
      CenterInput (I := I) Y.metric (mu x)
        (centerAverage.activeFill mu (stageTarget inp P L s k l) qstar x)
        join (p x) (rad x)) :
    stageComparisonMap inp P L s hs hconn k l x =
      let Y := X.obj (L.φ l)
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : SigmaCompactSpace Y.M := Y.sigmaCompact
      letI : T2Space Y.M := Y.t2
      letI : ConnectedSpace Y.M := hconn (L.φ l)
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      letI : TopologicalSpace.MetrizableSpace Y.M :=
        Manifold.metrizableSpace I Y.M
      letI : T3Space Y.M := inferInstance
      let i0 := baseIndex inp.decay inp.realizes inp.pack hs
      let mu := fun (y : (X.obj (L.φ k)).M) (gamma : Fin (inp.pack.A s)) =>
        rawWeights
          (cutRaw
            (seqAtom inp.decay inp.hD P L inp.pack s k i0)
            (seqAtom inp.decay inp.hD P L inp.pack s k) i0)
          y gamma
      centerOfMass (I := I) Y.metric (mu x)
        (centerAverage.activeFill mu (stageTarget inp P L s k l) qstar x)
        join (p x) (rad x) hcm := by
  let Y := X.obj (L.φ l)
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : ConnectedSpace Y.M := hconn (L.φ l)
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  letI : T3Space Y.M := inferInstance
  let i0 := baseIndex inp.decay inp.realizes inp.pack hs
  let mu := fun (y : (X.obj (L.φ k)).M) (gamma : Fin (inp.pack.A s)) =>
    rawWeights
      (cutRaw
        (seqAtom inp.decay inp.hD P L inp.pack s k i0)
        (seqAtom inp.decay inp.hD P L inp.pack s k) i0)
      y gamma
  let q := centerOfMass (I := I) Y.metric (mu x)
    (centerAverage.activeFill mu (stageTarget inp P L s k l) qstar x)
    join (p x) (rad x) hcm
  change stageComparisonMap inp P L s hs hconn k l x = q
  have huniq := uniqueStage_of_fill (I := I) inp P L s hs hconn k l
    qstar join p rad x hcm
  rw [stageCompare_choose (I := I) inp P L s hs hconn k l x hx huniq]
  apply huniq.unique
  · exact Classical.choose_spec huniq.exists
  · intro z
    rw [← centerAverage.energy_activeFill (I := I) Y.metric mu
      (stageTarget inp P L s k l) qstar x q,
      ← centerAverage.energy_activeFill (I := I) Y.metric mu
        (stageTarget inp P L s k l) qstar x z]
    exact centerOfMass.min hcm z

end HCGCompactness
end DifferentialGeometry
