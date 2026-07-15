import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.MetricCompactnessInputs
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCAtomConv

set_option autoImplicit false

/-!
# Finite-stage Step-C comparison map

This file defines the chart-independent finite-stage comparison map used by
Step B1.  Its weights are the actual normalized Step-C atoms at the source
stage, and its target points are the direct source-chart to target-chart
readouts.  Source charts enter later proofs, but not the map definition.
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

/-- The direct target-stage point associated with one finite Step-C slot.  The
partial-equivalence coercions make this a total function; its geometric chart
meaning is used only on the controlled normal-coordinate domains. -/
noncomputable def stageTarget
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) (s : Real) (k l : Nat)
    (x : (X.obj (L.φ k)).M) (gamma : Fin (inp.pack.A s)) :
    (X.obj (L.φ l)).M :=
  let Yk := X.obj (L.φ k)
  let Yl := X.obj (L.φ l)
  letI : TopologicalSpace Yk.M := Yk.topology
  letI : ChartedSpace H Yk.M := Yk.charted
  letI : IsManifold I ∞ Yk.M := Yk.smooth
  letI : T2Space Yk.M := Yk.t2
  letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
  letI : TopologicalSpace Yl.M := Yl.topology
  letI : ChartedSpace H Yl.M := Yl.charted
  letI : IsManifold I ∞ Yl.M := Yl.smooth
  letI : T2Space Yl.M := Yl.t2
  letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
  (NormalCoordinates.normalChartAt (I := I) Yl.metric
      (seqCenterD inp.decay P L l (gamma : Nat))).symm
    (NormalCoordinates.normalChartAt (I := I) Yk.metric
      (seqCenterD inp.decay P L k (gamma : Nat)) x)

/-- In any prescribed source-slot coordinates, the direct stage target is the
source transition followed by the target transition.  This is a total-function
identity; domain hypotheses are needed only for its geometric inverse-chart
interpretation. -/
@[simp] theorem stageTarget_chart
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) (s : Real) (k l : Nat)
    (alpha gamma : Fin (inp.pack.A s)) (z : E) :
    let Yk := X.obj (L.φ k)
    let Yl := X.obj (L.φ l)
    letI : TopologicalSpace Yk.M := Yk.topology
    letI : ChartedSpace H Yk.M := Yk.charted
    letI : IsManifold I ∞ Yk.M := Yk.smooth
    letI : T2Space Yk.M := Yk.t2
    letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
    letI : TopologicalSpace Yl.M := Yl.topology
    letI : ChartedSpace H Yl.M := Yl.charted
    letI : IsManifold I ∞ Yl.M := Yl.smooth
    letI : T2Space Yl.M := Yl.t2
    letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
    NormalCoordinates.normalChartAt (I := I) Yl.metric
        (seqCenterD inp.decay P L l (alpha : Nat))
        (stageTarget inp P L s k l
          ((NormalCoordinates.normalChartAt (I := I) Yk.metric
            (seqCenterD inp.decay P L k (alpha : Nat))).symm z) gamma) =
      normalTransition (I := I) Yl
        (seqCenterD inp.decay P L l (gamma : Nat))
        (seqCenterD inp.decay P L l (alpha : Nat))
        (normalTransition (I := I) Yk
          (seqCenterD inp.decay P L k (alpha : Nat))
          (seqCenterD inp.decay P L k (gamma : Nat)) z) := by
  rfl

/-- When the direct target lies in the prescribed target-stage source chart,
the local two-transition expression decodes to that same manifold point. -/
theorem stageTarget_local
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) (s : Real) (k l : Nat)
    (alpha gamma : Fin (inp.pack.A s)) (z : E)
    (hsrc :
      let Yk := X.obj (L.φ k)
      let Yl := X.obj (L.φ l)
      letI : TopologicalSpace Yk.M := Yk.topology
      letI : ChartedSpace H Yk.M := Yk.charted
      letI : IsManifold I ∞ Yk.M := Yk.smooth
      letI : T2Space Yk.M := Yk.t2
      letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
      letI : TopologicalSpace Yl.M := Yl.topology
      letI : ChartedSpace H Yl.M := Yl.charted
      letI : IsManifold I ∞ Yl.M := Yl.smooth
      letI : T2Space Yl.M := Yl.t2
      letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
      stageTarget inp P L s k l
          ((NormalCoordinates.normalChartAt (I := I) Yk.metric
            (seqCenterD inp.decay P L k (alpha : Nat))).symm z) gamma ∈
        (NormalCoordinates.normalChartAt (I := I) Yl.metric
          (seqCenterD inp.decay P L l (alpha : Nat))).source) :
    let Yk := X.obj (L.φ k)
    let Yl := X.obj (L.φ l)
    letI : TopologicalSpace Yk.M := Yk.topology
    letI : ChartedSpace H Yk.M := Yk.charted
    letI : IsManifold I ∞ Yk.M := Yk.smooth
    letI : T2Space Yk.M := Yk.t2
    letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
    letI : TopologicalSpace Yl.M := Yl.topology
    letI : ChartedSpace H Yl.M := Yl.charted
    letI : IsManifold I ∞ Yl.M := Yl.smooth
    letI : T2Space Yl.M := Yl.t2
    letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
    (NormalCoordinates.normalChartAt (I := I) Yl.metric
        (seqCenterD inp.decay P L l (alpha : Nat))).symm
      (normalTransition (I := I) Yl
        (seqCenterD inp.decay P L l (gamma : Nat))
        (seqCenterD inp.decay P L l (alpha : Nat))
        (normalTransition (I := I) Yk
          (seqCenterD inp.decay P L k (alpha : Nat))
          (seqCenterD inp.decay P L k (gamma : Nat)) z)) =
      stageTarget inp P L s k l
        ((NormalCoordinates.normalChartAt (I := I) Yk.metric
          (seqCenterD inp.decay P L k (alpha : Nat))).symm z) gamma := by
  letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
  letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
  letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
    (X.obj (L.φ k)).t2TangentBundle
  letI : TopologicalSpace (X.obj (L.φ l)).M := (X.obj (L.φ l)).topology
  letI : ChartedSpace H (X.obj (L.φ l)).M := (X.obj (L.φ l)).charted
  letI : IsManifold I ∞ (X.obj (L.φ l)).M := (X.obj (L.φ l)).smooth
  letI : T2Space (X.obj (L.φ l)).M := (X.obj (L.φ l)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ l)).M) :=
    (X.obj (L.φ l)).t2TangentBundle
  dsimp only
  rw [← stageTarget_chart (I := I) inp P L s k l alpha gamma z]
  exact NormalCoordinates.normalChartAt_left_inv (I := I)
    (X.obj (L.φ l)).metric
    (seqCenterD inp.decay P L l (alpha : Nat)) hsrc

/-- The actual finite-stage center energy has exactly one global minimizer. -/
def HasUniqueStageCenter
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) (s : Real) (hs : 0 ≤ s)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (k l : Nat) (x : (X.obj (L.φ k)).M) : Prop :=
  let Y := X.obj (L.φ l)
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : ConnectedSpace Y.M := hconn (L.φ l)
  let i0 := baseIndex inp.decay inp.realizes inp.pack hs
  ∃! y : Y.M, ∀ z : Y.M,
    CenterOfMass.centerEnergy (I := I) Y.metric
        (fun gamma => rawWeights
          (cutRaw
            (seqAtom inp.decay inp.hD P L inp.pack s k i0)
            (seqAtom inp.decay inp.hD P L inp.pack s k) i0)
          x gamma)
        (stageTarget inp P L s k l x) y ≤
      CenterOfMass.centerEnergy (I := I) Y.metric
        (fun gamma => rawWeights
          (cutRaw
            (seqAtom inp.decay inp.hD P L inp.pack s k i0)
            (seqAtom inp.decay inp.hD P L inp.pack s k) i0)
          x gamma)
        (stageTarget inp P L s k l x) z

/-- The global finite-stage comparison map.  Inside the controlled closed
source ball it selects the unique global center of the actual stage energy;
outside that ball, or when uniqueness fails, it uses the target
basepoint as a harmless totalization. -/
noncomputable def stageComparisonMap
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) (s : Real) (hs : 0 ≤ s)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (k l : Nat) : (X.obj (L.φ k)).M → (X.obj (L.φ l)).M := by
  classical
  exact fun x =>
    if hx : x ∈ L.hatSourceBall inp.decay P s k then
      if huniq : HasUniqueStageCenter inp P L s hs hconn k l x then
        Classical.choose huniq.exists
      else
        (X.obj (L.φ l)).basepoint
    else
      (X.obj (L.φ l)).basepoint

/-- On the controlled source ball, once uniqueness is available, the global
stage map is the chosen unique minimizer. -/
theorem stageCompare_choose
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) (s : Real) (hs : 0 ≤ s)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (k l : Nat) (x : (X.obj (L.φ k)).M)
    (hx : x ∈ L.hatSourceBall inp.decay P s k)
    (huniq : HasUniqueStageCenter inp P L s hs hconn k l x) :
    stageComparisonMap inp P L s hs hconn k l x =
      Classical.choose huniq.exists := by
  simp only [stageComparisonMap, hx, huniq, dite_true]

end HCGCompactness
end DifferentialGeometry
