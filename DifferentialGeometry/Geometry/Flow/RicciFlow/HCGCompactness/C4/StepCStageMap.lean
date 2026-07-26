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
  (NormalCoordinates.framedChartAt (I := I) Yl.metric
      (seqCenterD inp.decay P L l (gamma : Nat))).symm
    (NormalCoordinates.framedChartAt (I := I) Yk.metric
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
    NormalCoordinates.framedChartAt (I := I) Yl.metric
        (seqCenterD inp.decay P L l (alpha : Nat))
        (stageTarget inp P L s k l
          ((NormalCoordinates.framedChartAt (I := I) Yk.metric
            (seqCenterD inp.decay P L k (alpha : Nat))).symm z) gamma) =
      NormalCoordinates.framedTransition (I := I) Yl.metric
        (seqCenterD inp.decay P L l (gamma : Nat))
        (seqCenterD inp.decay P L l (alpha : Nat))
        (NormalCoordinates.framedTransition (I := I) Yk.metric
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
          ((NormalCoordinates.framedChartAt (I := I) Yk.metric
            (seqCenterD inp.decay P L k (alpha : Nat))).symm z) gamma ∈
        (NormalCoordinates.framedChartAt (I := I) Yl.metric
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
    (NormalCoordinates.framedChartAt (I := I) Yl.metric
        (seqCenterD inp.decay P L l (alpha : Nat))).symm
      (NormalCoordinates.framedTransition (I := I) Yl.metric
        (seqCenterD inp.decay P L l (gamma : Nat))
        (seqCenterD inp.decay P L l (alpha : Nat))
        (NormalCoordinates.framedTransition (I := I) Yk.metric
          (seqCenterD inp.decay P L k (alpha : Nat))
          (seqCenterD inp.decay P L k (gamma : Nat)) z)) =
      stageTarget inp P L s k l
        ((NormalCoordinates.framedChartAt (I := I) Yk.metric
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
  exact (NormalCoordinates.framedChartAt (I := I)
    (X.obj (L.φ l)).metric
    (seqCenterD inp.decay P L l (alpha : Nat))).left_inv hsrc

/-- Refining the net-limit data only reindexes the source and target stages of
the direct finite-stage target point. -/
@[simp] theorem stageTarget_subseq
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) (s : Real)
    {ψ : Nat → Nat} (hψ : StrictMono ψ) (k l : Nat) :
    stageTarget inp P (L.subseq hψ) s k l =
      stageTarget inp P L s (ψ k) (ψ l) := by
  rfl

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

/-- Unique global minimization for the actual stage energy is unchanged by a
further strict reindexing of the net-limit data. -/
theorem uniqueCenter_subseq
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) (s : Real) (hs : 0 ≤ s)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    {ψ : Nat → Nat} (hψ : StrictMono ψ) (k l : Nat)
    (x : (X.obj ((L.subseq hψ).φ k)).M) :
    HasUniqueStageCenter inp P (L.subseq hψ) s hs hconn k l x ↔
      HasUniqueStageCenter inp P L s hs hconn (ψ k) (ψ l) x := by
  have hseq :
      seqAtom inp.decay inp.hD P (L.subseq hψ) inp.pack s k =
        seqAtom inp.decay inp.hD P L inp.pack s (ψ k) := by
    funext gamma
    exact seqAtom_subseq inp.decay inp.hD P L inp.pack s hψ k gamma
  simp only [HasUniqueStageCenter, stageTarget_subseq, hseq,
    NetLimitData.subseq_phi, Function.comp_apply]
  rfl

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

/-- If the controlled source-ball test or unique-center test fails, the total
stage comparison map uses the target basepoint. -/
theorem stageCompare_default
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) (s : Real) (hs : 0 ≤ s)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (k l : Nat) (x : (X.obj (L.φ k)).M)
    (hdefault : x ∉ L.hatSourceBall inp.decay P s k ∨
      ¬ HasUniqueStageCenter inp P L s hs hconn k l x) :
    stageComparisonMap inp P L s hs hconn k l x =
      (X.obj (L.φ l)).basepoint := by
  rcases hdefault with hx | huniq
  · simp only [stageComparisonMap, hx, dite_false]
  · by_cases hx : x ∈ L.hatSourceBall inp.decay P s k
    · simp only [stageComparisonMap, hx, huniq, dite_true, dite_false]
    · simp only [stageComparisonMap, hx, dite_false]

/-- Reindexing the net-limit data only reindexes the two stage arguments of
the chart-independent comparison map. -/
@[simp] theorem stageCompare_subseq
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) (s : Real) (hs : 0 ≤ s)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    {ψ : Nat → Nat} (hψ : StrictMono ψ) (k l : Nat) :
    stageComparisonMap inp P (L.subseq hψ) s hs hconn k l =
      stageComparisonMap inp P L s hs hconn (ψ k) (ψ l) := by
  classical
  funext x
  have hcenter := uniqueCenter_subseq (I := I) inp P L s hs hconn hψ k l x
  have hseq :
      seqAtom inp.decay inp.hD P (L.subseq hψ) inp.pack s k =
        seqAtom inp.decay inp.hD P L inp.pack s (ψ k) := by
    funext gamma
    exact seqAtom_subseq inp.decay inp.hD P L inp.pack s hψ k gamma
  by_cases hx : x ∈ L.hatSourceBall inp.decay P s (ψ k)
  · have hx' : x ∈ (L.subseq hψ).hatSourceBall inp.decay P s k := by
      simpa only [NetLimitData.hatSourceBall_subseq] using hx
    by_cases hu : HasUniqueStageCenter inp P L s hs hconn (ψ k) (ψ l) x
    · have hu' : HasUniqueStageCenter inp P (L.subseq hψ) s hs hconn k l x :=
        hcenter.mpr hu
      rw [stageCompare_choose (I := I) inp P (L.subseq hψ) s hs hconn k l x hx' hu',
        stageCompare_choose (I := I) inp P L s hs hconn (ψ k) (ψ l) x hx hu]
      apply hu.unique
      · simpa only [stageTarget_subseq, hseq, NetLimitData.subseq_phi,
          Function.comp_apply] using Classical.choose_spec hu'.exists
      · exact Classical.choose_spec hu.exists
    · have hu' : ¬ HasUniqueStageCenter inp P (L.subseq hψ) s hs hconn k l x :=
        fun h => hu (hcenter.mp h)
      rw [stageCompare_default (I := I) inp P (L.subseq hψ) s hs hconn k l x
          (Or.inr hu'),
        stageCompare_default (I := I) inp P L s hs hconn (ψ k) (ψ l) x
          (Or.inr hu)]
      simp only [NetLimitData.subseq_phi, Function.comp_apply]
  · have hx' : x ∉ (L.subseq hψ).hatSourceBall inp.decay P s k := by
      simpa only [NetLimitData.hatSourceBall_subseq] using hx
    rw [stageCompare_default (I := I) inp P (L.subseq hψ) s hs hconn k l x
        (Or.inl hx'),
      stageCompare_default (I := I) inp P L s hs hconn (ψ k) (ψ l) x
        (Or.inl hx)]
    simp only [NetLimitData.subseq_phi, Function.comp_apply]

/-- The finite-stage comparison map preserves the pointed basepoint whenever
the source-stage atom family has the item-3 normal-radius control needed by the
canonical normalized weights. -/
theorem stageCompare_base
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) (s : Real) (hs : 0 ≤ s)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (k l : Nat)
    (hgp : Item3GpScaleAt (I := I) inp.decay inp.D P L inp.pack s k) :
    stageComparisonMap inp P L s hs hconn k l
        (X.obj (L.φ k)).basepoint =
      (X.obj (L.φ l)).basepoint := by
  classical
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
  letI : SigmaCompactSpace Yl.M := Yl.sigmaCompact
  letI : ConnectedSpace Yl.M := hconn (L.φ l)
  letI : TopologicalSpace.MetrizableSpace Yl.M :=
    Manifold.metrizableSpace I Yl.M
  letI : T3Space Yl.M := inferInstance
  letI : MetricSpace Yk.M := (P (L.φ k)).ms
  letI : RiemannianBundle (fun x : Yl.M => TangentSpace I x) :=
    ⟨Yl.metric.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : Yl.M => TangentSpace I x) :=
    ⟨Yl.metric.inner, Yl.metric.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace Yl.M := HopfRinow.riemMetricSpace (I := I) (M := Yl.M)
  have hx : (X.obj (L.φ k)).basepoint ∈
      L.hatSourceBall inp.decay P s k := by
    change Yk.basepoint ∈ Metric.closedBall Yk.basepoint s
    simpa only [Metric.mem_closedBall, dist_self] using hs
  by_cases huniq : HasUniqueStageCenter inp P L s hs hconn k l
      (X.obj (L.φ k)).basepoint
  · rw [stageCompare_choose (I := I) inp P L s hs hconn k l
      Yk.basepoint hx huniq]
    let i0 := baseIndex inp.decay inp.realizes inp.pack hs
    let mu := fun gamma : Fin (inp.pack.A s) =>
      rawWeights
        (cutRaw
          (seqAtom inp.decay inp.hD P L inp.pack s k i0)
          (seqAtom inp.decay inp.hD P L inp.pack s k) i0)
        Yk.basepoint gamma
    have hdelta : mu i0 = 1 ∧ ∀ j, j ≠ i0 → mu j = 0 := by
      simpa only [mu, i0] using
        seqWeights_base inp.decay inp.hD P L inp.realizes inp.pack hs k hgp
    have hcenterK :
        seqCenterD inp.decay P L k (i0 : Nat) = Yk.basepoint := by
      simp only [i0, baseIndex_val, seqCenterD, seqCenter_zero,
        Option.getD_some, Yk]
    have hcenterL :
        seqCenterD inp.decay P L l (i0 : Nat) = Yl.basepoint := by
      simp only [i0, baseIndex_val, seqCenterD, seqCenter_zero,
        Option.getD_some, Yl]
    have htarget :
        stageTarget inp P L s k l Yk.basepoint i0 = Yl.basepoint := by
      change
        (NormalCoordinates.framedChartAt (I := I) Yl.metric
            (seqCenterD inp.decay P L l (i0 : Nat))).symm
          (NormalCoordinates.framedChartAt (I := I) Yk.metric
            (seqCenterD inp.decay P L k (i0 : Nat)) Yk.basepoint) =
          Yl.basepoint
      rw [hcenterK, hcenterL, NormalCoordinates.framedChart_centre]
      change NormalCoordinates.framedExpDiffeo (I := I) Yl.metric
        Yl.basepoint (0 : E) = Yl.basepoint
      exact NormalCoordinates.framedExp_zero (I := I) Yl.metric Yl.basepoint
    have hzero :
        CenterOfMass.centerEnergy (I := I) Yl.metric mu
            (stageTarget inp P L s k l Yk.basepoint) Yl.basepoint = 0 := by
      simp only [CenterOfMass.centerEnergy]
      rw [Finset.sum_eq_zero, mul_zero]
      intro i _hi
      rcases eq_or_ne i i0 with rfl | hne
      · rw [htarget, Manifold.riemannianEDist_self]
        simp
      · rw [hdelta.2 i hne, zero_mul]
    have hmin : ∀ z : Yl.M,
        CenterOfMass.centerEnergy (I := I) Yl.metric mu
            (stageTarget inp P L s k l Yk.basepoint) Yl.basepoint ≤
          CenterOfMass.centerEnergy (I := I) Yl.metric mu
            (stageTarget inp P L s k l Yk.basepoint) z := by
      intro z
      rw [hzero]
      simp only [CenterOfMass.centerEnergy]
      refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => ?_)
      rcases eq_or_ne i i0 with rfl | hne
      · rw [hdelta.1]
        positivity
      · rw [hdelta.2 i hne, zero_mul]
    apply huniq.unique
    · exact Classical.choose_spec huniq.exists
    · exact hmin
  · simp only [stageComparisonMap, hx, huniq, dite_true, dite_false]

end HCGCompactness
end DifferentialGeometry
