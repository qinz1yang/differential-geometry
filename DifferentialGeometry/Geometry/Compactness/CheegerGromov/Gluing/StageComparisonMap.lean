import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.ChartFamily
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.MetricCompactness.Inputs
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.AtomConvergence
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Set Bundle Manifold
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Riemannian

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

noncomputable def stageTarget
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) (s : Real) (k l : Nat)
    (x : (X.obj (L.φ k)).M) (gamma : Fin (inp.pack.A s))
    (chart : NormalChartFamily (I := I) X :=
      c2RadiusNormalChartFamily (I := I) X) :
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
  (chart (L.φ l) (seqCenterD inp.decay P L l (gamma : Nat))).hom
    ((chart (L.φ k) (seqCenterD inp.decay P L k (gamma : Nat))).inv x)

@[simp] theorem stageTarget_chart
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) (s : Real) (k l : Nat)
    (alpha gamma : Fin (inp.pack.A s)) (z : E)
    (chart : NormalChartFamily (I := I) X :=
      c2RadiusNormalChartFamily (I := I) X) :
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
    (chart (L.φ l)
        (seqCenterD inp.decay P L l (alpha : Nat))).inv
        (stageTarget inp P L s k l
          ((chart (L.φ k)
            (seqCenterD inp.decay P L k (alpha : Nat))).hom z) gamma
          (chart := chart)) =
      (chart (L.φ l)
          (seqCenterD inp.decay P L l (gamma : Nat))).transition
        (chart (L.φ l)
          (seqCenterD inp.decay P L l (alpha : Nat)))
        ((chart (L.φ k)
            (seqCenterD inp.decay P L k (alpha : Nat))).transition
          (chart (L.φ k)
            (seqCenterD inp.decay P L k (gamma : Nat))) z) := by
  rfl

theorem stageTarget_local
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) (s : Real) (k l : Nat)
    (alpha gamma : Fin (inp.pack.A s)) (z : E)
    {chart : NormalChartFamily (I := I) X}
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
          ((chart (L.φ k)
            (seqCenterD inp.decay P L k (alpha : Nat))).hom z) gamma
          (chart := chart) ∈
        (chart (L.φ l)
          (seqCenterD inp.decay P L l (alpha : Nat))).hom.target) :
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
    (chart (L.φ l)
        (seqCenterD inp.decay P L l (alpha : Nat))).hom
      ((chart (L.φ l)
          (seqCenterD inp.decay P L l (gamma : Nat))).transition
        (chart (L.φ l)
          (seqCenterD inp.decay P L l (alpha : Nat)))
        ((chart (L.φ k)
            (seqCenterD inp.decay P L k (alpha : Nat))).transition
          (chart (L.φ k)
            (seqCenterD inp.decay P L k (gamma : Nat))) z)) =
      stageTarget inp P L s k l
        ((chart (L.φ k)
          (seqCenterD inp.decay P L k (alpha : Nat))).hom z) gamma
        (chart := chart) := by
  let : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  let : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
  let : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
  let : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
  let : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
    (X.obj (L.φ k)).t2TangentBundle
  let : TopologicalSpace (X.obj (L.φ l)).M := (X.obj (L.φ l)).topology
  let : ChartedSpace H (X.obj (L.φ l)).M := (X.obj (L.φ l)).charted
  let : IsManifold I ∞ (X.obj (L.φ l)).M := (X.obj (L.φ l)).smooth
  let : T2Space (X.obj (L.φ l)).M := (X.obj (L.φ l)).t2
  let : T2Space (TangentBundle I (X.obj (L.φ l)).M) :=
    (X.obj (L.φ l)).t2TangentBundle
  dsimp only
  rw [← stageTarget_chart (I := I) inp P L s k l alpha gamma z
    (chart := chart)]
  exact (chart (L.φ l)
    (seqCenterD inp.decay P L l (alpha : Nat))).hom.right_inv hsrc

theorem stageTarget_subseq
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) (s : Real)
    {ψ : Nat → Nat} (hψ : StrictMono ψ) (k l : Nat)
    (chart : NormalChartFamily (I := I) X :=
      c2RadiusNormalChartFamily (I := I) X) :
    stageTarget inp P (L.subseq hψ) s k l (chart := chart) =
      stageTarget inp P L s (ψ k) (ψ l) (chart := chart) := by
  rfl

noncomputable def stageCenterEnergy
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    {ι : Type*} [Fintype ι] (mu : ι → Real) (pts : ι → Y.M)
    (y : Y.M) : Real :=
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  CenterOfMass.centerEnergy (I := I) Y.metric mu pts y

def IsStageCenter
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    {ι : Type*} [Fintype ι] (mu : ι → Real) (pts : ι → Y.M)
    (y : Y.M) : Prop :=
  ∀ z : Y.M,
    stageCenterEnergy (I := I) Y mu pts y ≤
      stageCenterEnergy (I := I) Y mu pts z

omit [FiniteDimensional Real E] [CompleteSpace E] [NeZero (Module.finrank Real E)]
    [I.Boundaryless] in
private theorem stageCenterChoice_heq
    {Y Y' : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {ι : Type*} [Fintype ι]
    {mu mu' : ι → Real} {pts : ι → Y.M} {pts' : ι → Y'.M}
    (hY : Y = Y') (hmu : mu = mu') (hpts : HEq pts pts')
    (h : ∃! y : Y.M, IsStageCenter (I := I) Y mu pts y)
    (h' : ∃! y : Y'.M, IsStageCenter (I := I) Y' mu' pts' y) :
    HEq (Classical.choose h.exists) (Classical.choose h'.exists) := by
  subst Y'
  subst mu'
  have hpts' : pts = pts' := eq_of_heq hpts
  subst pts'
  exact heq_of_eq
    (h.unique (Classical.choose_spec h.exists)
      (Classical.choose_spec h'.exists))

def HasUniqueStageCenter
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) (s : Real) (hs : 0 ≤ s)
    (k l : Nat) (x : (X.obj (L.φ k)).M)
    (chart : NormalChartFamily (I := I) X :=
      c2RadiusNormalChartFamily (I := I) X) : Prop :=
  let Y := X.obj (L.φ l)
  let i0 := baseIndex inp.decay inp.realizes inp.pack hs
  ∃! y : Y.M,
    IsStageCenter (I := I) Y
      (fun gamma => rawWeights
        (cutRaw
          (seqAtom inp.decay inp.hD P L inp.pack s k i0)
          (seqAtom inp.decay inp.hD P L inp.pack s k) i0)
        x gamma)
      (stageTarget inp P L s k l x (chart := chart)) y

theorem uniqueCenter_subseq
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) (s : Real) (hs : 0 ≤ s)
    {ψ : Nat → Nat} (hψ : StrictMono ψ) (k l : Nat)
    (x : (X.obj ((L.subseq hψ).φ k)).M)
    (chart : NormalChartFamily (I := I) X :=
      c2RadiusNormalChartFamily (I := I) X) :
    HasUniqueStageCenter inp P (L.subseq hψ) s hs k l x
        (chart := chart) ↔
      HasUniqueStageCenter inp P L s hs (ψ k) (ψ l) x
        (chart := chart) := by
  have hseq :
      seqAtom inp.decay inp.hD P (L.subseq hψ) inp.pack s k =
        seqAtom inp.decay inp.hD P L inp.pack s (ψ k) := by
    funext gamma
    exact seqAtom_subseq inp.decay inp.hD P L inp.pack s hψ k gamma
  simp only [HasUniqueStageCenter, hseq,
    NetLimitData.subseq_phi, Function.comp_apply]
  rfl

noncomputable def stageComparisonMap
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) (s : Real) (hs : 0 ≤ s)
    (k l : Nat) (x : (X.obj (L.φ k)).M)
    (chart : NormalChartFamily (I := I) X :=
      c2RadiusNormalChartFamily (I := I) X) : (X.obj (L.φ l)).M := by
  classical
  exact
    if hx : x ∈ L.hatSourceBall inp.decay P s k then
      if huniq : HasUniqueStageCenter inp P L s hs k l x
          (chart := chart) then
        Classical.choose huniq.exists
      else
        (X.obj (L.φ l)).basepoint
    else
      (X.obj (L.φ l)).basepoint

theorem stageCompare_choose
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) (s : Real) (hs : 0 ≤ s)
    (k l : Nat) (x : (X.obj (L.φ k)).M)
    {chart : NormalChartFamily (I := I) X}
    (hx : x ∈ L.hatSourceBall inp.decay P s k)
    (huniq : HasUniqueStageCenter inp P L s hs k l x
      (chart := chart)) :
    stageComparisonMap inp P L s hs k l x (chart := chart) =
      Classical.choose huniq.exists := by
  simp only [stageComparisonMap, hx, huniq, dite_true]

theorem stageCompare_default
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) (s : Real) (hs : 0 ≤ s)
    (k l : Nat) (x : (X.obj (L.φ k)).M)
    {chart : NormalChartFamily (I := I) X}
    (hdefault : x ∉ L.hatSourceBall inp.decay P s k ∨
      ¬ HasUniqueStageCenter inp P L s hs k l x
        (chart := chart)) :
    stageComparisonMap inp P L s hs k l x (chart := chart) =
      (X.obj (L.φ l)).basepoint := by
  rcases hdefault with hx | huniq
  · simp only [stageComparisonMap, hx, dite_false]
  · by_cases hx : x ∈ L.hatSourceBall inp.decay P s k
    · simp only [stageComparisonMap, hx, huniq, dite_true, dite_false]
    · simp only [stageComparisonMap, hx, dite_false]

theorem stageCompare_subseq
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) (s : Real) (hs : 0 ≤ s)
    {ψ : Nat → Nat} (hψ : StrictMono ψ) (k l : Nat)
    (chart : NormalChartFamily (I := I) X :=
      c2RadiusNormalChartFamily (I := I) X) :
    stageComparisonMap inp P (L.subseq hψ) s hs k l
        (chart := chart) =
      stageComparisonMap inp P L s hs (ψ k) (ψ l)
        (chart := chart) := by
  classical
  funext x
  have hcenter := uniqueCenter_subseq (I := I) inp P L s hs hψ k l x
    (chart := chart)
  have hseq :
      seqAtom inp.decay inp.hD P (L.subseq hψ) inp.pack s k =
        seqAtom inp.decay inp.hD P L inp.pack s (ψ k) := by
    funext gamma
    exact seqAtom_subseq inp.decay inp.hD P L inp.pack s hψ k gamma
  by_cases hx : x ∈ L.hatSourceBall inp.decay P s (ψ k)
  · have hx' : x ∈ (L.subseq hψ).hatSourceBall inp.decay P s k := by
      change x ∈ (L.subseq hψ).hatSourceBall inp.decay P s k at hx
      exact hx
    by_cases hu : HasUniqueStageCenter inp P L s hs (ψ k) (ψ l) x
        (chart := chart)
    · have hu' : HasUniqueStageCenter inp P (L.subseq hψ) s hs k l x
          (chart := chart) := hcenter.mpr hu
      rw [stageCompare_choose (I := I) inp P (L.subseq hψ) s hs k l x hx' hu',
        stageCompare_choose (I := I) inp P L s hs (ψ k) (ψ l) x hx hu]
      let mu : Fin (inp.pack.A s) → Real := fun gamma => rawWeights
        (cutRaw
          (seqAtom inp.decay inp.hD P (L.subseq hψ) inp.pack s k
            (baseIndex inp.decay inp.realizes inp.pack hs))
          (seqAtom inp.decay inp.hD P (L.subseq hψ) inp.pack s k)
          (baseIndex inp.decay inp.realizes inp.pack hs)) x gamma
      let mu' : Fin (inp.pack.A s) → Real := fun gamma => rawWeights
        (cutRaw
          (seqAtom inp.decay inp.hD P L inp.pack s (ψ k)
            (baseIndex inp.decay inp.realizes inp.pack hs))
          (seqAtom inp.decay inp.hD P L inp.pack s (ψ k))
          (baseIndex inp.decay inp.realizes inp.pack hs)) x gamma
      have hmu : mu = mu' := by
        simp only [mu, mu', hseq]
        rfl
      have hobj : X.obj ((L.subseq hψ).φ l) = X.obj (L.φ (ψ l)) := by
        rfl
      have htarget := congrFun
        (stageTarget_subseq (I := I) inp P L s hψ k l chart) x
      exact eq_of_heq
        (stageCenterChoice_heq (I := I) hobj hmu (heq_of_eq htarget) hu' hu)
    · have hu' : ¬ HasUniqueStageCenter inp P (L.subseq hψ) s hs k l x
          (chart := chart) :=
        fun h => hu (hcenter.mp h)
      rw [stageCompare_default (I := I) inp P (L.subseq hψ) s hs k l x
          (Or.inr hu'),
        stageCompare_default (I := I) inp P L s hs (ψ k) (ψ l) x
          (Or.inr hu)]
      simp only [NetLimitData.subseq_phi, Function.comp_apply]
  · have hx' : x ∉ (L.subseq hψ).hatSourceBall inp.decay P s k := by
      change x ∉ (L.subseq hψ).hatSourceBall inp.decay P s k at hx
      exact hx
    rw [stageCompare_default (I := I) inp P (L.subseq hψ) s hs k l x
        (Or.inl hx'),
      stageCompare_default (I := I) inp P L s hs (ψ k) (ψ l) x
        (Or.inl hx)]
    simp only [NetLimitData.subseq_phi, Function.comp_apply]

theorem stageCmp_base_raw
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) (s : Real) (hs : 0 ≤ s)
    (k l : Nat)
    (chart : NormalChartFamily (I := I) X :=
      c2RadiusNormalChartFamily (I := I) X) :
    stageComparisonMap inp P L s hs k l
        (X.obj (L.φ k)).basepoint (chart := chart) =
      (X.obj (L.φ l)).basepoint := by
  classical
  let Yk := X.obj (L.φ k)
  let Yl := X.obj (L.φ l)
  let : TopologicalSpace Yk.M := Yk.topology
  let : ChartedSpace H Yk.M := Yk.charted
  let : IsManifold I ∞ Yk.M := Yk.smooth
  let : T2Space Yk.M := Yk.t2
  let : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
  let : TopologicalSpace Yl.M := Yl.topology
  let : ChartedSpace H Yl.M := Yl.charted
  let : IsManifold I ∞ Yl.M := Yl.smooth
  let : T2Space Yl.M := Yl.t2
  let : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
  let : SigmaCompactSpace Yl.M := Yl.sigmaCompact
  let : MetricSpace Yk.M := (P (L.φ k)).ms
  let : RiemannianBundle (fun x : Yl.M => TangentSpace I x) :=
    ⟨Yl.metric.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : Yl.M => TangentSpace I x) :=
    ⟨Yl.metric.inner, Yl.metric.contMDiff.continuous, fun _ _ _ => rfl⟩
  have hx : (X.obj (L.φ k)).basepoint ∈
      L.hatSourceBall inp.decay P s k := by
    change Yk.basepoint ∈ Metric.closedBall Yk.basepoint s
    simpa only [Metric.mem_closedBall, dist_self] using hs
  by_cases huniq : HasUniqueStageCenter inp P L s hs k l
      (X.obj (L.φ k)).basepoint (chart := chart)
  · rw [stageCompare_choose (I := I) inp P L s hs k l
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
        seqWeights_base_raw inp.decay inp.hD P L inp.realizes inp.pack hs k
    have hcenterK :
        seqCenterD inp.decay P L k (i0 : Nat) = Yk.basepoint := by
      simp only [i0, baseIndex_val, seqCenterD, seqCenter_zero,
        Option.getD_some, Yk]
    have hcenterL :
        seqCenterD inp.decay P L l (i0 : Nat) = Yl.basepoint := by
      simp only [i0, baseIndex_val, seqCenterD, seqCenter_zero,
        Option.getD_some, Yl]
    have htarget :
        stageTarget inp P L s k l Yk.basepoint i0 (chart := chart) =
          Yl.basepoint := by
      change
        (chart (L.φ l)
            (seqCenterD inp.decay P L l (i0 : Nat))).hom
          ((chart (L.φ k)
            (seqCenterD inp.decay P L k (i0 : Nat))).inv Yk.basepoint) =
          Yl.basepoint
      rw [hcenterK, hcenterL]
      let cK := chart (L.φ k) Yk.basepoint
      let cL := chart (L.φ l) Yl.basepoint
      have hzeroK :
          (0 : E) ∈ cK.hom.source :=
        cK.ball_subset <| by
          simpa only [Metric.mem_ball, dist_zero_right, norm_zero] using
            cK.radius_pos
      have hinvK : cK.inv Yk.basepoint = 0 := by
        calc
          cK.inv Yk.basepoint = cK.inv (cK.hom 0) :=
            congrArg cK.inv cK.map_zero.symm
          _ = 0 := cK.hom.left_inv hzeroK
      change cL.hom (cK.inv Yk.basepoint) = Yl.basepoint
      rw [hinvK]
      exact cL.map_zero
    have hzero :
        CenterOfMass.centerEnergy (I := I) Yl.metric mu
            (stageTarget inp P L s k l Yk.basepoint (chart := chart))
            Yl.basepoint = 0 := by
      simp only [CenterOfMass.centerEnergy]
      rw [Finset.sum_eq_zero, mul_zero]
      intro i _hi
      rcases eq_or_ne i i0 with rfl | hne
      · rw [htarget, Manifold.riemannianEDist_self]
        simp
      · rw [hdelta.2 i hne, zero_mul]
    have hmin : ∀ z : Yl.M,
        CenterOfMass.centerEnergy (I := I) Yl.metric mu
            (stageTarget inp P L s k l Yk.basepoint (chart := chart))
            Yl.basepoint ≤
          CenterOfMass.centerEnergy (I := I) Yl.metric mu
            (stageTarget inp P L s k l Yk.basepoint (chart := chart)) z := by
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

theorem stageCompare_base
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) (s : Real) (hs : 0 ≤ s)
    (k l : Nat)
    (chart : NormalChartFamily (I := I) X :=
      c2RadiusNormalChartFamily (I := I) X) :
    stageComparisonMap inp P L s hs k l
        (X.obj (L.φ k)).basepoint (chart := chart) =
      (X.obj (L.φ l)).basepoint :=
  stageCmp_base_raw inp P L s hs k l chart

end HCGCompactness
end DifferentialGeometry
