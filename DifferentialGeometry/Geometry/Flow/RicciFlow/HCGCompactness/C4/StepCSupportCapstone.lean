import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCProducers
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCHatReadout

set_option autoImplicit false

/-!
# Source-local finite-support capstone

This file assembles the source-chart cover, chart-local limit weights, sparse
two-index point families, and the selected normal-branch readout.  Every source
slot keeps its own chart and weight family.  The only global operation is a
finite maximum of the pair-index thresholds after the local capstones have
been proved.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Filter Set Bundle Manifold
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

/-- A frozen source ball is covered by source-local patches, and one pair-index
tail retains the selected-branch derivative and strict local solution on every
patch.  The joining map is the intrinsic minimizing join produced by the
selected branch. -/
def HasSuppCmFin
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (q : LiveSlot L pb r → NNReal) (δ : LiveSlot L pb r → Real)
    (sourceBall : Set (X.obj (L.φ n)).M)
    (sourcePatch : LiveSlot L pb r → Set (X.obj (L.φ n)).M)
    (mu : LiveSlot L pb r → (X.obj (L.φ n)).M → Fin (pb.A r) → Real)
    (ptsSeq : LiveSlot L pb r → Nat → Nat → (X.obj (L.φ n)).M →
      Fin (pb.A r) → (X.obj (L.φ n)).M) : Prop :=
  let Y := X.obj (L.φ n)
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : ConnectedSpace Y.M := hconn (L.φ n)
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  letI : T3Space Y.M := inferInstance
  letI : RiemannianBundle (fun z : Y.M => TangentSpace I z) :=
    Y.riemBundle (I := I)
  letI : (z : Y.M) → InnerProductSpace Real (TangentSpace I z) :=
    Y.riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun z : Y.M => TangentSpace I z) := Y.riemBundle_cont (I := I)
  letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
  letI : CompleteSpace Y.M :=
    MetricComplete.complete (I := I) Y (hcomplete.complete (L.φ n))
  letI : MetricSpace Y.M := HopfRinow.riemMetricSpace (I := I) (M := Y.M)
  ∃ radSeq : LiveSlot L pb r → Nat → Nat → Y.M → Real,
    sourceBall ⊆ ⋃ alpha : LiveSlot L pb r, sourcePatch alpha ∧
    (∀ alpha, sourcePatch alpha ⊆
      L.hatBall hd D P pb r n alpha.1) ∧
    (∀ alpha, centerAverage.WeightDataOn (sourcePatch alpha)
      (fun _ : Fin (pb.A r) => Set.univ) (mu alpha)) ∧
    (∀ alpha a b x, x ∈ sourcePatch alpha → 0 < radSeq alpha a b x) ∧
    (∀ alpha a b x, x ∈ sourcePatch alpha → ∀ gamma,
      mu alpha x gamma ≠ 0 →
        dist x (ptsSeq alpha a b x gamma) < radSeq alpha a b x) ∧
    (∀ epsilon > 0, ∃ N : Nat, ∀ a ≥ N, ∀ b ≥ N,
      ∀ alpha, ∀ x ∈ sourcePatch alpha,
        radSeq alpha a b x < epsilon) ∧
    ∃ N : Nat, ∀ a ≥ N, ∀ b ≥ N,
      ∀ alpha, ∀ x ∈ sourcePatch alpha,
        let join := minJoin (I := I) Y.metric (normal_enorm (I := I) Y)
        let pts := centerAverage.activeFill (mu alpha) (ptsSeq alpha a b)
          (fun y => y) x
        ∃ hcm : CenterInput (I := I) Y.metric (mu alpha x) pts join x
            (radSeq alpha a b x),
          HasHatCmStrict (I := I) hd P L pb r n hcomplete hconn q δ
            (mu alpha x) pts join x (radSeq alpha a b x) hcm

/-- Global-ball strict local readout obtained from source-local capstones.  The
source chart is an existential witness at each point; this definition does not
select or glue charts or weight families. -/
def HasSourceCmFin
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (q : LiveSlot L pb r → NNReal) (δ : LiveSlot L pb r → Real)
    (sourceBall : Set (X.obj (L.φ n)).M)
    (sourcePatch : LiveSlot L pb r → Set (X.obj (L.φ n)).M)
    (mu : LiveSlot L pb r → (X.obj (L.φ n)).M → Fin (pb.A r) → Real)
    (ptsSeq : LiveSlot L pb r → Nat → Nat → (X.obj (L.φ n)).M →
      Fin (pb.A r) → (X.obj (L.φ n)).M) : Prop :=
  let Y := X.obj (L.φ n)
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : ConnectedSpace Y.M := hconn (L.φ n)
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  letI : T3Space Y.M := inferInstance
  letI : RiemannianBundle (fun z : Y.M => TangentSpace I z) :=
    Y.riemBundle (I := I)
  letI : (z : Y.M) → InnerProductSpace Real (TangentSpace I z) :=
    Y.riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun z : Y.M => TangentSpace I z) := Y.riemBundle_cont (I := I)
  letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
  letI : CompleteSpace Y.M :=
    MetricComplete.complete (I := I) Y (hcomplete.complete (L.φ n))
  letI : MetricSpace Y.M := HopfRinow.riemMetricSpace (I := I) (M := Y.M)
  ∃ radSeq : LiveSlot L pb r → Nat → Nat → Y.M → Real,
    (∀ alpha a b x, x ∈ sourcePatch alpha → 0 < radSeq alpha a b x) ∧
    (∀ alpha a b x, x ∈ sourcePatch alpha → ∀ gamma,
      mu alpha x gamma ≠ 0 →
        dist x (ptsSeq alpha a b x gamma) < radSeq alpha a b x) ∧
    (∀ epsilon > 0, ∃ N : Nat, ∀ a ≥ N, ∀ b ≥ N,
      ∀ alpha, ∀ x ∈ sourcePatch alpha,
        radSeq alpha a b x < epsilon) ∧
    ∃ N : Nat, ∀ a ≥ N, ∀ b ≥ N,
      ∀ x ∈ sourceBall,
        ∃ alpha : LiveSlot L pb r, x ∈ sourcePatch alpha ∧
          let join := minJoin (I := I) Y.metric (normal_enorm (I := I) Y)
          let pts := centerAverage.activeFill (mu alpha) (ptsSeq alpha a b)
            (fun y => y) x
          ∃ hcm : CenterInput (I := I) Y.metric (mu alpha x) pts join x
              (radSeq alpha a b x),
            HasHatCmStrict (I := I) hd P L pb r n hcomplete hconn q δ
              (mu alpha x) pts join x (radSeq alpha a b x) hcm

/-- A common local pair-index tail and the finite source cover give the
global-ball existential-source readout with the same threshold. -/
theorem HasSuppCmFin.toSource
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X} {D : Real}
    {P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j)}
    {L : NetLimitData hd D P} {pb : hd.PackingBound D} {r : Real} {n : Nat}
    {hcomplete : SeqMetricComplete (I := I) X}
    {hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M}
    {q : LiveSlot L pb r → NNReal} {δ : LiveSlot L pb r → Real}
    {sourceBall : Set (X.obj (L.φ n)).M}
    {sourcePatch : LiveSlot L pb r → Set (X.obj (L.φ n)).M}
    {mu : LiveSlot L pb r → (X.obj (L.φ n)).M → Fin (pb.A r) → Real}
    {ptsSeq : LiveSlot L pb r → Nat → Nat → (X.obj (L.φ n)).M →
      Fin (pb.A r) → (X.obj (L.φ n)).M}
    (h : HasSuppCmFin (I := I) hd P L pb r n hcomplete hconn q δ
      sourceBall sourcePatch mu ptsSeq) :
    HasSourceCmFin (I := I) hd P L pb r n hcomplete hconn q δ
      sourceBall sourcePatch mu ptsSeq := by
  classical
  dsimp only [HasSuppCmFin] at h
  rcases h with ⟨radSeq, hcover, _hhat, _hweight, hpos, hactive,
    hsmall, N, hN⟩
  dsimp only [HasSourceCmFin]
  refine ⟨radSeq, hpos, hactive, hsmall, N, ?_⟩
  intro a ha b hb x hx
  rcases Set.mem_iUnion.mp (hcover hx) with ⟨alpha, hxalpha⟩
  exact ⟨alpha, hxalpha, hN a ha b hb alpha x hxalpha⟩

/-- Choose the covering divisor once, extract one master subsequence, and
assemble the finite family of source-local strict center solutions with one
common pair-index tail.  No chartwise weights are compared or glued. -/
theorem MetricCompactBase.exists_supp_cm_fin
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactBase (I := I) X)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (r : Real) (hr : 0 ≤ r) :
    ∃ (aMin : Real) (_haMin : 0 < aMin)
        (inp : MetricCompactnessInputs (I := I) X)
        (L : NetLimitData inp.decay inp.D
          (inp.properMetrics hcomplete hconn))
        (phi : Nat → Nat) (hphi : StrictMono phi)
        (U : LiveSlot L inp.pack r → Set E)
        (C0 C1 : LiveSlot L inp.pack r → Set E)
        (aInf : (alpha : LiveSlot L inp.pack r) →
          Fin (inp.pack.A r) → E → Real)
        (Jinf : (alpha : LiveSlot L inp.pack r) →
          InterSlot L inp.pack r alpha → E → E)
        (Jbarinf : (alpha : LiveSlot L inp.pack r) →
          InterSlot L inp.pack r alpha → E → E)
        (q : LiveSlot L inp.pack r → NNReal)
        (δ : LiveSlot L inp.pack r → Real),
      let P := inp.properMetrics hcomplete hconn
      let Lphi := L.subseq hphi
      let beta := fun (n : Nat) (alpha : LiveSlot L inp.pack r) =>
        seqCenterD inp.decay P Lphi n (alpha.1 : Nat)
      let weightInf := fun (alpha : LiveSlot L inp.pack r) (z : E)
          (gamma : Fin (inp.pack.A r)) =>
        rawWeights
          (cutRaw
            (aInf alpha (baseIndex inp.decay inp.realizes inp.pack hr))
            (aInf alpha) (baseIndex inp.decay inp.realizes inp.pack hr))
          z gamma
      HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1 aInf Jinf Jbarinf ∧
      (∀ gamma : LiveSlot L inp.pack r,
        let Rgamma := L.rInf (gamma.1 : Nat) + 1
        let rhoMin := aMin * inp.decay.mu Rgamma
        0 < q gamma ∧ 0 < δ gamma ∧ 0 < rhoMin ∧
          2 * rhoMin < (q gamma : Real)) ∧
      ∀ᶠ n in Filter.atTop,
        let Y := X.obj (Lphi.φ n)
        letI : TopologicalSpace Y.M := Y.topology
        letI : ChartedSpace H Y.M := Y.charted
        letI : IsManifold I ∞ Y.M := Y.smooth
        letI : IsManifold I 1 Y.M := IsManifold.of_le
          (I := I) (M := Y.M) (n := ∞) (by decide)
        letI : SigmaCompactSpace Y.M := Y.sigmaCompact
        letI : T2Space Y.M := Y.t2
        letI : ConnectedSpace Y.M := hconn (Lphi.φ n)
        letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
        letI : TopologicalSpace.MetrizableSpace Y.M :=
          Manifold.metrizableSpace I Y.M
        letI : T3Space Y.M := inferInstance
        letI : RiemannianBundle (fun z : Y.M => TangentSpace I z) :=
          Y.riemBundle (I := I)
        letI : (z : Y.M) → InnerProductSpace Real (TangentSpace I z) :=
          Y.riemInner (I := I)
        letI : IsContinuousRiemannianBundle E
            (fun z : Y.M => TangentSpace I z) := Y.riemBundle_cont (I := I)
        letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
        letI : CompleteSpace Y.M :=
          MetricComplete.complete (I := I) Y (hcomplete.complete (Lphi.φ n))
        letI : MetricSpace Y.M :=
          HopfRinow.riemMetricSpace (I := I) (M := Y.M)
        let chi := fun (alpha : LiveSlot L inp.pack r) =>
          NormalCoordinates.normalChartAt (I := I) Y.metric (beta n alpha)
        let sourceBall := Lphi.hatSourceBall inp.decay P r n
        let sourcePatch : LiveSlot L inp.pack r → Set Y.M := fun alpha =>
          sourceBall ∩ (chi alpha).source ∩ (chi alpha) ⁻¹' U alpha
        let localWeight := fun (alpha : LiveSlot L inp.pack r)
            (x : Y.M) (gamma : Fin (inp.pack.A r)) =>
          weightInf alpha (chi alpha x) gamma
        let pairPts : (alpha : LiveSlot L inp.pack r) →
            InterSlot L inp.pack r alpha → Nat → Nat → Y.M → Y.M :=
          fun alpha target a b x =>
            (chi alpha).symm
              (normalTransition (I := I) (X.obj (Lphi.φ b))
                (beta b target.1) (beta b alpha)
                (normalTransition (I := I) (X.obj (Lphi.φ a))
                  (beta a alpha) (beta a target.1) (chi alpha x)))
        let pts := fun (alpha : LiveSlot L inp.pack r) =>
          totalPts (X := X) pairPts alpha
        HasCompactCover sourceBall sourcePatch ∧
          HasSuppCmFin (I := I) inp.decay P Lphi inp.pack r n
            hcomplete hconn q δ sourceBall sourcePatch localWeight pts := by
  classical
  obtain ⟨aMin, haMin, hread⟩ :=
    exists_hat_cm_min (I := I) b.normalRadius b.realizes
      hcomplete hconn
  let c0 :=
    (8 * Real.exp b.decay.C / aMin) * b.normalRadius.gpRatio
  obtain ⟨D, hD_one, _hmuD, hc0, h8, _h16, hradD, hradRatio, hcap⟩ :=
    b.exists_item3D c0
  have hD : 0 < D := zero_lt_one.trans hD_one
  let inp := MetricCompactnessInputs.ofBase b D hD hcap
  have h8' : (8 : Real) < inp.normalRadius.gpRatio * inp.D := by
    simpa only [inp, MetricCompactnessInputs.ofBase] using h8
  have hradD' : 2 * item3RadiusFactor inp.decay inp.D < inp.D := by
    simpa only [inp, MetricCompactnessInputs.ofBase] using hradD
  have hradRatio' : 2 * item3RadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D := by
    simpa only [inp, MetricCompactnessInputs.ofBase] using hradRatio
  have hc0' :
      (8 * Real.exp inp.decay.C / aMin) * inp.normalRadius.gpRatio <
        inp.normalRadius.gpRatio * inp.D := by
    simpa only [inp, c0, MetricCompactnessInputs.ofBase] using hc0
  have hphys : 8 * Real.exp inp.decay.C < aMin * inp.D :=
    inp.physScale_of_extra haMin hc0'
  let P := inp.properMetrics hcomplete hconn
  obtain ⟨L, hstable⟩ := inp.exists_stable_net P
  obtain ⟨phi, hphi, U, C0, C1, aInf, Jinf, Jbarinf, hconv, hptsTail⟩ :=
    inp.exists_supp_pts_fin h8' hradD' hradRatio' P L hstable r hr hconn
  let Lphi := L.subseq hphi
  obtain ⟨q, δ, hqdata, hreadTail⟩ :=
    hread inp.hD hphys P Lphi inp.pack r
  refine ⟨aMin, haMin, inp, L, phi, hphi, U, C0, C1, aInf, Jinf, Jbarinf,
    q, δ, ?_⟩
  dsimp only
  refine ⟨hconv, ?_, ?_⟩
  · simpa only [Lphi, NetLimitData.subseq] using hqdata
  · filter_upwards [hptsTail, hreadTail] with n hn hreadN
    let Y := X.obj (Lphi.φ n)
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : ConnectedSpace Y.M := hconn (Lphi.φ n)
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M :=
      Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI : RiemannianBundle (fun z : Y.M => TangentSpace I z) :=
      Y.riemBundle (I := I)
    letI : (z : Y.M) → InnerProductSpace Real (TangentSpace I z) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun z : Y.M => TangentSpace I z) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M :=
      MetricComplete.complete (I := I) Y (hcomplete.complete (Lphi.φ n))
    letI : MetricSpace Y.M :=
      HopfRinow.riemMetricSpace (I := I) (M := Y.M)
    let beta := fun (k : Nat) (alpha : LiveSlot L inp.pack r) =>
      seqCenterD inp.decay P Lphi k (alpha.1 : Nat)
    let weightInf := fun (alpha : LiveSlot L inp.pack r) (z : E)
        (gamma : Fin (inp.pack.A r)) =>
      rawWeights
        (cutRaw
          (aInf alpha (baseIndex inp.decay inp.realizes inp.pack hr))
          (aInf alpha) (baseIndex inp.decay inp.realizes inp.pack hr))
        z gamma
    let chi := fun (alpha : LiveSlot L inp.pack r) =>
      NormalCoordinates.normalChartAt (I := I) Y.metric (beta n alpha)
    let sourceBall := Lphi.hatSourceBall inp.decay P r n
    let sourcePatch : LiveSlot L inp.pack r → Set Y.M := fun alpha =>
      sourceBall ∩ (chi alpha).source ∩ (chi alpha) ⁻¹' U alpha
    let localWeight := fun (alpha : LiveSlot L inp.pack r)
        (x : Y.M) (gamma : Fin (inp.pack.A r)) =>
      weightInf alpha (chi alpha x) gamma
    let pairPts : (alpha : LiveSlot L inp.pack r) →
        InterSlot L inp.pack r alpha → Nat → Nat → Y.M → Y.M :=
      fun alpha target a b x =>
        (chi alpha).symm
          (normalTransition (I := I) (X.obj (Lphi.φ b))
            (beta b target.1) (beta b alpha)
            (normalTransition (I := I) (X.obj (Lphi.φ a))
              (beta a alpha) (beta a target.1) (chi alpha x)))
    let pts := fun (alpha : LiveSlot L inp.pack r) =>
      totalPts (X := X) pairPts alpha
    dsimp only at hn hreadN
    rcases hn with ⟨hcompact, hcover, hhat, hweight, hpts⟩
    change HasCompactCover sourceBall sourcePatch ∧
      HasSuppCmFin (I := I) inp.decay P Lphi inp.pack r n
        hcomplete hconn q δ sourceBall sourcePatch localWeight pts
    refine ⟨hcompact, ?_⟩
    · dsimp only [HasSuppCmFin]
      have hlocal := fun alpha =>
        hreadN.2 alpha (sourcePatch alpha) (hhat alpha)
          (localWeight alpha) (hweight alpha) (pts alpha) (hpts alpha)
      choose radSeq hpos hactive hsmall hcap using hlocal
      refine ⟨radSeq, hcover, hhat, hweight, hpos, hactive, ?_, ?_⟩
      · intro epsilon hepsilon
        exact finite_cover_two_tail hcover
          (fun alpha a b x => radSeq alpha a b x < epsilon)
          (fun alpha => hsmall alpha epsilon hepsilon)
      · exact finite_cover_two_tail hcover _ hcap

/-- Global-ball corollary of `exists_supp_cm_fin`: on the same pair-index tail,
each source point has a source patch retaining the selected-branch strict local
solution.  The witness remains existential and does not define a chart
selector. -/
theorem MetricCompactBase.exists_cm_on_source
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactBase (I := I) X)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (r : Real) (hr : 0 ≤ r) :
    ∃ (aMin : Real) (_haMin : 0 < aMin)
        (inp : MetricCompactnessInputs (I := I) X)
        (L : NetLimitData inp.decay inp.D
          (inp.properMetrics hcomplete hconn))
        (phi : Nat → Nat) (hphi : StrictMono phi)
        (U : LiveSlot L inp.pack r → Set E)
        (aInf : (alpha : LiveSlot L inp.pack r) →
          Fin (inp.pack.A r) → E → Real)
        (q : LiveSlot L inp.pack r → NNReal)
        (δ : LiveSlot L inp.pack r → Real),
      let P := inp.properMetrics hcomplete hconn
      let Lphi := L.subseq hphi
      let beta := fun (n : Nat) (alpha : LiveSlot L inp.pack r) =>
        seqCenterD inp.decay P Lphi n (alpha.1 : Nat)
      let weightInf := fun (alpha : LiveSlot L inp.pack r) (z : E)
          (gamma : Fin (inp.pack.A r)) =>
        rawWeights
          (cutRaw
            (aInf alpha (baseIndex inp.decay inp.realizes inp.pack hr))
            (aInf alpha) (baseIndex inp.decay inp.realizes inp.pack hr))
          z gamma
      (∀ gamma : LiveSlot L inp.pack r,
        let Rgamma := L.rInf (gamma.1 : Nat) + 1
        let rhoMin := aMin * inp.decay.mu Rgamma
        0 < q gamma ∧ 0 < δ gamma ∧ 0 < rhoMin ∧
          2 * rhoMin < (q gamma : Real)) ∧
      ∀ᶠ n in Filter.atTop,
        let Y := X.obj (Lphi.φ n)
        letI : TopologicalSpace Y.M := Y.topology
        letI : ChartedSpace H Y.M := Y.charted
        letI : IsManifold I ∞ Y.M := Y.smooth
        letI : IsManifold I 1 Y.M := IsManifold.of_le
          (I := I) (M := Y.M) (n := ∞) (by decide)
        letI : SigmaCompactSpace Y.M := Y.sigmaCompact
        letI : T2Space Y.M := Y.t2
        letI : ConnectedSpace Y.M := hconn (Lphi.φ n)
        letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
        letI : TopologicalSpace.MetrizableSpace Y.M :=
          Manifold.metrizableSpace I Y.M
        letI : T3Space Y.M := inferInstance
        letI : RiemannianBundle (fun z : Y.M => TangentSpace I z) :=
          Y.riemBundle (I := I)
        letI : (z : Y.M) → InnerProductSpace Real (TangentSpace I z) :=
          Y.riemInner (I := I)
        letI : IsContinuousRiemannianBundle E
            (fun z : Y.M => TangentSpace I z) := Y.riemBundle_cont (I := I)
        letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
        letI : CompleteSpace Y.M :=
          MetricComplete.complete (I := I) Y (hcomplete.complete (Lphi.φ n))
        letI : MetricSpace Y.M :=
          HopfRinow.riemMetricSpace (I := I) (M := Y.M)
        let chi := fun (alpha : LiveSlot L inp.pack r) =>
          NormalCoordinates.normalChartAt (I := I) Y.metric (beta n alpha)
        let sourceBall := Lphi.hatSourceBall inp.decay P r n
        let sourcePatch : LiveSlot L inp.pack r → Set Y.M := fun alpha =>
          sourceBall ∩ (chi alpha).source ∩ (chi alpha) ⁻¹' U alpha
        let localWeight := fun (alpha : LiveSlot L inp.pack r)
            (x : Y.M) (gamma : Fin (inp.pack.A r)) =>
          weightInf alpha (chi alpha x) gamma
        let pairPts : (alpha : LiveSlot L inp.pack r) →
            InterSlot L inp.pack r alpha → Nat → Nat → Y.M → Y.M :=
          fun alpha target a b x =>
            (chi alpha).symm
              (normalTransition (I := I) (X.obj (Lphi.φ b))
                (beta b target.1) (beta b alpha)
                (normalTransition (I := I) (X.obj (Lphi.φ a))
                  (beta a alpha) (beta a target.1) (chi alpha x)))
        let pts := fun (alpha : LiveSlot L inp.pack r) =>
          totalPts (X := X) pairPts alpha
        HasSourceCmFin (I := I) inp.decay P Lphi inp.pack r n
          hcomplete hconn q δ sourceBall sourcePatch localWeight pts := by
  obtain ⟨aMin, haMin, inp, L, phi, hphi, U, _C0, _C1, aInf, _Jinf,
      _Jbarinf, q, δ, _hconv, hqdata, htail⟩ :=
    b.exists_supp_cm_fin hcomplete hconn r hr
  refine ⟨aMin, haMin, inp, L, phi, hphi, U, aInf, q, δ, ?_⟩
  dsimp only
  refine ⟨hqdata, ?_⟩
  filter_upwards [htail] with n hn
  exact hn.2.toSource

end HCGCompactness
end DifferentialGeometry
