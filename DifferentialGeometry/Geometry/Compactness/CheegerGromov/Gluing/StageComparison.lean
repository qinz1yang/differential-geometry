import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.ChartFamily
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.StageComparisonMap
import DifferentialGeometry.Analysis.Calculus.DerivativePerturbation
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.Fill
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.CenterRootConvergence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.CenterOfMass.NormalCoordinateStrictConvexity
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.CenterOfMass.BranchConstruction
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.CenterOfMass.NormalCoordinateHessian
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.CenterEquationSelection
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.Support
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.MetricExtension
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.CenterOfMass.ChartSolution
import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

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
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

theorem uniqueStage_of_fill
    (inp : MetricCompactCore (I := I) X)
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
    (chart : NormalChartFamily (I := I) X :=
      c2RadiusNormalChartFamily (I := I) X)
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
        (centerAverage.activeFill mu
          (stageTarget inp P L s k l (chart := chart)) qstar x)
        join (p x) (rad x)) :
    HasUniqueStageCenter inp P L s hs k l x (chart := chart) := by
  let Y := X.obj (L.φ l)
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : ConnectedSpace Y.M := hconn (L.φ l)
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let i0 := baseIndex inp.decay inp.realizes inp.pack hs
  let mu := fun (y : (X.obj (L.φ k)).M) (gamma : Fin (inp.pack.A s)) =>
    rawWeights
      (cutRaw
        (seqAtom inp.decay inp.hD P L inp.pack s k i0)
        (seqAtom inp.decay inp.hD P L inp.pack s k) i0)
      y gamma
  have huniq := centerAverage.uniqueMin_activeFill (I := I) Y.metric mu
    (stageTarget inp P L s k l (chart := chart)) qstar join p rad x hcm
  simpa only [HasUniqueStageCenter, IsStageCenter, stageCenterEnergy, i0, mu] using huniq

theorem stageCompare_eq_cm
    (inp : MetricCompactCore (I := I) X)
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
    (chart : NormalChartFamily (I := I) X :=
      c2RadiusNormalChartFamily (I := I) X)
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
        (centerAverage.activeFill mu
          (stageTarget inp P L s k l (chart := chart)) qstar x)
        join (p x) (rad x)) :
    stageComparisonMap inp P L s hs k l x (chart := chart) =
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
        (centerAverage.activeFill mu
          (stageTarget inp P L s k l (chart := chart)) qstar x)
        join (p x) (rad x) hcm := by
  let Y := X.obj (L.φ l)
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : ConnectedSpace Y.M := hconn (L.φ l)
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let i0 := baseIndex inp.decay inp.realizes inp.pack hs
  let mu := fun (y : (X.obj (L.φ k)).M) (gamma : Fin (inp.pack.A s)) =>
    rawWeights
      (cutRaw
        (seqAtom inp.decay inp.hD P L inp.pack s k i0)
        (seqAtom inp.decay inp.hD P L inp.pack s k) i0)
      y gamma
  let q := centerOfMass (I := I) Y.metric (mu x)
    (centerAverage.activeFill mu
      (stageTarget inp P L s k l (chart := chart)) qstar x)
    join (p x) (rad x) hcm
  change stageComparisonMap inp P L s hs k l x (chart := chart) = q
  have huniq := uniqueStage_of_fill (I := I) inp P L s hs hconn k l
    qstar join p rad x (chart := chart) hcm
  rw [stageCompare_choose (I := I) inp P L s hs k l x hx huniq]
  apply huniq.unique
  · exact Classical.choose_spec huniq.exists
  · intro z
    unfold stageCenterEnergy
    rw [← centerAverage.energy_activeFill (I := I) Y.metric mu
      (stageTarget inp P L s k l (chart := chart)) qstar x q,
      ← centerAverage.energy_activeFill (I := I) Y.metric mu
        (stageTarget inp P L s k l (chart := chart)) qstar x z]
    exact centerOfMass.min hcm z

theorem HasSuppConvData.pts_target_tail
    (inp : MetricCompactnessInputs (I := I) X)
    (h8 : (8 : Real) < inp.normalRadius.gpRatio * inp.D)
    (hradRatio : 2 * exponentialBallRadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P)
    (hstable : ∀ a b : Nat,
      (∀ᶠ k in Filter.atTop,
        BInter inp.decay inp.D P L.lamInf a b (L.φ k)) ∨
      (∀ᶠ k in Filter.atTop,
        ¬ BInter inp.decay inp.D P L.lamInf a b (L.φ k)))
    {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (hdata : HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf) :
    ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N,
      ∀ (alpha : LiveSlot L inp.pack r) (z : E), z ∈ U alpha →
        ∀ gamma : Fin (inp.pack.A r),
          stageWeightSub inp.toCore P L hr phi hphi alpha k z gamma ≠ 0 →
            let Lphi := L.subseq hphi
            let Yk := X.obj (Lphi.φ k)
            let Yl := X.obj (Lphi.φ l)
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
            let chiK := NormalCoordinates.normalChartAt (I := I) Yk.metric
              (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
            let chiL := NormalCoordinates.normalChartAt (I := I) Yl.metric
              (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
            chiL.symm (stagePtsSub inp.toCore P L phi hphi alpha k l z gamma) =
                stageTarget inp.toCore P Lphi r k l (chiK.symm z) gamma ∧
              chiL (stageTarget inp.toCore P Lphi r k l (chiK.symm z) gamma) =
                stagePtsSub inp.toCore P L phi hphi alpha k l z gamma := by
  classical
  let Lphi := L.subseq hphi
  let (alpha : LiveSlot L inp.pack r) :
      Finite (InterSlot L inp.pack r alpha) :=
    Finite.of_injective
      (fun target : InterSlot L inp.pack r alpha => target.1.1)
      (by
        intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        exact hab)
  have hpts := hdata.pts_eq_ne inp h8 hradRatio P L hstable hr
    phi hphi U C0 C1 aInf Jinf Jbarinf
  obtain ⟨hgp, hrad⟩ := inp.exponential_scale_tails h8 hradRatio P L r
  have hgpPhi : ExponentialRadiusScaleTail (I := I) inp.decay inp.D P
      Lphi inp.pack r :=
    hgp.subseq inp.decay inp.D P L inp.pack r hphi
  have hradPhi : ExponentialBallRadiusTail (I := I) inp.decay inp.D P
      Lphi inp.pack r (exponentialBallRadiusFactor inp.decay inp.D) :=
    hrad.subseq inp.decay inp.D P L inp.pack r
      (exponentialBallRadiusFactor inp.decay inp.D) hphi
  have hcenters : ∀ᶠ k in Filter.atTop,
      ∀ beta : LiveSlot L inp.pack r,
        seqCenter inp.decay inp.D P (Lphi.φ k) (beta.1 : Nat) =
          some (seqCenterD inp.decay P Lphi k (beta.1 : Nat)) :=
    Filter.eventually_all.mpr fun beta =>
      seqCenterD_live inp.decay P Lphi (beta.1 : Nat) (by
        simpa only [Lphi, NetLimitData.subseq] using beta.2)
  have hfactor : (8 : Real) ≤ exponentialBallRadiusFactor inp.decay inp.D := by
    have hExp : (1 : Real) ≤
        Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0)) := by
      rw [show (1 : Real) = Real.exp 0 from Real.exp_zero.symm]
      exact Real.exp_le_exp.mpr
        (mul_nonneg inp.decay.C_nonneg
          (by nlinarith [(inp.decay.lambda_pos inp.hD 0).le]))
    rw [exponentialBallRadiusFactor]
    nlinarith
  have hrev : ∀ᶠ l in Filter.atTop,
      ∀ (alpha : LiveSlot L inp.pack r)
        (target : InterSlot L inp.pack r alpha),
        NormalOverlapOn (I := I) (X.obj (Lphi.φ l))
          (seqCenterD inp.decay P Lphi l (target.1.1 : Nat))
          (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
          (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))) := by
    refine Filter.eventually_all.mpr fun alpha => ?_
    refine Filter.eventually_all.mpr fun target => ?_
    have hinterRev : ∀ᶠ n in Filter.atTop,
        BInter inp.decay inp.D P L.lamInf
          (target.1.1 : Nat) (alpha.1 : Nat) (L.φ n) :=
      target.2.mono fun _ hn =>
        BInter.symm inp.decay inp.D P L.lamInf hn
    have ht := hphi.tendsto_atTop.eventually
      (inp.pair_overlap_tail hradRatio P L r
        target.1 alpha hinterRev)
    exact ht.mono fun l hl => by
      rw [show Lphi = L.subseq hphi from rfl, seqCenterD_subseq]
      exact hl.2.2.2.2.2.1
  have hall := hpts.and (hgpPhi.and (hradPhi.and (hcenters.and hrev)))
  rw [Filter.eventually_atTop] at hall
  rcases hall with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro k hk l hl
  rcases hN k hk with ⟨hptsK, hgpK, hradK, hcentersK, _hrevK⟩
  have hrevL := (hN l hl).2.2.2.2
  intro alpha z hz gamma hweight
  let Yk := X.obj (Lphi.φ k)
  let Yl := X.obj (Lphi.φ l)
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
  obtain ⟨target, htarget, hraw⟩ :=
    hptsK alpha l z hz gamma hweight
  subst gamma
  have hGpGamma : 8 * L.lamInf (target.1.1 : Nat) ≤
      expMapC2Radius (I := I) Yk.metric
        (seqCenterD inp.decay P Lphi k (target.1.1 : Nat)) := by
    have hscale : 8 * Lphi.lamInf (target.1.1 : Nat) ≤
        exponentialBallRadiusFactor inp.decay inp.D *
          Lphi.lamInf (target.1.1 : Nat) :=
      mul_le_mul_of_nonneg_right hfactor
        (inp.decay.lambda_pos inp.hD
          (L.rInf (target.1.1 : Nat))).le
    have hcenter := hcentersK target.1
    have hradTarget := hradK target.1.1
      (seqCenterD inp.decay P Lphi k (target.1.1 : Nat)) (by
        simpa only using hcenter)
    simpa only [Lphi, NetLimitData.subseq_lamInf] using
      hscale.trans hradTarget.2
  have hgpOrig : ExponentialRadiusScaleAt (I := I) inp.decay inp.D P
      L inp.pack r (phi k) := by
    intro delta c hc
    simpa only [Lphi, NetLimitData.subseq_phi, Function.comp_apply,
      NetLimitData.subseq_lamInf] using hgpK delta c hc
  have hweightOrig :
      stageWeight inp P L hr alpha (phi k) z target.1.1 ≠ 0 := by
    simpa only [stageWeight, stageWeightSub_eq, rawWeights, cutRaw,
      seqAtomChart, NormalChartFamily.hom, c2RadiusNormalChartFamily,
      c2_radius_normal_ball_chart_apply, MetricCompactnessInputs.toCore] using hweight
  have hsmall : normalTransition (I := I) Yk
        (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
        (seqCenterD inp.decay P Lphi k (target.1.1 : Nat)) z ∈
      Metric.closedBall 0 (6 * L.lamInf (target.1.1 : Nat)) := by
    have hs := stageWeight_small inp P L hr alpha (phi k) hgpOrig
      target.1.1 (by
        simpa only [Yk, Lphi, NetLimitData.subseq_phi, Function.comp_apply,
          seqCenterD_subseq] using hGpGamma) z hweightOrig
    simpa only [Yk, Lphi, NetLimitData.subseq_phi, Function.comp_apply,
      seqCenterD_subseq] using hs
  have hv : normalTransition (I := I) Yk
        (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
        (seqCenterD inp.decay P Lphi k (target.1.1 : Nat)) z ∈
      Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)) := by
    rw [Metric.mem_ball] at ⊢
    rw [Metric.mem_closedBall] at hsmall
    have hlam : 0 < L.lamInf (target.1.1 : Nat) :=
      inp.decay.lambda_pos inp.hD (L.rInf (target.1.1 : Nat))
    nlinarith
  have hU8 : U alpha ⊆
      Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)) := by
    have hdata' := hdata
    dsimp only [HasSuppConvData] at hdata'
    exact hdata'.2.1 alpha
  have hGpAlpha : 8 * L.lamInf (alpha.1 : Nat) ≤
      expMapC2Radius (I := I) Yk.metric
        (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) := by
    have hscale : 8 * Lphi.lamInf (alpha.1 : Nat) ≤
        exponentialBallRadiusFactor inp.decay inp.D *
          Lphi.lamInf (alpha.1 : Nat) :=
      mul_le_mul_of_nonneg_right hfactor
        (inp.decay.lambda_pos inp.hD (L.rInf (alpha.1 : Nat))).le
    have hcenter := hcentersK alpha
    have hradAlpha := hradK alpha.1
      (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) (by
        simpa only using hcenter)
    simpa only [Lphi, NetLimitData.subseq_lamInf] using
      hscale.trans hradAlpha.2
  have hzNorm : ‖z‖ < expMapC2Radius (I := I) Yk.metric
      (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) := by
    have hz8 : ‖z‖ < 8 * L.lamInf (alpha.1 : Nat) := by
      simpa only [Metric.mem_ball, dist_zero_right] using hU8 hz
    exact hz8.trans_le hGpAlpha
  have hzExpSrc : z ∈
      (NormalCoordinates.expMapDiffeo (I := I) Yk.metric
        (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))).source :=
    mem_expMapDiffeo_source_of_norm_lt_radius (I := I) Yk.metric
      (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) hzNorm
  have hzChartSrc : z ∈
      (NormalCoordinates.normalChartAt (I := I) Yk.metric
        (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))).symm.source := by
    change z ∈ (NormalCoordinates.normalChartAt (I := I) Yk.metric
      (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))).target
    simpa only [NormalCoordinates.normalChartAt_target_eq] using hzExpSrc
  have hchiK :
      (NormalCoordinates.normalChartAt (I := I) Yk.metric
          (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))).symm z =
        NormalCoordinates.expMapDiffeo (I := I) Yk.metric
          (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) z := by
    rw [NormalCoordinates.normalChartAt_symm_apply (I := I) Yk.metric
      (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) hzChartSrc]
    exact (NormalCoordinates.expMapDiffeo_apply_eq (I := I) Yk.metric
      (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) hzExpSrc).symm
  have hsrc : stageTarget inp.toCore P Lphi r k l
        ((NormalCoordinates.normalChartAt (I := I) Yk.metric
          (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))).symm z)
        target.1.1 ∈
      (NormalCoordinates.normalChartAt (I := I) Yl.metric
        (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))).source := by
    have hov := (hrevL alpha target _ hv).2
    rw [hchiK]
    simpa only [stageTarget, normalTransition, Yk, Yl,
      MetricCompactnessInputs.toCore, c2RadiusNormalChartFamily, c2_radius_normal_ball_chart_inv,
      c2_radius_normal_ball_chart_apply] using hov
  rw [hraw]
  constructor
  · have hchart :
        NormalCoordinates.normalChartAt (I := I) Yl.metric
            (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
            (stageTarget inp.toCore P Lphi r k l
              ((NormalCoordinates.normalChartAt (I := I) Yk.metric
                (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))).symm z)
              target.1.1) =
          normalTransition (I := I) Yl
            (seqCenterD inp.decay P Lphi l (target.1.1 : Nat))
            (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
            (normalTransition (I := I) Yk
              (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
              (seqCenterD inp.decay P Lphi k (target.1.1 : Nat)) z) := by
      rw [hchiK]
      simpa only [MetricCompactnessInputs.toCore, c2RadiusNormalChartFamily,
        c2_radius_normal_ball_chart_inv, c2_radius_normal_ball_chart_transition, c2_radius_normal_ball_chart_apply] using
        (stageTarget_chart (I := I) inp.toCore P Lphi r k l
          alpha.1 target.1.1 z
            (chart := c2RadiusNormalChartFamily (I := I) X))
    rw [← hchart]
    exact (NormalCoordinates.normalChartAt (I := I) Yl.metric
      (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))).left_inv hsrc
  · exact stageTarget_chart (I := I) inp.toCore P Lphi r k l
      alpha.1 target.1.1 z
        (chart := c2RadiusNormalChartFamily (I := I) X)

theorem HasSuppConvData.pts_target_dist
    (inp : MetricCompactnessInputs (I := I) X)
    (h8 : (8 : Real) < inp.normalRadius.gpRatio * inp.D)
    (hradRatio : 2 * exponentialBallRadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P)
    (hstable : ∀ a b : Nat,
      (∀ᶠ k in Filter.atTop,
        BInter inp.decay inp.D P L.lamInf a b (L.φ k)) ∨
      (∀ᶠ k in Filter.atTop,
        ¬ BInter inp.decay inp.D P L.lamInf a b (L.φ k)))
    {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (hdata : HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf)
    (alpha : LiveSlot L inp.pack r)
    (eps : Real) (heps : 0 < eps) :
    ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N, ∀ z ∈ C0 alpha,
      ∀ gamma : Fin (inp.pack.A r),
        stageWeightSub inp P L hr phi hphi alpha k z gamma ≠ 0 →
          let Lphi := L.subseq hphi
          let Yk := X.obj (Lphi.φ k)
          let Yl := X.obj (Lphi.φ l)
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
          letI : MetricSpace Yl.M := (P (Lphi.φ l)).ms
          let chiK := NormalCoordinates.normalChartAt (I := I) Yk.metric
            (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
          let chiL := NormalCoordinates.normalChartAt (I := I) Yl.metric
            (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
          dist (chiL.symm z)
            (stageTarget inp P Lphi r k l (chiK.symm z) gamma) < eps := by
  obtain ⟨_hU, _hC0, _hC1, hC01, hC1U⟩ :=
    hdata.core_on inp P L r hr U C0 C1 aInf Jinf Jbarinf alpha
  have hC0U : C0 alpha ⊆ U alpha :=
    hC01.trans (interior_subset.trans hC1U)
  obtain ⟨Nt, htarget⟩ := hdata.pts_target_tail inp h8 hradRatio
    P L hstable hr phi hphi U C0 C1 aInf Jinf Jbarinf
  obtain ⟨Nd, hdist⟩ := hdata.pts_dist_tail inp P L hr phi hphi U C0 C1
    aInf Jinf Jbarinf alpha eps heps
  refine ⟨max Nt Nd, ?_⟩
  intro k hk l hl z hz gamma hweight
  have hkT : Nt ≤ k := (le_max_left Nt Nd).trans hk
  have hlT : Nt ≤ l := (le_max_left Nt Nd).trans hl
  have hkD : Nd ≤ k := (le_max_right Nt Nd).trans hk
  have hlD : Nd ≤ l := (le_max_right Nt Nd).trans hl
  have heq := htarget k hkT l hlT alpha z (hC0U hz) gamma hweight
  have hclose := hdist k hkD l hlD z hz gamma
  dsimp only at heq ⊢
  rw [← heq.1]
  exact hclose

theorem HasSuppConvData.actual_cm_tail
    (inp : MetricCompactnessInputs (I := I) X)
    (aMin : Real) (haMin : 0 < aMin)
    (hphys : 8 * Real.exp inp.decay.C < aMin * inp.D)
    (h8 : (8 : Real) < inp.normalRadius.gpRatio * inp.D)
    (hradRatio : 2 * exponentialBallRadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P)
    (hstable : ∀ a b : Nat,
      (∀ᶠ k in Filter.atTop,
        BInter inp.decay inp.D P L.lamInf a b (L.φ k)) ∨
      (∀ᶠ k in Filter.atTop,
        ¬ BInter inp.decay inp.D P L.lamInf a b (L.φ k)))
    {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (hdata : HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (q : LiveSlot L inp.pack r → NNReal)
    (δ : LiveSlot L inp.pack r → Real)
    (hqdata : ∀ gamma : LiveSlot L inp.pack r,
      let rho := aMin * inp.decay.mu (L.rInf (gamma.1 : Nat) + 1)
      0 < q gamma ∧ 0 < δ gamma ∧ 0 < rho ∧
        2 * rho < (q gamma : Real))
    (hqAcc : ∀ gamma : LiveSlot L inp.pack r,
      3 * inp.normalBounds.metricC 1 * (2 * (q gamma : Real)) ^ 2 ≤
        (2 / 3 : Real) * (q gamma : Real))
    (hbranch : ∀ᶠ n in Filter.atTop,
      HasLiveBrFull (I := I) P (L.subseq hphi) inp.pack r n
        hcomplete hconn aMin q δ)
    (hscale : ∀ᶠ n in Filter.atTop,
      ∀ gamma : LiveSlot L inp.pack r,
        let Lphi := L.subseq hphi
        let rho := aMin * inp.decay.mu (Lphi.rInf (gamma.1 : Nat) + 1)
        let x := seqCenterD inp.decay P Lphi n (gamma.1 : Nat)
        letI : TopologicalSpace (X.obj (Lphi.φ n)).M :=
          (X.obj (Lphi.φ n)).topology
        letI : ChartedSpace H (X.obj (Lphi.φ n)).M :=
          (X.obj (Lphi.φ n)).charted
        letI : IsManifold I ∞ (X.obj (Lphi.φ n)).M :=
          (X.obj (Lphi.φ n)).smooth
        letI : T2Space (TangentBundle I (X.obj (Lphi.φ n)).M) :=
          (X.obj (Lphi.φ n)).t2TangentBundle
        Metric.ball (0 : E) rho ⊆
            normalQuarter (I := I) (X.obj (Lphi.φ n)) x ∧
          rho ≤ inp.normalBounds.radius (Lphi.φ n) x ∧
          rho / 2 ≤ expRadiusGp
            (I := I) (X.obj (Lphi.φ n)).metric x)
    (alpha : LiveSlot L inp.pack r)
    (eps : Real) (heps : 0 < eps) :
    ∃ rad : Real, 0 < rad ∧ rad < eps ∧
      ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N, ∀ z ∈ C0 alpha,
        let Lphi := L.subseq hphi
        let Yk := X.obj (Lphi.φ k)
        let Yl := X.obj (Lphi.φ l)
        letI : TopologicalSpace Yk.M := Yk.topology
        letI : ChartedSpace H Yk.M := Yk.charted
        letI : IsManifold I ∞ Yk.M := Yk.smooth
        letI : T2Space Yk.M := Yk.t2
        letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
        letI : TopologicalSpace Yl.M := Yl.topology
        letI : ChartedSpace H Yl.M := Yl.charted
        letI : IsManifold I ∞ Yl.M := Yl.smooth
        letI : IsManifold I 1 Yl.M := IsManifold.of_le
          (I := I) (M := Yl.M) (n := ∞) (by decide)
        letI : SigmaCompactSpace Yl.M := Yl.sigmaCompact
        letI : T2Space Yl.M := Yl.t2
        letI : ConnectedSpace Yl.M := hconn (Lphi.φ l)
        letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
        letI : TopologicalSpace.MetrizableSpace Yl.M :=
          Manifold.metrizableSpace I Yl.M
        letI : T3Space Yl.M := inferInstance
        letI : RiemannianBundle (fun y : Yl.M ↦ TangentSpace I y) :=
          Yl.riemBundle (I := I)
        letI : (y : Yl.M) → InnerProductSpace Real (TangentSpace I y) :=
          Yl.riemInner (I := I)
        letI : IsContinuousRiemannianBundle E
            (fun y : Yl.M ↦ TangentSpace I y) := Yl.riemBundle_cont (I := I)
        letI : EMetricSpace Yl.M := Yl.emetricSpace (I := I)
        letI : CompleteSpace Yl.M :=
          MetricComplete.complete (I := I) Yl (hcomplete.complete (Lphi.φ l))
        letI : MetricSpace Yl.M :=
          HopfRinow.riemMetricSpace (I := I) (M := Yl.M)
        let chiK := NormalCoordinates.normalChartAt (I := I) Yk.metric
          (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
        let chiL := NormalCoordinates.normalChartAt (I := I) Yl.metric
          (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
        let mu := stageWeightSub inp P L hr phi hphi alpha k
        let stagePts := fun w gamma =>
          stageTarget inp P Lphi r k l (chiK.symm w) gamma
        let qstar := fun w => chiL.symm w
        let join := minJoin (I := I) Yl.metric (normal_enorm (I := I) Yl)
        ∃ hcm : CenterInput (I := I) Yl.metric (mu z)
            (centerAverage.activeFill mu stagePts qstar z)
            join (qstar z) rad,
          HasChartCmSol (I := I) Yl (hcomplete.complete (Lphi.φ l))
            (hconn (Lphi.φ l))
            (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
            (c2RadiusNormalBallChart (I := I) Yl
              (seqCenterD inp.decay P Lphi l (alpha.1 : Nat)))
            (q := q alpha) (delta := δ alpha) (mu z)
            (centerAverage.activeFill mu stagePts qstar z)
            join (qstar z) rad hcm ∧
          dist
              (chiL (centerOfMass (I := I) Yl.metric (mu z)
                (centerAverage.activeFill mu stagePts qstar z)
                join (qstar z) rad hcm))
              z ≤ 4 * rad := by
  let Lphi := L.subseq hphi
  let rhoBase := aMin * inp.decay.mu (L.rInf (alpha.1 : Nat) + 1)
  let gap := rhoBase / 2 - 4 * L.lamInf (alpha.1 : Nat)
  have hgap : 0 < gap := by
    dsimp only [gap, rhoBase]
    linarith [lamInf_lt_halfMin inp.decay inp.hD hphys P L
      (alpha.1 : Nat)]
  let rad := min (gap / 12) (eps / 2)
  have hrad : 0 < rad := by
    dsimp only [rad]
    exact lt_min (div_pos hgap (by norm_num)) (div_pos heps (by norm_num))
  have hradEps : rad < eps := by
    have hle : rad ≤ eps / 2 := min_le_right _ _
    linarith
  have hcageReal : 4 * L.lamInf (alpha.1 : Nat) + 6 * rad <
      rhoBase / 2 := by
    have hradGap : rad ≤ gap / 12 := min_le_left _ _
    dsimp only [gap] at hradGap
    nlinarith
  have hcage : ENNReal.ofReal
        (4 * L.lamInf (alpha.1 : Nat) + 6 * rad) <
      ENNReal.ofReal (rhoBase / 2) := by
    exact (ENNReal.ofReal_lt_ofReal_iff
      (div_pos (mul_pos haMin (inp.decay.mu_pos _)) (by norm_num))).2 (by
        simpa only [rhoBase] using hcageReal)
  obtain ⟨_hgp, _hradTail⟩ :=
    inp.exponential_scale_tails h8 hradRatio P L r
  have hweightEv := hdata.weightSub_ev inp P L hr phi hphi
    U C0 C1 aInf Jinf Jbarinf
  rw [Filter.eventually_atTop] at hweightEv
  rcases hweightEv with ⟨Nw, hweight⟩
  obtain ⟨Np, hpts⟩ := hdata.pts_target_dist inp h8 hradRatio
    P L hstable hr phi hphi U C0 C1 aInf Jinf Jbarinf alpha rad hrad
  rw [Filter.eventually_atTop] at hbranch hscale
  rcases hbranch with ⟨Nb, hbranch⟩
  rcases hscale with ⟨Ns, hscale⟩
  obtain ⟨_hU, _hC0, _hC1, hC01, hC1U⟩ :=
    hdata.core_on inp P L r hr U C0 C1 aInf Jinf Jbarinf alpha
  have hC0U : C0 alpha ⊆ U alpha :=
    hC01.trans (interior_subset.trans hC1U)
  refine ⟨rad, hrad, hradEps, max (max Nw Np) (max Nb Ns), ?_⟩
  intro k hk l hl z hz
  have hkW : Nw ≤ k := by omega
  have hkP : Np ≤ k := by omega
  have hlP : Np ≤ l := by omega
  have hlB : Nb ≤ l := by omega
  have hlS : Ns ≤ l := by omega
  let Yk := X.obj (Lphi.φ k)
  let Yl := X.obj (Lphi.φ l)
  let : TopologicalSpace Yk.M := Yk.topology
  let : ChartedSpace H Yk.M := Yk.charted
  let : IsManifold I ∞ Yk.M := Yk.smooth
  let : T2Space Yk.M := Yk.t2
  let : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
  let : TopologicalSpace Yl.M := Yl.topology
  let : ChartedSpace H Yl.M := Yl.charted
  let : IsManifold I ∞ Yl.M := Yl.smooth
  let : IsManifold I 1 Yl.M := IsManifold.of_le
    (I := I) (M := Yl.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Yl.M := Yl.sigmaCompact
  let : T2Space Yl.M := Yl.t2
  let : ConnectedSpace Yl.M := hconn (L.φ (phi l))
  let : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Yl.M :=
    Manifold.metrizableSpace I Yl.M
  let : T3Space Yl.M := inferInstance
  let : RiemannianBundle (fun y : Yl.M ↦ TangentSpace I y) :=
    Yl.riemBundle (I := I)
  let : (y : Yl.M) → InnerProductSpace Real (TangentSpace I y) :=
    Yl.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : Yl.M ↦ TangentSpace I y) := Yl.riemBundle_cont (I := I)
  let : EMetricSpace Yl.M := Yl.emetricSpace (I := I)
  let : CompleteSpace Yl.M :=
    MetricComplete.complete (I := I) Yl (hcomplete.complete (L.φ (phi l)))
  let : MetricSpace Yl.M :=
    HopfRinow.riemMetricSpace (I := I) (M := Yl.M)
  let chiK := NormalCoordinates.normalChartAt (I := I) Yk.metric
    (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
  let chiL := NormalCoordinates.normalChartAt (I := I) Yl.metric
    (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
  let mu := stageWeightSub inp P L hr phi hphi alpha k
  let stagePts := fun w gamma =>
    stageTarget inp P Lphi r k l (chiK.symm w) gamma
  let qstar := fun w => chiL.symm w
  let p := qstar z
  let x0 := seqCenterD inp.decay P Lphi l (alpha.1 : Nat)
  let rho := aMin * inp.decay.mu (L.rInf (alpha.1 : Nat) + 1)
  let join := minJoin (I := I) Yl.metric (normal_enorm (I := I) Yl)
  let pts := centerAverage.activeFill mu stagePts qstar z
  have hmu := hweight k hkW alpha
  have hzU : z ∈ U alpha := hC0U hz
  obtain ⟨_hRad, hExp, hMaps⟩ :=
    hdata.geom_on inp P L r hr U C0 C1 aInf Jinf Jbarinf l alpha
  have hzBall := hExp hzU
  have hzNorm : ‖z‖ < expMapC2Radius (I := I) Yl.metric x0 := by
    simpa only [Metric.mem_ball, dist_zero_right, Yl, x0, Lphi,
      NetLimitData.subseq_phi, Function.comp_apply, seqCenterD_subseq,
      NormalChartFamily.radius, c2RadiusNormalChartFamily,
      c2_radius_normal_ball_chart_radius] using hzBall
  have hzTarget : z ∈ chiL.target := by
    exact ball_subset_normalChartAt_target (I := I) Yl.metric x0 hzNorm
  have hzExpSrc : z ∈
      (NormalCoordinates.expMapDiffeo (I := I) Yl.metric x0).source := by
    simpa only [chiL, NormalCoordinates.normalChartAt_target_eq] using hzTarget
  have hzChartSrc : z ∈
      (NormalCoordinates.normalChartAt (I := I) Yl.metric x0).symm.source := by
    change z ∈ (NormalCoordinates.normalChartAt (I := I) Yl.metric x0).target
    simpa only [NormalCoordinates.normalChartAt_target_eq] using hzExpSrc
  have hchiL : chiL.symm z =
      (c2RadiusNormalChartFamily (I := I) X).hom (L.φ (phi l))
        (seqCenterD inp.decay P L (phi l) (alpha.1 : Nat)) z := by
    change (NormalCoordinates.normalChartAt (I := I) Yl.metric x0).symm z = _
    rw [NormalCoordinates.normalChartAt_symm_apply (I := I) Yl.metric x0
      hzChartSrc]
    rw [← NormalCoordinates.expMapDiffeo_apply_eq (I := I) Yl.metric x0 hzExpSrc]
    simp only [Yl, x0, Lphi, NetLimitData.subseq_phi, Function.comp_apply,
      seqCenterD_subseq, NormalChartFamily.hom, c2RadiusNormalChartFamily,
      c2_radius_normal_ball_chart_apply]
  have hactive : ∀ gamma, mu z gamma ≠ 0 →
      dist p (stagePts z gamma) < rad := by
    intro gamma hne
    have hproper := hpts k hkP l hlP z hz gamma hne
    have hhd : inp.decay.dist (Lphi.φ l) p (stagePts z gamma) < rad := by
      rw [← ProperMetricOn.dist_eq inp.decay inp.realizes P (Lphi.φ l)]
      exact hproper
    have hed : riemannianEDist I p (stagePts z gamma) =
        ENNReal.ofReal (inp.decay.dist (Lphi.φ l) p (stagePts z gamma)) := by
      have hrealize := inp.realizes.edist_eq (Lphi.φ l) p (stagePts z gamma)
      change riemannianEDist I p (stagePts z gamma) = _ at hrealize
      exact hrealize
    rw [HopfRinow.riemMetric_dist_eq, hed,
      ENNReal.toReal_ofReal (inp.realizes.dist_nonneg
        (Lphi.φ l) p (stagePts z gamma))]
    exact hhd
  have hptsFilled : ∀ gamma, dist p (pts gamma) < rad := by
    simpa only [pts, p] using
      centerAverage.activeFill_close
        (g := Yl.metric) (μ := mu) (pts := stagePts) (qstar := qstar)
        (x := z) hrad hactive
  have hpHat : p ∈
      Lphi.hatBall inp.decay inp.D P inp.pack r l alpha.1 := by
    have hpGeom := (hMaps hzU).1
    change chiL.symm z ∈ Lphi.hatBall inp.decay inp.D P inp.pack r l alpha.1
    rw [NetLimitData.hatBall_subseq, hchiL]
    exact hpGeom
  have hproperCenter :
      (letI : MetricSpace Yl.M := (P (Lphi.φ l)).ms
       dist p x0) < 4 * L.lamInf (alpha.1 : Nat) := by
    have hhat := hat_dist_centerD inp.decay P Lphi inp.pack r hpHat
    simpa only [x0, Lphi, NetLimitData.subseq_lamInf] using hhat
  have hhdCenter : inp.decay.dist (Lphi.φ l) p x0 <
      4 * L.lamInf (alpha.1 : Nat) := by
    rw [← ProperMetricOn.dist_eq inp.decay inp.realizes P (Lphi.φ l) p x0]
    exact hproperCenter
  have hedCenter : riemannianEDist I p x0 =
      ENNReal.ofReal (inp.decay.dist (Lphi.φ l) p x0) := by
    have hrealize := inp.realizes.edist_eq (Lphi.φ l) p x0
    change riemannianEDist I p x0 = _ at hrealize
    exact hrealize
  have hpq : dist x0 p ≤ 4 * L.lamInf (alpha.1 : Nat) := by
    rw [dist_comm, HopfRinow.riemMetric_dist_eq, hedCenter,
      ENNReal.toReal_ofReal (inp.realizes.dist_nonneg (Lphi.φ l) p x0)]
    exact hhdCenter.le
  have hscaleL := hscale l hlS alpha
  dsimp only [Lphi] at hscaleL
  rcases hscaleL with ⟨hquarter, hρmetric, hρexp⟩
  have hρexp' : rho / 2 ≤ expRadiusGp (I := I) Yl.metric x0 := by
    simpa only [rho, Yl, x0, Lphi, NetLimitData.subseq] using hρexp
  have hfull := hbranch l hlB alpha
  rcases hqdata alpha with ⟨_hq, _hδ, hρ, hρq⟩
  have hstrict : StrictDistInput (I := I) Yl.metric pts join p rad := by
    simpa only [Yl, x0, rho, pts, join, Lphi, NetLimitData.subseq] using
      HasNormalBrFull.strict_dist (I := I) inp.normalBounds (Lphi.φ l)
        (hcomplete.complete (Lphi.φ l)) (hconn (Lphi.φ l)) x0 hfull
        (hqAcc alpha) pts p rad (4 * L.lamInf (alpha.1 : Nat))
        hquarter hρ hρq hρmetric hρexp hrad hpq hptsFilled hcage
  let hcomplete' :=
    NetLimitData.sourceComplete (I := I) inp.decay P Lphi l hcomplete
      (hconn (Lphi.φ l))
  have hcm : CenterInput (I := I) Yl.metric (mu z) pts join p rad := by
    simpa only [pts, p] using
      centerAverage.inputOfFillSelf (I := I)
        (g := Yl.metric) (μ := mu) (pts := stagePts) (join := join)
        (r := fun _ => rad) (qstar := qstar) z hcomplete' hrad hactive
        (hmu.nonneg z hzU) (hmu.pos z hzU) hstrict
  have hcage2 : ENNReal.ofReal
        (4 * L.lamInf (alpha.1 : Nat) + 2 * rad) <
      ENNReal.ofReal (rhoBase / 2) := by
    apply (ENNReal.ofReal_le_ofReal ?_).trans_lt hcage
    nlinarith [hrad]
  have hqdataPhi : ∀ gamma : LiveSlot Lphi inp.pack r,
      let rhoGamma := aMin * inp.decay.mu
        (Lphi.rInf (gamma.1 : Nat) + 1)
      0 < q gamma ∧ 0 < δ gamma ∧ 0 < rhoGamma ∧
        2 * rhoGamma < (q gamma : Real) := by
    intro gamma
    simpa only [Lphi, NetLimitData.subseq] using hqdata gamma
  have hbranchScale : ∀ gamma : LiveSlot Lphi inp.pack r,
      let rhoGamma := aMin * inp.decay.mu
        (Lphi.rInf (gamma.1 : Nat) + 1)
      let xGamma := seqCenterD inp.decay P Lphi l (gamma.1 : Nat)
      letI : TopologicalSpace (X.obj (Lphi.φ l)).M :=
        (X.obj (Lphi.φ l)).topology
      letI : ChartedSpace H (X.obj (Lphi.φ l)).M :=
        (X.obj (Lphi.φ l)).charted
      letI : IsManifold I ∞ (X.obj (Lphi.φ l)).M :=
        (X.obj (Lphi.φ l)).smooth
      letI : T2Space (TangentBundle I (X.obj (Lphi.φ l)).M) :=
        (X.obj (Lphi.φ l)).t2TangentBundle
      HasNormalBrFull (I := I) (X.obj (Lphi.φ l))
          (hcomplete.complete (Lphi.φ l)) (hconn (Lphi.φ l)) xGamma
          (q gamma) (δ gamma) rhoGamma ∧
        rhoGamma ≤ inp.normalBounds.radius (Lphi.φ l) xGamma ∧
        rhoGamma / 2 ≤ expRadiusGp
          (I := I) (X.obj (Lphi.φ l)).metric xGamma := by
    intro gamma
    have hfullGamma := hbranch l hlB gamma
    have hscaleGamma := hscale l hlS gamma
    dsimp only [Lphi] at hscaleGamma ⊢
    exact ⟨hfullGamma, hscaleGamma.2.1, hscaleGamma.2.2⟩
  have hout := exists_hat_cmC_at (I := I) inp.decay P inp.realizes
    Lphi inp.pack r l hcomplete hconn q δ hqdataPhi hbranchScale alpha
    (mu z) pts join p rad hcm (hmu.sum_one z hzU) hpHat hcage2
  let c := centerOfMass (I := I) Yl.metric (mu z) pts join p rad hcm
  have hcMem : c ∈ Metric.closedBall p (2 * rad) := by
    simpa only [c] using centerOfMass.mem hcm
  have hpc : dist p c ≤ 2 * rad := by
    simpa only [dist_comm] using Metric.mem_closedBall.mp hcMem
  have hjoinDist {t : Real} (ht : 0 ≤ t) :
      dist p (join p c t) ≤ dist p c * t := by
    have hed := minJoin_edist_le (I := I) Yl.metric
      (normal_enorm (I := I) Yl) p c ht
    have hmono := ENNReal.toReal_mono ENNReal.ofReal_ne_top hed
    have hmul : 0 ≤ (riemannianEDist I p c).toReal * t :=
      mul_nonneg ENNReal.toReal_nonneg ht
    rw [ENNReal.toReal_ofReal hmul] at hmono
    simpa only [join, ← HopfRinow.riemMetric_dist_eq] using hmono
  have hjoin : Set.MapsTo (join p c) (Set.Icc (0 : Real) 1)
      (chiL.source ∩ chiL ⁻¹' Metric.ball (0 : E) rhoBase) := by
    intro t ht
    have hpt : dist p (join p c t) ≤ 2 * rad := by
      calc
        dist p (join p c t) ≤ dist p c * t := hjoinDist ht.1
        _ ≤ dist p c * 1 :=
          mul_le_mul_of_nonneg_left ht.2 dist_nonneg
        _ ≤ 2 * rad := by simpa only [mul_one] using hpc
    have hxt : dist x0 (join p c t) ≤
        4 * L.lamInf (alpha.1 : Nat) + 2 * rad := by
      calc
        dist x0 (join p c t) ≤ dist x0 p + dist p (join p c t) :=
          dist_triangle _ _ _
        _ ≤ 4 * L.lamInf (alpha.1 : Nat) + 2 * rad :=
          add_le_add hpq hpt
    have htReal : (riemannianEDist I x0 (join p c t)).toReal ≤
        4 * L.lamInf (alpha.1 : Nat) + 2 * rad := by
      rw [← HopfRinow.riemMetric_dist_eq]
      exact hxt
    have htExp : (riemannianEDist I x0 (join p c t)).toReal <
        expRadiusGp (I := I) Yl.metric x0 := by
      apply htReal.trans_lt
      calc
        4 * L.lamInf (alpha.1 : Nat) + 2 * rad < rhoBase / 2 := by
          nlinarith [hrad]
        _ ≤ expRadiusGp (I := I) Yl.metric x0 := by
          simpa only [rhoBase] using hρexp'
    have htControl := inp.normalBounds.raw_chart_mem_norm_le (Lphi.φ l) x0
      (join p c t) ⟨Exponential.riemannianEDist_ne_top (I := I) _ _, htExp⟩
    refine ⟨htControl.1, ?_⟩
    change chiL (join p c t) ∈ Metric.ball (0 : E) rhoBase
    rw [Metric.mem_ball, dist_zero_right]
    calc
      ‖chiL (join p c t)‖ ≤
          2 * (riemannianEDist I x0 (join p c t)).toReal := by
        simpa only [chiL, Yl, x0, Lphi] using htControl.2
      _ ≤ 2 * (4 * L.lamInf (alpha.1 : Nat) + 2 * rad) :=
        mul_le_mul_of_nonneg_left htReal (by norm_num)
      _ < rhoBase := by nlinarith [hcageReal, hrad]
  have hEquiv : NormalCoordMetricEquivOn (I := I) Yl x0
      (Metric.ball (0 : E) rhoBase) := by
    intro w hw v
    exact inp.normalBounds.metric_equiv (Lphi.φ l) x0 w
      (Metric.ball_subset_ball hρmetric hw) v
  have hchart := NormalCoordMetricEquivOn.chart_dist_le
    (I := I) Yl (hcomplete.complete (Lphi.φ l)) (hconn (Lphi.φ l))
      (normal_enorm (I := I) Yl) hEquiv hjoin
  have hchart' : dist (chiL p) (chiL c) ≤ Real.sqrt 2 * dist p c := by
    simpa only [chiL, ← HopfRinow.riemMetric_dist_eq] using hchart
  have hpDecode : chiL p = z := by
    change chiL (chiL.symm z) = z
    exact chiL.right_inv hzTarget
  have hsqrt : Real.sqrt 2 ≤ 2 := by
    linarith [Real.sqrt_two_lt_three_halves]
  have hcoord : dist (chiL c) z ≤ 4 * rad := by
    rw [← hpDecode, dist_comm]
    calc
      dist (chiL p) (chiL c) ≤ Real.sqrt 2 * dist p c := hchart'
      _ ≤ Real.sqrt 2 * (2 * rad) :=
        mul_le_mul_of_nonneg_left hpc (Real.sqrt_nonneg 2)
      _ ≤ 2 * (2 * rad) :=
        mul_le_mul_of_nonneg_right hsqrt (mul_nonneg (by norm_num) hrad.le)
      _ = 4 * rad := by ring
  refine ⟨hcm, ?_, ?_⟩
  · exact hout
  · simpa only [mu, stagePts, qstar, pts, p, join, c] using hcoord

namespace BoundedGeometryNormalChartData


theorem ratio_gt_48
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : BoundedGeometryNormalChartData (I := I) X hd) {aMin R : Real} {q : NNReal}
    (hρq : 2 * (aMin * hd.mu R) < (q : Real))
    (hqRadius : 6 * (q : Real) < d.phaseRadius R) :
    48 * aMin < d.ratio := by
  have hmu : 0 < hd.mu R := hd.mu_pos R
  dsimp only [phaseRadius] at hqRadius
  nlinarith


theorem pair_lam_lt_three
    (inp : MetricCompactCore (I := I) X)
    (d : BoundedGeometryNormalChartData (I := I) X inp.decay)
    (aMin : Real)
    (hphys : 8 * Real.exp inp.decay.C < aMin * inp.D)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P)
    {alpha gamma : Nat}
    (hratio : 48 * aMin < d.ratio)
    (hfreq : ∃ᶠ k in Filter.atTop,
      BInter inp.decay inp.D P L.lamInf alpha gamma (L.φ k)) :
    L.lamInf gamma < 3 * L.lamInf alpha := by
  have hmu0 : 0 < inp.decay.mu 0 := inp.decay.mu_pos 0
  have h384div :
      384 * Real.exp inp.decay.C / inp.D < d.ratio := by
    calc
      384 * Real.exp inp.decay.C / inp.D =
          48 * (8 * Real.exp inp.decay.C / inp.D) := by ring
      _ < 48 * aMin := mul_lt_mul_of_pos_left
        ((div_lt_iff₀ inp.hD).2 hphys) (by norm_num)
      _ < d.ratio := hratio
  have h384 :
      384 * Real.exp inp.decay.C < d.ratio * inp.D :=
    (div_lt_iff₀ inp.hD).1 h384div
  have hright : d.ratio * inp.D * (2 * inp.decay.mu 0) ≤ inp.D := by
    calc
      d.ratio * inp.D * (2 * inp.decay.mu 0) =
          inp.D * (2 * (d.ratio * inp.decay.mu 0)) := by ring
      _ ≤ inp.D * 1 := mul_le_mul_of_nonneg_left
        (by nlinarith [d.ratio_mu0_le]) inp.hD.le
      _ = inp.D := by ring
  have hsmallMu :
      768 * Real.exp inp.decay.C * inp.decay.mu 0 < inp.D := by
    calc
      768 * Real.exp inp.decay.C * inp.decay.mu 0 =
          (384 * Real.exp inp.decay.C) * (2 * inp.decay.mu 0) := by ring
      _ < (d.ratio * inp.D) * (2 * inp.decay.mu 0) :=
        mul_lt_mul_of_pos_right h384 (mul_pos (by norm_num) hmu0)
      _ ≤ inp.D := hright
  have hlambdaSmall :
      (768 * Real.exp inp.decay.C) * inp.decay.lambda inp.D 0 < 1 := by
    rw [InjectivityRadiusDecay.lambda]
    calc
      (768 * Real.exp inp.decay.C) * (inp.decay.mu 0 / inp.D) =
          (768 * Real.exp inp.decay.C * inp.decay.mu 0) / inp.D := by ring
      _ < inp.D / inp.D := div_lt_div_of_pos_right hsmallMu inp.hD
      _ = 1 := div_self (ne_of_gt inp.hD)
  have hlambda0 : 0 < inp.decay.lambda inp.D 0 :=
    inp.decay.lambda_pos inp.hD 0
  have harg :
      inp.decay.C * (10 * inp.decay.lambda inp.D 0) < 1 := by
    calc
      inp.decay.C * (10 * inp.decay.lambda inp.D 0) =
          (10 * inp.decay.C) * inp.decay.lambda inp.D 0 := by ring
      _ < (10 * Real.exp inp.decay.C) *
          inp.decay.lambda inp.D 0 :=
        mul_lt_mul_of_pos_right
          (mul_lt_mul_of_pos_left
            (lt_of_lt_of_le (lt_add_one inp.decay.C)
              (Real.add_one_le_exp inp.decay.C)) (by norm_num)) hlambda0
      _ < (768 * Real.exp inp.decay.C) *
          inp.decay.lambda inp.D 0 := by
        apply mul_lt_mul_of_pos_right _ hlambda0
        exact mul_lt_mul_of_pos_right (by norm_num)
          (Real.exp_pos inp.decay.C)
      _ < 1 := hlambdaSmall
  have hargNonneg :
      0 ≤ inp.decay.C * (10 * inp.decay.lambda inp.D 0) :=
    mul_nonneg inp.decay.C_nonneg
      (mul_nonneg (by norm_num) hlambda0.le)
  have hexpBound := Real.exp_bound' hargNonneg harg.le
    (n := 2) (by norm_num)
  have hargSq :
      (inp.decay.C * (10 * inp.decay.lambda inp.D 0)) ^ 2 < 1 := by
    nlinarith [sq_nonneg
      (inp.decay.C * (10 * inp.decay.lambda inp.D 0))]
  have hexp :
      Real.exp (inp.decay.C * (10 * inp.decay.lambda inp.D 0)) < 3 := by
    norm_num [Finset.sum_range_succ, Nat.factorial] at hexpBound
    nlinarith
  have hfreq' :
      ∃ᶠ k : Nat in Filter.atTop,
        BInter inp.decay inp.D P L.lamInf gamma alpha (L.φ k) :=
    hfreq.mono fun k hk =>
      BInter.symm inp.decay inp.D P L.lamInf hk
  have hclose := L.rInf_close inp.decay P hfreq'
  have halpha0 :
      L.lamInf alpha ≤ inp.decay.lambda inp.D 0 :=
    inp.decay.lambda_antitone inp.hD (L.rInf_mem alpha).1
  have hgamma0 :
      L.lamInf gamma ≤ inp.decay.lambda inp.D 0 :=
    inp.decay.lambda_antitone inp.hD (L.rInf_mem gamma).1
  have hgap :
      L.rInf alpha - L.rInf gamma ≤
        10 * inp.decay.lambda inp.D 0 := by
    linarith
  have hpair :
      L.lamInf gamma ≤
        Real.exp (inp.decay.C * (10 * inp.decay.lambda inp.D 0)) *
          L.lamInf alpha := by
    simpa only [NetLimitData.lamInf] using
      inp.decay.lambda_exp_le inp.hD hgap
  exact hpair.trans_lt
    (mul_lt_mul_of_pos_right hexp
      (inp.decay.lambda_pos inp.hD (L.rInf alpha)))


theorem stage_radius_gt
    (inp : MetricCompactCore (I := I) X)
    (d : BoundedGeometryNormalChartData (I := I) X inp.decay)
    (aMin : Real)
    (hphys : 8 * Real.exp inp.decay.C < aMin * inp.D)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P)
    {gamma k : Nat}
    (hratio : 48 * aMin < d.ratio)
    (hcenter :
      inp.decay.dist (L.φ k)
          (seqCenterD inp.decay P L k gamma)
          (X.obj (L.φ k)).basepoint <
        L.rInf gamma + 1) :
    letI : TopologicalSpace (X.obj (L.φ k)).M :=
      (X.obj (L.φ k)).topology
    letI : ChartedSpace H (X.obj (L.φ k)).M :=
      (X.obj (L.φ k)).charted
    letI : IsManifold I ∞ (X.obj (L.φ k)).M :=
      (X.obj (L.φ k)).smooth
    letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
      (X.obj (L.φ k)).t2TangentBundle
    384 * L.lamInf gamma <
      (d.chart (L.φ k) (seqCenterD inp.decay P L k gamma)).radius := by
  let : TopologicalSpace (X.obj (L.φ k)).M :=
    (X.obj (L.φ k)).topology
  let : ChartedSpace H (X.obj (L.φ k)).M :=
    (X.obj (L.φ k)).charted
  let : IsManifold I ∞ (X.obj (L.φ k)).M :=
    (X.obj (L.φ k)).smooth
  let : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
    (X.obj (L.φ k)).t2TangentBundle
  have hmu :
      inp.decay.mu (L.rInf gamma + 1) ≤
        inp.decay.mu
          (inp.decay.dist (L.φ k)
            (seqCenterD inp.decay P L k gamma)
            (X.obj (L.φ k)).basepoint) :=
    inp.decay.mu_antitone hcenter.le
  have hprod :
      48 * aMin * inp.decay.mu (L.rInf gamma + 1) <
        d.ratio *
          inp.decay.mu
            (inp.decay.dist (L.φ k)
              (seqCenterD inp.decay P L k gamma)
              (X.obj (L.φ k)).basepoint) := by
    calc
      48 * aMin * inp.decay.mu (L.rInf gamma + 1) <
          d.ratio * inp.decay.mu (L.rInf gamma + 1) :=
        mul_lt_mul_of_pos_right hratio
          (inp.decay.mu_pos (L.rInf gamma + 1))
      _ ≤ d.ratio *
          inp.decay.mu
            (inp.decay.dist (L.φ k)
              (seqCenterD inp.decay P L k gamma)
              (X.obj (L.φ k)).basepoint) :=
        mul_le_mul_of_nonneg_left hmu d.ratio_pos.le
  rw [d.radius_eq]
  nlinarith [lamInf_lt_halfMin inp.decay inp.hD hphys P L gamma]


theorem stage_rho_le
    (inp : MetricCompactCore (I := I) X)
    (d : BoundedGeometryNormalChartData (I := I) X inp.decay)
    (aMin : Real) (haMin : 0 < aMin)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P)
    {gamma k : Nat}
    (hratio : 48 * aMin < d.ratio)
    (hcenter :
      inp.decay.dist (L.φ k)
          (seqCenterD inp.decay P L k gamma)
          (X.obj (L.φ k)).basepoint <
        L.rInf gamma + 1) :
    letI : TopologicalSpace (X.obj (L.φ k)).M :=
      (X.obj (L.φ k)).topology
    letI : ChartedSpace H (X.obj (L.φ k)).M :=
      (X.obj (L.φ k)).charted
    letI : IsManifold I ∞ (X.obj (L.φ k)).M :=
      (X.obj (L.φ k)).smooth
    letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
      (X.obj (L.φ k)).t2TangentBundle
    aMin * inp.decay.mu (L.rInf gamma + 1) ≤
      (d.chart (L.φ k)
        (seqCenterD inp.decay P L k gamma)).radius / 4 := by
  let : TopologicalSpace (X.obj (L.φ k)).M :=
    (X.obj (L.φ k)).topology
  let : ChartedSpace H (X.obj (L.φ k)).M :=
    (X.obj (L.φ k)).charted
  let : IsManifold I ∞ (X.obj (L.φ k)).M :=
    (X.obj (L.φ k)).smooth
  let : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
    (X.obj (L.φ k)).t2TangentBundle
  have hmu :
      inp.decay.mu (L.rInf gamma + 1) ≤
        inp.decay.mu
          (inp.decay.dist (L.φ k)
            (seqCenterD inp.decay P L k gamma)
            (X.obj (L.φ k)).basepoint) :=
    inp.decay.mu_antitone hcenter.le
  have hprod :
      4 * aMin * inp.decay.mu (L.rInf gamma + 1) <
        d.ratio *
          inp.decay.mu
            (inp.decay.dist (L.φ k)
              (seqCenterD inp.decay P L k gamma)
              (X.obj (L.φ k)).basepoint) := by
    calc
      4 * aMin * inp.decay.mu (L.rInf gamma + 1) <
          d.ratio * inp.decay.mu (L.rInf gamma + 1) := by
        apply mul_lt_mul_of_pos_right _ (inp.decay.mu_pos _)
        nlinarith
      _ ≤ d.ratio *
          inp.decay.mu
            (inp.decay.dist (L.φ k)
              (seqCenterD inp.decay P L k gamma)
              (X.obj (L.φ k)).basepoint) :=
        mul_le_mul_of_nonneg_left hmu d.ratio_pos.le
  rw [d.radius_eq]
  nlinarith

theorem target_mem
    (inp : MetricCompactCore (I := I) X)
    (d : BoundedGeometryNormalChartData (I := I) X inp.decay)
    (aMin : Real)
    (hphys : 8 * Real.exp inp.decay.C < aMin * inp.D)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    {alpha gamma k : Nat}
    (hratio : 48 * aMin < d.ratio)
    (hcenterAlpha :
      inp.decay.dist (L.φ k)
          (seqCenterD inp.decay P L k alpha)
          (X.obj (L.φ k)).basepoint <
        L.rInf alpha + 1)
    (hcenterGamma :
      inp.decay.dist (L.φ k)
          (seqCenterD inp.decay P L k gamma)
          (X.obj (L.φ k)).basepoint <
        L.rInf gamma + 1)
    (hfreq : ∃ᶠ n : Nat in Filter.atTop,
      BInter inp.decay inp.D P L.lamInf alpha gamma (L.φ n))
    (hinter :
      BInter inp.decay inp.D P L.lamInf alpha gamma (L.φ k))
    (w : E)
    (hw : w ∈ Metric.closedBall 0 (6 * L.lamInf gamma)) :
    let Y := X.obj (L.φ k)
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (d.chart (L.φ k) (seqCenterD inp.decay P L k gamma)).hom w ∈
      (d.chart (L.φ k)
        (seqCenterD inp.decay P L k alpha)).hom.target := by
  let Y := X.obj (L.φ k)
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : Y.M ↦ TangentSpace I y) :=
    Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M :=
    MetricComplete.complete (I := I) Y (hcomplete.complete (L.φ k))
  let : ConnectedSpace Y.M := hconn (L.φ k)
  let : MetricSpace Y.M := (P (L.φ k)).ms
  let cAlpha := seqCenterD inp.decay P L k alpha
  let cGamma := seqCenterD inp.decay P L k gamma
  let chiAlpha := d.chart (L.φ k) cAlpha
  let chiGamma := d.chart (L.φ k) cGamma
  let y := chiGamma.hom w
  have hradAlpha :
      384 * L.lamInf alpha < chiAlpha.radius := by
    simpa only [chiAlpha, cAlpha, Y] using
      d.stage_radius_gt inp aMin hphys P L hratio hcenterAlpha
  have hradGamma :
      384 * L.lamInf gamma < chiGamma.radius := by
    simpa only [chiGamma, cGamma, Y] using
      d.stage_radius_gt inp aMin hphys P L hratio hcenterGamma
  have hlamGamma : 0 < L.lamInf gamma :=
    inp.decay.lambda_pos inp.hD (L.rInf gamma)
  have hwNorm : ‖w‖ ≤ 6 * L.lamInf gamma := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hw
  have hwBall : w ∈ Metric.ball 0 chiGamma.radius := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hwNorm.trans_lt (by nlinarith)
  have hseg :
      segment Real 0 w ⊆ Metric.ball 0 chiGamma.radius :=
    (convex_ball (0 : E) chiGamma.radius).segment_subset
      (Metric.mem_ball_self chiGamma.radius_pos) hwBall
  have hchart :
      (letI : MetricSpace Y.M := (P (L.φ k)).ms
       dist (chiGamma.hom 0) (chiGamma.hom w)) ≤
        Real.sqrt 2 * dist 0 w := by
    exact NormalBallChart.MetricEquivOn.hom_dist_le
      Y (P (L.φ k)) chiGamma
        (by simpa only [chiGamma, cGamma, Y] using
          d.metric_equiv (L.φ k) cGamma)
        chiGamma.ball_subset hseg
  have hsqrt : Real.sqrt 2 ≤ 2 := by
    linarith [Real.sqrt_two_lt_three_halves]
  have hgammaTarget :
      (letI : MetricSpace Y.M := (P (L.φ k)).ms
       dist cGamma y) ≤ 12 * L.lamInf gamma := by
    calc
      (letI : MetricSpace Y.M := (P (L.φ k)).ms
       dist cGamma y) =
          dist (chiGamma.hom 0) (chiGamma.hom w) := by
            rw [chiGamma.map_zero]
      _ ≤ Real.sqrt 2 * dist 0 w := hchart
      _ = Real.sqrt 2 * ‖w‖ := by rw [dist_zero_left]
      _ ≤ Real.sqrt 2 * (6 * L.lamInf gamma) :=
        mul_le_mul_of_nonneg_left hwNorm (Real.sqrt_nonneg 2)
      _ ≤ 2 * (6 * L.lamInf gamma) :=
        mul_le_mul_of_nonneg_right hsqrt
          (mul_nonneg (by norm_num) hlamGamma.le)
      _ = 12 * L.lamInf gamma := by ring
  have hcenterDist :
      (letI : MetricSpace Y.M := (P (L.φ k)).ms
       dist cAlpha cGamma) <
        5 * L.lamInf alpha + 5 * L.lamInf gamma := by
    obtain ⟨x, z, hx, hz, hmeet⟩ := hinter
    have hxc : x = cAlpha := by
      dsimp only [cAlpha]
      unfold seqCenterD
      rw [hx]
      simp only [Option.getD_some]
    have hzc : z = cGamma := by
      dsimp only [cGamma]
      unfold seqCenterD
      rw [hz]
      simp only [Option.getD_some]
    rw [hxc, hzc] at hmeet
    obtain ⟨v, hvAlpha, hvGamma⟩ :=
      Set.not_disjoint_iff.mp hmeet
    rw [Metric.mem_ball] at hvAlpha hvGamma
    have htri := dist_triangle cAlpha v cGamma
    rw [dist_comm v cAlpha] at hvAlpha
    linarith
  have hpair :
      L.lamInf gamma < 3 * L.lamInf alpha :=
    d.pair_lam_lt_three inp aMin hphys P L hratio hfreq
  have hproper :
      (letI : MetricSpace Y.M := (P (L.φ k)).ms
       dist cAlpha y) < 56 * L.lamInf alpha := by
    have htri :
        (letI : MetricSpace Y.M := (P (L.φ k)).ms
         dist cAlpha y) ≤ dist cAlpha cGamma + dist cGamma y :=
      dist_triangle _ _ _
    nlinarith
  have hdist :
      inp.decay.dist (L.φ k) cAlpha y < chiAlpha.radius := by
    rw [← ProperMetricOn.dist_eq inp.decay inp.realizes P
      (L.φ k) cAlpha y]
    exact hproper.trans (by nlinarith)
  have hed : riemannianEDist I cAlpha y =
      ENNReal.ofReal (inp.decay.dist (L.φ k) cAlpha y) := by
    have hrealize := inp.realizes.edist_eq (L.φ k) cAlpha y
    change riemannianEDist I cAlpha y = _ at hrealize
    exact hrealize
  have hedRad : riemannianEDist I cAlpha y <
      ENNReal.ofReal chiAlpha.radius := by
    rw [hed]
    exact (ENNReal.ofReal_lt_ofReal_iff chiAlpha.radius_pos).2 hdist
  have hread := d.toNormalChartData.mem_image_and_norm_inv_eq_riemannian_distance
    (L.φ k) (hcomplete.complete (L.φ k)) (hconn (L.φ k))
      cAlpha y hedRad
  rcases hread.1 with ⟨v, hv, hvy⟩
  change y ∈ chiAlpha.hom.target
  rw [← hvy]
  exact chiAlpha.hom.map_source (chiAlpha.ball_subset hv)

theorem weight_trans_mem
    (inp : MetricCompactCore (I := I) X)
    (d : BoundedGeometryNormalChartData (I := I) X inp.decay)
    (aMin : Real)
    (hphys : 8 * Real.exp inp.decay.C < aMin * inp.D)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P)
    {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (k : Nat)
    (alpha : LiveSlot L inp.pack r) (z : E)
    (hinner : NormalChartFamily.hom d.chart (L.φ (phi k))
        (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat)) z ∈
      ⋃ gamma : Fin (inp.pack.A r),
        L.innerBall inp.decay inp.D P inp.pack r (phi k) gamma)
    (target : InterSlot L inp.pack r alpha)
    (hweight : stageWeightSub inp P L hr phi hphi alpha k z target.1.1
      (chart := d.chart) ≠ 0)
    (hradius : aMin * inp.decay.mu
        (L.rInf (target.1.1 : Nat) + 1) ≤
      NormalChartFamily.radius d.chart (L.φ (phi k))
        (seqCenterD inp.decay P L (phi k) (target.1.1 : Nat)) / 4) :
    NormalChartFamily.transition d.chart (L.φ (phi k))
        (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
        (seqCenterD inp.decay P L (phi k) (target.1.1 : Nat)) z ∈
      Metric.closedBall 0 (6 * L.lamInf (target.1.1 : Nat)) := by
  classical
  let Y := X.obj (L.φ (phi k))
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M :=
    MetricComplete.complete (I := I) Y (hcomplete.complete (L.φ (phi k)))
  let x :=
    NormalChartFamily.hom d.chart (L.φ (phi k))
      (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat)) z
  let c := seqCenterD inp.decay P L (phi k) (target.1.1 : Nat)
  let i0 := baseIndex inp.decay inp.realizes inp.pack hr
  let s : Set Y.M := ⋃ gamma : Fin (inp.pack.A r),
    L.innerBall inp.decay inp.D P inp.pack r (phi k) gamma
  have hweights := seqWeights_data_raw (I := I) inp.decay inp.hD P L
    inp.pack r (phi k) i0 (s := s) Set.Subset.rfl
  have hxHat :
      x ∈ L.hatBall inp.decay inp.D P inp.pack r (phi k) target.1.1 := by
    apply hweights.active_mem x
    · simpa only [x, s] using hinner
    · rw [show x =
          (d.chart (L.φ (phi k))
            (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))).hom z by
        with_unfolding_all rfl]
      simpa only [i0] using
        (show
          (let Y := X.obj (L.φ (phi k))
           letI : TopologicalSpace Y.M := Y.topology
           letI : ChartedSpace H Y.M := Y.charted
           letI : IsManifold I ∞ Y.M := Y.smooth
           letI : T2Space Y.M := Y.t2
           letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
           let i0 := baseIndex inp.decay inp.realizes inp.pack hr
           rawWeights
             (cutRaw
               (seqAtom inp.decay inp.hD P L inp.pack r (phi k) i0)
               (seqAtom inp.decay inp.hD P L inp.pack r (phi k)) i0)
             ((d.chart (L.φ (phi k))
               (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))).hom z)
             target.1.1 ≠ 0) by
          simpa only using congrArg (fun value => value ≠ 0)
            (stageWeightSub_eq (I := I) inp P L hr phi hphi alpha k z
              target.1.1 (chart := d.chart)) ▸ hweight)
  have hproper :
      (letI : MetricSpace Y.M := (P (L.φ (phi k))).ms
       dist x c) < 4 * L.lamInf (target.1.1 : Nat) := by
    have hhat := hat_dist_centerD inp.decay P L inp.pack r hxHat
    simpa only [c, Y] using hhat
  have hdist : inp.decay.dist (L.φ (phi k)) c x <
      4 * L.lamInf (target.1.1 : Nat) := by
    rw [← ProperMetricOn.dist_eq inp.decay inp.realizes P (L.φ (phi k)) c x]
    simpa only [dist_comm] using hproper
  have hhalf : 4 * L.lamInf (target.1.1 : Nat) <
      (aMin * inp.decay.mu (L.rInf (target.1.1 : Nat) + 1)) / 2 :=
    lamInf_lt_halfMin inp.decay inp.hD hphys P L (target.1.1 : Nat)
  have haMin : 0 < aMin := by
    have hprod : 0 < aMin * inp.D :=
      (mul_pos (by norm_num) (Real.exp_pos inp.decay.C)).trans hphys
    nlinarith [inp.hD]
  have hrho : 0 <
      aMin * inp.decay.mu (L.rInf (target.1.1 : Nat) + 1) :=
    mul_pos haMin (inp.decay.mu_pos _)
  have hdistRad : inp.decay.dist (L.φ (phi k)) c x <
      (d.chart (L.φ (phi k)) c).radius := by
    calc
      inp.decay.dist (L.φ (phi k)) c x <
          4 * L.lamInf (target.1.1 : Nat) := hdist
      _ < (aMin * inp.decay.mu
          (L.rInf (target.1.1 : Nat) + 1)) / 2 := hhalf
      _ < (d.chart (L.φ (phi k)) c).radius := by
        dsimp only [NormalChartFamily.radius, Y, c] at hradius ⊢
        nlinarith
  have hed : riemannianEDist I c x =
      ENNReal.ofReal (inp.decay.dist (L.φ (phi k)) c x) := by
    have hrealize := inp.realizes.edist_eq (L.φ (phi k)) c x
    change riemannianEDist I c x = _ at hrealize
    exact hrealize
  have hedRad : riemannianEDist I c x <
      ENNReal.ofReal (d.chart (L.φ (phi k)) c).radius := by
    rw [hed]
    exact (ENNReal.ofReal_lt_ofReal_iff
      (d.chart (L.φ (phi k)) c).radius_pos).2 hdistRad
  have hread := d.toNormalChartData.mem_image_and_norm_inv_eq_riemannian_distance
    (L.φ (phi k)) (hcomplete.complete (L.φ (phi k)))
    (hconn (L.φ (phi k)))
    c x hedRad
  have hnorm : ‖(d.chart (L.φ (phi k)) c).inv x‖ <
      4 * L.lamInf (target.1.1 : Nat) := by
    rw [hread.2, hed,
      ENNReal.toReal_ofReal (inp.realizes.dist_nonneg (L.φ (phi k)) c x)]
    exact hdist
  rw [Metric.mem_closedBall, dist_zero_right]
  change ‖(d.chart (L.φ (phi k)) c).inv x‖ ≤
    6 * L.lamInf (target.1.1 : Nat)
  calc
    ‖(d.chart (L.φ (phi k)) c).inv x‖ ≤
        4 * L.lamInf (target.1.1 : Nat) := hnorm.le
    _ ≤ 6 * L.lamInf (target.1.1 : Nat) := by
      have hlam := inp.decay.lambda_pos inp.hD
        (L.rInf (target.1.1 : Nat))
      dsimp only [NetLimitData.lamInf]
      nlinarith

theorem pts_target_tail
    (inp : MetricCompactCore (I := I) X)
    (d : BoundedGeometryNormalChartData (I := I) X inp.decay)
    (aMin : Real) (haMin : 0 < aMin)
    (hphys : 8 * Real.exp inp.decay.C < aMin * inp.D)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P)
    (hstable : ∀ a b : Nat,
      (∀ᶠ k in Filter.atTop,
        BInter inp.decay inp.D P L.lamInf a b (L.φ k)) ∨
      (∀ᶠ k in Filter.atTop,
        ¬ BInter inp.decay inp.D P L.lamInf a b (L.φ k)))
    {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (hdata : HasSuppConvDataOn (I := I) inp P L r hr phi hphi d.chart
      U C0 C1 aInf Jinf Jbarinf)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (q : LiveSlot L inp.pack r → NNReal)
    (δ : LiveSlot L inp.pack r → Real)
    (hqdata : ∀ gamma : LiveSlot L inp.pack r,
      let Rgamma := L.rInf (gamma.1 : Nat) + 1
      let rho := aMin * inp.decay.mu Rgamma
      0 < q gamma ∧ 0 < δ gamma ∧ 0 < rho ∧
        2 * rho < (q gamma : Real) ∧
        6 * (q gamma : Real) < d.phaseRadius Rgamma ∧
        3 * d.metricC 1 * (2 * (q gamma : Real)) ^ 2 ≤
          (2 / 3 : Real) * (q gamma : Real) ∧
        PhaseFlow.phaseErr (d.phaseK (2 * q gamma)) <
          ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
            (E × E) →L[Real] (E × E))‖₊⁻¹ ∧
        ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
          (E × E) →L[Real] (E × E))‖₊ *
            (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
              (E × E) →L[Real] (E × E))‖₊⁻¹ -
              PhaseFlow.phaseErr (d.phaseK (2 * q gamma)))⁻¹ *
            PhaseFlow.phaseErr (d.phaseK (2 * q gamma)) < 1 / 24) :
    ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N,
      ∀ (alpha : LiveSlot L inp.pack r) (z : E), z ∈ U alpha →
        ∀ gamma : Fin (inp.pack.A r),
          stageWeightSub inp P L hr phi hphi alpha k z gamma
              (chart := d.chart) ≠ 0 →
            let Lphi := L.subseq hphi
            let Yk := X.obj (Lphi.φ k)
            let Yl := X.obj (Lphi.φ l)
            letI : TopologicalSpace Yk.M := Yk.topology
            letI : ChartedSpace H Yk.M := Yk.charted
            letI : IsManifold I ∞ Yk.M := Yk.smooth
            letI : T2Space Yk.M := Yk.t2
            letI : T2Space (TangentBundle I Yk.M) :=
              Yk.t2TangentBundle
            letI : TopologicalSpace Yl.M := Yl.topology
            letI : ChartedSpace H Yl.M := Yl.charted
            letI : IsManifold I ∞ Yl.M := Yl.smooth
            letI : T2Space Yl.M := Yl.t2
            letI : T2Space (TangentBundle I Yl.M) :=
              Yl.t2TangentBundle
            (d.chart (Lphi.φ l)
                (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))).hom
                (stagePtsSub inp P L phi hphi alpha k l z gamma
                  (chart := d.chart)) =
              stageTarget inp P Lphi r k l
                ((d.chart (Lphi.φ k)
                  (seqCenterD inp.decay P Lphi k
                    (alpha.1 : Nat))).hom z)
                gamma (chart := d.chart) ∧
            (d.chart (Lphi.φ l)
                (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))).inv
                (stageTarget inp P Lphi r k l
                  ((d.chart (Lphi.φ k)
                    (seqCenterD inp.decay P Lphi k
                      (alpha.1 : Nat))).hom z)
                  gamma (chart := d.chart)) =
              stagePtsSub inp P L phi hphi alpha k l z gamma
                (chart := d.chart) := by
  classical
  let Lphi := L.subseq hphi
  let (alpha : LiveSlot L inp.pack r) :
      Finite (InterSlot L inp.pack r alpha) :=
    Finite.of_injective
      (fun target : InterSlot L inp.pack r alpha => target.1.1)
      (by
        intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        exact hab)
  have hcenters :
      ∀ᶠ k in Filter.atTop, ∀ beta : LiveSlot L inp.pack r,
        inp.decay.dist (Lphi.φ k)
            (seqCenterD inp.decay P Lphi k (beta.1 : Nat))
            (X.obj (Lphi.φ k)).basepoint <
          L.rInf (beta.1 : Nat) + 1 := by
    have ht := liveCenters_rInf inp.decay P inp.realizes
      Lphi inp.pack r
    filter_upwards [ht] with k hk
    intro beta
    let betaPhi : LiveSlot Lphi inp.pack r :=
      ⟨beta.1, by
        simpa only [Lphi, NetLimitData.subseq] using beta.2⟩
    simpa only [betaPhi, Lphi, NetLimitData.subseq,
      Function.comp_apply] using hk betaPhi
  have hlamInf : Lphi.lamInf = L.lamInf := by
    simpa only [Lphi] using
      (NetLimitData.subseq_lamInf (L := L) hphi)
  have hslots : ∀ᶠ k in Filter.atTop,
      ∀ (alpha : LiveSlot L inp.pack r)
        (gamma : Fin (inp.pack.A r)),
        BInter inp.decay inp.D P Lphi.lamInf
            (alpha.1 : Nat) (gamma : Nat) (Lphi.φ k) →
          ∃ target : InterSlot L inp.pack r alpha,
            target.1.1 = gamma :=
    Filter.eventually_all.mpr fun alpha =>
      Filter.eventually_all.mpr fun gamma => by
        rcases hstable (alpha.1 : Nat) (gamma : Nat) with
          hinter | hdisjoint
        · have hstatus := hphi.tendsto_atTop.eventually
            (L.alive_eventually (gamma : Nat))
          filter_upwards [hstatus] with k hstatusK
          intro hcurrent
          rw [hlamInf] at hcurrent
          exact inter_slot_of_binter inp.decay P L inp.pack r alpha
            hstatusK (by
              simpa only [Lphi, NetLimitData.subseq_phi,
                Function.comp_apply] using hcurrent) hinter
        · have hdisjointPhi :=
            hphi.tendsto_atTop.eventually hdisjoint
          filter_upwards [hdisjointPhi] with k hdisjointK
          intro hcurrent
          rw [hlamInf] at hcurrent
          exact (hdisjointK (by
            simpa only [Lphi, NetLimitData.subseq_phi,
              Function.comp_apply] using hcurrent)).elim
  have hinters : ∀ᶠ k in Filter.atTop,
      ∀ (alpha : LiveSlot L inp.pack r)
        (target : InterSlot L inp.pack r alpha),
        BInter inp.decay inp.D P Lphi.lamInf
          (alpha.1 : Nat) (target.1.1 : Nat) (Lphi.φ k) :=
    Filter.eventually_all.mpr fun alpha =>
      Filter.eventually_all.mpr fun target => by
        have ht := hphi.tendsto_atTop.eventually target.2
        exact ht.mono fun k hk => by
          rw [hlamInf]
          simpa only [Lphi, NetLimitData.subseq_phi,
            Function.comp_apply] using hk
  have hall := hcenters.and (hslots.and hinters)
  rw [Filter.eventually_atTop] at hall
  rcases hall with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro k hk l hl
  rcases hN k hk with
    ⟨hcentersK, hslotsK, _hintersK⟩
  rcases hN l hl with
    ⟨hcentersL, _hslotsL, hintersL⟩
  intro alpha z hz gamma hweight
  let Yk := X.obj (Lphi.φ k)
  let Yl := X.obj (Lphi.φ l)
  let : TopologicalSpace Yk.M := Yk.topology
  let : ChartedSpace H Yk.M := Yk.charted
  let : IsManifold I ∞ Yk.M := Yk.smooth
  let : T2Space Yk.M := Yk.t2
  let : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
  let : MetricSpace Yk.M := (P (Lphi.φ k)).ms
  let : TopologicalSpace Yl.M := Yl.topology
  let : ChartedSpace H Yl.M := Yl.charted
  let : IsManifold I ∞ Yl.M := Yl.smooth
  let : T2Space Yl.M := Yl.t2
  let : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
  let xOrig := NormalChartFamily.hom d.chart (L.φ (phi k))
    (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat)) z
  let i0 := baseIndex inp.decay inp.realizes inp.pack hr
  let sOrig : Set (X.obj (L.φ (phi k))).M :=
    ⋃ gamma : Fin (inp.pack.A r),
      L.innerBall inp.decay inp.D P inp.pack r (phi k) gamma
  have hgeom := hdata.geom_on inp P L r hr d.chart
    U C0 C1 aInf Jinf Jbarinf k alpha
  have hxGeom := hgeom.2 hz
  have hweightRaw := hweight
  rw [stageWeightSub_eq (chart := d.chart)] at hweightRaw
  have hweights := seqWeights_data_raw (I := I) inp.decay inp.hD P L
    inp.pack r (phi k) i0 (s := sOrig) Set.Subset.rfl
  have hhatGammaOrig :
      xOrig ∈ L.hatBall inp.decay inp.D P inp.pack r (phi k) gamma := by
    apply hweights.active_mem xOrig
    · simpa only [sOrig, xOrig] using hxGeom.2
    · simpa only [xOrig, i0] using hweightRaw
  have hcurrentOrig :=
    L.binter_of_mem_hat inp.decay inp.hD P inp.pack r (phi k)
      hxGeom.1 hhatGammaOrig
  have hcurrent : BInter inp.decay inp.D P Lphi.lamInf
      (alpha.1 : Nat) (gamma : Nat) (Lphi.φ k) := by
    rw [hlamInf]
    simpa only [Lphi, NetLimitData.subseq_phi, Function.comp_apply] using
      hcurrentOrig
  obtain ⟨target, htarget⟩ :=
    hslotsK alpha gamma hcurrent
  subst gamma
  rcases hqdata alpha with
    ⟨_hq, _hδ, _hrho, hrhoQ, hqWide, _hqAcc, _herr, _hinvErr⟩
  have hratio : 48 * aMin < d.ratio :=
    d.ratio_gt_48 hrhoQ hqWide
  have hradiusPhi :=
    d.stage_rho_le inp aMin haMin P Lphi hratio
      (hcentersK target.1)
  have hradius :
      aMin * inp.decay.mu
          (L.rInf (target.1.1 : Nat) + 1) ≤
        NormalChartFamily.radius d.chart (L.φ (phi k))
          (seqCenterD inp.decay P L (phi k) (target.1.1 : Nat)) / 4 := by
    with_unfolding_all exact hradiusPhi
  have hsmall :=
    d.weight_trans_mem inp aMin hphys P L hr phi hphi
      hcomplete hconn k alpha z hxGeom.2 target hweight hradius
  let w :=
    (d.chart (Lphi.φ k)
      (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))).transition
      (d.chart (Lphi.φ k)
        (seqCenterD inp.decay P Lphi k
          (target.1.1 : Nat))) z
  have hsmallW :
      w ∈ Metric.closedBall 0
        (6 * Lphi.lamInf (target.1.1 : Nat)) := by
    have hwEq : w = NormalChartFamily.transition d.chart (L.φ (phi k))
        (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
        (seqCenterD inp.decay P L (phi k) (target.1.1 : Nat)) z := by
      with_unfolding_all rfl
    rw [hwEq, hlamInf]
    exact hsmall
  have hsmallSub :
      (d.chart (Lphi.φ k)
          (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))).transition
        (d.chart (Lphi.φ k)
          (seqCenterD inp.decay P Lphi k (target.1.1 : Nat))) z ∈
        Metric.closedBall 0 (6 * L.lamInf (target.1.1 : Nat)) := by
    simpa only [w, hlamInf] using hsmallW
  have hfreqPhi : ∃ᶠ n : Nat in Filter.atTop,
      BInter inp.decay inp.D P Lphi.lamInf
        (alpha.1 : Nat) (target.1.1 : Nat) (Lphi.φ n) :=
    (hinters.mono fun n hn => hn alpha target).frequently
  have htargetMem :=
    d.target_mem inp aMin hphys P Lphi hcomplete hconn hratio
      (hcentersL alpha) (hcentersL target.1)
      hfreqPhi (hintersL alpha target) w hsmallW
  have hsrc :
      stageTarget inp P Lphi r k l
          ((d.chart (Lphi.φ k)
            (seqCenterD inp.decay P Lphi k
              (alpha.1 : Nat))).hom z)
          target.1.1 (chart := d.chart) ∈
        (d.chart (Lphi.φ l)
          (seqCenterD inp.decay P Lphi l
            (alpha.1 : Nat))).hom.target := by
    simpa only [stageTarget, w,
      Geometry.Riemannian.NormalCoordinates.NormalBallChart.transition,
      Geometry.Riemannian.NormalCoordinates.NormalBallChart.inv] using
        htargetMem
  have hraw :=
    stagePtsSub_eq_raw inp P L phi hphi alpha target k l z
      (chart := d.chart) hsmallSub
  constructor
  · rw [hraw]
    exact stageTarget_local (I := I) inp P Lphi r k l
      alpha.1 target.1.1 z (chart := d.chart) hsrc
  · rw [hraw]
    exact stageTarget_chart (I := I) inp P Lphi r k l
      alpha.1 target.1.1 z (chart := d.chart)

theorem actual_cm_tail
    (inp : MetricCompactCore (I := I) X)
    (d : BoundedGeometryNormalChartData (I := I) X inp.decay)
    (aMin : Real) (haMin : 0 < aMin)
    (hphys : 8 * Real.exp inp.decay.C < aMin * inp.D)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P)
    {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (hdata : HasSuppConvDataOn (I := I) inp P L r hr phi hphi d.chart
      U C0 C1 aInf Jinf Jbarinf)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (q : LiveSlot L inp.pack r → NNReal)
    (δ : LiveSlot L inp.pack r → Real)
    (hqdata : ∀ gamma : LiveSlot L inp.pack r,
      let Rgamma := L.rInf (gamma.1 : Nat) + 1
      let rho := aMin * inp.decay.mu Rgamma
      0 < q gamma ∧ 0 < δ gamma ∧ 0 < rho ∧
        2 * rho < (q gamma : Real) ∧
        6 * (q gamma : Real) < d.phaseRadius Rgamma ∧
        3 * d.metricC 1 * (2 * (q gamma : Real)) ^ 2 ≤
          (2 / 3 : Real) * (q gamma : Real) ∧
        PhaseFlow.phaseErr (d.phaseK (2 * q gamma)) <
          ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
            (E × E) →L[Real] (E × E))‖₊⁻¹ ∧
        ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
            (E × E) →L[Real] (E × E))‖₊ *
            (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
              (E × E) →L[Real] (E × E))‖₊⁻¹ -
              PhaseFlow.phaseErr (d.phaseK (2 * q gamma)))⁻¹ *
            PhaseFlow.phaseErr (d.phaseK (2 * q gamma)) < 1 / 24)
    (hbranch : ∀ᶠ n in Filter.atTop,
      ∀ gamma : LiveSlot L inp.pack r,
        let Rgamma := L.rInf (gamma.1 : Nat) + 1
        let rho := aMin * inp.decay.mu Rgamma
        let x0 := seqCenterD inp.decay P (L.subseq hphi) n
          (gamma.1 : Nat)
        letI : TopologicalSpace (X.obj ((L.subseq hphi).φ n)).M :=
          (X.obj ((L.subseq hphi).φ n)).topology
        letI : ChartedSpace H (X.obj ((L.subseq hphi).φ n)).M :=
          (X.obj ((L.subseq hphi).φ n)).charted
        letI : IsManifold I ∞ (X.obj ((L.subseq hphi).φ n)).M :=
          (X.obj ((L.subseq hphi).φ n)).smooth
        letI : T2Space
            (TangentBundle I (X.obj ((L.subseq hphi).φ n)).M) :=
          (X.obj ((L.subseq hphi).φ n)).t2TangentBundle
        ∃ e : OpenPartialHomeomorph (E × E) (E × E),
          IsNormalDiag (I := I) (X.obj ((L.subseq hphi).φ n))
              (hcomplete.complete ((L.subseq hphi).φ n))
              (hconn ((L.subseq hphi).φ n))
              x0 (q gamma) (δ gamma) e
              (c := d.chart ((L.subseq hphi).φ n) x0) ∧
            NormalDiagFence (I := I) (X.obj ((L.subseq hphi).φ n))
              x0 (q gamma) e
                (c := d.chart ((L.subseq hphi).φ n) x0) ∧
            ApproximatesLinearOn
              (e.symm : E × E → E × E)
              ((PhaseFlow.freeDiagCLE (E := E)).symm :
                (E × E) →L[Real] (E × E))
              e.target
              (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
                  (E × E) →L[Real] (E × E))‖₊ *
                (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
                    (E × E) →L[Real] (E × E))‖₊⁻¹ -
                  PhaseFlow.phaseErr (d.phaseK (2 * q gamma)))⁻¹ *
                PhaseFlow.phaseErr (d.phaseK (2 * q gamma))) ∧
            rho ≤ (d.chart ((L.subseq hphi).φ n) x0).radius / 4)
    (alpha : LiveSlot L inp.pack r)
    (eps : Real) (heps : 0 < eps) :
    ∃ rad : Real, 0 < rad ∧ rad < eps ∧
      ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N, ∀ z ∈ C0 alpha,
        let Lphi := L.subseq hphi
        let Yl := X.obj (Lphi.φ l)
        letI : TopologicalSpace Yl.M := Yl.topology
        letI : ChartedSpace H Yl.M := Yl.charted
        letI : IsManifold I ∞ Yl.M := Yl.smooth
        letI : IsManifold I 1 Yl.M := IsManifold.of_le
          (I := I) (M := Yl.M) (n := ∞) (by decide)
        letI : SigmaCompactSpace Yl.M := Yl.sigmaCompact
        letI : T2Space Yl.M := Yl.t2
        letI : ConnectedSpace Yl.M := hconn (Lphi.φ l)
        letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
        letI : TopologicalSpace.MetrizableSpace Yl.M :=
          Manifold.metrizableSpace I Yl.M
        letI : T3Space Yl.M := inferInstance
        letI : RiemannianBundle (fun y : Yl.M ↦ TangentSpace I y) :=
          Yl.riemBundle (I := I)
        letI : (y : Yl.M) → InnerProductSpace Real (TangentSpace I y) :=
          Yl.riemInner (I := I)
        letI : IsContinuousRiemannianBundle E
            (fun y : Yl.M ↦ TangentSpace I y) := Yl.riemBundle_cont (I := I)
        letI : EMetricSpace Yl.M := Yl.emetricSpace (I := I)
        letI : CompleteSpace Yl.M :=
          MetricComplete.complete (I := I) Yl
            (hcomplete.complete (Lphi.φ l))
        letI : MetricSpace Yl.M :=
          HopfRinow.riemMetricSpace (I := I) (M := Yl.M)
        let x0 := seqCenterD inp.decay P Lphi l (alpha.1 : Nat)
        let chiL := d.chart (Lphi.φ l) x0
        let mu := stageWeightSub inp P L hr phi hphi alpha k
          (chart := d.chart)
        let stagePts := fun w gamma =>
          chiL.hom (stagePtsSub inp P L phi hphi alpha k l w gamma
            (chart := d.chart))
        let qstar := chiL.hom
        let join := minJoin (I := I) Yl.metric (normal_enorm (I := I) Yl)
        let p := qstar z
        let pts := centerAverage.activeFill mu stagePts qstar z
        ∃ hcm : CenterInput (I := I) Yl.metric (mu z) pts join p rad,
          HasLiveChartCenterSolution (I := I) d P L inp.pack r (phi l) hcomplete hconn
            q δ alpha (mu z) pts join p rad hcm ∧
          dist
              (chiL.inv (centerOfMass (I := I) Yl.metric (mu z)
                pts join p rad hcm))
              z ≤ 4 * rad := by
  classical
  let Lphi := L.subseq hphi
  let rhoBase := aMin * inp.decay.mu (L.rInf (alpha.1 : Nat) + 1)
  let gap := rhoBase / 2 - 4 * L.lamInf (alpha.1 : Nat)
  have hgap : 0 < gap := by
    dsimp only [gap, rhoBase]
    linarith [lamInf_lt_halfMin inp.decay inp.hD hphys P L
      (alpha.1 : Nat)]
  let rad := min (gap / 12) (eps / 2)
  have hrad : 0 < rad := by
    dsimp only [rad]
    exact lt_min (div_pos hgap (by norm_num)) (div_pos heps (by norm_num))
  have hradEps : rad < eps := by
    have hle : rad ≤ eps / 2 := min_le_right _ _
    linarith
  have hcageReal : 4 * L.lamInf (alpha.1 : Nat) + 6 * rad <
      rhoBase / 2 := by
    have hradGap : rad ≤ gap / 12 := min_le_left _ _
    dsimp only [gap] at hradGap
    nlinarith
  have hcage : ENNReal.ofReal
        (4 * L.lamInf (alpha.1 : Nat) + 6 * rad) <
      ENNReal.ofReal (rhoBase / 2) := by
    exact (ENNReal.ofReal_lt_ofReal_iff
      (div_pos (mul_pos haMin (inp.decay.mu_pos _)) (by norm_num))).2
        hcageReal
  have hweightEv := hdata.weightSub_ev_raw inp P L hr phi hphi d.chart
    U C0 C1 aInf Jinf Jbarinf
  rw [Filter.eventually_atTop] at hweightEv
  rcases hweightEv with ⟨Nw, hweight⟩
  obtain ⟨Np, hpts⟩ := d.pts_dist_tail inp P L hr phi hphi U C0 C1
    aInf Jinf Jbarinf hdata alpha rad hrad
  have hbranchPhi := hbranch
  rw [Filter.eventually_atTop] at hbranchPhi
  rcases hbranchPhi with ⟨Nb, hbranchPhi⟩
  obtain ⟨_hU, _hC0, _hC1, hC01, hC1U⟩ :=
    hdata.core_on inp P L r hr d.chart U C0 C1 aInf Jinf Jbarinf alpha
  have hC0U : C0 alpha ⊆ U alpha :=
    hC01.trans (interior_subset.trans hC1U)
  refine ⟨rad, hrad, hradEps, max Nw (max Np Nb), ?_⟩
  intro k hk l hl z hz
  have hkW : Nw ≤ k := by omega
  have hkP : Np ≤ k := by omega
  have hlP : Np ≤ l := by omega
  have hlB : Nb ≤ l := by omega
  let Yl := X.obj (L.φ (phi l))
  let : TopologicalSpace Yl.M := Yl.topology
  let : ChartedSpace H Yl.M := Yl.charted
  let : IsManifold I ∞ Yl.M := Yl.smooth
  let : IsManifold I 1 Yl.M := IsManifold.of_le
    (I := I) (M := Yl.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Yl.M := Yl.sigmaCompact
  let : T2Space Yl.M := Yl.t2
  let : ConnectedSpace Yl.M := hconn (L.φ (phi l))
  let : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Yl.M :=
    Manifold.metrizableSpace I Yl.M
  let : T3Space Yl.M := inferInstance
  let : RiemannianBundle (fun y : Yl.M ↦ TangentSpace I y) :=
    Yl.riemBundle (I := I)
  let : (y : Yl.M) → InnerProductSpace Real (TangentSpace I y) :=
    Yl.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : Yl.M ↦ TangentSpace I y) := Yl.riemBundle_cont (I := I)
  let : EMetricSpace Yl.M := Yl.emetricSpace (I := I)
  let : CompleteSpace Yl.M :=
    MetricComplete.complete (I := I) Yl (hcomplete.complete (L.φ (phi l)))
  let : MetricSpace Yl.M :=
    HopfRinow.riemMetricSpace (I := I) (M := Yl.M)
  let x0 := seqCenterD inp.decay P L (phi l) (alpha.1 : Nat)
  let chiL := d.chart (L.φ (phi l)) x0
  let mu := stageWeightSub inp P L hr phi hphi alpha k (chart := d.chart)
  let stagePts := fun w gamma =>
    chiL.hom (stagePtsSub inp P L phi hphi alpha k l w gamma
      (chart := d.chart))
  let qstar := chiL.hom
  let join := minJoin (I := I) Yl.metric (normal_enorm (I := I) Yl)
  let p := qstar z
  let pts := centerAverage.activeFill mu stagePts qstar z
  have hmu := hweight k hkW alpha
  have hzU : z ∈ U alpha := hC0U hz
  have hactive : ∀ gamma, mu z gamma ≠ 0 →
      dist p (stagePts z gamma) < rad := by
    intro gamma _hne
    have hclose := hpts k hkP l hlP z hz gamma
    have hproper :
        (letI : MetricSpace Yl.M := (P (L.φ (phi l))).ms
         dist p (stagePts z gamma)) < rad := by
      with_unfolding_all exact hclose
    have hhd : inp.decay.dist (L.φ (phi l)) p (stagePts z gamma) < rad := by
      rw [← ProperMetricOn.dist_eq inp.decay inp.realizes P (L.φ (phi l))
        p (stagePts z gamma)]
      exact hproper
    have hed : riemannianEDist I p (stagePts z gamma) =
        ENNReal.ofReal (inp.decay.dist (L.φ (phi l)) p
          (stagePts z gamma)) := by
      have hrealize := inp.realizes.edist_eq (L.φ (phi l))
        p (stagePts z gamma)
      change riemannianEDist I p (stagePts z gamma) = _ at hrealize
      exact hrealize
    rw [HopfRinow.riemMetric_dist_eq, hed,
      ENNReal.toReal_ofReal (inp.realizes.dist_nonneg
        (L.φ (phi l)) p (stagePts z gamma))]
    exact hhd
  have hptsFilled : ∀ gamma, dist p (pts gamma) < rad := by
    simpa only [pts, p] using
      centerAverage.activeFill_close
        (g := Yl.metric) (μ := mu) (pts := stagePts) (qstar := qstar)
        (x := z) hrad hactive
  have hpHat : p ∈
      L.hatBall inp.decay inp.D P inp.pack r (phi l) alpha.1 := by
    have hpGeom :=
      ((hdata.geom_on inp P L r hr d.chart U C0 C1 aInf Jinf Jbarinf
        l alpha).2 hzU).1
    have hpEq : p = NormalChartFamily.hom d.chart (L.φ (phi l))
        (seqCenterD inp.decay P L (phi l) (alpha.1 : Nat)) z := by
      with_unfolding_all rfl
    rw [hpEq]
    exact hpGeom
  have hproperCenter :
      (letI : MetricSpace Yl.M := (P (L.φ (phi l))).ms
       dist p x0) < 4 * L.lamInf (alpha.1 : Nat) := by
    have hhat := hat_dist_centerD inp.decay P L inp.pack r hpHat
    simpa only [x0] using hhat
  have hhdCenter : inp.decay.dist (L.φ (phi l)) p x0 <
      4 * L.lamInf (alpha.1 : Nat) := by
    rw [← ProperMetricOn.dist_eq inp.decay inp.realizes P (L.φ (phi l)) p x0]
    exact hproperCenter
  have hedCenter : riemannianEDist I p x0 =
      ENNReal.ofReal (inp.decay.dist (L.φ (phi l)) p x0) := by
    have hrealize := inp.realizes.edist_eq (L.φ (phi l)) p x0
    change riemannianEDist I p x0 = _ at hrealize
    exact hrealize
  have hpq : dist x0 p ≤ 4 * L.lamInf (alpha.1 : Nat) := by
    rw [dist_comm, HopfRinow.riemMetric_dist_eq, hedCenter,
      ENNReal.toReal_ofReal (inp.realizes.dist_nonneg (L.φ (phi l)) p x0)]
    exact hhdCenter.le
  have hfull := hbranchPhi l hlB alpha
  rcases hfull with ⟨e, he, hf, happrox, hρInner⟩
  rcases hqdata alpha with
    ⟨hq, _hδ, hρ, hρq, _hqWide, hqAcc, _herr, hinvErr⟩
  have hρInner' : rhoBase ≤ chiL.radius / 4 := by
    with_unfolding_all exact hρInner
  have hstrict : StrictDistInput (I := I) Yl.metric pts join p rad := by
    simpa only [Yl, x0, rhoBase, pts, join, Lphi, NetLimitData.subseq,
      Function.comp_apply, seqCenterD_subseq] using
      d.strict_dist_input (L.φ (phi l))
        (hcomplete.complete (L.φ (phi l)))
        (hconn (L.φ (phi l)))
        (seqCenterD inp.decay P L (phi l) (alpha.1 : Nat))
        hq he hf happrox hinvErr hqAcc pts p rad
        (4 * L.lamInf (alpha.1 : Nat)) hρInner hρ hρq hrad hpq
        hptsFilled hcage
  have hcm : CenterInput (I := I) Yl.metric (mu z) pts join p rad := by
    simpa only [pts, p] using
      centerAverage.inputOfFillSelf (I := I)
        (g := Yl.metric) (μ := mu) (pts := stagePts) (join := join)
        (r := fun _ => rad) (qstar := qstar) z
        (inferInstance : CompleteSpace Yl.M) hrad hactive
        (hmu.nonneg z hzU) (hmu.pos z hzU) hstrict
  have hcage2 : ENNReal.ofReal
        (4 * L.lamInf (alpha.1 : Nat) + 2 * rad) <
      ENNReal.ofReal (rhoBase / 2) := by
    apply (ENNReal.ofReal_le_ofReal ?_).trans_lt hcage
    nlinarith [hrad]
  have hout := d.has_live_chart_center_solution_of_cage
    P inp.realizes L inp.pack r (phi l)
    hcomplete hconn q δ hqdata (hbranchPhi l hlB) alpha
    (mu z) pts join p rad hcm (hmu.sum_one z hzU) hpHat hcage2
  let c := centerOfMass (I := I) Yl.metric (mu z) pts join p rad hcm
  have hcMem : c ∈ Metric.closedBall p (2 * rad) := by
    simpa only [c] using centerOfMass.mem hcm
  have hpc : dist p c ≤ 2 * rad := by
    simpa only [dist_comm] using Metric.mem_closedBall.mp hcMem
  have hjoinDist {t : Real} (ht : 0 ≤ t) :
      dist p (join p c t) ≤ dist p c * t := by
    have hed := minJoin_edist_le (I := I) Yl.metric
      (normal_enorm (I := I) Yl) p c ht
    have hmono := ENNReal.toReal_mono ENNReal.ofReal_ne_top hed
    have hmul : 0 ≤ (riemannianEDist I p c).toReal * t :=
      mul_nonneg ENNReal.toReal_nonneg ht
    rw [ENNReal.toReal_ofReal hmul] at hmono
    simpa only [join, ← HopfRinow.riemMetric_dist_eq] using hmono
  have hjoin : Set.MapsTo (join p c) (Set.Icc (0 : Real) 1)
      (chiL.hom.target ∩ chiL.inv ⁻¹'
        Metric.ball (0 : E) chiL.radius) := by
    intro t ht
    have hpt : dist p (join p c t) ≤ 2 * rad := by
      calc
        dist p (join p c t) ≤ dist p c * t := hjoinDist ht.1
        _ ≤ dist p c * 1 :=
          mul_le_mul_of_nonneg_left ht.2 dist_nonneg
        _ ≤ 2 * rad := by simpa only [mul_one] using hpc
    have hxt : dist x0 (join p c t) ≤
        4 * L.lamInf (alpha.1 : Nat) + 2 * rad := by
      calc
        dist x0 (join p c t) ≤ dist x0 p + dist p (join p c t) :=
          dist_triangle _ _ _
        _ ≤ 4 * L.lamInf (alpha.1 : Nat) + 2 * rad :=
          add_le_add hpq hpt
    have hxtRho : dist x0 (join p c t) < rhoBase / 2 :=
      hxt.trans_lt (by nlinarith [hcageReal, hrad])
    have hriem : riemannianEDist I x0 (join p c t) =
        ENNReal.ofReal (dist x0 (join p c t)) := by
      rw [HopfRinow.riemMetric_dist_eq]
      exact (ENNReal.ofReal_toReal
        (Exponential.riemannianEDist_ne_top (I := I) _ _)).symm
    have hradPos := chiL.radius_pos
    have hhalfChart : rhoBase / 2 < chiL.radius := by
      nlinarith [hρInner', hρ]
    have hyRad : riemannianEDist I x0 (join p c t) <
        ENNReal.ofReal chiL.radius := by
      rw [hriem]
      exact (ENNReal.ofReal_lt_ofReal_iff hradPos).2
        (hxtRho.trans hhalfChart)
    have hyControl := d.toNormalChartData.mem_image_and_norm_inv_eq_riemannian_distance
      (Lphi.φ l) (hcomplete.complete (Lphi.φ l))
        (hconn (Lphi.φ l)) x0 (join p c t) hyRad
    obtain ⟨w, hw, hwy⟩ := hyControl.1
    have hwsrc : w ∈ chiL.hom.source := chiL.ball_subset hw
    have hytarget : join p c t ∈ chiL.hom.target := by
      rw [← hwy]
      exact chiL.hom.map_source hwsrc
    have hinv : chiL.inv (join p c t) = w := by
      rw [← hwy]
      exact chiL.hom.left_inv hwsrc
    refine ⟨hytarget, ?_⟩
    change chiL.inv (join p c t) ∈ Metric.ball (0 : E) chiL.radius
    rw [hinv]
    exact hw
  have hEquiv := d.metric_equiv (L.φ (phi l)) x0
  have hchart := NormalBallChart.MetricEquivOn.inv_dist_le
    (J := I) Yl (hcomplete.complete (L.φ (phi l)))
      (hconn (L.φ (phi l))) (normal_enorm (I := I) Yl) chiL hEquiv hjoin
  have hchart' : dist (chiL.inv p) (chiL.inv c) ≤
      Real.sqrt 2 * dist p c := by
    simpa only [← HopfRinow.riemMetric_dist_eq] using hchart
  obtain ⟨hRad, _hMaps⟩ :=
    hdata.geom_on inp P L r hr d.chart U C0 C1 aInf Jinf Jbarinf l alpha
  have hpDecode : chiL.inv p = z := by
    change chiL.hom.symm (chiL.hom z) = z
    exact chiL.hom.left_inv (chiL.ball_subset (hRad hzU))
  have hsqrt : Real.sqrt 2 ≤ 2 := by
    linarith [Real.sqrt_two_lt_three_halves]
  have hcoord : dist (chiL.inv c) z ≤ 4 * rad := by
    rw [← hpDecode, dist_comm]
    calc
      dist (chiL.inv p) (chiL.inv c) ≤
          Real.sqrt 2 * dist p c := hchart'
      _ ≤ Real.sqrt 2 * (2 * rad) :=
        mul_le_mul_of_nonneg_left hpc (Real.sqrt_nonneg 2)
      _ ≤ 2 * (2 * rad) :=
        mul_le_mul_of_nonneg_right hsqrt (mul_nonneg (by norm_num) hrad.le)
      _ = 4 * rad := by ring
  with_unfolding_all
    exact ⟨hcm, hout, hcoord⟩

end BoundedGeometryNormalChartData

def HasStageRootReadout
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (C0 : LiveSlot L inp.pack r → Set E)
    (alpha : LiveSlot L inp.pack r)
    (Phi3 : Nat → Nat → Nat → E → E)
    (chart : NormalChartFamily (I := I) X :=
      c2RadiusNormalChartFamily (I := I) X) : Prop :=
  ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N, ∀ z ∈ C0 alpha,
    let Lphi := L.subseq hphi
    let Yk := X.obj (Lphi.φ k)
    let Yl := X.obj (Lphi.φ l)
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
    let chiK := chart (Lphi.φ k)
      (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
    let chiL := chart (Lphi.φ l)
      (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
    chiK.hom z ∈ Lphi.hatSourceBall inp.decay P r k →
      chiL.inv
          (stageComparisonMap inp P Lphi r hr k l
            (chiK.hom z) (chart := chart)) =
          Phi3 l k l z ∧
        Phi3 l k l z ∈ Metric.ball 0 chiL.radius ∧
        stageComparisonMap inp P Lphi r hr k l
            (chiK.hom z) (chart := chart) =
          chiL.hom (Phi3 l k l z) ∧
        stageComparisonMap inp P Lphi r hr k l
            (chiK.hom z) (chart := chart) ∈
          chiL.hom.target

theorem HasSuppConvData.stage_root_tail
    (inp : MetricCompactnessInputs (I := I) X)
    (aMin : Real) (haMin : 0 < aMin)
    (hphys : 8 * Real.exp inp.decay.C < aMin * inp.D)
    (h8 : (8 : Real) < inp.normalRadius.gpRatio * inp.D)
    (hradRatio : 2 * exponentialBallRadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P)
    (hstable : ∀ a b : Nat,
      (∀ᶠ k in Filter.atTop,
        BInter inp.decay inp.D P L.lamInf a b (L.φ k)) ∨
      (∀ᶠ k in Filter.atTop,
        ¬ BInter inp.decay inp.D P L.lamInf a b (L.φ k)))
    {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (hdata : HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (q : LiveSlot L inp.pack r → NNReal)
    (δ : LiveSlot L inp.pack r → Real)
    (hqdata : ∀ gamma : LiveSlot L inp.pack r,
      let rho := aMin * inp.decay.mu (L.rInf (gamma.1 : Nat) + 1)
      0 < q gamma ∧ 0 < δ gamma ∧ 0 < rho ∧
        2 * rho < (q gamma : Real))
    (hqAcc : ∀ gamma : LiveSlot L inp.pack r,
      3 * inp.normalBounds.metricC 1 * (2 * (q gamma : Real)) ^ 2 ≤
        (2 / 3 : Real) * (q gamma : Real))
    (hbranch : ∀ᶠ n in Filter.atTop,
      HasLiveBrFull (I := I) P (L.subseq hphi) inp.pack r n
        hcomplete hconn aMin q δ)
    (hscale : ∀ᶠ n in Filter.atTop,
      ∀ gamma : LiveSlot L inp.pack r,
        let Lphi := L.subseq hphi
        let rho := aMin * inp.decay.mu (Lphi.rInf (gamma.1 : Nat) + 1)
        let x := seqCenterD inp.decay P Lphi n (gamma.1 : Nat)
        letI : TopologicalSpace (X.obj (Lphi.φ n)).M :=
          (X.obj (Lphi.φ n)).topology
        letI : ChartedSpace H (X.obj (Lphi.φ n)).M :=
          (X.obj (Lphi.φ n)).charted
        letI : IsManifold I ∞ (X.obj (Lphi.φ n)).M :=
          (X.obj (Lphi.φ n)).smooth
        letI : T2Space (TangentBundle I (X.obj (Lphi.φ n)).M) :=
          (X.obj (Lphi.φ n)).t2TangentBundle
        Metric.ball (0 : E) rho ⊆
            normalQuarter (I := I) (X.obj (Lphi.φ n)) x ∧
          rho ≤ inp.normalBounds.radius (Lphi.φ n) x ∧
          rho / 2 ≤ expRadiusGp
            (I := I) (X.obj (Lphi.φ n)).metric x)
    (alpha : LiveSlot L inp.pack r)
    (e : Nat → OpenPartialHomeomorph (E × E) (E × E))
    (hdiag :
      let Lphi := L.subseq hphi
      ∀ n, IsNormalDiag (I := I) (X.obj (Lphi.φ n))
        (hcomplete.complete (Lphi.φ n)) (hconn (Lphi.φ n))
        (seqCenterD inp.decay P Lphi n (alpha.1 : Nat))
        (q alpha) (δ alpha) (e n))
    (hfence :
      let Lphi := L.subseq hphi
      ∀ n, NormalDiagFence (I := I) (X.obj (Lphi.φ n))
        (seqCenterD inp.decay P Lphi n (alpha.1 : Nat)) (q alpha) (e n))
    (W : Set E) (PhiInf : E → E) (rootRho : Real)
    (Phi3 : Nat → Nat → Nat → E → E)
    (hroot : HasStageRootCube inp.toCore P L hr phi hphi C1 alpha e
      W PhiInf rootRho Phi3) :
    HasStageRootReadout inp.toCore P L hr phi hphi C0 alpha Phi3 := by
  dsimp only [HasStageRootReadout]
  rcases hroot with
    ⟨_hW, _hWcpt, hC1W, hrootRho, hPhiInf, _htriple,
      Nroot, hrootTail⟩
  have heps : 0 < rootRho / 4 := by positivity
  obtain ⟨rad, hrad, hradSmall, Ncm, hcmTail⟩ :=
    hdata.actual_cm_tail inp aMin haMin hphys h8 hradRatio
      P L hstable hr phi hphi U C0 C1 aInf Jinf Jbarinf
      hcomplete hconn q δ hqdata hqAcc hbranch hscale alpha
      (rootRho / 4) heps
  obtain ⟨Ntgt, htgtTail⟩ :=
    hdata.pts_target_tail inp h8 hradRatio P L hstable hr
      phi hphi U C0 C1 aInf Jinf Jbarinf
  refine ⟨max Nroot (max Ncm Ntgt), ?_⟩
  intro k hk l hl z hz hx
  have hkRoot : Nroot ≤ k := by omega
  have hlRoot : Nroot ≤ l := by omega
  have hkCm : Ncm ≤ k := by omega
  have hlCm : Ncm ≤ l := by omega
  have hkTgt : Ntgt ≤ k := by omega
  have hlTgt : Ntgt ≤ l := by omega
  let Lphi := L.subseq hphi
  let Yk := X.obj (Lphi.φ k)
  let Yl := X.obj (Lphi.φ l)
  let : TopologicalSpace Yk.M := Yk.topology
  let : ChartedSpace H Yk.M := Yk.charted
  let : IsManifold I ∞ Yk.M := Yk.smooth
  let : T2Space Yk.M := Yk.t2
  let : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
  let : TopologicalSpace Yl.M := Yl.topology
  let : ChartedSpace H Yl.M := Yl.charted
  let : IsManifold I ∞ Yl.M := Yl.smooth
  let : IsManifold I 1 Yl.M := IsManifold.of_le
    (I := I) (M := Yl.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Yl.M := Yl.sigmaCompact
  let : T2Space Yl.M := Yl.t2
  let : ConnectedSpace Yl.M := hconn (Lphi.φ l)
  let : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Yl.M :=
    Manifold.metrizableSpace I Yl.M
  let : T3Space Yl.M := inferInstance
  let : RiemannianBundle (fun y : Yl.M ↦ TangentSpace I y) :=
    Yl.riemBundle (I := I)
  let : (y : Yl.M) → InnerProductSpace Real (TangentSpace I y) :=
    Yl.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : Yl.M ↦ TangentSpace I y) := Yl.riemBundle_cont (I := I)
  let : EMetricSpace Yl.M := Yl.emetricSpace (I := I)
  let : CompleteSpace Yl.M :=
    MetricComplete.complete (I := I) Yl (hcomplete.complete (Lphi.φ l))
  let : MetricSpace Yl.M :=
    HopfRinow.riemMetricSpace (I := I) (M := Yl.M)
  let chiK := NormalCoordinates.normalChartAt (I := I) Yk.metric
    (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
  let chiL := NormalCoordinates.normalChartAt (I := I) Yl.metric
    (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
  let mu := stageWeightSub inp.toCore P L hr phi hphi alpha k
  let stagePts := fun w gamma =>
    stageTarget inp.toCore P Lphi r k l (chiK.symm w) gamma
  let qstar := fun w => chiL.symm w
  let p := qstar z
  let x0 := seqCenterD inp.decay P Lphi l (alpha.1 : Nat)
  let join := minJoin (I := I) Yl.metric (normal_enorm (I := I) Yl)
  let pts := centerAverage.activeFill mu stagePts qstar z
  have hcmOut := hcmTail k hkCm l hlCm z hz
  dsimp only at hcmOut
  rcases hcmOut with ⟨hcm, hstrict, hcoord⟩
  let c := centerOfMass (I := I) Yl.metric (mu z) pts join p rad hcm
  let zc := chiL c
  let xi : Fin (inp.pack.A r) → E := fun i => chiL (pts i)
  have hzcClose : dist zc z < rootRho := by
    have hfour : 4 * rad < rootRho := by nlinarith [hradSmall]
    have hcoordLe : dist zc z ≤ 4 * rad := by
      simpa only [zc, c, mu, pts, join, p, qstar, stagePts, chiL] using
        hcoord
    exact hcoordLe.trans_lt hfour
  dsimp only [HasChartCmSol] at hstrict
  rcases hstrict with ⟨hqSel, eSel, heSel, hfSel, hread⟩
  rcases hread with ⟨hcTarget, hsol⟩
  have hsolSel : HasCmSolC (I := I) Yl.metric
      (normal_enorm (I := I) Yl) x0
      (c2RadiusNormalBallChart (I := I) Yl x0)
      (IsNormalDiag.toBranch (I := I) Yl
        (hcomplete.complete (Lphi.φ l)) (hconn (Lphi.φ l))
        x0 hqSel heSel) zc (mu z, xi) := by
    with_unfolding_all exact hsol
  let chartSel := c2RadiusNormalBallChart (I := I) Yl x0
  have htgtSel : ∀ i, (zc, xi i) ∈ eSel.target := by
    intro i
    have hzcTarget : chartSel.hom zc ∈ chartSel.restrictBall.target := by
      have hmap := chartSel.restrictBall.map_source hsolSel.1
      change chartSel.hom zc ∈ chartSel.restrictBall.target at hmap
      exact hmap
    have hxiTarget : chartSel.hom (xi i) ∈ chartSel.restrictBall.target := by
      have hmap := chartSel.restrictBall.map_source (hsolSel.2.1 i)
      change chartSel.hom (xi i) ∈ chartSel.restrictBall.target at hmap
      exact hmap
    have hout := IsNormalDiag.target_of_inv_dom (I := I) Yl
      (hcomplete.complete (Lphi.φ l)) (hconn (Lphi.φ l))
      x0 hqSel heSel hzcTarget hxiTarget (hsolSel.2.2.1 i).1
    have hzcDecode : chartSel.inv (chartSel.hom zc) = zc :=
      chartSel.hom.left_inv (chartSel.ball_subset hsolSel.1)
    have hxiDecode : chartSel.inv (chartSel.hom (xi i)) = xi i :=
      chartSel.hom.left_inv (chartSel.ball_subset (hsolSel.2.1 i))
    rwa [hzcDecode, hxiDecode] at hout
  have hselZero : invVelSum eSel (mu z) xi zc = 0 := by
    exact (IsNormalDiag.chartCmC_zero_iff (I := I) Yl
      (hcomplete.complete (Lphi.φ l)) (hconn (Lphi.φ l))
      x0 hqSel heSel hfSel zc (mu z) xi htgtSel).mp hsolSel.2.2.2.1
  have hzcBall := hsolSel.1
  have heCanon : IsNormalDiag (I := I) Yl
      (hcomplete.complete (Lphi.φ l)) (hconn (Lphi.φ l)) x0
      (q alpha) (δ alpha) (e l) := by
    simpa only [Lphi, Yl, x0] using hdiag l
  have hfCanon : NormalDiagFence (I := I) Yl x0 (q alpha) (e l) := by
    simpa only [Lphi, Yl, x0] using hfence l
  have heq : e l ≈ eSel :=
    IsNormalDiag.eqOnSource (I := I) Yl
      (hcomplete.complete (Lphi.φ l)) (hconn (Lphi.φ l)) x0
      heCanon hfCanon heSel hfSel
  have hcanonXiZero : invVelSum (e l) (mu z) xi zc = 0 := by
    calc
      invVelSum (e l) (mu z) xi zc = invVelSum eSel (mu z) xi zc :=
        (invVelSum_congr_br eSel (e l) (mu z) xi zc (Setoid.symm heq)
          (fun i _hne => by
            simpa only [zc, xi, c, mu, pts, join, p] using htgtSel i)).symm
      _ = 0 := hselZero
  obtain ⟨_hU, _hC0, _hC1, hC01, hC1U⟩ :=
    hdata.core_on inp P L r hr U C0 C1 aInf Jinf Jbarinf alpha
  have hzU : z ∈ U alpha := hC1U (interior_subset (hC01 hz))
  have hxi : ∀ i, mu z i ≠ 0 →
      xi i = stagePtsSub inp.toCore P L phi hphi alpha k l z i := by
    intro i hi
    have hdecode := htgtTail k hkTgt l hlTgt alpha z hzU i hi
    dsimp only at hdecode
    dsimp only [xi, pts]
    simp only [centerAverage.activeFill, hi, ↓reduceIte]
    simpa only [stagePts, chiL, chiK, Lphi, Yk, Yl] using hdecode.2
  have hcanonPtsZero : invVelSum (e l) (mu z)
      (stagePtsSub inp.toCore P L phi hphi alpha k l z) zc = 0 := by
    calc
      invVelSum (e l) (mu z)
          (stagePtsSub inp.toCore P L phi hphi alpha k l z) zc =
          invVelSum (e l) (mu z) xi zc :=
        (invVelSum_congr_ne (e l) (mu z) xi
          (stagePtsSub inp.toCore P L phi hphi alpha k l z) zc hxi).symm
      _ = 0 := hcanonXiZero
  have hstageZero : stageInvVelSub inp P L hr phi hphi alpha e
      l k l (z, zc) = 0 := by
    simpa only [stageInvVelSub, stageCfgSub, mu] using hcanonPtsZero
  have hzC1 : z ∈ C1 alpha := interior_subset (hC01 hz)
  have hzClosure : z ∈ closure W := subset_closure (hC1W hzC1)
  have hrootData := hrootTail l hlRoot k hkRoot l hlRoot
  have hspec := hrootData.2 z hzClosure
  rcases hspec with
    ⟨_hPhiClose, _hPhiZero, _hInvertible, _hPhiTarget, huniq⟩
  have hPhiInfZ : PhiInf z = z := by
    simpa only [id_eq] using hPhiInf hzC1
  have hzcTube : dist zc (PhiInf z) < rootRho := by
    rw [hPhiInfZ]
    exact hzcClose
  have hcenterRoot : zc = Phi3 l k l z :=
    (huniq zc hzcTube).mp hstageZero
  let x : Yk.M := chiK.symm z
  let i0 := baseIndex inp.decay inp.realizes inp.pack hr
  have hseq :
      seqAtom inp.decay inp.hD P Lphi inp.pack r k =
        seqAtom inp.decay inp.hD P L inp.pack r (phi k) := by
    funext gamma
    exact seqAtom_subseq inp.decay inp.hD P L inp.pack r hphi k gamma
  obtain ⟨_hRadK, hExpK, _hMapsK⟩ :=
    hdata.geom_on inp P L r hr U C0 C1 aInf Jinf Jbarinf k alpha
  have hzBallK := hExpK hzU
  have hzNormK : ‖z‖ < expMapC2Radius (I := I) Yk.metric
      (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) := by
    simpa only [Metric.mem_ball, dist_zero_right, Yk, Lphi,
      NetLimitData.subseq_phi, Function.comp_apply, seqCenterD_subseq,
      NormalChartFamily.radius, c2RadiusNormalChartFamily,
      c2_radius_normal_ball_chart_radius] using hzBallK
  have hzTargetK : z ∈ chiK.target := by
    exact ball_subset_normalChartAt_target (I := I) Yk.metric
      (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) hzNormK
  have hzExpSrcK : z ∈
      (NormalCoordinates.expMapDiffeo (I := I) Yk.metric
        (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))).source := by
    simpa only [chiK, NormalCoordinates.normalChartAt_target_eq] using
      hzTargetK
  have hzChartSrcK : z ∈
      (NormalCoordinates.normalChartAt (I := I) Yk.metric
        (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))).symm.source := by
    change z ∈ (NormalCoordinates.normalChartAt (I := I) Yk.metric
      (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))).target
    simpa only [NormalCoordinates.normalChartAt_target_eq] using hzExpSrcK
  have hchiK : x =
      (c2RadiusNormalChartFamily (I := I) X).hom (L.φ (phi k))
        (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat)) z := by
    change (NormalCoordinates.normalChartAt (I := I) Yk.metric
      (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))).symm z = _
    rw [NormalCoordinates.normalChartAt_symm_apply (I := I) Yk.metric
      (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) hzChartSrcK]
    rw [← NormalCoordinates.expMapDiffeo_apply_eq (I := I) Yk.metric
      (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) hzExpSrcK]
    simp only [Yk, Lphi, NetLimitData.subseq_phi, Function.comp_apply,
      seqCenterD_subseq, NormalChartFamily.hom, c2RadiusNormalChartFamily,
      c2_radius_normal_ball_chart_apply]
  let muM := fun (y : Yk.M) (gamma : Fin (inp.pack.A r)) =>
    rawWeights
      (cutRaw
        (seqAtom inp.decay inp.hD P Lphi inp.pack r k i0)
        (seqAtom inp.decay inp.hD P Lphi inp.pack r k) i0)
      y gamma
  let qstarM : Yk.M → Yl.M := fun _ => p
  let pM : Yk.M → Yl.M := fun _ => p
  let radM : Yk.M → Real := fun _ => rad
  have hmu : muM x = mu z := by
    funext gamma
    change muM x gamma =
      stageWeightSub inp.toCore P L hr phi hphi alpha k z gamma
    simp only [stageWeightSub, seqAtomOn, rawWeights, cutRaw,
      MetricCompactnessInputs.toCore]
    rw [hchiK]
    simp only [muM, i0, hseq, rawWeights, cutRaw,
      NormalChartFamily.hom, c2RadiusNormalChartFamily, c2_radius_normal_ball_chart_apply]
    rfl
  have hptsEq : centerAverage.activeFill muM
      (stageTarget inp.toCore P Lphi r k l) qstarM x = pts := by
    funext gamma
    simp only [centerAverage.activeFill]
    rw [congrFun hmu gamma]
    rfl
  have hcmM : CenterInput (I := I) Yl.metric (muM x)
      (centerAverage.activeFill muM (stageTarget inp.toCore P Lphi r k l)
        qstarM x) join (pM x) (radM x) := by
    rw [hmu, hptsEq]
    with_unfolding_all
      exact hcm
  have hmap := stageCompare_eq_cm (I := I) inp P Lphi r hr hconn k l
    qstarM join pM radM x hx
      (chart := c2RadiusNormalChartFamily (I := I) X) hcmM
  have hcGlobal : c = centerOfMass (I := I) Yl.metric (muM x)
      (centerAverage.activeFill muM (stageTarget inp.toCore P Lphi r k l)
        qstarM x) join (pM x) (radM x) hcmM := by
    apply centerOfMass.unique hcmM c
    intro y
    rw [hmu, hptsEq]
    with_unfolding_all
      exact centerOfMass.min hcm y
  have hmapC : stageComparisonMap inp.toCore P Lphi r hr k l x = c := by
    exact hmap.trans hcGlobal.symm
  have hchartReadout :
      chiL (stageComparisonMap inp.toCore P Lphi r hr k l x) =
        Phi3 l k l z := by
    rw [hmapC]
    exact hcenterRoot
  have hrootBall : Phi3 l k l z ∈ normalBall (I := I) Yl x0 := by
    change Phi3 l k l z ∈
      Metric.ball 0 (expMapC2Radius (I := I) Yl.metric x0)
    rw [← hcenterRoot]
    with_unfolding_all
      exact hzcBall
  have hdecode : chiL.symm zc = c := by
    have hright :=
      (c2RadiusNormalBallChart (I := I) Yl x0).restrictBall.right_inv hcTarget
    with_unfolding_all
      exact hright
  have hmapDecode :
      stageComparisonMap inp.toCore P Lphi r hr k l x =
        chiL.symm (Phi3 l k l z) := by
    calc
      stageComparisonMap inp.toCore P Lphi r hr k l x = c := hmapC
      _ = chiL.symm zc := hdecode.symm
      _ = chiL.symm (Phi3 l k l z) := congrArg chiL.symm hcenterRoot
  have htarget :
      stageComparisonMap inp.toCore P Lphi r hr k l x ∈
        (c2RadiusNormalBallChart (I := I) Yl x0).hom.target := by
    rw [hmapDecode]
    have hball :
        Phi3 l k l z ∈
          Metric.ball 0 (c2RadiusNormalBallChart (I := I) Yl x0).radius := by
      exact hrootBall
    have hExpSrc := (c2RadiusNormalBallChart (I := I) Yl x0).ball_subset hball
    have hExpSrc' : Phi3 l k l z ∈
        (NormalCoordinates.expMapDiffeo (I := I) Yl.metric x0).source := by
      with_unfolding_all
        exact hExpSrc
    have hChartSrc : Phi3 l k l z ∈
        (NormalCoordinates.normalChartAt (I := I) Yl.metric x0).symm.source := by
      change Phi3 l k l z ∈
        (NormalCoordinates.normalChartAt (I := I) Yl.metric x0).target
      simpa only [NormalCoordinates.normalChartAt_target_eq] using hExpSrc'
    have hchiL : chiL.symm (Phi3 l k l z) =
        NormalCoordinates.expMapDiffeo (I := I) Yl.metric x0
          (Phi3 l k l z) := by
      change (NormalCoordinates.normalChartAt (I := I) Yl.metric x0).symm
        (Phi3 l k l z) = _
      rw [NormalCoordinates.normalChartAt_symm_apply (I := I) Yl.metric x0
        hChartSrc]
      exact (NormalCoordinates.expMapDiffeo_apply_eq (I := I) Yl.metric x0
        hExpSrc').symm
    rw [hchiL]
    exact (c2RadiusNormalBallChart (I := I) Yl x0).hom.map_source hExpSrc
  exact ⟨hchartReadout, hrootBall, hmapDecode, htarget⟩

theorem HasSuppConvData.stage_jet_of_root
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (hdata : HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf)
    (alpha : LiveSlot L inp.pack r)
    (e : Nat → OpenPartialHomeomorph (E × E) (E × E))
    (W : Set E) (PhiInf : E → E) (rootRho : Real)
    (Phi3 : Nat → Nat → Nat → E → E)
    (hroot : HasStageRootCube inp P L hr phi hphi C1 alpha e
      W PhiInf rootRho Phi3)
    (hread : HasStageRootReadout inp P L hr phi hphi C0 alpha Phi3)
    (R : Real) (hRr : R < r)
    (p : Nat) (eps : Real) (heps : 0 < eps) :
    ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N, ∀ z ∈ C0 alpha,
      let Lphi := L.subseq hphi
      let Yk := X.obj (Lphi.φ k)
      let Yl := X.obj (Lphi.φ l)
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
      let chiK := NormalCoordinates.normalChartAt (I := I) Yk.metric
        (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
      let chiL := NormalCoordinates.normalChartAt (I := I) Yl.metric
        (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
      let Fkl := fun w =>
        chiL (stageComparisonMap inp P Lphi r hr k l (chiK.symm w))
      z ∈ interior (C0 alpha) →
      chiK.symm z ∈ Lphi.hatSourceBall inp.decay P R k →
        stageComparisonMap inp P Lphi r hr k l (chiK.symm z) ∈
            (normalExpPD (I := I) Yl
              (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))).target ∧
          ContDiffAt Real ∞ Fkl z ∧
          ∀ j ≤ p, mapDerivNorm j Fkl id z ≤ eps := by
  obtain ⟨_hU, hC0, _hC1, hC01, hC1U⟩ :=
    hdata.core_on inp P L r hr U C0 C1 aInf Jinf Jbarinf alpha
  let Lphi := L.subseq hphi
  let Psi : Nat → Nat → E → E := fun k l =>
    let Yk := X.obj (Lphi.φ k)
    let Yl := X.obj (Lphi.φ l)
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
    let chiK := NormalCoordinates.normalChartAt (I := I) Yk.metric
      (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
    let chiL := NormalCoordinates.normalChartAt (I := I) Yl.metric
      (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
    fun w => chiL
      (stageComparisonMap inp P Lphi r hr k l (chiK.symm w))
  let S : Nat → E → Prop := fun k z =>
    let Yk := X.obj (Lphi.φ k)
    letI : TopologicalSpace Yk.M := Yk.topology
    letI : ChartedSpace H Yk.M := Yk.charted
    letI : IsManifold I ∞ Yk.M := Yk.smooth
    letI : T2Space Yk.M := Yk.t2
    letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
    let chiK := NormalCoordinates.normalChartAt (I := I) Yk.metric
      (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
    z ∈ interior (C0 alpha) ∧
      chiK.symm z ∈ Lphi.hatSourceBall inp.decay P R k
  dsimp only [HasStageRootReadout] at hread
  obtain ⟨Nread, hreadTail⟩ := hread
  have hEq : ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N, ∀ z ∈ C0 alpha,
      S k z → Psi k l =ᶠ[nhds z] Phi3 l k l := by
    refine ⟨Nread, ?_⟩
    intro k hk l hl z _hz hSz
    let Yk := X.obj (Lphi.φ k)
    let Yl := X.obj (Lphi.φ l)
    let : TopologicalSpace Yk.M := Yk.topology
    let : ChartedSpace H Yk.M := Yk.charted
    let : IsManifold I ∞ Yk.M := Yk.smooth
    let : T2Space Yk.M := Yk.t2
    let : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
    let : MetricSpace Yk.M := (P (Lphi.φ k)).ms
    let : TopologicalSpace Yl.M := Yl.topology
    let : ChartedSpace H Yl.M := Yl.charted
    let : IsManifold I ∞ Yl.M := Yl.smooth
    let : T2Space Yl.M := Yl.t2
    let : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
    let chiK := NormalCoordinates.normalChartAt (I := I) Yk.metric
      (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
    let chiL := NormalCoordinates.normalChartAt (I := I) Yl.metric
      (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
    change z ∈ interior (C0 alpha) ∧
      chiK.symm z ∈ Lphi.hatSourceBall inp.decay P R k at hSz
    have hzU : z ∈ U alpha :=
      hC1U (interior_subset (hC01 (interior_subset hSz.1)))
    obtain ⟨_hRad, hExp, _hMaps⟩ :=
      hdata.geom_on inp P L r hr U C0 C1 aInf Jinf Jbarinf k alpha
    have hzBall := hExp hzU
    have hzTarget : z ∈ chiK.target := by
      have hzNorm : ‖z‖ < expMapC2Radius (I := I) Yk.metric
          (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) := by
        simpa only [Metric.mem_ball, dist_zero_right, Yk, Lphi,
          NetLimitData.subseq_phi, Function.comp_apply, seqCenterD_subseq,
          NormalChartFamily.radius, c2RadiusNormalChartFamily,
          c2_radius_normal_ball_chart_radius] using hzBall
      exact ball_subset_normalChartAt_target (I := I) Yk.metric
        (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) hzNorm
    have hchi : ContinuousAt chiK.symm z :=
      chiK.contMDiffOn_invFun.continuousOn.continuousAt
        (chiK.open_target.mem_nhds hzTarget)
    have hbigNhd : Lphi.hatSourceBall inp.decay P r k ∈ nhds (chiK.symm z) :=
      NetLimitData.hatSource_nhds (I := I) (X := X) inp.decay P Lphi
        (n := k) (R := R) (s := r) hRr hSz.2
    have hsource : ∀ᶠ y in nhds z,
        chiK.symm y ∈ Lphi.hatSourceBall inp.decay P r k :=
      hchi.eventually hbigNhd
    have hreadKL := hreadTail k hk l hl
    change (fun w => chiL
      (stageComparisonMap inp P Lphi r hr k l (chiK.symm w)))
        =ᶠ[nhds z] Phi3 l k l
    filter_upwards [isOpen_interior.mem_nhds hSz.1, hsource] with y hy hySource
    exact (hreadKL y (interior_subset hy) hySource).1
  obtain ⟨N, hN⟩ := hroot.at_tail inp P L hr phi hphi C1 alpha e
    W PhiInf rootRho Phi3 hC0 hC01 Psi S hEq p eps heps
  refine ⟨max N Nread, ?_⟩
  intro k hk l hl z hz
  dsimp only
  intro hzInt hxR
  have hSk : S k z := by
    dsimp only [S]
    exact ⟨hzInt, hxR⟩
  have hkRoot : N ≤ k := (Nat.le_max_left N Nread).trans hk
  have hlRoot : N ≤ l := (Nat.le_max_left N Nread).trans hl
  have hkRead : Nread ≤ k := (Nat.le_max_right N Nread).trans hk
  have hlRead : Nread ≤ l := (Nat.le_max_right N Nread).trans hl
  have hout := hN k hkRoot l hlRoot z hz hSk
  let Yk := X.obj (Lphi.φ k)
  let : TopologicalSpace Yk.M := Yk.topology
  let : ChartedSpace H Yk.M := Yk.charted
  let : IsManifold I ∞ Yk.M := Yk.smooth
  let : T2Space Yk.M := Yk.t2
  let : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
  let chiK := NormalCoordinates.normalChartAt (I := I) Yk.metric
    (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
  let Yl := X.obj (Lphi.φ l)
  let : TopologicalSpace Yl.M := Yl.topology
  let : ChartedSpace H Yl.M := Yl.charted
  let : IsManifold I ∞ Yl.M := Yl.smooth
  let : T2Space Yl.M := Yl.t2
  let : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
  let chiL := NormalCoordinates.normalChartAt (I := I) Yl.metric
    (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
  let x0 := seqCenterD inp.decay P Lphi l (alpha.1 : Nat)
  have hxBig : chiK.symm z ∈ Lphi.hatSourceBall inp.decay P r k :=
    mem_of_mem_nhds (NetLimitData.hatSource_nhds
      (I := I) (X := X) inp.decay P Lphi
      (n := k) (R := R) (s := r) hRr hxR)
  have hreadAt := hreadTail k hkRead l hlRead z hz hxBig
  have hrootBall : Phi3 l k l z ∈ normalBall (I := I) Yl x0 := by
    change Phi3 l k l z ∈
      Metric.ball 0 (expMapC2Radius (I := I) Yl.metric x0)
    with_unfolding_all
      exact hreadAt.2.1
  have hzU : z ∈ U alpha :=
    hC1U (interior_subset (hC01 (interior_subset hzInt)))
  obtain ⟨_hRadK, hExpK, _hMapsK⟩ :=
    hdata.geom_on inp P L r hr U C0 C1 aInf Jinf Jbarinf k alpha
  have hzBallK := hExpK hzU
  have hzNormK : ‖z‖ < expMapC2Radius (I := I) Yk.metric
      (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) := by
    simpa only [Metric.mem_ball, dist_zero_right, Yk, Lphi,
      NetLimitData.subseq_phi, Function.comp_apply, seqCenterD_subseq,
      NormalChartFamily.radius, c2RadiusNormalChartFamily,
      c2_radius_normal_ball_chart_radius] using hzBallK
  have hzTargetK : z ∈ chiK.target := by
    exact ball_subset_normalChartAt_target (I := I) Yk.metric
      (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) hzNormK
  have hzExpSrcK : z ∈
      (NormalCoordinates.expMapDiffeo (I := I) Yk.metric
        (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))).source := by
    simpa only [chiK, NormalCoordinates.normalChartAt_target_eq] using
      hzTargetK
  have hzChartSrcK : z ∈
      (NormalCoordinates.normalChartAt (I := I) Yk.metric
        (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))).symm.source := by
    change z ∈ (NormalCoordinates.normalChartAt (I := I) Yk.metric
      (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))).target
    simpa only [NormalCoordinates.normalChartAt_target_eq] using hzExpSrcK
  have hchiK : chiK.symm z =
      (c2RadiusNormalChartFamily (I := I) X).hom (L.φ (phi k))
        (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat)) z := by
    change (NormalCoordinates.normalChartAt (I := I) Yk.metric
      (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))).symm z = _
    rw [NormalCoordinates.normalChartAt_symm_apply (I := I) Yk.metric
      (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) hzChartSrcK]
    rw [← NormalCoordinates.expMapDiffeo_apply_eq (I := I) Yk.metric
      (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) hzExpSrcK]
    simp only [Yk, Lphi, NetLimitData.subseq_phi, Function.comp_apply,
      seqCenterD_subseq, NormalChartFamily.hom, c2RadiusNormalChartFamily,
      c2_radius_normal_ball_chart_apply]
  have htarget :
      stageComparisonMap inp P Lphi r hr k l (chiK.symm z) ∈
        (normalExpPD (I := I) Yl x0).target := by
    have hdecode := hreadAt.2.2.1
    have hdecodeExp :
        stageComparisonMap inp P Lphi r hr k l
            ((c2RadiusNormalChartFamily (I := I) X).hom (L.φ (phi k))
              (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat)) z) =
          NormalCoordinates.expMapDiffeo (I := I) Yl.metric x0
            (Phi3 l k l z) := by
      with_unfolding_all
        exact hdecode
    have hdecode' :
        stageComparisonMap inp P Lphi r hr k l (chiK.symm z) =
          normalExpPD (I := I) Yl x0 (Phi3 l k l z) := by
      calc
        stageComparisonMap inp P Lphi r hr k l (chiK.symm z) =
            stageComparisonMap inp P Lphi r hr k l
              ((c2RadiusNormalChartFamily (I := I) X).hom (L.φ (phi k))
                (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat)) z) :=
          congrArg (stageComparisonMap inp P Lphi r hr k l) hchiK
        _ = NormalCoordinates.expMapDiffeo (I := I) Yl.metric x0
              (Phi3 l k l z) := hdecodeExp
        _ = normalExpPD (I := I) Yl x0 (Phi3 l k l z) := by
          with_unfolding_all
            rfl
    rw [hdecode']
    apply (normalExpPD (I := I) Yl x0).map_source
    rw [normalExpPD_source]
    change Phi3 l k l z ∈
      Metric.ball 0 (expMapC2Radius (I := I) Yl.metric x0)
    exact hrootBall
  refine ⟨?_, ?_⟩
  · simpa only [chiK, Yk, Lphi] using htarget
  · simpa only [Psi] using hout

def HasStageJetTail
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (C0 : LiveSlot L inp.pack r → Set E)
    (R : Real) (p : Nat) (eps : Real)
    (chart : NormalChartFamily (I := I) X :=
      c2RadiusNormalChartFamily (I := I) X) : Prop :=
  ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N,
    ∀ alpha : LiveSlot L inp.pack r, ∀ z ∈ C0 alpha,
      let Lphi := L.subseq hphi
      let Yk := X.obj (Lphi.φ k)
      let Yl := X.obj (Lphi.φ l)
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
      let chiK := chart (Lphi.φ k)
        (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
      let chiL := chart (Lphi.φ l)
        (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
      let Fkl := fun w =>
        chiL.inv
          (stageComparisonMap inp P Lphi r hr k l
            (chiK.hom w) (chart := chart))
      z ∈ interior (C0 alpha) →
      chiK.hom z ∈ Lphi.hatSourceBall inp.decay P R k →
        stageComparisonMap inp P Lphi r hr k l
            (chiK.hom z) (chart := chart) ∈ chiL.restrictBall.target ∧
          ContDiffAt Real ∞ Fkl z ∧
          ∀ j ≤ p, mapDerivNorm j Fkl id z ≤ eps

theorem HasStageJetTail.subseq
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    {phi : Nat → Nat} (hphi : StrictMono phi)
    (C0 : LiveSlot L inp.pack r → Set E)
    (R : Real) (p : Nat) (eps : Real)
    (chart : NormalChartFamily (I := I) X :=
      c2RadiusNormalChartFamily (I := I) X)
    (h : HasStageJetTail inp P L hr phi hphi C0 R p eps
      (chart := chart))
    {ψ : Nat → Nat} (hψ : StrictMono ψ) :
    HasStageJetTail inp P L hr (phi ∘ ψ) (hphi.comp hψ)
      C0 R p eps (chart := chart) := by
  dsimp only [HasStageJetTail] at h ⊢
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  intro k hk l hl alpha z hz
  have hkψ : N ≤ ψ k := hk.trans (hψ.id_le k)
  have hlψ : N ≤ ψ l := hl.trans (hψ.id_le l)
  have hmap : ∀ x,
      stageComparisonMap inp P (L.subseq (hphi.comp hψ)) r hr k l x
          (chart := chart) =
        stageComparisonMap inp P (L.subseq hphi) r hr
          (ψ k) (ψ l) x (chart := chart) := by
    intro x
    exact congrFun (by
      simpa only [NetLimitData.subseq, Function.comp_apply] using
        (stageCompare_subseq (I := I) inp P (L.subseq hphi)
          r hr hψ k l (chart := chart))) x
  have hball :
      (L.subseq (hphi.comp hψ)).hatSourceBall inp.decay P R k =
        (L.subseq hphi).hatSourceBall inp.decay P R (ψ k) := rfl
  rw [hball]
  simp_rw [hmap]
  with_unfolding_all
    exact hN (ψ k) hkψ (ψ l) hlψ alpha z hz

theorem HasSuppConvData.stage_jet_tail
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (hdata : HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf)
    (e : (alpha : LiveSlot L inp.pack r) →
      Nat → OpenPartialHomeomorph (E × E) (E × E))
    (W : LiveSlot L inp.pack r → Set E)
    (PhiInf : LiveSlot L inp.pack r → E → E)
    (rootRho : LiveSlot L inp.pack r → Real)
    (Phi3 : LiveSlot L inp.pack r → Nat → Nat → Nat → E → E)
    (hroot : ∀ alpha, HasStageRootCube inp P L hr phi hphi C1 alpha
      (e alpha) (W alpha) (PhiInf alpha) (rootRho alpha) (Phi3 alpha))
    (hread : ∀ alpha,
      HasStageRootReadout inp P L hr phi hphi C0 alpha (Phi3 alpha))
    (R : Real) (hRr : R < r)
    (p : Nat) (eps : Real) (heps : 0 < eps) :
    HasStageJetTail inp P L hr phi hphi C0 R p eps := by
  classical
  dsimp only [HasStageJetTail]
  have hlocal : ∀ alpha : LiveSlot L inp.pack r,
      ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N, ∀ z ∈ C0 alpha,
        let Lphi := L.subseq hphi
        let Yk := X.obj (Lphi.φ k)
        let Yl := X.obj (Lphi.φ l)
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
        let chiK := c2RadiusNormalChartFamily (I := I) X (Lphi.φ k)
          (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
        let chiL := c2RadiusNormalChartFamily (I := I) X (Lphi.φ l)
          (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
        let Fkl := fun w =>
          chiL.inv
            (stageComparisonMap inp P Lphi r hr k l
              (chiK.hom w) (chart := c2RadiusNormalChartFamily (I := I) X))
        z ∈ interior (C0 alpha) →
        chiK.hom z ∈ Lphi.hatSourceBall inp.decay P R k →
          stageComparisonMap inp P Lphi r hr k l
              (chiK.hom z) (chart := c2RadiusNormalChartFamily (I := I) X) ∈
              chiL.restrictBall.target ∧
            ContDiffAt Real ∞ Fkl z ∧
            ∀ j ≤ p, mapDerivNorm j Fkl id z ≤ eps := by
    intro alpha
    with_unfolding_all
      exact hdata.stage_jet_of_root inp P L hr phi hphi U C0 C1 aInf
        Jinf Jbarinf alpha (e alpha) (W alpha) (PhiInf alpha)
        (rootRho alpha) (Phi3 alpha) (hroot alpha) (hread alpha)
        R hRr p eps heps
  let := Fintype.ofFinite (LiveSlot L inp.pack r)
  choose N hN using hlocal
  refine ⟨Finset.univ.sup N, ?_⟩
  intro k hk l hl alpha z hz
  let alpha' : LiveSlot L inp.pack r := by
    with_unfolding_all
      exact alpha
  have hAlpha : N alpha' ≤ Finset.univ.sup N :=
    Finset.le_sup (f := N) (Finset.mem_univ alpha')
  have hz' : z ∈ C0 alpha' := by
    with_unfolding_all
      exact hz
  with_unfolding_all
    exact hN alpha' k (hAlpha.trans hk) l (hAlpha.trans hl) z hz'

theorem HasSuppConvData.exists_stage_tail
    (inp : MetricCompactnessInputs (I := I) X)
    (aMin : Real) (haMin : 0 < aMin)
    (hphys : 8 * Real.exp inp.decay.C < aMin * inp.D)
    (h8 : (8 : Real) < inp.normalRadius.gpRatio * inp.D)
    (hradRatio : 2 * exponentialBallRadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (hstable : ∀ a b : Nat,
      (∀ᶠ k in Filter.atTop,
        BInter inp.decay inp.D P L.lamInf a b (L.φ k)) ∨
      (∀ᶠ k in Filter.atTop,
        ¬ BInter inp.decay inp.D P L.lamInf a b (L.φ k)))
    {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (hdata : HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (q : LiveSlot L inp.pack r → NNReal)
    (δ : LiveSlot L inp.pack r → Real)
    (hqdata : ∀ gamma : LiveSlot L inp.pack r,
      let rho := aMin * inp.decay.mu (L.rInf (gamma.1 : Nat) + 1)
      0 < q gamma ∧ 0 < δ gamma ∧ 0 < rho ∧
        2 * rho < (q gamma : Real))
    (hqAcc : ∀ gamma : LiveSlot L inp.pack r,
      3 * inp.normalBounds.metricC 1 * (2 * (q gamma : Real)) ^ 2 ≤
        (2 / 3 : Real) * (q gamma : Real))
    (hC1q : ∀ gamma : LiveSlot L inp.pack r,
      C1 gamma ⊆ Metric.ball 0 ((q gamma : Real) / 2))
    (hbranch : ∀ n, HasLiveBrFull (I := I) P (L.subseq hphi)
      inp.pack r n hcomplete hconn aMin q δ)
    (hscale : ∀ n (gamma : LiveSlot L inp.pack r),
      let Lphi := L.subseq hphi
      let rho := aMin * inp.decay.mu (Lphi.rInf (gamma.1 : Nat) + 1)
      let x := seqCenterD inp.decay P Lphi n (gamma.1 : Nat)
      letI : TopologicalSpace (X.obj (Lphi.φ n)).M :=
        (X.obj (Lphi.φ n)).topology
      letI : ChartedSpace H (X.obj (Lphi.φ n)).M :=
        (X.obj (Lphi.φ n)).charted
      letI : IsManifold I ∞ (X.obj (Lphi.φ n)).M :=
        (X.obj (Lphi.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (Lphi.φ n)).M) :=
        (X.obj (Lphi.φ n)).t2TangentBundle
      Metric.ball (0 : E) rho ⊆
          normalQuarter (I := I) (X.obj (Lphi.φ n)) x ∧
        rho ≤ inp.normalBounds.radius (Lphi.φ n) x ∧
        rho / 2 ≤ expRadiusGp
          (I := I) (X.obj (Lphi.φ n)).metric x)
    (deltaInf : LiveSlot L inp.pack r → Real)
    (e : LiveSlot L inp.pack r →
      Nat → OpenPartialHomeomorph (E × E) (E × E))
    (eInf : LiveSlot L inp.pack r →
      OpenPartialHomeomorph (E × E) (E × E))
    (hpair :
      let Lphi := L.subseq hphi
      let index : Nat → Nat := fun n => Lphi.φ n
      let Xphi : PointedRiemannianSeq.{u, uE, uH} (I := I) := X.subseq index
      let c : LiveSlot L inp.pack r → ∀ n : Nat, (Xphi.obj n).M :=
        fun alpha n => seqCenterD inp.decay P Lphi n (alpha.1 : Nat)
      ∀ alpha, HasDiagPairConv (I := I) (hcomplete.subseq index)
        (PointedRiemannianSeq.connected_subseq hconn index)
        (c alpha) (q alpha) (q alpha / 2) (δ alpha) (deltaInf alpha)
        (e alpha) (eInf alpha)
        (chart := c2RadiusNormalChartFamily (I := I) Xphi))
    (hfence :
      let Lphi := L.subseq hphi
      let index : Nat → Nat := fun n => Lphi.φ n
      let Xphi : PointedRiemannianSeq.{u, uE, uH} (I := I) := X.subseq index
      let c : LiveSlot L inp.pack r → ∀ n : Nat, (Xphi.obj n).M :=
        fun alpha n => seqCenterD inp.decay P Lphi n (alpha.1 : Nat)
      ∀ alpha n, NormalDiagFence (I := I) (Xphi.obj n)
        (c alpha n) (q alpha) (e alpha n)
        (c := c2RadiusNormalBallChart (I := I) (Xphi.obj n) (c alpha n))) :
    ∃ (W : LiveSlot L inp.pack r → Set E)
        (PhiInf : LiveSlot L inp.pack r → E → E)
        (rootRho : LiveSlot L inp.pack r → Real)
        (Phi3 : LiveSlot L inp.pack r → Nat → Nat → Nat → E → E),
      (∀ alpha, HasStageRootCube inp P L hr phi hphi C1 alpha
        (e alpha) (W alpha) (PhiInf alpha) (rootRho alpha) (Phi3 alpha)) ∧
      (∀ alpha,
        HasStageRootReadout inp P L hr phi hphi C0 alpha (Phi3 alpha)) ∧
      ∀ R, R < r → ∀ p eps, 0 < eps →
        HasStageJetTail inp P L hr phi hphi C0 R p eps := by
  classical
  let Lphi := L.subseq hphi
  let index : Nat → Nat := fun n => Lphi.φ n
  let Xphi : PointedRiemannianSeq.{u, uE, uH} (I := I) := X.subseq index
  let c : LiveSlot L inp.pack r → ∀ n : Nat, (Xphi.obj n).M :=
    fun alpha n => seqCenterD inp.decay P Lphi n (alpha.1 : Nat)
  dsimp only at hpair hfence
  have hcube : ∀ alpha : LiveSlot L inp.pack r,
      ∃ (W : Set E) (PhiInf : E → E) (rootRho : Real)
          (Phi3 : Nat → Nat → Nat → E → E),
        HasStageRootCube inp P L hr phi hphi C1 alpha (e alpha)
          W PhiInf rootRho Phi3 := by
    intro alpha
    exact hdata.exists_stage_cube inp P L hr phi hphi U C0 C1 aInf
      Jinf Jbarinf alpha (hpair alpha) (by simpa using hC1q alpha)
  choose W PhiInf rootRho Phi3 hroot using hcube
  have hread : ∀ alpha : LiveSlot L inp.pack r,
      HasStageRootReadout inp P L hr phi hphi C0 alpha
        (Phi3 alpha) := by
    intro alpha
    have hdiag : ∀ n, IsNormalDiag (I := I) (X.obj (Lphi.φ n))
        (hcomplete.complete (Lphi.φ n)) (hconn (Lphi.φ n))
        (seqCenterD inp.decay P Lphi n (alpha.1 : Nat))
        (q alpha) (δ alpha) (e alpha n) := by
      with_unfolding_all
        exact (hpair alpha).2.2.2.2.2.1
    have hfenceAlpha : ∀ n, NormalDiagFence (I := I)
        (X.obj (Lphi.φ n))
        (seqCenterD inp.decay P Lphi n (alpha.1 : Nat))
        (q alpha) (e alpha n) := by
      with_unfolding_all
        exact hfence alpha
    exact hdata.stage_root_tail inp aMin haMin hphys h8 hradRatio
      P L hstable hr phi hphi U C0 C1 aInf Jinf Jbarinf hcomplete hconn
      q δ hqdata hqAcc (Filter.Eventually.of_forall hbranch)
      (Filter.Eventually.of_forall hscale) alpha (e alpha) hdiag hfenceAlpha
      (W alpha) (PhiInf alpha) (rootRho alpha) (Phi3 alpha) (hroot alpha)
  refine ⟨W, PhiInf, rootRho, Phi3, hroot, hread, ?_⟩
  intro R hRr p eps heps
  exact hdata.stage_jet_tail inp P L hr phi hphi U C0 C1 aInf Jinf
    Jbarinf e W PhiInf rootRho Phi3 hroot hread R hRr p eps heps

def HasStageBaseTail
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (chart : NormalChartFamily (I := I) X :=
      c2RadiusNormalChartFamily (I := I) X) : Prop :=
  let Lphi := L.subseq hphi
  ∀ᶠ k in Filter.atTop, ∀ l,
    stageComparisonMap inp P Lphi r hr k l (chart := chart)
        (X.obj (Lphi.φ k)).basepoint =
      (X.obj (Lphi.φ l)).basepoint

theorem HasStageBaseTail.subseq
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    {phi : Nat → Nat} (hphi : StrictMono phi)
    (chart : NormalChartFamily (I := I) X :=
      c2RadiusNormalChartFamily (I := I) X)
    (h : HasStageBaseTail inp P L hr phi hphi (chart := chart))
    {ψ : Nat → Nat} (hψ : StrictMono ψ) :
    HasStageBaseTail inp P L hr (phi ∘ ψ) (hphi.comp hψ)
      (chart := chart) := by
  dsimp only [HasStageBaseTail] at h ⊢
  filter_upwards [hψ.tendsto_atTop.eventually h] with k hk
  intro l
  have hL : L.subseq (hphi.comp hψ) = (L.subseq hphi).subseq hψ := by
    cases L
    rfl
  rw [hL]
  have hmap := stageCompare_subseq (I := I) inp P (L.subseq hphi)
    r hr hψ k l (chart := chart)
  rw [congrFun hmap _]
  simpa only [NetLimitData.subseq_phi, Function.comp_apply] using hk (ψ l)

def HasStageMetricOn
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real}
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (chart : NormalChartFamily (I := I) X)
    (V C1 : LiveSlot L inp.pack r → Set E)
    (gInf : LiveSlot L inp.pack r →
      E → (E →L[Real] E →L[Real] Real)) : Prop :=
  ∀ alpha,
    let Lphi := L.subseq hphi
    C1 alpha ⊆ V alpha ∧
    ContDiffOn Real (∞ : WithTop ℕ∞) (gInf alpha) (V alpha) ∧
    MapCInfConvOnCompacts (V alpha)
      (fun n => chart.metric (Lphi.φ n)
        (seqCenterD inp.decay P Lphi n (alpha.1 : Nat)))
      (gInf alpha) ∧
    ∀ z ∈ V alpha, ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf alpha z v v ∧
        gInf alpha z v v ≤ 2 * ‖v‖ ^ 2


theorem HasStageMetricOn.subseq
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real}
    {phi : Nat → Nat} (hphi : StrictMono phi)
    (chart : NormalChartFamily (I := I) X)
    (V C1 : LiveSlot L inp.pack r → Set E)
    (gInf : LiveSlot L inp.pack r →
      E → (E →L[Real] E →L[Real] Real))
    (h : HasStageMetricOn inp P L phi hphi chart V C1 gInf)
    {ψ : Nat → Nat} (hψ : StrictMono ψ) :
    HasStageMetricOn inp P L (phi ∘ ψ) (hphi.comp hψ)
      chart V C1 gInf := by
  intro alpha
  rcases h alpha with ⟨hC1, hgInf, hconv, hequiv⟩
  refine ⟨hC1, hgInf, ?_, hequiv⟩
  simpa only [NetLimitData.subseq_phi, Function.comp_apply,
    seqCenterD_subseq] using
    hconv.comp_tendsto_atTop hψ.tendsto_atTop

def HasStageJetDataOn
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (chart : NormalChartFamily (I := I) X)
    (V U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (gInf : LiveSlot L inp.pack r →
      E → (E →L[Real] E →L[Real] Real)) : Prop :=
  HasSuppConvDataOn (I := I) inp P L r hr phi hphi chart U C0 C1
      aInf Jinf Jbarinf ∧
  HasStageMetricOn inp P L phi hphi chart V C1 gInf ∧
  (∀ R, R < r → ∀ p eps, 0 < eps →
    HasStageJetTail inp P L hr phi hphi C0 R p eps
      (chart := chart)) ∧
  HasStageBaseTail inp P L hr phi hphi (chart := chart)

theorem HasStageJetDataOn.subseq
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    {phi : Nat → Nat} (hphi : StrictMono phi)
    (chart : NormalChartFamily (I := I) X)
    (V U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (gInf : LiveSlot L inp.pack r →
      E → (E →L[Real] E →L[Real] Real))
    (h : HasStageJetDataOn (I := I) inp P L hr phi hphi chart
      V U C0 C1 aInf Jinf Jbarinf gInf)
    {ψ : Nat → Nat} (hψ : StrictMono ψ) :
    HasStageJetDataOn (I := I) inp P L hr
      (phi ∘ ψ) (hphi.comp hψ) chart
      V U C0 C1 aInf Jinf Jbarinf gInf := by
  rcases h with ⟨hdata, hmetric, hjets, hbase⟩
  refine ⟨hdata.subseq inp P L r hr hphi chart
      U C0 C1 aInf Jinf Jbarinf hψ,
    hmetric.subseq inp P L hphi chart V C1 gInf hψ,
    ?_, hbase.subseq inp P L hr hphi
      (chart := chart) (hψ := hψ)⟩
  intro R hR p eps heps
  exact (hjets R hR p eps heps).subseq inp P L hr hphi
    C0 R p eps (chart := chart) (hψ := hψ)

def HasStageJetData
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (gInf : LiveSlot L inp.pack r →
      E → (E →L[Real] E →L[Real] Real)) : Prop :=
  HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf ∧
  (∀ alpha,
    let Lphi := L.subseq hphi
    let Ralpha := L.rInf (alpha.1 : Nat) + 1
    let Ualpha := Metric.ball (0 : E)
      (inp.normalRadius.phaseRadius Ralpha)
    C1 alpha ⊆ Ualpha ∧
    ContDiffOn Real (∞ : WithTop ℕ∞) (gInf alpha) Ualpha ∧
    MapCInfConvOnCompacts Ualpha
      (fun n => normalCoordMetric (I := I)
        (X.obj (Lphi.φ n))
        (seqCenterD inp.decay P Lphi n (alpha.1 : Nat)))
      (gInf alpha) ∧
    ∀ z ∈ Ualpha, ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf alpha z v v ∧
        gInf alpha z v v ≤ 2 * ‖v‖ ^ 2) ∧
  (∀ R, R < r → ∀ p eps, 0 < eps →
    HasStageJetTail inp P L hr phi hphi C0 R p eps) ∧
  HasStageBaseTail inp P L hr phi hphi

theorem HasStageJetData.subseq
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    {phi : Nat → Nat} (hphi : StrictMono phi)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (gInf : LiveSlot L inp.pack r →
      E → (E →L[Real] E →L[Real] Real))
    (h : HasStageJetData (I := I) inp P L hr phi hphi
      U C0 C1 aInf Jinf Jbarinf gInf)
    {ψ : Nat → Nat} (hψ : StrictMono ψ) :
    HasStageJetData (I := I) inp P L hr (phi ∘ ψ) (hphi.comp hψ)
      U C0 C1 aInf Jinf Jbarinf gInf := by
  rcases h with ⟨hdata, hmetric, hjets, hbase⟩
  refine ⟨hdata.subseq inp P L r hr hphi U C0 C1 aInf Jinf Jbarinf hψ,
    ?_, ?_, hbase.subseq inp P L hr hphi (hψ := hψ)⟩
  · intro alpha
    rcases hmetric alpha with ⟨hC1, hgInf, hconv, hequiv⟩
    exact ⟨hC1, hgInf, hconv.comp_tendsto_atTop hψ.tendsto_atTop, hequiv⟩
  · intro R hR p eps heps
    exact (hjets R hR p eps heps).subseq inp P L hr hphi C0 R p eps
      (hψ := hψ)

theorem HasStageJetData.hloc_tail
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (gInf : LiveSlot L inp.pack r →
      E → (E →L[Real] E →L[Real] Real))
    (hstage : HasStageJetData (I := I) inp P L hr phi hphi
      U C0 C1 aInf Jinf Jbarinf gInf)
    (R : Real) (hRr : R < r) :
    ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N,
      let Lphi := L.subseq hphi
      let Yk := X.obj (Lphi.φ k)
      let Yl := X.obj (Lphi.φ l)
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
      IsLocalDiffeomorphOn I I (∞ : WithTop ℕ∞)
        (stageComparisonMap inp P Lphi r hr k l)
        (Lphi.hatSourceBall inp.decay P R k) := by
  classical
  rcases hstage with ⟨hdata, _hmetric, hjets, _hbase⟩
  let Rmid := (R + r) / 2
  have hRmid : R < Rmid := by
    dsimp only [Rmid]
    linarith
  have hmidr : Rmid < r := by
    dsimp only [Rmid]
    linarith
  obtain ⟨N, hN⟩ := hjets Rmid hmidr 1 (1 / 2 : Real) (by norm_num)
  refine ⟨N, ?_⟩
  intro k hk l hl
  dsimp only
  let Lphi := L.subseq hphi
  let Yk := X.obj (Lphi.φ k)
  let Yl := X.obj (Lphi.φ l)
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
  let F := stageComparisonMap inp P Lphi r hr k l
  rintro ⟨x, hx⟩
  have hxLarge : x ∈ Lphi.hatSourceBall inp.decay P r k := by
    let : MetricSpace Yk.M := (P (Lphi.φ k)).ms
    exact cball_subset_of_le hRr.le
      (by simpa only [NetLimitData.hatSourceBall, Yk] using hx)
  have hcover := hdata.source_cover inp P L r hr U C0 C1 aInf
    Jinf Jbarinf k
  obtain ⟨alpha, z, hzInt, hzx⟩ :=
    Set.mem_iUnion.mp (hcover hxLarge)
  let xk0 := seqCenterD inp.decay P Lphi k (alpha.1 : Nat)
  let xl0 := seqCenterD inp.decay P Lphi l (alpha.1 : Nat)
  let chiK := NormalCoordinates.normalChartAt (I := I) Yk.metric xk0
  let chiL := NormalCoordinates.normalChartAt (I := I) Yl.metric xl0
  have hxEq : chiK.symm z = x := by
    with_unfolding_all
      exact hzx
  obtain ⟨_hUopen, _hC0, _hC1, hC01, hC1U⟩ :=
    hdata.core_on inp P L r hr U C0 C1 aInf Jinf Jbarinf alpha
  obtain ⟨_hRad, hExp, _hMaps⟩ :=
    hdata.geom_on inp P L r hr U C0 C1 aInf Jinf Jbarinf k alpha
  have hzC0 : z ∈ C0 alpha := interior_subset hzInt
  have hzU : z ∈ U alpha :=
    hC1U (interior_subset (hC01 hzC0))
  have hzBall := hExp hzU
  have hzNormal : z ∈
      Metric.ball 0 (expMapC2Radius (I := I) Yk.metric xk0) := by
    simpa only [Yk, xk0, Lphi, NetLimitData.subseq_phi,
      Function.comp_apply, seqCenterD_subseq, NormalChartFamily.radius,
      c2RadiusNormalChartFamily, c2_radius_normal_ball_chart_radius] using hzBall
  have hzTarget : z ∈ chiK.target := by
    have hzNorm : ‖z‖ < expMapC2Radius (I := I) Yk.metric xk0 := by
      simpa only [Metric.mem_ball, dist_zero_right] using hzNormal
    exact ball_subset_normalChartAt_target (I := I) Yk.metric xk0 hzNorm
  let c := (normalExpPD (I := I) Yk xk0).symm
  let d := (normalExpPD (I := I) Yl xl0).symm
  have hzSource : z ∈ (normalExpPD (I := I) Yk xk0).source := by
    rw [normalExpPD_source]
    change z ∈ Metric.ball 0 (expMapC2Radius (I := I) Yk.metric xk0)
    exact hzNormal
  have hnormalEq : normalExpPD (I := I) Yk xk0 z = x := by
    with_unfolding_all
      exact hxEq
  have hxc : x ∈ c.source := by
    have hout := (normalExpPD (I := I) Yk xk0).map_source hzSource
    rw [hnormalEq] at hout
    with_unfolding_all
      exact hout
  have hcx : c x = z := by
    have hout := (normalExpPD (I := I) Yk xk0).left_inv hzSource
    rw [hnormalEq] at hout
    with_unfolding_all
      exact hout
  let Bmid : Set Yk.M :=
    letI : MetricSpace Yk.M := (P (Lphi.φ k)).ms
    Metric.ball Yk.basepoint Rmid
  have hBopen : IsOpen Bmid := by
    have hb :
        @IsOpen Yk.M
          (P (Lphi.φ k)).ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
          Bmid := by
      let : MetricSpace Yk.M := (P (Lphi.φ k)).ms
      exact Metric.isOpen_ball
    rw [ProperMetricOn.top_eq Yk (P (Lphi.φ k))] at hb
    exact hb
  let V : Set E :=
    interior (C0 alpha) ∩ (chiK.target ∩ chiK.symm ⁻¹' Bmid)
  have hV : IsOpen V := by
    dsimp only [V]
    exact isOpen_interior.inter
      (chiK.toOpenPartialHomeomorph.continuousOn_invFun.isOpen_inter_preimage
        chiK.open_target hBopen)
  have hxBmid : x ∈ Bmid := by
    let : MetricSpace Yk.M := (P (Lphi.φ k)).ms
    exact Metric.closedBall_subset_ball hRmid
      (by simpa only [Bmid, NetLimitData.hatSourceBall, Yk] using hx)
  have hcxV : c x ∈ V := by
    rw [hcx]
    refine ⟨hzInt, hzTarget, ?_⟩
    change chiK.symm z ∈ Bmid
    rw [hxEq]
    exact hxBmid
  have hjetAt (w : E) (hw : w ∈ V) :
      stageComparisonMap inp P Lphi r hr k l (chiK.symm w) ∈
          (normalExpPD (I := I) Yl xl0).target ∧
        ContDiffAt Real ∞
          (fun u => chiL
            (stageComparisonMap inp P Lphi r hr k l (chiK.symm u))) w ∧
        ∀ j ≤ 1,
          mapDerivNorm j
            (fun u => chiL
              (stageComparisonMap inp P Lphi r hr k l (chiK.symm u)))
            id w ≤ (1 / 2 : Real) := by
    have hwMid : chiK.symm w ∈
        Lphi.hatSourceBall inp.decay P Rmid k := by
      let : MetricSpace Yk.M := (P (Lphi.φ k)).ms
      have hwB : chiK.symm w ∈ Bmid := hw.2.2
      change chiK.symm w ∈ Metric.closedBall Yk.basepoint Rmid
      apply Metric.ball_subset_closedBall
      simpa only [Bmid] using hwB
    with_unfolding_all
      exact hN k hk l hl alpha w (interior_subset hw.1) hw.1 hwMid
  have hmap : Set.MapsTo (fun w => F (c.symm w)) V d.source := by
    intro w hw
    have hout := (hjetAt w hw).1
    with_unfolding_all
      exact hout
  have hG : ContDiffOn Real ∞ (fun w => d (F (c.symm w))) V := by
    intro w hw
    have hout := (hjetAt w hw).2.1
    have hout' : ContDiffAt Real ∞ (fun u => d (F (c.symm u))) w := by
      with_unfolding_all
        exact hout
    exact hout'.contDiffWithinAt
  have hinv : ∀ w ∈ V,
      (fderiv Real (fun u => d (F (c.symm u))) w).IsInvertible := by
    intro w hw
    have hcd := (hjetAt w hw).2.1
    have hdiff : DifferentiableAt Real
        (fun u => chiL
          (stageComparisonMap inp P Lphi r hr k l (chiK.symm u))) w :=
      hcd.differentiableAt (by simp)
    have hneu := neumannOfDerivNorm hdiff ((hjetAt w hw).2.2 1 le_rfl)
    have hlt :
        ‖ContinuousLinearMap.id Real E -
          fderiv Real
            (fun u => chiL
              (stageComparisonMap inp P Lphi r hr k l (chiK.symm u))) w‖ <
            1 :=
      hneu.trans_lt (by norm_num)
    have hout := Coordinates.isInvertible_of_norm_id_sub_lt hlt
    with_unfolding_all
      exact hout
  exact Coordinates.isLocalDiffeomorphAt_of_coordinates c d hV hxc hcxV hmap hG hinv

theorem MetricCompactBase.exists_stage_data
    (b : MetricCompactBase (I := I) X)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (r : Real) (hr : 0 ≤ r) :
    ∃ (inp : MetricCompactnessInputs (I := I) X)
        (L : NetLimitData inp.decay inp.D
          (properMetricsOfCompleteConnected (I := I) hcomplete hconn))
        (phi : Nat → Nat) (hphi : StrictMono phi)
        (U : LiveSlot L inp.pack r → Set E)
        (C0 C1 : LiveSlot L inp.pack r → Set E)
        (aInf : (alpha : LiveSlot L inp.pack r) →
          Fin (inp.pack.A r) → E → Real)
        (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
          InterSlot L inp.pack r alpha → E → E)
        (gInf : LiveSlot L inp.pack r →
          E → (E →L[Real] E →L[Real] Real)),
      let P := properMetricsOfCompleteConnected (I := I) hcomplete hconn
      HasStageJetData inp P L hr phi hphi U C0 C1
        aInf Jinf Jbarinf gInf := by
  classical
  obtain ⟨aMin, haMin, inp, L, phi, hphi, U, C0, C1, aInf, Jinf,
      Jbarinf, q, δ, gInf, deltaInf, e, eInf, hAll⟩ :=
    b.exists_supp_diag_fin hcomplete hconn r hr
  let P := properMetricsOfCompleteConnected (I := I) hcomplete hconn
  dsimp only at hAll
  obtain ⟨hdata, hAll⟩ := hAll
  obtain ⟨hstable, hAll⟩ := hAll
  obtain ⟨hphys, hAll⟩ := hAll
  obtain ⟨h8, hAll⟩ := hAll
  obtain ⟨_hradD, hAll⟩ := hAll
  obtain ⟨hradRatio, hAll⟩ := hAll
  obtain ⟨hqdata, hAll⟩ := hAll
  obtain ⟨hqWide, hAll⟩ := hAll
  obtain ⟨hqAcc, hAll⟩ := hAll
  obtain ⟨_herr, hAll⟩ := hAll
  obtain ⟨_hinvErr, hAll⟩ := hAll
  obtain ⟨hC1q, hAll⟩ := hAll
  obtain ⟨_hcenter, hAll⟩ := hAll
  obtain ⟨hmetric, hAll⟩ := hAll
  obtain ⟨hbranch, hAll⟩ := hAll
  obtain ⟨hscale, hAll⟩ := hAll
  obtain ⟨hpairFence, _hcap⟩ := hAll
  obtain ⟨W, PhiInf, rootRho, Phi3, hroot, hread, hjet⟩ :=
    hdata.exists_stage_tail inp aMin haMin hphys h8 hradRatio
      P L hstable hr phi hphi U C0 C1 aInf Jinf Jbarinf hcomplete hconn
      q δ hqdata hqAcc hC1q hbranch hscale deltaInf e eInf
      (fun alpha => (hpairFence alpha).1)
      (fun alpha n => (hpairFence alpha).2 n)
  obtain ⟨hgp, _hrad⟩ :=
    inp.exponential_scale_tails h8 hradRatio P L r
  have hgpPhi : ExponentialRadiusScaleTail (I := I) inp.decay inp.D P
      (L.subseq hphi) inp.pack r :=
    hgp.subseq inp.decay inp.D P L inp.pack r hphi
  have hbase : HasStageBaseTail (I := I) inp P L hr phi hphi := by
    dsimp only [HasStageBaseTail]
    filter_upwards [hgpPhi] with k hk
    intro l
    exact stageCompare_base inp P (L.subseq hphi) r hr k l
  have hmetric' : ∀ alpha : LiveSlot L inp.pack r,
      let Ralpha := L.rInf (alpha.1 : Nat) + 1
      let Ualpha := Metric.ball (0 : E)
        (inp.normalRadius.phaseRadius Ralpha)
      C1 alpha ⊆ Ualpha ∧
      ContDiffOn Real (∞ : WithTop ℕ∞) (gInf alpha) Ualpha ∧
      MapCInfConvOnCompacts Ualpha
        (fun n => normalCoordMetric (I := I)
          (X.obj ((L.subseq hphi).φ n))
          (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)))
        (gInf alpha) ∧
      ∀ z ∈ Ualpha, ∀ v : E,
        (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf alpha z v v ∧
          gInf alpha z v v ≤ 2 * ‖v‖ ^ 2 := by
    intro alpha
    dsimp only
    refine ⟨?_, hmetric alpha⟩
    have hqPos : 0 < (q alpha : Real) := by
      exact_mod_cast (hqdata alpha).1
    have hhalfSix : (q alpha : Real) / 2 < 6 * (q alpha : Real) := by
      linarith
    have hhalfPhase : (q alpha : Real) / 2 <
        inp.normalRadius.phaseRadius (L.rInf (alpha.1 : Nat) + 1) :=
      hhalfSix.trans (hqWide alpha)
    exact (hC1q alpha).trans (Metric.ball_subset_ball hhalfPhase.le)
  refine ⟨inp, L, phi, hphi, U, C0, C1, aInf, Jinf, Jbarinf, gInf, ?_⟩
  dsimp only [HasStageJetData]
  exact ⟨hdata, hmetric', hjet, hbase⟩

end HCGCompactness
end DifferentialGeometry
