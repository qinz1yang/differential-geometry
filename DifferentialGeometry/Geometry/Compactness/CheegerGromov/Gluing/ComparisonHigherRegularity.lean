import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.CenterMapHigherRegularity



import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.LiveScale
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.MetricSequence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.Diagonal

set_option autoImplicit false

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

namespace BoundedGeometryNormalData

theorem stage_root_tail
    (inp : MetricCompactCore (I := I) X)
    (d : BoundedGeometryNormalData (I := I) X inp.decay)
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
    (e : Nat → OpenPartialHomeomorph (E × E) (E × E))
    (hdiag :
      let Lphi := L.subseq hphi
      ∀ n, IsNormalDiag (I := I) (X.obj (Lphi.φ n))
        (hcomplete.complete (Lphi.φ n)) (hconn (Lphi.φ n))
        (seqCenterD inp.decay P Lphi n (alpha.1 : Nat))
        (q alpha) (δ alpha) (e n)
        (c := d.chart (Lphi.φ n)
          (seqCenterD inp.decay P Lphi n (alpha.1 : Nat))))
    (hfence :
      let Lphi := L.subseq hphi
      ∀ n, NormalDiagFence (I := I) (X.obj (Lphi.φ n))
        (seqCenterD inp.decay P Lphi n (alpha.1 : Nat))
        (q alpha) (e n)
        (c := d.chart (Lphi.φ n)
          (seqCenterD inp.decay P Lphi n (alpha.1 : Nat))))
    (W : Set E) (PhiInf : E → E) (rootRho : Real)
    (Phi3 : Nat → Nat → Nat → E → E)
    (hroot : HasStageRootCube inp P L hr phi hphi C1 alpha e
      W PhiInf rootRho Phi3 (chart := d.chart)) :
    HasStageRootReadout inp P L hr phi hphi C0 alpha Phi3
      (chart := d.chart) := by
  dsimp only [HasStageRootReadout]
  rcases hroot with
    ⟨_hW, _hWcpt, hC1W, hrootRho, hPhiInf, _htriple,
      Nroot, hrootTail⟩
  have heps : 0 < rootRho / 4 := by positivity
  obtain ⟨rad, hrad, hradSmall, Ncm, hcmTail⟩ :=
    d.actual_cm_tail inp aMin haMin hphys P L hr phi hphi
      U C0 C1 aInf Jinf Jbarinf hdata hcomplete hconn q δ
      hqdata hbranch alpha (rootRho / 4) heps
  obtain ⟨Ntgt, htgtTail⟩ :=
    d.pts_target_tail inp aMin haMin hphys P L hstable hr
      phi hphi U C0 C1 aInf Jinf Jbarinf hdata hcomplete hconn
      q δ hqdata
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
      (fun y : Yl.M ↦ TangentSpace I y) :=
    Yl.riemBundle_cont (I := I)
  letI : EMetricSpace Yl.M := Yl.emetricSpace (I := I)
  letI : CompleteSpace Yl.M :=
    MetricComplete.complete (I := I) Yl (hcomplete.complete (Lphi.φ l))
  letI : MetricSpace Yl.M :=
    HopfRinow.riemMetricSpace (I := I) (M := Yl.M)
  let chiK := d.chart (Lphi.φ k)
    (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
  let chiL := d.chart (Lphi.φ l)
    (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
  let mu := stageWeightSub inp P L hr phi hphi alpha k
    (chart := d.chart)
  let stagePts := fun w gamma =>
    chiL.hom (stagePtsSub inp P L phi hphi alpha k l w gamma
      (chart := d.chart))
  let qstar := chiL.hom
  let p := qstar z
  let x0 := seqCenterD inp.decay P Lphi l (alpha.1 : Nat)
  let join := minJoin (I := I) Yl.metric (normal_enorm (I := I) Yl)
  let pts := centerAverage.activeFill mu stagePts qstar z
  have hcmOut := hcmTail k hkCm l hlCm z hz
  dsimp only at hcmOut
  rcases hcmOut with ⟨hcm, hstrict, hcoord⟩
  let c := centerOfMass (I := I) Yl.metric (mu z) pts join p rad hcm
  let zc := chiL.inv c
  let xi : Fin (inp.pack.A r) → E := fun i => chiL.inv (pts i)
  have hzcClose : dist zc z < rootRho := by
    have hfour : 4 * rad < rootRho := by nlinarith [hradSmall]
    have hcoordLe : dist zc z ≤ 4 * rad := by
      simpa only [zc, c, mu, pts, join, p, qstar, stagePts, chiL] using
        hcoord
    exact hcoordLe.trans_lt hfour
  dsimp only [HasLiveChartCenterSolution, HasChartCmSol] at hstrict
  rcases hstrict with ⟨hqSel, eSel, heSel, hfSel, hread⟩
  rcases hread with ⟨hcTarget, hsol⟩
  let chartSel := chiL
  have hsolSel : HasCmSolC (I := I) Yl.metric
      (normal_enorm (I := I) Yl) x0 chartSel
      (IsNormalDiag.toBranch (I := I) Yl
        (hcomplete.complete (Lphi.φ l)) (hconn (Lphi.φ l))
        x0 hqSel heSel) zc (mu z, xi) := by
    simpa only [chartSel, zc, xi, c, x0, Yl, Lphi, mu, pts,
      join, p, chiL] using hsol
  have htgtSel : ∀ i, (zc, xi i) ∈ eSel.target := by
    intro i
    have hzcTarget : chartSel.hom zc ∈ chartSel.restrictBall.target := by
      have hmap := chartSel.restrictBall.map_source hsolSel.1
      change chartSel.hom zc ∈ chartSel.restrictBall.target at hmap
      exact hmap
    have hxiTarget :
        chartSel.hom (xi i) ∈ chartSel.restrictBall.target := by
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
    have hout' :
        (chartSel.inv (chartSel.hom zc),
          chartSel.inv (chartSel.hom (xi i))) ∈ eSel.target := by
      simpa only [chartSel, chiL, Lphi, NetLimitData.subseq,
        Function.comp_apply, seqCenterD_subseq] using hout
    rwa [hzcDecode, hxiDecode] at hout'
  have hselZero : invVelSum eSel (mu z) xi zc = 0 :=
    (IsNormalDiag.chartCmC_zero_iff (I := I) Yl
      (hcomplete.complete (Lphi.φ l)) (hconn (Lphi.φ l))
      x0 hqSel heSel hfSel zc (mu z) xi htgtSel).mp
        hsolSel.2.2.2.1
  have heCanon : IsNormalDiag (I := I) Yl
      (hcomplete.complete (Lphi.φ l)) (hconn (Lphi.φ l)) x0
      (q alpha) (δ alpha) (e l) (c := chiL) := by
    simpa only [Lphi, Yl, x0, chiL] using hdiag l
  have hfCanon : NormalDiagFence (I := I) Yl x0
      (q alpha) (e l) (c := chiL) := by
    simpa only [Lphi, Yl, x0, chiL] using hfence l
  have heq : e l ≈ eSel :=
    IsNormalDiag.eqOnSource (I := I) Yl
      (hcomplete.complete (Lphi.φ l)) (hconn (Lphi.φ l)) x0
      heCanon hfCanon heSel hfSel
  have hcanonXiZero : invVelSum (e l) (mu z) xi zc = 0 := by
    calc
      invVelSum (e l) (mu z) xi zc =
          invVelSum eSel (mu z) xi zc :=
        (invVelSum_congr_br eSel (e l) (mu z) xi zc
          (Setoid.symm heq)
          (fun i _hne => by
            simpa only [zc, xi, c, mu, pts, join, p] using
              htgtSel i)).symm
      _ = 0 := hselZero
  obtain ⟨_hU, _hC0, _hC1, hC01, hC1U⟩ :=
    hdata.core_on inp P L r hr d.chart U C0 C1 aInf Jinf Jbarinf
      alpha
  have hzU : z ∈ U alpha :=
    hC1U (interior_subset (hC01 hz))
  have hxi : ∀ i, mu z i ≠ 0 →
      xi i = stagePtsSub inp P L phi hphi alpha k l z i
        (chart := d.chart) := by
    intro i hi
    have hdecode :=
      htgtTail k hkTgt l hlTgt alpha z hzU i hi
    dsimp only at hdecode
    dsimp only [xi, pts]
    simp only [centerAverage.activeFill, hi, ↓reduceIte]
    change chiL.inv
      (chiL.hom
        (stagePtsSub inp P L phi hphi alpha k l z i
          (chart := d.chart))) =
      stagePtsSub inp P L phi hphi alpha k l z i
        (chart := d.chart)
    rw [hdecode.1]
    exact hdecode.2
  have hcanonPtsZero : invVelSum (e l) (mu z)
      (stagePtsSub inp P L phi hphi alpha k l z
        (chart := d.chart)) zc = 0 := by
    calc
      invVelSum (e l) (mu z)
          (stagePtsSub inp P L phi hphi alpha k l z
            (chart := d.chart)) zc =
          invVelSum (e l) (mu z) xi zc :=
        (invVelSum_congr_ne (e l) (mu z) xi
          (stagePtsSub inp P L phi hphi alpha k l z
            (chart := d.chart)) zc hxi).symm
      _ = 0 := hcanonXiZero
  have hstageZero : stageInvVelSub inp P L hr phi hphi alpha e
      l k l (z, zc) (chart := d.chart) = 0 := by
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
  let x : Yk.M := chiK.hom z
  let i0 := baseIndex inp.decay inp.realizes inp.pack hr
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
    simpa only [muM, x, mu, i0, Lphi, Yk, chiK] using
      (stageWeightSub_eq (I := I) inp P L hr phi hphi alpha k z gamma
        (chart := d.chart)).symm
  have hptsEq : centerAverage.activeFill muM
      (stageTarget inp P Lphi r k l (chart := d.chart))
      qstarM x = pts := by
    dsimp only [pts]
    funext gamma
    simp only [centerAverage.activeFill]
    rw [congrFun hmu gamma]
    by_cases hi : mu z gamma = 0
    · simp only [hi, ↓reduceIte, qstarM, qstar, p]
    · simp only [hi, ↓reduceIte]
      have hdecode :=
        htgtTail k hkTgt l hlTgt alpha z hzU gamma hi
      dsimp only at hdecode
      simpa only [x, stagePts, chiK, Lphi] using hdecode.1.symm
  have hcmM : CenterInput (I := I) Yl.metric (muM x)
      (centerAverage.activeFill muM
        (stageTarget inp P Lphi r k l (chart := d.chart))
        qstarM x) join (pM x) (radM x) := by
    rw [hmu, hptsEq]
    simpa only [pM, radM] using hcm
  have hmap := stageCompare_eq_cm (I := I) inp P Lphi r hr hconn
    k l qstarM join pM radM x hx (chart := d.chart) hcmM
  have hcGlobal : c = centerOfMass (I := I) Yl.metric (muM x)
      (centerAverage.activeFill muM
        (stageTarget inp P Lphi r k l (chart := d.chart))
        qstarM x) join (pM x) (radM x) hcmM := by
    apply centerOfMass.unique hcmM c
    intro y
    rw [hmu, hptsEq]
    simpa only [c] using centerOfMass.min hcm y
  have hmapC :
      stageComparisonMap inp P Lphi r hr k l x
          (chart := d.chart) = c :=
    hmap.trans hcGlobal.symm
  have hchartReadout :
      chiL.inv
          (stageComparisonMap inp P Lphi r hr k l x
            (chart := d.chart)) =
        Phi3 l k l z := by
    rw [hmapC]
    exact hcenterRoot
  have hrootBall : Phi3 l k l z ∈ Metric.ball 0 chiL.radius := by
    rw [← hcenterRoot]
    simpa only [zc, x0, chartSel, chiL] using hsolSel.1
  have hdecode : chiL.hom zc = c := by
    have hright := chiL.restrictBall.right_inv hcTarget
    simpa only [
      Geometry.Riemannian.NormalCoordinates.NormalBallChart.restrictBall_apply,
      zc, c, chiL] using hright
  have hmapDecode :
      stageComparisonMap inp P Lphi r hr k l x
          (chart := d.chart) =
        chiL.hom (Phi3 l k l z) := by
    calc
      stageComparisonMap inp P Lphi r hr k l x
          (chart := d.chart) = c := hmapC
      _ = chiL.hom zc := hdecode.symm
      _ = chiL.hom (Phi3 l k l z) :=
        congrArg chiL.hom hcenterRoot
  have htarget :
      stageComparisonMap inp P Lphi r hr k l x
          (chart := d.chart) ∈ chiL.hom.target := by
    rw [hmapDecode]
    exact chiL.hom.map_source (chiL.ball_subset hrootBall)
  exact ⟨hchartReadout, hrootBall, hmapDecode, htarget⟩

end BoundedGeometryNormalData

theorem HasSuppConvDataOn.stage_jet_of_root
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (chart : NormalChartFamily (I := I) X)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (hdata : HasSuppConvDataOn (I := I) inp P L r hr phi hphi chart
      U C0 C1 aInf Jinf Jbarinf)
    (alpha : LiveSlot L inp.pack r)
    (e : Nat → OpenPartialHomeomorph (E × E) (E × E))
    (W : Set E) (PhiInf : E → E) (rootRho : Real)
    (Phi3 : Nat → Nat → Nat → E → E)
    (hroot : HasStageRootCube inp P L hr phi hphi C1 alpha e
      W PhiInf rootRho Phi3 (chart := chart))
    (hread : HasStageRootReadout inp P L hr phi hphi C0 alpha Phi3
      (chart := chart))
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
          ∀ j ≤ p, mapDerivNorm j Fkl id z ≤ eps := by
  obtain ⟨_hU, hC0, _hC1, hC01, hC1U⟩ :=
    hdata.core_on inp P L r hr chart U C0 C1 aInf Jinf Jbarinf alpha
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
    let chiK := chart (Lphi.φ k)
      (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
    let chiL := chart (Lphi.φ l)
      (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
    fun w => chiL.inv
      (stageComparisonMap inp P Lphi r hr k l
        (chiK.hom w) (chart := chart))
  let S : Nat → E → Prop := fun k z =>
    let Yk := X.obj (Lphi.φ k)
    letI : TopologicalSpace Yk.M := Yk.topology
    letI : ChartedSpace H Yk.M := Yk.charted
    letI : IsManifold I ∞ Yk.M := Yk.smooth
    letI : T2Space Yk.M := Yk.t2
    letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
    let chiK := chart (Lphi.φ k)
      (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
    z ∈ interior (C0 alpha) ∧
      chiK.hom z ∈ Lphi.hatSourceBall inp.decay P R k
  dsimp only [HasStageRootReadout] at hread
  obtain ⟨Nread, hreadTail⟩ := hread
  have hEq : ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N, ∀ z ∈ C0 alpha,
      S k z → Psi k l =ᶠ[nhds z] Phi3 l k l := by
    refine ⟨Nread, ?_⟩
    intro k hk l hl z _hz hSz
    let Yk := X.obj (Lphi.φ k)
    let Yl := X.obj (Lphi.φ l)
    letI : TopologicalSpace Yk.M := Yk.topology
    letI : ChartedSpace H Yk.M := Yk.charted
    letI : IsManifold I ∞ Yk.M := Yk.smooth
    letI : T2Space Yk.M := Yk.t2
    letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
    letI : MetricSpace Yk.M := (P (Lphi.φ k)).ms
    letI : TopologicalSpace Yl.M := Yl.topology
    letI : ChartedSpace H Yl.M := Yl.charted
    letI : IsManifold I ∞ Yl.M := Yl.smooth
    letI : T2Space Yl.M := Yl.t2
    letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
    let chiK := chart (Lphi.φ k)
      (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
    let chiL := chart (Lphi.φ l)
      (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
    change z ∈ interior (C0 alpha) ∧
      chiK.hom z ∈ Lphi.hatSourceBall inp.decay P R k at hSz
    have hzU : z ∈ U alpha :=
      hC1U (interior_subset (hC01 (interior_subset hSz.1)))
    obtain ⟨hRad, _hMaps⟩ :=
      hdata.geom_on inp P L r hr chart U C0 C1 aInf Jinf Jbarinf k alpha
    have hzBall : z ∈ Metric.ball 0 chiK.radius := hRad hzU
    have hchi : ContinuousAt chiK.hom z :=
      chiK.smooth_to.continuousOn.continuousAt
        (Metric.isOpen_ball.mem_nhds hzBall)
    have hbigNhd : Lphi.hatSourceBall inp.decay P r k ∈
        nhds (chiK.hom z) :=
      NetLimitData.hatSource_nhds (I := I) (X := X) inp.decay P Lphi
        (n := k) (R := R) (s := r) hRr hSz.2
    have hsource : ∀ᶠ y in nhds z,
        chiK.hom y ∈ Lphi.hatSourceBall inp.decay P r k :=
      hchi.eventually hbigNhd
    have hreadKL := hreadTail k hk l hl
    change (fun w => chiL.inv
      (stageComparisonMap inp P Lphi r hr k l
        (chiK.hom w) (chart := chart))) =ᶠ[nhds z] Phi3 l k l
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
  letI : TopologicalSpace Yk.M := Yk.topology
  letI : ChartedSpace H Yk.M := Yk.charted
  letI : IsManifold I ∞ Yk.M := Yk.smooth
  letI : T2Space Yk.M := Yk.t2
  letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
  let chiK := chart (Lphi.φ k)
    (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
  let Yl := X.obj (Lphi.φ l)
  letI : TopologicalSpace Yl.M := Yl.topology
  letI : ChartedSpace H Yl.M := Yl.charted
  letI : IsManifold I ∞ Yl.M := Yl.smooth
  letI : T2Space Yl.M := Yl.t2
  letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
  let chiL := chart (Lphi.φ l)
    (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
  have hxBig : chiK.hom z ∈ Lphi.hatSourceBall inp.decay P r k :=
    mem_of_mem_nhds (NetLimitData.hatSource_nhds
      (I := I) (X := X) inp.decay P Lphi
      (n := k) (R := R) (s := r) hRr hxR)
  have hreadAt := hreadTail k hkRead l hlRead z hz hxBig
  have htarget :
      stageComparisonMap inp P Lphi r hr k l
          (chiK.hom z) (chart := chart) ∈ chiL.restrictBall.target := by
    rw [hreadAt.2.2.1]
    exact chiL.restrictBall.map_source hreadAt.2.1
  refine ⟨htarget, ?_⟩
  simpa only [Psi] using hout

theorem HasSuppConvDataOn.stage_jet_tail
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (chart : NormalChartFamily (I := I) X)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (hdata : HasSuppConvDataOn (I := I) inp P L r hr phi hphi chart
      U C0 C1 aInf Jinf Jbarinf)
    (e : (alpha : LiveSlot L inp.pack r) →
      Nat → OpenPartialHomeomorph (E × E) (E × E))
    (W : LiveSlot L inp.pack r → Set E)
    (PhiInf : LiveSlot L inp.pack r → E → E)
    (rootRho : LiveSlot L inp.pack r → Real)
    (Phi3 : LiveSlot L inp.pack r → Nat → Nat → Nat → E → E)
    (hroot : ∀ alpha, HasStageRootCube inp P L hr phi hphi C1 alpha
      (e alpha) (W alpha) (PhiInf alpha) (rootRho alpha) (Phi3 alpha)
      (chart := chart))
    (hread : ∀ alpha,
      HasStageRootReadout inp P L hr phi hphi C0 alpha
        (Phi3 alpha) (chart := chart))
    (R : Real) (hRr : R < r)
    (p : Nat) (eps : Real) (heps : 0 < eps) :
    HasStageJetTail inp P L hr phi hphi C0 R p eps
      (chart := chart) := by
  classical
  dsimp only [HasStageJetTail]
  have hlocal := fun alpha : LiveSlot L inp.pack r =>
    hdata.stage_jet_of_root inp P L hr phi hphi chart U C0 C1
      aInf Jinf Jbarinf alpha (e alpha) (W alpha)
      (PhiInf alpha) (rootRho alpha) (Phi3 alpha) (hroot alpha)
      (hread alpha) R hRr p eps heps
  letI := Fintype.ofFinite (LiveSlot L inp.pack r)
  choose N hN using hlocal
  refine ⟨Finset.univ.sup N, ?_⟩
  intro k hk l hl alpha z hz
  have hAlpha : N alpha ≤ Finset.univ.sup N :=
    Finset.le_sup (f := N) (Finset.mem_univ alpha)
  exact hN alpha k (hAlpha.trans hk) l (hAlpha.trans hl) z hz

namespace BoundedGeometryNormalData

theorem stage_jet_tail
    (inp : MetricCompactCore (I := I) X)
    (d : BoundedGeometryNormalData (I := I) X inp.decay)
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
    (e : (alpha : LiveSlot L inp.pack r) →
      Nat → OpenPartialHomeomorph (E × E) (E × E))
    (hdiag : ∀ alpha,
      let Lphi := L.subseq hphi
      ∀ n, IsNormalDiag (I := I) (X.obj (Lphi.φ n))
        (hcomplete.complete (Lphi.φ n)) (hconn (Lphi.φ n))
        (seqCenterD inp.decay P Lphi n (alpha.1 : Nat))
        (q alpha) (δ alpha) (e alpha n)
        (c := d.chart (Lphi.φ n)
          (seqCenterD inp.decay P Lphi n (alpha.1 : Nat))))
    (hfence : ∀ alpha,
      let Lphi := L.subseq hphi
      ∀ n, NormalDiagFence (I := I) (X.obj (Lphi.φ n))
        (seqCenterD inp.decay P Lphi n (alpha.1 : Nat))
        (q alpha) (e alpha n)
        (c := d.chart (Lphi.φ n)
          (seqCenterD inp.decay P Lphi n (alpha.1 : Nat))))
    (W : LiveSlot L inp.pack r → Set E)
    (PhiInf : LiveSlot L inp.pack r → E → E)
    (rootRho : LiveSlot L inp.pack r → Real)
    (Phi3 : LiveSlot L inp.pack r → Nat → Nat → Nat → E → E)
    (hroot : ∀ alpha, HasStageRootCube inp P L hr phi hphi C1 alpha
      (e alpha) (W alpha) (PhiInf alpha) (rootRho alpha) (Phi3 alpha)
      (chart := d.chart))
    (R : Real) (hRr : R < r)
    (p : Nat) (eps : Real) (heps : 0 < eps) :
    HasStageJetTail inp P L hr phi hphi C0 R p eps
      (chart := d.chart) := by
  apply hdata.stage_jet_tail inp P L hr phi hphi d.chart U C0 C1
    aInf Jinf Jbarinf e W PhiInf rootRho Phi3 hroot
  · intro alpha
    exact d.stage_root_tail inp aMin haMin hphys P L hstable hr
      phi hphi U C0 C1 aInf Jinf Jbarinf hdata hcomplete hconn
      q δ hqdata hbranch alpha (e alpha) (hdiag alpha) (hfence alpha)
      (W alpha) (PhiInf alpha) (rootRho alpha) (Phi3 alpha)
      (hroot alpha)
  · exact hRr
  · exact heps

theorem stage_base_tail
    (inp : MetricCompactCore (I := I) X)
    (d : BoundedGeometryNormalData (I := I) X inp.decay)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi) :
    HasStageBaseTail inp P L hr phi hphi (chart := d.chart) := by
  dsimp only [HasStageBaseTail]
  exact Filter.Eventually.of_forall fun k l =>
    stageCmp_base_raw inp P (L.subseq hphi) r hr k l
      (chart := d.chart)

theorem exists_supp_base
    (inp : MetricCompactCore (I := I) X)
    (d : BoundedGeometryNormalData (I := I) X inp.decay)
    (aMin : Real)
    (hphys : 8 * Real.exp inp.decay.C < aMin * inp.D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (hstable : ∀ a b : Nat,
      (∀ᶠ k in Filter.atTop,
        BInter inp.decay inp.D P L.lamInf a b (L.φ k)) ∨
      (∀ᶠ k in Filter.atTop,
        ¬ BInter inp.decay inp.D P L.lamInf a b (L.φ k)))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (r : Real) (hr : 0 ≤ r)
    (hratio : 48 * aMin < d.ratio) :
    ∃ (phi : Nat → Nat) (hphi : StrictMono phi)
        (U C0 C1 : LiveSlot L inp.pack r → Set E)
        (aInf : (alpha : LiveSlot L inp.pack r) →
          Fin (inp.pack.A r) → E → Real)
        (Jinf : (alpha : LiveSlot L inp.pack r) →
          InterSlot L inp.pack r alpha → E → E)
        (Jbarinf : (alpha : LiveSlot L inp.pack r) →
          InterSlot L inp.pack r alpha → E → E),
      HasSuppConvDataOn (I := I) inp P L r hr phi hphi d.chart
          U C0 C1 aInf Jinf Jbarinf ∧
        HasStageBaseTail inp P L hr phi hphi
          (chart := d.chart) := by
  obtain ⟨phi, hphi, U, C0, C1, aInf, Jinf, Jbarinf, hdata⟩ :=
    d.exists_supp_data inp aMin hphys P L hstable hcomplete hconn
      r hr hratio
  exact ⟨phi, hphi, U, C0, C1, aInf, Jinf, Jbarinf, hdata,
    d.stage_base_tail inp P L hr phi hphi⟩

theorem exists_supp_metric
    (inp : MetricCompactCore (I := I) X)
    (d : BoundedGeometryNormalData (I := I) X inp.decay)
    (aMin : Real)
    (hphys : 8 * Real.exp inp.decay.C < aMin * inp.D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (hstable : ∀ a b : Nat,
      (∀ᶠ k in Filter.atTop,
        BInter inp.decay inp.D P L.lamInf a b (L.φ k)) ∨
      (∀ᶠ k in Filter.atTop,
        ¬ BInter inp.decay inp.D P L.lamInf a b (L.φ k)))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (r : Real) (hr : 0 ≤ r)
    (hratio : 48 * aMin < d.ratio) :
    ∃ (phi : Nat → Nat) (hphi : StrictMono phi)
        (V U C0 C1 : LiveSlot L inp.pack r → Set E)
        (aInf : (alpha : LiveSlot L inp.pack r) →
          Fin (inp.pack.A r) → E → Real)
        (Jinf : (alpha : LiveSlot L inp.pack r) →
          InterSlot L inp.pack r alpha → E → E)
        (Jbarinf : (alpha : LiveSlot L inp.pack r) →
          InterSlot L inp.pack r alpha → E → E)
        (gInf : LiveSlot L inp.pack r →
          E → (E →L[Real] E →L[Real] Real)),
      (∀ alpha, V alpha =
        Metric.ball 0 (d.phaseRadius (L.rInf (alpha.1 : Nat) + 1))) ∧
        (∀ n (alpha : LiveSlot L inp.pack r),
          inp.decay.dist ((L.subseq hphi).φ n)
            (seqCenterD inp.decay P (L.subseq hphi) n
              (alpha.1 : Nat))
            (X.obj ((L.subseq hphi).φ n)).basepoint <
              L.rInf (alpha.1 : Nat) + 1) ∧
        HasSuppConvDataOn (I := I) inp P L r hr phi hphi d.chart
          U C0 C1 aInf Jinf Jbarinf ∧
        HasStageMetricOn inp P L phi hphi d.chart V C1 gInf ∧
        HasStageBaseTail inp P L hr phi hphi
          (chart := d.chart) := by
  classical
  obtain ⟨phi0, hphi0, U, C0, C1, aInf, Jinf, Jbarinf,
      hdata0, hbase0⟩ :=
    d.exists_supp_base inp aMin hphys P L hstable hcomplete hconn
      r hr hratio
  let L0 := L.subseq hphi0
  obtain ⟨psi, gInf, hpsi, hcenter, hmetric⟩ :=
    d.exists_stage_metric inp P L0 r
  let phi := phi0 ∘ psi
  have hphi : StrictMono phi := hphi0.comp hpsi
  let V : LiveSlot L inp.pack r → Set E := fun alpha =>
    Metric.ball 0 (d.phaseRadius (L.rInf (alpha.1 : Nat) + 1))
  have hdata : HasSuppConvDataOn (I := I) inp P L r hr phi hphi d.chart
      U C0 C1 aInf Jinf Jbarinf :=
    hdata0.subseq inp P L r hr hphi0 d.chart
      U C0 C1 aInf Jinf Jbarinf hpsi
  have hbase : HasStageBaseTail inp P L hr phi hphi
      (chart := d.chart) :=
    hbase0.subseq inp P L hr hphi0
      (chart := d.chart) (hψ := hpsi)
  have hcenter' : ∀ n (alpha : LiveSlot L inp.pack r),
      inp.decay.dist ((L.subseq hphi).φ n)
        (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))
        (X.obj ((L.subseq hphi).φ n)).basepoint <
          L.rInf (alpha.1 : Nat) + 1 := by
    intro n alpha
    simpa only [phi, L0, NetLimitData.subseq, Function.comp_apply,
      seqCenterD_subseq] using hcenter n alpha
  have hU8 : ∀ alpha : LiveSlot L inp.pack r,
      U alpha ⊆ Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)) := by
    have hcopy := hdata
    dsimp only [HasSuppConvDataOn] at hcopy
    exact hcopy.2.1
  have hstageMetric :
      HasStageMetricOn inp P L phi hphi d.chart V C1 gInf := by
    intro alpha
    obtain ⟨hgInf, hconv, hequiv⟩ := hmetric alpha
    have hC1U : C1 alpha ⊆ U alpha :=
      (hdata.core_on inp P L r hr d.chart U C0 C1
        aInf Jinf Jbarinf alpha).2.2.2.2
    let Ralpha := L.rInf (alpha.1 : Nat) + 1
    have hhalf := lamInf_lt_halfMin inp.decay inp.hD hphys P L
      (alpha.1 : Nat)
    have hmu : 0 < inp.decay.mu Ralpha := inp.decay.mu_pos Ralpha
    have hprod :
        48 * aMin * inp.decay.mu Ralpha <
          d.ratio * inp.decay.mu Ralpha :=
      mul_lt_mul_of_pos_right hratio hmu
    have hlam : 0 < L.lamInf (alpha.1 : Nat) :=
      inp.decay.lambda_pos inp.hD (L.rInf (alpha.1 : Nat))
    have height :
        8 * L.lamInf (alpha.1 : Nat) <
          aMin * inp.decay.mu Ralpha := by
      dsimp only [Ralpha] at hhalf ⊢
      nlinarith
    have hfour :
        4 * (aMin * inp.decay.mu Ralpha) <
          d.ratio * inp.decay.mu Ralpha := by
      nlinarith [hprod, height, hlam]
    have hsmall :
        8 * L.lamInf (alpha.1 : Nat) < d.phaseRadius Ralpha := by
      dsimp only [BoundedGeometryNormalData.phaseRadius]
      nlinarith [height, hfour]
    have hC1V : C1 alpha ⊆ V alpha :=
      hC1U.trans <| (hU8 alpha).trans <|
        Metric.ball_subset_ball hsmall.le
    refine ⟨hC1V, ?_, ?_, ?_⟩
    · simpa only [V, L0, NetLimitData.subseq_lamInf] using hgInf
    · simpa only [V, phi, L0, NormalChartFamily.metric,
        BoundedGeometryNormalData.chartMetric, NetLimitData.subseq,
        Function.comp_apply, seqCenterD_subseq,
        NetLimitData.subseq_lamInf] using hconv
    · simpa only [V, L0, NetLimitData.subseq_lamInf] using hequiv
  exact ⟨phi, hphi, V, U, C0, C1, aInf, Jinf, Jbarinf, gInf,
    fun _alpha => rfl, hcenter', hdata, hstageMetric, hbase⟩

theorem stage_data_of
    (inp : MetricCompactCore (I := I) X)
    (d : BoundedGeometryNormalData (I := I) X inp.decay)
    (aMin : Real) (haMin : 0 < aMin)
    (hphys : 8 * Real.exp inp.decay.C < aMin * inp.D)
    (hratio : 48 * aMin < d.ratio)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (hstable : ∀ a b : Nat,
      (∀ᶠ k in Filter.atTop,
        BInter inp.decay inp.D P L.lamInf a b (L.φ k)) ∨
      (∀ᶠ k in Filter.atTop,
        ¬ BInter inp.decay inp.D P L.lamInf a b (L.φ k)))
    {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (V U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (gInf : LiveSlot L inp.pack r →
      E → (E →L[Real] E →L[Real] Real))
    (hV : ∀ alpha, V alpha =
      Metric.ball 0 (d.phaseRadius (L.rInf (alpha.1 : Nat) + 1)))
    (hdata : HasSuppConvDataOn (I := I) inp P L r hr phi hphi d.chart
      U C0 C1 aInf Jinf Jbarinf)
    (hmetric : HasStageMetricOn inp P L phi hphi d.chart V C1 gInf)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (hbase : HasStageBaseTail inp P L hr phi hphi
      (chart := d.chart))
    (hcenter : ∀ n (alpha : LiveSlot L inp.pack r),
      inp.decay.dist ((L.subseq hphi).φ n)
        (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))
        (X.obj ((L.subseq hphi).φ n)).basepoint ≤
          L.rInf (alpha.1 : Nat) + 1)
    (q : LiveSlot L inp.pack r → NNReal)
    (hqdata : ∀ gamma : LiveSlot L inp.pack r,
      let Rgamma := L.rInf (gamma.1 : Nat) + 1
      let rho := aMin * inp.decay.mu Rgamma
      0 < q gamma ∧ 0 < rho ∧
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
    HasStageJetDataOn (I := I) inp P L hr phi hphi d.chart
      V U C0 C1 aInf Jinf Jbarinf gInf := by
  classical
  obtain ⟨deltaStage, _deltaInf, e, _eInf, hpair, hstage⟩ :=
    d.exists_stage_pair inp P L phi hphi hcomplete hconn
      V C1 gInf hV hcenter hmetric q (fun alpha => by
        rcases hqdata alpha with
          ⟨hq, _hrho, _hrhoq, hqWide, hqAcc, herr, hinvErr⟩
        exact ⟨hq, hqWide, hqAcc, herr, hinvErr⟩)
  have hdiag : ∀ alpha,
      let Lphi := L.subseq hphi
      ∀ n, IsNormalDiag (I := I) (X.obj (Lphi.φ n))
        (hcomplete.complete (Lphi.φ n)) (hconn (Lphi.φ n))
        (seqCenterD inp.decay P Lphi n (alpha.1 : Nat))
        (q alpha) (deltaStage alpha) (e alpha n)
        (c := d.chart (Lphi.φ n)
          (seqCenterD inp.decay P Lphi n (alpha.1 : Nat))) := by
    intro alpha
    let Lphi := L.subseq hphi
    let index : Nat → Nat := fun n => Lphi.φ n
    let Xphi : PointedRiemannianSeq.{u, uE, uH} (I := I) :=
      X.subseq index
    let dphi : BoundedGeometryNormalData (I := I) Xphi
        (inp.decay.subseq index) := d.subseq index
    let c : LiveSlot L inp.pack r → ∀ n : Nat, (Xphi.obj n).M :=
      fun beta n =>
        seqCenterD inp.decay P Lphi n (beta.1 : Nat)
    simpa only [Lphi, index, Xphi, dphi, c,
      PointedRiemannianSeq.subseq, BoundedGeometryNormalData.subseq] using
      (hpair alpha).2.2.2.2.2.1
  have hfence : ∀ alpha,
      let Lphi := L.subseq hphi
      ∀ n, NormalDiagFence (I := I) (X.obj (Lphi.φ n))
        (seqCenterD inp.decay P Lphi n (alpha.1 : Nat))
        (q alpha) (e alpha n)
        (c := d.chart (Lphi.φ n)
          (seqCenterD inp.decay P Lphi n (alpha.1 : Nat))) := by
    intro alpha
    let Lphi := L.subseq hphi
    let index : Nat → Nat := fun n => Lphi.φ n
    let Xphi : PointedRiemannianSeq.{u, uE, uH} (I := I) :=
      X.subseq index
    let dphi : BoundedGeometryNormalData (I := I) Xphi
        (inp.decay.subseq index) := d.subseq index
    let c : LiveSlot L inp.pack r → ∀ n : Nat, (Xphi.obj n).M :=
      fun beta n =>
        seqCenterD inp.decay P Lphi n (beta.1 : Nat)
    dsimp only
    intro stage
    simpa only [Lphi, index, Xphi, dphi, c,
      PointedRiemannianSeq.subseq, BoundedGeometryNormalData.subseq] using
      (hstage alpha stage).1
  have hinv : ∀ alpha,
      let Lphi := L.subseq hphi
      ∀ n, ApproximatesLinearOn
        ((e alpha n).symm : E × E → E × E)
        ((PhaseFlow.freeDiagCLE (E := E)).symm :
          (E × E) →L[Real] (E × E))
        (e alpha n).target
        (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
            (E × E) →L[Real] (E × E))‖₊ *
          (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
              (E × E) →L[Real] (E × E))‖₊⁻¹ -
            PhaseFlow.phaseErr (d.phaseK (2 * q alpha)))⁻¹ *
          PhaseFlow.phaseErr (d.phaseK (2 * q alpha))) := by
    intro alpha
    let Lphi := L.subseq hphi
    let index : Nat → Nat := fun n => Lphi.φ n
    let Xphi : PointedRiemannianSeq.{u, uE, uH} (I := I) :=
      X.subseq index
    let dphi : BoundedGeometryNormalData (I := I) Xphi
        (inp.decay.subseq index) := d.subseq index
    let c : LiveSlot L inp.pack r → ∀ n : Nat, (Xphi.obj n).M :=
      fun beta n =>
        seqCenterD inp.decay P Lphi n (beta.1 : Nat)
    dsimp only
    intro stage
    simpa only [Lphi, index, Xphi, dphi, c,
      PointedRiemannianSeq.subseq, BoundedGeometryNormalData.subseq] using
      (hstage alpha stage).2
  have hqdata' : ∀ gamma : LiveSlot L inp.pack r,
      let Rgamma := L.rInf (gamma.1 : Nat) + 1
      let rho := aMin * inp.decay.mu Rgamma
      0 < q gamma ∧ 0 < deltaStage gamma ∧ 0 < rho ∧
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
            PhaseFlow.phaseErr (d.phaseK (2 * q gamma)) < 1 / 24 := by
    intro gamma
    rcases hqdata gamma with
      ⟨hq, hrho, hrhoq, hqWide, hqAcc, herr, hinvErr⟩
    exact ⟨hq, (hpair gamma).2.2.2.1, hrho, hrhoq,
      hqWide, hqAcc, herr, hinvErr⟩
  have hbranch : ∀ᶠ n in Filter.atTop,
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
        letI : T2Space (TangentBundle I
            (X.obj ((L.subseq hphi).φ n)).M) :=
          (X.obj ((L.subseq hphi).φ n)).t2TangentBundle
        ∃ e0 : OpenPartialHomeomorph (E × E) (E × E),
          IsNormalDiag (I := I) (X.obj ((L.subseq hphi).φ n))
              (hcomplete.complete ((L.subseq hphi).φ n))
              (hconn ((L.subseq hphi).φ n))
              x0 (q gamma) (deltaStage gamma) e0
              (c := d.chart ((L.subseq hphi).φ n) x0) ∧
            NormalDiagFence (I := I) (X.obj ((L.subseq hphi).φ n))
              x0 (q gamma) e0
              (c := d.chart ((L.subseq hphi).φ n) x0) ∧
            ApproximatesLinearOn
              (e0.symm : E × E → E × E)
              ((PhaseFlow.freeDiagCLE (E := E)).symm :
                (E × E) →L[Real] (E × E))
              e0.target
              (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
                  (E × E) →L[Real] (E × E))‖₊ *
                (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
                    (E × E) →L[Real] (E × E))‖₊⁻¹ -
                  PhaseFlow.phaseErr (d.phaseK (2 * q gamma)))⁻¹ *
                PhaseFlow.phaseErr (d.phaseK (2 * q gamma))) ∧
            rho ≤ (d.chart ((L.subseq hphi).φ n) x0).radius / 4 := by
    apply Filter.Eventually.of_forall
    intro n gamma
    let Lphi := L.subseq hphi
    let Rgamma := L.rInf (gamma.1 : Nat) + 1
    let rho := aMin * inp.decay.mu Rgamma
    let x0 := seqCenterD inp.decay P Lphi n (gamma.1 : Nat)
    letI : TopologicalSpace (X.obj (Lphi.φ n)).M :=
      (X.obj (Lphi.φ n)).topology
    letI : ChartedSpace H (X.obj (Lphi.φ n)).M :=
      (X.obj (Lphi.φ n)).charted
    letI : IsManifold I ∞ (X.obj (Lphi.φ n)).M :=
      (X.obj (Lphi.φ n)).smooth
    letI : T2Space (TangentBundle I (X.obj (Lphi.φ n)).M) :=
      (X.obj (Lphi.φ n)).t2TangentBundle
    have hfour : 4 * aMin < d.ratio := by nlinarith [hratio]
    have hmu : 0 < inp.decay.mu Rgamma := inp.decay.mu_pos Rgamma
    have hrhoPhase : rho < d.phaseRadius Rgamma := by
      have hmul := mul_lt_mul_of_pos_right hfour hmu
      dsimp only [rho, BoundedGeometryNormalData.phaseRadius]
      nlinarith
    have hphaseChart :
        d.phaseRadius Rgamma ≤
          (d.chart (Lphi.φ n) x0).radius / 4 := by
      rw [BoundedGeometryNormalData.phaseRadius, d.radius_eq]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (inp.decay.mu_antitone (hcenter n gamma)) d.ratio_pos.le)
        (by norm_num)
    exact ⟨e gamma n, hdiag gamma n, hfence gamma n, hinv gamma n,
      hrhoPhase.le.trans hphaseChart⟩
  have hU8 : ∀ alpha : LiveSlot L inp.pack r,
      U alpha ⊆ Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)) := by
    have hcopy := hdata
    dsimp only [HasSuppConvDataOn] at hcopy
    exact hcopy.2.1
  have hC1q : ∀ alpha : LiveSlot L inp.pack r,
      C1 alpha ⊆ Metric.ball 0 ((q alpha : Real) / 2) := by
    intro alpha
    have hC1U : C1 alpha ⊆ U alpha :=
      (hdata.core_on inp P L r hr d.chart U C0 C1
        aInf Jinf Jbarinf alpha).2.2.2.2
    have hlam := lamInf_lt_halfMin inp.decay inp.hD hphys P L
      (alpha.1 : Nat)
    rcases hqdata alpha with
      ⟨_hq, _hrho, hrhoq, _hqWide, _hqAcc, _herr, _hinvErr⟩
    have hsmall :
        8 * L.lamInf (alpha.1 : Nat) < (q alpha : Real) / 2 := by
      nlinarith
    exact hC1U.trans <| (hU8 alpha).trans <|
      Metric.ball_subset_ball hsmall.le
  have hcube : ∀ alpha : LiveSlot L inp.pack r,
      ∃ (W : Set E) (PhiInf : E → E) (rootRho : Real)
          (Phi3 : Nat → Nat → Nat → E → E),
        HasStageRootCube inp P L hr phi hphi C1 alpha (e alpha)
          W PhiInf rootRho Phi3 (chart := d.chart) := by
    intro alpha
    exact hdata.exists_stage_cube inp P L hr phi hphi d.chart
      U C0 C1 aInf Jinf Jbarinf alpha (hpair alpha) (hC1q alpha)
  choose W PhiInf rootRho Phi3 hroot using hcube
  have hjets : ∀ R, R < r → ∀ p eps, 0 < eps →
      HasStageJetTail inp P L hr phi hphi C0 R p eps
        (chart := d.chart) := by
    intro R hR p eps heps
    exact d.stage_jet_tail inp aMin haMin hphys P L hstable hr
      phi hphi U C0 C1 aInf Jinf Jbarinf hdata hcomplete hconn
      q deltaStage hqdata' hbranch e hdiag hfence
      W PhiInf rootRho Phi3 hroot R hR p eps heps
  exact ⟨hdata, hmetric, hjets, hbase⟩

private noncomputable def baseScale
    {hd : InjRadiusDecayInput (I := I) X}
    (d : BoundedGeometryNormalData (I := I) X hd)
    (hre : hd.RealizesEdist)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) : Real :=
  Classical.choose (d.exists_live_scale hre hcomplete hconn)

noncomputable def stageScale
    {hd : InjRadiusDecayInput (I := I) X}
    (d : BoundedGeometryNormalData (I := I) X hd)
    (hre : hd.RealizesEdist)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) : Real :=
  min (baseScale d hre hcomplete hconn) (d.ratio / 96)

omit [CompleteSpace E] in
theorem stageScale_pos
    {hd : InjRadiusDecayInput (I := I) X}
    (d : BoundedGeometryNormalData (I := I) X hd)
    (hre : hd.RealizesEdist)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    0 < d.stageScale hre hcomplete hconn := by
  apply lt_min
  · exact (Classical.choose_spec
      (d.exists_live_scale hre hcomplete hconn)).1
  · exact div_pos d.ratio_pos (by norm_num)

omit [CompleteSpace E] in
theorem stageScale_ratio
    {hd : InjRadiusDecayInput (I := I) X}
    (d : BoundedGeometryNormalData (I := I) X hd)
    (hre : hd.RealizesEdist)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    48 * d.stageScale hre hcomplete hconn < d.ratio := by
  have hle :
      d.stageScale hre hcomplete hconn ≤ d.ratio / 96 := by
    exact min_le_right _ _
  calc
    48 * d.stageScale hre hcomplete hconn ≤ 48 * (d.ratio / 96) :=
      mul_le_mul_of_nonneg_left hle (by norm_num)
    _ = d.ratio / 2 := by ring
    _ < d.ratio := half_lt_self d.ratio_pos

theorem stage_data
    (inp : MetricCompactCore (I := I) X)
    (d : BoundedGeometryNormalData (I := I) X inp.decay)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (hphys : 8 * Real.exp inp.decay.C <
      d.stageScale inp.realizes hcomplete hconn * inp.D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (hstable : ∀ a b : Nat,
      (∀ᶠ k in Filter.atTop,
        BInter inp.decay inp.D P L.lamInf a b (L.φ k)) ∨
      (∀ᶠ k in Filter.atTop,
        ¬ BInter inp.decay inp.D P L.lamInf a b (L.φ k)))
    (r : Real) (hr : 0 ≤ r) :
    ∃ (phi : Nat → Nat) (hphi : StrictMono phi)
        (V U C0 C1 : LiveSlot L inp.pack r → Set E)
        (aInf : (alpha : LiveSlot L inp.pack r) →
          Fin (inp.pack.A r) → E → Real)
        (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
          InterSlot L inp.pack r alpha → E → E)
        (gInf : LiveSlot L inp.pack r →
          E → (E →L[Real] E →L[Real] Real)),
      HasStageJetDataOn (I := I) inp P L hr phi hphi d.chart
        V U C0 C1 aInf Jinf Jbarinf gInf := by
  classical
  let aBase := baseScale d inp.realizes hcomplete hconn
  have hscaleRaw := Classical.choose_spec
    (d.exists_live_scale inp.realizes hcomplete hconn)
  have haBase : 0 < aBase := by
    simpa only [aBase, baseScale] using hscaleRaw.1
  let aMin := d.stageScale inp.realizes hcomplete hconn
  have haMin : 0 < aMin := d.stageScale_pos inp.realizes hcomplete hconn
  have haMinBase : aMin ≤ aBase := by
    dsimp only [aMin, stageScale]
    exact min_le_left _ _
  have hratio : 48 * aMin < d.ratio :=
    d.stageScale_ratio inp.realizes hcomplete hconn
  obtain ⟨q, _delta, hqraw, _hbranch⟩ :=
    hscaleRaw.2 P L inp.pack r
  have hqdata : ∀ gamma : LiveSlot L inp.pack r,
      let Rgamma := L.rInf (gamma.1 : Nat) + 1
      let rho := aMin * inp.decay.mu Rgamma
      0 < q gamma ∧ 0 < rho ∧
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
            PhaseFlow.phaseErr (d.phaseK (2 * q gamma)) < 1 / 24 := by
    intro gamma
    have hraw := hqraw gamma
    dsimp only at hraw ⊢
    rcases hraw with
      ⟨hq, _hdelta, _hrho, hqMin, hqWide, hqAcc, herr, hinvErr⟩
    have hmu : 0 < inp.decay.mu (L.rInf (gamma.1 : Nat) + 1) :=
      inp.decay.mu_pos _
    have hrho : 0 <
        aMin * inp.decay.mu (L.rInf (gamma.1 : Nat) + 1) :=
      mul_pos haMin hmu
    have hscaleLe :
        aMin * inp.decay.mu (L.rInf (gamma.1 : Nat) + 1) ≤
          aBase * inp.decay.mu (L.rInf (gamma.1 : Nat) + 1) :=
      mul_le_mul_of_nonneg_right haMinBase hmu.le
    refine ⟨hq, hrho, ?_, hqWide, hqAcc, herr, hinvErr⟩
    exact (mul_le_mul_of_nonneg_left hscaleLe (by norm_num)).trans_lt hqMin
  obtain ⟨phi, hphi, V, U, C0, C1, aInf, Jinf, Jbarinf, gInf,
      hV, hcenter, hdata, hmetric, hbase⟩ :=
    d.exists_supp_metric inp aMin hphys P L hstable hcomplete hconn
      r hr hratio
  refine ⟨phi, hphi, V, U, C0, C1, aInf, Jinf, Jbarinf, gInf, ?_⟩
  exact d.stage_data_of inp aMin haMin hphys hratio P L hstable hr
    phi hphi V U C0 C1 aInf Jinf Jbarinf gInf hV hdata hmetric
    hcomplete hconn hbase (fun n alpha => (hcenter n alpha).le) q hqdata

theorem exists_stage_data
    (inp : MetricCompactCore (I := I) X)
    (d : BoundedGeometryNormalData (I := I) X inp.decay)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    ∃ aMin : Real, 0 < aMin ∧ 48 * aMin < d.ratio ∧
      ∀ (_hphys : 8 * Real.exp inp.decay.C < aMin * inp.D)
        (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
        (L : NetLimitData inp.decay inp.D P)
        (_hstable : ∀ a b : Nat,
          (∀ᶠ k in Filter.atTop,
            BInter inp.decay inp.D P L.lamInf a b (L.φ k)) ∨
          (∀ᶠ k in Filter.atTop,
            ¬ BInter inp.decay inp.D P L.lamInf a b (L.φ k)))
        (r : Real) (hr : 0 ≤ r),
        ∃ (phi : Nat → Nat) (hphi : StrictMono phi)
            (V U C0 C1 : LiveSlot L inp.pack r → Set E)
            (aInf : (alpha : LiveSlot L inp.pack r) →
              Fin (inp.pack.A r) → E → Real)
            (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
              InterSlot L inp.pack r alpha → E → E)
            (gInf : LiveSlot L inp.pack r →
              E → (E →L[Real] E →L[Real] Real)),
          HasStageJetDataOn (I := I) inp P L hr phi hphi d.chart
            V U C0 C1 aInf Jinf Jbarinf gInf := by
  refine ⟨d.stageScale inp.realizes hcomplete hconn,
    d.stageScale_pos inp.realizes hcomplete hconn,
    d.stageScale_ratio inp.realizes hcomplete hconn, ?_⟩
  intro hphys P L hstable r hr
  exact d.stage_data inp hcomplete hconn hphys P L hstable r hr

theorem stage_diag
    (inp : MetricCompactCore (I := I) X)
    (d : BoundedGeometryNormalData (I := I) X inp.decay)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (hphys : 8 * Real.exp inp.decay.C <
      d.stageScale inp.realizes hcomplete hconn * inp.D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L0 : NetLimitData inp.decay inp.D P)
    (hstable : IsStableNet inp P L0) :
    ∃ (hseed : HasStageSeedOn inp P L0 d.chart)
        (psi : Nat → Nat) (_hpsi : StrictMono psi),
      ∀ q : Nat,
        HasRadiusTailOn inp P L0 hconn d.chart hseed psi q := by
  have hseed : HasStageSeedOn inp P L0 d.chart := by
    refine ⟨hstable, ?_⟩
    intro L hstableL r hr
    exact d.stage_data inp hcomplete hconn hphys P L hstableL r hr
  obtain ⟨psi, hpsi, htail⟩ :=
    hseed.exists_radius_diag inp P L0 hconn d.chart
  exact ⟨hseed, psi, hpsi, htail⟩

theorem exists_stage_diag
    (inp : MetricCompactCore (I := I) X)
    (d : BoundedGeometryNormalData (I := I) X inp.decay)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    ∃ aMin : Real, 0 < aMin ∧ 48 * aMin < d.ratio ∧
      ∀ (_hphys : 8 * Real.exp inp.decay.C < aMin * inp.D)
        (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
        (L0 : NetLimitData inp.decay inp.D P)
        (_hstable : IsStableNet inp P L0),
        ∃ (hseed : HasStageSeedOn inp P L0 d.chart)
            (psi : Nat → Nat) (_hpsi : StrictMono psi),
          ∀ q : Nat,
            HasRadiusTailOn inp P L0 hconn d.chart hseed psi q := by
  refine ⟨d.stageScale inp.realizes hcomplete hconn,
    d.stageScale_pos inp.realizes hcomplete hconn,
    d.stageScale_ratio inp.realizes hcomplete hconn, ?_⟩
  intro hphys P L0 hstable
  exact d.stage_diag inp hcomplete hconn hphys P L0 hstable

end BoundedGeometryNormalData

end HCGCompactness
end DifferentialGeometry
