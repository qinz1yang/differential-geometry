import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.Comparison



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

theorem HasStageJetDataOn.hloc_tail
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
      E → (E →L[Real] E →L[Real] Real))
    (hstage : HasStageJetDataOn (I := I) inp P L hr phi hphi
      chart V U C0 C1 aInf Jinf Jbarinf gInf)
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
        (stageComparisonMap inp P Lphi r hr k l (chart := chart))
        (Lphi.hatSourceBall inp.decay P R k) := by
  classical
  rcases hstage with ⟨hdata, _hmetric, hjets, _hbase⟩
  have hcoverData := hdata
  dsimp only [HasSuppConvDataOn] at hcoverData
  rcases hcoverData with
    ⟨_hU, _hU8, _hC0, _hC1, _hC01, _hC1U, _hconvex, _hzero,
      _hbuffer, hsource, _hgeom, _hlim, _hweight, _htrans, _hsmooth⟩
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
  let F := stageComparisonMap inp P Lphi r hr k l (chart := chart)
  rintro ⟨x, hx⟩
  have hxLarge : x ∈ Lphi.hatSourceBall inp.decay P r k := by
    let : MetricSpace Yk.M := (P (Lphi.φ k)).ms
    exact cball_subset_of_le hRr.le
      (by simpa only [NetLimitData.hatSourceBall, Yk] using hx)
  have hcover := hsource k
  obtain ⟨alpha, z, hzInt, hzx⟩ :=
    Set.mem_iUnion.mp (hcover hxLarge)
  let xk0 := seqCenterD inp.decay P Lphi k (alpha.1 : Nat)
  let xl0 := seqCenterD inp.decay P Lphi l (alpha.1 : Nat)
  let chiK := chart (Lphi.φ k) xk0
  let chiL := chart (Lphi.φ l) xl0
  have hxEq : chiK.hom z = x := by
    with_unfolding_all
      exact hzx
  obtain ⟨_hUopen, _hC0, _hC1, hC01, hC1U⟩ :=
    hdata.core_on inp P L r hr chart U C0 C1 aInf Jinf Jbarinf alpha
  obtain ⟨hRad, _hMaps⟩ :=
    hdata.geom_on inp P L r hr chart U C0 C1 aInf Jinf Jbarinf k alpha
  have hzC0 : z ∈ C0 alpha := interior_subset hzInt
  have hzU : z ∈ U alpha :=
    hC1U (interior_subset (hC01 hzC0))
  have hzBall := hRad hzU
  have hzSource : z ∈ chiK.restrictBall.source := by
    with_unfolding_all
      exact hzBall
  let c := chiK.restrictBall.symm
  let d := chiL.restrictBall.symm
  have hc_symm (w : E) : c.symm w = chiK.hom w := by
    rfl
  have hd_apply (y : Yl.M) : d y = chiL.inv y := by
    rfl
  have hd_source : d.source = chiL.restrictBall.target := by
    rfl
  have hxc : x ∈ c.source := by
    have hout := chiK.restrictBall.map_source hzSource
    rw [NormalCoordinates.NormalBallChart.restrictBall_apply, hxEq] at hout
    with_unfolding_all
      exact hout
  have hcx : c x = z := by
    have hout := chiK.restrictBall.left_inv hzSource
    rw [NormalCoordinates.NormalBallChart.restrictBall_apply, hxEq] at hout
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
  let Vloc : Set E :=
    interior (C0 alpha) ∩
      (chiK.restrictBall.source ∩ chiK.restrictBall ⁻¹' Bmid)
  have hVloc : IsOpen Vloc := by
    dsimp only [Vloc]
    exact isOpen_interior.inter
      (chiK.restrictBall.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage
        chiK.restrictBall.open_source hBopen)
  have hxBmid : x ∈ Bmid := by
    let : MetricSpace Yk.M := (P (Lphi.φ k)).ms
    exact Metric.closedBall_subset_ball hRmid
      (by simpa only [Bmid, NetLimitData.hatSourceBall, Yk] using hx)
  have hcxV : c x ∈ Vloc := by
    rw [hcx]
    refine ⟨hzInt, hzSource, ?_⟩
    change chiK.restrictBall z ∈ Bmid
    simpa only [NormalCoordinates.NormalBallChart.restrictBall_apply, hxEq]
      using hxBmid
  have hjetAt (w : E) (hw : w ∈ Vloc) :
      stageComparisonMap inp P Lphi r hr k l
          (chiK.hom w) (chart := chart) ∈ chiL.restrictBall.target ∧
        ContDiffAt Real ∞
          (fun u => chiL.inv
            (stageComparisonMap inp P Lphi r hr k l
              (chiK.hom u) (chart := chart))) w ∧
        ∀ j ≤ 1,
          mapDerivNorm j
            (fun u => chiL.inv
              (stageComparisonMap inp P Lphi r hr k l
                (chiK.hom u) (chart := chart)))
            id w ≤ (1 / 2 : Real) := by
    have hwMid : chiK.hom w ∈
        Lphi.hatSourceBall inp.decay P Rmid k := by
      let : MetricSpace Yk.M := (P (Lphi.φ k)).ms
      have hwBmid : chiK.hom w ∈ Bmid := by
        have hwRestr : chiK.restrictBall w ∈ Bmid := by
          exact hw.2.2
        simpa only [NormalCoordinates.NormalBallChart.restrictBall_apply]
          using hwRestr
      exact Metric.ball_subset_closedBall
        (by simpa only [Bmid, NetLimitData.hatSourceBall, Yk] using hwBmid)
    simpa only [chiK, chiL, xk0, xl0, Yk, Yl, Lphi] using
      hN k hk l hl alpha w (interior_subset hw.1) hw.1 hwMid
  have hmap : Set.MapsTo (fun w => F (c.symm w)) Vloc d.source := by
    intro w hw
    have hout := (hjetAt w hw).1
    simpa only [F, hc_symm, hd_source] using hout
  have hG : ContDiffOn Real ∞ (fun w => d (F (c.symm w))) Vloc := by
    intro w hw
    have hout := (hjetAt w hw).2.1
    have hout' : ContDiffAt Real ∞ (fun u => d (F (c.symm u))) w := by
      simpa only [F, hc_symm, hd_apply] using hout
    exact hout'.contDiffWithinAt
  have hinv : ∀ w ∈ Vloc,
      (fderiv Real (fun u => d (F (c.symm u))) w).IsInvertible := by
    intro w hw
    have hcd := (hjetAt w hw).2.1
    have hdiff : DifferentiableAt Real
        (fun u => chiL.inv
          (stageComparisonMap inp P Lphi r hr k l
            (chiK.hom u) (chart := chart))) w :=
      hcd.differentiableAt (by simp)
    have hneu := neumannOfDerivNorm hdiff ((hjetAt w hw).2.2 1 le_rfl)
    have hlt :
        ‖ContinuousLinearMap.id Real E -
          fderiv Real
            (fun u => chiL.inv
              (stageComparisonMap inp P Lphi r hr k l
                (chiK.hom u) (chart := chart))) w‖ < 1 :=
      hneu.trans_lt (by norm_num)
    have hout := Coordinates.isInvertible_of_norm_id_sub_lt hlt
    simpa only [F, hc_symm, hd_apply] using hout
  exact Coordinates.isLocalDiffeomorphAt_of_coordinates c d hVloc hxc hcxV hmap hG hinv

end HCGCompactness
end DifferentialGeometry
