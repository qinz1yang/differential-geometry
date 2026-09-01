import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.InverseChartConvergence.StageJet
import DifferentialGeometry.Analysis.Calculus.DerivativePerturbation
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricConvergence.BoundedGeometry
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.MappingControl.InjectivityHigherRegularity

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Set Filter Topology Bundle Manifold
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Analysis

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}


theorem BoundedGeometryNormalChartData.inv_chart_conv
    (inp : MetricCompactCore (I := I) X)
    (d : BoundedGeometryNormalChartData (I := I) X inp.decay)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (hcomplete : ∀ j, MetricComplete (I := I) (X.obj j))
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (Vmetric U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (gInf : LiveSlot L inp.pack r →
      E → (E →L[Real] E →L[Real] Real))
    (hstage : HasStageJetDataOn (I := I) inp P L hr phi hphi
      d.chart Vmetric U C0 C1 aInf Jinf Jbarinf gInf)
    (S T Vrad : Real) (hST : S < T)
    (hroom : T + (4 + 8 * Real.sqrt 2) * inp.decay.lambda inp.D 0 < Vrad)
    (hVr : Vrad < r)
    (alpha : LiveSlot L inp.pack r)
    (Q W K : Set E) (hQ : IsOpen Q) (hW : IsOpen W)
    (hK : IsCompact K) (hKQ : K ⊆ Q) (hQW : closure Q ⊆ W)
    (hWint : W ⊆ interior (C0 alpha))
    (kn ln : Nat → Nat)
    (hkn : Tendsto kn atTop atTop) (hln : Tendsto ln atTop atTop)
    (hsource : ∀ᶠ n in atTop,
      let Lphi := L.subseq hphi
      let Yk := X.obj (Lphi.φ (kn n))
      letI : TopologicalSpace Yk.M := Yk.topology
      letI : ChartedSpace H Yk.M := Yk.charted
      letI : IsManifold I ∞ Yk.M := Yk.smooth
      letI : T2Space Yk.M := Yk.t2
      letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
      letI : MetricSpace Yk.M := (P (Lphi.φ (kn n))).ms
      Set.MapsTo
        (d.chart (Lphi.φ (kn n))
          (seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat))).hom
        W (Lphi.hatSourceBall inp.decay P S (kn n))) :
    let Lphi := L.subseq hphi
    let G : Nat → E → E := fun n w ↦
      let Yk := X.obj (Lphi.φ (kn n))
      let Yl := X.obj (Lphi.φ (ln n))
      letI : TopologicalSpace Yk.M := Yk.topology
      letI : ChartedSpace H Yk.M := Yk.charted
      letI : IsManifold I ∞ Yk.M := Yk.smooth
      letI : T2Space Yk.M := Yk.t2
      letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
      letI : MetricSpace Yk.M := (P (Lphi.φ (kn n))).ms
      letI : Nonempty Yk.M := ⟨Yk.basepoint⟩
      letI : TopologicalSpace Yl.M := Yl.topology
      letI : ChartedSpace H Yl.M := Yl.charted
      letI : IsManifold I ∞ Yl.M := Yl.smooth
      letI : T2Space Yl.M := Yl.t2
      letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
      let chiK := d.chart (Lphi.φ (kn n))
        (seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat))
      let chiL := d.chart (Lphi.φ (ln n))
        (seqCenterD inp.decay P Lphi (ln n) (alpha.1 : Nat))
      let F := stageComparisonMap inp P Lphi r hr
        (kn n) (ln n) (chart := d.chart)
      chiK.inv
        (Function.invFunOn F (Metric.ball Yk.basepoint T) (chiL.hom w))
    ∃ Vout : Set E,
      IsOpen Vout ∧ IsCompact (closure Vout) ∧ K ⊆ Vout ∧
        MapCInfConvOnCompacts Vout G id ∧
        ∀ᶠ n in atTop,
          ContDiffOn Real (∞ : WithTop ℕ∞) (G n) Vout := by
  classical
  dsimp only
  let Lphi := L.subseq hphi
  let A : Nat → E → E := fun n z ↦
    let Yk := X.obj (Lphi.φ (kn n))
    let Yl := X.obj (Lphi.φ (ln n))
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
    let chiK := d.chart (Lphi.φ (kn n))
      (seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat))
    let chiL := d.chart (Lphi.φ (ln n))
      (seqCenterD inp.decay P Lphi (ln n) (alpha.1 : Nat))
    chiL.inv (stageComparisonMap inp P Lphi r hr
      (kn n) (ln n) (chiK.hom z) (chart := d.chart))
  let G : Nat → E → E := fun n w ↦
    let Yk := X.obj (Lphi.φ (kn n))
    let Yl := X.obj (Lphi.φ (ln n))
    letI : TopologicalSpace Yk.M := Yk.topology
    letI : ChartedSpace H Yk.M := Yk.charted
    letI : IsManifold I ∞ Yk.M := Yk.smooth
    letI : T2Space Yk.M := Yk.t2
    letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
    letI : MetricSpace Yk.M := (P (Lphi.φ (kn n))).ms
    letI : Nonempty Yk.M := ⟨Yk.basepoint⟩
    letI : TopologicalSpace Yl.M := Yl.topology
    letI : ChartedSpace H Yl.M := Yl.charted
    letI : IsManifold I ∞ Yl.M := Yl.smooth
    letI : T2Space Yl.M := Yl.t2
    letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
    let chiK := d.chart (Lphi.φ (kn n))
      (seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat))
    let chiL := d.chart (Lphi.φ (ln n))
      (seqCenterD inp.decay P Lphi (ln n) (alpha.1 : Nat))
    let F := stageComparisonMap inp P Lphi r hr
      (kn n) (ln n) (chart := d.chart)
    chiK.inv
      (Function.invFunOn F (Metric.ball Yk.basepoint T) (chiL.hom w))
  change ∃ Vout : Set E,
    IsOpen Vout ∧ IsCompact (closure Vout) ∧ K ⊆ Vout ∧
      MapCInfConvOnCompacts Vout G id ∧
      ∀ᶠ n in atTop,
        ContDiffOn Real (∞ : WithTop ℕ∞) (G n) Vout
  have hstage0 := hstage
  rcases hstage with ⟨hdata, hmetric, hjets, hbase⟩
  have hgap : 0 ≤
      (4 + 8 * Real.sqrt 2) * inp.decay.lambda inp.D 0 :=
    mul_nonneg (by positivity) (inp.decay.lambda_pos inp.hD 0).le
  have hTr : T < r := by linarith
  have hSr : S < r := hST.trans hTr
  have hQint : Q ⊆ interior (C0 alpha) :=
    subset_closure.trans (hQW.trans hWint)
  have hsourceQ : ∀ᶠ n in atTop,
      let Yk := X.obj (Lphi.φ (kn n))
      letI : TopologicalSpace Yk.M := Yk.topology
      letI : ChartedSpace H Yk.M := Yk.charted
      letI : IsManifold I ∞ Yk.M := Yk.smooth
      letI : T2Space Yk.M := Yk.t2
      letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
      Set.MapsTo
        (d.chart (Lphi.φ (kn n))
          (seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat))).hom
        Q (Lphi.hatSourceBall inp.decay P S (kn n)) := by
    filter_upwards [hsource] with n hn
    simpa only [Lphi] using
      hn.mono_left (subset_closure.trans hQW)
  have hAconv : MapCInfConvOnCompacts Q A id := by
    simpa only [A, Lphi] using
      HasStageJetDataOn.chart_conv (I := I) inp P L hr phi hphi
        d.chart Vmetric U C0 C1 aInf Jinf Jbarinf gInf
        ⟨hdata, hmetric, hjets, hbase⟩ S hSr alpha Q hQint
        kn ln hkn hln hsourceQ
  obtain ⟨Njet, hNjet⟩ := hjets S hSr 1 (1 / 2 : Real) (by norm_num)
  obtain ⟨Ninj, hNinj⟩ :=
    d.inj_tail inp P L hr phi hphi hcomplete hconn
      Vmetric U C0 C1 aInf Jinf Jbarinf gInf hstage0
      T Vrad hroom hVr
  obtain ⟨_hUopen, _hC0compact, _hC1compact, hC01, hC1U⟩ :=
    hdata.core_on inp P L r hr d.chart U C0 C1 aInf Jinf Jbarinf alpha
  have hIntU : interior (C0 alpha) ⊆ U alpha :=
    interior_subset.trans (hC01.trans (interior_subset.trans hC1U))
  have hgood : ∀ᶠ n in atTop,
      IsLocalDiffeomorphOn 𝓘(ℝ, E) 𝓘(ℝ, E)
          (∞ : WithTop ℕ∞) (A n) W ∧
        Set.InjOn (A n) W ∧ LeftInvOn (G n) (A n) W := by
    filter_upwards [hkn.eventually_ge_atTop (max Njet Ninj),
      hln.eventually_ge_atTop (max Njet Ninj), hsource] with n hnk hnl hsrc
    have hnkJet : Njet ≤ kn n := (le_max_left _ _).trans hnk
    have hnlJet : Njet ≤ ln n := (le_max_left _ _).trans hnl
    have hnkInj : Ninj ≤ kn n := (le_max_right _ _).trans hnk
    have hnlInj : Ninj ≤ ln n := (le_max_right _ _).trans hnl
    let Yk := X.obj (Lphi.φ (kn n))
    let Yl := X.obj (Lphi.φ (ln n))
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
    let : MetricSpace Yk.M := (P (Lphi.φ (kn n))).ms
    let : MetricSpace Yl.M := (P (Lphi.φ (ln n))).ms
    let : Nonempty Yk.M := ⟨Yk.basepoint⟩
    let F := stageComparisonMap inp P Lphi r hr
      (kn n) (ln n) (chart := d.chart)
    let ck := seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat)
    let cl := seqCenterD inp.decay P Lphi (ln n) (alpha.1 : Nat)
    let chiK := d.chart (Lphi.φ (kn n)) ck
    let chiL := d.chart (Lphi.φ (ln n)) cl
    have hjet (z : E) (hz : z ∈ W) :
        F (chiK.hom z) ∈ chiL.restrictBall.target ∧
          ContDiffAt Real ∞ (A n) z ∧
          ∀ j ≤ 1, mapDerivNorm j (A n) id z ≤ (1 / 2 : Real) := by
      have hzInt : z ∈ interior (C0 alpha) := hWint hz
      have hzSrc := hsrc hz
      simpa only [A, F, chiK, chiL, ck, cl, Yk, Yl, Lphi] using
        hNjet (kn n) hnkJet (ln n) hnlJet alpha z
          (interior_subset hzInt) hzInt hzSrc
    have hAcd : ContDiffOn Real ∞ (A n) W := fun z hz ↦
      (hjet z hz).2.1.contDiffWithinAt
    have hAinv : ∀ z ∈ W,
        (fderiv Real (writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, E)
          z (A n)) (extChartAt 𝓘(ℝ, E) z z)).IsInvertible := by
      intro z hz
      have hdiff : DifferentiableAt Real (A n) z :=
        (hjet z hz).2.1.differentiableAt (by simp)
      have hraw : mapDerivNorm 1 (A n) id z ≤ (1 / 2 : Real) :=
        (hjet z hz).2.2 1 le_rfl
      have hneu := neumannOfDerivNorm hdiff hraw
      apply Coordinates.isInvertible_of_norm_id_sub_lt
      simpa only [writtenInExtChartAt_model_space, ext_chart_model_space_apply] using
        hneu.trans_lt (by norm_num)
    have hAloc : IsLocalDiffeomorphOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
        (A n) W := by
      apply Coordinates.contMDiffOn_isLocalDiffeomorphOn_infty hW
      · simpa only [contMDiffOn_iff_contDiffOn] using hAcd
      · exact hAinv
    have hFInj := hNinj (kn n) hnkInj (ln n) hnlInj
    obtain ⟨hRad, _hMaps⟩ :=
      hdata.geom_on inp P L r hr d.chart U C0 C1 aInf Jinf Jbarinf
        (kn n) alpha
    have hUsrc : U alpha ⊆ chiK.hom.source := by
      intro z hz
      exact chiK.ball_subset (hRad hz)
    have hdecode (q : Yl.M) (hq : q ∈ chiL.restrictBall.target) :
        chiL.hom (chiL.inv q) = q := by
      change chiL.hom (chiL.hom.symm q) = q
      apply chiL.hom.toPartialEquiv.right_inv
      rcases hq with ⟨z, hz, rfl⟩
      exact chiL.hom.map_source (chiL.ball_subset hz)
    have hAinj : Set.InjOn (A n) W := by
      intro z hz w hw hzw
      have hzU : z ∈ U alpha := hIntU (hWint hz)
      have hwU : w ∈ U alpha := hIntU (hWint hw)
      have hzT : chiK.hom z ∈
          Lphi.hatSourceBall inp.decay P T (kn n) :=
        cball_subset_of_le hST.le (hsrc hz)
      have hwT : chiK.hom w ∈
          Lphi.hatSourceBall inp.decay P T (kn n) :=
        cball_subset_of_le hST.le (hsrc hw)
      have hFzT : F (chiK.hom z) ∈ chiL.restrictBall.target :=
        (hjet z hz).1
      have hFwT : F (chiK.hom w) ∈ chiL.restrictBall.target :=
        (hjet w hw).1
      have hinvEq :
          chiL.inv (F (chiK.hom z)) =
            chiL.inv (F (chiK.hom w)) := by
        simpa only [A, F, chiK, chiL, ck, cl, Yk, Yl, Lphi] using hzw
      have hFzw : F (chiK.hom z) = F (chiK.hom w) := by
        calc
          F (chiK.hom z) =
              chiL.hom (chiL.inv (F (chiK.hom z))) :=
            (hdecode _ hFzT).symm
          _ = chiL.hom (chiL.inv (F (chiK.hom w))) :=
            congrArg chiL.hom hinvEq
          _ = F (chiK.hom w) := hdecode _ hFwT
      have hxy : chiK.hom z = chiK.hom w :=
        hFInj hzT hwT hFzw
      calc
        z = chiK.inv (chiK.hom z) :=
          (chiK.hom.left_inv (hUsrc hzU)).symm
        _ = chiK.inv (chiK.hom w) := congrArg chiK.inv hxy
        _ = w := chiK.hom.left_inv (hUsrc hwU)
    have hleft : LeftInvOn (G n) (A n) W := by
      intro z hz
      have hzU : z ∈ U alpha := hIntU (hWint hz)
      have hzClosed : chiK.hom z ∈
          Lphi.hatSourceBall inp.decay P S (kn n) := hsrc hz
      have hzBall : chiK.hom z ∈ Metric.ball Yk.basepoint T := by
        rw [Metric.mem_ball]
        have hzLe : dist (chiK.hom z) Yk.basepoint ≤ S := by
          change dist (chiK.hom z) Yk.basepoint ≤ S at hzClosed
          exact hzClosed
        exact hzLe.trans_lt hST
      have hFzT : F (chiK.hom z) ∈ chiL.restrictBall.target :=
        (hjet z hz).1
      have hdecodeA : chiL.hom (A n z) = F (chiK.hom z) := by
        simpa only [A, F, chiK, chiL, ck, cl, Yk, Yl, Lphi] using
          hdecode _ hFzT
      have hFInjBall : Set.InjOn F (Metric.ball Yk.basepoint T) :=
        hFInj.mono Metric.ball_subset_closedBall
      have hinv : Function.invFunOn F (Metric.ball Yk.basepoint T)
          (chiL.hom (A n z)) = chiK.hom z := by
        rw [hdecodeA]
        exact hFInjBall.leftInvOn_invFunOn hzBall
      change chiK.inv
        (Function.invFunOn F (Metric.ball Yk.basepoint T)
          (chiL.hom (A n z))) = z
      rw [hinv]
      exact chiK.hom.left_inv (hUsrc hzU)
    exact ⟨hAloc, hAinj, hleft⟩
  exact exists_inv_seq hQ hW hK hKQ hQW hAconv hgood

end HCGCompactness
end DifferentialGeometry
