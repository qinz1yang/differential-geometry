import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.ChartFamily
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.InverseHigherRegularity



import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricLocalHigherRegularity
import DifferentialGeometry.Geometry.Metric.Convergence.MetricTowerConvergence

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Set Filter Topology
open Bundle Manifold
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.PDE.RicciFlow

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

theorem BoundedGeometryNormalData.inv_cov_comp_tail
    (inp : MetricCompactCore (I := I) X)
    (d : BoundedGeometryNormalData (I := I) X inp.decay)
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
    {R S T Vrad : Real} (hRS : R < S) (hST : S < T)
    (hroom : T + (4 + 8 * Real.sqrt 2) * inp.decay.lambda inp.D 0 < Vrad)
    (hVr : Vrad < r)
    (e : Module.Basis (Fin (Module.finrank Real E)) Real E)
    (p : Nat) (eps : Real) (heps : 0 < eps) :
    letI : NormedAddCommGroup (E →L[Real] Real) :=
      ContinuousLinearMap.toNormedAddCommGroup
    letI : NormedSpace Real (E →L[Real] Real) :=
      ContinuousLinearMap.toNormedSpace
    letI : NormedAddCommGroup (E →L[Real] E →L[Real] Real) :=
      ContinuousLinearMap.toNormedAddCommGroup
    letI : NormedSpace Real (E →L[Real] E →L[Real] Real) :=
      ContinuousLinearMap.toNormedSpace
    let Lphi := L.subseq hphi
    let A : LiveSlot L inp.pack r → Nat → Nat → E → E :=
      fun alpha k l z =>
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
        let chiK := d.chart (Lphi.φ k)
          (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
        let chiL := d.chart (Lphi.φ l)
          (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
        chiL.inv (stageComparisonMap inp P Lphi r hr k l
          (chiK.hom z) (chart := d.chart))
    let G : LiveSlot L inp.pack r → Nat → Nat → E → E :=
      fun alpha k l w =>
        let Yk := X.obj (Lphi.φ k)
        let Yl := X.obj (Lphi.φ l)
        letI : TopologicalSpace Yk.M := Yk.topology
        letI : ChartedSpace H Yk.M := Yk.charted
        letI : IsManifold I ∞ Yk.M := Yk.smooth
        letI : T2Space Yk.M := Yk.t2
        letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
        letI : MetricSpace Yk.M := (P (Lphi.φ k)).ms
        letI : Nonempty Yk.M := ⟨Yk.basepoint⟩
        letI : TopologicalSpace Yl.M := Yl.topology
        letI : ChartedSpace H Yl.M := Yl.charted
        letI : IsManifold I ∞ Yl.M := Yl.smooth
        letI : T2Space Yl.M := Yl.t2
        letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
        let chiK := d.chart (Lphi.φ k)
          (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
        let chiL := d.chart (Lphi.φ l)
          (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
        let F := stageComparisonMap inp P Lphi r hr k l
          (chart := d.chart)
        chiK.inv
          (Function.invFunOn F (Metric.ball Yk.basepoint T) (chiL.hom w))
    let B : LiveSlot L inp.pack r → Nat →
        E → (E →L[Real] E →L[Real] Real) := fun alpha k =>
      NormalChartFamily.metric d.chart (Lphi.φ k)
        (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
    let Q : LiveSlot L inp.pack r → Nat → Nat →
        E → (E →L[Real] E →L[Real] Real) := fun alpha k l w =>
      _root_.DifferentialGeometry.HCGCompactness.pullbackForm
        (B alpha k (G alpha k l w), fderiv Real (G alpha k l) w)
    let Gamma : LiveSlot L inp.pack r → Nat → E →
        Fin (Module.finrank Real E) → Fin (Module.finrank Real E) →
          Fin (Module.finrank Real E) → Real := fun alpha l z i j m =>
      e.coord m
        (MetricKoszul.raisedKoszulOp
          (B alpha l z) (fderiv Real (B alpha l) z)
          (e i) (e j))
    let tower : (alpha : LiveSlot L inp.pack r) →
        (k l a : Nat) → E →
          (Fin (2 + a) → Fin (Module.finrank Real E)) → Real :=
      fun alpha k l a =>
        iterCovComp (I := 𝓘(Real, E))
          (fun i _ => e i) (Gamma alpha l)
          (fun w slots => (Q alpha k l w - B alpha l w)
            (e (slots 0)) (e (slots 1))) a
    ∃ eta : LiveSlot L inp.pack r → Real,
      (∀ alpha, 0 < eta alpha) ∧
      ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N,
        let Yk := X.obj (Lphi.φ k)
        letI : TopologicalSpace Yk.M := Yk.topology
        letI : ChartedSpace H Yk.M := Yk.charted
        letI : IsManifold I ∞ Yk.M := Yk.smooth
        letI : T2Space Yk.M := Yk.t2
        letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
        letI : MetricSpace Yk.M := (P (Lphi.φ k)).ms
        ∀ y ∈ Lphi.hatSourceBall inp.decay P R k,
          ∃ (alpha : LiveSlot L inp.pack r) (z : E),
            (d.chart (Lphi.φ k)
              (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))).hom z = y ∧
            Metric.closedBall z (eta alpha) ⊆ interior (C0 alpha) ∧
            ∀ a ≤ p, ∀ slots : Fin (2 + a) →
                Fin (Module.finrank Real E),
              |tower alpha k l a (A alpha k l z) slots| < eps := by
  classical
  let : NormedAddCommGroup (E →L[Real] Real) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace Real (E →L[Real] Real) :=
    ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (E →L[Real] E →L[Real] Real) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace Real (E →L[Real] E →L[Real] Real) :=
    ContinuousLinearMap.toNormedSpace
  dsimp only
  let Lphi := L.subseq hphi
  let A : LiveSlot L inp.pack r → Nat → Nat → E → E :=
    fun alpha k l z =>
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
      let chiK := d.chart (Lphi.φ k)
        (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
      let chiL := d.chart (Lphi.φ l)
        (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
      chiL.inv (stageComparisonMap inp P Lphi r hr k l
        (chiK.hom z) (chart := d.chart))
  let G : LiveSlot L inp.pack r → Nat → Nat → E → E :=
    fun alpha k l w =>
      let Yk := X.obj (Lphi.φ k)
      let Yl := X.obj (Lphi.φ l)
      letI : TopologicalSpace Yk.M := Yk.topology
      letI : ChartedSpace H Yk.M := Yk.charted
      letI : IsManifold I ∞ Yk.M := Yk.smooth
      letI : T2Space Yk.M := Yk.t2
      letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
      letI : MetricSpace Yk.M := (P (Lphi.φ k)).ms
      letI : Nonempty Yk.M := ⟨Yk.basepoint⟩
      letI : TopologicalSpace Yl.M := Yl.topology
      letI : ChartedSpace H Yl.M := Yl.charted
      letI : IsManifold I ∞ Yl.M := Yl.smooth
      letI : T2Space Yl.M := Yl.t2
      letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
      let chiK := d.chart (Lphi.φ k)
        (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
      let chiL := d.chart (Lphi.φ l)
        (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
      let F := stageComparisonMap inp P Lphi r hr k l
        (chart := d.chart)
      chiK.inv
        (Function.invFunOn F (Metric.ball Yk.basepoint T) (chiL.hom w))
  let B : LiveSlot L inp.pack r → Nat →
      E → (E →L[Real] E →L[Real] Real) := fun alpha k =>
    NormalChartFamily.metric d.chart (Lphi.φ k)
      (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
  let Q : LiveSlot L inp.pack r → Nat → Nat →
      E → (E →L[Real] E →L[Real] Real) := fun alpha k l w =>
    _root_.DifferentialGeometry.HCGCompactness.pullbackForm
      (B alpha k (G alpha k l w), fderiv Real (G alpha k l) w)
  let Gamma : LiveSlot L inp.pack r → Nat → E →
      Fin (Module.finrank Real E) → Fin (Module.finrank Real E) →
        Fin (Module.finrank Real E) → Real := fun alpha l z i j m =>
    e.coord m
      (MetricKoszul.raisedKoszulOp
        (B alpha l z) (fderiv Real (B alpha l) z)
        (e i) (e j))
  let tower : (alpha : LiveSlot L inp.pack r) →
      (k l a : Nat) → E →
        (Fin (2 + a) → Fin (Module.finrank Real E)) → Real :=
    fun alpha k l a =>
      iterCovComp (I := 𝓘(Real, E))
        (fun i _ => e i) (Gamma alpha l)
        (fun w slots => (Q alpha k l w - B alpha l w)
          (e (slots 0)) (e (slots 1))) a
  rcases hstage with ⟨hdata, hmetric, hjets, hbase⟩
  have hgap : 0 ≤
      (4 + 8 * Real.sqrt 2) * inp.decay.lambda inp.D 0 :=
    mul_nonneg (by positivity) (inp.decay.lambda_pos inp.hD 0).le
  have hTr : T < r := by linarith
  have hSr : S < r := hST.trans hTr
  have hraw := hdata
  dsimp only [HasSuppConvDataOn] at hraw
  rcases hraw with
    ⟨_hUraw, _hU8, _hC0raw, _hC1raw, _hC01raw, _hC1Uraw,
      _hconvex, _hzero, hbufferData, _hcore, _hgeom, _hlim,
      _hweight, _htrans, _hsmooth⟩
  obtain ⟨eta, heta, hcover⟩ := hbufferData
  have hlocal : ∀ (alpha : LiveSlot L inp.pack r) (a : Fin (p + 1)),
      ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N, ∀ z : E,
        Metric.closedBall z (eta alpha) ⊆ interior (C0 alpha) →
        let Yk := X.obj (Lphi.φ k)
        letI : TopologicalSpace Yk.M := Yk.topology
        letI : ChartedSpace H Yk.M := Yk.charted
        letI : IsManifold I ∞ Yk.M := Yk.smooth
        letI : T2Space Yk.M := Yk.t2
        letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
        letI : MetricSpace Yk.M := (P (Lphi.φ k)).ms
        let chiK := d.chart (Lphi.φ k)
          (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
        chiK.hom z ∈ Lphi.hatSourceBall inp.decay P R k →
          ∀ slots : Fin (2 + (a : Nat)) → Fin (Module.finrank Real E),
            |tower alpha k l a (A alpha k l z) slots| < eps := by
    intro alpha a
    obtain ⟨_hUopen, hC0compact, _hC1compact, hC01, hC1U⟩ :=
      hdata.core_on inp P L r hr d.chart U C0 C1 aInf Jinf Jbarinf alpha
    have hIntU : interior (C0 alpha) ⊆ U alpha :=
      interior_subset.trans (hC01.trans (interior_subset.trans hC1U))
    by_contra htail
    push Not at htail
    choose k hk l hl z hbuffer hrest using htail
    have hrest' : ∀ n,
        let Yk := X.obj (Lphi.φ (k n))
        letI : TopologicalSpace Yk.M := Yk.topology
        letI : ChartedSpace H Yk.M := Yk.charted
        letI : IsManifold I ∞ Yk.M := Yk.smooth
        letI : T2Space Yk.M := Yk.t2
        letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
        letI : MetricSpace Yk.M := (P (Lphi.φ (k n))).ms
        let chiK := d.chart (Lphi.φ (k n))
          (seqCenterD inp.decay P Lphi (k n) (alpha.1 : Nat))
        chiK.hom (z n) ∈ Lphi.hatSourceBall inp.decay P R (k n) ∧
          ∃ slots : Fin (2 + (a : Nat)) → Fin (Module.finrank Real E),
            eps ≤ |tower alpha (k n) (l n) a
              (A alpha (k n) (l n) (z n)) slots| := by
      intro n
      have hn := hrest n
      dsimp only at hn ⊢
      push Not at hn
      exact hn
    have hsource : ∀ n,
        let Yk := X.obj (Lphi.φ (k n))
        letI : TopologicalSpace Yk.M := Yk.topology
        letI : ChartedSpace H Yk.M := Yk.charted
        letI : IsManifold I ∞ Yk.M := Yk.smooth
        letI : T2Space Yk.M := Yk.t2
        letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
        letI : MetricSpace Yk.M := (P (Lphi.φ (k n))).ms
        let chiK := d.chart (Lphi.φ (k n))
          (seqCenterD inp.decay P Lphi (k n) (alpha.1 : Nat))
        chiK.hom (z n) ∈ Lphi.hatSourceBall inp.decay P R (k n) :=
      fun n => (hrest' n).1
    choose slots hbad using fun n => (hrest' n).2
    have hzC0 : ∀ n, z n ∈ C0 alpha := by
      intro n
      exact interior_subset (hbuffer n
        (Metric.mem_closedBall_self (heta alpha).le))
    obtain ⟨zInf, _hzInf, ψ, hψ, hzconv⟩ :=
      hC0compact.tendsto_subseq hzC0
    let kn : Nat → Nat := fun n => k (ψ n)
    let ln : Nat → Nat := fun n => l (ψ n)
    let zn : Nat → E := fun n => z (ψ n)
    let slotn : Nat → (Fin (2 + (a : Nat)) →
        Fin (Module.finrank Real E)) := fun n => slots (ψ n)
    have hkn : Tendsto kn atTop atTop :=
      (tendsto_atTop_mono hk tendsto_id).comp hψ.tendsto_atTop
    have hln : Tendsto ln atTop atTop :=
      (tendsto_atTop_mono hl tendsto_id).comp hψ.tendsto_atTop
    have hzn : Tendsto zn atTop (𝓝 zInf) := by
      change Tendsto (Function.comp z ψ) atTop (nhds zInf)
      exact hzconv
    have hbuffer' : ∀ n, Metric.closedBall (zn n) (eta alpha) ⊆
        interior (C0 alpha) := fun n => hbuffer (ψ n)
    have hsource' : ∀ n,
        let Yk := X.obj (Lphi.φ (kn n))
        letI : TopologicalSpace Yk.M := Yk.topology
        letI : ChartedSpace H Yk.M := Yk.charted
        letI : IsManifold I ∞ Yk.M := Yk.smooth
        letI : T2Space Yk.M := Yk.t2
        letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
        letI : MetricSpace Yk.M := (P (Lphi.φ (kn n))).ms
        (d.chart (Lphi.φ (kn n))
          (seqCenterD inp.decay P Lphi (kn n)
            (alpha.1 : Nat))).hom (zn n) ∈
              Lphi.hatSourceBall inp.decay P R (kn n) := by
      intro n
      simpa only [kn, zn, Lphi] using hsource (ψ n)
    obtain ⟨q, hq, hVopen, hVcompact, hVW, hWint, hstay⟩ :=
      d.source_stay inp P L hr phi hphi U C0 C1 aInf Jinf Jbarinf
        hdata alpha hRS (heta alpha) kn zn zInf hzn hbuffer' hsource'
    let V : Set E := Metric.ball zInf q
    let W : Set E := Metric.ball zInf (2 * q)
    have hstay' : ∀ᶠ n in atTop,
        let Yk := X.obj (Lphi.φ (kn n))
        letI : TopologicalSpace Yk.M := Yk.topology
        letI : ChartedSpace H Yk.M := Yk.charted
        letI : IsManifold I ∞ Yk.M := Yk.smooth
        letI : T2Space Yk.M := Yk.t2
        letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
        letI : MetricSpace Yk.M := (P (Lphi.φ (kn n))).ms
        Set.MapsTo
          (d.chart (Lphi.φ (kn n))
            (seqCenterD inp.decay P Lphi (kn n)
              (alpha.1 : Nat))).hom
          W (Lphi.hatSourceBall inp.decay P S (kn n)) := by
      simpa only [V, W, Lphi] using hstay
    have hAconvW : MapCInfConvOnCompacts W
        (fun n => A alpha (kn n) (ln n)) id := by
      simpa only [A, Lphi] using
        HasStageJetDataOn.chart_conv (I := I) inp P L hr phi hphi
          d.chart Vmetric U C0 C1 aInf Jinf Jbarinf gInf
          ⟨hdata, hmetric, hjets, hbase⟩ S hSr alpha W hWint
          kn ln hkn hln hstay'
    let K : Set E := Metric.closedBall zInf (q / 2)
    have hKcompact : IsCompact K := isCompact_closedBall zInf (q / 2)
    have hKV : K ⊆ V := Metric.closedBall_subset_ball (by linarith)
    obtain ⟨Vout, hVoutOpen, hVoutCompact, hKVout, hGconv, hGcd⟩ :=
      d.inv_chart_conv inp P L hr phi hphi hcomplete hconn
        Vmetric U C0 C1 aInf Jinf Jbarinf gInf
        ⟨hdata, hmetric, hjets, hbase⟩ S T Vrad hST hroom hVr
        alpha V W K hVopen Metric.isOpen_ball hKcompact hKV hVW hWint
        kn ln hkn hln hstay'
    let D : Set E := interior (C0 alpha)
    have hVD : V ⊆ D := by
      intro w hw
      exact hWint (hVW (subset_closure hw))
    have hKD : K ⊆ D := hKV.trans hVD
    have hKinter : K ⊆ Vout ∩ D := fun w hw => ⟨hKVout hw, hKD hw⟩
    obtain ⟨O, hOopen, hKO, hOclosure⟩ :=
      hKcompact.exists_isOpen_closure_subset
        ((hVoutOpen.inter isOpen_interior).mem_nhdsSet.mpr hKinter)
    have hOsubVout : O ⊆ Vout :=
      subset_closure.trans (hOclosure.trans inter_subset_left)
    have hOD : O ⊆ D :=
      subset_closure.trans (hOclosure.trans inter_subset_right)
    have hOclosureVout : closure O ⊆ Vout :=
      hOclosure.trans inter_subset_left
    have hOclosureD : closure O ⊆ D :=
      hOclosure.trans inter_subset_right
    have hOcompact : IsCompact (closure O) :=
      hVoutCompact.of_isClosed_subset isClosed_closure
        (hOclosureVout.trans subset_closure)
    have hGconvO : MapCInfConvOnCompacts O
        (fun n => G alpha (kn n) (ln n)) id := by
      intro C hC hCO p'
      exact hGconv C hC (hCO.trans hOsubVout) p'
    have hGcdO : ∀ᶠ n in atTop,
        ContDiffOn Real (∞ : WithTop ℕ∞)
          (G alpha (kn n) (ln n)) O := by
      filter_upwards [hGcd] with n hn
      exact hn.mono hOsubVout
    have hGmapO : ∀ᶠ n in atTop,
        Set.MapsTo (G alpha (kn n) (ln n)) O D := by
      have hmapClosure : ∀ᶠ n in atTop,
          Set.MapsTo (G alpha (kn n) (ln n)) (closure O) D :=
        hGconv.eventually_mapsTo hOcompact hOclosureVout
          continuous_id.continuousOn isOpen_interior
          (fun w hw => hOclosureD hw)
      filter_upwards [hmapClosure] with n hn
      exact hn.mono subset_closure Subset.rfl
    obtain ⟨Nsm, hNsm⟩ := eventually_atTop.mp (hGcdO.and hGmapO)
    let Gp : Nat → E → E := fun n =>
      if Nsm ≤ n then G alpha (kn n) (ln n) else id
    have hGpconv : MapCInfConvOnCompacts O Gp id := by
      apply hGconvO.congr_eventually hOopen
      · filter_upwards [eventually_atTop.2 ⟨Nsm, fun n hn => hn⟩] with n hn
        intro w _hw
        simp only [Gp, if_pos hn]
      · exact Set.eqOn_refl id O
    have hGpcd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (Gp n) O := by
      intro n
      by_cases hn : Nsm ≤ n
      · simpa only [Gp, if_pos hn] using (hNsm n hn).1
      · simpa only [Gp, if_neg hn] using
          (contDiff_id :
            ContDiff Real (∞ : WithTop ℕ∞) (id : E → E)).contDiffOn
    have hGpmap : ∀ n, Set.MapsTo (Gp n) O D := by
      intro n
      by_cases hn : Nsm ≤ n
      · simpa only [Gp, if_pos hn] using (hNsm n hn).2
      · simp only [Gp, if_neg hn]
        intro w hw
        exact hOD hw
    obtain ⟨hC1V, hgInf, hBconv, hgEquiv⟩ := hmetric alpha
    have hDVmetric : D ⊆ Vmetric alpha :=
      interior_subset.trans
        (hC01.trans (interior_subset.trans hC1V))
    have hOVmetric : O ⊆ Vmetric alpha := hOD.trans hDVmetric
    have hBkconvD : MapCInfConvOnCompacts D
        (fun n => B alpha (kn n)) (gInf alpha) := by
      intro C hC hCD p'
      exact (hBconv.comp_tendsto_atTop hkn) C hC
        (hCD.trans hDVmetric) p'
    have hBlconvO : MapCInfConvOnCompacts O
        (fun n => B alpha (ln n)) (gInf alpha) := by
      intro C hC hCO p'
      exact (hBconv.comp_tendsto_atTop hln) C hC
        (hCO.trans hOVmetric) p'
    have hDU : D ⊆ U alpha := hIntU
    have hBkcd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞)
        (B alpha (kn n)) D := by
      intro n
      let Yk := X.obj (Lphi.φ (kn n))
      let : TopologicalSpace Yk.M := Yk.topology
      let : ChartedSpace H Yk.M := Yk.charted
      let : IsManifold I ∞ Yk.M := Yk.smooth
      let : T2Space Yk.M := Yk.t2
      let : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
      let ck := seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat)
      let chiK := d.chart (Lphi.φ (kn n)) ck
      obtain ⟨hRad, _hmap⟩ :=
        hdata.geom_on inp P L r hr d.chart U C0 C1 aInf Jinf Jbarinf
          (kn n) alpha
      have hsmooth := chiK.metric_cont_diff_on Yk.metric isOpen_interior
        (chiK.smooth_to.mono (hDU.trans hRad))
      simpa only [B, NormalChartFamily.metric, Yk, ck, chiK, Lphi] using
        hsmooth
    have hBlcd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞)
        (B alpha (ln n)) O := by
      intro n
      let Yl := X.obj (Lphi.φ (ln n))
      let : TopologicalSpace Yl.M := Yl.topology
      let : ChartedSpace H Yl.M := Yl.charted
      let : IsManifold I ∞ Yl.M := Yl.smooth
      let : T2Space Yl.M := Yl.t2
      let : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
      let cl := seqCenterD inp.decay P Lphi (ln n) (alpha.1 : Nat)
      let chiL := d.chart (Lphi.φ (ln n)) cl
      obtain ⟨hRad, _hmap⟩ :=
        hdata.geom_on inp P L r hr d.chart U C0 C1 aInf Jinf Jbarinf
          (ln n) alpha
      have hsmooth := chiL.metric_cont_diff_on Yl.metric hOopen
        (chiL.smooth_to.mono ((hOD.trans hDU).trans hRad))
      simpa only [B, NormalChartFamily.metric, Yl, cl, chiL, Lphi] using
        hsmooth
    have hgInfD : ContDiffOn Real (∞ : WithTop ℕ∞) (gInf alpha) D :=
      hgInf.mono hDVmetric
    have hgInfO : ContDiffOn Real (∞ : WithTop ℕ∞) (gInf alpha) O :=
      hgInf.mono hOVmetric
    have hBlco : ∀ n w, w ∈ O → IsCoercive (B alpha (ln n) w) := by
      intro n w hw
      let Yl := X.obj (Lphi.φ (ln n))
      let : TopologicalSpace Yl.M := Yl.topology
      let : ChartedSpace H Yl.M := Yl.charted
      let : IsManifold I ∞ Yl.M := Yl.smooth
      let : T2Space Yl.M := Yl.t2
      let : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
      let cl := seqCenterD inp.decay P Lphi (ln n) (alpha.1 : Nat)
      let chiL := d.chart (Lphi.φ (ln n)) cl
      obtain ⟨hRad, _hmap⟩ :=
        hdata.geom_on inp P L r hr d.chart U C0 C1 aInf Jinf Jbarinf
          (ln n) alpha
      have hco := (d.metric_equiv (Lphi.φ (ln n)) cl).coercive
        Yl.metric (hRad (hDU (hOD hw)))
      simpa only [B, NormalChartFamily.metric, Yl, cl, chiL, Lphi] using hco
    have hgInfCo : ∀ w, w ∈ O → IsCoercive (gInf alpha w) := by
      intro w hw
      refine ⟨1 / 2, by norm_num, ?_⟩
      intro v
      simpa only [pow_two, mul_assoc] using
        (hgEquiv w (hOVmetric hw) v).1
    let Qp : Nat → E → (E →L[Real] E →L[Real] Real) := fun n w =>
      _root_.DifferentialGeometry.HCGCompactness.pullbackForm
        (B alpha (kn n) (Gp n w), fderiv Real (Gp n) w)
    have hQraw := MapCInfConvOnCompacts.pullbackAlong
      hOopen isOpen_interior hGpconv hBkconvD hGpcd
      ((contDiff_id :
        ContDiff Real (∞ : WithTop ℕ∞) (id : E → E)).contDiffOn)
      hBkcd hgInfD hOD hGpmap
    have hQpconv : MapCInfConvOnCompacts O Qp (gInf alpha) := by
      apply hQraw.congr hOopen
      · intro n
        exact Set.eqOn_refl (Qp n) O
      · intro w _hw
        ext u v
        simp only [
          _root_.DifferentialGeometry.HCGCompactness.pullbackForm_apply,
          fderiv_id, ContinuousLinearMap.id_apply, id_eq]
    have hQpcd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (Qp n) O := by
      intro n
      have hBG : ContDiffOn Real (∞ : WithTop ℕ∞)
          (fun w => B alpha (kn n) (Gp n w)) O := by
        simpa only [Function.comp_def] using
          ContDiffOn.comp (hBkcd n) (hGpcd n) (hGpmap n)
      have hDG : ContDiffOn Real (∞ : WithTop ℕ∞)
          (fun w => fderiv Real (Gp n) w) O := by
        intro w hw
        exact (((hGpcd n).contDiffAt (hOopen.mem_nhds hw)).fderiv_right
          (m := (∞ : WithTop ℕ∞)) (by simp)).contDiffWithinAt
      have hpull :=
        (_root_.DifferentialGeometry.HCGCompactness.pullbackForm.contDiff
          (E := E) (F := E)).comp_contDiffOn (hBG.prodMk hDG)
      change ContDiffOn Real (∞ : WithTop ℕ∞)
        (_root_.DifferentialGeometry.HCGCompactness.pullbackForm ∘
          fun w => (B alpha (kn n) (Gp n w), fderiv Real (Gp n) w)) O
      exact hpull
    have htower := metric_tower_conv hOopen e
      (fun n => B alpha (ln n)) Qp (gInf alpha)
      hBlconvO hQpconv hBlcd hQpcd hgInfO hBlco hgInfCo (a : Nat)
    obtain ⟨Ntower, hNtower⟩ :=
      htower K hKcompact hKO 0 (eps / 2) (by positivity)
    obtain ⟨Nclose, hNclose⟩ :=
      hAconvW (closure V) hVcompact hVW 0 (q / 4) (by positivity)
    obtain ⟨Nz, hNz⟩ :=
      Metric.tendsto_atTop.1 hzn (q / 4) (by positivity)
    let n := max (max (max Ntower Nclose) Nz) Nsm
    have hnTower : Ntower ≤ n :=
      ((le_max_left Ntower Nclose).trans (le_max_left _ Nz)).trans
        (le_max_left _ Nsm)
    have hnClose : Nclose ≤ n :=
      ((le_max_right Ntower Nclose).trans (le_max_left _ Nz)).trans
        (le_max_left _ Nsm)
    have hnZ : Nz ≤ n :=
      (le_max_right (max Ntower Nclose) Nz).trans (le_max_left _ Nsm)
    have hnSm : Nsm ≤ n := le_max_right _ _
    have hznDist : dist (zn n) zInf < q / 4 := hNz n hnZ
    have hznV : zn n ∈ V := by
      rw [Metric.mem_ball]
      linarith
    have hAzDist :
        dist (A alpha (kn n) (ln n) (zn n)) (zn n) ≤ q / 4 := by
      have hraw := hNclose n hnClose 0 le_rfl
        (zn n) (subset_closure hznV)
      simpa only [mapDerivNorm, norm_iteratedFDeriv_zero, id_eq,
        dist_eq_norm] using hraw
    have hAnK : A alpha (kn n) (ln n) (zn n) ∈ K := by
      change dist (A alpha (kn n) (ln n) (zn n)) zInf ≤ q / 2
      calc
        dist (A alpha (kn n) (ln n) (zn n)) zInf
            ≤ dist (A alpha (kn n) (ln n) (zn n)) (zn n) +
                dist (zn n) zInf := dist_triangle _ _ _
        _ ≤ q / 4 + q / 4 := add_le_add hAzDist hznDist.le
        _ = q / 2 := by ring
    have hnorm :
        ‖iterCovComp (I := 𝓘(Real, E))
          (fun i _ => e i)
          (fun w i j m =>
            e.coord m
              (MetricKoszul.raisedKoszulOp
                (B alpha (ln n) w) (fderiv Real (B alpha (ln n)) w)
                (e i) (e j)))
          (fun w (slots : Fin 2 → Fin (Module.finrank Real E)) =>
            (Qp n w - B alpha (ln n) w)
            (e (slots 0)) (e (slots 1)))
          (a : Nat) (A alpha (kn n) (ln n) (zn n))‖ ≤ eps / 2 := by
      have hraw := hNtower n hnTower 0 le_rfl
        (A alpha (kn n) (ln n) (zn n)) hAnK
      simp only [mapDerivNorm, norm_iteratedFDeriv_zero] at hraw
      rw [show (fun _ : Fin (2 + (a : Nat)) →
        Fin (Module.finrank Real E) => (0 : Real)) = 0 by rfl, sub_zero] at hraw
      exact hraw
    have hcomponent :
        ‖tower alpha (kn n) (ln n) a
          (A alpha (kn n) (ln n) (zn n)) (slotn n)‖ ≤ eps / 2 := by
      have hpi := (norm_le_pi_norm
        (iterCovComp (I := 𝓘(Real, E))
          (fun i _ => e i)
          (fun w i j m =>
            e.coord m
              (MetricKoszul.raisedKoszulOp
                (B alpha (ln n) w) (fderiv Real (B alpha (ln n)) w)
                (e i) (e j)))
          (fun w (slots : Fin 2 → Fin (Module.finrank Real E)) =>
            (Qp n w - B alpha (ln n) w)
            (e (slots 0)) (e (slots 1)))
          (a : Nat) (A alpha (kn n) (ln n) (zn n))) (slotn n)).trans hnorm
      simpa only [Qp, Gp, if_pos hnSm, tower, Gamma, Q] using hpi
    have hsmall :
        |tower alpha (kn n) (ln n) a
          (A alpha (kn n) (ln n) (zn n)) (slotn n)| < eps := by
      have habs :
          |tower alpha (kn n) (ln n) a
            (A alpha (kn n) (ln n) (zn n)) (slotn n)| ≤ eps / 2 := by
        simpa only [Real.norm_eq_abs] using hcomponent
      linarith
    have hbadn := hbad (ψ n)
    have hbadn' : eps ≤
        |tower alpha (kn n) (ln n) a
          (A alpha (kn n) (ln n) (zn n)) (slotn n)| := by
      simpa only [kn, ln, zn, slotn] using hbadn
    exact (not_lt_of_ge hbadn') hsmall
  choose Naa hNaa using hlocal
  let := Fintype.ofFinite (LiveSlot L inp.pack r)
  let Nalpha : LiveSlot L inp.pack r → Nat := fun alpha =>
    Finset.univ.sup (fun a : Fin (p + 1) => Naa alpha a)
  refine ⟨eta, heta, Finset.univ.sup Nalpha, ?_⟩
  intro k hk l hl
  let Yk := X.obj (Lphi.φ k)
  let : TopologicalSpace Yk.M := Yk.topology
  let : ChartedSpace H Yk.M := Yk.charted
  let : IsManifold I ∞ Yk.M := Yk.smooth
  let : T2Space Yk.M := Yk.t2
  let : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
  let : MetricSpace Yk.M := (P (Lphi.φ k)).ms
  intro y hy
  have hyBig : y ∈ Lphi.hatSourceBall inp.decay P r k :=
    cball_subset_of_le (hRS.trans (hST.trans hTr)).le hy
  obtain ⟨alpha, z, hzy, hzbuffer⟩ := hcover k y hyBig
  let chiK := d.chart (Lphi.φ k)
    (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
  have hzy' : chiK.hom z = y := by
    change NormalChartFamily.hom d.chart (L.φ (phi k))
      (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat)) z = y
    exact hzy
  have hzSource : chiK.hom z ∈
      Lphi.hatSourceBall inp.decay P R k := by
    simpa only [hzy'] using hy
  have hAlpha : Nalpha alpha ≤ Finset.univ.sup Nalpha :=
    Finset.le_sup (f := Nalpha) (Finset.mem_univ alpha)
  have hkAlpha : Nalpha alpha ≤ k := hAlpha.trans hk
  have hlAlpha : Nalpha alpha ≤ l := hAlpha.trans hl
  refine ⟨alpha, z, hzy', hzbuffer, ?_⟩
  intro a ha slots
  let afin : Fin (p + 1) := ⟨a, Nat.lt_succ_iff.mpr ha⟩
  have hAfin : Naa alpha afin ≤ Nalpha alpha :=
    Finset.le_sup (f := fun b : Fin (p + 1) => Naa alpha b)
      (Finset.mem_univ afin)
  have hkAfin : Naa alpha afin ≤ k := hAfin.trans hkAlpha
  have hlAfin : Naa alpha afin ≤ l := hAfin.trans hlAlpha
  simpa only [chiK, Yk, Lphi, afin] using
    hNaa alpha afin k hkAfin l hlAfin z hzbuffer hzSource slots

end HCGCompactness
end DifferentialGeometry
