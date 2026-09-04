import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.LocalPullbackBounds.BoundedGeometry
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricDerivativeBounds.StageJet
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.InverseCovariantDerivativeComponents.BoundedGeometry
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.MappingControl.LocalDiffeomorphism
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.Tower

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Set Filter Topology
open Bundle Manifold
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

local instance higherDualNormedAddCommGroup : NormedAddCommGroup (E →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance higherDualNormedSpace : NormedSpace Real (E →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace

local instance higherBilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance higherBilinearNormedSpace :
    NormedSpace Real (E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace

theorem BoundedGeometryNormalChartData.cov_comp_tail
    (inp : MetricCompactCore (I := I) X)
    (d : BoundedGeometryNormalChartData (I := I) X inp.decay)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (Vmetric U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (gInf : LiveSlot L inp.pack r →
      E → (E →L[Real] E →L[Real] Real))
    (hstage : HasStageJetDataOn (I := I) inp P L hr phi hphi
      d.chart Vmetric U C0 C1 aInf Jinf Jbarinf gInf)
    {R S : Real} (hRS : R < S) (hSr : S < r)
    (e : Module.Basis (Fin (Module.finrank Real E)) Real E)
    (p : Nat) (eps : Real) (heps : 0 < eps) :
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
    let B : LiveSlot L inp.pack r → Nat →
        E → (E →L[Real] E →L[Real] Real) := fun alpha k =>
      d.chartMetric (Lphi.φ k)
        (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
    let Q : LiveSlot L inp.pack r → Nat → Nat →
        E → (E →L[Real] E →L[Real] Real) := fun alpha k l z =>
      _root_.DifferentialGeometry.CheegerGromovCompactness.pullbackForm
        (B alpha l (A alpha k l z), fderiv Real (A alpha k l) z)
    let Gamma : LiveSlot L inp.pack r → Nat → E →
        Fin (Module.finrank Real E) → Fin (Module.finrank Real E) →
          Fin (Module.finrank Real E) → Real := fun alpha k z i j m =>
      e.coord m
        (MetricKoszul.raisedKoszulOp
          (B alpha k z) (fderiv Real (B alpha k) z)
          (e i) (e j))
    let tower : (alpha : LiveSlot L inp.pack r) →
        (k l a : Nat) → E →
          (Fin (2 + a) → Fin (Module.finrank Real E)) → Real :=
      fun alpha k l a =>
        iterCovComp (I := 𝓘(Real, E))
          (fun i _ => e i) (Gamma alpha k)
          (fun z slots => (Q alpha k l z - B alpha k z)
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
            ∀ a ≤ p, ∀ slots : Fin (2 + a) → Fin (Module.finrank Real E),
              |tower alpha k l a z slots| < eps := by
  classical
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
  let B : LiveSlot L inp.pack r → Nat →
      E → (E →L[Real] E →L[Real] Real) := fun alpha k =>
    d.chartMetric (Lphi.φ k)
      (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
  let Q : LiveSlot L inp.pack r → Nat → Nat →
      E → (E →L[Real] E →L[Real] Real) := fun alpha k l z =>
    _root_.DifferentialGeometry.CheegerGromovCompactness.pullbackForm
      (B alpha l (A alpha k l z), fderiv Real (A alpha k l) z)
  let Gamma : LiveSlot L inp.pack r → Nat → E →
      Fin (Module.finrank Real E) → Fin (Module.finrank Real E) →
        Fin (Module.finrank Real E) → Real := fun alpha k z i j m =>
    e.coord m
      (MetricKoszul.raisedKoszulOp
        (B alpha k z) (fderiv Real (B alpha k) z)
        (e i) (e j))
  let tower : (alpha : LiveSlot L inp.pack r) →
      (k l a : Nat) → E →
        (Fin (2 + a) → Fin (Module.finrank Real E)) → Real :=
    fun alpha k l a =>
      iterCovComp (I := 𝓘(Real, E))
        (fun i _ => e i) (Gamma alpha k)
        (fun z slots => (Q alpha k l z - B alpha k z)
          (e (slots 0)) (e (slots 1))) a
  rcases hstage with ⟨hdata, hmetric, hjets, hbase⟩
  have hshape := hdata
  dsimp only [HasSupportedCenterMapConvergenceOn] at hshape
  rcases hshape with
    ⟨_hopen, _hU8, _hC0compact, _hC1compact, _hC01, _hC1U,
      _hconvex, _hzero, hbuffer, _hcore, _hgeom, _hrest⟩
  obtain ⟨eta, heta, hcover⟩ := hbuffer
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
            |tower alpha k l a z slots| < eps := by
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
            eps ≤ |tower alpha (k n) (l n) a (z n) slots| := by
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
        (d.chart (Lphi.φ (k n))
          (seqCenterD inp.decay P Lphi (k n) (alpha.1 : Nat))).hom (z n) ∈
            Lphi.hatSourceBall inp.decay P R (k n) :=
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
      change Tendsto (Function.comp z ψ) atTop (𝓝 zInf)
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
          (seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat))).hom (zn n) ∈
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
            (seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat))).hom
          W (Lphi.hatSourceBall inp.decay P S (kn n)) := by
      simpa only [V, W, Lphi] using hstay
    have hQconv : MapCInfConvergenceOnCompacts V
        (fun n => Q alpha (kn n) (ln n)) (gInf alpha) := by
      have hraw := HasStageJetDataOn.pb_convergence (I := I) inp P L hr phi hphi
        d.chart Vmetric U C0 C1 aInf Jinf Jbarinf gInf
        ⟨hdata, hmetric, hjets, hbase⟩ S hSr alpha V W
        hVopen hVcompact hVW hWint kn ln hkn hln hstay'
      with_unfolding_all
        exact hraw
    let D : Set E := interior (C0 alpha)
    have hDopen : IsOpen D := isOpen_interior
    obtain ⟨hC1V, hgInf, hBconv, hgEquiv⟩ := hmetric alpha
    have hDVmetric : D ⊆ Vmetric alpha :=
      interior_subset.trans (hC01.trans (interior_subset.trans hC1V))
    have hWD : W ⊆ D := hWint
    have hVD : V ⊆ D := subset_closure.trans (hVW.trans hWD)
    have hclosureD : closure V ⊆ D := hVW.trans hWD
    have hVU : V ⊆ U alpha := hVD.trans hIntU
    have hGconvD : MapCInfConvergenceOnCompacts D
        (fun n => B alpha (kn n)) (gInf alpha) := by
      intro K hK hKD p'
      exact (hBconv.comp_tendsto_atTop hkn) K hK
        (hKD.trans hDVmetric) p'
    have hGconvV : MapCInfConvergenceOnCompacts V
        (fun n => B alpha (kn n)) (gInf alpha) := by
      intro K hK hKV p'
      exact hGconvD K hK (hKV.trans hVD) p'
    have hBcd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞)
        (B alpha (kn n)) V := by
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
      have hsmooth := chiK.metric_cont_diff_on Yk.metric hVopen
        (chiK.smooth_to.mono (hVU.trans hRad))
      simpa only [B, BoundedGeometryNormalChartData.chartMetric, Yk, ck, chiK, Lphi] using hsmooth
    have hBco : ∀ n z, z ∈ V → IsCoercive (B alpha (kn n) z) := by
      intro n z hz
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
      have hEquiv : chiK.MetricEquivOn Yk.metric (U alpha) := by
        intro w hw v
        exact d.metric_equiv (Lphi.φ (kn n)) ck w (hRad hw) v
      simpa only [B, BoundedGeometryNormalChartData.chartMetric, Yk, ck, chiK, Lphi] using
        hEquiv.coercive Yk.metric (hVU hz)
    have hgInfV : ContDiffOn Real (∞ : WithTop ℕ∞) (gInf alpha) V :=
      hgInf.mono (hVD.trans hDVmetric)
    have hgInfCo : ∀ z, z ∈ V → IsCoercive (gInf alpha z) := by
      intro z hz
      refine ⟨1 / 2, by norm_num, ?_⟩
      intro v
      simpa only [pow_two, mul_assoc] using
        (hgEquiv z (hDVmetric (hVD hz)) v).1
    obtain ⟨rho, hrho, hthick⟩ :=
      hVcompact.exists_cthickening_subset_open hDopen hclosureD
    have hAconvW : MapCInfConvergenceOnCompacts W
        (fun n => A alpha (kn n) (ln n)) id := by
      simpa only [A, Lphi] using
        HasStageJetDataOn.chart_convergence (I := I) inp P L hr phi hphi
          d.chart Vmetric U C0 C1 aInf Jinf Jbarinf gInf
          ⟨hdata, hmetric, hjets, hbase⟩ S hSr alpha W hWint
          kn ln hkn hln hstay'
    obtain ⟨Nclose, hNclose⟩ :=
      hAconvW (closure V) hVcompact hVW 0 (rho / 2) (by positivity)
    obtain ⟨Njet, hNjet⟩ := hjets S hSr 0 1 (by norm_num)
    have hgood : ∀ᶠ n in atTop,
        ContDiffOn Real (∞ : WithTop ℕ∞) (A alpha (kn n) (ln n)) V ∧
        Set.MapsTo (A alpha (kn n) (ln n)) V D ∧
        ContDiffOn Real (∞ : WithTop ℕ∞) (B alpha (ln n)) D := by
      filter_upwards [hkn.eventually_ge_atTop Njet,
        hln.eventually_ge_atTop Njet, hstay',
        eventually_atTop.2 ⟨Nclose, hNclose⟩] with n hnk hnl hsrc hclose
      have hAcd : ContDiffOn Real (∞ : WithTop ℕ∞)
          (A alpha (kn n) (ln n)) V := by
        intro z hzV
        have hzW : z ∈ W := hVW (subset_closure hzV)
        have hzInt : z ∈ interior (C0 alpha) := hWint hzW
        have hjet := hNjet (kn n) hnk (ln n) hnl alpha z
          (interior_subset hzInt)
        have hsrcz := hsrc hzW
        simpa only [A, Lphi] using (hjet hzInt hsrcz).2.1.contDiffWithinAt
      have hAmap : Set.MapsTo (A alpha (kn n) (ln n)) V D := by
        intro z hzV
        have hzClosure : z ∈ closure V := subset_closure hzV
        have hzero := hclose 0 le_rfl z hzClosure
        have hdist : dist (A alpha (kn n) (ln n) z) z ≤ rho / 2 := by
          simpa only [mapDerivNorm, norm_iteratedFDeriv_zero, id_eq,
            dist_eq_norm, A, Lphi] using hzero
        have hdistRho : dist (A alpha (kn n) (ln n) z) z < rho := by
          linarith
        exact hthick (Metric.mem_cthickening_of_dist_le
          (A alpha (kn n) (ln n) z) z rho
          (closure V) hzClosure hdistRho.le)
      have hBtarget : ContDiffOn Real (∞ : WithTop ℕ∞)
          (B alpha (ln n)) D := by
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
        have hsmooth := chiL.metric_cont_diff_on Yl.metric hDopen
          (chiL.smooth_to.mono (hIntU.trans hRad))
        simpa only [B, BoundedGeometryNormalChartData.chartMetric, Yl, cl, chiL, Lphi] using hsmooth
      exact ⟨hAcd, hAmap, hBtarget⟩
    obtain ⟨Nsm, hNsm⟩ := eventually_atTop.mp hgood
    have hQsmooth : ∀ n, Nsm ≤ n →
        ContDiffOn Real (∞ : WithTop ℕ∞)
          (Q alpha (kn n) (ln n)) V := by
      intro n hn
      have hBAc : ContDiffOn Real (∞ : WithTop ℕ∞)
          (fun z => B alpha (ln n) (A alpha (kn n) (ln n) z)) V := by
        simpa only [Function.comp_def] using
          ContDiffOn.comp (hNsm n hn).2.2 (hNsm n hn).1 (hNsm n hn).2.1
      have hDAc : ContDiffOn Real (∞ : WithTop ℕ∞)
          (fun z => fderiv Real (A alpha (kn n) (ln n)) z) V := by
        intro z hz
        exact ((((hNsm n hn).1).contDiffAt (hVopen.mem_nhds hz)).fderiv_right
          (m := (∞ : WithTop ℕ∞)) (by simp)).contDiffWithinAt
      have hpull :=
        (_root_.DifferentialGeometry.CheegerGromovCompactness.pullbackForm.contDiff
          (E := E) (F := E)).comp_contDiffOn (hBAc.prodMk hDAc)
      with_unfolding_all
        exact hpull
    let Qp : Nat → E → (E →L[Real] E →L[Real] Real) := fun n =>
      if Nsm ≤ n then Q alpha (kn n) (ln n) else gInf alpha
    have hQpconv : MapCInfConvergenceOnCompacts V Qp (gInf alpha) := by
      apply hQconv.congr_eventually hVopen
      · filter_upwards [eventually_atTop.2 ⟨Nsm, fun n hn => hn⟩] with n hn
        intro z _hz
        simp only [Qp, if_pos hn]
      · exact Set.eqOn_refl (gInf alpha) V
    have hQpcd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (Qp n) V := by
      intro n
      by_cases hn : Nsm ≤ n
      · simpa only [Qp, if_pos hn] using hQsmooth n hn
      · simpa only [Qp, if_neg hn] using hgInfV
    have htower := metric_tower_convergence hVopen e
      (fun n => B alpha (kn n)) Qp (gInf alpha)
      hGconvV hQpconv hBcd hQpcd hgInfV hBco hgInfCo (a : Nat)
    let K : Set E := Metric.closedBall zInf (q / 2)
    have hKcompact : IsCompact K := isCompact_closedBall zInf (q / 2)
    have hKV : K ⊆ V := Metric.closedBall_subset_ball (by linarith)
    obtain ⟨Ntower, hNtower⟩ :=
      htower K hKcompact hKV 0 (eps / 2) (by positivity)
    obtain ⟨Nz, hNz⟩ := Metric.tendsto_atTop.1 hzn (q / 2) (by positivity)
    let n := max (max Ntower Nz) Nsm
    have hnTower : Ntower ≤ n :=
      (le_max_left Ntower Nz).trans (le_max_left _ _)
    have hnZ : Nz ≤ n :=
      (le_max_right Ntower Nz).trans (le_max_left _ _)
    have hnSm : Nsm ≤ n := le_max_right _ _
    have hznK : zn n ∈ K := by
      change dist (zn n) zInf ≤ q / 2
      exact (hNz n hnZ).le
    have hnorm :
        ‖iterCovComp (I := 𝓘(Real, E))
          (fun i _ => e i)
          (fun z i j m =>
            e.coord m
              (MetricKoszul.raisedKoszulOp
                (B alpha (kn n) z) (fderiv Real (B alpha (kn n)) z)
                (e i) (e j)))
          (fun z (slots : Fin 2 → Fin (Module.finrank Real E)) =>
            (Qp n z - B alpha (kn n) z)
            (e (slots 0)) (e (slots 1)))
          (a : Nat) (zn n)‖ ≤ eps / 2 := by
      have hraw := hNtower n hnTower 0 le_rfl (zn n) hznK
      simp only [mapDerivNorm, norm_iteratedFDeriv_zero] at hraw
      rw [show (fun _ : Fin (2 + (a : Nat)) →
        Fin (Module.finrank Real E) => (0 : Real)) = 0 by rfl, sub_zero] at hraw
      exact hraw
    have hcomponent :
        ‖tower alpha (kn n) (ln n) a (zn n) (slotn n)‖ ≤ eps / 2 := by
      have hpi := (norm_le_pi_norm
        (iterCovComp (I := 𝓘(Real, E))
          (fun i _ => e i)
          (fun z i j m =>
            e.coord m
              (MetricKoszul.raisedKoszulOp
                (B alpha (kn n) z) (fderiv Real (B alpha (kn n)) z)
                (e i) (e j)))
          (fun z (slots : Fin 2 → Fin (Module.finrank Real E)) =>
            (Qp n z - B alpha (kn n) z)
            (e (slots 0)) (e (slots 1)))
          (a : Nat) (zn n)) (slotn n)).trans hnorm
      simpa only [Qp, if_pos hnSm, tower, Gamma] using hpi
    have hsmall :
        |tower alpha (kn n) (ln n) a (zn n) (slotn n)| < eps := by
      have habs :
          |tower alpha (kn n) (ln n) a (zn n) (slotn n)| ≤ eps / 2 := by
        simpa only [Real.norm_eq_abs] using hcomponent
      linarith
    have hbadn := hbad (ψ n)
    have hbadn' :
        eps ≤ |tower alpha (kn n) (ln n) a (zn n) (slotn n)| := by
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
    cball_subset_of_le (hRS.trans hSr).le hy
  obtain ⟨alpha, z, hzy, hzbuffer⟩ := hcover k y hyBig
  let chiK := d.chart (Lphi.φ k)
    (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
  have hzy' : chiK.hom z = y := by
    with_unfolding_all
      exact hzy
  have hzSource : chiK.hom z ∈ Lphi.hatSourceBall inp.decay P R k := by
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

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private theorem chart_norm_eq
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I M) {x : M}
    (c : NormalBallChart (I := I) x) :
    letI : LocallyCompactSpace c.ball := c.ball.2.locallyCompactSpace
    letI : SigmaCompactSpace c.ball := inferInstance
    ∀ (G : SmoothRiemannianMetric I M) (a : Nat) (z : c.ball),
      metricDerivNorm (I := 𝓘(Real, E)) a
          (c.localMetric G) (c.localMetric g) (c.localMetric g) z =
        metricDerivNorm (I := I) a G g g (c.hom (z : E)) := by
  let : LocallyCompactSpace c.ball := c.ball.2.locallyCompactSpace
  let : SigmaCompactSpace c.ball := inferInstance
  let : SigmaCompactSpace c.image := by
    apply isSigmaCompact_univ_iff.mp
    have hrange : Set.range (c.ballDiffeo : c.ball → c.image) = Set.univ :=
      Set.range_eq_univ.mpr c.ballDiffeo.surjective
    rw [← hrange]
    exact isSigmaCompact_range c.ballDiffeo.continuous
  intro G a z
  unfold NormalBallChart.localMetric
  rw [metricDerivNorm_pullbackCross (I := 𝓘(Real, E)) (J := I)]
  rw [metricDerivNorm_restrictOpen (I := I) G g g]
  congr 1

private noncomputable def flatApproximationModelMetric :
    SmoothRiemannianMetric 𝓘(Real, E) E where
  inner := (riemannianMetricVectorSpace E).inner
  symm := (riemannianMetricVectorSpace E).symm
  pos := (riemannianMetricVectorSpace E).pos
  isVonNBounded := (riemannianMetricVectorSpace E).isVonNBounded
  contMDiff := (riemannianMetricVectorSpace E).contMDiff.of_le le_top

omit [CompleteSpace E] [NeZero (Module.finrank Real E)] [I.Boundaryless] in
private theorem normalBallLocalMetric_inner_model
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I M) {x : M}
    (c : NormalBallChart (I := I) x) (z : c.ball) (u v : E) :
    (c.localMetric g).inner z
        (show TangentSpace (modelWithCornersSelf Real E) z from u)
        (show TangentSpace (modelWithCornersSelf Real E) z from v) =
      c.metric g z u v := by
  have hu :
      (tangentSpaceModelContinuousLinearEquiv
        (I := modelWithCornersSelf Real E) z).symm u =
        (show TangentSpace (modelWithCornersSelf Real E) z from u) := by
    apply (tangentSpaceModelContinuousLinearEquiv
      (I := modelWithCornersSelf Real E) z).injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    with_unfolding_all
      rfl
  have hv :
      (tangentSpaceModelContinuousLinearEquiv
        (I := modelWithCornersSelf Real E) z).symm v =
        (show TangentSpace (modelWithCornersSelf Real E) z from v) := by
    apply (tangentSpaceModelContinuousLinearEquiv
      (I := modelWithCornersSelf Real E) z).injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    with_unfolding_all
      rfl
  have hinner := c.localMetric_inner g z u v
  rw [hu, hv] at hinner
  exact hinner

omit [NeZero (Module.finrank Real E)] in
omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] in
private theorem chart_pull_coeff
    {Mk Ml : Type u}
    [TopologicalSpace Mk] [ChartedSpace H Mk] [IsManifold I ∞ Mk]
    [TopologicalSpace Ml] [ChartedSpace H Ml] [IsManifold I ∞ Ml]
    (gl : SmoothRiemannianMetric I Ml)
    {ck0 : Mk} {cl0 : Ml}
    (ck : NormalBallChart (I := I) ck0)
    (cl : NormalBallChart (I := I) cl0)
    (F : Mk → Ml) (G : SmoothRiemannianMetric I Mk)
    (z : E) (hz : z ∈ Metric.ball (0 : E) ck.radius)
    (htarget : F (ck.hom z) ∈ cl.restrictBall.target)
    (hF : MDifferentiableAt I I F (ck.hom z))
    (hG : ∀ v w : TangentSpace I (ck.hom z),
      G.inner (ck.hom z) v w =
        gl.inner (F (ck.hom z))
          (mfderiv I I F (ck.hom z) v)
          (mfderiv I I F (ck.hom z) w))
    (u v : E) :
    let A : E → E := fun q ↦ cl.inv (F (ck.hom q))
    ck.metric G z u v =
      _root_.DifferentialGeometry.CheegerGromovCompactness.pullbackForm
        (cl.metric gl (A z), fderiv Real A z) u v := by
  let A : E → E := fun q ↦ cl.inv (F (ck.hom q))
  dsimp only
  have hzK : z ∈ ck.hom.source := ck.ball_subset hz
  have hK : MDifferentiableAt 𝓘(Real, E) I ck.hom z :=
    ((ck.hom.contMDiffOn_toFun.mdifferentiableOn one_ne_zero z hzK).mdifferentiableAt
      (ck.hom.open_source.mem_nhds hzK))
  have hFK : MDifferentiableAt 𝓘(Real, E) I (F ∘ ck.hom) z :=
    hF.comp z hK
  have hLinv : MDifferentiableAt I 𝓘(Real, E) cl.inv (F (ck.hom z)) := by
    have hraw :=
      ((cl.restrictBall.symm.contMDiffOn_toFun.mdifferentiableOn
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
        (F (ck.hom z)) htarget).mdifferentiableAt
          (cl.restrictBall.open_target.mem_nhds htarget))
    with_unfolding_all
      exact hraw
  have hA : MDifferentiableAt 𝓘(Real, E) 𝓘(Real, E) A z := by
    exact (hLinv.comp z hFK).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun q => rfl)
  have hzL : A z ∈ cl.restrictBall.source := by
    have hraw := cl.restrictBall.map_target htarget
    with_unfolding_all
      exact hraw
  have hL : MDifferentiableAt 𝓘(Real, E) I cl.hom (A z) :=
    ((cl.hom.contMDiffOn_toFun.mdifferentiableOn one_ne_zero
      (A z) (cl.ball_subset (by
        simpa only [NormalBallChart.restrict_ball_source] using hzL))).mdifferentiableAt
        (cl.hom.open_source.mem_nhds
          (cl.ball_subset (by
            simpa only [NormalBallChart.restrict_ball_source] using hzL))))
  have hnear : ∀ᶠ q in nhds z, F (ck.hom q) ∈ cl.restrictBall.target :=
    hFK.continuousAt.eventually (cl.restrictBall.open_target.mem_nhds htarget)
  have heq : cl.hom ∘ A =ᶠ[nhds z] F ∘ ck.hom := by
    filter_upwards [hnear] with q hq
    change cl.hom (cl.inv (F (ck.hom q))) = F (ck.hom q)
    exact cl.restrictBall.right_inv hq
  have hcomp :
      (mfderiv 𝓘(Real, E) I cl.hom (A z)).comp
          (fderiv Real A z) =
        (mfderiv I I F (ck.hom z)).comp
          (mfderiv 𝓘(Real, E) I ck.hom z) := by
    have hderiv := Filter.EventuallyEq.mfderiv_eq
      (I := 𝓘(Real, E)) (I' := I) heq
    rw [mfderiv_comp z hL hA, mfderiv_comp z hF hK] at hderiv
    rw [mfderiv_eq_fderiv] at hderiv
    convert hderiv using 1 ; with_unfolding_all rfl
  have hbase : cl.hom (A z) = F (ck.hom z) := heq.self_of_nhds
  have hu := DFunLike.congr_fun hcomp u
  have hv := DFunLike.congr_fun hcomp v
  rw [ck.metric_apply G, hG]
  rw [_root_.DifferentialGeometry.CheegerGromovCompactness.pullbackForm_apply]
  rw [cl.metric_apply gl, hbase]
  exact congrArg₂
    (fun a b ↦ gl.inner (F (ck.hom z)) a b) hu.symm hv.symm

omit [NeZero (Module.finrank Real E)] in
omit [I.Boundaryless] in
private theorem chart_local_norm_le
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I M) {x : M}
    (c : NormalBallChart (I := I) x) :
    letI : LocallyCompactSpace c.ball := c.ball.2.locallyCompactSpace
    letI : SigmaCompactSpace c.ball := inferInstance
    ∀ (V : TopologicalSpace.Opens E) [T2Space V]
      (hVc : V ≤ c.ball) {z0 : E} (cut : ContDiffBump z0)
      (G : SmoothRiemannianMetric I M)
      (Q B : E → (E →L[Real] E →L[Real] Real))
      (a : Nat) (z : V) {bnd : Real},
      (∀ w ∈ V, cut w = 1) →
      tsupport (cut : E → Real) ⊆ (c.ball : Set E) →
      ContDiffOn Real (∞ : WithTop ℕ∞) B V →
      0 ≤ bnd →
      (∀ w : V, ∀ u v : E,
        ((c.localMetric G).restrictOpenOfSubset
          (I := 𝓘(Real, E)) hVc).inner w u v = Q (w : E) u v) →
      (∀ w : V, ∀ u v : E,
        ((c.localMetric g).restrictOpenOfSubset
          (I := 𝓘(Real, E)) hVc).inner w u v = B (w : E) u v) →
      (∀ w : E, w ∈ V → IsCoercive (B w)) →
      (∀ v : E,
        (1 / 2 : Real) * ‖v‖ ^ 2 ≤ B (z : E) v v ∧
          B (z : E) v v ≤ 2 * ‖v‖ ^ 2) →
      (let e := (stdOrthonormalBasis Real E).toBasis
       let Gamma := fun w i j m ↦ e.coord m
         (MetricKoszul.raisedKoszulOp (B w) (fderiv Real B w)
           (e i) (e j))
       let base := fun w (slots : Fin 2 → Fin (Module.finrank Real E)) ↦
         (Q w - B w) (e (slots 0)) (e (slots 1))
       ∀ q : Nat, ∀ w : V,
         ∀ slots : Fin (2 + q) → Fin (Module.finrank Real E),
           MDifferentiableAt 𝓘(Real, E) 𝓘(Real, Real)
             (fun y : E ↦ iterCovComp (I := 𝓘(Real, E))
               (fun i _ ↦ e i) Gamma base q y slots) (w : E)) →
      (let e := (stdOrthonormalBasis Real E).toBasis
       let Gamma := fun w i j m ↦ e.coord m
         (MetricKoszul.raisedKoszulOp (B w) (fderiv Real B w)
           (e i) (e j))
       let base := fun w (slots : Fin 2 → Fin (Module.finrank Real E)) ↦
         (Q w - B w) (e (slots 0)) (e (slots 1))
       ∀ slots : Fin (2 + a) → Fin (Module.finrank Real E),
         |iterCovComp (I := 𝓘(Real, E)) (fun i _ ↦ e i)
            Gamma base a (z : E) slots| ≤ bnd) →
      metricDerivNorm (I := 𝓘(Real, E)) a
          ((c.localMetric G).restrictOpenOfSubset
            (I := 𝓘(Real, E)) hVc)
          ((c.localMetric g).restrictOpenOfSubset
            (I := 𝓘(Real, E)) hVc)
          ((c.localMetric g).restrictOpenOfSubset
            (I := 𝓘(Real, E)) hVc) z ≤
        Real.sqrt (2 ^ (2 + a)) *
          (Real.sqrt
            (Fintype.card
              (Fin (2 + a) → Fin (Module.finrank Real E)) : Real) * bnd) := by
  let : LocallyCompactSpace c.ball := c.ball.2.locallyCompactSpace
  let : SigmaCompactSpace c.ball := inferInstance
  intro V _ hVc z0 cut G Q B a z bnd
    hcut_one hcut_support hBcd hbnd hQ hB hco hequiv hdiff hcomp
  classical
  let e : Module.Basis (Fin (Module.finrank Real E)) Real E :=
    (stdOrthonormalBasis Real E).toBasis
  let Gamma := fun w i j m ↦ e.coord m
    (MetricKoszul.raisedKoszulOp (B w) (fderiv Real B w)
      (e i) (e j))
  let base := fun w (slots : Fin 2 → Fin (Module.finrank Real E)) ↦
    (Q w - B w) (e (slots 0)) (e (slots 1))
  let Gv := (c.localMetric G).restrictOpenOfSubset
    (I := 𝓘(Real, E)) hVc
  let gv := (c.localMetric g).restrictOpenOfSubset
    (I := 𝓘(Real, E)) hVc
  have hequivV : ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gv.inner z v v ∧
        gv.inner z v v ≤ 2 * ‖v‖ ^ 2 := by
    intro v
    rw [hB z v v]
    exact hequiv v
  apply metricDerivNorm_le_of_iterCovComp_le V Gv gv a z hbnd hequivV
  intro slots
  let frame : Fin (Module.finrank Real E) →
      (w : V) → TangentSpace 𝓘(Real, E) w := fun i _ ↦ e i
  let hframe : IsLocalFrameOn 𝓘(Real, E) E (1 : WithTop ℕ∞)
      frame Set.univ := constantBasis_isLocalFrameOn V e
  have hcut_smooth : ContMDiff 𝓘(Real, E) 𝓘(Real, Real) ∞
      (cut : E → Real) := cut.contDiff.contMDiff
  have hcut_range : ∀ w : E, cut w ∈ Set.Icc (0 : Real) 1 :=
    fun w ↦ ⟨cut.nonneg, cut.le_one⟩
  let gTot : SmoothRiemannianMetric 𝓘(Real, E) E :=
    (flatApproximationModelMetric (E := E)).bumpExtendOpen c.ball (c.localMetric g)
      (cut : E → Real) hcut_smooth hcut_range hcut_support
  have hgv : gv =
      gTot.restrictOpen (I := 𝓘(Real, E)) V := by
    apply SmoothRiemannianMetric.ext_inner
    intro w u v
    rw [SmoothRiemannianMetric.restrictOpen_inner]
    change (c.localMetric g).inner
        (TopologicalSpace.Opens.inclusion hVc w) u v =
      gTot.inner (w : E) u v
    symm
    simpa only [gTot] using
      bumpExtendOpen_eq_gU_on (I := 𝓘(Real, E))
        (flatApproximationModelMetric (E := E)) c.ball (c.localMetric g)
        (cut : E → Real) hcut_smooth hcut_range hcut_support
        (V : Set E) hcut_one hVc (w : E) w.2 u v
  have hchrEq :
      (fun w ↦ Tensor.Coordinates.christoffelSymbolInFrame
        (Geometry.Connection.leviCivitaConnectionOfMetric
          (I := 𝓘(Real, E)) gv) frame hframe w) =
        fun (w : V) ↦ Gamma (w : E) := by
    funext w i j m
    have hfield : DifferentialGeometry.Geometry.Curvature.restrictOpenTangentField
        (I := 𝓘(Real, E)) V
        (fun y : E ↦ (constantModelVectorFieldSection (E := E) (e j)) y) =
          fun y : V ↦ (show TangentSpace 𝓘(Real, E) y from e j) := by
      funext y
      rw [DifferentialGeometry.Geometry.Curvature.restrictOpenTangentField_apply]
      with_unfolding_all
        rfl
    have hres := DifferentialGeometry.Geometry.Curvature.metricCov_restrictOpen_globalSection
      (I := 𝓘(Real, E)) gTot V
      (constantModelVectorFieldSection (E := E) (e j)) w (e i)
    rw [hfield] at hres
    have hres' :
        ((Geometry.Connection.leviCivitaConnectionOfMetric
            (I := 𝓘(Real, E)) gv (frame j) w) (e i)) =
          ((Geometry.Connection.leviCivitaConnectionOfMetric
            (I := 𝓘(Real, E)) gTot (fun _ : E ↦ e j) (w : E)) (e i)) := by
      rw [hgv]
      have hconst : (fun y : E => (constantModelVectorFieldSection (E := E) (e j)) y) =
          fun _ : E => e j := by
        funext y
        with_unfolding_all
          rfl
      rw [hconst] at hres
      simpa only [DifferentialGeometry.Geometry.Curvature.metricCov, frame] using hres
    have hEq :
        (fun y : E ↦ gTot.inner y) =ᶠ[nhds (w : E)] B := by
      filter_upwards [V.2.mem_nhds w.2] with y hy
      apply ContinuousLinearMap.ext
      intro u
      apply ContinuousLinearMap.ext
      intro v
      calc
        gTot.inner y u v =
            (c.localMetric g).inner
              (TopologicalSpace.Opens.inclusion hVc ⟨y, hy⟩) u v := by
          simpa only [gTot] using
            bumpExtendOpen_eq_gU_on (I := 𝓘(Real, E))
              (flatApproximationModelMetric (E := E)) c.ball (c.localMetric g)
              (cut : E → Real) hcut_smooth hcut_range hcut_support
              (V : Set E) hcut_one hVc y hy u v
        _ = B y u v := hB ⟨y, hy⟩ u v
    have hBdiff : DifferentiableAt Real B (w : E) :=
      ((hBcd.contDiffAt (V.2.mem_nhds w.2)).differentiableAt (by simp))
    have hcov :
        ((Geometry.Connection.leviCivitaConnectionOfMetric
            (I := 𝓘(Real, E)) gv (frame j) w) (frame i w)) =
          MetricKoszul.koszulVec (hco (w : E) w.2)
            (fderiv Real B (w : E)) (e i) (e j) := by
      rw [hres']
      exact Geometry.Connection.const_cov_eq_nhds
        gTot B hEq hBdiff (hco (w : E) w.2) (e i) (e j)
    have hbasis : hframe.toBasisAt (Set.mem_univ w) = e := by
      ext q
      rw [hframe.toBasisAt_coe]
      with_unfolding_all
        rfl
    change hframe.coeff m w _ = _
    rw [hcov]
    simp only [IsLocalFrameOn.coeff, Set.mem_univ, dite_true, hbasis]
    exact congrArg (e.coord m)
      (MetricKoszul.raisedKoszulOp_eq (hco (w : E) w.2)
        (fderiv Real B (w : E)) (e i) (e j)).symm
  have hbaseEq :
      frameComp0S (I := 𝓘(Real, E))
          (Tensor0SBundle.metricTensorField (I := 𝓘(Real, E)) Gv -
            Tensor0SBundle.metricTensorField (I := 𝓘(Real, E)) gv) frame =
        fun (w : V) ↦ base (w : E) := by
    funext w s
    change Gv.inner w (e (s 0)) (e (s 1)) -
        gv.inner w (e (s 0)) (e (s 1)) =
      (Q (w : E) - B (w : E)) (e (s 0)) (e (s 1))
    rw [hQ w (e (s 0)) (e (s 1)), hB w (e (s 0)) (e (s 1))]
    rfl
  have hres := DifferentialGeometry.PDE.RicciFlow.iterCovComp_restrict
    V (fun i ↦ e i) Gamma base hdiff a z slots
  calc
    |iterCovComp (I := 𝓘(Real, E)) (M := V)
        (fun i _ ↦ (stdOrthonormalBasis Real E).toBasis i)
        (fun w ↦ Tensor.Coordinates.christoffelSymbolInFrame
          (Geometry.Connection.leviCivitaConnectionOfMetric
            (I := 𝓘(Real, E)) gv)
          (fun i (_ : V) ↦ (stdOrthonormalBasis Real E).toBasis i)
          (constantBasis_isLocalFrameOn V
            (stdOrthonormalBasis Real E).toBasis) w)
        (frameComp0S (I := 𝓘(Real, E))
          (Tensor0SBundle.metricTensorField (I := 𝓘(Real, E)) Gv -
            Tensor0SBundle.metricTensorField (I := 𝓘(Real, E)) gv)
          (fun i (_ : V) ↦ (stdOrthonormalBasis Real E).toBasis i))
        a z slots| =
      |iterCovComp (I := 𝓘(Real, E)) (M := V)
        (fun i _ ↦ e i) (fun w ↦ Gamma (w : E))
        (fun w ↦ base (w : E)) a z slots| := by
          simp only [e, frame, hchrEq, hbaseEq]
    _ = |iterCovComp (I := 𝓘(Real, E)) (fun i _ ↦ e i)
        Gamma base a (z : E) slots| := congrArg abs hres
    _ ≤ bnd := by simpa only [e, Gamma, base] using hcomp slots

theorem BoundedGeometryNormalChartData.fwd_norm_tail
    (inp : MetricCompactCore (I := I) X)
    (d : BoundedGeometryNormalChartData (I := I) X inp.decay)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (Vmetric U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (gInf : LiveSlot L inp.pack r →
      E → (E →L[Real] E →L[Real] Real))
    (hstage : HasStageJetDataOn (I := I) inp P L hr phi hphi
      d.chart Vmetric U C0 C1 aInf Jinf Jbarinf gInf)
    {R S : Real} (hRS : R < S) (hSr : S < r)
    (p : Nat) (eps : Real) (heps : 0 < eps) :
    ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N,
      let Lphi := L.subseq hphi
      let Yk := X.obj (Lphi.φ k)
      let Yl := X.obj (Lphi.φ l)
      letI : TopologicalSpace Yk.M := Yk.topology
      letI : ChartedSpace H Yk.M := Yk.charted
      letI : IsManifold I ∞ Yk.M := Yk.smooth
      letI : SigmaCompactSpace Yk.M := Yk.sigmaCompact
      letI : T2Space Yk.M := Yk.t2
      letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
      letI : MetricSpace Yk.M := (P (Lphi.φ k)).ms
      letI : TopologicalSpace Yl.M := Yl.topology
      letI : ChartedSpace H Yl.M := Yl.charted
      letI : IsManifold I ∞ Yl.M := Yl.smooth
      letI : SigmaCompactSpace Yl.M := Yl.sigmaCompact
      letI : T2Space Yl.M := Yl.t2
      letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
      let F := stageComparisonMap inp P Lphi r hr k l
        (chart := d.chart)
      ∀ (G : SmoothRiemannianMetric I Yk.M),
        (∀ y ∈ Lphi.hatSourceBall inp.decay P S k,
          ∀ v w : TangentSpace I y,
            G.inner y v w =
              Yl.metric.inner (F y) (mfderiv I I F y v)
                (mfderiv I I F y w)) →
        ∀ a ≤ p, ∀ y ∈ Lphi.hatSourceBall inp.decay P R k,
          metricDerivNorm (I := I) a G Yk.metric Yk.metric y ≤ eps := by
  classical
  let e : Module.Basis (Fin (Module.finrank Real E)) Real E :=
    (stdOrthonormalBasis Real E).toBasis
  let fac : Fin (p + 1) → Real := fun a ↦
    Real.sqrt (2 ^ (2 + (a : Nat))) *
      Real.sqrt
        (Fintype.card
          (Fin (2 + (a : Nat)) → Fin (Module.finrank Real E)) : Real)
  let Cmax : Real := Finset.univ.sup' Finset.univ_nonempty fac
  have hfac_nonneg : ∀ a, 0 ≤ fac a := by
    intro a
    dsimp only [fac]
    positivity
  have hfac_le : ∀ a, fac a ≤ Cmax := by
    intro a
    exact Finset.le_sup' fac (Finset.mem_univ a)
  have hCmax_nonneg : 0 ≤ Cmax := by
    let a0 : Fin (p + 1) := ⟨0, Nat.zero_lt_succ p⟩
    exact (hfac_nonneg a0).trans (hfac_le a0)
  let epsComp := eps / (Cmax + 1)
  have hden : 0 < Cmax + 1 := by linarith
  have hepsComp : 0 < epsComp := div_pos heps hden
  have hbudget : ∀ a, fac a * epsComp ≤ eps := by
    intro a
    refine (mul_le_mul_of_nonneg_right (hfac_le a) hepsComp.le).trans ?_
    dsimp only [epsComp]
    rw [← mul_div_assoc, div_le_iff₀ hden]
    nlinarith
  obtain ⟨eta, heta, Ncomp, hcomp⟩ :=
    d.cov_comp_tail inp P L hr phi hphi
      Vmetric U C0 C1 aInf Jinf Jbarinf gInf hstage
      hRS hSr e p epsComp hepsComp
  obtain ⟨Njet, hjet⟩ := hstage.2.2.1 S hSr 0 1 (by norm_num)
  obtain ⟨Nloc, hloc⟩ :=
    hstage.hloc_tail inp P L hr phi hphi d.chart
      Vmetric U C0 C1 aInf Jinf Jbarinf gInf S hSr
  refine ⟨max Ncomp (max Njet Nloc), ?_⟩
  intro k hk l hl
  dsimp only
  let Lphi := L.subseq hphi
  let Yk := X.obj (Lphi.φ k)
  let Yl := X.obj (Lphi.φ l)
  let : TopologicalSpace Yk.M := Yk.topology
  let : ChartedSpace H Yk.M := Yk.charted
  let : IsManifold I ∞ Yk.M := Yk.smooth
  let : SigmaCompactSpace Yk.M := Yk.sigmaCompact
  let : T2Space Yk.M := Yk.t2
  let : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
  let : MetricSpace Yk.M := (P (Lphi.φ k)).ms
  let : TopologicalSpace Yl.M := Yl.topology
  let : ChartedSpace H Yl.M := Yl.charted
  let : IsManifold I ∞ Yl.M := Yl.smooth
  let : SigmaCompactSpace Yl.M := Yl.sigmaCompact
  let : T2Space Yl.M := Yl.t2
  let : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
  let F := stageComparisonMap inp P Lphi r hr k l
    (chart := d.chart)
  have hkComp : Ncomp ≤ k := (Nat.le_max_left _ _).trans hk
  have hlComp : Ncomp ≤ l := (Nat.le_max_left _ _).trans hl
  have hkJet : Njet ≤ k :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right Ncomp _).trans hk)
  have hlJet : Njet ≤ l :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right Ncomp _).trans hl)
  have hkLocal : Nloc ≤ k :=
    (Nat.le_max_right _ _).trans ((Nat.le_max_right Ncomp _).trans hk)
  have hlLocal : Nloc ≤ l :=
    (Nat.le_max_right _ _).trans ((Nat.le_max_right Ncomp _).trans hl)
  have hjetKL := hjet k hkJet l hlJet
  have hlocKL := hloc k hkLocal l hlLocal
  intro G hG a ha y hy
  obtain ⟨alpha, z, hzy, hbuffer, hcompZ⟩ :=
    hcomp k hkComp l hlComp y hy
  rcases hstage with ⟨hdata, _hmetric, _hjets, _hbase⟩
  let ck := seqCenterD inp.decay P Lphi k (alpha.1 : Nat)
  let cl := seqCenterD inp.decay P Lphi l (alpha.1 : Nat)
  let chiK := d.chart (Lphi.φ k) ck
  let chiL := d.chart (Lphi.φ l) cl
  let A : E → E := fun q ↦ chiL.inv (F (chiK.hom q))
  let B : E → (E →L[Real] E →L[Real] Real) :=
    d.chartMetric (Lphi.φ k) ck
  let BL : E → (E →L[Real] E →L[Real] Real) :=
    d.chartMetric (Lphi.φ l) cl
  let Q : E → (E →L[Real] E →L[Real] Real) := fun q ↦
    _root_.DifferentialGeometry.CheegerGromovCompactness.pullbackForm
      (BL (A q), fderiv Real A q)
  obtain ⟨_hUopen, _hC0compact, _hC1compact, hC01, hC1U⟩ :=
    hdata.core_on inp P L r hr d.chart U C0 C1 aInf Jinf Jbarinf alpha
  obtain ⟨hRadK, _hmapK⟩ :=
    hdata.geom_on inp P L r hr d.chart U C0 C1 aInf Jinf Jbarinf
      k alpha
  let Bmid : Set Yk.M := Metric.ball Yk.basepoint S
  have hBopen : IsOpen Bmid := by
    have hb :
        @IsOpen Yk.M
          (P (Lphi.φ k)).ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
          Bmid := Metric.isOpen_ball
    rw [ProperMetricOn.top_eq Yk (P (Lphi.φ k))] at hb
    exact hb
  let Vset : Set E :=
    Metric.ball z (eta alpha / 2) ∩
      (chiK.restrictBall.source ∩ chiK.restrictBall ⁻¹' Bmid)
  have hVopen : IsOpen Vset := by
    dsimp only [Vset]
    exact Metric.isOpen_ball.inter
      (chiK.restrictBall.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage
        chiK.restrictBall.open_source hBopen)
  let V : TopologicalSpace.Opens E := ⟨Vset, hVopen⟩
  let : SigmaCompactSpace V :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen 𝓘(Real, E) V.isOpen)
  have hzInt : z ∈ interior (C0 alpha) :=
    hbuffer (Metric.mem_closedBall_self (heta alpha).le)
  have hzU : z ∈ U alpha :=
    hC1U (interior_subset (hC01 (interior_subset hzInt)))
  have hzBall : z ∈ Metric.ball (0 : E) chiK.radius := hRadK hzU
  have hyBmid : y ∈ Bmid := by
    exact Metric.closedBall_subset_ball hRS
      (by simpa only [Bmid, NetLimitData.hatSourceBall, Yk] using hy)
  have hzV : z ∈ V := by
    refine ⟨Metric.mem_ball_self (by linarith [heta alpha]), ?_⟩
    refine ⟨?_, ?_⟩
    · simpa only [NormalBallChart.restrict_ball_source] using hzBall
    · change chiK.restrictBall z ∈ Bmid
      rw [NormalBallChart.restrict_ball_apply, hzy]
      exact hyBmid
  have hVclosed : ∀ w : V, (w : E) ∈ Metric.closedBall z (eta alpha) := by
    intro w
    have hw : dist (w : E) z < eta alpha / 2 := by
      simpa only [V, Vset, Metric.mem_ball] using w.2.1
    rw [Metric.mem_closedBall]
    linarith [heta alpha]
  have hVint : ∀ w : V, (w : E) ∈ interior (C0 alpha) :=
    fun w ↦ hbuffer (hVclosed w)
  have hVU : ∀ w : V, (w : E) ∈ U alpha := by
    intro w
    exact hC1U (interior_subset (hC01 (interior_subset (hVint w))))
  have hVc : V ≤ chiK.ball := by
    intro w hw
    exact hRadK (hVU ⟨w, hw⟩)
  have hsourceS (w : V) :
      chiK.hom (w : E) ∈ Lphi.hatSourceBall inp.decay P S k := by
    have hwBmid : chiK.restrictBall (w : E) ∈ Bmid := w.2.2.2
    rw [NormalBallChart.restrict_ball_apply] at hwBmid
    exact Metric.ball_subset_closedBall
      (by simpa only [Bmid] using hwBmid)
  have hjetAt (w : V) :
      F (chiK.hom (w : E)) ∈ chiL.restrictBall.target ∧
        ContDiffAt Real ∞ A (w : E) := by
    have hout := hjetKL alpha (w : E) (interior_subset (hVint w))
      (hVint w) (hsourceS w)
    simpa only [A, F, chiK, chiL, ck, cl, Yk, Yl, Lphi] using
      ⟨hout.1, hout.2.1⟩
  have hQcoeff : ∀ (w : V) (u v : E),
      ((chiK.localMetric G).restrictOpenOfSubset
        (I := 𝓘(Real, E)) hVc).inner w u v =
        Q (w : E) u v := by
    intro w u v
    have hFdiff : MDifferentiableAt I I F (chiK.hom (w : E)) :=
      (hlocKL ⟨chiK.hom (w : E), hsourceS w⟩).mdifferentiableAt (by simp)
    have hmetricEq : ∀ v' w' : TangentSpace I (chiK.hom (w : E)),
        G.inner (chiK.hom (w : E)) v' w' =
          Yl.metric.inner (F (chiK.hom (w : E)))
            (mfderiv I I F (chiK.hom (w : E)) v')
            (mfderiv I I F (chiK.hom (w : E)) w') :=
      hG _ (hsourceS w)
    change (chiK.localMetric G).inner
        (TopologicalSpace.Opens.inclusion hVc w) u v = Q (w : E) u v
    rw [normalBallLocalMetric_inner_model]
    have hout := chart_pull_coeff (I := I) Yl.metric chiK chiL F G
      (w : E) (hVc w.2) (hjetAt w).1 hFdiff hmetricEq u v
    simpa only [Q, BL, A, BoundedGeometryNormalChartData.chartMetric] using hout
  have hBcoeff : ∀ (w : V) (u v : E),
      ((chiK.localMetric Yk.metric).restrictOpenOfSubset
        (I := 𝓘(Real, E)) hVc).inner w u v =
        B (w : E) u v := by
    intro w u v
    change (chiK.localMetric Yk.metric).inner
        (TopologicalSpace.Opens.inclusion hVc w) u v = B (w : E) u v
    rw [normalBallLocalMetric_inner_model]
    rfl
  have hBco : ∀ w : E, w ∈ V → IsCoercive (B w) := by
    intro w hw
    have hEquiv : chiK.MetricEquivOn Yk.metric (U alpha) := by
      intro q hq v
      exact d.metric_equiv (Lphi.φ k) ck q (hRadK hq) v
    simpa only [B, BoundedGeometryNormalChartData.chartMetric, chiK, ck, Yk, Lphi] using
      hEquiv.coercive Yk.metric (hVU ⟨w, hw⟩)
  have hequiv : ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤ B z v v ∧
        B z v v ≤ 2 * ‖v‖ ^ 2 := by
    intro v
    simpa only [B, BoundedGeometryNormalChartData.chartMetric, chiK, ck, Yk, Lphi] using
      d.metric_equiv (Lphi.φ k) ck z hzBall v
  have hBcd : ContDiffOn Real (∞ : WithTop ℕ∞) B V := by
    have hsmooth := chiK.metric_cont_diff_on Yk.metric hVopen
      (chiK.smooth_to.mono hVc)
    with_unfolding_all
      exact hsmooth
  have hAcd : ContDiffOn Real (∞ : WithTop ℕ∞) A V := by
    intro w hw
    exact (hjetAt ⟨w, hw⟩).2.contDiffWithinAt
  have hAmap : Set.MapsTo A V chiL.ball := by
    intro w hw
    have hout := chiL.restrictBall.map_target (hjetAt ⟨w, hw⟩).1
    with_unfolding_all
      exact hout
  have hBLcd : ContDiffOn Real (∞ : WithTop ℕ∞) BL chiL.ball := by
    have hsmooth := chiL.metric_cont_diff_on Yl.metric Metric.isOpen_ball
      chiL.smooth_to
    with_unfolding_all
      exact hsmooth
  have hBAcd : ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun w ↦ BL (A w)) V := by
    simpa only [Function.comp_def] using hBLcd.comp hAcd hAmap
  have hDAcd : ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun w ↦ fderiv Real A w) V := by
    intro w hw
    exact (((hAcd.contDiffAt (hVopen.mem_nhds hw)).fderiv_right
      (m := (∞ : WithTop ℕ∞)) (by simp)).contDiffWithinAt)
  have hQcd : ContDiffOn Real (∞ : WithTop ℕ∞) Q V := by
    have hpull :=
      (_root_.DifferentialGeometry.CheegerGromovCompactness.pullbackForm.contDiff
        (E := E) (F := E)).comp_contDiffOn (hBAcd.prodMk hDAcd)
    with_unfolding_all
      exact hpull
  let Gamma := fun w i j m ↦ e.coord m
    (MetricKoszul.raisedKoszulOp (B w) (fderiv Real B w)
      (e i) (e j))
  let base := fun w (slots : Fin 2 → Fin (Module.finrank Real E)) ↦
    (Q w - B w) (e (slots 0)) (e (slots 1))
  have hdiff : ∀ q : Nat, ∀ w : V,
      ∀ slots : Fin (2 + q) → Fin (Module.finrank Real E),
        MDifferentiableAt 𝓘(Real, E) 𝓘(Real, Real)
          (fun y : E ↦ iterCovComp (I := 𝓘(Real, E))
            (fun i _ ↦ e i) Gamma base q y slots) (w : E) := by
    simpa only [Gamma, base] using
      metric_iterCovComp_mdifferentiableAt V e B Q hBcd hQcd hBco
  have hcompLe : ∀ slots : Fin (2 + a) → Fin (Module.finrank Real E),
      |iterCovComp (I := 𝓘(Real, E)) (fun i _ ↦ e i)
          Gamma base a z slots| ≤ epsComp := by
    intro slots
    have hraw := (hcompZ a ha slots).le
    simpa only [Gamma, base, B, BL, Q, A, chiK, chiL, F, ck, cl,
      BoundedGeometryNormalChartData.chartMetric, Yk, Yl, Lphi] using hraw
  let cut : ContDiffBump z :=
    { rIn := eta alpha / 2
      rOut := eta alpha
      rIn_pos := by linarith [heta alpha]
      rIn_lt_rOut := by linarith [heta alpha] }
  have hcut_one : ∀ w ∈ V, cut w = 1 := by
    intro w hw
    apply cut.one_of_mem_closedBall
    change w ∈ Metric.closedBall z (eta alpha / 2)
    exact Metric.ball_subset_closedBall hw.1
  have hcut_support :
      tsupport (cut : E → Real) ⊆ (chiK.ball : Set E) := by
    rw [cut.tsupport_eq]
    change Metric.closedBall z (eta alpha) ⊆ (chiK.ball : Set E)
    exact hbuffer.trans fun q hq ↦
      hRadK (hC1U (interior_subset (hC01 (interior_subset hq))))
  let zV : V := ⟨z, hzV⟩
  have hlocal := chart_local_norm_le (I := I) Yk.metric chiK
    V hVc cut G Q B a zV hcut_one hcut_support hBcd
    hepsComp.le hQcoeff hBcoeff hBco hequiv hdiff hcompLe
  let : LocallyCompactSpace chiK.ball := chiK.ball.2.locallyCompactSpace
  let : SigmaCompactSpace chiK.ball := inferInstance
  let zK : chiK.ball := TopologicalSpace.Opens.inclusion hVc zV
  have hpoint : chiK.hom (zK : E) = y := by
    simpa only [zK, zV] using hzy
  calc
    metricDerivNorm (I := I) a G Yk.metric Yk.metric y =
        metricDerivNorm (I := I) a G Yk.metric Yk.metric
          (chiK.hom (zK : E)) :=
      congrArg (fun q ↦ metricDerivNorm (I := I) a
        G Yk.metric Yk.metric q) hpoint.symm
    _ = metricDerivNorm (I := 𝓘(Real, E)) a
          (chiK.localMetric G) (chiK.localMetric Yk.metric)
          (chiK.localMetric Yk.metric) zK :=
      (chart_norm_eq (I := I) Yk.metric chiK G a zK).symm
    _ = metricDerivNorm (I := 𝓘(Real, E)) a
          ((chiK.localMetric G).restrictOpenOfSubset
            (I := 𝓘(Real, E)) hVc)
          ((chiK.localMetric Yk.metric).restrictOpenOfSubset
            (I := 𝓘(Real, E)) hVc)
          ((chiK.localMetric Yk.metric).restrictOpenOfSubset
            (I := 𝓘(Real, E)) hVc) zV :=
      (metricDerivNorm_flat (I := 𝓘(Real, E)) hVc
        (chiK.localMetric G) (chiK.localMetric Yk.metric)
        (chiK.localMetric Yk.metric) a zV).symm
    _ ≤ Real.sqrt (2 ^ (2 + a)) *
          (Real.sqrt
            (Fintype.card
              (Fin (2 + a) → Fin (Module.finrank Real E)) : Real) * epsComp) :=
      hlocal
    _ ≤ eps := by
      let afin : Fin (p + 1) := ⟨a, Nat.lt_succ_iff.mpr ha⟩
      simpa only [fac, afin, mul_assoc] using hbudget afin

theorem BoundedGeometryNormalChartData.inv_norm_tail
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
    {R S T Vrad : Real} (hRS : R < S) (hST : S < T)
    (hroom : T + (4 + 8 * Real.sqrt 2) * inp.decay.lambda inp.D 0 < Vrad)
    (hVr : Vrad < r)
    (p : Nat) (eps : Real) (heps : 0 < eps) :
    ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N,
      let Lphi := L.subseq hphi
      let Yk := X.obj (Lphi.φ k)
      let Yl := X.obj (Lphi.φ l)
      letI : TopologicalSpace Yk.M := Yk.topology
      letI : ChartedSpace H Yk.M := Yk.charted
      letI : IsManifold I ∞ Yk.M := Yk.smooth
      letI : SigmaCompactSpace Yk.M := Yk.sigmaCompact
      letI : T2Space Yk.M := Yk.t2
      letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
      letI : MetricSpace Yk.M := (P (Lphi.φ k)).ms
      letI : Nonempty Yk.M := ⟨Yk.basepoint⟩
      letI : TopologicalSpace Yl.M := Yl.topology
      letI : ChartedSpace H Yl.M := Yl.charted
      letI : IsManifold I ∞ Yl.M := Yl.smooth
      letI : SigmaCompactSpace Yl.M := Yl.sigmaCompact
      letI : T2Space Yl.M := Yl.t2
      letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
      letI : MetricSpace Yl.M := (P (Lphi.φ l)).ms
      let F := stageComparisonMap inp P Lphi r hr k l
        (chart := d.chart)
      let Hinv := Function.invFunOn F (Metric.ball Yk.basepoint T)
      ∀ (G : SmoothRiemannianMetric I Yl.M),
        (∀ y ∈ F '' Lphi.hatSourceBall inp.decay P S k,
          ∀ v w : TangentSpace I y,
            G.inner y v w =
              Yk.metric.inner (Hinv y) (mfderiv I I Hinv y v)
                (mfderiv I I Hinv y w)) →
        ∀ a ≤ p, ∀ y ∈ F '' Lphi.hatSourceBall inp.decay P R k,
          metricDerivNorm (I := I) a G Yl.metric Yl.metric y ≤ eps := by
  classical
  let e : Module.Basis (Fin (Module.finrank Real E)) Real E :=
    (stdOrthonormalBasis Real E).toBasis
  let fac : Fin (p + 1) → Real := fun a ↦
    Real.sqrt (2 ^ (2 + (a : Nat))) *
      Real.sqrt
        (Fintype.card
          (Fin (2 + (a : Nat)) → Fin (Module.finrank Real E)) : Real)
  let Cmax : Real := Finset.univ.sup' Finset.univ_nonempty fac
  have hfac_nonneg : ∀ a, 0 ≤ fac a := by
    intro a
    dsimp only [fac]
    positivity
  have hfac_le : ∀ a, fac a ≤ Cmax := by
    intro a
    exact Finset.le_sup' fac (Finset.mem_univ a)
  have hCmax_nonneg : 0 ≤ Cmax := by
    let a0 : Fin (p + 1) := ⟨0, Nat.zero_lt_succ p⟩
    exact (hfac_nonneg a0).trans (hfac_le a0)
  let epsComp := eps / (Cmax + 1)
  have hden : 0 < Cmax + 1 := by linarith
  have hepsComp : 0 < epsComp := div_pos heps hden
  have hbudget : ∀ a, fac a * epsComp ≤ eps := by
    intro a
    refine (mul_le_mul_of_nonneg_right (hfac_le a) hepsComp.le).trans ?_
    dsimp only [epsComp]
    rw [← mul_div_assoc, div_le_iff₀ hden]
    nlinarith
  have hgap : 0 ≤
      (4 + 8 * Real.sqrt 2) * inp.decay.lambda inp.D 0 :=
    mul_nonneg (by positivity) (inp.decay.lambda_pos inp.hD 0).le
  have hTr : T < r := by linarith
  have hSr : S < r := hST.trans hTr
  obtain ⟨eta, heta, Ncomp, hcomp⟩ :=
    d.inv_cov_comp_tail inp P L hr phi hphi hcomplete hconn
      Vmetric U C0 C1 aInf Jinf Jbarinf gInf hstage
      hRS hST hroom hVr e p epsComp hepsComp
  have hmove : ∀ alpha : LiveSlot L inp.pack r,
      HasStageJetTail (I := I) inp P L hr phi hphi C0 S 0
        (eta alpha / 2) (chart := d.chart) := by
    intro alpha
    exact hstage.2.2.1 S hSr 0 (eta alpha / 2)
      (div_pos (heta alpha) (by norm_num))
  choose Nmove hNmove using hmove
  let := Fintype.ofFinite (LiveSlot L inp.pack r)
  let NmoveAll : Nat := Finset.univ.sup Nmove
  obtain ⟨Nloc, hloc⟩ :=
    hstage.hloc_tail inp P L hr phi hphi d.chart
      Vmetric U C0 C1 aInf Jinf Jbarinf gInf T hTr
  obtain ⟨Ninj, hinj⟩ :=
    d.inj_tail inp P L hr phi hphi hcomplete hconn
      Vmetric U C0 C1 aInf Jinf Jbarinf gInf hstage
      T Vrad hroom hVr
  let N := max Ncomp (max Nloc (max Ninj NmoveAll))
  refine ⟨N, ?_⟩
  intro k hk l hl
  dsimp only
  let Lphi := L.subseq hphi
  let Yk := X.obj (Lphi.φ k)
  let Yl := X.obj (Lphi.φ l)
  let : TopologicalSpace Yk.M := Yk.topology
  let : ChartedSpace H Yk.M := Yk.charted
  let : IsManifold I ∞ Yk.M := Yk.smooth
  let : SigmaCompactSpace Yk.M := Yk.sigmaCompact
  let : T2Space Yk.M := Yk.t2
  let : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
  let : MetricSpace Yk.M := (P (Lphi.φ k)).ms
  let : Nonempty Yk.M := ⟨Yk.basepoint⟩
  let : TopologicalSpace Yl.M := Yl.topology
  let : ChartedSpace H Yl.M := Yl.charted
  let : IsManifold I ∞ Yl.M := Yl.smooth
  let : SigmaCompactSpace Yl.M := Yl.sigmaCompact
  let : T2Space Yl.M := Yl.t2
  let : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
  let : MetricSpace Yl.M := (P (Lphi.φ l)).ms
  let F := stageComparisonMap inp P Lphi r hr k l
    (chart := d.chart)
  let Hinv := Function.invFunOn F (Metric.ball Yk.basepoint T)
  have hkComp : Ncomp ≤ k := by dsimp only [N] at hk; omega
  have hlComp : Ncomp ≤ l := by dsimp only [N] at hl; omega
  have hkLocal : Nloc ≤ k := by dsimp only [N] at hk; omega
  have hlLocal : Nloc ≤ l := by dsimp only [N] at hl; omega
  have hkInj : Ninj ≤ k := by dsimp only [N] at hk; omega
  have hlInj : Ninj ≤ l := by dsimp only [N] at hl; omega
  have hmoveLe (alpha : LiveSlot L inp.pack r) : Nmove alpha ≤ NmoveAll :=
    Finset.le_sup (f := Nmove) (Finset.mem_univ alpha)
  have hlocKL := hloc k hkLocal l hlLocal
  have hinjKL := hinj k hkInj l hlInj
  intro G hG a ha q hq
  rcases hq with ⟨y, hy, rfl⟩
  obtain ⟨alpha, z, hzy, hbuffer, hcompZ⟩ :=
    hcomp k hkComp l hlComp y hy
  rcases hstage with ⟨hdata, _hmetric, _hjets, _hbase⟩
  let ck := seqCenterD inp.decay P Lphi k (alpha.1 : Nat)
  let cl := seqCenterD inp.decay P Lphi l (alpha.1 : Nat)
  let chiK := d.chart (Lphi.φ k) ck
  let chiL := d.chart (Lphi.φ l) cl
  let A : E → E := fun w => chiL.inv (F (chiK.hom w))
  let Grev : E → E := fun w => chiK.inv (Hinv (chiL.hom w))
  let BK : E → (E →L[Real] E →L[Real] Real) :=
    d.chartMetric (Lphi.φ k) ck
  let BL : E → (E →L[Real] E →L[Real] Real) :=
    d.chartMetric (Lphi.φ l) cl
  let Q : E → (E →L[Real] E →L[Real] Real) := fun w =>
    _root_.DifferentialGeometry.CheegerGromovCompactness.pullbackForm
      (BK (Grev w), fderiv Real Grev w)
  have hzInt : z ∈ interior (C0 alpha) :=
    hbuffer (Metric.mem_closedBall_self (heta alpha).le)
  have hyS : chiK.hom z ∈
      Lphi.hatSourceBall inp.decay P S k := by
    have hzy' : chiK.hom z = y := by
      simpa only [chiK, ck, Yk, Lphi] using hzy
    rw [hzy']
    exact cball_subset_of_le hRS.le hy
  have hkMove : Nmove alpha ≤ k :=
    (hmoveLe alpha).trans (by dsimp only [N] at hk; omega)
  have hlMove : Nmove alpha ≤ l :=
    (hmoveLe alpha).trans (by dsimp only [N] at hl; omega)
  have hjetZraw := hNmove alpha k hkMove l hlMove alpha z
    (interior_subset hzInt) hzInt hyS
  have hjetZ :
      F (chiK.hom z) ∈ chiL.restrictBall.target ∧
        ContDiffAt Real ∞ A z ∧
        ∀ j ≤ 0, mapDerivNorm j A id z ≤ eta alpha / 2 := by
    simpa only [A, F, chiK, chiL, ck, cl, Yk, Yl, Lphi] using hjetZraw
  have hAzDist : dist (A z) z ≤ eta alpha / 2 := by
    have hraw := hjetZ.2.2 0 le_rfl
    simpa only [mapDerivNorm, norm_iteratedFDeriv_zero, id_eq,
      dist_eq_norm] using hraw
  have hAzInt : A z ∈ interior (C0 alpha) := by
    apply hbuffer
    change dist (A z) z ≤ eta alpha
    linarith [heta alpha]
  obtain ⟨_hUopen, _hC0compact, _hC1compact, hC01, hC1U⟩ :=
    hdata.core_on inp P L r hr d.chart U C0 C1 aInf Jinf Jbarinf alpha
  obtain ⟨hRadK, _hmapK⟩ :=
    hdata.geom_on inp P L r hr d.chart U C0 C1 aInf Jinf Jbarinf
      k alpha
  obtain ⟨hRadL, _hmapL⟩ :=
    hdata.geom_on inp P L r hr d.chart U C0 C1 aInf Jinf Jbarinf
      l alpha
  have hzU : z ∈ U alpha :=
    hC1U (interior_subset (hC01 (interior_subset hzInt)))
  have hzBall : z ∈ Metric.ball (0 : E) chiK.radius := hRadK hzU
  have hBallOpen : IsOpen (Metric.ball Yk.basepoint T) := by
    have hb :
        @IsOpen Yk.M
          (P (Lphi.φ k)).ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
          (Metric.ball Yk.basepoint T) := Metric.isOpen_ball
    rw [ProperMetricOn.top_eq Yk (P (Lphi.φ k))] at hb
    exact hb
  have hlocBall : IsLocalDiffeomorphOn I I (∞ : WithTop ℕ∞) F
      (Metric.ball Yk.basepoint T) := by
    rintro ⟨x, hx⟩
    exact hlocKL ⟨x, Metric.ball_subset_closedBall hx⟩
  have hinjBall : Set.InjOn F (Metric.ball Yk.basepoint T) :=
    hinjKL.mono Metric.ball_subset_closedBall
  obtain ⟨Phi, hPhiSource, hPhiTarget, hPhiEq⟩ :=
    exists_partial_diffeomorph_of_is_local_diffeomorph_on_inj_on hlocBall hBallOpen hinjBall
  have hsymmEq : Set.EqOn (Phi.symm : Yl.M → Yk.M) Hinv Phi.target := by
    intro q hq
    rw [hPhiTarget] at hq
    obtain ⟨x, hx, rfl⟩ := hq
    have hPhix : (Phi : Yk.M → Yl.M) x = F x := hPhiEq hx
    have hleft : (Phi.symm : Yl.M → Yk.M) (F x) = x := by
      rw [← hPhix]
      exact Phi.toPartialEquiv.left_inv (by rw [hPhiSource]; exact hx)
    have hinv : Hinv (F x) = x :=
      hinjBall.leftInvOn_invFunOn hx
    rw [hleft, hinv]
  have hBallSOpen : IsOpen (Metric.ball Yk.basepoint S) := by
    have hb :
        @IsOpen Yk.M
          (P (Lphi.φ k)).ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
          (Metric.ball Yk.basepoint S) := Metric.isOpen_ball
    rw [ProperMetricOn.top_eq Yk (P (Lphi.φ k))] at hb
    exact hb
  have hBallSsub : Metric.ball Yk.basepoint S ⊆ Phi.source := by
    rw [hPhiSource]
    exact Metric.ball_subset_ball hST.le
  have hImageOpen : IsOpen ((Phi : Yk.M → Yl.M) ''
      Metric.ball Yk.basepoint S) :=
    Phi.toOpenPartialHomeomorph.isOpen_image_of_subset_source
      hBallSOpen hBallSsub
  let Wphi : Set Yl.M :=
    (Phi : Yk.M → Yl.M) '' Metric.ball Yk.basepoint S ∩
      (Phi.target ∩
        (Phi.symm : Yl.M → Yk.M) ⁻¹' chiK.restrictBall.target)
  have hWphiOpen : IsOpen Wphi := by
    dsimp only [Wphi]
    exact hImageOpen.inter
      (Phi.symm.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage
        Phi.open_target chiK.restrictBall.open_target)
  let Wcoord : Set E :=
    chiL.restrictBall.source ∩ chiL.restrictBall ⁻¹' Wphi
  have hWcoordOpen : IsOpen Wcoord := by
    dsimp only [Wcoord]
    exact chiL.restrictBall.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage
      chiL.restrictBall.open_source hWphiOpen
  let Vset : Set E :=
    Metric.ball (A z) (eta alpha / 4) ∩
      (interior (C0 alpha) ∩ Wcoord)
  have hVopen : IsOpen Vset :=
    Metric.isOpen_ball.inter (isOpen_interior.inter hWcoordOpen)
  let V : TopologicalSpace.Opens E := ⟨Vset, hVopen⟩
  let : SigmaCompactSpace V :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen 𝓘(Real, E) V.isOpen)
  have hySopen : y ∈ Metric.ball Yk.basepoint S := by
    have hyR : dist y Yk.basepoint ≤ R := by
      exact Metric.mem_closedBall.mp
        (by simpa only [NetLimitData.hatSourceBall, Yk] using hy)
    rw [Metric.mem_ball]
    exact hyR.trans_lt hRS
  have hPhiY : (Phi : Yk.M → Yl.M) y = F y :=
    hPhiEq (Metric.ball_subset_ball hST.le hySopen)
  have hPhiSymmY : (Phi.symm : Yl.M → Yk.M) (F y) = y := by
    rw [← hPhiY]
    exact Phi.toPartialEquiv.left_inv (hBallSsub hySopen)
  have hdecode : chiL.hom (A z) = F y := by
    have hzy' : chiK.hom z = y := by
      simpa only [chiK, ck, Yk, Lphi] using hzy
    change chiL.hom (chiL.inv (F (chiK.hom z))) = F y
    rw [hzy']
    have hright :=
      chiL.restrictBall.right_inv (by simpa only [hzy'] using hjetZ.1)
    with_unfolding_all
      exact hright
  have hyKtarget : y ∈ chiK.restrictBall.target := by
    refine ⟨z, ?_, ?_⟩
    · with_unfolding_all
        exact hzBall
    · simpa only [NormalBallChart.restrict_ball_apply] using hzy
  have hAzV : A z ∈ V := by
    refine ⟨Metric.mem_ball_self (by linarith [heta alpha]), hAzInt, ?_⟩
    have hAzSource : A z ∈ chiL.restrictBall.source :=
      chiL.restrictBall.map_target hjetZ.1
    refine ⟨hAzSource, ?_⟩
    change chiL.restrictBall (A z) ∈ Wphi
    rw [NormalBallChart.restrict_ball_apply, hdecode]
    refine ⟨⟨y, hySopen, hPhiY⟩, ?_, ?_⟩
    · rw [hPhiTarget]
      exact ⟨y, Metric.ball_subset_ball hST.le hySopen, rfl⟩
    · change Phi.symm (F y) ∈ chiK.restrictBall.target
      rw [hPhiSymmY]
      exact hyKtarget
  have hVc : V ≤ chiL.ball := by
    intro w hw
    with_unfolding_all
      exact hw.2.2.1
  have hImageEq : (Phi : Yk.M → Yl.M) '' Metric.ball Yk.basepoint S =
      F '' Metric.ball Yk.basepoint S :=
    Set.EqOn.image_eq (fun x hx =>
      hPhiEq (Metric.ball_subset_ball hST.le hx))
  have hHcdOn : ContMDiffOn I I ∞ Hinv Phi.target :=
    Phi.symm.contMDiffOn_toFun.congr
      (fun q hq => (hsymmEq hq).symm)
  let Gaux : E → E := fun w =>
    chiK.restrictBall.symm (Phi.symm (chiL.restrictBall w))
  have hauxMD : ContMDiffOn 𝓘(Real, E) 𝓘(Real, E) ∞ Gaux V := by
    have h1 := chiL.restrictBall.contMDiffOn_toFun.mono
      (fun (w : E) (hw : w ∈ (V : Set E)) => hw.2.2.1)
    have h2 := Phi.symm.contMDiffOn_toFun.comp h1
      (fun (w : E) (hw : w ∈ (V : Set E)) => hw.2.2.2.2.1)
    have h3 := chiK.restrictBall.symm.contMDiffOn_toFun.comp h2
      (fun (w : E) (hw : w ∈ (V : Set E)) => hw.2.2.2.2.2)
    exact h3.congr (fun w _ ↦ rfl)
  have hauxEq : Set.EqOn Gaux Grev V := by
    intro w hw
    have heq := hsymmEq hw.2.2.2.2.1
    have hcongr := congrArg chiK.inv heq
    with_unfolding_all
      exact hcongr
  have hGrevcd : ContDiffOn Real (∞ : WithTop ℕ∞) Grev V := by
    rw [← contMDiffOn_iff_contDiffOn]
    exact hauxMD.congr (fun w hw => (hauxEq hw).symm)
  have hGrevMap : Set.MapsTo Grev V chiK.ball := by
    intro w hw
    rw [← hauxEq hw]
    have hout := chiK.restrictBall.map_target hw.2.2.2.2.2
    with_unfolding_all
      exact hout
  have hQcoeff : ∀ (w : V) (u v : E),
      ((chiL.localMetric G).restrictOpenOfSubset
        (I := 𝓘(Real, E)) hVc).inner w u v =
        Q (w : E) u v := by
    intro w u v
    have hPhiTarget : chiL.hom (w : E) ∈ Phi.target := by
      simpa only [NormalBallChart.restrict_ball_apply] using
        w.2.2.2.2.2.1
    have hInvTarget :
        Hinv (chiL.hom (w : E)) ∈ chiK.restrictBall.target := by
      have hmem := w.2.2.2.2.2.2
      rw [NormalBallChart.restrict_ball_apply] at hmem
      change Phi.symm (chiL.hom (w : E)) ∈
        chiK.restrictBall.target at hmem
      rw [hsymmEq hPhiTarget] at hmem
      exact hmem
    have hHdiff : MDifferentiableAt I I Hinv (chiL.hom (w : E)) := by
      have hraw := (hHcdOn.contMDiffAt
        (Phi.open_target.mem_nhds hPhiTarget)).mdifferentiableAt (by simp)
      exact hraw
    have hstageBall : chiL.hom (w : E) ∈
        F '' Metric.ball Yk.basepoint S := by
      have hraw := w.2.2.2.2.1
      rw [hImageEq] at hraw
      simpa only [NormalBallChart.restrict_ball_apply] using hraw
    have hstageClosed : chiL.hom (w : E) ∈
        F '' Lphi.hatSourceBall inp.decay P S k := by
      apply Set.image_mono _ hstageBall
      intro x hx
      simpa only [NetLimitData.hatSourceBall, Yk] using
        Metric.ball_subset_closedBall hx
    have hmetricEq :
        ∀ v' w' : TangentSpace I (chiL.hom (w : E)),
          G.inner (chiL.hom (w : E)) v' w' =
            Yk.metric.inner (Hinv (chiL.hom (w : E)))
              (mfderiv I I Hinv (chiL.hom (w : E)) v')
              (mfderiv I I Hinv (chiL.hom (w : E)) w') :=
      hG _ hstageClosed
    change (chiL.localMetric G).inner
        (TopologicalSpace.Opens.inclusion hVc w) u v = Q (w : E) u v
    rw [normalBallLocalMetric_inner_model]
    have hout := chart_pull_coeff (I := I) Yk.metric chiL chiK Hinv G
      (w : E) (hVc w.2) hInvTarget hHdiff hmetricEq u v
    simpa only [Q, BK, Grev, BoundedGeometryNormalChartData.chartMetric] using hout
  have hBcoeff : ∀ (w : V) (u v : E),
      ((chiL.localMetric Yl.metric).restrictOpenOfSubset
        (I := 𝓘(Real, E)) hVc).inner w u v =
        BL (w : E) u v := by
    intro w u v
    change (chiL.localMetric Yl.metric).inner
        (TopologicalSpace.Opens.inclusion hVc w) u v = BL (w : E) u v
    rw [normalBallLocalMetric_inner_model]
    rfl
  have hVU : ∀ w : V, (w : E) ∈ U alpha := by
    intro w
    exact hC1U
      (interior_subset (hC01 (interior_subset w.2.2.1)))
  have hBLco : ∀ w : E, w ∈ V → IsCoercive (BL w) := by
    intro w hw
    have hEquiv : chiL.MetricEquivOn Yl.metric (U alpha) := by
      intro q hq v
      exact d.metric_equiv (Lphi.φ l) cl q (hRadL hq) v
    simpa only [BL, BoundedGeometryNormalChartData.chartMetric, chiL, cl, Yl, Lphi] using
      hEquiv.coercive Yl.metric (hVU ⟨w, hw⟩)
  have hequiv : ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤ BL (A z) v v ∧
        BL (A z) v v ≤ 2 * ‖v‖ ^ 2 := by
    intro v
    simpa only [BL, BoundedGeometryNormalChartData.chartMetric, chiL, cl, Yl, Lphi] using
      d.metric_equiv (Lphi.φ l) cl (A z) (hRadL (hVU ⟨A z, hAzV⟩)) v
  have hBLcd : ContDiffOn Real (∞ : WithTop ℕ∞) BL V := by
    have hsmooth := chiL.metric_cont_diff_on Yl.metric hVopen
      (chiL.smooth_to.mono hVc)
    with_unfolding_all
      exact hsmooth
  have hBKcd : ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun w => BK (Grev w)) V := by
    have hsource : ContDiffOn Real (∞ : WithTop ℕ∞) BK chiK.ball := by
      have hsmooth := chiK.metric_cont_diff_on Yk.metric Metric.isOpen_ball
        chiK.smooth_to
      with_unfolding_all
        exact hsmooth
    simpa only [Function.comp_def] using hsource.comp hGrevcd hGrevMap
  have hDGrev : ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun w => fderiv Real Grev w) V := by
    intro w hw
    exact (((hGrevcd.contDiffAt (hVopen.mem_nhds hw)).fderiv_right
      (m := (∞ : WithTop ℕ∞)) (by simp)).contDiffWithinAt)
  have hQcd : ContDiffOn Real (∞ : WithTop ℕ∞) Q V := by
    have hpull :=
      (_root_.DifferentialGeometry.CheegerGromovCompactness.pullbackForm.contDiff
        (E := E) (F := E)).comp_contDiffOn (hBKcd.prodMk hDGrev)
    with_unfolding_all
      exact hpull
  let Gamma := fun w i j m ↦ e.coord m
    (MetricKoszul.raisedKoszulOp (BL w) (fderiv Real BL w)
      (e i) (e j))
  let base := fun w (slots : Fin 2 → Fin (Module.finrank Real E)) ↦
    (Q w - BL w) (e (slots 0)) (e (slots 1))
  have hdiff : ∀ q' : Nat, ∀ w : V,
      ∀ slots : Fin (2 + q') → Fin (Module.finrank Real E),
        MDifferentiableAt 𝓘(Real, E) 𝓘(Real, Real)
          (fun x : E ↦ iterCovComp (I := 𝓘(Real, E))
            (fun i _ ↦ e i) Gamma base q' x slots) (w : E) := by
    simpa only [Gamma, base] using
      metric_iterCovComp_mdifferentiableAt V e BL Q hBLcd hQcd hBLco
  have hcompLe : ∀ slots : Fin (2 + a) → Fin (Module.finrank Real E),
      |iterCovComp (I := 𝓘(Real, E)) (fun i _ ↦ e i)
          Gamma base a (A z) slots| ≤ epsComp := by
    intro slots
    have hraw := (hcompZ a ha slots).le
    with_unfolding_all
      exact hraw
  let cut : ContDiffBump (A z) :=
    { rIn := eta alpha / 4
      rOut := eta alpha / 2
      rIn_pos := by linarith [heta alpha]
      rIn_lt_rOut := by linarith [heta alpha] }
  have hcut_one : ∀ w ∈ V, cut w = 1 := by
    intro w hw
    apply cut.one_of_mem_closedBall
    change w ∈ Metric.closedBall (A z) (eta alpha / 4)
    exact Metric.ball_subset_closedBall hw.1
  have hcut_support :
      tsupport (cut : E → Real) ⊆ (chiL.ball : Set E) := by
    rw [cut.tsupport_eq]
    intro w hw
    have hwAz : dist w (A z) ≤ eta alpha / 2 :=
      Metric.mem_closedBall.mp hw
    have hwz : dist w z ≤ eta alpha := by
      calc
        dist w z ≤ dist w (A z) + dist (A z) z := dist_triangle _ _ _
        _ ≤ eta alpha / 2 + eta alpha / 2 :=
          add_le_add hwAz hAzDist
        _ = eta alpha := by ring
    exact hRadL
      (hC1U (interior_subset
        (hC01 (interior_subset (hbuffer
          (Metric.mem_closedBall.mpr hwz))))))
  let wV : V := ⟨A z, hAzV⟩
  have hlocal := chart_local_norm_le (I := I) Yl.metric chiL
    V hVc cut G Q BL a wV hcut_one hcut_support hBLcd
    hepsComp.le hQcoeff hBcoeff hBLco hequiv hdiff hcompLe
  let : LocallyCompactSpace chiL.ball := chiL.ball.2.locallyCompactSpace
  let : SigmaCompactSpace chiL.ball := inferInstance
  let wL : chiL.ball := TopologicalSpace.Opens.inclusion hVc wV
  have hpoint : chiL.hom (wL : E) = F y := by
    simpa only [wL, wV] using hdecode
  calc
    metricDerivNorm (I := I) a G Yl.metric Yl.metric (F y) =
        metricDerivNorm (I := I) a G Yl.metric Yl.metric
          (chiL.hom (wL : E)) :=
      congrArg (fun q' ↦ metricDerivNorm (I := I) a
        G Yl.metric Yl.metric q') hpoint.symm
    _ = metricDerivNorm (I := 𝓘(Real, E)) a
          (chiL.localMetric G) (chiL.localMetric Yl.metric)
          (chiL.localMetric Yl.metric) wL :=
      (chart_norm_eq (I := I) Yl.metric chiL G a wL).symm
    _ = metricDerivNorm (I := 𝓘(Real, E)) a
          ((chiL.localMetric G).restrictOpenOfSubset
            (I := 𝓘(Real, E)) hVc)
          ((chiL.localMetric Yl.metric).restrictOpenOfSubset
            (I := 𝓘(Real, E)) hVc)
          ((chiL.localMetric Yl.metric).restrictOpenOfSubset
            (I := 𝓘(Real, E)) hVc) wV :=
      (metricDerivNorm_flat (I := 𝓘(Real, E)) hVc
        (chiL.localMetric G) (chiL.localMetric Yl.metric)
        (chiL.localMetric Yl.metric) a wV).symm
    _ ≤ Real.sqrt (2 ^ (2 + a)) *
          (Real.sqrt
            (Fintype.card
              (Fin (2 + a) → Fin (Module.finrank Real E)) : Real) * epsComp) :=
      hlocal
    _ ≤ eps := by
      let afin : Fin (p + 1) := ⟨a, Nat.lt_succ_iff.mpr ha⟩
      simpa only [fac, afin, mul_assoc] using hbudget afin

end CheegerGromovCompactness
end DifferentialGeometry
