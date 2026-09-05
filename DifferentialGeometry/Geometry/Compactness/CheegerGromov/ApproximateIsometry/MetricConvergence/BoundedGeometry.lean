import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.ChartFamily
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricConvergence.StageJet

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

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

theorem HasStageJetConvergenceOn.chart_convergence
    (inp : MetricCompactSeedWithDivisor (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (chart : NormalChartFamily (I := I) X)
    (Vmetric U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (gInf : LiveSlot L inp.pack r →
      E → (E →L[Real] E →L[Real] Real))
    (hstage : HasStageJetConvergenceOn (I := I) inp P L hr phi hphi chart
      Vmetric U C0 C1 aInf Jinf Jbarinf gInf)
    (R : Real) (hRr : R < r) (alpha : LiveSlot L inp.pack r)
    (V : Set E) (hVint : V ⊆ interior (C0 alpha))
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
      Set.MapsTo
        (chart (Lphi.φ (kn n))
          (seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat))).hom
        V (Lphi.hatSourceBall inp.decay P R (kn n))) :
    MapCInfConvergenceOnCompacts V
      (fun n z ↦
        let Lphi := L.subseq hphi
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
        let chiK := chart (Lphi.φ (kn n))
          (seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat))
        let chiL := chart (Lphi.φ (ln n))
          (seqCenterD inp.decay P Lphi (ln n) (alpha.1 : Nat))
        chiL.inv (stageComparisonMap inp P Lphi r hr
          (kn n) (ln n) (chiK.hom z) (chart := chart))) id := by
  rcases hstage with ⟨_hdata, _hmetric, hjets, _hbase⟩
  intro K hK hKV p eps heps
  obtain ⟨Njet, hNjet⟩ := hjets R hRr p eps heps
  obtain ⟨Nk, hNk⟩ := eventually_atTop.mp (hkn.eventually_ge_atTop Njet)
  obtain ⟨Nl, hNl⟩ := eventually_atTop.mp (hln.eventually_ge_atTop Njet)
  obtain ⟨Ns, hNs⟩ := eventually_atTop.mp hsource
  refine ⟨max (max Nk Nl) Ns, ?_⟩
  intro n hn j hj z hzK
  have hnK : Nk ≤ n := (le_max_left Nk Nl).trans
    ((le_max_left (max Nk Nl) Ns).trans hn)
  have hnL : Nl ≤ n := (le_max_right Nk Nl).trans
    ((le_max_left (max Nk Nl) Ns).trans hn)
  have hnS : Ns ≤ n := (le_max_right (max Nk Nl) Ns).trans hn
  have hzV : z ∈ V := hKV hzK
  have hzInt : z ∈ interior (C0 alpha) := hVint hzV
  have hjet := hNjet (kn n) (hNk n hnK) (ln n) (hNl n hnL)
    alpha z (interior_subset hzInt)
  have hsrc := hNs n hnS hzV
  simpa only using (hjet hzInt hsrc).2.2 j hj

theorem HasStageJetConvergenceOn.pb_convergence
    (inp : MetricCompactSeedWithDivisor (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (chart : NormalChartFamily (I := I) X)
    (Vmetric U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (gInf : LiveSlot L inp.pack r →
      E → (E →L[Real] E →L[Real] Real))
    (hstage : HasStageJetConvergenceOn (I := I) inp P L hr phi hphi chart
      Vmetric U C0 C1 aInf Jinf Jbarinf gInf)
    (R : Real) (hRr : R < r) (alpha : LiveSlot L inp.pack r)
    (V W : Set E) (hVopen : IsOpen V) (hVcompact : IsCompact (closure V))
    (hVW : closure V ⊆ W) (hWint : W ⊆ interior (C0 alpha))
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
      Set.MapsTo
        (chart (Lphi.φ (kn n))
          (seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat))).hom
        W (Lphi.hatSourceBall inp.decay P R (kn n))) :
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
      let chiK := chart (Lphi.φ (kn n))
        (seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat))
      let chiL := chart (Lphi.φ (ln n))
        (seqCenterD inp.decay P Lphi (ln n) (alpha.1 : Nat))
      chiL.inv (stageComparisonMap inp P Lphi r hr
        (kn n) (ln n) (chiK.hom z) (chart := chart))
    let B : Nat → E → (E →L[Real] E →L[Real] Real) := fun n ↦
      chart.metric (Lphi.φ (ln n))
        (seqCenterD inp.decay P Lphi (ln n) (alpha.1 : Nat))
    MapCInfConvergenceOnCompacts V
      (fun n z ↦ _root_.DifferentialGeometry.CheegerGromovCompactness.pullbackForm
        (B n (A n z), fderiv Real (A n) z))
      (gInf alpha) := by
  classical
  let : NormedAddCommGroup (E →L[Real] Real) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace Real (E →L[Real] Real) :=
    ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (E →L[Real] (E →L[Real] Real)) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace Real (E →L[Real] (E →L[Real] Real)) :=
    ContinuousLinearMap.toNormedSpace
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
    let chiK := chart (Lphi.φ (kn n))
      (seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat))
    let chiL := chart (Lphi.φ (ln n))
      (seqCenterD inp.decay P Lphi (ln n) (alpha.1 : Nat))
    chiL.inv (stageComparisonMap inp P Lphi r hr
      (kn n) (ln n) (chiK.hom z) (chart := chart))
  let B : Nat → E → (E →L[Real] E →L[Real] Real) := fun n ↦
    chart.metric (Lphi.φ (ln n))
      (seqCenterD inp.decay P Lphi (ln n) (alpha.1 : Nat))
  change MapCInfConvergenceOnCompacts V
    (fun n z ↦ _root_.DifferentialGeometry.CheegerGromovCompactness.pullbackForm
      (B n (A n z), fderiv Real (A n) z)) (gInf alpha)
  rcases hstage with ⟨hdata, hmetric, hjets, _hbase⟩
  obtain ⟨_hUopen, _hC0compact, _hC1compact, hC01, hC1U⟩ :=
    hdata.core_on inp P L r hr chart U C0 C1 aInf Jinf Jbarinf alpha
  obtain ⟨hC1V, hgInf, hBconv, _hgequiv⟩ := hmetric alpha
  let D : Set E := interior (C0 alpha)
  have hDopen : IsOpen D := isOpen_interior
  have hDU : D ⊆ U alpha :=
    interior_subset.trans (hC01.trans (interior_subset.trans hC1U))
  have hDVmetric : D ⊆ Vmetric alpha :=
    interior_subset.trans (hC01.trans (interior_subset.trans hC1V))
  have hWD : W ⊆ D := hWint
  have hVD : V ⊆ D := subset_closure.trans (hVW.trans hWD)
  have hclosureD : closure V ⊆ D := hVW.trans hWD
  obtain ⟨rho, hrho, hthick⟩ :=
    hVcompact.exists_cthickening_subset_open hDopen hclosureD
  have hAconvW : MapCInfConvergenceOnCompacts W A id := by
    simpa only [A, Lphi] using
      HasStageJetConvergenceOn.chart_convergence (I := I) inp P L hr phi hphi
        chart Vmetric U C0 C1 aInf Jinf Jbarinf gInf
        ⟨hdata, hmetric, hjets, _hbase⟩ R hRr alpha W hWint
        kn ln hkn hln hsource
  have hAconv : MapCInfConvergenceOnCompacts V A id := by
    intro K hK hKV p
    exact hAconvW K hK (hKV.trans (subset_closure.trans hVW)) p
  obtain ⟨Nclose, hNclose⟩ :=
    hAconvW (closure V) hVcompact hVW 0 (rho / 2) (by positivity)
  obtain ⟨Njet, hNjet⟩ := hjets R hRr 0 1 (by norm_num)
  have hgood : ∀ᶠ n in atTop,
      ContDiffOn Real (∞ : WithTop ℕ∞) (A n) V ∧
      Set.MapsTo (A n) V D ∧
      ContDiffOn Real (∞ : WithTop ℕ∞) (B n) D := by
    filter_upwards [hkn.eventually_ge_atTop Njet,
      hln.eventually_ge_atTop Njet, hsource,
      eventually_atTop.2 ⟨Nclose, hNclose⟩] with n hnk hnl hsrc hclose
    have hAcd : ContDiffOn Real (∞ : WithTop ℕ∞) (A n) V := by
      intro z hzV
      have hzW : z ∈ W := hVW (subset_closure hzV)
      have hzInt : z ∈ interior (C0 alpha) := hWint hzW
      have hjet := hNjet (kn n) hnk (ln n) hnl alpha z
        (interior_subset hzInt)
      have hsrcz := hsrc hzW
      simpa only [A, Lphi] using (hjet hzInt hsrcz).2.1.contDiffWithinAt
    have hAmap : Set.MapsTo (A n) V D := by
      intro z hzV
      have hzClosure : z ∈ closure V := subset_closure hzV
      have hzero := hclose 0 le_rfl z hzClosure
      have hdist : dist (A n z) z ≤ rho / 2 := by
        simpa only [mapDerivNorm, norm_iteratedFDeriv_zero, id_eq,
          dist_eq_norm, A, Lphi] using hzero
      have hdistRho : dist (A n z) z < rho := by linarith
      exact hthick (Metric.mem_cthickening_of_dist_le
        (A n z) z rho (closure V) hzClosure hdistRho.le)
    have hBcd : ContDiffOn Real (∞ : WithTop ℕ∞) (B n) D := by
      let Yl := X.obj (Lphi.φ (ln n))
      let : TopologicalSpace Yl.M := Yl.topology
      let : ChartedSpace H Yl.M := Yl.charted
      let : IsManifold I ∞ Yl.M := Yl.smooth
      let : T2Space Yl.M := Yl.t2
      let : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
      let cl := seqCenterD inp.decay P Lphi (ln n) (alpha.1 : Nat)
      let chiL := chart (Lphi.φ (ln n)) cl
      obtain ⟨hRad, _hmap⟩ :=
        hdata.geom_on inp P L r hr chart U C0 C1 aInf Jinf Jbarinf
          (ln n) alpha
      have hsmooth := chiL.metric_cont_diff_on Yl.metric hDopen
        (chiL.smooth_to.mono (hDU.trans hRad))
      simpa only [B, NormalChartFamily.metric, Yl, cl, chiL, Lphi] using hsmooth
    exact ⟨hAcd, hAmap, hBcd⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hgood
  let Ap : Nat → E → E := fun n ↦ if N ≤ n then A n else id
  let Bp : Nat → E → (E →L[Real] E →L[Real] Real) := fun n ↦
    if N ≤ n then B n else gInf alpha
  have hApconv : MapCInfConvergenceOnCompacts V Ap id := by
    apply hAconv.congr_eventually hVopen
    · filter_upwards [eventually_atTop.2 ⟨N, fun n hn ↦ hn⟩] with n hn
      intro z _hz
      simp only [Ap, if_pos hn]
    · exact Set.eqOn_refl id V
  have hBpconv : MapCInfConvergenceOnCompacts D Bp (gInf alpha) := by
    have hBsub : MapCInfConvergenceOnCompacts D B (gInf alpha) := by
      intro K hK hKD p
      exact (hBconv.comp_tendsto_atTop hln) K hK
        (hKD.trans hDVmetric) p
    apply hBsub.congr_eventually hDopen
    · filter_upwards [eventually_atTop.2 ⟨N, fun n hn ↦ hn⟩] with n hn
      intro z _hz
      simp only [Bp, if_pos hn]
    · exact Set.eqOn_refl (gInf alpha) D
  have hApc : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (Ap n) V := by
    intro n
    by_cases hn : N ≤ n
    · simpa only [Ap, if_pos hn] using (hN n hn).1
    · simpa only [Ap, if_neg hn] using
        (contDiff_id : ContDiff Real (∞ : WithTop ℕ∞) (id : E → E)).contDiffOn
  have hBpc : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (Bp n) D := by
    intro n
    by_cases hn : N ≤ n
    · simpa only [Bp, if_pos hn] using (hN n hn).2.2
    · simpa only [Bp, if_neg hn] using hgInf.mono hDVmetric
  have hApmap : ∀ n, Set.MapsTo (Ap n) V D := by
    intro n
    by_cases hn : N ≤ n
    · simpa only [Ap, if_pos hn] using (hN n hn).2.1
    · intro z hz
      simpa only [Ap, if_neg hn, id_eq] using hVD hz
  have hpb := MapCInfConvergenceOnCompacts.pullbackForm_comp_fderiv
    (V := E) (W := E) hVopen hDopen
      hApconv hBpconv hApc
      (contDiff_id : ContDiff Real (∞ : WithTop ℕ∞) (id : E → E)).contDiffOn
      hBpc (hgInf.mono hDVmetric) hVD hApmap
  apply hpb.congr_eventually hVopen
  · filter_upwards [eventually_atTop.2 ⟨N, fun n hn ↦ hn⟩] with n hn
    intro z _hz
    simp only [Ap, Bp, if_pos hn]
  · intro z _hz
    change gInf alpha z =
      _root_.DifferentialGeometry.CheegerGromovCompactness.pullbackForm
        (gInf alpha z, fderiv Real id z)
    rw [fderiv_id]
    ext v w
    rfl

end CheegerGromovCompactness
end DifferentialGeometry
