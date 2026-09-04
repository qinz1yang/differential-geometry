import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.ChartFamily
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.CenterOfMass.NormalCoordinates.InverseVelocityConvergence

import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.DiagonalInverse.Convergence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.CenterMap.Construction.Fill
import DifferentialGeometry.Analysis.Calculus.Inverse.MovingImplicit
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped ContDiff Topology

namespace DifferentialGeometry
namespace CheegerGromovCompactness

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

theorem invVelocitySub_convergence_on
    (inp : MetricCompactCore (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (alpha : LiveSlot L inp.pack r)
    (kn ln : Nat → Nat) {S : Set E} (hS : IsOpen S)
    (weightInf : E → Fin (inp.pack.A r) → Real)
    {chart : NormalChartFamily (I := I) X}
    (hcfgC : ∀ m, ContDiffOn Real (∞ : WithTop ℕ∞)
      (stageConfigurationSub inp P L hr phi hphi alpha (kn m) (ln m)
        (chart := chart)) S)
    (hcfgInfC : ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun z => (weightInf z,
        fun _ : Fin (inp.pack.A r) => z)) S)
    (hcfg : MapCInfConvergenceOnCompacts S
      (fun m => stageConfigurationSub inp P L hr phi hphi alpha (kn m) (ln m)
        (chart := chart))
      (fun z => (weightInf z, fun _ : Fin (inp.pack.A r) => z)))
    (e : Nat → OpenPartialHomeomorph (E × E) (E × E))
    (eInf : OpenPartialHomeomorph (E × E) (E × E))
    {V : Set (E × E)} (hV : IsOpen V)
    (heC : ∀ᶠ m in atTop, ContDiffOn Real ∞
      ((e m).symm : E × E → E × E) V)
    (heInfC : ContDiffOn Real ∞
      (eInf.symm : E × E → E × E) V)
    (hinv : MapCInfConvergenceOnCompacts V
      (fun m ↦ ((e m).symm : E × E → E × E)) eInf.symm)
    {D : Set (E × E)} (hD : IsOpen D)
    (hfst : MapsTo (fun q : E × E => q.1) D S)
    (hmap : ∀ᶠ m in atTop, ∀ q, q ∈ D →
      ∀ gamma : Fin (inp.pack.A r),
        (q.2, (stageConfigurationSub inp P L hr phi hphi alpha
          (kn m) (ln m) q.1 (chart := chart)).2 gamma) ∈ V)
    (hmapInf : ∀ q, q ∈ D → (q.2, q.1) ∈ V) :
    MapCInfConvergenceOnCompacts D
      (fun m q => invVelocitySum (e m)
        (stageConfigurationSub inp P L hr phi hphi alpha
          (kn m) (ln m) q.1 (chart := chart)).1
        (stageConfigurationSub inp P L hr phi hphi alpha
          (kn m) (ln m) q.1 (chart := chart)).2 q.2)
      (fun q => invVelocitySum eInf
        (weightInf q.1) (fun _ => q.1) q.2) := by
  have hcfgD : MapCInfConvergenceOnCompacts D
      (fun m q => stageConfigurationSub inp P L hr phi hphi alpha
        (kn m) (ln m) q.1 (chart := chart))
      (fun q => (weightInf q.1,
        fun _ : Fin (inp.pack.A r) => q.1)) :=
    hcfg.precomp hD hS contDiff_fst.contDiffOn hfst hcfgC hcfgInfC
  have hcfgDC : ∀ m, ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun q : E × E => stageConfigurationSub inp P L hr phi hphi alpha
        (kn m) (ln m) q.1 (chart := chart)) D :=
    fun m => (hcfgC m).comp contDiff_fst.contDiffOn hfst
  have hcfgInfDC : ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun q : E × E => (weightInf q.1,
        fun _ : Fin (inp.pack.A r) => q.1)) D :=
    hcfgInfC.comp contDiff_fst.contDiffOn hfst
  have hctr : MapCInfConvergenceOnCompacts D
      (fun _ : Nat => fun q : E × E => q.2) (fun q : E × E => q.2) :=
    mapCInfConvergence_const (fun q : E × E => q.2)
  exact NormalBranchHessian.invVelocityConfiguration_tail
    (ι := Fin (inp.pack.A r)) (U := D) (V := V)
    (e := e) (eInf := eInf)
    (configuration := fun m q => stageConfigurationSub inp P L hr phi hphi alpha
      (kn m) (ln m) q.1 (chart := chart))
    (configurationInf := fun q => (weightInf q.1,
      fun _ : Fin (inp.pack.A r) => q.1))
    (ctr := fun _ : Nat => fun q : E × E => q.2)
    (ctrInf := fun q : E × E => q.2)
    hD hV hinv hcfgD hctr heC heInfC hcfgDC hcfgInfDC
    (fun _ => contDiff_snd.contDiffOn) contDiff_snd.contDiffOn
    hmap (fun q hq _ => hmapInf q hq)

theorem invVelocitySub_convergence
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (alpha : LiveSlot L inp.pack r)
    (kn ln : Nat → Nat) {S : Set E} (hS : IsOpen S)
    (weightInf : E → Fin (inp.pack.A r) → Real)
    {chart : NormalChartFamily (I := I) X}
    (hcfgC : ∀ m, ContDiffOn Real (∞ : WithTop ℕ∞)
      (stageConfigurationSub inp.toCore P L hr phi hphi alpha (kn m) (ln m)
        (chart := chart)) S)
    (hcfgInfC : ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun z => (weightInf z,
        fun _ : Fin (inp.pack.A r) => z)) S)
    (hcfg : MapCInfConvergenceOnCompacts S
      (fun m => stageConfigurationSub inp.toCore P L hr phi hphi alpha (kn m) (ln m)
        (chart := chart))
      (fun z => (weightInf z, fun _ : Fin (inp.pack.A r) => z)))
    (e : Nat → OpenPartialHomeomorph (E × E) (E × E))
    (eInf : OpenPartialHomeomorph (E × E) (E × E))
    (hinvData : ∃ delta0 : Real, 0 < delta0 ∧
      (∀ n, ContDiffOn Real ∞
        ((e n).symm : E × E → E × E) (Metric.ball 0 delta0)) ∧
      ContDiffOn Real ∞ (eInf.symm : E × E → E × E)
        (Metric.ball 0 delta0) ∧
      MapCInfConvergenceOnCompacts (Metric.ball 0 delta0)
        (fun n ↦ ((e n).symm : E × E → E × E)) eInf.symm)
    (nn : Nat → Nat) (hnn : Tendsto nn atTop atTop) :
    ∃ delta0 : Real, 0 < delta0 ∧
      ∀ (D : Set (E × E)), IsOpen D →
        MapsTo (fun q : E × E => q.1) D S →
        (∀ m q, q ∈ D → ∀ gamma : Fin (inp.pack.A r),
          (q.2, (stageConfigurationSub inp.toCore P L hr phi hphi alpha
            (kn m) (ln m) q.1 (chart := chart)).2 gamma) ∈
              Metric.ball 0 delta0) →
        (∀ q, q ∈ D → (q.2, q.1) ∈ Metric.ball 0 delta0) →
        MapCInfConvergenceOnCompacts D
          (fun m q => invVelocitySum (e (nn m))
            (stageConfigurationSub inp.toCore P L hr phi hphi alpha
              (kn m) (ln m) q.1 (chart := chart)).1
            (stageConfigurationSub inp.toCore P L hr phi hphi alpha
              (kn m) (ln m) q.1 (chart := chart)).2 q.2)
      (fun q => invVelocitySum eInf
            (weightInf q.1) (fun _ => q.1) q.2) := by
  rcases hinvData with ⟨delta0, hdelta0, heC, heInfC, hinv⟩
  refine ⟨delta0, hdelta0, ?_⟩
  intro D hD hfst hmap hmapInf
  have he := hinv.comp_tendsto_atTop hnn
  exact invVelocitySub_convergence_on inp.toCore P L hr phi hphi alpha kn ln hS weightInf
    hcfgC hcfgInfC hcfg (fun m => e (nn m)) eInf Metric.isOpen_ball
    (Filter.Eventually.of_forall fun m => heC (nn m)) heInfC he hD hfst
    (Filter.Eventually.of_forall hmap) hmapInf

theorem HasSupportedCenterMapConvergence.invVelocity_sub_convergence
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (hdata : HasSupportedCenterMapConvergence (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf)
    (alpha : LiveSlot L inp.pack r)
    (e : Nat → OpenPartialHomeomorph (E × E) (E × E))
    (eInf : OpenPartialHomeomorph (E × E) (E × E))
    (hinvData : ∃ delta0 : Real, 0 < delta0 ∧
      (∀ n, ContDiffOn Real ∞
        ((e n).symm : E × E → E × E) (Metric.ball 0 delta0)) ∧
      ContDiffOn Real ∞ (eInf.symm : E × E → E × E)
        (Metric.ball 0 delta0) ∧
      MapCInfConvergenceOnCompacts (Metric.ball 0 delta0)
        (fun n ↦ ((e n).symm : E × E → E × E)) eInf.symm)
    (nn kn ln : Nat → Nat) (hnn : Tendsto nn atTop atTop)
    (hkn : Tendsto kn atTop atTop) (hln : Tendsto ln atTop atTop) :
    let i0 := baseIndex inp.decay inp.realizes inp.pack hr
    let weightInf := fun z gamma =>
      rawWeights (cutRaw (aInf alpha i0) (aInf alpha) i0) z gamma
    ∃ delta0 : Real, 0 < delta0 ∧
      ∀ (D : Set (E × E)), IsOpen D →
        MapsTo (fun q : E × E => q.1) D (U alpha) →
        (∀ m q, q ∈ D → ∀ gamma : Fin (inp.pack.A r),
          (q.2, (stageConfigurationSub inp P L hr phi hphi alpha
            (kn m) (ln m) q.1).2 gamma) ∈ Metric.ball 0 delta0) →
        (∀ q, q ∈ D → (q.2, q.1) ∈ Metric.ball 0 delta0) →
        MapCInfConvergenceOnCompacts D
          (fun m q => invVelocitySum (e (nn m))
            (stageConfigurationSub inp P L hr phi hphi alpha
              (kn m) (ln m) q.1).1
            (stageConfigurationSub inp P L hr phi hphi alpha
              (kn m) (ln m) q.1).2 q.2)
          (fun q => invVelocitySum eInf
            (weightInf q.1) (fun _ => q.1) q.2) := by
  dsimp only
  let i0 := baseIndex inp.decay inp.realizes inp.pack hr
  let weightInf := fun z gamma =>
    rawWeights (cutRaw (aInf alpha i0) (aInf alpha) i0) z gamma
  have hdata0 := hdata
  have hUopen : IsOpen (U alpha) := by
    dsimp only [HasSupportedCenterMapConvergence] at hdata0
    exact hdata0.1 alpha
  obtain ⟨hcfgC, hcfgInfC, hcfg⟩ :=
    hdata.configurationSub_data inp P L hr phi hphi U C0 C1 aInf Jinf Jbarinf
      kn ln hkn hln alpha
  exact invVelocitySub_convergence inp P L hr phi hphi alpha kn ln hUopen weightInf
    hcfgC hcfgInfC hcfg e eInf hinvData nn hnn

theorem HasDiagPairConvergence.exists_invVelocity_on
    {hcomplete : SeqMetricComplete (I := I) X}
    {hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M}
    {c : ∀ n : Nat, (X.obj n).M}
    {qStage qInf : NNReal} {deltaStage deltaInf : Real}
    {e : Nat → OpenPartialHomeomorph (E × E) (E × E)}
    {eInf : OpenPartialHomeomorph (E × E) (E × E)}
    {chart : NormalChartFamily (I := I) X}
    (hpair : HasDiagPairConvergence (I := I) hcomplete hconn c
      qStage qInf deltaStage deltaInf e eInf (chart := chart))
    {ι : Type} [Fintype ι]
    {S K : Set E} {V : Set (E × E)}
    (hS : IsOpen S) (hK : IsCompact K) (hV : IsOpen V)
    {mu : E → ι → Real}
    (hmuC : ContDiffOn Real (∞ : WithTop ℕ∞) mu S)
    (hmu : centerAverage.WeightDataOn S (fun _ : ι => Set.univ) mu)
    (hKS : K ⊆ S) (hKq : K ⊆ Metric.ball (0 : E) qInf)
    (hVt : V ⊆ eInf.target)
    (hdiagV : (fun z : E ↦ (z, z)) '' K ⊆ V) :
    let swap : E × E → E × E := fun q => (q.2, q.1)
    let D : Set (E × E) :=
      (S ×ˢ Set.univ) ∩ swap ⁻¹' V
    let FInf : E × E → E := fun q =>
      invVelocitySum eInf (mu q.1) (fun _ : ι => q.1) q.2
    ∃ (W₀ : Set E) (PhiInf : E → E),
      Set.EqOn PhiInf id K ∧
      Nonempty (Analysis.CompactRootTube D W₀ K FInf PhiInf) := by
  classical
  rcases hpair with
    ⟨_hqStage, _hqInf, _hqInfStage, _hdeltaStage, _hdeltaInf,
      _hnormal, _hInfSource, _hInfZero, _hInfTarget, _hInfC,
      hInfSymmC, hInfDiag, ⟨eta, heta, hInfApprox⟩, _hforward,
      _delta0, _hdelta0, _hdelta0lt, _himage, _hstageMap, _hinv⟩
  dsimp only
  let swap : E × E → E × E := fun q => (q.2, q.1)
  let D : Set (E × E) := (S ×ˢ Set.univ) ∩ swap ⁻¹' V
  let FInf : E × E → E := fun q =>
    invVelocitySum eInf (mu q.1) (fun _ : ι => q.1) q.2
  have hswapC : Continuous swap := by
    dsimp only [swap]
    fun_prop
  have hD : IsOpen D := by
    exact (hS.prod isOpen_univ).inter (hV.preimage hswapC)
  have hmuD : ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun q : E × E => mu q.1) D :=
    hmuC.comp contDiff_fst.contDiffOn (fun q hq => hq.1.1)
  have hxiD : ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun q : E × E => fun _ : ι => q.1) D :=
    contDiffOn_pi.mpr fun _ => contDiff_fst.contDiffOn
  have hFInf : ContDiffOn Real (∞ : WithTop ℕ∞) FInf D := by
    apply NormalBranchHessian.invVelocitySum_contDiff (hInfSymmC.mono hVt) hmuD hxiD
      contDiff_snd.contDiffOn
    intro q hq i
    exact hq.2
  have hgraph : Set.MapsTo (fun z : E => (z, z)) K D := by
    intro z hz
    exact ⟨⟨hKS hz, Set.mem_univ z⟩, hdiagV ⟨z, hz, rfl⟩⟩
  have hroot : ∀ z ∈ K, FInf (z, z) = 0 := by
    intro z hz
    have hdiag := (hInfDiag z (hKq hz)).2
    simp only [FInf, invVelocitySum, hdiag, smul_zero,
      Finset.sum_const_zero]
  have hinv : ∀ z ∈ K,
      (Analysis.partialFDeriv₂ FInf z z).IsInvertible := by
    intro z hz
    obtain ⟨L, hL⟩ := invVelocitySum_inv eInf
      (mu z) (fun _ : ι => z) hInfSymmC
      (fun _ => (hInfDiag z (hKq hz)).1) hInfApprox
      (hmu.nonneg z (hKS hz)) (hmu.sum_one z (hKS hz)) heta
    have hFAt : DifferentiableAt Real FInf (z, z) :=
      (hFInf.contDiffAt (hD.mem_nhds (hgraph hz))).differentiableAt (by simp)
    have hslice : HasFDerivAt (fun u => FInf (z, u))
        (L : E →L[Real] E) z := by
      simpa only [FInf] using hL
    exact ⟨L, (Analysis.partialFDeriv₂_eq hFAt hslice).symm⟩
  exact Analysis.exists_rootTube hD hK hFInf continuousOn_id hgraph hroot hinv

theorem HasDiagPairConvergence.exists_invVelocity_tube
    {hcomplete : SeqMetricComplete (I := I) X}
    {hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M}
    {c : ∀ n : Nat, (X.obj n).M}
    {qStage qInf : NNReal} {deltaStage deltaInf : Real}
    {e : Nat → OpenPartialHomeomorph (E × E) (E × E)}
    {eInf : OpenPartialHomeomorph (E × E) (E × E)}
    {chart : NormalChartFamily (I := I) X}
    (hpair : HasDiagPairConvergence (I := I) hcomplete hconn c
      qStage qInf deltaStage deltaInf e eInf (chart := chart))
    {ι : Type} [Fintype ι]
    {S K : Set E} (hS : IsOpen S) (hK : IsCompact K)
    {mu : E → ι → Real}
    (hmuC : ContDiffOn Real (∞ : WithTop ℕ∞) mu S)
    (hmu : centerAverage.WeightDataOn S (fun _ : ι => Set.univ) mu)
    (hKS : K ⊆ S) (hKq : K ⊆ Metric.ball (0 : E) qInf) :
    let swap : E × E → E × E := fun q => (q.2, q.1)
    let D : Set (E × E) :=
      (S ×ˢ Set.univ) ∩ swap ⁻¹' eInf.target
    let FInf : E × E → E := fun q =>
      invVelocitySum eInf (mu q.1) (fun _ : ι => q.1) q.2
    ∃ (W₀ : Set E) (PhiInf : E → E),
      Set.EqOn PhiInf id K ∧
      Nonempty (Analysis.CompactRootTube D W₀ K FInf PhiInf) := by
  have hpair0 := hpair
  rcases hpair0 with
    ⟨_hqStage, _hqInf, _hqInfStage, _hdeltaStage, _hdeltaInf,
      _hnormal, _hInfSource, _hInfZero, _hInfTarget, _hInfC,
      _hInfSymmC, hInfDiag, _hInfApprox, _hforward,
      _delta0, _hdelta0, _hdelta0lt, _himage, _hstageMap, _hinv⟩
  exact hpair.exists_invVelocity_on hS hK eInf.open_target hmuC hmu hKS hKq
    subset_rfl (by
      rintro _ ⟨z, hz, rfl⟩
      exact (hInfDiag z (hKq hz)).1)

end CheegerGromovCompactness
end DifferentialGeometry
