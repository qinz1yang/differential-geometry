import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
import DifferentialGeometry.Geometry.Metric.UniversalCover.Completeness
import DifferentialGeometry.Geometry.Metric.UniversalCover.Metric
import DifferentialGeometry.Topology.Covering.Smooth.LocalDiffeomorph
import DifferentialGeometry.Topology.Covering.SmoothLift
import DifferentialGeometry.Topology.Manifold.InjectiveLocalDiffeomorph
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Basic
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import DifferentialGeometry.Analysis.Integration.Measure.PullbackCross
import Mathlib.Geometry.Manifold.Instances.Icc

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open MeasureTheory Set Bundle _root_.Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.Integral.Measure
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M] [Inhabited M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [ConnectedSpace M] in
theorem universalCover_image_ball_liftedMetric
    (g : SmoothRiemannianMetric I M) (x : UniversalCover M)
    (r : ℝ) (hr : 0 < r) :
    (UniversalCover.proj : UniversalCover M → M) ''
        riemannianBallOf (I := I) (UniversalCover.liftedMetric (I := I) g) x r =
      riemannianBallOf (I := I) g (UniversalCover.proj x) r := by
  have _hr : 0 < r := hr
  let gL := UniversalCover.liftedMetric (I := I) g
  let _ : RiemannianBundle (fun z : M => TangentSpace I z) := ⟨g.toRiemannianMetric⟩
  let _ : RiemannianBundle (fun z : UniversalCover M => TangentSpace I z) :=
    ⟨gL.toRiemannianMetric⟩
  let _ : ∀ z : M, InnerProductSpace ℝ (TangentSpace I z) :=
    fun z => Bundle.instInnerProductSpaceReal (E := fun z : M => TangentSpace I z) z
  let _ : ∀ z : UniversalCover M, InnerProductSpace ℝ (TangentSpace I z) :=
    fun z => Bundle.instInnerProductSpaceReal (E := fun z : UniversalCover M => TangentSpace I z) z
  let _ : ∀ z : M, NormedSpace ℝ (TangentSpace I z) := fun z => inferInstance
  let _ : ∀ z : UniversalCover M, NormedSpace ℝ (TangentSpace I z) := fun z => inferInstance
  have hcrb : IsContinuousRiemannianBundle E (fun z : M => TangentSpace I z) :=
    ⟨⟨fun z => g.inner z, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  have hcrbL : IsContinuousRiemannianBundle E (fun z : UniversalCover M => TangentSpace I z) :=
    ⟨⟨fun z => gL.inner z, gL.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  have _hlcm : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional (M := M) I
  let _ : RegularSpace M := inferInstance
  let _ : RegularSpace (UniversalCover M) := UniversalCover.uc_regularSpace (M := M) I
  let _ : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  let _ : PseudoEMetricSpace (UniversalCover M) :=
    UniversalCover.ucPseudoEMetricSpace (I := I) (M := M) gL
  have hnorm : ∀ (z : M) (v : TangentSpace I z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner z v v)) := by
    intro z v
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    congr 1
  have hnormL : ∀ (z : UniversalCover M) (v : TangentSpace I z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gL.inner z v v)) := by
    intro z v
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    congr 1
  ext y
  constructor
  · rintro ⟨x', hx', rfl⟩
    have hlip := UniversalCover.proj_lipschitzWith_one (I := I) (M := M) g hnorm hnormL
    have h := hlip x x'
    rw [ENNReal.coe_one, one_mul] at h
    rw [IsRiemannianManifold.out (I := I) (M := UniversalCover M) x x',
      IsRiemannianManifold.out (I := I) (M := M) (UniversalCover.proj x)
        (UniversalCover.proj x')] at h
    exact lt_of_le_of_lt h hx'
  · intro hy
    obtain ⟨γ, hγ0, hγ1, hγsmooth, hγlen⟩ :=
      Manifold.exists_lt_of_riemannianEDist_lt (I := I) (M := M) hy
    let γc : C(unitInterval, M) :=
      ⟨fun t => γ (t : ℝ),
        hγsmooth.continuousOn.comp_continuous continuous_subtype_val (fun t => t.2)⟩
    have hγc0 : γc 0 = UniversalCover.proj x := by
      change γ (0 : ℝ) = UniversalCover.proj x
      rw [hγ0]
    let Γ : C(unitInterval, UniversalCover M) :=
      (UniversalCover.proj_isCoveringMap).liftPath γc x hγc0
    have hΓ_lifts : UniversalCover.proj ∘ Γ = γc :=
      IsCoveringMap.liftPath_lifts (UniversalCover.proj_isCoveringMap) γc x hγc0
    have hΓ0 : Γ 0 = x :=
      IsCoveringMap.liftPath_zero (UniversalCover.proj_isCoveringMap) γc x hγc0
    have hΓproj : ∀ t, UniversalCover.proj (Γ t) = γc t := fun t => congr_fun hΓ_lifts t
    have hγcsmooth : ContMDiff (𝓡∂ 1) I 1 γc := by
      rw [← contMDiffOn_comp_projIcc_iff (x := (0 : ℝ)) (y := 1)]
      refine hγsmooth.congr (fun t ht => ?_)
      change γ ↑(Set.projIcc 0 1 zero_le_one t) = γ t
      rw [Set.projIcc_of_mem zero_le_one ht]
    have hΓsmooth : ContMDiff (𝓡∂ 1) I 1 Γ :=
      DifferentialGeometry.Topology.contMDiff_one_of_lift_through_localDiffeomorph
        (p := (UniversalCover.proj : UniversalCover M → M))
        UniversalCover.proj_localDiffeo hγcsmooth Γ hΓproj
    let Γℝ : ℝ → UniversalCover M := fun t => Γ (Set.projIcc 0 1 zero_le_one t)
    have hΓℝsmooth : ContMDiffOn 𝓘(ℝ, ℝ) I 1 Γℝ (Set.Icc (0 : ℝ) 1) :=
      contMDiffOn_comp_projIcc_iff.mpr hΓsmooth
    have hΓℝ0 : Γℝ 0 = x := by
      change Γ (Set.projIcc 0 1 zero_le_one 0) = x
      simpa using hΓ0
    have hproj_Γℝ : ∀ t ∈ Set.Icc (0 : ℝ) 1, UniversalCover.proj (Γℝ t) = γ t := by
      intro t ht
      change UniversalCover.proj (Γ (Set.projIcc 0 1 zero_le_one t)) = γ t
      rw [hΓproj, Set.projIcc_of_mem zero_le_one ht]
      rfl
    have hlen_eq : pathELength I (fun t => UniversalCover.proj (Γℝ t)) 0 1 =
        pathELength I γ 0 1 :=
      pathELength_congr (fun t ht => hproj_Γℝ t ht)
    have hlen_proj : pathELength I (fun t => UniversalCover.proj (Γℝ t)) 0 1 =
        pathELength I Γℝ 0 1 :=
      UniversalCover.proj_pathELength_eq (I := I) (M := M) g hnorm hnormL hΓℝsmooth
    have hed : riemannianEDistOf (I := I) gL x (Γℝ 1) ≤ pathELength I Γℝ 0 1 :=
      Manifold.riemannianEDist_le_pathELength (I := I) (M := UniversalCover M) hΓℝsmooth
        hΓℝ0 rfl zero_le_one
    refine ⟨Γℝ 1, ?_, ?_⟩
    · calc riemannianEDistOf (I := I) gL x (Γℝ 1) ≤ pathELength I Γℝ 0 1 := hed
        _ = pathELength I (fun t => UniversalCover.proj (Γℝ t)) 0 1 := hlen_proj.symm
        _ = pathELength I γ 0 1 := hlen_eq
        _ < ENNReal.ofReal r := hγlen
    · rw [hproj_Γℝ 1 (by norm_num)]
      exact hγ1

variable [SecondCountableTopology M]

private local instance upstreamCoverVolumeMeasurable : MeasurableSpace M := borel M
private local instance upstreamCoverVolumeBorel : BorelSpace M := ⟨rfl⟩
private local instance upstreamCoverVolumeLiftMeasurable :
    MeasurableSpace (UniversalCover M) := borel (UniversalCover M)
private local instance upstreamCoverVolumeLiftBorel :
    BorelSpace (UniversalCover M) := ⟨rfl⟩
private local instance upstreamCoverVolumeC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance upstreamCoverVolumeLiftC1 :
    IsManifold I 1 (UniversalCover M) := IsManifold.of_le (n := ∞) (by decide)

theorem universalCover_volume_image_le
    (g : SmoothRiemannianMetric I M) (U : Set (UniversalCover M)) (hU : IsOpen U) :
    riemannianVolumeMeasure (I := I) (M := M) g
        ((UniversalCover.proj : UniversalCover M → M) '' U) ≤
      riemannianVolumeMeasure (I := I) (M := UniversalCover M)
        (UniversalCover.liftedMetric (I := I) g) U := by
  classical
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let _ : LocallyPathConnectedSpace (UniversalCover M) :=
    ChartedSpace.locallyPathConnectedSpace H (UniversalCover M)
  let _ : SecondCountableTopology (UniversalCover M) :=
    ChartedSpace.secondCountable_of_sigmaCompact H (UniversalCover M)
  let gX := UniversalCover.liftedMetric (I := I) g
  let μX := riemannianVolumeMeasure (I := I) (M := UniversalCover M) gX
  let μM := riemannianVolumeMeasure (I := I) (M := M) g
  let proj := UniversalCover.proj (X := M)
  have hloc : IsLocalHomeomorph proj :=
    isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
      ((UniversalCover.proj_isCoveringMap (X := M)).isCoveringMapOn.isLocalHomeomorphOn)
  have hshrink : ∀ q : UniversalCover M,
      ∃ O : Set (UniversalCover M), IsOpen O ∧ q ∈ O ∧ Set.InjOn proj O := by
    intro q
    obtain ⟨e, hqe, heq⟩ := hloc q
    refine ⟨e.source, e.open_source, hqe, ?_⟩
    rw [heq]
    exact e.injOn
  obtain ⟨b, hb⟩ := TopologicalSpace.exists_seq_basis (α := UniversalCover M)
  have hcover : ∀ q ∈ U, ∃ n : ℕ, q ∈ b n ∧ Set.InjOn proj (b n) := by
    intro q hq
    obtain ⟨O, hOopen, hqO, hOinj⟩ := hshrink q
    obtain ⟨s, hs, hqs, hsub⟩ :=
      hb.exists_subset_of_mem_open (by exact ⟨hq, hqO⟩ : q ∈ U ∩ O) (hU.inter hOopen)
    obtain ⟨n, rfl⟩ := hs
    exact ⟨n, hqs, fun y hy z hz hyz => hOinj (hsub hy).2 (hsub hz).2 hyz⟩
  let S : ℕ → Set (UniversalCover M) :=
    fun n => if Set.InjOn proj (b n) then b n else ∅
  have hS_open : ∀ n, IsOpen (S n) := by
    intro n
    by_cases h : Set.InjOn proj (b n)
    · have hSn : S n = b n := by dsimp only [S]; rw [ite_eq_left h]
      rw [hSn]
      exact hb.isOpen (Set.mem_range_self n)
    · have hSn : S n = ∅ := by dsimp only [S]; rw [ite_eq_right h]
      rw [hSn]
      exact isOpen_empty
  have hS_inj : ∀ n, Set.InjOn proj (S n) := by
    intro n
    by_cases h : Set.InjOn proj (b n)
    · have hSn : S n = b n := by dsimp only [S]; rw [ite_eq_left h]
      rw [hSn]; exact h
    · have hSn : S n = ∅ := by dsimp only [S]; rw [ite_eq_right h]
      rw [hSn]; exact Set.injOn_empty (f := proj)
  have hS_cover : U ⊆ ⋃ n, S n := by
    intro q hq
    obtain ⟨n, hqn, hinj⟩ := hcover q hq
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    have hSn : S n = b n := by dsimp only [S]; rw [ite_eq_left hinj]
    rw [hSn]; exact hqn
  let D : ℕ → Set (UniversalCover M) := fun n => S n \ ⋃ m < n, S m
  have hDS : ∀ n, D n ⊆ S n := fun n => Set.sdiff_subset
  have hD_meas : ∀ n, MeasurableSet (D n) := fun n =>
    (hS_open n).measurableSet.diff (MeasurableSet.biUnion (Set.to_countable _)
      (fun m _ => (hS_open m).measurableSet))
  have hD_disj : Pairwise (Function.onFun Disjoint D) := by
    intro m n hmn
    change Disjoint (D m) (D n)
    rw [Set.disjoint_left]
    intro q hqm hqn
    rcases lt_or_gt_of_ne hmn with hlt | hlt
    · have hmem : q ∈ ⋃ m < n, S m := Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨hlt, hqm.1⟩⟩
      exact hqn.2 hmem
    · have hmem : q ∈ ⋃ n < m, S n := Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨hlt, hqn.1⟩⟩
      exact hqm.2 hmem
  have hDU : U ⊆ ⋃ n, D n := by
    intro q hq
    have hex : ∃ n, q ∈ S n := Set.mem_iUnion.mp (hS_cover hq)
    refine Set.mem_iUnion.mpr ⟨Nat.find hex, ?_⟩
    refine ⟨Nat.find_spec hex, ?_⟩
    · intro hmem
      obtain ⟨m, hmem'⟩ := Set.mem_iUnion.mp hmem
      obtain ⟨hm, hmq⟩ := Set.mem_iUnion.mp hmem'
      exact Nat.find_min hex hm hmq
  let A : ℕ → Set (UniversalCover M) := fun n => U ∩ D n
  have hAS : ∀ n, A n ⊆ S n := fun n => fun q hq => hDS n hq.2
  have hAD : ∀ n, A n ⊆ D n := fun n => Set.inter_subset_right
  have hAU : ∀ n, A n ⊆ U := fun n => Set.inter_subset_left
  have hA_meas : ∀ n, MeasurableSet (A n) := fun n =>
    hU.measurableSet.inter (hD_meas n)
  have hA_disj : Pairwise (Function.onFun Disjoint A) := fun m n hmn =>
    (hD_disj hmn).mono (hAD m) (hAD n)
  have hA_eq : U = ⋃ n, A n := by
    refine Set.Subset.antisymm ?_ ?_
    · intro q hq
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hDU hq)
      exact Set.mem_iUnion.mpr ⟨n, hq, hn⟩
    · intro q hq
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hq
      exact (hAU n) hn
  have hkey : ∀ n, μX (A n) = μM (proj '' A n) := by
    intro n
    obtain ⟨Φ, hsrc, htgt, hcoe⟩ :=
      DifferentialGeometry.Topology.Manifold.exists_partialDiffeomorph_of_injOn
        (I := I) (J := I) (f := proj) (S := S n) (hS_open n)
        ((UniversalCover.proj_localDiffeo (I := I) (M := M)).isLocalDiffeomorphOn (S n))
        (hS_inj n)
    let Φ₁ : PartialDiffeomorph I I (UniversalCover M) M 1 :=
      DifferentialGeometry.PartialDiffeomorph.ofLE Φ (by norm_num)
    have hsrc₁ : Φ₁.source = S n := hsrc
    have htgt₁ : Φ₁.target = proj '' S n := htgt
    have hcoe₁ : (Φ₁ : UniversalCover M → M) = proj := hcoe
    have hisom : ∀ x ∈ Φ₁.source, ∀ v w : TangentSpace I x,
        gX.inner x v w =
          g.inner (Φ₁ x) (mfderiv I I Φ₁ x v) (mfderiv I I Φ₁ x w) := by
      intro x _ v w
      have hd : mfderiv I I Φ₁ x = ContinuousLinearMap.id ℝ E := by
        rw [show (Φ₁ : UniversalCover M → M) = proj from hcoe₁]
        exact (UniversalCover.hasMFDerivAt_proj (I := I) (M := M) x).mfderiv
      have hcoe_x : Φ₁ x = proj x := congrFun hcoe₁ x
      change g.inner (proj x) v w =
        g.inner (Φ₁ x) (mfderiv I I Φ₁ x v) (mfderiv I I Φ₁ x w)
      rw [hcoe_x, hd]
      rfl
    have hvol := riemannianVolumeMeasure_partialIsometry (I := I) (J := I)
      gX g Φ₁ hisom
    have hAΦ : A n ⊆ Φ₁.source := by rw [hsrc₁]; exact hAS n
    have hsymm_meas : AEMeasurable (Φ₁.symm : M → UniversalCover M)
        (μM.restrict Φ₁.target) :=
      Φ₁.contMDiffOn_invFun.continuousOn.aemeasurable Φ₁.open_target.measurableSet
    have hset : ((Φ₁.symm : M → UniversalCover M) ⁻¹' A n) ∩ Φ₁.target = proj '' A n := by
      ext y
      constructor
      · rintro ⟨hyA, hyT⟩
        refine ⟨(Φ₁.symm : M → UniversalCover M) y, hyA, ?_⟩
        have hright : Φ₁.toPartialEquiv.toFun (Φ₁.toPartialEquiv.invFun y) = y :=
          Φ₁.toPartialEquiv.right_inv hyT
        calc proj ((Φ₁.symm : M → UniversalCover M) y)
            = Φ₁.toPartialEquiv.toFun (Φ₁.toPartialEquiv.invFun y) :=
              (congrFun hcoe₁ (Φ₁.toPartialEquiv.invFun y)).symm
          _ = y := hright
      · rintro ⟨q, hqA, rfl⟩
        have hqS : q ∈ S n := hAS n hqA
        have hqx : q ∈ Φ₁.source := by rw [hsrc₁]; exact hqS
        have hleft : Φ₁.toPartialEquiv.invFun (Φ₁.toPartialEquiv.toFun q) = q :=
          Φ₁.toPartialEquiv.left_inv hqx
        have hcoe_q : Φ₁.toPartialEquiv.toFun q = proj q := congrFun hcoe₁ q
        refine ⟨?_, ?_⟩
        · change Φ₁.toPartialEquiv.invFun (proj q) ∈ A n
          rw [← hcoe_q]
          rw [hleft]
          exact hqA
        · rw [htgt₁]
          exact ⟨q, hqS, rfl⟩
    calc μX (A n) = (μX.restrict Φ₁.source) (A n) := by
          rw [Measure.restrict_apply' Φ₁.open_source.measurableSet,
            Set.inter_eq_self_of_subset_left hAΦ]
      _ = (Measure.map (Φ₁.symm : M → UniversalCover M) (μM.restrict Φ₁.target)) (A n) := by
          rw [hvol]
      _ = (μM.restrict Φ₁.target) ((Φ₁.symm : M → UniversalCover M) ⁻¹' A n) :=
          Measure.map_apply_of_aemeasurable hsymm_meas (hA_meas n)
      _ = μM (proj '' A n) := by
          rw [Measure.restrict_apply' Φ₁.open_target.measurableSet, hset]
  calc μM (proj '' U) = μM (⋃ n, proj '' A n) := by
        rw [hA_eq, Set.image_iUnion]
    _ ≤ ∑' n, μM (proj '' A n) := measure_iUnion_le _
    _ = ∑' n, μX (A n) := tsum_congr fun n => (hkey n).symm
    _ = μX (⋃ n, A n) := (measure_iUnion hA_disj hA_meas).symm
    _ = μX U := by rw [← hA_eq]

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
