import DifferentialGeometry.Analysis.Integration.Measure.PullbackCross
import DifferentialGeometry.Geometry.Metric.Pullback.Local
import Mathlib.Topology.Compactness.SigmaCompact

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Topology
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace N := borel N
private local instance : BorelSpace N := ⟨rfl⟩

private def partialDiffeomorphOfLe (Φ : PartialDiffeomorph I I M N ∞) :
    PartialDiffeomorph I I M N 1 where
  toPartialEquiv := Φ.toPartialEquiv
  open_source := Φ.open_source
  open_target := Φ.open_target
  contMDiffOn_toFun := Φ.contMDiffOn_toFun.of_le (by simp)
  contMDiffOn_invFun := Φ.contMDiffOn_invFun.of_le (by simp)

omit [SigmaCompactSpace M] [T2Space N] [SigmaCompactSpace N] in
private theorem inner_eq_of_eq_localPullMetric_of_isRightInverse
    (gM : SmoothRiemannianMetric I M) (gN : SmoothRiemannianMetric I N)
    {p : M → N} (hp : IsLocalDiffeomorph I I ∞ p)
    (hpull : localPullMetric gN p hp = gM)
    (ψ : PartialDiffeomorph I I N M 1)
    (hright : ∀ y ∈ ψ.source, p (ψ y) = y)
    {y : N} (hy : y ∈ ψ.source) (v w : TangentSpace I y) :
    gN.inner y v w =
      gM.inner (ψ y) (mfderiv I I (ψ : N → M) y v) (mfderiv I I (ψ : N → M) y w) := by
  have hMdψ : MDiffAt (ψ : N → M) y := ψ.mdifferentiableAt (by decide) hy
  have hMdp : MDiffAt p (ψ y) := hp.contMDiff.mdifferentiableAt (by simp)
  have hev : (p ∘ (ψ : N → M)) =ᶠ[𝓝 y] id :=
    Filter.eventuallyEq_of_mem (ψ.open_source.mem_nhds hy) (fun z hz => hright z hz)
  have hchain : mfderiv I I (p ∘ (ψ : N → M)) y =
      ContinuousLinearMap.id ℝ (TangentSpace I y) := by
    rw [hev.mfderiv_eq, mfderiv_id]
  have hpψ : ∀ v : TangentSpace I y,
      mfderiv I I p (ψ y) (mfderiv I I (ψ : N → M) y v) = v := by
    intro v
    have h := mfderiv_comp_apply (I := I) (I' := I) (I'' := I) y hMdp hMdψ v
    rw [hchain] at h
    exact h.symm
  rw [← hpull]
  rw [localPullMetric_inner]
  rw [hpψ v, hpψ w, hright y hy]

private theorem map_restrict_source_eq_restrict_target
    [I.Boundaryless]
    (gM : SmoothRiemannianMetric I M) (gN : SmoothRiemannianMetric I N)
    {p : M → N} (hp : IsLocalDiffeomorph I I ∞ p)
    (hpull : localPullMetric gN p hp = gM)
    (Φ : PartialDiffeomorph I I M N 1) (hΦ : EqOn p Φ Φ.source) :
    Measure.map p ((riemannianVolumeMeasure (I := I) (M := M) gM).restrict Φ.source) =
      (riemannianVolumeMeasure (I := I) (M := N) gN).restrict Φ.target := by
  let ψ : PartialDiffeomorph I I N M 1 := Φ.symm
  have hright : ∀ y ∈ ψ.source, p (ψ y) = y := by
    intro y hy
    have hyΦ : ψ y ∈ Φ.source := Φ.toPartialEquiv.map_target hy
    rw [hΦ hyΦ]
    exact Φ.toPartialEquiv.right_inv hy
  have hleft : EqOn (fun z : M => ψ.invFun z) p ψ.target := by
    intro z hz
    exact (hΦ hz).symm
  have hpush := riemannianVolumeMeasure_partialIsometry (I := I) (J := I)
    (M := N) (N := M) gN gM ψ
    (fun y hy v w =>
      inner_eq_of_eq_localPullMetric_of_isRightInverse gM gN hp hpull ψ hright hy v w)
  have hae : (fun z : M => ψ.invFun z)
      =ᵐ[(riemannianVolumeMeasure (I := I) (M := M) gM).restrict ψ.target] p := by
    change ∀ᵐ z ∂((riemannianVolumeMeasure (I := I) (M := M) gM).restrict ψ.target),
      ψ.invFun z = p z
    rw [MeasureTheory.ae_iff]
    have hcompl : ((riemannianVolumeMeasure (I := I) (M := M) gM).restrict ψ.target)
        ψ.targetᶜ = 0 := by
      rw [Measure.restrict_apply ψ.open_target.measurableSet.compl]
      simp
    exact measure_mono_null (fun z hz hzt => hz (hleft hzt)) hcompl
  calc Measure.map p ((riemannianVolumeMeasure (I := I) (M := M) gM).restrict ψ.target)
      = Measure.map (fun z : M => ψ.invFun z)
          ((riemannianVolumeMeasure (I := I) (M := M) gM).restrict ψ.target) :=
        (Measure.map_congr hae).symm
    _ = (riemannianVolumeMeasure (I := I) (M := N) gN).restrict ψ.source := hpush.symm

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [IsManifold I ∞ N] [T2Space N] [SigmaCompactSpace N] in
private theorem measurableSet_image_of_partialDiffeomorph
    (Φ : PartialDiffeomorph I I M N 1) {V : Set M} (hV : MeasurableSet V)
    (hVsub : V ⊆ Φ.source) : MeasurableSet (Φ '' V) := by
  have hcont : Continuous fun y : Φ.target => Φ.symm (y : N) :=
    continuousOn_iff_continuous_domRestrict.mp Φ.symm.contMDiffOn_toFun.continuousOn
  have hpre : MeasurableSet {y : Φ.target | Φ.symm (y : N) ∈ V} := hcont.measurable hV
  have himg : Φ '' V = Subtype.val '' {y : Φ.target | Φ.symm (y : N) ∈ V} := by
    ext y
    constructor
    · rintro ⟨x, hxV, rfl⟩
      refine ⟨⟨Φ x, Φ.toPartialEquiv.map_source (hVsub hxV)⟩, ?_, rfl⟩
      simp only [Set.mem_ofPred_eq]
      have hmem : (⇑Φ.symm.toPartialEquiv) (⇑Φ.toPartialEquiv x) = x :=
        Φ.toPartialEquiv.left_inv (hVsub hxV)
      rw [hmem]
      exact hxV
    · rintro ⟨y', hy'V, rfl⟩
      exact ⟨Φ.symm y', hy'V, Φ.toPartialEquiv.right_inv y'.2⟩
  rw [himg]
  exact Φ.open_target.measurableSet.subtype_image hpre

private theorem map_restrict_eq_restrict_image
    [I.Boundaryless]
    (gM : SmoothRiemannianMetric I M) (gN : SmoothRiemannianMetric I N)
    {p : M → N} (hp : IsLocalDiffeomorph I I ∞ p)
    (hpull : localPullMetric gN p hp = gM)
    (Φ : PartialDiffeomorph I I M N 1) (hΦ : EqOn p Φ Φ.source)
    {V : Set M} (hV : MeasurableSet V) (hVsub : V ⊆ Φ.source) :
    Measure.map p ((riemannianVolumeMeasure (I := I) (M := M) gM).restrict V) =
      (riemannianVolumeMeasure (I := I) (M := N) gN).restrict (p '' V) := by
  have hpmeas : Measurable p := hp.contMDiff.continuous.measurable
  have hinj : ∀ a ∈ Φ.source, ∀ b ∈ Φ.source, p a = p b → a = b := by
    intro a ha b hb hab
    rw [hΦ ha, hΦ hb] at hab
    exact Φ.toPartialEquiv.injOn ha hb hab
  have himg : p '' V = Φ '' V := by
    ext y
    constructor
    · rintro ⟨x, hxV, rfl⟩
      exact ⟨x, hxV, (hΦ (hVsub hxV)).symm⟩
    · rintro ⟨x, hxV, rfl⟩
      exact ⟨x, hxV, hΦ (hVsub hxV)⟩
  have hIm : MeasurableSet (p '' V) := by
    rw [himg]
    exact measurableSet_image_of_partialDiffeomorph Φ hV hVsub
  have htarget : p '' V ⊆ Φ.target := by
    rintro y ⟨x, hxV, rfl⟩
    rw [hΦ (hVsub hxV)]
    exact Φ.toPartialEquiv.map_source (hVsub hxV)
  have hsource := map_restrict_source_eq_restrict_target gM gN hp hpull Φ hΦ
  ext A hA
  have hAi : MeasurableSet (A ∩ p '' V) := hA.inter hIm
  rw [Measure.map_apply hpmeas hA, Measure.restrict_apply hA,
    Measure.restrict_apply (hpmeas hA)]
  have hpre : MeasurableSet (p ⁻¹' (A ∩ p '' V)) := hpmeas hAi
  have hkey : (riemannianVolumeMeasure (I := I) (M := M) gM) (p ⁻¹' A ∩ V) =
      (Measure.map p ((riemannianVolumeMeasure (I := I) (M := M) gM).restrict Φ.source))
        (A ∩ p '' V) := by
    rw [Measure.map_apply hpmeas hAi, Measure.restrict_apply hpre]
    congr 1
    ext z
    constructor
    · rintro ⟨hzA, hzV⟩
      exact ⟨⟨hzA, ⟨z, hzV, rfl⟩⟩, hVsub hzV⟩
    · rintro ⟨⟨hzA, hzW⟩, hzsrc⟩
      obtain ⟨w, hwV, hwp⟩ := hzW
      exact ⟨hzA, (hinj w (hVsub hwV) z hzsrc hwp) ▸ hwV⟩
  rw [hkey, hsource]
  rw [Measure.restrict_apply hAi]
  congr 1
  exact Set.inter_eq_left.mpr (Subset.trans Set.inter_subset_right htarget)

omit [TopologicalSpace N] [T2Space N] [SigmaCompactSpace N] in
private theorem indicator_inter_eq_mul_indicator (A S : Set N) (y : N) :
    (A ∩ S).indicator (1 : N → ENNReal) y =
      A.indicator (1 : N → ENNReal) y * S.indicator (1 : N → ENNReal) y := by
  by_cases hyA : y ∈ A <;> by_cases hyS : y ∈ S <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, hyA, hyS]

omit [TopologicalSpace M] [T2Space M] [SigmaCompactSpace M] in
private theorem pairwise_disjoint_sdiff_iUnion_lt {ι : Type*} (W : ι → Set M) (lev : ι → ℕ)
    (hlev : Function.Injective lev) :
    Pairwise (Function.onFun Disjoint fun a => W a \ ⋃ b, ⋃ (_ : lev b < lev a), W b) := by
  intro a c hac
  rcases lt_trichotomy (lev a) (lev c) with hlt | heq | hgt
  · refine Set.disjoint_left.mpr fun x hx hy => ?_
    have hmem : x ∈ ⋃ b, ⋃ (_ : lev b < lev c), W b := by
      apply Set.mem_iUnion.mpr
      exact ⟨a, Set.mem_iUnion.mpr ⟨hlt, hx.1⟩⟩
    exact hy.2 hmem
  · exact absurd (hlev heq) hac
  · refine Set.disjoint_left.mpr fun x hx hy => ?_
    have hmem : x ∈ ⋃ b, ⋃ (_ : lev b < lev a), W b := by
      apply Set.mem_iUnion.mpr
      exact ⟨c, Set.mem_iUnion.mpr ⟨hgt, hy.1⟩⟩
    exact hx.2 hmem

omit [TopologicalSpace M] [T2Space M] [SigmaCompactSpace M] in
private theorem iUnion_sdiff_iUnion_lt_eq {ι : Type*} [Countable ι]
    (W : ι → Set M) (lev : ι → ℕ) (hcover : ⋃ i, W i = univ) :
    ⋃ i, (W i \ ⋃ j, ⋃ (_ : lev j < lev i), W j) = univ := by
  classical
  apply Set.eq_univ_of_forall
  intro x
  have hx : ∃ i, x ∈ W i := by
    have : x ∈ ⋃ i, W i := by rw [hcover]; trivial
    exact Set.mem_iUnion.mp this
  obtain ⟨i₀, hi₀⟩ := hx
  have hm : ∃ m, ∃ i, lev i = m ∧ x ∈ W i := ⟨lev i₀, i₀, rfl, hi₀⟩
  have hspec := Nat.find_spec hm
  have hle' : lev (Classical.choose hspec) = Nat.find hm := (Classical.choose_spec hspec).1
  refine Set.mem_iUnion.mpr ⟨Classical.choose hspec, (Classical.choose_spec hspec).2, ?_⟩
  intro hmem
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hmem
  obtain ⟨hjn, hxj⟩ := Set.mem_iUnion.mp hj
  have hmem' : ∃ i, lev i = lev j ∧ x ∈ W i := ⟨j, rfl, hxj⟩
  exact Nat.find_min hm (by rw [← hle']; exact hjn) hmem'

omit [TopologicalSpace M] [T2Space M] [SigmaCompactSpace M]
  [TopologicalSpace N] [T2Space N] [SigmaCompactSpace N] in
private theorem indicator_image_eq_indicator_setOf {ι : Type*} (p : M → N) {V : ι → Set M}
    (y : N) (i : ι) :
    (p '' V i).indicator (fun _ => (1 : ENNReal)) y =
      ({k : ι | y ∈ p '' V k} : Set ι).indicator (fun _ => (1 : ENNReal)) i := by
  by_cases hn : y ∈ p '' V i
  · rw [Set.indicator_of_mem hn]
    have hmem : i ∈ ({k : ι | y ∈ p '' V k} : Set ι) := hn
    rw [Set.indicator_of_mem hmem]
  · rw [Set.indicator_of_notMem hn]
    have hmem : i ∉ ({k : ι | y ∈ p '' V k} : Set ι) := hn
    rw [Set.indicator_of_notMem hmem]

omit [TopologicalSpace M] [T2Space M] [SigmaCompactSpace M]
  [TopologicalSpace N] [T2Space N] [SigmaCompactSpace N] in
private theorem tsum_indicator_image_eq_natCast {ι : Type*} [Countable ι]
    {p : M → N} {V W : ι → Set M}
    (hVsub : ∀ i, V i ⊆ W i) (hinj : ∀ i, Set.InjOn p (W i))
    (hdisj : Pairwise (Function.onFun Disjoint V)) (hcover : ⋃ i, V i = univ)
    (k : ℕ) (hcard : ∀ y : N, {x : M | p x = y}.encard = (k : ℕ∞)) (y : N) :
    ∑' i, (p '' V i).indicator (1 : N → ENNReal) y = (k : ENNReal) := by
  classical
  let toFib : ({j : ι | y ∈ p '' V j} : Set ι) → {x : M | p x = y} := fun i =>
    ⟨Classical.choose i.2, (Classical.choose_spec i.2).2⟩
  have hinjFib : Function.Injective toFib := by
    intro i j hij
    have hij' : Classical.choose i.2 = Classical.choose j.2 := congrArg Subtype.val hij
    refine Subtype.ext ?_
    by_contra hne
    exact Set.disjoint_left.mp (hdisj hne) (Classical.choose_spec i.2).1
      (hij' ▸ (Classical.choose_spec j.2).1)
  have hsurjFib : Function.Surjective toFib := by
    intro x
    have hxcover : x.1 ∈ ⋃ i, V i := by rw [hcover]; trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxcover
    have hmem : y ∈ p '' V i := x.2 ▸ Set.mem_image_of_mem p hi
    refine ⟨⟨i, hmem⟩, ?_⟩
    refine Subtype.ext ?_
    have hch := Classical.choose_spec hmem
    exact hinj i (hVsub i hch.1) (hVsub i hi) (by rw [hch.2, x.2])
  have hbij : ({j : ι | y ∈ p '' V j} : Set ι) ≃ {x : M | p x = y} :=
    Equiv.ofBijective toFib ⟨hinjFib, hsurjFib⟩
  have hJcard : ({j : ι | y ∈ p '' V j} : Set ι).encard = (k : ℕ∞) := by
    rw [Set.encard_congr hbij, hcard y]
  calc ∑' i, (p '' V i).indicator (1 : N → ENNReal) y
      = ∑' i, ({j : ι | y ∈ p '' V j} : Set ι).indicator (fun _ => (1 : ENNReal)) i :=
        tsum_congr fun i => indicator_image_eq_indicator_setOf p y i
    _ = ∑' i : {j : ι | y ∈ p '' V j}, (1 : ENNReal) :=
        (tsum_subtype _ fun _ => (1 : ENNReal)).symm
    _ = _ := ENNReal.tsum_set_one _
    _ = (k : ENNReal) := by rw [hJcard, ENat.toENNReal_coe]

omit [T2Space N] [SigmaCompactSpace N] in
private theorem tsum_measure_inter_eq_natCast_mul {ι : Type*} [Countable ι]
    (μ : Measure N) {S : ι → Set N} {A : Set N} (k : ℕ)
    (hA : MeasurableSet A) (hS : ∀ i, MeasurableSet (S i))
    (hcount : ∀ y, ∑' i, (S i).indicator (1 : N → ENNReal) y = (k : ENNReal)) :
    ∑' i, μ (A ∩ S i) = (k : ENNReal) * μ A := by
  calc ∑' i, μ (A ∩ S i)
      = ∑' i, ∫⁻ y, (A ∩ S i).indicator (1 : N → ENNReal) y ∂μ := by
        refine tsum_congr fun i => ?_
        rw [lintegral_indicator_one (hA.inter (hS i))]
    _ = ∫⁻ y, ∑' i, (A ∩ S i).indicator (1 : N → ENNReal) y ∂μ :=
        (lintegral_tsum fun i => (measurable_const.indicator (hA.inter (hS i))).aemeasurable).symm
    _ = ∫⁻ y, A.indicator (1 : N → ENNReal) y * (k : ENNReal) ∂μ := by
        refine lintegral_congr fun y => ?_
        rw [← hcount y, ← ENNReal.tsum_mul_left]
        exact tsum_congr fun i => indicator_inter_eq_mul_indicator A (S i) y
    _ = ∫⁻ y, A.indicator (fun _ => (k : ENNReal)) y ∂μ := by
        refine lintegral_congr fun y => ?_
        by_cases hy : y ∈ A <;>
          simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy]
    _ = (k : ENNReal) * μ A := by
        rw [lintegral_indicator hA, setLIntegral_const]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [IsManifold I ∞ N] [T2Space N] [SigmaCompactSpace N] in
private theorem measurableSet_image_of_eqOn_partialDiffeomorph
    {p : M → N} {Φ : PartialDiffeomorph I I M N 1} (hΦ : EqOn p Φ Φ.source)
    {V : Set M} (hV : MeasurableSet V) (hVsub : V ⊆ Φ.source) : MeasurableSet (p '' V) := by
  have himg : p '' V = Φ '' V := by
    ext y
    constructor
    · rintro ⟨x, hxV, rfl⟩
      exact ⟨x, hxV, (hΦ (hVsub hxV)).symm⟩
    · rintro ⟨x, hxV, rfl⟩
      exact ⟨x, hxV, hΦ (hVsub hxV)⟩
  rw [himg]
  exact measurableSet_image_of_partialDiffeomorph Φ hV hVsub

theorem riemannianVolumeMeasure_map_eq_natCast_smul_of_localPullMetric
    [I.Boundaryless]
    (gM : SmoothRiemannianMetric I M) (gN : SmoothRiemannianMetric I N)
    {p : M → N} (hp : IsLocalDiffeomorph I I ∞ p)
    (hpull : localPullMetric gN p hp = gM) (k : ℕ)
    (hcard : ∀ y : N, {x : M | p x = y}.encard = (k : ℕ∞)) :
    Measure.map p (riemannianVolumeMeasure (I := I) (M := M) gM) =
      (k : ENNReal) • riemannianVolumeMeasure (I := I) (M := N) gN := by
  classical
  have hpmeas : Measurable p := hp.contMDiff.continuous.measurable
  obtain ⟨s, hsc, hscover⟩ := countable_cover_nhds_of_sigmaCompact
    (fun x : M => (Classical.choose (hp x)).open_source.mem_nhds (hp x).choose_spec.1)
  rcases s.eq_empty_or_nonempty with hs | hs
  · have hMempty : IsEmpty M := by
      rw [hs] at hscover
      simp only [Set.biUnion_empty] at hscover
      exact Set.univ_eq_empty_iff.mp hscover.symm
    have hzero : riemannianVolumeMeasure (I := I) (M := M) gM = 0 := by
      refine Measure.ext fun A _ => ?_
      have hAempty : A = ∅ :=
        Set.eq_empty_iff_forall_notMem.mpr fun x _ => hMempty.false x
      rw [hAempty]
      simp
    rw [hzero, Measure.map_zero]
    rcases isEmpty_or_nonempty N with hN | hN
    · have hnzero : riemannianVolumeMeasure (I := I) (M := N) gN = 0 := by
        refine Measure.ext fun A _ => ?_
        have hAempty : A = ∅ :=
          Set.eq_empty_iff_forall_notMem.mpr fun x _ => hN.false x
        rw [hAempty]
        simp
      rw [hnzero, smul_zero]
    · obtain ⟨y₀⟩ := hN
      have hk : k = 0 := by
        have hfib : {x : M | p x = y₀} = ∅ :=
          Set.eq_empty_iff_forall_notMem.mpr fun x _ => hMempty.false x
        have h := hcard y₀
        rw [hfib, Set.encard_empty] at h
        exact_mod_cast h.symm
      rw [hk]
      simp
  · let _ : Countable s := hsc.to_subtype
    obtain ⟨lev, hlev⟩ := Countable.exists_injective_nat s
    let W : s → Set M := fun i => (Classical.choose (hp (i : M))).source
    let V : s → Set M := fun i => W i \ ⋃ j, ⋃ (_ : lev j < lev i), W j
    have hcover : ⋃ i : s, W i = univ := by
      apply Set.eq_univ_of_forall
      intro x
      have hx : x ∈ ⋃ y ∈ s, (Classical.choose (hp y)).source := by
        rw [hscover]
        trivial
      obtain ⟨y, hy⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hyS, hxy⟩ := Set.mem_iUnion.mp hy
      exact Set.mem_iUnion.mpr ⟨⟨y, hyS⟩, hxy⟩
    have hVsub : ∀ i, V i ⊆ W i := fun i => Set.sdiff_subset
    have hWmeas : ∀ i : s, MeasurableSet (W i) := fun i =>
      (Classical.choose (hp (i : M))).open_source.measurableSet
    have hVmeas : ∀ i, MeasurableSet (V i) := by
      intro i
      have hUi : MeasurableSet (⋃ j, ⋃ (_ : lev j < lev i), W j) :=
        MeasurableSet.biUnion (Set.to_countable {j : s | lev j < lev i})
          (fun j _ => hWmeas j)
      exact (hWmeas i).diff hUi
    have hinjOn : ∀ i, Set.InjOn p (W i) := by
      intro i a ha b hb hab
      have hle := (hp (i : M)).choose_spec.2
      rw [hle ha, hle hb] at hab
      exact (Classical.choose (hp (i : M))).toPartialEquiv.injOn ha hb hab
    have hVdisj : Pairwise (Function.onFun Disjoint V) := by
      exact pairwise_disjoint_sdiff_iUnion_lt W lev hlev
    have hVcover : ⋃ i : s, V i = univ :=
      iUnion_sdiff_iUnion_lt_eq W lev hcover
    have hVsource : ∀ i, V i ⊆ (Classical.choose (hp (i : M))).source := fun i =>
      fun x hx => hVsub i hx
    have hlocal : ∀ i,
        Measure.map p ((riemannianVolumeMeasure (I := I) (M := M) gM).restrict (V i)) =
          (riemannianVolumeMeasure (I := I) (M := N) gN).restrict (p '' V i) := fun i =>
      map_restrict_eq_restrict_image gM gN hp hpull
        (partialDiffeomorphOfLe (Classical.choose (hp (i : M))))
        (hp (i : M)).choose_spec.2 (hVmeas i) (hVsource i)
    have hImmeas : ∀ i, MeasurableSet (p '' V i) := fun i =>
      measurableSet_image_of_eqOn_partialDiffeomorph
        (Φ := partialDiffeomorphOfLe (Classical.choose (hp (i : M))))
        (hp (i : M)).choose_spec.2 (hVmeas i) (hVsource i)
    have hcount : ∀ y : N,
        ∑' i, (p '' V i).indicator (1 : N → ENNReal) y = (k : ENNReal) :=
      tsum_indicator_image_eq_natCast hVsub hinjOn hVdisj hVcover k hcard
    refine Measure.ext fun A hA => ?_
    rw [Measure.map_apply hpmeas hA, Measure.smul_apply]
    have hdisj' : Pairwise (Function.onFun Disjoint fun i : s => p ⁻¹' A ∩ V i) :=
      fun i j hij => (hVdisj hij).mono Set.inter_subset_right Set.inter_subset_right
    have hdecomp : (riemannianVolumeMeasure (I := I) (M := M) gM) (p ⁻¹' A) =
        ∑' i : s, (riemannianVolumeMeasure (I := I) (M := M) gM) (p ⁻¹' A ∩ V i) := by
      rw [← measure_iUnion hdisj' fun i => (hpmeas hA).inter (hVmeas i)]
      congr 1
      ext x
      constructor
      · intro hx
        have hxcover : x ∈ ⋃ i : s, V i := by rw [hVcover]; trivial
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxcover
        refine Set.mem_iUnion.mpr ⟨i, ?_⟩
        exact ⟨hx, hi⟩
      · intro hx
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        exact hi.1
    rw [hdecomp]
    calc ∑' i : s, (riemannianVolumeMeasure (I := I) (M := M) gM) (p ⁻¹' A ∩ V i)
        = ∑' i : s, ((riemannianVolumeMeasure (I := I) (M := N) gN).restrict (p '' V i)) A := by
          refine tsum_congr fun i => ?_
          rw [← hlocal i, Measure.map_apply hpmeas hA, Measure.restrict_apply (hpmeas hA)]
      _ = ∑' i : s, (riemannianVolumeMeasure (I := I) (M := N) gN) (A ∩ p '' V i) := by
          refine tsum_congr fun i => ?_
          rw [Measure.restrict_apply hA]
      _ = (k : ENNReal) * (riemannianVolumeMeasure (I := I) (M := N) gN) A :=
          tsum_measure_inter_eq_natCast_mul _ k hA hImmeas hcount
      _ = (k : ENNReal) • (riemannianVolumeMeasure (I := I) (M := N) gN) A :=
          (smul_eq_mul _ _).symm

end DifferentialGeometry.Integral.Measure
