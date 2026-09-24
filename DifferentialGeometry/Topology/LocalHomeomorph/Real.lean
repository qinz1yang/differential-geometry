import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Instances.Real.Lemmas

section

set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric
open scoped Topology

namespace IsLocalHomeomorph

variable {X : Type*} [TopologicalSpace X] {f : X → ℝ}

private theorem isOpen_image_of_continuousOn_section
    (hf : IsLocalHomeomorph f) {I : Set ℝ} (hI : IsOpen I) {g : ℝ → X}
    (hg : ContinuousOn g I) (hfg : ∀ t ∈ I, f (g t) = t) : IsOpen (g '' I) := by
  let G : I → X := fun t => g t
  have hG : Continuous G := hg.domRestrict
  have hcomp : f ∘ G = (Subtype.val : I → ℝ) := funext fun t => hfg t t.property
  have hemb : IsOpenEmbedding (f ∘ G) := by
    rw [hcomp]
    exact hI.isOpenEmbedding_subtypeVal
  have hopen := (hf.isOpenEmbedding_of_comp hemb hG).isOpen_range
  have heq : range G = g '' I := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, t.property, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩
  rwa [heq] at hopen

private theorem eqOn_interval_sections [T2Space X]
    (hf : IsLocalHomeomorph f) {I J : Set ℝ}
    (hI : IsPreconnected I) (hJ : IsPreconnected J) {g h : ℝ → X}
    (hg : ContinuousOn g I) (hh : ContinuousOn h J)
    (hfg : ∀ t ∈ I, f (g t) = t) (hfh : ∀ t ∈ J, f (h t) = t)
    {a : ℝ} (haI : a ∈ I) (haJ : a ∈ J) (ha : g a = h a) : EqOn g h (I ∩ J) := by
  have hc : IsPreconnected (I ∩ J) := (hI.ordConnected.inter hJ.ordConnected).isPreconnected
  exact (T2Space.isSeparatedMap f).eqOn_of_comp_eqOn hf.isLocallyInjective hc
    (hg.mono inter_subset_left) (hh.mono inter_subset_right)
    (fun t ht => (hfg t ht.1).trans (hfh t ht.2).symm) ⟨haI, haJ⟩ ha

private theorem exists_section_union [T2Space X]
    (hf : IsLocalHomeomorph f) {I J : Set ℝ} (hIo : IsOpen I) (hJo : IsOpen J)
    (hIc : IsPreconnected I) (hJc : IsPreconnected J) {g h : ℝ → X}
    (hg : ContinuousOn g I) (hh : ContinuousOn h J)
    (hfg : ∀ t ∈ I, f (g t) = t) (hfh : ∀ t ∈ J, f (h t) = t)
    {a : ℝ} (haI : a ∈ I) (haJ : a ∈ J) (ha : g a = h a) :
    ∃ k : ℝ → X, ContinuousOn k (I ∪ J) ∧
      (∀ t ∈ I ∪ J, f (k t) = t) ∧ EqOn k g I ∧ EqOn k h J := by
  classical
  have heq := hf.eqOn_interval_sections hIc hJc hg hh hfg hfh haI haJ ha
  let k := I.piecewise g h
  have hkI : EqOn k g I := fun t ht => piecewise_eq_of_mem I g h ht
  have hkJ : EqOn k h J := by
    intro t ht
    by_cases htI : t ∈ I
    · exact (hkI htI).trans (heq ⟨htI, ht⟩)
    · exact piecewise_eq_of_notMem I g h htI
  have hkc : ContinuousOn k (I ∪ J) := by
    apply (continuousOn_union_iff_of_isOpen hIo hJo).mpr
    exact ⟨hg.congr hkI, hh.congr hkJ⟩
  refine ⟨k, hkc, ?_, hkI, hkJ⟩
  intro t ht
  rcases ht with ht | ht
  · rw [hkI ht]
    exact hfg t ht
  · rw [hkJ ht]
    exact hfh t ht

private theorem exists_open_interval_section (hf : IsLocalHomeomorph f) (x : X) :
    ∃ (I : Set ℝ) (g : ℝ → X), IsOpen I ∧ IsPreconnected I ∧ f x ∈ I ∧
      ContinuousOn g I ∧ (∀ t ∈ I, f (g t) = t) ∧ g (f x) = x := by
  let e := hf.localInverseAt x
  have hfx : f x ∈ e.source := hf.apply_self_mem_localInverseAt_source
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (e.open_source.mem_nhds hfx)
  refine ⟨ball (f x) r, e, isOpen_ball,
    (by rw [Real.ball_eq_Ioo]; exact isPreconnected_Ioo), mem_ball_self hr,
    e.continuousOn.mono hsub, ?_, hf.localInverseAt_apply_self⟩
  exact fun t ht => hf.apply_localInverseAt_of_mem (hsub ht)

private def sectionReachable (f : X → ℝ) (x y : X) : Prop :=
  ∃ (I : Set ℝ) (g : ℝ → X), IsOpen I ∧ IsPreconnected I ∧ f x ∈ I ∧ f y ∈ I ∧
    ContinuousOn g I ∧ (∀ t ∈ I, f (g t) = t) ∧ g (f x) = x ∧ g (f y) = y

private theorem sectionReachable_self (hf : IsLocalHomeomorph f) (x : X) :
    sectionReachable f x x := by
  obtain ⟨I, g, hIo, hIc, hxI, hg, hfg, hgx⟩ := hf.exists_open_interval_section x
  exact ⟨I, g, hIo, hIc, hxI, hxI, hg, hfg, hgx, hgx⟩

private theorem isOpen_sectionReachable (hf : IsLocalHomeomorph f) (x : X) :
    IsOpen {y | sectionReachable f x y} := by
  apply isOpen_iff_mem_nhds.mpr
  intro y hy
  obtain ⟨I, g, hIo, hIc, hxI, hyI, hg, hfg, hgx, hgy⟩ := hy
  have hopen := hf.isOpen_image_of_continuousOn_section hIo hg hfg
  have hyim : y ∈ g '' I := ⟨f y, hyI, hgy⟩
  apply mem_of_superset (hopen.mem_nhds hyim)
  rintro z ⟨t, ht, rfl⟩
  have hft := hfg t ht
  exact ⟨I, g, hIo, hIc, hxI, hft.symm ▸ ht, hg, hfg, hgx, congrArg g hft⟩

variable [T2Space X]

private theorem isClosed_sectionReachable (hf : IsLocalHomeomorph f) (x : X) :
    IsClosed {y | sectionReachable f x y} := by
  apply isClosed_of_closure_subset
  intro z hz
  obtain ⟨J, h, hJo, hJc, hzJ, hh, hfh, hhz⟩ := hf.exists_open_interval_section z
  have hW : IsOpen (h '' J) := hf.isOpen_image_of_continuousOn_section hJo hh hfh
  have hzW : z ∈ h '' J := ⟨f z, hzJ, hhz⟩
  obtain ⟨y, hyW, hyR⟩ := mem_closure_iff.mp hz (h '' J) hW hzW
  obtain ⟨I, g, hIo, hIc, hxI, hyI, hg, hfg, hgx, hgy⟩ := hyR
  obtain ⟨t, htJ, hty⟩ := hyW
  have hfy : f y = t := hty ▸ hfh t htJ
  have hyJ : f y ∈ J := hfy.symm ▸ htJ
  have hhy : h (f y) = y := (congrArg h hfy).trans hty
  obtain ⟨k, hkc, hfk, hkI, hkJ⟩ := hf.exists_section_union hIo hJo hIc hJc hg hh hfg hfh
    hyI hyJ (hgy.trans hhy.symm)
  refine ⟨I ∪ J, k, hIo.union hJo, hIc.union (f y) hyI hyJ hJc,
    Or.inl hxI, Or.inr hzJ, hkc, hfk, ?_, ?_⟩
  · exact (hkI hxI).trans hgx
  · exact (hkJ hzJ).trans hhz

private theorem sectionReachable_of_preconnected [PreconnectedSpace X]
    (hf : IsLocalHomeomorph f) (x y : X) : sectionReachable f x y := by
  have hclopen : IsClopen {y | sectionReachable f x y} :=
    ⟨isClosed_sectionReachable hf x, isOpen_sectionReachable hf x⟩
  have heq := hclopen.eq_univ ⟨x, sectionReachable_self hf x⟩
  change y ∈ {y | sectionReachable f x y}
  rw [heq]
  exact mem_univ y

theorem injective_of_preconnected_real [PreconnectedSpace X]
    (hf : IsLocalHomeomorph f) : Function.Injective f := by
  intro x y hxy
  obtain ⟨_, g, _, _, _, _, _, _, hgx, hgy⟩ := sectionReachable_of_preconnected hf x y
  exact hgx.symm.trans ((congrArg g hxy).trans hgy)

theorem isOpenEmbedding_of_preconnected_real [PreconnectedSpace X]
    (hf : IsLocalHomeomorph f) : IsOpenEmbedding f :=
  hf.isOpenEmbedding_of_injective hf.injective_of_preconnected_real

end IsLocalHomeomorph

end

end
