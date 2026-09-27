/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossSeamTubePages
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.InteriorTwoSided

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem crossOpenSheetOf_subset_sdiff (i : Fin 4) :
    crossOpenSheetOf i ⊆ crossingFigure \ spliceCore := fun _ hw =>
  ⟨crossSheetOf_subset_crossingFigure i (crossOpenSheetOf_subset_crossSheetOf i hw),
    disjoint_left.mp (disjoint_crossOpenSheetOf_spliceCore i) hw⟩

theorem pos_of_isPreconnected_of_ne_zero {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsPreconnected s) {g : X → ℝ} (hg : ContinuousOn g s) (hne : ∀ x ∈ s, g x ≠ 0)
    {x₀ : X} (hx₀ : x₀ ∈ s) (hpos : 0 < g x₀) : ∀ x ∈ s, 0 < g x := by
  intro x hx
  by_contra hle
  obtain ⟨y, hy, hy0⟩ := hs.intermediate_value hx hx₀ hg ⟨not_lt.mp hle, hpos.le⟩
  exact hne y hy hy0

theorem neg_of_isPreconnected_of_ne_zero {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsPreconnected s) {g : X → ℝ} (hg : ContinuousOn g s) (hne : ∀ x ∈ s, g x ≠ 0)
    {x₀ : X} (hx₀ : x₀ ∈ s) (hneg : g x₀ < 0) : ∀ x ∈ s, g x < 0 := by
  intro x hx
  by_contra hle
  obtain ⟨y, hy, hy0⟩ := hs.intermediate_value hx₀ hx hg ⟨hneg.le, not_lt.mp hle⟩
  exact hne y hy hy0

theorem norm_crossDirOf (i : Fin 4) : ‖crossDirOf i‖ = 1 := by
  fin_cases i <;> simp [crossDirOf, Prod.norm_def]

theorem crossWedge_ne_zero (i : Fin 4) {s ε : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (hε : 0 < ε) :
    (((1 - s) * ε) • crossDirOf i + (s * ε) • crossDirOf (i + 1)).1 ≠ 0 ∧
      (((1 - s) * ε) • crossDirOf i + (s * ε) • crossDirOf (i + 1)).2 ≠ 0 := by
  have h1 : 0 < (1 - s) * ε := mul_pos (by linarith [hs.2]) hε
  have h2 : 0 < s * ε := mul_pos hs.1 hε
  fin_cases i <;>
    simp only [crossDirOf, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      Fin.reduceAdd, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Prod.smul_mk,
      smul_eq_mul, mul_one, mul_zero, mul_neg, Prod.fst_add, Prod.snd_add, add_zero, zero_add,
      ne_eq, neg_eq_zero] <;>
    constructor <;> linarith

theorem not_crossWedge_of_succ {β : (ℝ × ℝ) × ℝ → ℝ} {t₀ r : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1)
    (hr : 0 < r) (i : Fin 4)
    (hcont : ContinuousOn β (spliceCylinder ∩ Metric.ball (((0 : ℝ), (0 : ℝ)), t₀) r))
    (hpos : ∀ w ∈ crossOpenSheetOf i ∩ Metric.ball (((0 : ℝ), (0 : ℝ)), t₀) r, 0 < β w)
    (hneg : ∀ w ∈ crossOpenSheetOf (i + 1) ∩ Metric.ball (((0 : ℝ), (0 : ℝ)), t₀) r, β w < 0)
    (hoff : ∀ w ∈ spliceCylinder ∩ Metric.ball (((0 : ℝ), (0 : ℝ)), t₀) r,
      w ∉ crossingFigure → β w ≠ 0) : False := by
  obtain ⟨ε, hε0, hε1, hεr⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ε < r :=
    ⟨min (r / 2) 1, lt_min (half_pos hr) one_pos, min_le_right _ _,
      (min_le_left _ _).trans_lt (half_lt_self hr)⟩
  have hγc : Continuous fun s : ℝ =>
      ((((1 - s) * ε) • crossDirOf i + (s * ε) • crossDirOf (i + 1), t₀) : (ℝ × ℝ) × ℝ) := by
    fun_prop
  have hnorm : ∀ s ∈ Icc (0 : ℝ) 1,
      ‖((1 - s) * ε) • crossDirOf i + (s * ε) • crossDirOf (i + 1)‖ ≤ ε := by
    intro s hs
    have h1 : 0 ≤ (1 - s) * ε := mul_nonneg (by linarith [hs.2]) hε0.le
    have h2 : 0 ≤ s * ε := mul_nonneg hs.1 hε0.le
    calc ‖((1 - s) * ε) • crossDirOf i + (s * ε) • crossDirOf (i + 1)‖
        ≤ ‖((1 - s) * ε) • crossDirOf i‖ + ‖(s * ε) • crossDirOf (i + 1)‖ := norm_add_le _ _
      _ = (1 - s) * ε + s * ε := by
        rw [norm_smul, norm_smul, norm_crossDirOf, norm_crossDirOf, Real.norm_of_nonneg h1,
          Real.norm_of_nonneg h2, mul_one, mul_one]
      _ = ε := by ring
  have hγmem : ∀ s ∈ Icc (0 : ℝ) 1,
      ((((1 - s) * ε) • crossDirOf i + (s * ε) • crossDirOf (i + 1), t₀) : (ℝ × ℝ) × ℝ) ∈
        spliceCylinder ∩ Metric.ball (((0 : ℝ), (0 : ℝ)), t₀) r := by
    intro s hs
    have hn := hnorm s hs
    rw [Prod.norm_def] at hn
    have hn1 := (le_max_left _ _).trans hn
    have hn2 := (le_max_right _ _).trans hn
    rw [Real.norm_eq_abs, abs_le] at hn1 hn2
    refine ⟨⟨mem_spliceSquare.mpr ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩, ht₀⟩,
      ?_⟩
    rw [Metric.mem_ball, Prod.dist_eq, dist_self, dist_eq_norm]
    simp only [Prod.mk_zero_zero, sub_zero]
    exact max_lt (hn.trans_lt hεr) hr
  have hγ0 : ((((1 - 0) * ε) • crossDirOf i + (0 * ε) • crossDirOf (i + 1), t₀) :
      (ℝ × ℝ) × ℝ) ∈ crossOpenSheetOf i ∩ Metric.ball (((0 : ℝ), (0 : ℝ)), t₀) r := by
    refine ⟨?_, (hγmem 0 ⟨le_rfl, zero_le_one⟩).2⟩
    simp only [sub_zero, one_mul, zero_mul, zero_smul, add_zero]
    exact smul_crossDirOf_mem_crossOpenSheetOf i hε0 hε1 ht₀
  have hγ1 : ((((1 - 1) * ε) • crossDirOf i + (1 * ε) • crossDirOf (i + 1), t₀) :
      (ℝ × ℝ) × ℝ) ∈ crossOpenSheetOf (i + 1) ∩ Metric.ball (((0 : ℝ), (0 : ℝ)), t₀) r := by
    refine ⟨?_, (hγmem 1 ⟨zero_le_one, le_rfl⟩).2⟩
    simp only [sub_self, zero_mul, zero_smul, one_mul, zero_add]
    exact smul_crossDirOf_mem_crossOpenSheetOf (i + 1) hε0 hε1 ht₀
  obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' zero_le_one
    (hcont.comp hγc.continuousOn fun s hs => hγmem s hs) ⟨(hneg _ hγ1).le, (hpos _ hγ0).le⟩
  rcases eq_or_lt_of_le hs.1 with rfl | hs1
  · exact (hpos _ hγ0).ne' hs0
  rcases eq_or_lt_of_le hs.2 with rfl | hs2
  · exact (hneg _ hγ1).ne hs0
  refine hoff _ (hγmem s hs) ?_ hs0
  rintro ⟨hw, -⟩
  obtain ⟨hx, hy⟩ := crossWedge_ne_zero i ⟨hs1, hs2⟩ hε0
  rcases hw with hw | hw
  · exact hx hw.2
  · exact hy hw.2

section Sides

variable {X : Type*} [TopologicalSpace X] [T2Space X] {chart : (ℝ × ℝ) × ℝ → X}
  {f : EuclideanSpace ℝ (Fin 2) → X} {Dom J₁ J₂ : Set (EuclideanSpace ℝ (Fin 2))}

theorem exists_forall_mem_of_crossSeamPage_ownership (hchart : ContinuousOn chart spliceCylinder)
    (hinjc : InjOn chart spliceCylinder) (hDom : IsCompact Dom) (hf : ContinuousOn f Dom)
    (hJ : Dom ∩ f ⁻¹' (chart '' spliceCore) = J₁ ∪ J₂) (hJ₁ : IsClosed J₁) (hJ₂ : IsClosed J₂)
    (hJJ : Disjoint J₁ J₂) (hinj₁ : InjOn f J₁) (hinj₂ : InjOn f J₂)
    (hsurj₁ : chart '' spliceCore ⊆ f '' J₁) (hsurj₂ : chart '' spliceCore ⊆ f '' J₂)
    (huniq : ∀ x ∈ Dom, ∀ y ∈ Dom, f x = f y →
      f x ∈ chart '' (crossingFigure \ spliceCore) → x = y)
    (hsurj : chart '' crossingFigure ⊆ f '' Dom) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1)
    {a₁ b₁ : EuclideanSpace ℝ (Fin 2)} (ha₁ : a₁ ∈ Dom) (hb₁ : b₁ ∈ Dom)
    (hfa : f a₁ = chart (((0 : ℝ), (0 : ℝ)), t₀)) (hfb : f b₁ = chart (((0 : ℝ), (0 : ℝ)), t₀))
    (hab : a₁ ≠ b₁) {O₁ O₂ : Set (EuclideanSpace ℝ (Fin 2))} (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂)
    (hO : Disjoint O₁ O₂) (ha₁O : a₁ ∈ O₁) (hb₁O : b₁ ∈ O₂) (i : Fin 4) :
    ∃ δ > 0, (a₁ ∈ crossSeamPage chart f Dom i → ∀ x ∈ Dom,
        f x ∈ chart '' (crossOpenSheetOf i ∩ Metric.ball (((0 : ℝ), (0 : ℝ)), t₀) δ) →
          x ∈ O₁) ∧
      (a₁ ∉ crossSeamPage chart f Dom i → ∀ x ∈ Dom,
        f x ∈ chart '' (crossOpenSheetOf i ∩ Metric.ball (((0 : ℝ), (0 : ℝ)), t₀) δ) →
          x ∈ O₂) := by
  have hhu : ∀ x ∈ Dom, ∀ y ∈ Dom, f x = f y → f x ∈ chart '' crossOpenSheetOf i → x = y :=
    fun x hx y hy hxy hm => huniq x hx y hy hxy (image_mono (crossOpenSheetOf_subset_sdiff i) hm)
  have hsu : chart '' crossOpenSheetOf i ⊆ f '' Dom :=
    (image_mono ((crossOpenSheetOf_subset_sdiff i).trans sdiff_subset)).trans hsurj
  have hJ' : Dom ∩ f ⁻¹' (chart '' spliceCore) = J₂ ∪ J₁ := by rw [hJ, union_comm]
  have hcore : (((0 : ℝ), (0 : ℝ)), t₀) ∈ spliceCore := ⟨mem_singleton _, ht₀⟩
  have hm₁ := Function.invFunOn_mem (hsurj₁ ⟨_, hcore, rfl⟩)
  have hm₂ := Function.invFunOn_mem (hsurj₂ ⟨_, hcore, rfl⟩)
  have hclass := crossSeamPage_class hchart hinjc hDom hf hJ hJ₁ hJ₂ hJJ hinj₁ hinj₂ hsurj₁
    hsurj₂ hhu hsu
  rcases eq_invFunOn_or_eq_invFunOn_of_crossSeam hJ hinj₁ hinj₂ hsurj₁ hsurj₂ ht₀ ha₁ hfa with
    ha | ha <;>
  rcases eq_invFunOn_or_eq_invFunOn_of_crossSeam hJ hinj₁ hinj₂ hsurj₁ hsurj₂ ht₀ hb₁ hfb with
    hb | hb
  · exact absurd (ha.trans hb.symm) hab
  · rw [ha] at ha₁O ⊢
    rw [hb] at hb₁O
    rcases hclass with ⟨hZ₁, -⟩ | ⟨hZ₁, hZ₂⟩
    · obtain ⟨δ, hδ, hown⟩ := forall_mem_of_subset_crossSeamPage hchart hinjc hDom hf hJ hinj₁
        hinj₂ hsurj₁ hsurj₂ hhu hsu hZ₁ ht₀ hO₁ hO₂ hO ha₁O hb₁O
      exact ⟨δ, hδ, fun _ => hown, fun hn => absurd (hZ₁ hm₁) hn⟩
    · obtain ⟨δ, hδ, hown⟩ := forall_mem_of_subset_crossSeamPage hchart hinjc hDom hf hJ' hinj₂
        hinj₁ hsurj₂ hsurj₁ hhu hsu hZ₁ ht₀ hO₂ hO₁ hO.symm hb₁O ha₁O
      exact ⟨δ, hδ, fun hm => absurd hm (disjoint_left.mp hZ₂ hm₁), fun _ => hown⟩
  · rw [ha] at ha₁O ⊢
    rw [hb] at hb₁O
    rcases hclass with ⟨hZ₁, hZ₂⟩ | ⟨hZ₁, -⟩
    · obtain ⟨δ, hδ, hown⟩ := forall_mem_of_subset_crossSeamPage hchart hinjc hDom hf hJ hinj₁
        hinj₂ hsurj₁ hsurj₂ hhu hsu hZ₁ ht₀ hO₂ hO₁ hO.symm hb₁O ha₁O
      exact ⟨δ, hδ, fun hm => absurd hm (disjoint_left.mp hZ₂ hm₂), fun _ => hown⟩
    · obtain ⟨δ, hδ, hown⟩ := forall_mem_of_subset_crossSeamPage hchart hinjc hDom hf hJ' hinj₂
        hinj₁ hsurj₂ hsurj₁ hhu hsu hZ₁ ht₀ hO₁ hO₂ hO ha₁O hb₁O
      exact ⟨δ, hδ, fun _ => hown, fun hn => absurd (hZ₁ hm₂) hn⟩
  · exact absurd (ha.trans hb.symm) hab

theorem exists_two_sides_of_crossSeamSheet (hchart : ContinuousOn chart spliceCylinder)
    (hinjc : InjOn chart spliceCylinder) (hf : ContinuousOn f Dom)
    (hJ : Dom ∩ f ⁻¹' (chart '' spliceCore) = J₁ ∪ J₂) (hJJ : Disjoint J₁ J₂)
    (hsurj₁ : chart '' spliceCore ⊆ f '' J₁) (hsurj₂ : chart '' spliceCore ⊆ f '' J₂)
    (huniq : ∀ x ∈ Dom, ∀ y ∈ Dom, f x = f y →
      f x ∈ chart '' (crossingFigure \ spliceCore) → x = y)
    (himage : ∀ x ∈ Dom, f x ∈ chart '' spliceCylinder → f x ∈ chart '' crossingFigure)
    (hsurj : chart '' crossingFigure ⊆ f '' Dom)
    (hopen : IsOpen (chart '' ((Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) ×ˢ Ioo (0 : ℝ) 1)))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) {e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin 3))}
    (hze : chart (((0 : ℝ), (0 : ℝ)), t₀) ∈ e.source)
    {a₁ b₁ : EuclideanSpace ℝ (Fin 2)} {S₁ S₂ : Set (EuclideanSpace ℝ (Fin 2))}
    (ha₁ : a₁ ∈ S₁) (hb₁ : b₁ ∈ S₂) (hS₁ : S₁ ⊆ Dom ∩ f ⁻¹' e.source)
    (hS₂ : S₂ ⊆ Dom ∩ f ⁻¹' e.source) (hS : Disjoint S₁ S₂)
    (hS₁n : S₁ ∈ 𝓝[Dom ∩ f ⁻¹' e.source] a₁) (hS₂n : S₂ ∈ 𝓝[Dom ∩ f ⁻¹' e.source] b₁)
    (hinjS₁ : InjOn (e ∘ f) S₁)
    (hfiber : ∀ᶠ y in 𝓝 (e (chart (((0 : ℝ), (0 : ℝ)), t₀))),
      (Dom ∩ f ⁻¹' e.source) ∩ (e ∘ f) ⁻¹' {y} ⊆ S₁ ∪ S₂)
    {U V : Set (EuclideanSpace ℝ (Fin 3))}
    {h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {L : EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] ℝ × ℝ × ℝ} (hU : IsOpen U) (hV : IsOpen V)
    (hzU : e (chart (((0 : ℝ), (0 : ℝ)), t₀)) ∈ U) (hh : IsPLHomeomorphOn h U V)
    (hh0 : h (e (chart (((0 : ℝ), (0 : ℝ)), t₀))) = 0)
    (hnear : ∀ᶠ y in 𝓝 (e (chart (((0 : ℝ), (0 : ℝ)), t₀))),
      (y ∈ (e ∘ f) '' S₁ ↔ (L (h y)).2.2 = 0) ∧ (y ∈ (e ∘ f) '' S₂ ↔ (L (h y)).2.1 = 0))
    (hown : ∀ O₁ O₂ : Set (EuclideanSpace ℝ (Fin 2)), IsOpen O₁ → IsOpen O₂ → Disjoint O₁ O₂ →
      a₁ ∈ O₁ → b₁ ∈ O₂ → ∀ i : Fin 4, ∃ δ > 0,
        (a₁ ∈ crossSeamPage chart f Dom i → ∀ x ∈ Dom, f x ∈ chart '' (crossOpenSheetOf i ∩
          Metric.ball (((0 : ℝ), (0 : ℝ)), t₀) δ) → x ∈ O₁) ∧
        (a₁ ∉ crossSeamPage chart f Dom i → ∀ x ∈ Dom, f x ∈ chart '' (crossOpenSheetOf i ∩
          Metric.ball (((0 : ℝ), (0 : ℝ)), t₀) δ) → x ∈ O₂)) :
    ∃ r > 0, ∃ iP iM : Fin 4, iP ≠ iM ∧ a₁ ∈ crossSeamPage chart f Dom iP ∧
      a₁ ∈ crossSeamPage chart f Dom iM ∧
      ContinuousOn (fun w => (L (h (e (chart w)))).2.1)
        (spliceCylinder ∩ Metric.ball (((0 : ℝ), (0 : ℝ)), t₀) r) ∧
      (∀ w ∈ crossOpenSheetOf iP ∩ Metric.ball (((0 : ℝ), (0 : ℝ)), t₀) r,
        0 < (L (h (e (chart w)))).2.1) ∧
      (∀ w ∈ crossOpenSheetOf iM ∩ Metric.ball (((0 : ℝ), (0 : ℝ)), t₀) r,
        (L (h (e (chart w)))).2.1 < 0) ∧
      (∀ w ∈ spliceCylinder ∩ Metric.ball (((0 : ℝ), (0 : ℝ)), t₀) r, w ∉ crossingFigure →
        (L (h (e (chart w)))).2.1 ≠ 0) := by
  set p : (ℝ × ℝ) × ℝ := (((0 : ℝ), (0 : ℝ)), t₀) with hp
  have hpB : p ∈ (Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) ×ˢ Ioo (0 : ℝ) 1 :=
    ⟨⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩, ht₀⟩
  have hBcyl : (Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) ×ˢ Ioo (0 : ℝ) 1 ⊆ spliceCylinder :=
    prod_mono (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self) Ioo_subset_Icc_self
  have hpcyl : p ∈ spliceCylinder := hBcyl hpB
  have hab : a₁ ≠ b₁ := fun hab => disjoint_left.mp hS ha₁ (hab ▸ hb₁)
  have hJ₁Dom : J₁ ⊆ Dom := (subset_union_left.trans hJ.symm.subset).trans inter_subset_left
  have hJ₂Dom : J₂ ⊆ Dom := (subset_union_right.trans hJ.symm.subset).trans inter_subset_left
  have hS₁D : S₁ ∈ 𝓝[Dom] a₁ := nhdsWithin_le_of_mem (Filter.inter_mem self_mem_nhdsWithin
    (hf a₁ (hS₁ ha₁).1 (e.open_source.mem_nhds (hS₁ ha₁).2))) hS₁n
  have hS₂D : S₂ ∈ 𝓝[Dom] b₁ := nhdsWithin_le_of_mem (Filter.inter_mem self_mem_nhdsWithin
    (hf b₁ (hS₂ hb₁).1 (e.open_source.mem_nhds (hS₂ hb₁).2))) hS₂n
  obtain ⟨W₁, hW₁o, ha₁W₁, hW₁⟩ := mem_nhdsWithin.mp hS₁D
  obtain ⟨W₂, hW₂o, hb₁W₂, hW₂⟩ := mem_nhdsWithin.mp hS₂D
  obtain ⟨G₁, G₂, hG₁, hG₂, ha₁G, hb₁G, hG⟩ := t2_separation hab
  choose δ hδ hδown using hown (W₁ ∩ G₁) (W₂ ∩ G₂) (hW₁o.inter hG₁) (hW₂o.inter hG₂)
    (hG.mono inter_subset_right inter_subset_right) ⟨ha₁W₁, ha₁G⟩ ⟨hb₁W₂, hb₁G⟩
  set Gev : Set (EuclideanSpace ℝ (Fin 3)) := {y | y ∈ U ∧
    ((y ∈ (e ∘ f) '' S₁ ↔ (L (h y)).2.2 = 0) ∧ (y ∈ (e ∘ f) '' S₂ ↔ (L (h y)).2.1 = 0)) ∧
    (Dom ∩ f ⁻¹' e.source) ∩ (e ∘ f) ⁻¹' {y} ⊆ S₁ ∪ S₂} with hGevdef
  have hGev : Gev ∈ 𝓝 (e (chart p)) :=
    Filter.Eventually.and (hU.mem_nhds hzU) (hnear.and hfiber)
  have hcw : ContinuousWithinAt (e ∘ chart) spliceCylinder p :=
    (e.continuousAt hze).comp_continuousWithinAt (hchart p hpcyl)
  obtain ⟨r₀, hr₀, hr₀sub⟩ := Metric.mem_nhdsWithin_iff.mp
    (Filter.inter_mem (hchart p hpcyl (e.open_source.mem_nhds hze)) (hcw hGev))
  have hw₀ : ∀ w ∈ spliceCylinder ∩ Metric.ball p r₀, chart w ∈ e.source ∧ e (chart w) ∈ Gev :=
    fun w hw => ⟨(hr₀sub ⟨hw.2, hw.1⟩).1, (hr₀sub ⟨hw.2, hw.1⟩).2⟩
  have hLc : Continuous fun v : EuclideanSpace ℝ (Fin 3) => (L v).2.1 :=
    continuous_fst.comp (continuous_snd.comp L.toContinuousLinearEquiv.continuous)
  have hβc : ContinuousOn (fun w => (L (h (e (chart w)))).2.1)
      (spliceCylinder ∩ Metric.ball p r₀) := by
    have h1 : ContinuousOn (fun w => e (chart w)) (spliceCylinder ∩ Metric.ball p r₀) :=
      e.continuousOn.comp (hchart.mono inter_subset_left) fun w hw => (hw₀ w hw).1
    exact hLc.comp_continuousOn (hh.isPiecewiseAffineOn.continuousOn.comp h1
      fun w hw => (hw₀ w hw).2.1)
  have hS₂val : ∀ w ∈ spliceCylinder ∩ Metric.ball p r₀, (L (h (e (chart w)))).2.1 = 0 →
      ∃ x ∈ S₂, f x = chart w := by
    intro w hw h0
    obtain ⟨x, hx, hxe⟩ := ((hw₀ w hw).2.2.1.2).mpr h0
    exact ⟨x, hx, e.injOn (hS₂ hx).2 (hw₀ w hw).1 hxe⟩
  have hoff : ∀ w ∈ spliceCylinder ∩ Metric.ball p r₀, w ∉ crossingFigure →
      (L (h (e (chart w)))).2.1 ≠ 0 := by
    intro w hw hwf h0
    obtain ⟨x, hx, hxw⟩ := hS₂val w hw h0
    have hm := himage x (hS₂ hx).1 ⟨w, hw.1, hxw.symm⟩
    rw [hxw] at hm
    exact hwf (mem_of_apply_mem_image_of_injOn hinjc crossingFigure_subset_spliceCylinder hw.1 hm)
  obtain ⟨r₁, hr₁, hr₁₀, hr₁δ⟩ : ∃ r₁ > 0, r₁ ≤ r₀ ∧ ∀ i, r₁ ≤ δ i :=
    ⟨min r₀ (min (min (δ 0) (δ 1)) (min (δ 2) (δ 3))),
      lt_min hr₀ (lt_min (lt_min (hδ 0) (hδ 1)) (lt_min (hδ 2) (hδ 3))), min_le_left _ _,
      fun i => by fin_cases i <;> simp⟩
  have hownA : ∀ i, a₁ ∈ crossSeamPage chart f Dom i → ∀ x ∈ Dom,
      ∀ w ∈ crossOpenSheetOf i ∩ Metric.ball p r₁, f x = chart w → x ∈ S₁ := by
    intro i ha x hx w hw hxw
    have hm := (hδown i).1 ha x hx
      ⟨w, ⟨hw.1, Metric.ball_subset_ball (hr₁δ i) hw.2⟩, hxw.symm⟩
    exact hW₁ ⟨hm.1, hx⟩
  have hownB : ∀ i, a₁ ∉ crossSeamPage chart f Dom i → ∀ x ∈ Dom,
      ∀ w ∈ crossOpenSheetOf i ∩ Metric.ball p r₁, f x = chart w → x ∈ S₂ := by
    intro i ha x hx w hw hxw
    have hm := (hδown i).2 ha x hx
      ⟨w, ⟨hw.1, Metric.ball_subset_ball (hr₁δ i) hw.2⟩, hxw.symm⟩
    exact hW₂ ⟨hm.1, hx⟩
  have hsub₀ : ∀ i, crossOpenSheetOf i ∩ Metric.ball p r₁ ⊆ spliceCylinder ∩ Metric.ball p r₀ :=
    fun i w hw => ⟨crossOpenSheetOf_subset_spliceCylinder i hw.1,
      Metric.ball_subset_ball hr₁₀ hw.2⟩
  have hne : ∀ i, a₁ ∈ crossSeamPage chart f Dom i →
      ∀ w ∈ crossOpenSheetOf i ∩ Metric.ball p r₁, (L (h (e (chart w)))).2.1 ≠ 0 := by
    intro i ha w hw h0
    obtain ⟨x, hx, hxw⟩ := hsurj ⟨w, crossSheetOf_subset_crossingFigure i
      (crossOpenSheetOf_subset_crossSheetOf i hw.1), rfl⟩
    have hxS₁ := hownA i ha x hx w hw hxw
    obtain ⟨x', hx', hx'w⟩ := hS₂val w (hsub₀ i hw) h0
    have hxx' : x = x' := huniq x hx x' (hS₂ hx').1 (hxw.trans hx'w.symm)
      (by rw [hxw]; exact ⟨w, crossOpenSheetOf_subset_sdiff i hw.1, rfl⟩)
    rw [← hxx'] at hx'
    exact disjoint_left.mp hS hxS₁ hx'
  have h0V : (0 : EuclideanSpace ℝ (Fin 3)) ∈ V := by
    rw [← hh0]
    exact hh.1.mapsTo hzU
  have hinv0 : Function.invFunOn h U 0 = e (chart p) := by
    rw [← hh0]
    exact hh.1.injOn.leftInvOn_invFunOn hzU
  have hLs : Continuous fun ε : ℝ => L.symm ((0 : ℝ), ε, (0 : ℝ)) :=
    L.symm.toContinuousLinearEquiv.continuous.comp (by fun_prop)
  have hL0 : L.symm ((0 : ℝ), (0 : ℝ), (0 : ℝ)) = 0 := L.symm.map_zero
  have hg0 : Function.invFunOn h U (L.symm ((0 : ℝ), (0 : ℝ), (0 : ℝ))) = e (chart p) := by
    rw [hL0, hinv0]
  have hgc : ContinuousAt (fun ε : ℝ => Function.invFunOn h U (L.symm ((0 : ℝ), ε, (0 : ℝ))))
      0 := by
    have hc : ContinuousAt (Function.invFunOn h U) (L.symm ((0 : ℝ), (0 : ℝ), (0 : ℝ))) := by
      rw [hL0]
      exact hh.2.2.continuousOn.continuousAt (hV.mem_nhds h0V)
    exact ContinuousAt.comp (f := fun ε : ℝ => L.symm ((0 : ℝ), ε, (0 : ℝ))) hc
      hLs.continuousAt
  obtain ⟨N, hN, hNsub⟩ := exists_mem_nhds_inter_image_subset_image_inter
    isHPolytope_spliceCylinder.1 hchart hinjc hpcyl (Metric.ball_mem_nhds p hr₁)
  set Gtgt : Set (EuclideanSpace ℝ (Fin 3)) := {y | y ∈ e.target ∧
    e.symm y ∈ N ∩ chart '' ((Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) ×ˢ Ioo (0 : ℝ) 1)} with hGtgtdef
  have hGtgt : Gtgt ∈ 𝓝 (e (chart p)) := by
    refine Filter.Eventually.and (e.open_target.mem_nhds (e.map_source hze)) ?_
    refine e.continuousAt_symm (e.map_source hze) ?_
    rw [e.left_inv hze]
    exact Filter.inter_mem hN (hopen.mem_nhds ⟨p, hpB, rfl⟩)
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), L.symm ((0 : ℝ), ε, (0 : ℝ)) ∈ V ∧
      Function.invFunOn h U (L.symm ((0 : ℝ), ε, (0 : ℝ))) ∈ Gev ∧
        Function.invFunOn h U (L.symm ((0 : ℝ), ε, (0 : ℝ))) ∈ Gtgt := by
    refine (hLs.continuousAt.eventually_mem ?_).and
      ((hgc.eventually_mem ?_).and (hgc.eventually_mem ?_))
    · rw [hL0]
      exact hV.mem_nhds h0V
    · rw [hg0]
      exact hGev
    · rw [hg0]
      exact hGtgt
  have hproduce : ∀ ε : ℝ, ε ≠ 0 → (L.symm ((0 : ℝ), ε, (0 : ℝ)) ∈ V ∧
      Function.invFunOn h U (L.symm ((0 : ℝ), ε, (0 : ℝ))) ∈ Gev ∧
        Function.invFunOn h U (L.symm ((0 : ℝ), ε, (0 : ℝ))) ∈ Gtgt) →
      ∃ i, a₁ ∈ crossSeamPage chart f Dom i ∧
        ∃ w ∈ crossOpenSheetOf i ∩ Metric.ball p r₁, (L (h (e (chart w)))).2.1 = ε := by
    rintro ε hε ⟨hV', ⟨-, ⟨hA, hB⟩, hfib⟩, htgt, hsyN, hsyB⟩
    have hhy : h (Function.invFunOn h U (L.symm ((0 : ℝ), ε, (0 : ℝ)))) =
        L.symm ((0 : ℝ), ε, (0 : ℝ)) := hh.1.invOn_invFunOn.2 hV'
    have hLy : L (h (Function.invFunOn h U (L.symm ((0 : ℝ), ε, (0 : ℝ))))) =
        ((0 : ℝ), ε, (0 : ℝ)) := by
      rw [hhy, L.apply_symm_apply]
    obtain ⟨x, hx, hxy⟩ := hA.mpr (by rw [hLy])
    have hyB : Function.invFunOn h U (L.symm ((0 : ℝ), ε, (0 : ℝ))) ∉ (e ∘ f) '' S₂ := by
      intro hm
      have h2 := hB.mp hm
      rw [hLy] at h2
      exact hε h2
    have hfxsrc := (hS₁ hx).2
    have hfx : e.symm (Function.invFunOn h U (L.symm ((0 : ℝ), ε, (0 : ℝ)))) = f x := by
      rw [← hxy]
      exact e.left_inv hfxsrc
    rw [hfx] at hsyN hsyB
    obtain ⟨w, ⟨hwc, hwb⟩, hwx⟩ := hNsub ⟨hsyN, image_mono hBcyl hsyB⟩
    have hwfig : w ∈ crossingFigure := by
      have hm := himage x (hS₁ hx).1 ⟨w, hwc, hwx⟩
      rw [← hwx] at hm
      exact mem_of_apply_mem_image_of_injOn hinjc crossingFigure_subset_spliceCylinder hwc hm
    have hwcore : w ∉ spliceCore := by
      intro hwco
      have hxJ : x ∈ Dom ∩ f ⁻¹' (chart '' spliceCore) := ⟨(hS₁ hx).1, w, hwco, hwx⟩
      rw [hJ] at hxJ
      obtain ⟨x', hx'D, hx'ne, hx'f⟩ : ∃ x', x' ∈ Dom ∧ x' ≠ x ∧ f x' = f x := by
        rcases hxJ with hx1 | hx2
        · obtain ⟨x', hx', hx'w⟩ := hsurj₂ ⟨w, hwco, rfl⟩
          refine ⟨x', hJ₂Dom hx', fun he => ?_, hx'w.trans hwx⟩
          rw [he] at hx'
          exact disjoint_left.mp hJJ hx1 hx'
        · obtain ⟨x', hx', hx'w⟩ := hsurj₁ ⟨w, hwco, rfl⟩
          refine ⟨x', hJ₁Dom hx', fun he => ?_, hx'w.trans hwx⟩
          rw [he] at hx'
          exact disjoint_left.mp hJJ hx' hx2
      have hx'P : x' ∈ (Dom ∩ f ⁻¹' e.source) ∩
          (e ∘ f) ⁻¹' {Function.invFunOn h U (L.symm ((0 : ℝ), ε, (0 : ℝ)))} := by
        refine ⟨⟨hx'D, ?_⟩, ?_⟩
        · rw [mem_preimage, hx'f]
          exact hfxsrc
        · rw [mem_preimage, mem_singleton_iff, ← hxy, Function.comp_apply, Function.comp_apply,
            hx'f]
      rcases hfib hx'P with h1 | h2
      · exact hx'ne (hinjS₁ h1 hx (by rw [Function.comp_apply, Function.comp_apply, hx'f]))
      · exact hyB ⟨x', h2, by rw [← hxy, Function.comp_apply, Function.comp_apply, hx'f]⟩
    obtain ⟨i, hi⟩ := exists_mem_crossOpenSheetOf hwfig hwcore
    have ha : a₁ ∈ crossSeamPage chart f Dom i := by
      by_contra hn
      exact disjoint_left.mp hS hx (hownB i hn x (hS₁ hx).1 w ⟨hi, hwb⟩ hwx.symm)
    refine ⟨i, ha, w, ⟨hi, hwb⟩, ?_⟩
    rw [hwx]
    change (L (h ((e ∘ f) x))).2.1 = ε
    rw [hxy, hLy]
  obtain ⟨ε₀, hε₀, hε₀P⟩ := Metric.eventually_nhds_iff.mp hev
  have hhalf : dist (ε₀ / 2) 0 < ε₀ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hε₀)]
    exact half_lt_self hε₀
  have hhalf' : dist (-(ε₀ / 2)) 0 < ε₀ := by
    rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (half_pos hε₀)]
    exact half_lt_self hε₀
  obtain ⟨iP, haP, wP, hwP, hβP⟩ := hproduce (ε₀ / 2) (half_pos hε₀).ne' (hε₀P hhalf)
  obtain ⟨iM, haM, wM, hwM, hβM⟩ :=
    hproduce (-(ε₀ / 2)) (neg_ne_zero.mpr (half_pos hε₀).ne') (hε₀P hhalf')
  have hconn : ∀ i, IsPreconnected (crossOpenSheetOf i ∩ Metric.ball p r₁) := fun i =>
    ((convex_crossOpenSheetOf i).inter (convex_ball p r₁)).isPreconnected
  have hposall := pos_of_isPreconnected_of_ne_zero (hconn iP) (hβc.mono (hsub₀ iP))
    (hne iP haP) hwP (by rw [hβP]; exact half_pos hε₀)
  have hnegall := neg_of_isPreconnected_of_ne_zero (hconn iM) (hβc.mono (hsub₀ iM))
    (hne iM haM) hwM (by rw [hβM]; linarith)
  refine ⟨r₁, hr₁, iP, iM, ?_, haP, haM,
    hβc.mono (inter_subset_inter_right _ (Metric.ball_subset_ball hr₁₀)), hposall, hnegall,
    fun w hw => hoff w ⟨hw.1, Metric.ball_subset_ball hr₁₀ hw.2⟩⟩
  rintro rfl
  have := hposall wM hwM
  linarith

end Sides

section Opposite

variable {X : Type*} [TopologicalSpace X] [T2Space X] {chart : (ℝ × ℝ) × ℝ → X}
  {f : EuclideanSpace ℝ (Fin 2) → X} {Dom J₁ J₂ : Set (EuclideanSpace ℝ (Fin 2))}

theorem exists_opposite_crossSeamPage (hchart : ContinuousOn chart spliceCylinder)
    (hinjc : InjOn chart spliceCylinder) (hDom : IsCompact Dom) (hf : ContinuousOn f Dom)
    (hJ : Dom ∩ f ⁻¹' (chart '' spliceCore) = J₁ ∪ J₂) (hJ₁ : IsClosed J₁) (hJ₂ : IsClosed J₂)
    (hJJ : Disjoint J₁ J₂) (hinj₁ : InjOn f J₁) (hinj₂ : InjOn f J₂)
    (hsurj₁ : chart '' spliceCore ⊆ f '' J₁) (hsurj₂ : chart '' spliceCore ⊆ f '' J₂)
    (huniq : ∀ x ∈ Dom, ∀ y ∈ Dom, f x = f y →
      f x ∈ chart '' (crossingFigure \ spliceCore) → x = y)
    (himage : ∀ x ∈ Dom, f x ∈ chart '' spliceCylinder → f x ∈ chart '' crossingFigure)
    (hsurj : chart '' crossingFigure ⊆ f '' Dom)
    (hopen : IsOpen (chart '' ((Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) ×ˢ Ioo (0 : ℝ) 1)))
    {e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin 3))}
    (hze : chart (((0 : ℝ), (0 : ℝ)), 1 / 2) ∈ e.source)
    (hcross : HasPLTwoSidedDoubleCrossingAt (e ∘ f) (Dom ∩ f ⁻¹' e.source)
      (e (chart (((0 : ℝ), (0 : ℝ)), 1 / 2)))) :
    ∃ k : Fin 4, J₁ ⊆ crossSeamPage chart f Dom k ∧ J₁ ⊆ crossSeamPage chart f Dom (k + 2) ∧
      J₂ ⊆ crossSeamPage chart f Dom (k + 1) ∧ J₂ ⊆ crossSeamPage chart f Dom (k + 3) := by
  have ht : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have ht' : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht
  obtain ⟨a, b, Sa, Sb, haSa, hbSb, hfa, hfb, hSaP, hSbP, hdisj, hSan, hSbn, hfSa, hfSb, hcr,
    hfiber⟩ := hcross
  have hfa' : f a = chart (((0 : ℝ), (0 : ℝ)), 1 / 2) := e.injOn (hSaP haSa).2 hze hfa
  have hfb' : f b = chart (((0 : ℝ), (0 : ℝ)), 1 / 2) := e.injOn (hSbP hbSb).2 hze hfb
  have hab : a ≠ b := fun he => disjoint_left.mp hdisj haSa (he ▸ hbSb)
  obtain ⟨U, V, h, L, hU, hV, hzU, hh, hh0, hnear⟩ := hcr.exists_linearEquiv_normalForm
  have hownA := fun O₁ O₂ hO₁ hO₂ hO ha hb i =>
    exists_forall_mem_of_crossSeamPage_ownership (O₁ := O₁) (O₂ := O₂) hchart hinjc hDom hf hJ
      hJ₁ hJ₂ hJJ hinj₁ hinj₂ hsurj₁ hsurj₂ huniq hsurj ht' (hSaP haSa).1 (hSbP hbSb).1 hfa' hfb'
      hab hO₁ hO₂ hO ha hb i
  have hownB := fun O₁ O₂ hO₁ hO₂ hO ha hb i =>
    exists_forall_mem_of_crossSeamPage_ownership (O₁ := O₁) (O₂ := O₂) hchart hinjc hDom hf hJ
      hJ₁ hJ₂ hJJ hinj₁ hinj₂ hsurj₁ hsurj₂ huniq hsurj ht' (hSbP hbSb).1 (hSaP haSa).1 hfb' hfa'
      hab.symm hO₁ hO₂ hO ha hb i
  obtain ⟨r, hr, iP, iM, hne, haP, haM, hβc, hpos, hneg, hoff⟩ :=
    exists_two_sides_of_crossSeamSheet hchart hinjc hf hJ hJJ hsurj₁ hsurj₂ huniq himage hsurj
      hopen ht hze haSa hbSb hSaP hSbP hdisj hSan hSbn hfSa.bijOn.injOn hfiber hU hV hzU hh hh0
      hnear hownA
  have hnear' : ∀ᶠ y in 𝓝 (e (chart (((0 : ℝ), (0 : ℝ)), 1 / 2))),
      (y ∈ (e ∘ f) '' Sb ↔
          ((L.trans ((LinearEquiv.refl ℝ ℝ).prodCongr (LinearEquiv.prodComm ℝ ℝ ℝ))) (h y)).2.2
            = 0) ∧
        (y ∈ (e ∘ f) '' Sa ↔
          ((L.trans ((LinearEquiv.refl ℝ ℝ).prodCongr (LinearEquiv.prodComm ℝ ℝ ℝ))) (h y)).2.1
            = 0) :=
    hnear.mono fun y hy => ⟨hy.2, hy.1⟩
  have hfiber' : ∀ᶠ y in 𝓝 (e (chart (((0 : ℝ), (0 : ℝ)), 1 / 2))),
      (Dom ∩ f ⁻¹' e.source) ∩ (e ∘ f) ⁻¹' {y} ⊆ Sb ∪ Sa :=
    hfiber.mono fun y hy => hy.trans (union_comm Sa Sb).subset
  obtain ⟨-, -, kP, kM, hkne, hbP, hbM, -, -, -, -⟩ :=
    exists_two_sides_of_crossSeamSheet hchart hinjc hf hJ hJJ hsurj₁ hsurj₂ huniq himage hsurj
      hopen ht hze hbSb haSa hSbP hSaP hdisj.symm hSbn hSan hfSb.bijOn.injOn hfiber' hU hV hzU hh
      hh0 hnear' hownB
  have hwedge : iM = iP + 2 := by
    have hn1 : iM ≠ iP + 1 := by
      rintro rfl
      exact not_crossWedge_of_succ ht' hr iP hβc hpos hneg hoff
    have hn2 : iP ≠ iM + 1 := by
      intro hi
      refine not_crossWedge_of_succ (β := fun w => -(L (h (e (chart w)))).2.1) ht' hr iM
        hβc.neg (fun w hw => neg_pos.mpr (hneg w hw)) (fun w hw => ?_)
        (fun w hw hwf => neg_ne_zero.mpr (hoff w hw hwf))
      rw [← hi] at hw
      exact neg_lt_zero.mpr (hpos w hw)
    have key : ∀ x y : Fin 4, x ≠ y → y ≠ x + 1 → x ≠ y + 1 → y = x + 2 := by decide
    exact key iP iM hne hn1 hn2
  rw [hwedge] at haM
  have hhu : ∀ i, ∀ x ∈ Dom, ∀ y ∈ Dom, f x = f y → f x ∈ chart '' crossOpenSheetOf i → x = y :=
    fun i x hx y hy hxy hm => huniq x hx y hy hxy
      (image_mono (crossOpenSheetOf_subset_sdiff i) hm)
  have hsu : ∀ i, chart '' crossOpenSheetOf i ⊆ f '' Dom := fun i =>
    (image_mono ((crossOpenSheetOf_subset_sdiff i).trans sdiff_subset)).trans hsurj
  have hclass : ∀ i, (J₁ ⊆ crossSeamPage chart f Dom i ∧ Disjoint J₂ (crossSeamPage chart f Dom i))
      ∨ (J₂ ⊆ crossSeamPage chart f Dom i ∧ Disjoint J₁ (crossSeamPage chart f Dom i)) :=
    fun i => crossSeamPage_class hchart hinjc hDom hf hJ hJ₁ hJ₂ hJJ hinj₁ hinj₂ hsurj₁ hsurj₂
      (hhu i) (hsu i)
  have hmain : ∀ {Ja Jb : Set (EuclideanSpace ℝ (Fin 2))},
      (∀ i, (Ja ⊆ crossSeamPage chart f Dom i ∧ Disjoint Jb (crossSeamPage chart f Dom i)) ∨
        (Jb ⊆ crossSeamPage chart f Dom i ∧ Disjoint Ja (crossSeamPage chart f Dom i))) →
      a ∈ Ja → b ∈ Jb →
      Ja ⊆ crossSeamPage chart f Dom iP ∧ Ja ⊆ crossSeamPage chart f Dom (iP + 2) ∧
        Jb ⊆ crossSeamPage chart f Dom (iP + 1) ∧ Jb ⊆ crossSeamPage chart f Dom (iP + 3) := by
    intro Ja Jb hcl haJ hbJ
    have hA : ∀ i, a ∈ crossSeamPage chart f Dom i → Ja ⊆ crossSeamPage chart f Dom i := by
      intro i hi
      rcases hcl i with ⟨hs, -⟩ | ⟨-, hd⟩
      · exact hs
      · exact absurd hi (disjoint_left.mp hd haJ)
    have hB : ∀ i, b ∈ crossSeamPage chart f Dom i → Jb ⊆ crossSeamPage chart f Dom i := by
      intro i hi
      rcases hcl i with ⟨-, hd⟩ | ⟨hs, -⟩
      · exact absurd hi (disjoint_left.mp hd hbJ)
      · exact hs
    have hexcl : ∀ i, b ∈ crossSeamPage chart f Dom i → a ∉ crossSeamPage chart f Dom i := by
      intro i hbi hai
      rcases hcl i with ⟨-, hd⟩ | ⟨-, hd⟩
      · exact disjoint_left.mp hd hbJ hbi
      · exact disjoint_left.mp hd haJ hai
    have key : ∀ i k k' : Fin 4, k ≠ i → k ≠ i + 2 → k' ≠ i → k' ≠ i + 2 → k ≠ k' →
        (k = i + 1 ∧ k' = i + 3) ∨ (k = i + 3 ∧ k' = i + 1) := by decide
    have hk := key iP kP kM (fun he => hexcl _ hbP (he ▸ haP)) (fun he => hexcl _ hbP (he ▸ haM))
      (fun he => hexcl _ hbM (he ▸ haP)) (fun he => hexcl _ hbM (he ▸ haM)) hkne
    refine ⟨hA _ haP, hA _ haM, ?_, ?_⟩
    · rcases hk with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact hB _ (h1 ▸ hbP)
      · exact hB _ (h2 ▸ hbM)
    · rcases hk with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact hB _ (h2 ▸ hbM)
      · exact hB _ (h1 ▸ hbP)
  have hcore : (((0 : ℝ), (0 : ℝ)), (1 / 2 : ℝ)) ∈ spliceCore := ⟨mem_singleton _, ht'⟩
  have hm₁ := Function.invFunOn_mem (hsurj₁ ⟨_, hcore, rfl⟩)
  have hm₂ := Function.invFunOn_mem (hsurj₂ ⟨_, hcore, rfl⟩)
  have e1 : ∀ x : Fin 4, x + 1 + 2 = x + 3 := by decide
  have e2 : ∀ x : Fin 4, x + 1 + 1 = x + 2 := by decide
  have e3 : ∀ x : Fin 4, x + 1 + 3 = x := by decide
  rcases eq_invFunOn_or_eq_invFunOn_of_crossSeam hJ hinj₁ hinj₂ hsurj₁ hsurj₂ ht' (hSaP haSa).1
    hfa' with ha | ha <;>
  rcases eq_invFunOn_or_eq_invFunOn_of_crossSeam hJ hinj₁ hinj₂ hsurj₁ hsurj₂ ht' (hSbP hbSb).1
    hfb' with hb | hb
  · exact absurd (ha.trans hb.symm) hab
  · rw [← ha] at hm₁
    rw [← hb] at hm₂
    obtain ⟨h1, h2, h3, h4⟩ := hmain hclass hm₁ hm₂
    exact ⟨iP, h1, h2, h3, h4⟩
  · rw [← ha] at hm₂
    rw [← hb] at hm₁
    obtain ⟨h1, h2, h3, h4⟩ := hmain (fun i => (hclass i).symm) hm₂ hm₁
    refine ⟨iP + 1, h3, ?_, ?_, ?_⟩
    · rw [e1]
      exact h4
    · rw [e2]
      exact h2
    · rw [e3]
      exact h1
  · exact absurd (ha.trans hb.symm) hab

end Opposite

end DifferentialGeometry.Topology.PiecewiseLinear
