import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import DifferentialGeometry.External.Schoenflies.SimpleArc
import DifferentialGeometry.External.Schoenflies.Subarc
import DifferentialGeometry.External.Schoenflies.Concatenate
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import DifferentialGeometry.Topology.PlanarJordan.LocalSides
import DifferentialGeometry.External.Schoenflies.JordanClosed

section

set_option autoImplicit false

open Set

namespace DifferentialGeometry.Topology

theorem exists_contact_interval_avoiding_closed_sets
    {X : Type*} [TopologicalSpace X] {γ : ℝ → X}
    (hγ : ContinuousOn γ (Icc (0 : ℝ) 1)) {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B)
    (hdisj : Disjoint (γ '' Icc (0 : ℝ) 1 ∩ A) B)
    (h0 : γ 0 ∈ A) (h1 : γ 1 ∈ B) :
    ∃ s t : ℝ, 0 ≤ s ∧ s < t ∧ t ≤ 1 ∧ γ s ∈ A ∧ γ t ∈ B ∧
      ∀ r ∈ Ioo s t, γ r ∉ A ∪ B := by
  let T := Icc (0 : ℝ) 1 ∩ γ ⁻¹' B
  have hT : IsCompact T := isCompact_Icc.of_isClosed_subset
    (hγ.preimage_isClosed_of_isClosed isClosed_Icc hB) inter_subset_left
  have h1T : (1 : ℝ) ∈ T := ⟨⟨zero_le_one, le_rfl⟩, h1⟩
  obtain ⟨t, ht, hmin⟩ := hT.exists_isMinOn ⟨1, h1T⟩ continuousOn_id
  let S := Icc (0 : ℝ) t ∩ γ ⁻¹' A
  have hS : IsCompact S := isCompact_Icc.of_isClosed_subset
    ((hγ.mono (Icc_subset_Icc le_rfl ht.1.2)).preimage_isClosed_of_isClosed isClosed_Icc hA)
    inter_subset_left
  have h0S : (0 : ℝ) ∈ S := ⟨⟨le_rfl, ht.1.1⟩, h0⟩
  obtain ⟨s, hs, hmax⟩ := hS.exists_isMaxOn ⟨0, h0S⟩ continuousOn_id
  have hst : s < t := by
    apply lt_of_le_of_ne hs.1.2
    intro h
    apply disjoint_left.mp hdisj ⟨⟨s, ⟨hs.1.1, hs.1.2.trans ht.1.2⟩, rfl⟩, hs.2⟩
    exact h.symm ▸ ht.2
  refine ⟨s, t, hs.1.1, hst, ht.1.2, hs.2, ht.2, ?_⟩
  intro r hr
  rintro (hrA | hrB)
  · have hrS : r ∈ S := ⟨⟨hs.1.1.trans hr.1.le, hr.2.le⟩, hrA⟩
    exact (not_le_of_gt hr.1) (hmax hrS)
  · have hrT : r ∈ T := ⟨⟨hs.1.1.trans hr.1.le, hr.2.le.trans ht.1.2⟩, hrB⟩
    exact (not_le_of_gt hr.2) (hmin hrT)

end DifferentialGeometry.Topology

end

section

set_option autoImplicit false
noncomputable section

open Set Metric

namespace DifferentialGeometry.Topology.PlanarJordan

local notation "Plane" => Schoenflies.Plane

theorem exists_jordan_curve_of_connected_punctured_spine
    {P : Set Plane} (hP : IsOpen P) (hPc : IsPreconnected P)
    (e : OpenPartialHomeomorph (ℝ × ℝ) Plane) {ε : ℝ} (hε : 0 < ε)
    (hsource : Icc (-ε) ε ×ˢ Icc (-ε) ε ⊆ e.source)
    (hcenter : e (0, 0) ∉ P)
    (hspine : ∀ t ∈ Icc (-ε) ε, t ≠ 0 → e (t, 0) ∈ P) :
    ∃ C : Set Plane, Schoenflies.IsJordanCurve C ∧ C ⊆ P ∪ {e (0, 0)} ∧
      ∃ a b : ℝ, a < 0 ∧ 0 < b ∧ Icc a b ⊆ Icc (-ε) ε ∧
        ∃ A : Set Plane, IsCompact A ∧ e (0, 0) ∉ A ∧
          C = A ∪ (fun t : ℝ => e (t, 0)) '' Icc a b := by
  let L : ℝ → Plane := fun t => e (t, 0)
  have hline (t : ℝ) (ht : t ∈ Icc (-ε) ε) : (t, (0 : ℝ)) ∈ e.source :=
    hsource ⟨ht, by constructor <;> linarith⟩
  have hLc : ContinuousOn L (Icc (-ε) ε) :=
    e.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn hline
  have hLi : InjOn L (Icc (-ε) ε) := by
    intro s hs t ht heq
    exact congrArg Prod.fst (e.injOn (hline s hs) (hline t ht) heq)
  have hleft : L (-ε) ∈ P := hspine _ ⟨le_rfl, by linarith⟩ (by linarith)
  have hright : L ε ∈ P := hspine _ ⟨by linarith, le_rfl⟩ hε.ne'
  have hneq : L (-ε) ≠ L ε := by
    intro h
    have heq := hLi ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ h
    linarith
  obtain ⟨A₀, hA₀P, _, hA₀⟩ := Schoenflies.exists_simple_arc_of_isPreconnected
    hP hPc hleft hright hneq
  obtain ⟨γ, hγc, hγi, hγA, hγ0, hγ1⟩ := hA₀
  have hγP (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : γ t ∈ P :=
    hA₀P (hγA ▸ mem_image_of_mem γ ht)
  let Aleft := L '' Icc (-ε) 0
  let Aright := L '' Icc 0 ε
  have hleftSub : Icc (-ε) (0 : ℝ) ⊆ Icc (-ε) ε := Icc_subset_Icc le_rfl hε.le
  have hrightSub : Icc (0 : ℝ) ε ⊆ Icc (-ε) ε := Icc_subset_Icc (by linarith) le_rfl
  have hAcl : IsClosed Aleft :=
    (isCompact_Icc.image_of_continuousOn (hLc.mono hleftSub)).isClosed
  have hAcr : IsClosed Aright :=
    (isCompact_Icc.image_of_continuousOn (hLc.mono hrightSub)).isClosed
  have hdisj : Disjoint (γ '' Icc (0 : ℝ) 1 ∩ Aleft) Aright := by
    apply disjoint_left.mpr
    rintro x ⟨⟨t, ht, htx⟩, a, ha, hax⟩ ⟨b, hb, hbx⟩
    have hab := hLi (hleftSub ha) (hrightSub hb) (hax.trans hbx.symm)
    have ha0 : a = 0 := by linarith [ha.2, hb.1]
    apply hcenter
    have hxP : x ∈ P := htx ▸ hγP t ht
    simpa only [← hax, ha0, L] using hxP
  have hγ0l : γ 0 ∈ Aleft := ⟨-ε, ⟨le_rfl, by linarith⟩, hγ0.symm⟩
  have hγ1r : γ 1 ∈ Aright := ⟨ε, ⟨hε.le, le_rfl⟩, hγ1.symm⟩
  obtain ⟨s, t, hs0, hst, ht1, hsA, htA, havoid⟩ :=
    DifferentialGeometry.Topology.exists_contact_interval_avoiding_closed_sets
      hγc hAcl hAcr hdisj hγ0l hγ1r
  obtain ⟨a, ha, has⟩ := hsA
  obtain ⟨b, hb, hbt⟩ := htA
  have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨hs0, hst.le.trans ht1⟩
  have htI : t ∈ Icc (0 : ℝ) 1 := ⟨hs0.trans hst.le, ht1⟩
  have ha0 : a < 0 := lt_of_le_of_ne ha.2 (by
    intro h
    apply hcenter
    simpa only [← has, h, L] using hγP s hsI)
  have hb0 : 0 < b := lt_of_le_of_ne hb.1 (by
    intro h
    apply hcenter
    simpa only [← hbt, ← h, L] using hγP t htI)
  have hab : a < b := ha0.trans hb0
  have habSub : Icc a b ⊆ Icc (-ε) ε := Icc_subset_Icc ha.1 hb.2
  let A := γ '' Icc s t
  let B := L '' Icc a b
  have hA : Schoenflies.IsArcBetween A (L a) (L b) := by
    have h := Schoenflies.isArcBetween_subarc_of_injOn_I hγc hγi hsI htI hst.ne
    rw [uIcc_of_le hst.le] at h
    simpa only [has, hbt] using h
  have hB : Schoenflies.IsArcBetween B (L a) (L b) := by
    let f := Schoenflies.subarc L a b
    have hLc' : ContinuousOn L (Icc a b) := hLc.mono habSub
    have hf : ContinuousOn f (Icc (0 : ℝ) 1) := by
      apply hLc'.comp (Schoenflies.continuous_reparam).continuousOn
      simpa only [uIcc_of_le hab.le] using Schoenflies.mapsTo_reparam (a := a) (b := b)
    have hfi : InjOn f (Icc (0 : ℝ) 1) :=
      Schoenflies.injOn_subarc (hLi.mono (by simpa only [uIcc_of_le hab.le] using habSub)) hab.ne
    refine ⟨f, hf, hfi, ?_, ?_, ?_⟩
    · rw [Schoenflies.subarc_image, uIcc_of_le hab.le]
    · simp only [f, Schoenflies.subarc, Schoenflies.reparam, zero_mul, add_zero]
    · simp only [f, Schoenflies.subarc, Schoenflies.reparam, one_mul, add_sub_cancel]
  have hmeet : ∀ x ∈ A, x ∈ B → x = L a ∨ x = L b := by
    rintro x ⟨r, hr, hrx⟩ ⟨q, hq, hqx⟩
    by_cases hrs : r = s
    · exact Or.inl (hrx.symm.trans (hrs ▸ has.symm))
    by_cases hrt : r = t
    · exact Or.inr (hrx.symm.trans (hrt ▸ hbt.symm))
    have hr' : r ∈ Ioo s t := ⟨lt_of_le_of_ne hr.1 (Ne.symm hrs), lt_of_le_of_ne hr.2 hrt⟩
    apply False.elim
    apply havoid r hr'
    have hqfull := habSub hq
    by_cases hq0 : q ≤ 0
    · exact Or.inl ⟨q, ⟨hqfull.1, hq0⟩, hqx.trans hrx.symm⟩
    · exact Or.inr ⟨q, ⟨(lt_of_not_ge hq0).le, hqfull.2⟩, hqx.trans hrx.symm⟩
  have hJ := Schoenflies.IsJordanCurve.of_two_arcs hA hB.reverse hmeet
  refine ⟨A ∪ B, hJ, ?_, a, b, ha0, hb0, habSub, A, hA.isArc.isCompact, ?_, rfl⟩
  · intro x hx
    rcases hx with ⟨r, hr, rfl⟩ | ⟨q, hq, rfl⟩
    · exact Or.inl (hγP r ⟨hs0.trans hr.1, hr.2.trans ht1⟩)
    · by_cases hq0 : q = 0
      · exact Or.inr (by simpa only [hq0, L] using mem_singleton (e (0, 0)))
      · exact Or.inl (hspine q (habSub hq) hq0)
  · rintro ⟨r, hr, heq⟩
    exact hcenter (heq ▸ hγP r ⟨hs0.trans hr.1, hr.2.trans ht1⟩)

end DifferentialGeometry.Topology.PlanarJordan

end

end

section

set_option autoImplicit false
noncomputable section

open Set Metric Filter
open scoped Topology

namespace DifferentialGeometry.Topology.PlanarJordan

local notation "Plane" => Schoenflies.Plane

theorem exists_cross_box_of_arc_union_spine
    (e : OpenPartialHomeomorph (ℝ × ℝ) Plane) {ε a b : ℝ} (hε : 0 < ε)
    (hsource : Icc (-ε) ε ×ˢ Icc (-ε) ε ⊆ e.source)
    (ha : a < 0) (hb : 0 < b) (hab : Icc a b ⊆ Icc (-ε) ε)
    {A : Set Plane} (hA : IsCompact A) (h0 : e (0, 0) ∉ A) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧
      (Ioo (-δ) δ ×ˢ Ioo (-δ) δ ⊆ e.source) ∧
      ∀ p ∈ Ioo (-δ) δ ×ˢ Ioo (-δ) δ,
        e p ∈ A ∪ (fun t : ℝ => e (t, 0)) '' Icc a b ↔ p.2 = 0 := by
  have h0source : (0 : ℝ × ℝ) ∈ e.source :=
    hsource (show ((0 : ℝ), (0 : ℝ)) ∈ Icc (-ε) ε ×ˢ Icc (-ε) ε from
      ⟨by constructor <;> linarith, by constructor <;> linarith⟩)
  have hc : ContinuousAt e (0 : ℝ × ℝ) :=
    e.continuousOn.continuousAt (e.open_source.mem_nhds h0source)
  have hnear : e ⁻¹' Aᶜ ∈ 𝓝 (0 : ℝ × ℝ) :=
    hc.preimage_mem_nhds (hA.isClosed.isOpen_compl.mem_nhds h0)
  obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.mp hnear
  let δ := min (min η ε) (min (-a) b) / 2
  have hδ : 0 < δ := half_pos (lt_min (lt_min hη hε) (lt_min (neg_pos.mpr ha) hb))
  have hδη : δ < η := (half_lt_self (lt_min (lt_min hη hε)
    (lt_min (neg_pos.mpr ha) hb))).trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδε : δ < ε := (half_lt_self (lt_min (lt_min hη hε)
    (lt_min (neg_pos.mpr ha) hb))).trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hδa : δ < -a := (half_lt_self (lt_min (lt_min hη hε)
    (lt_min (neg_pos.mpr ha) hb))).trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδb : δ < b := (half_lt_self (lt_min (lt_min hη hε)
    (lt_min (neg_pos.mpr ha) hb))).trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hbox : Ioo (-δ) δ ×ˢ Ioo (-δ) δ ⊆ e.source := by
    intro p hp
    apply hsource
    constructor <;> constructor <;> linarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]
  refine ⟨δ, hδ, hδε, hbox, ?_⟩
  intro p hp
  have hpη : p ∈ ball (0 : ℝ × ℝ) η := by
    rw [mem_ball, Prod.dist_eq]
    change max (dist p.1 0) (dist p.2 0) < η
    rw [dist_zero_right, dist_zero_right, max_lt_iff]
    constructor <;> rw [Real.norm_eq_abs, abs_lt] <;>
      constructor <;> linarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]
  have hpA : e p ∉ A := hηsub hpη
  constructor
  · rintro (hpA' | ⟨t, ht, hte⟩)
    · exact (hpA hpA').elim
    · have htS : (t, (0 : ℝ)) ∈ e.source :=
        hsource ⟨hab ht, by constructor <;> linarith⟩
      exact (congrArg Prod.snd (e.injOn htS (hbox hp) hte)).symm
  · intro hp0
    apply Or.inr
    refine ⟨p.1, ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩, ?_⟩
    have he : (p.1, (0 : ℝ)) = p := Prod.ext rfl hp0.symm
    exact congrArg e he

end DifferentialGeometry.Topology.PlanarJordan

end

end

section

set_option autoImplicit false
noncomputable section

open Set Metric

namespace DifferentialGeometry.Topology.PlanarJordan

local notation "Plane" => Schoenflies.Plane

theorem not_disjoint_preconnected_regions_of_local_cross
    {P N : Set Plane} (hP : IsOpen P) (hPc : IsPreconnected P) (hNc : IsPreconnected N)
    (hPN : Disjoint P N)
    (e : OpenPartialHomeomorph (ℝ × ℝ) Plane) {ε : ℝ} (hε : 0 < ε)
    (hsource : Icc (-ε) ε ×ˢ Icc (-ε) ε ⊆ e.source)
    (hcenterP : e (0, 0) ∉ P) (hcenterN : e (0, 0) ∉ N)
    (hspine : ∀ t ∈ Icc (-ε) ε, t ≠ 0 → e (t, 0) ∈ P)
    (hvertical : ∀ t ∈ Icc (-ε) ε, t ≠ 0 → e (0, t) ∈ N) : False := by
  obtain ⟨C, hC, hCP, a, b, ha, hb, hab, A, hA, hA0, hCA⟩ :=
    exists_jordan_curve_of_connected_punctured_spine hP hPc e hε hsource hcenterP hspine
  obtain ⟨δ, hδ, hδε, hbox, hcurve⟩ :=
    exists_cross_box_of_arc_union_spine e hε hsource ha hb hab hA hA0
  have hsep := Schoenflies.jordan_curve_theorem hC
  have hcurve' : ∀ p ∈ Ioo (-δ) δ ×ˢ Ioo (-δ) δ, e p ∈ C ↔ p.2 = 0 := by
    rw [hCA]
    exact hcurve
  have hsplit := flowBox_halves_in_opposite_regions
    hsep.isOpen_inside hsep.isOpen_outside Schoenflies.disjoint_inside_outside
    (Schoenflies.inside_union_outside C) hsep.frontier_inside hsep.frontier_outside
    e (by linarith : -δ < δ) hδ hbox hcurve'
  have hNcomp : N ⊆ Cᶜ := by
    intro x hx hxC
    rcases hCP hxC with hxP | hx0
    · exact disjoint_left.mp hPN hxP hx
    · have heq := mem_singleton_iff.mp hx0
      exact hcenterN (heq ▸ hx)
  have hNcover : N ⊆ Schoenflies.inside C ∪ Schoenflies.outside C := by
    rw [Schoenflies.inside_union_outside]
    exact hNcomp
  have hNsides := hNc.subset_or_subset hsep.isOpen_inside hsep.isOpen_outside
    Schoenflies.disjoint_inside_outside hNcover
  have hNpos : e (0, δ / 2) ∈ N := hvertical _
    ⟨by linarith, by linarith⟩ (by linarith)
  have hNneg : e (0, -(δ / 2)) ∈ N := hvertical _
    ⟨by linarith, by linarith⟩ (by linarith)
  have hpos : e (0, δ / 2) ∈ e '' (Ioo (-δ) δ ×ˢ Ioo (0 : ℝ) δ) :=
    ⟨(0, δ / 2), ⟨⟨by linarith, by linarith⟩, by constructor <;> linarith⟩, rfl⟩
  have hneg : e (0, -(δ / 2)) ∈ e '' (Ioo (-δ) δ ×ˢ Ioo (-δ) (0 : ℝ)) :=
    ⟨(0, -(δ / 2)), ⟨⟨by linarith, by linarith⟩, by constructor <;> linarith⟩, rfl⟩
  rcases hsplit with ⟨hpi, hno⟩ | ⟨hpo, hni⟩ <;> rcases hNsides with hNi | hNo
  · exact disjoint_left.mp Schoenflies.disjoint_inside_outside (hNi hNneg) (hno hneg)
  · exact disjoint_left.mp Schoenflies.disjoint_inside_outside (hpi hpos) (hNo hNpos)
  · exact disjoint_left.mp Schoenflies.disjoint_inside_outside (hNi hNpos) (hpo hpos)
  · exact disjoint_left.mp Schoenflies.disjoint_inside_outside (hni hneg) (hNo hNneg)

end DifferentialGeometry.Topology.PlanarJordan

end

end

section

set_option autoImplicit false
noncomputable section

open Set

namespace DifferentialGeometry.Topology.PlanarJordan

local notation "Plane" => Schoenflies.Plane

theorem not_alternating_cross_of_preconnected_strict_levels
    {D : Set Plane} (hD : IsOpen D) {u : Plane → ℝ} (hu : ContinuousOn u D) {c : ℝ}
    (hpos : IsPreconnected {x | x ∈ D ∧ c < u x})
    (hneg : IsPreconnected {x | x ∈ D ∧ u x < c})
    (e : OpenPartialHomeomorph (ℝ × ℝ) Plane) {ε : ℝ} (hε : 0 < ε)
    (hsource : Icc (-ε) ε ×ˢ Icc (-ε) ε ⊆ e.source)
    (himage : MapsTo e (Icc (-ε) ε ×ˢ Icc (-ε) ε) D)
    (hcenter : u (e (0, 0)) = c)
    (hpositive : ∀ t ∈ Icc (-ε) ε, t ≠ 0 → c < u (e (t, 0)))
    (hnegative : ∀ t ∈ Icc (-ε) ε, t ≠ 0 → u (e (0, t)) < c) : False := by
  let P := {x | x ∈ D ∧ c < u x}
  let N := {x | x ∈ D ∧ u x < c}
  have hP : IsOpen P := by
    have h := hu.isOpen_inter_preimage hD (isOpen_Ioi : IsOpen (Ioi c))
    exact h
  have hPN : Disjoint P N := disjoint_left.mpr fun x hx hy => (not_lt_of_gt hx.2) hy.2
  apply not_disjoint_preconnected_regions_of_local_cross hP hpos hneg hPN e hε hsource
  · intro h
    exact (lt_irrefl c) (hcenter ▸ h.2)
  · intro h
    exact (lt_irrefl c) (hcenter ▸ h.2)
  · intro t ht hne
    exact ⟨himage ⟨ht, by constructor <;> linarith⟩, hpositive t ht hne⟩
  · intro t ht hne
    exact ⟨himage ⟨by constructor <;> linarith, ht⟩, hnegative t ht hne⟩

end DifferentialGeometry.Topology.PlanarJordan

end

end
