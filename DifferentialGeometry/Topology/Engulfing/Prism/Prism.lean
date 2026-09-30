import DifferentialGeometry.Topology.Order.SemicontinuousInsertion.Insertion
import DifferentialGeometry.Topology.Engulfing.Prism.Stretch
import DifferentialGeometry.Topology.Homeomorph.ExtensionByIdentity
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Analysis.Convex.Segment

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Topology

theorem isOpen_prism_neighborhood {X : Type*} [TopologicalSpace X] {f g : X → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hfg : ∀ x, f x ≤ g x)
    {W : Set (X × ℝ)} (hW : IsOpen W) :
    IsOpen {x | ∀ t ∈ Icc (f x) (g x), (x, t) ∈ W} := by
  let T : X × Icc (0 : ℝ) 1 → X × ℝ := fun p =>
    (p.1, (1 - p.2.1) * f p.1 + p.2.1 * g p.1)
  have hT : Continuous T := continuous_fst.prodMk
    (((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).mul
      (hf.comp continuous_fst)).add
      ((continuous_subtype_val.comp continuous_snd).mul (hg.comp continuous_fst)))
  have hclosed : IsClosed (Prod.fst '' (T ⁻¹' Wᶜ)) :=
    isClosedMap_fst_of_compactSpace _ (hW.isClosed_compl.preimage hT)
  have heq : {x | ∀ r : Icc (0 : ℝ) 1, T (x, r) ∈ W} =
      (Prod.fst '' (T ⁻¹' Wᶜ))ᶜ := by
    ext x
    constructor
    · intro h
      rintro ⟨⟨y, r⟩, hy, hyx⟩
      change y = x at hyx
      subst y
      exact hy (h r)
    · intro h r
      by_contra hr
      exact h ⟨(x, r), hr, rfl⟩
  have hgood : IsOpen {x | ∀ r : Icc (0 : ℝ) 1, T (x, r) ∈ W} := by
    rw [heq]
    exact hclosed.isOpen_compl
  convert hgood using 1
  ext x
  constructor
  · intro h r
    apply h
    apply (Convex.mem_Icc (hfg x)).mpr
    exact ⟨1 - r.1, r.1, sub_nonneg.mpr r.2.2, r.2.1, by ring, rfl⟩
  · intro h t ht
    obtain ⟨a, b, ha, hb, hab, he⟩ := (Convex.mem_Icc (hfg x)).mp ht
    have hb1 : b ≤ 1 := by linarith
    have hr := h ⟨b, hb, hb1⟩
    change (x, (1 - b) * f x + b * g x) ∈ W at hr
    have hab' : a = 1 - b := by linarith
    rw [hab'] at he
    rwa [he] at hr

theorem exists_prism_engulfing {X : Type*} [MetricSpace X] {f g : X → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hfg : ∀ x, f x ≤ g x)
    {U W : Set (X × ℝ)} (hU : IsOpen U) (hW : IsOpen W)
    (hgraph : ∀ x, (x, f x) ∈ U)
    (hprism : ∀ x t, t ∈ Icc (f x) (g x) → (x, t) ∈ W) :
    ∃ H : (X × ℝ) ≃ₜ (X × ℝ),
      (∀ p, (H p).1 = p.1) ∧ (∀ p ∉ W, H p = p) ∧
      (∀ x, f x = g x → ∀ t, H (x, t) = (x, t)) ∧
      ∀ x t, t ∈ Icc (f x) (g x) → (x, t) ∈ H '' U := by
  obtain ⟨u, huc, hu, huU⟩ := exists_continuous_graph_width hf hU hgraph
  obtain ⟨v, hvc, hv, hvW⟩ := exists_continuous_graph_width hf hW
    (fun x => hprism x (f x) ⟨le_rfl, hfg x⟩)
  obtain ⟨w, hwc, hw, hwW⟩ := exists_continuous_graph_width hg hW
    (fun x => hprism x (g x) ⟨hfg x, le_rfl⟩)
  let ε : X → ℝ := fun x => min (u x) (v x) / 2
  let β : X → ℝ := fun x => min (u x) (g x - f x) / 2
  have hε (x : X) : 0 < ε x ∧ ε x ≤ u x ∧ ε x ≤ v x := by
    have hp : 0 < min (u x) (v x) := lt_min (hu x) (hv x)
    dsimp [ε]
    constructor
    · positivity
    · constructor <;> linarith [min_le_left (u x) (v x), min_le_right (u x) (v x)]
  have hβ (x : X) : 0 ≤ β x ∧ β x ≤ u x ∧ β x ≤ g x - f x := by
    have hp : 0 ≤ min (u x) (g x - f x) :=
      le_min (hu x).le (sub_nonneg.mpr (hfg x))
    dsimp [β]
    constructor
    · positivity
    · constructor <;> linarith [min_le_left (u x) (g x - f x), min_le_right (u x) (g x - f x)]
  let a : X → ℝ := fun x => f x - ε x
  let b : X → ℝ := fun x => f x + β x
  let d : X → ℝ := fun x => g x + w x / 2
  have ha : Continuous a := hf.sub ((huc.min hvc).div_const 2)
  have hb : Continuous b := hf.add ((huc.min (hg.sub hf)).div_const 2)
  have hd : Continuous d := hg.add (hwc.div_const 2)
  have hab (x : X) : a x < b x := by dsimp [a, b]; linarith [(hε x).1, (hβ x).1]
  have hbd (x : X) : b x < d x := by dsimp [b, d]; linarith [(hβ x).2.2, hw x]
  have hag (x : X) : a x < g x := by dsimp [a]; linarith [(hε x).1, hfg x]
  have hgd (x : X) : g x < d x := by dsimp [d]; linarith [hw x]
  let H := intervalStretchHomeomorph a b g d ha hb hg hd hab hbd hag hgd
  have habU (x : X) (t : ℝ) (ht : t ∈ Icc (a x) (b x)) : (x, t) ∈ U := by
    apply huU x t
    rw [abs_le]
    dsimp [a, b] at ht
    constructor <;> linarith [(hε x).2.1, (hβ x).2.1, ht.1, ht.2]
  have hadW (x : X) (t : ℝ) (ht : t ∈ Ioo (a x) (d x)) : (x, t) ∈ W := by
    by_cases htf : t < f x
    · apply hvW x t
      rw [abs_of_neg (sub_neg.mpr htf)]
      dsimp [a] at ht
      linarith [(hε x).2.2, ht.1]
    by_cases hgt : g x < t
    · apply hwW x t
      rw [abs_of_pos (sub_pos.mpr hgt)]
      dsimp [d] at ht
      linarith [hw x, ht.2]
    · exact hprism x t ⟨le_of_not_gt htf, le_of_not_gt hgt⟩
  refine ⟨H, fun _ => rfl, ?_, ?_, ?_⟩
  · intro p hp
    apply intervalStretchHomeomorph_apply_of_not_mem_Ioo
    intro ht
    exact hp (hadW p.1 p.2 ht)
  · intro x hx t
    have hbg : b x = g x := by
      dsimp [b, β]
      rw [← hx, sub_self, min_eq_right (hu x).le, zero_div, add_zero]
    apply Prod.ext
    · rfl
    · change intervalStretch (a x) (b x) (g x) (d x) t = t
      rw [hbg, intervalStretch_self]
  · intro x t ht
    refine ⟨H.symm (x, t), ?_, H.apply_symm_apply (x, t)⟩
    apply habU x
    exact intervalStretch_mem_left (hag x) (hgd x) (hab x)
      ⟨by dsimp [a]; linarith [(hε x).1, ht.1], ht.2⟩

theorem exists_closed_prism_engulfing {X : Type*} [MetricSpace X] {F : Set X}
    (hF : IsClosed F) {f g : F → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ x, f x ≤ g x) (hboundary : ∀ x : F, x.1 ∈ frontier F → f x = g x)
    {U W : Set (X × ℝ)} (hU : IsOpen U) (hW : IsOpen W)
    (hgraph : ∀ x : F, (x.1, f x) ∈ U)
    (hprism : ∀ (x : F) t, t ∈ Icc (f x) (g x) → (x.1, t) ∈ W) :
    ∃ H : (X × ℝ) ≃ₜ (X × ℝ),
      (∀ p, (H p).1 = p.1) ∧ (∀ p ∉ W, H p = p) ∧
      (∀ p, p.1 ∉ interior F → H p = p) ∧
      (∀ x : F, f x = g x → ∀ t, H (x.1, t) = (x.1, t)) ∧
      ∀ (x : F) t, t ∈ Icc (f x) (g x) → (x.1, t) ∈ H '' U := by
  let j : F × ℝ → X × ℝ := Prod.map Subtype.val id
  have hj : IsClosedEmbedding j := hF.isClosedEmbedding_subtypeVal.prodMap IsClosedEmbedding.id
  have hrange : range j = F ×ˢ (univ : Set ℝ) := by
    simp only [j, range_prodMap, Subtype.range_coe, range_id]
  obtain ⟨G, hGfst, hGfix, hGdeg, hGprism⟩ := exists_prism_engulfing hf hg hfg
    (hU.preimage hj.continuous) (hW.preimage hj.continuous) hgraph hprism
  obtain ⟨H, hHj, hHout⟩ := exists_homeomorph_extension_of_isClosedEmbedding hj G (by
    intro p hp
    rw [hrange, frontier_prod_univ_eq] at hp
    exact hGdeg p.1 (hboundary p.1 hp.1) p.2)
  have hHoutside (p : X × ℝ) (hp : p.1 ∉ interior F) : H p = p := by
    apply hHout
    rw [hrange, interior_prod_eq, interior_univ]
    exact fun h => hp h.1
  refine ⟨H, ?_, ?_, hHoutside, ?_, ?_⟩
  · intro p
    by_cases hp : p.1 ∈ F
    · let q : F × ℝ := (⟨p.1, hp⟩, p.2)
      have hpq : j q = p := rfl
      rw [← hpq, hHj]
      exact congrArg Subtype.val (hGfst q)
    · rw [hHoutside p (fun h => hp (interior_subset h))]
  · intro p hpW
    by_cases hp : p.1 ∈ F
    · let q : F × ℝ := (⟨p.1, hp⟩, p.2)
      have hpq : j q = p := rfl
      rw [← hpq, hHj, hGfix q hpW]
    · exact hHoutside p (fun h => hp (interior_subset h))
  · intro x hx t
    change H (j (x, t)) = j (x, t)
    rw [hHj, hGdeg x hx t]
  · intro x t ht
    obtain ⟨q, hq, hqt⟩ := hGprism x t ht
    exact ⟨j q, hq, by rw [hHj, hqt]; rfl⟩

theorem exists_prism_engulfing_near_closed_set {X : Type*} [MetricSpace X]
    {A O : Set X} (hA : IsClosed A) (hO : IsOpen O) (hAO : A ⊆ O)
    {f g : X → ℝ} (hf : Continuous f) (hg : Continuous g) (hfg : ∀ x, f x ≤ g x)
    {U W : Set (X × ℝ)} (hU : IsOpen U) (hW : IsOpen W)
    (hgraph : ∀ x ∈ O, (x, f x) ∈ U)
    (hprism : ∀ x ∈ O, ∀ t, t ∈ Icc (f x) (g x) → (x, t) ∈ W) :
    ∃ H : (X × ℝ) ≃ₜ (X × ℝ),
      (∀ p, (H p).1 = p.1) ∧ (∀ p ∉ W, H p = p) ∧
      (∀ p, p.1 ∉ O → H p = p) ∧
      (∀ x, f x = g x → ∀ t, H (x, t) = (x, t)) ∧
      ∀ x ∈ A, ∀ t, t ∈ Icc (f x) (g x) → (x, t) ∈ H '' U := by
  obtain ⟨χ, hχO, hχA, hχb⟩ := exists_closed_support_cutoff hA hO hAO
  let C := tsupport χ
  let g' : X → ℝ := fun x => f x + χ x * (g x - f x)
  have hg' : Continuous g' := hf.add (χ.continuous.mul (hg.sub hf))
  have hbounds (x : X) : f x ≤ g' x ∧ g' x ≤ g x := by
    have hmul := mul_le_mul_of_nonneg_right (hχb x).2 (sub_nonneg.mpr (hfg x))
    have hnonneg := mul_nonneg (hχb x).1 (sub_nonneg.mpr (hfg x))
    dsimp [g']
    constructor <;> nlinarith
  have hfrontier (x : C) (hx : x.1 ∈ frontier C) : f x.1 = g' x.1 := by
    have hχzero : χ x.1 = 0 := by
      by_contra hn
      have hinside : x.1 ∈ interior C :=
        interior_maximal (subset_tsupport χ) χ.continuous.isOpen_support hn
      exact hx.2 hinside
    simp only [g', hχzero, zero_mul, add_zero]
  obtain ⟨H, hHfst, hHfix, hHout, hHdeg, hHprism⟩ := exists_closed_prism_engulfing
    (isClosed_tsupport χ) (hf.comp continuous_subtype_val) (hg'.comp continuous_subtype_val)
    (fun x => (hbounds x.1).1) hfrontier hU hW
    (fun x => hgraph x.1 (hχO x.2)) (by
      intro x t ht
      exact hprism x.1 (hχO x.2) t ⟨ht.1, ht.2.trans (hbounds x.1).2⟩)
  refine ⟨H, hHfst, hHfix, ?_, ?_, ?_⟩
  · intro p hp
    apply hHout p
    exact fun h => hp (hχO (interior_subset h))
  · intro x hx t
    by_cases hxC : x ∈ C
    · apply hHdeg ⟨x, hxC⟩ _ t
      change f x = g' x
      simp only [g', hx, sub_self, mul_zero, add_zero]
    · exact hHout (x, t) (fun hi => hxC (interior_subset hi))
  · intro x hx t ht
    have hxC : x ∈ C := subset_tsupport χ (by rw [Function.mem_support, hχA x hx]; norm_num)
    apply hHprism ⟨x, hxC⟩ t
    change t ∈ Icc (f x) (g' x)
    simpa only [g', hχA x hx, one_mul, add_sub_cancel] using ht

theorem exists_engulfing_over_closed_set {X : Type*} [MetricSpace X] {A : Set X}
    (hA : IsClosed A) {f g : X → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ x, f x ≤ g x) {U W : Set (X × ℝ)} (hU : IsOpen U) (hW : IsOpen W)
    (hgraph : ∀ x ∈ A, (x, f x) ∈ U)
    (hprism : ∀ x ∈ A, ∀ t, t ∈ Icc (f x) (g x) → (x, t) ∈ W) :
    ∃ H : (X × ℝ) ≃ₜ (X × ℝ),
      (∀ p, (H p).1 = p.1) ∧ (∀ p ∉ W, H p = p) ∧
      (∀ x, f x = g x → ∀ t, H (x, t) = (x, t)) ∧
      ∀ x ∈ A, ∀ t, t ∈ Icc (f x) (g x) → (x, t) ∈ H '' U := by
  let O : Set X := {x | (x, f x) ∈ U} ∩ {x | ∀ t ∈ Icc (f x) (g x), (x, t) ∈ W}
  have hO : IsOpen O := (hU.preimage (continuous_id.prodMk hf)).inter
    (isOpen_prism_neighborhood hf hg hfg hW)
  obtain ⟨H, hHfst, hHfix, -, hHdeg, hHprism⟩ := exists_prism_engulfing_near_closed_set
    hA hO (fun x hx => ⟨hgraph x hx, hprism x hx⟩) hf hg hfg hU hW
    (fun _ hx => hx.1) (fun _ hx => hx.2)
  exact ⟨H, hHfst, hHfix, hHdeg, hHprism⟩

end DifferentialGeometry.Topology.Engulfing
