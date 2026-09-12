import DifferentialGeometry.Topology.PiecewiseLinear.Subdivision

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem image_filter_mem_eq {α β : Type*} [DecidableEq β] {f : α → β} {d : Finset α}
    {g : Finset β} (hg : g ⊆ d.image f) : (d.filter fun a => f a ∈ g).image f = g := by
  ext p
  constructor
  · intro hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    exact (Finset.mem_filter.mp ha).2
  · intro hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (hg hp)
    exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hp⟩, rfl⟩

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def IsFlag (K : Geometry.SimplicialComplex ℝ E) (d : Finset (Finset E)) : Prop :=
  (∀ s ∈ d, s ∈ K.faces) ∧ ∀ s ∈ d, ∀ t ∈ d, s ⊆ t ∨ t ⊆ s

namespace IsFlag

variable {K : Geometry.SimplicialComplex ℝ E} {d : Finset (Finset E)}

theorem mem_faces (h : IsFlag K d) {s : Finset E} (hs : s ∈ d) : s ∈ K.faces := h.1 s hs

theorem subset_or_subset (h : IsFlag K d) {s t : Finset E} (hs : s ∈ d) (ht : t ∈ d) :
    s ⊆ t ∨ t ⊆ s :=
  h.2 s hs t ht

theorem mono (h : IsFlag K d) {d' : Finset (Finset E)} (hd' : d' ⊆ d) : IsFlag K d' :=
  ⟨fun s hs => h.1 s (hd' hs), fun s hs t ht => h.2 s (hd' hs) t (hd' ht)⟩

theorem coe_subset_faces (h : IsFlag K d) : (d : Set (Finset E)) ⊆ K.faces :=
  fun s hs => h.1 s (Finset.mem_coe.mp hs)

theorem exists_top (h : IsFlag K d) (hd : d.Nonempty) : ∃ u ∈ d, ∀ s ∈ d, s ⊆ u := by
  obtain ⟨u, hu, hmax⟩ := d.exists_max_image Finset.card hd
  refine ⟨u, hu, fun s hs => ?_⟩
  rcases h.subset_or_subset hs hu with hsu | hus
  · exact hsu
  · exact (Finset.eq_of_subset_of_card_le hus (hmax s hs)).ge

theorem exists_mem_top_notMem (h : IsFlag K d) {s₀ : Finset E} (hs₀ : s₀ ∈ d)
    (htop : ∀ s ∈ d, s ⊆ s₀) : ∃ v ∈ s₀, ∀ s ∈ d, s ≠ s₀ → v ∉ s := by
  classical
  by_cases hrest : (d.erase s₀).Nonempty
  · obtain ⟨s₁, hs₁, htop₁⟩ := (h.mono (Finset.erase_subset s₀ d)).exists_top hrest
    have hss : s₁ ⊂ s₀ := Finset.ssubset_iff_subset_ne.mpr
      ⟨htop s₁ (Finset.mem_of_mem_erase hs₁), Finset.ne_of_mem_erase hs₁⟩
    obtain ⟨v, hv, hvs₁⟩ := Finset.exists_of_ssubset hss
    exact ⟨v, hv, fun s hs hne hvs => hvs₁ (htop₁ s (Finset.mem_erase.mpr ⟨hne, hs⟩) hvs)⟩
  · rw [Finset.not_nonempty_iff_eq_empty] at hrest
    obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces (h.mem_faces hs₀)
    refine ⟨v, hv, fun s hs hne => ?_⟩
    have hmem : s ∈ d.erase s₀ := Finset.mem_erase.mpr ⟨hne, hs⟩
    rw [hrest] at hmem
    exact absurd hmem (Finset.notMem_empty s)

end IsFlag

section Derived

variable (K : Geometry.SimplicialComplex ℝ E) {c : Finset E → E}
  (hc : ∀ s ∈ K.faces, c s ∈ openSimplex s)

include hc

theorem injOn_faces_of_mem_openSimplex : Set.InjOn c K.faces := by
  intro s hs t ht h
  refine face_eq_of_mem_openSimplex K hs ht (hc s hs) ?_
  rw [h]
  exact hc t ht

theorem mem_convexHull_of_subset_of_mem_openSimplex {u s : Finset E} (hsu : s ⊆ u)
    (hs : s ∈ K.faces) : c s ∈ convexHull ℝ (u : Set E) :=
  convexHull_mono (Finset.coe_subset.mpr hsu) (openSimplex_subset_convexHull s (hc s hs))

theorem weights_pos_iff_of_mem_openSimplex {u s : Finset E} (hu : u ∈ K.faces) (hsu : s ⊆ u)
    (hs : s ∈ K.faces) {v : E} (hv : v ∈ u) : 0 < weights u (c s) v ↔ v ∈ s :=
  (mem_openSimplex_iff_weights_pos (K.indep hu) hsu
    (mem_convexHull_of_subset_of_mem_openSimplex K hc hsu hs)).mp (hc s hs) v hv

theorem IsFlag.injOn {d : Finset (Finset E)} (hd : IsFlag K d) :
    Set.InjOn c (d : Set (Finset E)) :=
  (injOn_faces_of_mem_openSimplex K hc).mono hd.coe_subset_faces

theorem mem_openSimplex_top [DecidableEq E] {d : Finset (Finset E)} (hd : IsFlag K d)
    {u : Finset E} (hu : u ∈ d) (htop : ∀ s ∈ d, s ⊆ u) {x : E}
    (hx : x ∈ openSimplex (d.image c)) : x ∈ openSimplex u := by
  obtain ⟨l, hl₀, hl₁, hlx⟩ := (mem_openSimplex_image_iff (hd.injOn K hc)).mp hx
  have huK := hd.mem_faces hu
  have hcs : ∀ s ∈ d, c s ∈ convexHull ℝ (u : Set E) := fun s hs =>
    mem_convexHull_of_subset_of_mem_openSimplex K hc (htop s hs) (hd.mem_faces hs)
  have hxu : x ∈ convexHull ℝ (u : Set E) := by
    rw [← hlx]
    exact (convex_convexHull ℝ _).sum_mem (fun s hs => (hl₀ s hs).le) hl₁ hcs
  rw [mem_openSimplex_self_iff (K.indep huK) hxu]
  intro v hv
  rw [← hlx, weights_sum_smul (K.indep huK) d hcs (fun s hs => (hl₀ s hs).le) hl₁ v hv]
  refine Finset.sum_pos' (fun s hs => mul_nonneg (hl₀ s hs).le (weights_nonneg (hcs s hs) hv))
    ⟨u, hu, mul_pos (hl₀ u hu) ?_⟩
  exact (weights_pos_iff_of_mem_openSimplex K hc huK (Finset.Subset.refl u) huK hv).mpr hv

theorem top_coeff_le {d d' : Finset (Finset E)} (hd : IsFlag K d)
    (hd' : IsFlag K d') {u : Finset E} (hu : u ∈ d) (htop : ∀ s ∈ d, s ⊆ u) (hu' : u ∈ d')
    (htop' : ∀ s ∈ d', s ⊆ u) {l l' : Finset E → ℝ} (hl₀ : ∀ s ∈ d, 0 < l s)
    (hl₁ : ∑ s ∈ d, l s = 1) (hl'₀ : ∀ s ∈ d', 0 < l' s) (hl'₁ : ∑ s ∈ d', l' s = 1)
    (heq : ∑ s ∈ d, l s • c s = ∑ s ∈ d', l' s • c s) : l' u ≤ l u := by
  classical
  have huK := hd.mem_faces hu
  have hcs : ∀ s ∈ d, c s ∈ convexHull ℝ (u : Set E) := fun s hs =>
    mem_convexHull_of_subset_of_mem_openSimplex K hc (htop s hs) (hd.mem_faces hs)
  have hcs' : ∀ s ∈ d', c s ∈ convexHull ℝ (u : Set E) := fun s hs =>
    mem_convexHull_of_subset_of_mem_openSimplex K hc (htop' s hs) (hd'.mem_faces hs)
  by_cases hrest : (d.erase u).Nonempty
  · obtain ⟨s₁, hs₁, htop₁⟩ := (hd.mono (Finset.erase_subset u d)).exists_top hrest
    have hs₁u : s₁ ⊂ u :=
      Finset.ssubset_iff_subset_ne.mpr ⟨htop s₁ (Finset.mem_of_mem_erase hs₁),
        Finset.ne_of_mem_erase hs₁⟩
    obtain ⟨v, hvu, hvs₁⟩ := Finset.exists_of_ssubset hs₁u
    have hw : weights u (∑ s ∈ d, l s • c s) v = weights u (∑ s ∈ d', l' s • c s) v := by
      rw [heq]
    rw [weights_sum_smul (K.indep huK) d hcs (fun s hs => (hl₀ s hs).le) hl₁ v hvu,
      weights_sum_smul (K.indep huK) d' hcs' (fun s hs => (hl'₀ s hs).le) hl'₁ v hvu] at hw
    have hleft : ∑ s ∈ d, l s * weights u (c s) v = l u * weights u (c u) v := by
      rw [← Finset.add_sum_erase d _ hu]
      have hzero : ∑ s ∈ d.erase u, l s * weights u (c s) v = 0 := by
        refine Finset.sum_eq_zero fun s hs => ?_
        have hvs : v ∉ s := fun hvs => hvs₁ (htop₁ s hs hvs)
        have h0 : weights u (c s) v = 0 :=
          le_antisymm (not_lt.mp (mt (weights_pos_iff_of_mem_openSimplex K hc huK
            (htop s (Finset.mem_of_mem_erase hs)) (hd.mem_faces (Finset.mem_of_mem_erase hs))
            hvu).mp hvs)) (weights_nonneg (hcs s (Finset.mem_of_mem_erase hs)) hvu)
        rw [h0, mul_zero]
      rw [hzero, add_zero]
    have hright : l' u * weights u (c u) v ≤ ∑ s ∈ d', l' s * weights u (c s) v :=
      Finset.single_le_sum (fun s hs => mul_nonneg (hl'₀ s hs).le (weights_nonneg (hcs' s hs) hvu))
        hu'
    have hpos : 0 < weights u (c u) v :=
      (weights_pos_iff_of_mem_openSimplex K hc huK (Finset.Subset.refl u) huK hvu).mpr hvu
    rw [hleft] at hw
    exact le_of_mul_le_mul_right (hw ▸ hright) hpos
  · rw [Finset.not_nonempty_iff_eq_empty] at hrest
    have hd1 : d = {u} := by
      ext s
      constructor
      · intro hs
        by_contra hne
        have : s ∈ d.erase u := Finset.mem_erase.mpr ⟨fun h => hne (h ▸ Finset.mem_singleton_self u), hs⟩
        rw [hrest] at this
        exact absurd this (Finset.notMem_empty s)
      · intro hs
        rw [Finset.mem_singleton] at hs
        exact hs ▸ hu
    have hlu : l u = 1 := by
      rw [hd1, Finset.sum_singleton] at hl₁
      exact hl₁
    rw [hlu]
    calc l' u ≤ ∑ s ∈ d', l' s := Finset.single_le_sum (fun s hs => (hl'₀ s hs).le) hu'
      _ = 1 := hl'₁

theorem eq_of_mem_openSimplex_image_aux [DecidableEq E] :
    ∀ (n : ℕ) {d d' : Finset (Finset E)}, d.card ≤ n → IsFlag K d → IsFlag K d' →
      d.Nonempty → d'.Nonempty → ∀ {x : E}, x ∈ openSimplex (d.image c) →
        x ∈ openSimplex (d'.image c) → d = d' := by
  intro n
  induction n with
  | zero =>
    intro d d' hcard _ _ hne _ _ _ _
    exact absurd (Finset.card_pos.mpr hne) (by omega)
  | succ n ih =>
    intro d d' hcard hd hd' hne hne' x hx hx'
    obtain ⟨u, hu, htop⟩ := hd.exists_top hne
    obtain ⟨u', hu', htop'⟩ := hd'.exists_top hne'
    have huu' : u = u' := face_eq_of_mem_openSimplex K (hd.mem_faces hu) (hd'.mem_faces hu')
      (mem_openSimplex_top K hc hd hu htop hx) (mem_openSimplex_top K hc hd' hu' htop' hx')
    subst huu'
    obtain ⟨l, hl₀, hl₁, hlx⟩ := (mem_openSimplex_image_iff (hd.injOn K hc)).mp hx
    obtain ⟨l', hl'₀, hl'₁, hl'x⟩ := (mem_openSimplex_image_iff (hd'.injOn K hc)).mp hx'
    have heq : ∑ s ∈ d, l s • c s = ∑ s ∈ d', l' s • c s := hlx.trans hl'x.symm
    have hlu : l u = l' u :=
      le_antisymm (top_coeff_le K hc hd' hd hu' htop' hu htop hl'₀ hl'₁ hl₀ hl₁ heq.symm)
        (top_coeff_le K hc hd hd' hu htop hu' htop' hl₀ hl₁ hl'₀ hl'₁ heq)
    have hrest : ∀ {e : Finset (Finset E)} {m : Finset E → ℝ}, u ∈ e → (∀ s ∈ e, 0 < m s) →
        ∑ s ∈ e, m s = 1 → m u < 1 → (e.erase u).Nonempty := by
      intro e m hue hm₀ hm₁ hmu
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      have h1 : ∑ s ∈ e, m s = m u := by
        rw [← Finset.add_sum_erase e _ hue, hemp, Finset.sum_empty, add_zero]
      rw [hm₁] at h1
      exact absurd h1.symm hmu.ne
    by_cases hlu1 : l u = 1
    · have hsingle : ∀ {e : Finset (Finset E)} {m : Finset E → ℝ}, IsFlag K e → u ∈ e →
          (∀ s ∈ e, 0 < m s) → ∑ s ∈ e, m s = 1 → m u = 1 → e = {u} := by
        intro e m _ hue hm₀ hm₁ hmu
        have hzero : ∑ s ∈ e.erase u, m s = 0 := by
          have := Finset.add_sum_erase e m hue
          rw [hm₁, hmu] at this
          linarith
        have hemp : e.erase u = ∅ := by
          by_contra hne
          have hpos : 0 < ∑ s ∈ e.erase u, m s :=
            Finset.sum_pos (fun s hs => hm₀ s (Finset.mem_of_mem_erase hs))
              (Finset.nonempty_iff_ne_empty.mpr hne)
          exact absurd hzero hpos.ne'
        ext s
        rw [Finset.mem_singleton]
        constructor
        · intro hs
          by_contra hne
          have : s ∈ e.erase u := Finset.mem_erase.mpr ⟨hne, hs⟩
          rw [hemp] at this
          exact absurd this (Finset.notMem_empty s)
        · intro hs
          exact hs ▸ hue
      rw [hsingle hd hu hl₀ hl₁ hlu1, hsingle hd' hu' hl'₀ hl'₁ (hlu ▸ hlu1)]
    · have hlt : l u < 1 :=
        lt_of_le_of_ne (hl₁ ▸ Finset.single_le_sum (fun s hs => (hl₀ s hs).le) hu) hlu1
      have hne₁ := hrest hu hl₀ hl₁ hlt
      have hne₁' := hrest hu' hl'₀ hl'₁ (hlu ▸ hlt)
      have hremainder : ∀ {e : Finset (Finset E)} {m : Finset E → ℝ}, IsFlag K e → u ∈ e →
          (∀ s ∈ e, 0 < m s) → ∑ s ∈ e, m s = 1 → ∑ s ∈ e, m s • c s = x → m u < 1 →
          (1 - m u)⁻¹ • (x - m u • c u) ∈ openSimplex ((e.erase u).image c) := by
        intro e m he hue hm₀ hm₁ hmx hmu
        rw [mem_openSimplex_image_iff ((he.mono (Finset.erase_subset u e)).injOn K hc)]
        have hne0 : 1 - m u ≠ 0 := (sub_pos.mpr hmu).ne'
        refine ⟨fun s => m s / (1 - m u),
          fun s hs => div_pos (hm₀ s (Finset.mem_of_mem_erase hs)) (sub_pos.mpr hmu), ?_, ?_⟩
        · simp_rw [div_eq_mul_inv]
          rw [← Finset.sum_mul, Finset.sum_erase_eq_sub hue, hm₁, mul_inv_cancel₀ hne0]
        · simp_rw [div_eq_inv_mul, mul_smul]
          rw [← Finset.smul_sum, Finset.sum_erase_eq_sub hue, hmx]
      have hyd := hremainder hd hu hl₀ hl₁ hlx hlt
      have hyd' := hremainder hd' hu' hl'₀ hl'₁ hl'x (hlu ▸ hlt)
      rw [hlu] at hyd
      have hcard' : (d.erase u).card ≤ n := by
        rw [Finset.card_erase_of_mem hu]
        omega
      have := ih hcard' (hd.mono (Finset.erase_subset u d)) (hd'.mono (Finset.erase_subset u d'))
        hne₁ hne₁' hyd hyd'
      rw [← Finset.insert_erase hu, ← Finset.insert_erase hu', this]

theorem eq_of_mem_openSimplex_image [DecidableEq E] {d d' : Finset (Finset E)} (hd : IsFlag K d)
    (hd' : IsFlag K d') (hne : d.Nonempty) (hne' : d'.Nonempty) {x : E}
    (hx : x ∈ openSimplex (d.image c)) (hx' : x ∈ openSimplex (d'.image c)) : d = d' :=
  eq_of_mem_openSimplex_image_aux K hc d.card le_rfl hd hd' hne hne' hx hx'

theorem weights_eq_zero_of_notMem {u s : Finset E} (hu : u ∈ K.faces) (hsu : s ⊆ u)
    (hs : s ∈ K.faces) {v : E} (hv : v ∈ u) (hvs : v ∉ s) : weights u (c s) v = 0 :=
  le_antisymm (not_lt.mp (mt (weights_pos_iff_of_mem_openSimplex K hc hu hsu hs hv).mp hvs))
    (weights_nonneg (mem_convexHull_of_subset_of_mem_openSimplex K hc hsu hs) hv)

theorem eq_zero_of_sum_smul_eq_zero {d : Finset (Finset E)} (hd : IsFlag K d) (hne : d.Nonempty)
    {m : Finset E → ℝ} (hm₀ : ∑ s ∈ d, m s = 0) (hmx : ∑ s ∈ d, m s • c s = 0) :
    ∀ s ∈ d, m s = 0 := by
  classical
  obtain ⟨u, hu, htop⟩ := hd.exists_top hne
  have huK := hd.mem_faces hu
  have hcs : ∀ s ∈ d, c s ∈ convexHull ℝ (u : Set E) := fun s hs =>
    mem_convexHull_of_subset_of_mem_openSimplex K hc (htop s hs) (hd.mem_faces hs)
  let a : Finset E → ℝ := fun s => max (m s) 0
  let b : Finset E → ℝ := fun s => max (-m s) 0
  have hab : ∀ s, a s - b s = m s := fun s => max_zero_sub_max_neg_zero_eq_self (m s)
  have ha₀ : ∀ s, 0 ≤ a s := fun s => le_max_right _ _
  have hb₀ : ∀ s, 0 ≤ b s := fun s => le_max_right _ _
  have hsum : ∑ s ∈ d, a s = ∑ s ∈ d, b s := by
    have h := hm₀
    simp_rw [← hab, Finset.sum_sub_distrib] at h
    exact sub_eq_zero.mp h
  have hsmul : ∑ s ∈ d, a s • c s = ∑ s ∈ d, b s • c s := by
    have h := hmx
    simp_rw [← hab, sub_smul, Finset.sum_sub_distrib] at h
    exact sub_eq_zero.mp h
  by_cases hW : ∑ s ∈ d, a s = 0
  · have ha : ∀ s ∈ d, a s = 0 := (Finset.sum_eq_zero_iff_of_nonneg fun s _ => ha₀ s).mp hW
    have hb : ∀ s ∈ d, b s = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun s _ => hb₀ s).mp (hsum ▸ hW)
    intro s hs
    rw [← hab s, ha s hs, hb s hs, sub_zero]
  · have hWpos : 0 < ∑ s ∈ d, a s :=
      lt_of_le_of_ne (Finset.sum_nonneg fun s _ => ha₀ s) (Ne.symm hW)
    set W := ∑ s ∈ d, a s with hWdef
    have hla : ∀ s ∈ d, 0 ≤ a s / W := fun s _ => div_nonneg (ha₀ s) hWpos.le
    have hlb : ∀ s ∈ d, 0 ≤ b s / W := fun s _ => div_nonneg (hb₀ s) hWpos.le
    have hla₁ : ∑ s ∈ d, a s / W = 1 := by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul, mul_inv_cancel₀ hWpos.ne']
    have hlb₁ : ∑ s ∈ d, b s / W = 1 := by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul, ← hsum, mul_inv_cancel₀ hWpos.ne']
    have hpts : ∑ s ∈ d, (a s / W) • c s = ∑ s ∈ d, (b s / W) • c s := by
      simp_rw [div_eq_inv_mul, mul_smul, ← Finset.smul_sum]
      rw [hsmul]
    have hweights : ∀ v ∈ u, ∑ s ∈ d, a s / W * weights u (c s) v =
        ∑ s ∈ d, b s / W * weights u (c s) v := by
      intro v hv
      rw [← weights_sum_smul (K.indep huK) d hcs hla hla₁ v hv,
        ← weights_sum_smul (K.indep huK) d hcs hlb hlb₁ v hv, hpts]
    set S := d.filter fun s => m s ≠ 0 with hSdef
    have hSflag : IsFlag K S := hd.mono (Finset.filter_subset _ _)
    have hSne : S.Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hemp
      apply hW
      exact Finset.sum_eq_zero fun s hs => by
        have : m s = 0 := not_not.mp (hemp hs)
        simp [a, this]
    obtain ⟨s₀, hs₀, htop₀⟩ := hSflag.exists_top hSne
    obtain ⟨v, hv, hvs⟩ := hSflag.exists_mem_top_notMem hs₀ htop₀
    have hs₀d : s₀ ∈ d := Finset.mem_of_mem_filter s₀ hs₀
    have hvu : v ∈ u := htop s₀ hs₀d hv
    have hsingle : ∀ f : Finset E → ℝ, (∀ s ∈ d, m s = 0 → f s = 0) →
        ∑ s ∈ d, f s * weights u (c s) v = f s₀ * weights u (c s₀) v := by
      intro f hf
      refine Finset.sum_eq_single s₀ (fun s hs hne => ?_) fun h => absurd hs₀d h
      by_cases hms : m s = 0
      · rw [hf s hs hms, zero_mul]
      · have hsS : s ∈ S := Finset.mem_filter.mpr ⟨hs, hms⟩
        rw [weights_eq_zero_of_notMem K hc huK (htop s hs) (hd.mem_faces hs) hvu
          (hvs s hsS hne), mul_zero]
    have hkey := hweights v hvu
    rw [hsingle (fun s => a s / W) fun s _ hms => by simp [a, hms],
      hsingle (fun s => b s / W) fun s _ hms => by simp [b, hms]] at hkey
    have hpos : 0 < weights u (c s₀) v :=
      (weights_pos_iff_of_mem_openSimplex K hc huK (htop s₀ hs₀d) (hd.mem_faces hs₀d) hvu).mpr hv
    have hab₀ : a s₀ / W = b s₀ / W := mul_right_cancel₀ hpos.ne' hkey
    have hms₀ : m s₀ = 0 := by
      rw [← hab s₀, sub_eq_zero]
      exact (div_left_inj' hWpos.ne').mp hab₀
    exact absurd hms₀ (Finset.mem_filter.mp hs₀).2

theorem affineIndependent_image [DecidableEq E] {d : Finset (Finset E)} (hd : IsFlag K d)
    (hne : d.Nonempty) : AffineIndependent ℝ ((↑) : ((d.image c : Finset E) : Set E) → E) := by
  have hind : AffineIndependent ℝ fun s : d => c s := by
    rw [affineIndependent_iff_of_fintype]
    intro w hw hvs
    rw [Finset.weightedVSub_eq_linear_combination _ hw] at hvs
    let m : Finset E → ℝ := fun s => if h : s ∈ d then w ⟨s, h⟩ else 0
    have hm : ∀ i : d, m i = w i := fun i => by simp [m, i.2]
    have hm₀ : ∑ s ∈ d, m s = 0 := by
      rw [← Finset.sum_coe_sort d m]
      simp_rw [hm]
      exact hw
    have hmx : ∑ s ∈ d, m s • c s = 0 := by
      rw [← Finset.sum_coe_sort d (fun s => m s • c s)]
      simp_rw [hm]
      exact hvs
    intro i
    rw [← hm i]
    exact eq_zero_of_sum_smul_eq_zero K hc hd hne hm₀ hmx i i.2
  have hrange : Set.range (fun s : d => c s) = ((d.image c : Finset E) : Set E) := by
    ext y
    simp [Finset.coe_image]
  have h := hind.range
  rwa [hrange] at h

noncomputable def derived [DecidableEq E] : Geometry.SimplicialComplex ℝ E where
  faces := {f | ∃ d : Finset (Finset E), IsFlag K d ∧ d.Nonempty ∧ f = d.image c}
  isRelLowerSet_faces := by
    rintro f ⟨d, hd, hne, rfl⟩
    refine ⟨hne.image c, fun g hgf hg => ?_⟩
    refine ⟨d.filter fun s => c s ∈ g, hd.mono (Finset.filter_subset _ _), ?_,
      (image_filter_mem_eq hgf).symm⟩
    obtain ⟨p, hp⟩ := hg
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp (hgf hp)
    exact ⟨s, Finset.mem_filter.mpr ⟨hs, hp⟩⟩
  indep := by
    rintro f ⟨d, hd, hne, rfl⟩
    exact affineIndependent_image K hc hd hne
  inter_subset_convexHull := by
    rintro f g ⟨d, hd, hne, rfl⟩ ⟨d', hd', hne', rfl⟩ x ⟨hxf, hxg⟩
    obtain ⟨T, hTf, hTne, hxT⟩ := exists_openSimplex_of_mem_convexHull hxf
    obtain ⟨T', hTg, hTne', hxT'⟩ := exists_openSimplex_of_mem_convexHull hxg
    rw [← image_filter_mem_eq hTf] at hxT
    rw [← image_filter_mem_eq hTg] at hxT'
    have heT : (d.filter fun s => c s ∈ T).Nonempty := by
      obtain ⟨p, hp⟩ := hTne
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp (hTf hp)
      exact ⟨s, Finset.mem_filter.mpr ⟨hs, hp⟩⟩
    have heT' : (d'.filter fun s => c s ∈ T').Nonempty := by
      obtain ⟨p, hp⟩ := hTne'
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp (hTg hp)
      exact ⟨s, Finset.mem_filter.mpr ⟨hs, hp⟩⟩
    have heq := eq_of_mem_openSimplex_image K hc (hd.mono (Finset.filter_subset _ _))
      (hd'.mono (Finset.filter_subset _ _)) heT heT' hxT hxT'
    refine convexHull_mono ?_ (openSimplex_subset_convexHull _ hxT)
    intro p hp
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hp)
    refine ⟨Finset.mem_coe.mpr (Finset.mem_image_of_mem c (Finset.mem_of_mem_filter s hs)), ?_⟩
    rw [heq] at hs
    exact Finset.mem_coe.mpr (Finset.mem_image_of_mem c (Finset.mem_of_mem_filter s hs))

theorem mem_derived_faces_iff [DecidableEq E] {f : Finset E} :
    f ∈ (derived K hc).faces ↔ ∃ d : Finset (Finset E), IsFlag K d ∧ d.Nonempty ∧ f = d.image c :=
  Iff.rfl

theorem exists_flag_of_mem_openSimplex_aux [DecidableEq E] :
    ∀ (n : ℕ) {u : Finset E}, u.card ≤ n → u ∈ K.faces → ∀ {x : E}, x ∈ openSimplex u →
      ∃ d : Finset (Finset E), IsFlag K d ∧ d.Nonempty ∧ (∀ s ∈ d, s ⊆ u) ∧
        x ∈ convexHull ℝ ((d.image c : Finset E) : Set E) := by
  intro n
  induction n with
  | zero =>
    intro u hcard hu x _
    exact absurd (Finset.card_pos.mpr (K.nonempty_of_mem_faces hu)) (by omega)
  | succ n ih =>
    intro u hcard hu x hx
    have hindep := K.indep hu
    have hxu : x ∈ convexHull ℝ (u : Set E) := openSimplex_subset_convexHull u hx
    have hcu : c u ∈ convexHull ℝ (u : Set E) := openSimplex_subset_convexHull u (hc u hu)
    have hw : ∀ v ∈ u, 0 < weights u x v := (mem_openSimplex_self_iff hindep hxu).mp hx
    have hμ : ∀ v ∈ u, 0 < weights u (c u) v := (mem_openSimplex_self_iff hindep hcu).mp (hc u hu)
    obtain ⟨v₀, hv₀, hmin⟩ :=
      u.exists_min_image (fun v => weights u x v / weights u (c u) v) (K.nonempty_of_mem_faces hu)
    set r := weights u x v₀ / weights u (c u) v₀ with hrdef
    have hrpos : 0 < r := div_pos (hw v₀ hv₀) (hμ v₀ hv₀)
    have hrle : ∀ v ∈ u, r * weights u (c u) v ≤ weights u x v := fun v hv =>
      (le_div_iff₀ (hμ v hv)).mp (hmin v hv)
    have hr1 : r ≤ 1 := by
      have h1 : ∑ v ∈ u, r * weights u (c u) v ≤ ∑ v ∈ u, weights u x v :=
        Finset.sum_le_sum hrle
      rw [← Finset.mul_sum, sum_weights hcu, sum_weights hxu, mul_one] at h1
      exact h1
    by_cases hr : r = 1
    · have hle : ∀ v ∈ u, weights u (c u) v ≤ weights u x v := fun v hv => by
        simpa [hr] using hrle v hv
      have hwμ : ∀ v ∈ u, weights u (c u) v = weights u x v :=
        (Finset.sum_eq_sum_iff_of_le hle).mp (by rw [sum_weights hcu, sum_weights hxu])
      have hxc : x = c u := by
        rw [← sum_weights_smul hxu, ← sum_weights_smul hcu]
        exact Finset.sum_congr rfl fun v hv => by rw [hwμ v hv]
      refine ⟨{u}, ⟨fun s hs => ?_, fun s hs t ht => ?_⟩, Finset.singleton_nonempty u,
        fun s hs => ?_, ?_⟩
      · rw [Finset.mem_singleton] at hs
        exact hs ▸ hu
      · rw [Finset.mem_singleton] at hs ht
        exact Or.inl (hs ▸ ht ▸ Finset.Subset.refl u)
      · rw [Finset.mem_singleton] at hs
        exact hs ▸ Finset.Subset.refl u
      · rw [Finset.image_singleton, Finset.coe_singleton, hxc]
        exact subset_convexHull ℝ _ (mem_singleton _)
    · have hrlt : r < 1 := lt_of_le_of_ne hr1 hr
      have h1r : 0 < 1 - r := sub_pos.mpr hrlt
      let w' : E → ℝ := fun v => (weights u x v - r * weights u (c u) v) / (1 - r)
      have hw'₀ : ∀ v ∈ u, 0 ≤ w' v := fun v hv =>
        div_nonneg (sub_nonneg.mpr (hrle v hv)) h1r.le
      have hw'₁ : ∑ v ∈ u, w' v = 1 := by
        simp only [w']
        simp_rw [div_eq_mul_inv]
        rw [← Finset.sum_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_weights hxu,
          sum_weights hcu, mul_one, mul_inv_cancel₀ h1r.ne']
      set y := ∑ v ∈ u, w' v • v with hydef
      have hy : y ∈ convexHull ℝ (u : Set E) :=
        mem_convexHull_iff_exists_weights.mpr ⟨w', hw'₀, hw'₁, rfl⟩
      have hwy : ∀ v ∈ u, weights u y v = w' v := weights_eq hindep hy hw'₁ rfl
      have hw'v₀ : w' v₀ = 0 := by
        simp only [w', hrdef]
        rw [div_mul_cancel₀ _ (hμ v₀ hv₀).ne', sub_self, zero_div]
      obtain ⟨t, htu, htne, hyt⟩ := exists_openSimplex_of_mem_convexHull hy
      have htne' : t ≠ u := by
        intro htu'
        subst htu'
        have := (mem_openSimplex_self_iff hindep hy).mp hyt v₀ hv₀
        rw [hwy v₀ hv₀, hw'v₀] at this
        exact lt_irrefl _ this
      have htss : t ⊂ u := Finset.ssubset_iff_subset_ne.mpr ⟨htu, htne'⟩
      have htK : t ∈ K.faces := K.down_closed hu htu htne
      have hcard' : t.card ≤ n := by
        have := Finset.card_lt_card htss
        omega
      obtain ⟨d₁, hd₁, hne₁, htop₁, hyd₁⟩ := ih hcard' htK hyt
      refine ⟨insert u d₁, ⟨fun s hs => ?_, fun s hs t' ht' => ?_⟩,
        Finset.insert_nonempty u d₁, fun s hs => ?_, ?_⟩
      · rcases Finset.mem_insert.mp hs with hsu | hs
        · rw [hsu]
          exact hu
        · exact hd₁.mem_faces hs
      · rcases Finset.mem_insert.mp hs with hsu | hs <;>
          rcases Finset.mem_insert.mp ht' with htu' | ht'
        · rw [hsu, htu']
          exact Or.inl (Finset.Subset.refl _)
        · rw [hsu]
          exact Or.inr ((htop₁ t' ht').trans htu)
        · rw [htu']
          exact Or.inl ((htop₁ s hs).trans htu)
        · exact hd₁.subset_or_subset hs ht'
      · rcases Finset.mem_insert.mp hs with hsu | hs
        · rw [hsu]
        · exact (htop₁ s hs).trans htu
      · have hx' : x = r • c u + (1 - r) • y := by
          rw [hydef, ← sum_weights_smul hxu, ← sum_weights_smul hcu]
          simp_rw [Finset.smul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [smul_smul, smul_smul, ← add_smul]
          congr 1
          simp only [w']
          field_simp
          ring
        rw [hx']
        refine (convex_convexHull ℝ _) ?_ ?_ hrpos.le h1r.le (by ring)
        · exact subset_convexHull ℝ _ (Finset.mem_coe.mpr
            (Finset.mem_image_of_mem c (Finset.mem_insert_self u d₁)))
        · exact convexHull_mono (Finset.coe_subset.mpr
            (Finset.image_subset_image (Finset.subset_insert u d₁))) hyd₁

theorem exists_flag_of_mem_openSimplex [DecidableEq E] {u : Finset E} (hu : u ∈ K.faces) {x : E}
    (hx : x ∈ openSimplex u) :
    ∃ d : Finset (Finset E), IsFlag K d ∧ d.Nonempty ∧ (∀ s ∈ d, s ⊆ u) ∧
      x ∈ convexHull ℝ ((d.image c : Finset E) : Set E) :=
  exists_flag_of_mem_openSimplex_aux K hc u.card le_rfl hu hx

theorem convexHull_image_subset [DecidableEq E] {d : Finset (Finset E)} (hd : IsFlag K d)
    {u : Finset E} (htop : ∀ s ∈ d, s ⊆ u) :
    convexHull ℝ ((d.image c : Finset E) : Set E) ⊆ convexHull ℝ (u : Set E) := by
  refine convexHull_min (fun p hp => ?_) (convex_convexHull ℝ _)
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hp)
  exact mem_convexHull_of_subset_of_mem_openSimplex K hc (htop s hs) (hd.mem_faces hs)

theorem derived_isSubdivision [DecidableEq E] : IsSubdivision (derived K hc) K := by
  refine ⟨Subset.antisymm ?_ ?_, ?_⟩
  · intro x hx
    obtain ⟨f, ⟨d, hd, hne, rfl⟩, hxf⟩ := (derived K hc).mem_space_iff.mp hx
    obtain ⟨u, hu, htop⟩ := hd.exists_top hne
    exact K.convexHull_subset_space (hd.mem_faces hu) (convexHull_image_subset K hc hd htop hxf)
  · intro x hx
    obtain ⟨u, hu, hxu⟩ := exists_face_mem_openSimplex K hx
    obtain ⟨d, hd, hne, -, hxd⟩ := exists_flag_of_mem_openSimplex K hc hu hxu
    exact (derived K hc).convexHull_subset_space ⟨d, hd, hne, rfl⟩ hxd
  · rintro f ⟨d, hd, hne, rfl⟩
    obtain ⟨u, hu, htop⟩ := hd.exists_top hne
    exact ⟨u, hd.mem_faces hu, convexHull_image_subset K hc hd htop⟩

end Derived

theorem centroid_mem_openSimplex {s : Finset E} (hs : s.Nonempty) :
    s.centroid ℝ id ∈ openSimplex s := by
  have hcard : (0 : ℝ) < s.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hs)
  refine ⟨fun _ => (s.card : ℝ)⁻¹, fun v _ => inv_pos.mpr hcard, ?_, ?_⟩
  · rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hcard.ne']
  · rw [Finset.centroid_def, Finset.affineCombination_eq_linear_combination _ _ _
      (Finset.sum_centroidWeights_eq_one_of_nonempty ℝ _ hs)]
    exact Finset.sum_congr rfl fun v _ => by rw [Finset.centroidWeights_apply]; rfl

theorem centroid_mem_openSimplex_of_mem_faces (K : Geometry.SimplicialComplex ℝ E) :
    ∀ s ∈ K.faces, s.centroid ℝ id ∈ openSimplex s :=
  fun _ hs => centroid_mem_openSimplex (K.nonempty_of_mem_faces hs)

noncomputable def barycentricSubdivision [DecidableEq E] (K : Geometry.SimplicialComplex ℝ E) :
    Geometry.SimplicialComplex ℝ E :=
  derived K (centroid_mem_openSimplex_of_mem_faces K)

theorem barycentricSubdivision_isSubdivision [DecidableEq E] (K : Geometry.SimplicialComplex ℝ E) :
    IsSubdivision (barycentricSubdivision K) K :=
  derived_isSubdivision K (centroid_mem_openSimplex_of_mem_faces K)

end DifferentialGeometry.Topology.PiecewiseLinear
