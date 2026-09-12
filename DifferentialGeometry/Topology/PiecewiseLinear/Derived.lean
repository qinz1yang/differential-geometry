import DifferentialGeometry.Topology.PiecewiseLinear.Subdivision

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

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

end Derived

end DifferentialGeometry.Topology.PiecewiseLinear
