import DifferentialGeometry.Topology.PiecewiseLinear.Derived
import DifferentialGeometry.Topology.PiecewiseLinear.ConeBase

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section RelFace

variable (K L L' : Geometry.SimplicialComplex ℝ E) (c : Finset E → E)

structure IsRelFace (τ : Finset E) (d : Finset (Finset E)) : Prop where
  base : τ = ∅ ∨ τ ∈ L'.faces
  flag : IsFlag K d
  notMem : ∀ s ∈ d, s ∉ L.faces
  subset : ∀ s ∈ d, (τ : Set E) ⊆ convexHull ℝ (s : Set E)
  nonempty : τ.Nonempty ∨ d.Nonempty

variable {K L L' c}

theorem IsRelFace.mono {τ : Finset E} {d : Finset (Finset E)} (h : IsRelFace K L L' τ d)
    {τ' : Finset E} {d' : Finset (Finset E)} (hτ' : τ' ⊆ τ) (hd' : d' ⊆ d)
    (hne : τ'.Nonempty ∨ d'.Nonempty) : IsRelFace K L L' τ' d' where
  base := by
    rcases τ'.eq_empty_or_nonempty with h0 | h0
    · exact Or.inl h0
    · rcases h.base with hτ | hτ
      · exact absurd (hτ' h0.choose_spec) (by simp [hτ])
      · exact Or.inr (L'.down_closed hτ hτ' h0)
  flag := h.flag.mono hd'
  notMem := fun s hs => h.notMem s (hd' hs)
  subset := fun s hs => (Finset.coe_subset.mpr hτ').trans (h.subset s (hd' hs))
  nonempty := hne

theorem IsRelFace.subset_faces {τ : Finset E} {d : Finset (Finset E)}
    (h : IsRelFace K L L' τ d) : ∀ s ∈ d, s ∈ K.faces := fun _ hs => h.flag.mem_faces hs

theorem IsRelFace.convexHull_subset_of_mem {τ : Finset E} {d : Finset (Finset E)}
    (h : IsRelFace K L L' τ d) {s : Finset E} (hs : s ∈ d) :
    convexHull ℝ (τ : Set E) ⊆ convexHull ℝ (s : Set E) :=
  convexHull_min (h.subset s hs) (convex_convexHull ℝ _)

variable (hL : L.faces ⊆ K.faces) (hL' : IsSubdivision L' L)
  (hc : ∀ s ∈ K.faces, c s ∈ openSimplex s)

include hL

theorem notMem_space_of_notMem_faces {s : Finset E} (hs : s ∈ K.faces) (hsL : s ∉ L.faces) {x : E}
    (hx : x ∈ openSimplex s) : x ∉ L.space := by
  intro hxL
  obtain ⟨t, ht, hxt⟩ := L.mem_space_iff.mp hxL
  exact hsL (L.down_closed ht (face_subset_of_mem_openSimplex_of_mem_convexHull K hs (hL ht) hx hxt)
    (K.nonempty_of_mem_faces hs))

include hc

theorem c_notMem_space {s : Finset E} (hs : s ∈ K.faces) (hsL : s ∉ L.faces) : c s ∉ L.space :=
  notMem_space_of_notMem_faces hL hs hsL (hc s hs)

include hL'

variable [DecidableEq E]

theorem IsRelFace.disjoint {τ : Finset E} {d : Finset (Finset E)} (h : IsRelFace K L L' τ d) :
    Disjoint τ (d.image c) := by
  rw [Finset.disjoint_left]
  intro v hvτ hvd
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hvd
  have hτ : τ ∈ L'.faces := by
    rcases h.base with h0 | h0
    · exact absurd (h0 ▸ hvτ) (Finset.notMem_empty _)
    · exact h0
  have hvL : c s ∈ L.space := hL'.space_eq ▸
    L'.convexHull_subset_space hτ (subset_convexHull ℝ _ (Finset.mem_coe.mpr hvτ))
  exact c_notMem_space hL hc (h.subset_faces s hs) (h.notMem s hs) hvL

theorem IsRelFace.exists_vertex_avoiding {τ : Finset E} {d : Finset (Finset E)}
    (h : IsRelFace K L L' τ d) {u : Finset E} (hu : u ∈ d) (htop : ∀ s ∈ d, s ⊆ u) :
    ∃ v ∈ u, (∀ w ∈ τ, weights u w v = 0) ∧ ∀ s ∈ d.erase u, weights u (c s) v = 0 := by
  classical
  have huK : u ∈ K.faces := h.subset_faces u hu
  by_cases hrest : (d.erase u).Nonempty
  · obtain ⟨u', hu', htop'⟩ := (h.flag.mono (Finset.erase_subset u d)).exists_top hrest
    have hu'u : u' ⊂ u := Finset.ssubset_iff_subset_ne.mpr
      ⟨htop u' (Finset.mem_of_mem_erase hu'), Finset.ne_of_mem_erase hu'⟩
    obtain ⟨v, hvu, hvu'⟩ := Finset.exists_of_ssubset hu'u
    refine ⟨v, hvu, fun w hw => ?_, fun s hs => ?_⟩
    · exact weights_eq_zero_of_subset_of_notMem (K.indep huK) hu'u.subset
        (h.subset u' (Finset.mem_of_mem_erase hu') (Finset.mem_coe.mpr hw)) hvu hvu'
    · exact weights_eq_zero_of_subset_of_notMem (K.indep huK) hu'u.subset
        (convexHull_mono (Finset.coe_subset.mpr (htop' s hs))
          (openSimplex_subset_convexHull _ (hc s (h.subset_faces s (Finset.mem_of_mem_erase hs)))))
        hvu hvu'
  · rw [Finset.not_nonempty_iff_eq_empty] at hrest
    rcases τ.eq_empty_or_nonempty with hτ | hτ
    · obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces huK
      refine ⟨v, hv, fun w hw => absurd (hτ ▸ hw) (Finset.notMem_empty w), fun s hs => ?_⟩
      rw [hrest] at hs
      exact absurd hs (Finset.notMem_empty s)
    · have hτ' : τ ∈ L'.faces := by
        rcases h.base with h0 | h0
        · exact absurd hτ (by rw [h0]; exact Finset.not_nonempty_empty)
        · exact h0
      obtain ⟨t, ht, hτt⟩ := hL'.exists_face_subset hτ'
      have hτu : convexHull ℝ (τ : Set E) ⊆ convexHull ℝ ((t ∩ u : Finset E) : Set E) := by
        rw [Finset.coe_inter]
        exact fun x hx => K.inter_subset_convexHull (hL ht) huK ⟨hτt hx, h.convexHull_subset_of_mem hu hx⟩
      have htu : t ∩ u ⊂ u := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_right, fun heq => ?_⟩
        have hut : u ⊆ t := by
          intro v hv
          have : v ∈ t ∩ u := by
            rw [heq]
            exact hv
          exact (Finset.mem_inter.mp this).1
        exact h.notMem u hu (L.down_closed ht hut (K.nonempty_of_mem_faces huK))
      obtain ⟨v, hvu, hvtu⟩ := Finset.exists_of_ssubset htu
      refine ⟨v, hvu, fun w hw => ?_, fun s hs => ?_⟩
      · exact weights_eq_zero_of_subset_of_notMem (K.indep huK) htu.subset
          (hτu (subset_convexHull ℝ _ (Finset.mem_coe.mpr hw))) hvu hvtu
      · rw [hrest] at hs
        exact absurd hs (Finset.notMem_empty s)

omit hL hL' in
theorem IsRelFace.points_subset {τ : Finset E} {d : Finset (Finset E)} (h : IsRelFace K L L' τ d)
    {u : Finset E} (hu : u ∈ d) (htop : ∀ s ∈ d, s ⊆ u) :
    ((τ ∪ d.image c : Finset E) : Set E) ⊆ convexHull ℝ (u : Set E) := by
  intro x hx
  rcases Finset.mem_union.mp (Finset.mem_coe.mp hx) with hx | hx
  · exact h.subset u hu (Finset.mem_coe.mpr hx)
  · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    exact convexHull_mono (Finset.coe_subset.mpr (htop s hs))
      (openSimplex_subset_convexHull _ (hc s (h.subset_faces s hs)))

omit hL hL' in
theorem IsRelFace.mem_openSimplex_top {τ : Finset E} {d : Finset (Finset E)}
    (h : IsRelFace K L L' τ d) {u : Finset E} (hu : u ∈ d) (htop : ∀ s ∈ d, s ⊆ u) {x : E}
    (hx : x ∈ openSimplex (τ ∪ d.image c)) : x ∈ openSimplex u := by
  obtain ⟨l, hl₀, hl₁, hlx⟩ := hx
  have huK := h.subset_faces u hu
  have hpts := h.points_subset hc hu htop
  have hxu : x ∈ convexHull ℝ (u : Set E) := by
    rw [← hlx]
    exact (convex_convexHull ℝ _).sum_mem (fun w hw => (hl₀ w hw).le) hl₁
      fun w hw => hpts (Finset.mem_coe.mpr hw)
  rw [mem_openSimplex_self_iff (K.indep huK) hxu]
  intro v hv
  have hw := weights_sum_smul (K.indep huK) (τ ∪ d.image c) (p := fun w => w)
    (fun w hw => hpts (Finset.mem_coe.mpr hw)) (fun w hw => (hl₀ w hw).le) hl₁ v hv
  rw [hlx] at hw
  rw [hw]
  have hcu : c u ∈ τ ∪ d.image c := Finset.mem_union_right _ (Finset.mem_image_of_mem c hu)
  refine Finset.sum_pos' (fun w hw => mul_nonneg (hl₀ w hw).le
    (weights_nonneg (hpts (Finset.mem_coe.mpr hw)) hv)) ⟨c u, hcu, mul_pos (hl₀ _ hcu) ?_⟩
  exact (mem_openSimplex_self_iff (K.indep huK) (openSimplex_subset_convexHull _ (hc u huK))).mp
    (hc u huK) v hv

omit hL hL' in
theorem IsRelFace.weights_top_eq {τ : Finset E} {d : Finset (Finset E)} (h : IsRelFace K L L' τ d)
    {u : Finset E} (hu : u ∈ d) (htop : ∀ s ∈ d, s ⊆ u) {l : E → ℝ}
    (hl₀ : ∀ w ∈ τ ∪ d.image c, 0 ≤ l w) (hl₁ : ∑ w ∈ τ ∪ d.image c, l w = 1) {v : E} (hv : v ∈ u)
    (hτ : ∀ w ∈ τ, weights u w v = 0) (hd : ∀ s ∈ d.erase u, weights u (c s) v = 0) :
    weights u (∑ w ∈ τ ∪ d.image c, l w • w) v = l (c u) * weights u (c u) v := by
  have huK := h.subset_faces u hu
  have hpts := h.points_subset hc hu htop
  rw [weights_sum_smul (K.indep huK) (τ ∪ d.image c) (p := fun w => w)
    (fun w hw => hpts (Finset.mem_coe.mpr hw)) hl₀ hl₁ v hv]
  refine Finset.sum_eq_single (c u) (fun w hw hne => ?_)
    fun hcu => absurd (Finset.mem_union_right _ (Finset.mem_image_of_mem c hu)) hcu
  rcases Finset.mem_union.mp hw with hw | hw
  · rw [hτ w hw, mul_zero]
  · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hw
    have hsu : s ≠ u := fun hsu => hne (by rw [hsu])
    rw [hd s (Finset.mem_erase.mpr ⟨hsu, hs⟩), mul_zero]

theorem IsRelFace.top_coeff_le {τ τ' : Finset E} {d d' : Finset (Finset E)}
    (h : IsRelFace K L L' τ d) (h' : IsRelFace K L L' τ' d') {u : Finset E} (hu : u ∈ d)
    (htop : ∀ s ∈ d, s ⊆ u) (hu' : u ∈ d') (htop' : ∀ s ∈ d', s ⊆ u) {l l' : E → ℝ}
    (hl₀ : ∀ w ∈ τ ∪ d.image c, 0 < l w) (hl₁ : ∑ w ∈ τ ∪ d.image c, l w = 1)
    (hl'₀ : ∀ w ∈ τ' ∪ d'.image c, 0 < l' w) (hl'₁ : ∑ w ∈ τ' ∪ d'.image c, l' w = 1)
    (heq : ∑ w ∈ τ ∪ d.image c, l w • w = ∑ w ∈ τ' ∪ d'.image c, l' w • w) :
    l' (c u) ≤ l (c u) := by
  have huK := h.subset_faces u hu
  obtain ⟨v, hv, hτv, hdv⟩ := h.exists_vertex_avoiding hL hL' hc hu htop
  have hleft := h.weights_top_eq hc hu htop (fun w hw => (hl₀ w hw).le) hl₁ hv hτv hdv
  have hpts' := h'.points_subset hc hu' htop'
  have hright : l' (c u) * weights u (c u) v ≤
      weights u (∑ w ∈ τ' ∪ d'.image c, l' w • w) v := by
    rw [weights_sum_smul (K.indep huK) (τ' ∪ d'.image c) (p := fun w => w)
      (fun w hw => hpts' (Finset.mem_coe.mpr hw)) (fun w hw => (hl'₀ w hw).le) hl'₁ v hv]
    exact Finset.single_le_sum (fun w hw => mul_nonneg (hl'₀ w hw).le
      (weights_nonneg (hpts' (Finset.mem_coe.mpr hw)) hv))
      (Finset.mem_union_right _ (Finset.mem_image_of_mem c hu'))
  have hpos : 0 < weights u (c u) v :=
    (mem_openSimplex_self_iff (K.indep huK) (openSimplex_subset_convexHull _ (hc u huK))).mp
      (hc u huK) v hv
  rw [← heq, hleft] at hright
  exact le_of_mul_le_mul_right hright hpos

omit hL hL' in
theorem IsRelFace.erase_top_eq {τ : Finset E} {d : Finset (Finset E)} (h : IsRelFace K L L' τ d)
    {u : Finset E} (hu : u ∈ d) (hcu : c u ∉ τ) :
    (τ ∪ d.image c).erase (c u) = τ ∪ (d.erase u).image c := by
  ext y
  simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨hne, hy | ⟨s, hs, rfl⟩⟩
    · exact Or.inl hy
    · exact Or.inr ⟨s, ⟨fun hsu => hne (by rw [hsu]), hs⟩, rfl⟩
  · rintro (hy | ⟨s, hs, rfl⟩)
    · exact ⟨fun hyc => hcu (hyc ▸ hy), Or.inl hy⟩
    · refine ⟨fun hcs => ?_, Or.inr ⟨s, hs.2, rfl⟩⟩
      exact hs.1 (injOn_faces_of_mem_openSimplex K hc (h.subset_faces s hs.2)
        (h.subset_faces u hu) hcs)

omit hL hL' hc in
theorem mem_openSimplex_erase_of_coeff_lt {S : Finset E} {l : E → ℝ} (hl₀ : ∀ w ∈ S, 0 < l w)
    (hl₁ : ∑ w ∈ S, l w = 1) {x : E} (hlx : ∑ w ∈ S, l w • w = x) {p : E} (hp : p ∈ S)
    (hlt : l p < 1) : (1 - l p)⁻¹ • (x - l p • p) ∈ openSimplex (S.erase p) := by
  have hne0 : 1 - l p ≠ 0 := (sub_pos.mpr hlt).ne'
  refine ⟨fun w => l w / (1 - l p),
    fun w hw => div_pos (hl₀ w (Finset.mem_of_mem_erase hw)) (sub_pos.mpr hlt), ?_, ?_⟩
  · simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul, Finset.sum_erase_eq_sub hp, hl₁, mul_inv_cancel₀ hne0]
  · simp_rw [div_eq_inv_mul, mul_smul]
    rw [← Finset.smul_sum, Finset.sum_erase_eq_sub hp, hlx]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] hL hL' hc in
theorem erase_nonempty_of_coeff_lt {S : Finset E} {l : E → ℝ}
    (hl₁ : ∑ w ∈ S, l w = 1) {p : E} (hp : p ∈ S) (hlt : l p < 1) : (S.erase p).Nonempty := by
  by_contra hemp
  rw [Finset.not_nonempty_iff_eq_empty] at hemp
  have h1 : ∑ w ∈ S, l w = l p := by
    rw [← Finset.add_sum_erase S _ hp, hemp, Finset.sum_empty, add_zero]
  rw [hl₁] at h1
  exact absurd h1.symm hlt.ne

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E] hL hL' hc in
theorem eq_singleton_of_coeff_eq_one {S : Finset E} {l : E → ℝ} (hl₀ : ∀ w ∈ S, 0 < l w)
    (hl₁ : ∑ w ∈ S, l w = 1) {p : E} (hp : p ∈ S) (hone : l p = 1) : S = {p} := by
  classical
  have hzero : ∑ w ∈ S.erase p, l w = 0 := by
    have := Finset.add_sum_erase S l hp
    rw [hl₁, hone] at this
    linarith
  have hemp : S.erase p = ∅ := by
    by_contra hne
    have hpos : 0 < ∑ w ∈ S.erase p, l w :=
      Finset.sum_pos (fun w hw => hl₀ w (Finset.mem_of_mem_erase hw))
        (Finset.nonempty_iff_ne_empty.mpr hne)
    exact absurd hzero hpos.ne'
  ext w
  rw [Finset.mem_singleton]
  constructor
  · intro hw
    by_contra hne
    have : w ∈ S.erase p := Finset.mem_erase.mpr ⟨hne, hw⟩
    rw [hemp] at this
    exact absurd this (Finset.notMem_empty w)
  · intro hw
    exact hw ▸ hp

theorem IsRelFace.eq_of_mem_openSimplex_aux :
    ∀ (n : ℕ) {τ τ' : Finset E} {d d' : Finset (Finset E)}, d.card ≤ n →
      IsRelFace K L L' τ d → IsRelFace K L L' τ' d' → ∀ {x : E},
        x ∈ openSimplex (τ ∪ d.image c) → x ∈ openSimplex (τ' ∪ d'.image c) →
          τ = τ' ∧ d = d' := by
  intro n
  induction n with
  | zero =>
    intro τ τ' d d' hcard h h' x hx hx'
    have hd : d = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hd
    have hτ : τ ∈ L'.faces := by
      rcases h.base with h0 | h0
      · rcases h.nonempty with hne | hne
        · exact absurd hne (by rw [h0]; exact Finset.not_nonempty_empty)
        · exact absurd hne Finset.not_nonempty_empty
      · exact h0
    rw [Finset.image_empty, Finset.union_empty] at hx
    have hxL : x ∈ L.space :=
      hL'.space_eq ▸ L'.convexHull_subset_space hτ (openSimplex_subset_convexHull τ hx)
    rcases d'.eq_empty_or_nonempty with hd' | hd'
    · subst hd'
      rw [Finset.image_empty, Finset.union_empty] at hx'
      have hτ' : τ' ∈ L'.faces := by
        rcases h'.base with h0 | h0
        · rcases h'.nonempty with hne | hne
          · exact absurd hne (by rw [h0]; exact Finset.not_nonempty_empty)
          · exact absurd hne Finset.not_nonempty_empty
        · exact h0
      exact ⟨face_eq_of_mem_openSimplex L' hτ hτ' hx hx', rfl⟩
    · obtain ⟨u', hu', htop'⟩ := h'.flag.exists_top hd'
      exact absurd hxL (notMem_space_of_notMem_faces hL (h'.subset_faces u' hu')
        (h'.notMem u' hu') (h'.mem_openSimplex_top hc hu' htop' hx'))
  | succ n ih =>
    intro τ τ' d d' hcard h h' x hx hx'
    rcases d.eq_empty_or_nonempty with hd | hd
    · exact ih (by rw [hd]; simp) h h' hx hx'
    obtain ⟨u, hu, htop⟩ := h.flag.exists_top hd
    have hxu : x ∈ openSimplex u := h.mem_openSimplex_top hc hu htop hx
    rcases d'.eq_empty_or_nonempty with hd' | hd'
    · subst hd'
      rw [Finset.image_empty, Finset.union_empty] at hx'
      have hτ' : τ' ∈ L'.faces := by
        rcases h'.base with h0 | h0
        · rcases h'.nonempty with hne | hne
          · exact absurd hne (by rw [h0]; exact Finset.not_nonempty_empty)
          · exact absurd hne Finset.not_nonempty_empty
        · exact h0
      have hxL : x ∈ L.space :=
        hL'.space_eq ▸ L'.convexHull_subset_space hτ' (openSimplex_subset_convexHull τ' hx')
      exact absurd hxL (notMem_space_of_notMem_faces hL (h.subset_faces u hu) (h.notMem u hu) hxu)
    obtain ⟨u', hu', htop'⟩ := h'.flag.exists_top hd'
    have huu' : u = u' := face_eq_of_mem_openSimplex K (h.subset_faces u hu)
      (h'.subset_faces u' hu') hxu (h'.mem_openSimplex_top hc hu' htop' hx')
    subst huu'
    obtain ⟨l, hl₀, hl₁, hlx⟩ := hx
    obtain ⟨l', hl'₀, hl'₁, hl'x⟩ := hx'
    have heq : ∑ w ∈ τ ∪ d.image c, l w • w = ∑ w ∈ τ' ∪ d'.image c, l' w • w :=
      hlx.trans hl'x.symm
    have hlu : l (c u) = l' (c u) :=
      le_antisymm (h'.top_coeff_le hL hL' hc h hu' htop' hu htop hl'₀ hl'₁ hl₀ hl₁ heq.symm)
        (h.top_coeff_le hL hL' hc h' hu htop hu' htop' hl₀ hl₁ hl'₀ hl'₁ heq)
    have hcu : c u ∈ τ ∪ d.image c := Finset.mem_union_right _ (Finset.mem_image_of_mem c hu)
    have hcu' : c u ∈ τ' ∪ d'.image c := Finset.mem_union_right _ (Finset.mem_image_of_mem c hu')
    have hcuτ : c u ∉ τ := fun hmem =>
      (Finset.disjoint_left.mp (h.disjoint hL hL' hc)) hmem (Finset.mem_image_of_mem c hu)
    have hcuτ' : c u ∉ τ' := fun hmem =>
      (Finset.disjoint_left.mp (h'.disjoint hL hL' hc)) hmem (Finset.mem_image_of_mem c hu')
    by_cases hone : l (c u) = 1
    · have h1 := eq_singleton_of_coeff_eq_one hl₀ hl₁ hcu hone
      have h1' := eq_singleton_of_coeff_eq_one hl'₀ hl'₁ hcu' (hlu ▸ hone)
      have hτe : τ = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro w hw
        have : w ∈ ({c u} : Finset E) := h1 ▸ Finset.mem_union_left _ hw
        exact hcuτ ((Finset.mem_singleton.mp this) ▸ hw)
      have hτe' : τ' = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro w hw
        have : w ∈ ({c u} : Finset E) := h1' ▸ Finset.mem_union_left _ hw
        exact hcuτ' ((Finset.mem_singleton.mp this) ▸ hw)
      have hde : d = {u} := by
        ext s
        rw [Finset.mem_singleton]
        constructor
        · intro hs
          have : c s ∈ ({c u} : Finset E) :=
            h1 ▸ Finset.mem_union_right _ (Finset.mem_image_of_mem c hs)
          exact injOn_faces_of_mem_openSimplex K hc (h.subset_faces s hs) (h.subset_faces u hu)
            (Finset.mem_singleton.mp this)
        · intro hs
          exact hs ▸ hu
      have hde' : d' = {u} := by
        ext s
        rw [Finset.mem_singleton]
        constructor
        · intro hs
          have : c s ∈ ({c u} : Finset E) :=
            h1' ▸ Finset.mem_union_right _ (Finset.mem_image_of_mem c hs)
          exact injOn_faces_of_mem_openSimplex K hc (h'.subset_faces s hs) (h'.subset_faces u hu')
            (Finset.mem_singleton.mp this)
        · intro hs
          exact hs ▸ hu'
      rw [hτe, hτe', hde, hde']
      exact ⟨rfl, rfl⟩
    · have hlt : l (c u) < 1 :=
        lt_of_le_of_ne (hl₁ ▸ Finset.single_le_sum (fun w hw => (hl₀ w hw).le) hcu) hone
      have hy := mem_openSimplex_erase_of_coeff_lt hl₀ hl₁ hlx hcu hlt
      have hy' := mem_openSimplex_erase_of_coeff_lt hl'₀ hl'₁ hl'x hcu' (hlu ▸ hlt)
      rw [h.erase_top_eq hc hu hcuτ] at hy
      rw [h'.erase_top_eq hc hu' hcuτ', ← hlu] at hy'
      have hne := erase_nonempty_of_coeff_lt hl₁ hcu hlt
      have hne' := erase_nonempty_of_coeff_lt hl'₁ hcu' (hlu ▸ hlt)
      rw [h.erase_top_eq hc hu hcuτ] at hne
      rw [h'.erase_top_eq hc hu' hcuτ'] at hne'
      have hrest : IsRelFace K L L' τ (d.erase u) :=
        h.mono (Finset.Subset.refl τ) (Finset.erase_subset u d) (by
          rcases hne with ⟨w, hw⟩
          rcases Finset.mem_union.mp hw with hw | hw
          · exact Or.inl ⟨w, hw⟩
          · obtain ⟨s, hs, -⟩ := Finset.mem_image.mp hw
            exact Or.inr ⟨s, hs⟩)
      have hrest' : IsRelFace K L L' τ' (d'.erase u) :=
        h'.mono (Finset.Subset.refl τ') (Finset.erase_subset u d') (by
          rcases hne' with ⟨w, hw⟩
          rcases Finset.mem_union.mp hw with hw | hw
          · exact Or.inl ⟨w, hw⟩
          · obtain ⟨s, hs, -⟩ := Finset.mem_image.mp hw
            exact Or.inr ⟨s, hs⟩)
      have hcard' : (d.erase u).card ≤ n := by
        rw [Finset.card_erase_of_mem hu]
        omega
      obtain ⟨hτ, hd⟩ := ih hcard' hrest hrest' hy hy'
      refine ⟨hτ, ?_⟩
      rw [← Finset.insert_erase hu, ← Finset.insert_erase hu', hd]

theorem IsRelFace.eq_of_mem_openSimplex {τ τ' : Finset E} {d d' : Finset (Finset E)}
    (h : IsRelFace K L L' τ d) (h' : IsRelFace K L L' τ' d') {x : E}
    (hx : x ∈ openSimplex (τ ∪ d.image c)) (hx' : x ∈ openSimplex (τ' ∪ d'.image c)) :
    τ = τ' ∧ d = d' :=
  IsRelFace.eq_of_mem_openSimplex_aux hL hL' hc d.card le_rfl h h' hx hx'

omit [DecidableEq E] hL hL' hc in
theorem not_affineCombination_of_mem_openSimplex {T : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) {p : E} (hp : p ∈ openSimplex T) {τ : Finset E}
    (hτ : τ ⊂ T) {S : Finset E} (hS : (S : Set E) ⊆ convexHull ℝ (τ : Set E)) :
    ¬ ∃ a : E → ℝ, ∑ w ∈ S, a w = 1 ∧ ∑ w ∈ S, a w • w = p := by
  classical
  rintro ⟨a, ha₁, hap⟩
  have hpT : p ∈ convexHull ℝ (T : Set E) := openSimplex_subset_convexHull T hp
  have hpos := (mem_openSimplex_self_iff hT hpT).mp hp
  obtain ⟨v, hvT, hvτ⟩ := Finset.exists_of_ssubset hτ
  have hmem : ∀ w ∈ S, w ∈ convexHull ℝ (τ : Set E) := fun w hw => hS (Finset.mem_coe.mpr hw)
  let b : E → ℝ := fun u => ∑ w ∈ S, a w * weights τ w u
  have hb₁ : ∑ u ∈ τ, b u = 1 := by
    simp only [b]
    rw [Finset.sum_comm, ← ha₁]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [← Finset.mul_sum, sum_weights (hmem w hw), mul_one]
  have hbp : ∑ u ∈ τ, b u • u = p := by
    simp only [b]
    simp_rw [Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm, ← hap]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [← Finset.smul_sum, sum_weights_smul (hmem w hw)]
  let b' : E → ℝ := fun u => if u ∈ τ then b u else 0
  have h := weights_eq hT hpT (w := b') ?_ ?_ v hvT
  · simp only [b', if_neg hvτ] at h
    exact (hpos v hvT).ne' h
  · simp only [b']
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hτ.subset]
    exact hb₁
  · simp only [b', ite_smul, zero_smul]
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hτ.subset]
    exact hbp

theorem IsRelFace.exists_ssubset_rest_subset {τ : Finset E} {d : Finset (Finset E)}
    (h : IsRelFace K L L' τ d) {u : Finset E} (hu : u ∈ d) (htop : ∀ s ∈ d, s ⊆ u) :
    ∃ u' ⊂ u, ((τ ∪ (d.erase u).image c : Finset E) : Set E) ⊆ convexHull ℝ (u' : Set E) := by
  have huK : u ∈ K.faces := h.subset_faces u hu
  by_cases hrest : (d.erase u).Nonempty
  · obtain ⟨u', hu', htop'⟩ := (h.flag.mono (Finset.erase_subset u d)).exists_top hrest
    refine ⟨u', Finset.ssubset_iff_subset_ne.mpr
      ⟨htop u' (Finset.mem_of_mem_erase hu'), Finset.ne_of_mem_erase hu'⟩, ?_⟩
    intro x hx
    rcases Finset.mem_union.mp (Finset.mem_coe.mp hx) with hx | hx
    · exact h.subset u' (Finset.mem_of_mem_erase hu') (Finset.mem_coe.mpr hx)
    · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
      exact convexHull_mono (Finset.coe_subset.mpr (htop' s hs))
        (openSimplex_subset_convexHull _ (hc s (h.subset_faces s (Finset.mem_of_mem_erase hs))))
  · rw [Finset.not_nonempty_iff_eq_empty] at hrest
    rw [hrest, Finset.image_empty, Finset.union_empty]
    rcases τ.eq_empty_or_nonempty with hτ | hτ
    · refine ⟨∅, Finset.empty_ssubset.mpr (K.nonempty_of_mem_faces huK), ?_⟩
      rw [hτ, Finset.coe_empty]
      exact empty_subset _
    · have hτ' : τ ∈ L'.faces := by
        rcases h.base with h0 | h0
        · exact absurd hτ (by rw [h0]; exact Finset.not_nonempty_empty)
        · exact h0
      obtain ⟨t, ht, hτt⟩ := hL'.exists_face_subset hτ'
      refine ⟨t ∩ u, ?_, ?_⟩
      · refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_right, fun heq => ?_⟩
        have hut : u ⊆ t := by
          intro v hv
          have : v ∈ t ∩ u := by
            rw [heq]
            exact hv
          exact (Finset.mem_inter.mp this).1
        exact h.notMem u hu (L.down_closed ht hut (K.nonempty_of_mem_faces huK))
      · intro x hx
        rw [Finset.coe_inter]
        exact K.inter_subset_convexHull (hL ht) huK
          ⟨hτt (subset_convexHull ℝ _ hx), h.subset u hu hx⟩

omit hL hL' in
theorem IsRelFace.union_eq_insert {τ : Finset E} {d : Finset (Finset E)}
    (h : IsRelFace K L L' τ d) {u : Finset E} (hu : u ∈ d) (hcu : c u ∉ τ) :
    τ ∪ d.image c = insert (c u) (τ ∪ (d.erase u).image c) := by
  rw [← h.erase_top_eq hc hu hcu, Finset.insert_erase]
  exact Finset.mem_union_right _ (Finset.mem_image_of_mem c hu)

theorem IsRelFace.affineIndependent_aux :
    ∀ (n : ℕ) {τ : Finset E} {d : Finset (Finset E)}, d.card ≤ n → IsRelFace K L L' τ d →
      AffineIndependent ℝ ((↑) : {x // x ∈ τ ∪ d.image c} → E) := by
  intro n
  induction n with
  | zero =>
    intro τ d hcard h
    have hd : d = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hd
    rw [Finset.image_empty, Finset.union_empty]
    rcases h.base with h0 | h0
    · rcases h.nonempty with hne | hne
      · exact absurd hne (by rw [h0]; exact Finset.not_nonempty_empty)
      · exact absurd hne Finset.not_nonempty_empty
    · exact L'.indep h0
  | succ n ih =>
    intro τ d hcard h
    rcases d.eq_empty_or_nonempty with hd | hd
    · exact ih (by rw [hd]; simp) h
    obtain ⟨u, hu, htop⟩ := h.flag.exists_top hd
    have huK := h.subset_faces u hu
    have hcuτ : c u ∉ τ := fun hmem =>
      (Finset.disjoint_left.mp (h.disjoint hL hL' hc)) hmem (Finset.mem_image_of_mem c hu)
    have hcurest : c u ∉ τ ∪ (d.erase u).image c := by
      intro hmem
      rcases Finset.mem_union.mp hmem with hmem | hmem
      · exact hcuτ hmem
      · obtain ⟨s, hs, hcs⟩ := Finset.mem_image.mp hmem
        exact Finset.ne_of_mem_erase hs (injOn_faces_of_mem_openSimplex K hc
          (h.subset_faces s (Finset.mem_of_mem_erase hs)) huK hcs)
    rw [h.union_eq_insert hc hu hcuτ]
    have hrest_ind : AffineIndependent ℝ ((↑) : {x // x ∈ τ ∪ (d.erase u).image c} → E) := by
      rcases (τ ∪ (d.erase u).image c).eq_empty_or_nonempty with hemp | hne
      · rw [hemp]
        have : Subsingleton {x // x ∈ (∅ : Finset E)} :=
          ⟨fun a _ => absurd a.2 (Finset.notMem_empty _)⟩
        exact affineIndependent_of_subsingleton ℝ _
      · have hrest : IsRelFace K L L' τ (d.erase u) :=
          h.mono (Finset.Subset.refl τ) (Finset.erase_subset u d) (by
            rcases hne with ⟨w, hw⟩
            rcases Finset.mem_union.mp hw with hw | hw
            · exact Or.inl ⟨w, hw⟩
            · obtain ⟨s, hs, -⟩ := Finset.mem_image.mp hw
              exact Or.inr ⟨s, hs⟩)
        have hcard' : (d.erase u).card ≤ n := by
          rw [Finset.card_erase_of_mem hu]
          omega
        exact ih hcard' hrest
    refine (affineIndependent_insert_iff hcurest hrest_ind).mpr ?_
    obtain ⟨u', hu'u, hsub⟩ := h.exists_ssubset_rest_subset hL hL' hc hu htop
    exact not_affineCombination_of_mem_openSimplex (K.indep huK) (hc u huK) hu'u hsub

theorem IsRelFace.affineIndependent {τ : Finset E} {d : Finset (Finset E)}
    (h : IsRelFace K L L' τ d) : AffineIndependent ℝ ((↑) : {x // x ∈ τ ∪ d.image c} → E) :=
  IsRelFace.affineIndependent_aux hL hL' hc d.card le_rfl h

omit hL hL' hc in
theorem IsRelFace.exists_sub {τ : Finset E} {d : Finset (Finset E)} (h : IsRelFace K L L' τ d)
    {g : Finset E} (hg : g ⊆ τ ∪ d.image c) (hne : g.Nonempty) :
    ∃ (τ' : Finset E) (d' : Finset (Finset E)), IsRelFace K L L' τ' d' ∧ τ' ⊆ τ ∧ d' ⊆ d ∧
      g = τ' ∪ d'.image c := by
  refine ⟨g ∩ τ, d.filter fun s => c s ∈ g,
    h.mono Finset.inter_subset_right (Finset.filter_subset _ _) ?_, Finset.inter_subset_right,
    Finset.filter_subset _ _, ?_⟩
  · obtain ⟨w, hw⟩ := hne
    rcases Finset.mem_union.mp (hg hw) with hwτ | hwd
    · exact Or.inl ⟨w, Finset.mem_inter.mpr ⟨hw, hwτ⟩⟩
    · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hwd
      exact Or.inr ⟨s, Finset.mem_filter.mpr ⟨hs, hw⟩⟩
  · ext w
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_image, Finset.mem_filter]
    constructor
    · intro hw
      rcases Finset.mem_union.mp (hg hw) with hwτ | hwd
      · exact Or.inl ⟨hw, hwτ⟩
      · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hwd
        exact Or.inr ⟨s, ⟨hs, hw⟩, rfl⟩
    · rintro (⟨hw, -⟩ | ⟨s, ⟨-, hw⟩, rfl⟩)
      · exact hw
      · exact hw

omit hL in
theorem exists_relFace_of_mem_openSimplex_aux :
    ∀ (n : ℕ) {u : Finset E}, u.card ≤ n → u ∈ K.faces → ∀ {x : E}, x ∈ openSimplex u →
      ∃ (τ : Finset E) (d : Finset (Finset E)), IsRelFace K L L' τ d ∧ (∀ s ∈ d, s ⊆ u) ∧
        (τ : Set E) ⊆ convexHull ℝ (u : Set E) ∧
        x ∈ convexHull ℝ ((τ ∪ d.image c : Finset E) : Set E) := by
  intro n
  induction n with
  | zero =>
    intro u hcard hu x _
    exact absurd (Finset.card_pos.mpr (K.nonempty_of_mem_faces hu)) (by omega)
  | succ n ih =>
    intro u hcard hu x hx
    have hindep := K.indep hu
    have hxu : x ∈ convexHull ℝ (u : Set E) := openSimplex_subset_convexHull u hx
    by_cases huL : u ∈ L.faces
    · have hxL : x ∈ L'.space := hL'.space_eq ▸ L.convexHull_subset_space huL hxu
      obtain ⟨τ, hτ, hxτ⟩ := exists_face_mem_openSimplex L' hxL
      refine ⟨τ, ∅, ⟨Or.inr hτ, ⟨fun s hs => absurd hs (Finset.notMem_empty s),
        fun s hs => absurd hs (Finset.notMem_empty s)⟩, fun s hs => absurd hs (Finset.notMem_empty s),
        fun s hs => absurd hs (Finset.notMem_empty s), Or.inl (L'.nonempty_of_mem_faces hτ)⟩,
        fun s hs => absurd hs (Finset.notMem_empty s), ?_, ?_⟩
      · exact (subset_convexHull ℝ _).trans
          (hL'.convexHull_subset_of_mem_openSimplex huL hτ hxτ hxu)
      · rw [Finset.image_empty, Finset.union_empty]
        exact openSimplex_subset_convexHull τ hxτ
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
    have hsingle : IsRelFace K L L' ∅ {u} := ⟨Or.inl rfl,
      ⟨fun s hs => (Finset.mem_singleton.mp hs) ▸ hu,
        fun s hs t ht => Or.inl ((Finset.mem_singleton.mp hs) ▸ (Finset.mem_singleton.mp ht) ▸
          Finset.Subset.refl u)⟩,
      fun s hs => (Finset.mem_singleton.mp hs) ▸ huL,
      fun s _ => by simp,
      Or.inr (Finset.singleton_nonempty u)⟩
    by_cases hr : r = 1
    · have hle : ∀ v ∈ u, weights u (c u) v ≤ weights u x v := fun v hv => by
        simpa [hr] using hrle v hv
      have hwμ : ∀ v ∈ u, weights u (c u) v = weights u x v :=
        (Finset.sum_eq_sum_iff_of_le hle).mp (by rw [sum_weights hcu, sum_weights hxu])
      have hxc : x = c u := by
        rw [← sum_weights_smul hxu, ← sum_weights_smul hcu]
        exact Finset.sum_congr rfl fun v hv => by rw [hwμ v hv]
      refine ⟨∅, {u}, hsingle, fun s hs => (Finset.mem_singleton.mp hs) ▸ Finset.Subset.refl u,
        by simp, ?_⟩
      rw [Finset.image_singleton, Finset.empty_union, Finset.coe_singleton, hxc]
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
      obtain ⟨τ₁, d₁, h₁, htop₁, hτ₁, hyd₁⟩ := ih hcard' htK hyt
      have hτ₁u : (τ₁ : Set E) ⊆ convexHull ℝ (u : Set E) :=
        hτ₁.trans (convexHull_mono (Finset.coe_subset.mpr htu))
      have hface : IsRelFace K L L' τ₁ (insert u d₁) := ⟨h₁.base,
        ⟨fun s hs => by
          rcases Finset.mem_insert.mp hs with hsu | hs
          · rw [hsu]
            exact hu
          · exact h₁.subset_faces s hs,
        fun s hs t' ht' => by
          rcases Finset.mem_insert.mp hs with hsu | hs <;>
            rcases Finset.mem_insert.mp ht' with htu' | ht'
          · rw [hsu, htu']
            exact Or.inl (Finset.Subset.refl _)
          · rw [hsu]
            exact Or.inr ((htop₁ t' ht').trans htu)
          · rw [htu']
            exact Or.inl ((htop₁ s hs).trans htu)
          · exact h₁.flag.subset_or_subset hs ht'⟩,
        fun s hs => by
          rcases Finset.mem_insert.mp hs with hsu | hs
          · rw [hsu]
            exact huL
          · exact h₁.notMem s hs,
        fun s hs => by
          rcases Finset.mem_insert.mp hs with hsu | hs
          · rw [hsu]
            exact hτ₁u
          · exact h₁.subset s hs,
        Or.inr (Finset.insert_nonempty u d₁)⟩
      refine ⟨τ₁, insert u d₁, hface, fun s hs => ?_, hτ₁u, ?_⟩
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
            (Finset.mem_union_right _ (Finset.mem_image_of_mem c (Finset.mem_insert_self u d₁))))
        · refine convexHull_mono (Finset.coe_subset.mpr (Finset.union_subset_union_right
            (Finset.image_subset_image (Finset.subset_insert u d₁)))) hyd₁

omit hL in
theorem exists_relFace_of_mem_openSimplex {u : Finset E} (hu : u ∈ K.faces) {x : E}
    (hx : x ∈ openSimplex u) :
    ∃ (τ : Finset E) (d : Finset (Finset E)), IsRelFace K L L' τ d ∧ (∀ s ∈ d, s ⊆ u) ∧
      (τ : Set E) ⊆ convexHull ℝ (u : Set E) ∧
      x ∈ convexHull ℝ ((τ ∪ d.image c : Finset E) : Set E) :=
  exists_relFace_of_mem_openSimplex_aux hL' hc u.card le_rfl hu hx

theorem IsRelFace.convexHull_subset_face {τ : Finset E} {d : Finset (Finset E)}
    (h : IsRelFace K L L' τ d) :
    ∃ t ∈ K.faces, convexHull ℝ ((τ ∪ d.image c : Finset E) : Set E) ⊆ convexHull ℝ (t : Set E) := by
  rcases d.eq_empty_or_nonempty with hd | hd
  · subst hd
    rw [Finset.image_empty, Finset.union_empty]
    have hτ : τ ∈ L'.faces := by
      rcases h.base with h0 | h0
      · rcases h.nonempty with hne | hne
        · exact absurd hne (by rw [h0]; exact Finset.not_nonempty_empty)
        · exact absurd hne Finset.not_nonempty_empty
      · exact h0
    obtain ⟨t, ht, hτt⟩ := hL'.exists_face_subset hτ
    exact ⟨t, hL ht, hτt⟩
  · obtain ⟨u, hu, htop⟩ := h.flag.exists_top hd
    exact ⟨u, h.subset_faces u hu,
      convexHull_min (h.points_subset hc hu htop) (convex_convexHull ℝ _)⟩

noncomputable def relDerived : Geometry.SimplicialComplex ℝ E where
  faces := {f | ∃ (τ : Finset E) (d : Finset (Finset E)), IsRelFace K L L' τ d ∧ f = τ ∪ d.image c}
  isRelLowerSet_faces := by
    rintro f ⟨τ, d, h, rfl⟩
    refine ⟨?_, fun g hgf hg => ?_⟩
    · rcases h.nonempty with hne | hne
      · exact hne.mono Finset.subset_union_left
      · obtain ⟨s, hs⟩ := hne
        exact ⟨c s, Finset.mem_union_right _ (Finset.mem_image_of_mem c hs)⟩
    · obtain ⟨τ', d', h', -, -, rfl⟩ := h.exists_sub hgf hg
      exact ⟨τ', d', h', rfl⟩
  indep := by
    rintro f ⟨τ, d, h, rfl⟩
    exact h.affineIndependent hL hL' hc
  inter_subset_convexHull := by
    rintro f g ⟨τ, d, h, rfl⟩ ⟨τ', d', h', rfl⟩ x ⟨hxf, hxg⟩
    obtain ⟨T, hTf, hTne, hxT⟩ := exists_openSimplex_of_mem_convexHull hxf
    obtain ⟨T', hTg, hTne', hxT'⟩ := exists_openSimplex_of_mem_convexHull hxg
    obtain ⟨τ₁, d₁, h₁, -, -, rfl⟩ := h.exists_sub hTf hTne
    obtain ⟨τ₂, d₂, h₂, -, -, rfl⟩ := h'.exists_sub hTg hTne'
    obtain ⟨hτ, hd⟩ := h₁.eq_of_mem_openSimplex hL hL' hc h₂ hxT hxT'
    subst hτ
    subst hd
    exact convexHull_mono (subset_inter (Finset.coe_subset.mpr hTf) (Finset.coe_subset.mpr hTg))
      (openSimplex_subset_convexHull _ hxT)

theorem mem_relDerived_faces_iff {f : Finset E} :
    f ∈ (relDerived hL hL' hc).faces ↔
      ∃ (τ : Finset E) (d : Finset (Finset E)), IsRelFace K L L' τ d ∧ f = τ ∪ d.image c :=
  Iff.rfl

theorem relDerived_isSubdivision : IsSubdivision (relDerived hL hL' hc) K := by
  refine ⟨Subset.antisymm ?_ ?_, ?_⟩
  · intro x hx
    obtain ⟨f, ⟨τ, d, h, rfl⟩, hxf⟩ := (relDerived hL hL' hc).mem_space_iff.mp hx
    obtain ⟨t, ht, hsub⟩ := h.convexHull_subset_face hL hL' hc
    exact K.convexHull_subset_space ht (hsub hxf)
  · intro x hx
    obtain ⟨u, hu, hxu⟩ := exists_face_mem_openSimplex K hx
    obtain ⟨τ, d, h, -, -, hxd⟩ := exists_relFace_of_mem_openSimplex hL' hc hu hxu
    exact (relDerived hL hL' hc).convexHull_subset_space ⟨τ, d, h, rfl⟩ hxd
  · rintro f ⟨τ, d, h, rfl⟩
    exact h.convexHull_subset_face hL hL' hc

theorem faces_subset_relDerived : L'.faces ⊆ (relDerived hL hL' hc).faces := by
  intro τ hτ
  refine ⟨τ, ∅, ⟨Or.inr hτ, ⟨fun s hs => absurd hs (Finset.notMem_empty s),
    fun s hs => absurd hs (Finset.notMem_empty s)⟩, fun s hs => absurd hs (Finset.notMem_empty s),
    fun s hs => absurd hs (Finset.notMem_empty s), Or.inl (L'.nonempty_of_mem_faces hτ)⟩, ?_⟩
  rw [Finset.image_empty, Finset.union_empty]

theorem relDerived_faces_finite [Finite K.faces] [Finite L'.faces] :
    (relDerived hL hL' hc).faces.Finite := by
  classical
  have hK : K.faces.Finite := Set.toFinite _
  have hL'f : L'.faces.Finite := Set.toFinite _
  refine (((insert ∅ hL'f.toFinset) ×ˢ hK.toFinset.powerset : Finset (Finset E × Finset (Finset E)))
    |>.finite_toSet.image fun p => p.1 ∪ p.2.image c).subset ?_
  rintro f ⟨τ, d, h, rfl⟩
  refine ⟨(τ, d), ?_, rfl⟩
  rw [Finset.mem_coe, Finset.mem_product, Finset.mem_insert, Finset.mem_powerset]
  refine ⟨?_, fun s hs => hK.mem_toFinset.mpr (h.subset_faces s hs)⟩
  rcases h.base with h0 | h0
  · exact Or.inl h0
  · exact Or.inr (hL'f.mem_toFinset.mpr h0)

end RelFace

end DifferentialGeometry.Topology.PiecewiseLinear
