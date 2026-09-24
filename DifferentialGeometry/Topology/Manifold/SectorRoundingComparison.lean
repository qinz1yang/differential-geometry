import DifferentialGeometry.Topology.Manifold.SectorRounding
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

open Set
open scoped ContDiff Manifold

namespace Real.smoothAbs

noncomputable def quadrantMap (ε : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  ((p.1 - p.2 + Real.smoothAbs ε (p.1 + p.2)) / 2,
    (Real.smoothAbs ε (p.1 + p.2) - (p.1 - p.2)) / 2)

@[simp] theorem quadrantMap_eq_smoothAbsQuadrant {ε : ℝ} (hε : 0 < ε)
    (p : {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2}) :
    quadrantMap ε p.val = (Homeomorph.smoothAbsQuadrant hε p).val := rfl

theorem quadrantMap_eq_self {ε : ℝ} (hε : 0 < ε) {p : ℝ × ℝ}
    (hp : ε ≤ p.1 + p.2) : quadrantMap ε p = p := by
  simp only [quadrantMap, Real.smoothAbs.eq_self_of_le hε hp]
  ext <;> dsimp <;> ring

theorem quadrantMap_mem_strip {ε : ℝ} (hε : 0 < ε) {p : ℝ × ℝ}
    (hp : 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ ε) :
    0 ≤ (quadrantMap ε p).1 ∧ 0 ≤ (quadrantMap ε p).2 ∧
      (quadrantMap ε p).1 + (quadrantMap ε p).2 ≤ ε := by
  let q : {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} := ⟨p, hp.1, hp.2.1⟩
  exact ⟨(Homeomorph.smoothAbsQuadrant_nonneg hε q).1,
    (Homeomorph.smoothAbsQuadrant_nonneg hε q).2,
    Homeomorph.smoothAbsQuadrant_sum_le hε q hp.2.2⟩

end Real.smoothAbs

namespace OpenPartialHomeomorph

variable {X Y P : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace P]

noncomputable def smoothAbsQuadrantMap
    (e : OpenPartialHomeomorph X (P × (ℝ × ℝ))) (ε : ℝ) (x : X) : X :=
  e.symm ((e x).1, Real.smoothAbs.quadrantMap ε (e x).2)

def smoothAbsQuadrantSet
    (e : OpenPartialHomeomorph X (P × (ℝ × ℝ))) (A : Set X) (ε : ℝ) : Set X :=
  (A \ e.source) ∪ e.symm ''
    (e.target ∩ {p | Real.smoothAbs ε (p.2.1 - p.2.2) ≤ p.2.1 + p.2.2})

theorem mem_smoothAbsQuadrantSet_iff
    (e : OpenPartialHomeomorph X (P × (ℝ × ℝ))) (A : Set X) (ε : ℝ)
    {x : X} (hx : x ∈ e.source) :
    x ∈ e.smoothAbsQuadrantSet A ε ↔
      Real.smoothAbs ε ((e x).2.1 - (e x).2.2) ≤ (e x).2.1 + (e x).2.2 := by
  constructor
  · rintro (h | ⟨p, hp, he⟩)
    · exact False.elim (h.2 hx)
    · have he' : e x = p := by rw [← he, e.right_inv hp.1]
      rw [he']
      exact hp.2
  · intro h
    exact Or.inr ⟨e x, ⟨e.map_source hx, h⟩, e.left_inv hx⟩

theorem isImage_smoothAbsQuadrantSet
    (e₀ : OpenPartialHomeomorph X (P × (ℝ × ℝ)))
    (e₁ : OpenPartialHomeomorph Y (P × (ℝ × ℝ))) (A₀ : Set X) (A₁ : Set Y) (ε : ℝ) :
    (e₀.trans e₁.symm).IsImage (e₀.smoothAbsQuadrantSet A₀ ε)
      (e₁.smoothAbsQuadrantSet A₁ ε) := by
  intro x hx
  symm
  have hx₀ : x ∈ e₀.source := hx.1
  have hx₁ : e₀ x ∈ e₁.target := hx.2
  change x ∈ e₀.smoothAbsQuadrantSet A₀ ε ↔
    e₁.symm (e₀ x) ∈ e₁.smoothAbsQuadrantSet A₁ ε
  rw [e₀.mem_smoothAbsQuadrantSet_iff A₀ ε hx₀,
    e₁.mem_smoothAbsQuadrantSet_iff A₁ ε (e₁.map_target hx₁), e₁.right_inv hx₁]

theorem isImage_of_quadrant_charts
    (e₀ : OpenPartialHomeomorph X (P × (ℝ × ℝ)))
    (e₁ : OpenPartialHomeomorph Y (P × (ℝ × ℝ)))
    {A₀ : Set X} {A₁ : Set Y}
    (h₀ : ∀ p ∈ e₀.target, e₀.symm p ∈ A₀ ↔ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2)
    (h₁ : ∀ p ∈ e₁.target, e₁.symm p ∈ A₁ ↔ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2) :
    (e₀.trans e₁.symm).IsImage A₀ A₁ := by
  intro x hx
  symm
  have hx₀ : x ∈ e₀.source := hx.1
  have hx₁ : e₀ x ∈ e₁.target := hx.2
  change x ∈ A₀ ↔ e₁.symm (e₀ x) ∈ A₁
  rw [h₁ _ hx₁, ← h₀ _ (e₀.map_source hx₀), e₀.left_inv hx₀]

theorem smoothAbsQuadrantMap_coordinate_mem_target
    (e : OpenPartialHomeomorph X (P × (ℝ × ℝ))) {ε : ℝ} (hε : 0 < ε)
    (hstrip : {p : P × (ℝ × ℝ) | 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε} ⊆
      e.target) {p : P × (ℝ × ℝ)} (hp : p ∈ e.target)
    (hq : 0 ≤ p.2.1 ∧ 0 ≤ p.2.2) :
    (p.1, Real.smoothAbs.quadrantMap ε p.2) ∈ e.target := by
  by_cases h : ε ≤ p.2.1 + p.2.2
  · rw [Real.smoothAbs.quadrantMap_eq_self hε h]
    exact hp
  · exact hstrip (Real.smoothAbs.quadrantMap_mem_strip hε
      ⟨hq.1, hq.2, (lt_of_not_ge h).le⟩)

theorem smoothAbsQuadrantMap_trans
    (e₀ : OpenPartialHomeomorph X (P × (ℝ × ℝ)))
    (e₁ : OpenPartialHomeomorph Y (P × (ℝ × ℝ))) {ε : ℝ} (hε : 0 < ε)
    (hstrip₀ : {p : P × (ℝ × ℝ) | 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε} ⊆
      e₀.target) {x : X} (hx : x ∈ (e₀.trans e₁.symm).source)
    (hq : 0 ≤ (e₀ x).2.1 ∧ 0 ≤ (e₀ x).2.2) :
    e₁.smoothAbsQuadrantMap ε ((e₀.trans e₁.symm) x) =
      (e₀.trans e₁.symm) (e₀.smoothAbsQuadrantMap ε x) := by
  have ht := e₀.smoothAbsQuadrantMap_coordinate_mem_target hε hstrip₀ (e₀.map_source hx.1) hq
  change e₁.symm ((e₁ (e₁.symm (e₀ x))).1,
    Real.smoothAbs.quadrantMap ε (e₁ (e₁.symm (e₀ x))).2) =
      e₁.symm (e₀ (e₀.symm ((e₀ x).1, Real.smoothAbs.quadrantMap ε (e₀ x).2)))
  have hx₁ : e₀ x ∈ e₁.target := hx.2
  rw [e₁.right_inv hx₁, e₀.right_inv ht]

theorem smoothAbsQuadrantMap_mem_trans_source
    (e₀ : OpenPartialHomeomorph X (P × (ℝ × ℝ)))
    (e₁ : OpenPartialHomeomorph Y (P × (ℝ × ℝ))) {ε : ℝ} (hε : 0 < ε)
    (hstrip₀ : {p : P × (ℝ × ℝ) | 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε} ⊆
      e₀.target)
    (hstrip₁ : {p : P × (ℝ × ℝ) | 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε} ⊆
      e₁.target) {x : X} (hx : x ∈ (e₀.trans e₁.symm).source)
    (hq : 0 ≤ (e₀ x).2.1 ∧ 0 ≤ (e₀ x).2.2) :
    e₀.smoothAbsQuadrantMap ε x ∈ (e₀.trans e₁.symm).source := by
  have ht₀ := e₀.smoothAbsQuadrantMap_coordinate_mem_target hε hstrip₀ (e₀.map_source hx.1) hq
  have ht₁ := e₁.smoothAbsQuadrantMap_coordinate_mem_target hε hstrip₁ hx.2 hq
  refine ⟨e₀.map_target ht₀, ?_⟩
  change e₀ (e₀.symm ((e₀ x).1, Real.smoothAbs.quadrantMap ε (e₀ x).2)) ∈ e₁.target
  rwa [e₀.right_inv ht₀]


theorem eqOn_unrounding_of_quadrant_charts
    (e₀ : OpenPartialHomeomorph X (P × (ℝ × ℝ)))
    (e₁ : OpenPartialHomeomorph Y (P × (ℝ × ℝ)))
    {A₀ : Set X} {A₁ : Set Y} {ε : ℝ} (hε : 0 < ε)
    (hraw₀ : ∀ p ∈ e₀.target, e₀.symm p ∈ A₀ ↔ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2)
    (hraw₁ : ∀ p ∈ e₁.target, e₁.symm p ∈ A₁ ↔ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2)
    (hstrip₀ : {p : P × (ℝ × ℝ) | 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε} ⊆
      e₀.target)
    (R₀ : A₀ ≃ₜ e₀.smoothAbsQuadrantSet A₀ ε)
    (R₁ : A₁ ≃ₜ e₁.smoothAbsQuadrantSet A₁ ε)
    (hR₀ : ∀ x : A₀, x.val ∈ e₀.source → (R₀ x).val = e₀.smoothAbsQuadrantMap ε x.val)
    (hR₁ : ∀ y : A₁, y.val ∈ e₁.source → (R₁ y).val = e₁.smoothAbsQuadrantMap ε y.val)
    (Q : e₀.smoothAbsQuadrantSet A₀ ε → e₁.smoothAbsQuadrantSet A₁ ε)
    {W : Set X} (hQ : ∀ z, z.val ∈ W → (Q z).val = (e₀.trans e₁.symm) z.val) :
    EqOn (fun x : A₀ => (R₁.symm (Q (R₀ x))).val)
      (fun x => (e₀.trans e₁.symm) x.val)
      {x | x.val ∈ (e₀.trans e₁.symm).source ∧ (R₀ x).val ∈ W} := by
  intro x hx
  have hx₀ : x.val ∈ e₀.source := hx.1.1
  have hx₁ : e₀ x.val ∈ e₁.target := hx.1.2
  have hq : 0 ≤ (e₀ x.val).2.1 ∧ 0 ≤ (e₀ x.val).2.2 := by
    apply (hraw₀ _ (e₀.map_source hx₀)).mp
    rw [e₀.left_inv hx₀]
    exact x.property
  have hy : (e₀.trans e₁.symm) x.val ∈ A₁ :=
    (e₀.isImage_of_quadrant_charts e₁ hraw₀ hraw₁ hx.1).mpr x.property
  let y : A₁ := ⟨(e₀.trans e₁.symm) x.val, hy⟩
  have hRy : R₁ y = Q (R₀ x) := by
    apply Subtype.ext
    rw [hR₁ y (e₁.map_target hx₁), hQ _ hx.2, hR₀ x hx₀]
    exact e₀.smoothAbsQuadrantMap_trans e₁ hε hstrip₀ hx.1 hq
  change (R₁.symm (Q (R₀ x))).val = (e₀.trans e₁.symm) x.val
  rw [← hRy, R₁.symm_apply_apply]

theorem exists_homeomorph_smoothAbs_quadrant_comparison [T2Space X] [T2Space Y] [CompactSpace P]
    (e₀ : OpenPartialHomeomorph X (P × (ℝ × ℝ)))
    (e₁ : OpenPartialHomeomorph Y (P × (ℝ × ℝ)))
    {A₀ : Set X} {A₁ : Set Y} (hA₀ : IsCompact A₀) (hA₁ : IsCompact A₁)
    {ε : ℝ} (hε : 0 < ε)
    (hraw₀ : ∀ p ∈ e₀.target, e₀.symm p ∈ A₀ ↔ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2)
    (hraw₁ : ∀ p ∈ e₁.target, e₁.symm p ∈ A₁ ↔ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2)
    (hstrip₀ : {p : P × (ℝ × ℝ) | 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε} ⊆
      e₀.target)
    (hstrip₁ : {p : P × (ℝ × ℝ) | 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε} ⊆
      e₁.target) :
    ∃ (R₀ : A₀ ≃ₜ e₀.smoothAbsQuadrantSet A₀ ε)
      (R₁ : A₁ ≃ₜ e₁.smoothAbsQuadrantSet A₁ ε),
      (∀ x : A₀, x.val ∈ e₀.source → (R₀ x).val = e₀.smoothAbsQuadrantMap ε x.val) ∧
      (∀ y : A₁, y.val ∈ e₁.source → (R₁ y).val = e₁.smoothAbsQuadrantMap ε y.val) ∧
      ∀ (Q : e₀.smoothAbsQuadrantSet A₀ ε → e₁.smoothAbsQuadrantSet A₁ ε)
        (W : Set X), IsOpen W →
        (∀ z, z.val ∈ W → (Q z).val = (e₀.trans e₁.symm) z.val) →
        ∃ U : Set X, IsOpen U ∧ U ⊆ (e₀.trans e₁.symm).source ∧
          (∀ x : A₀, x.val ∈ U ↔ x.val ∈ (e₀.trans e₁.symm).source ∧ (R₀ x).val ∈ W) ∧
          ∀ x : A₀, x.val ∈ U →
            (R₁.symm (Q (R₀ x))).val = (e₀.trans e₁.symm) x.val := by
  obtain ⟨R₀, hR₀, _⟩ := e₀.exists_homeomorph_smoothAbs_quadrant hA₀ hε hraw₀ hstrip₀
  obtain ⟨R₁, hR₁, _⟩ := e₁.exists_homeomorph_smoothAbs_quadrant hA₁ hε hraw₁ hstrip₁
  refine ⟨R₀, R₁, hR₀, hR₁, ?_⟩
  intro Q W hW hQ
  let V : Set A₀ := {x | x.val ∈ (e₀.trans e₁.symm).source ∧ (R₀ x).val ∈ W}
  have hV : IsOpen V :=
    ((e₀.trans e₁.symm).open_source.preimage continuous_subtype_val).inter
      (hW.preimage (continuous_subtype_val.comp R₀.continuous))
  obtain ⟨U, hU, hUV⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hV
  refine ⟨U ∩ (e₀.trans e₁.symm).source, hU.inter (e₀.trans e₁.symm).open_source,
    inter_subset_right, ?_, ?_⟩
  · intro x
    have hmem : x.val ∈ U ↔ x ∈ V := by
      change x ∈ Subtype.val ⁻¹' U ↔ x ∈ V
      rw [hUV]
    change (x.val ∈ U ∧ x.val ∈ (e₀.trans e₁.symm).source) ↔ _
    rw [hmem]
    exact ⟨fun h => h.1, fun h => ⟨h, h.1⟩⟩
  · intro x hx
    apply e₀.eqOn_unrounding_of_quadrant_charts e₁ hε hraw₀ hraw₁ hstrip₀ R₀ R₁ hR₀ hR₁ Q hQ
    change x ∈ V
    rw [← hUV]
    exact hx.1

theorem mem_smoothAbsQuadrantSet_iff_of_notMem_source
    (e : OpenPartialHomeomorph X (P × (ℝ × ℝ))) (A : Set X) (ε : ℝ)
    {x : X} (hx : x ∉ e.source) : x ∈ e.smoothAbsQuadrantSet A ε ↔ x ∈ A := by
  constructor
  · rintro (h | ⟨p, hp, he⟩)
    · exact h.1
    · exact False.elim (hx (he ▸ e.map_target hp.1))
  · intro h
    exact Or.inl ⟨h, hx⟩

theorem IsImage.smoothAbsQuadrantSet
    {c : OpenPartialHomeomorph X Y} {A : Set X} {B : Set Y}
    (hc : c.IsImage A B) (e : OpenPartialHomeomorph X (P × (ℝ × ℝ))) (ε : ℝ) :
    c.IsImage (e.smoothAbsQuadrantSet A ε)
      ((c.symm.trans e).smoothAbsQuadrantSet B ε) := by
  intro x hx
  let f := c.symm.trans e
  have heq : f (c x) = e x := by
    change e (c.symm (c x)) = e x
    rw [c.left_inv hx]
  have hs : c x ∈ f.source ↔ x ∈ e.source := by
    change (c x ∈ c.target ∧ c.symm (c x) ∈ e.source) ↔ _
    rw [c.left_inv hx]
    exact and_iff_right (c.map_source hx)
  by_cases hxe : x ∈ e.source
  · rw [f.mem_smoothAbsQuadrantSet_iff B ε (hs.mpr hxe),
      e.mem_smoothAbsQuadrantSet_iff A ε hxe, heq]
  · rw [f.mem_smoothAbsQuadrantSet_iff_of_notMem_source B ε (fun h => hxe (hs.mp h)),
      e.mem_smoothAbsQuadrantSet_iff_of_notMem_source A ε hxe]
    exact hc hx


theorem smoothAbsQuadrantMap_symm_trans
    (c : OpenPartialHomeomorph X Y) (e : OpenPartialHomeomorph X (P × (ℝ × ℝ)))
    (ε : ℝ) {x : X} (hx : x ∈ c.source) :
    (c.symm.trans e).smoothAbsQuadrantMap ε (c x) = c (e.smoothAbsQuadrantMap ε x) := by
  change c (e.symm ((e (c.symm (c x))).1,
    Real.smoothAbs.quadrantMap ε (e (c.symm (c x))).2)) = _
  rw [c.left_inv hx]
  rfl

theorem exists_homeomorph_smoothAbs_quadrant_collar [T2Space X] [T2Space Y] [CompactSpace P]
    (c : OpenPartialHomeomorph X Y) (e : OpenPartialHomeomorph X (P × (ℝ × ℝ)))
    {A : Set X} {B : Set Y} (hA : IsCompact A) (hB : IsCompact B)
    (hc : c.IsImage A B) {ε : ℝ} (hε : 0 < ε)
    (hraw : ∀ p ∈ e.target, e.symm p ∈ A ↔ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2)
    (hstrip : {p : P × (ℝ × ℝ) | 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε} ⊆
      (c.symm.trans e).target) :
    ∃ (R₀ : A ≃ₜ e.smoothAbsQuadrantSet A ε)
      (R₁ : B ≃ₜ (c.symm.trans e).smoothAbsQuadrantSet B ε),
      (∀ x : A, x.val ∈ e.source → (R₀ x).val = e.smoothAbsQuadrantMap ε x.val) ∧
      (∀ x : A, x.val ∉ e.source → (R₀ x).val = x.val) ∧
      (∀ y : B, y.val ∈ (c.symm.trans e).source →
        (R₁ y).val = (c.symm.trans e).smoothAbsQuadrantMap ε y.val) ∧
      (∀ y : B, y.val ∉ (c.symm.trans e).source → (R₁ y).val = y.val) ∧
      (∀ x : A, x.val ∈ c.source → (R₀ x).val ∈ c.source) ∧
      (∀ (x : A) (y : B), x.val ∈ c.source → y.val = c x.val → (R₁ y).val = c (R₀ x).val) ∧
      ∀ (Q : e.smoothAbsQuadrantSet A ε → (c.symm.trans e).smoothAbsQuadrantSet B ε)
        (W : Set X), IsOpen W → (∀ z, z.val ∈ W → (Q z).val = c z.val) →
        ∃ U : Set X, IsOpen U ∧ U ⊆ c.source ∧
          (∀ x : A, x.val ∈ U ↔ x.val ∈ c.source ∧ (R₀ x).val ∈ W) ∧
          ∀ x : A, x.val ∈ U → (R₁.symm (Q (R₀ x))).val = c x.val := by
  let f := c.symm.trans e
  have hstripe : {p : P × (ℝ × ℝ) | 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε} ⊆
      e.target := fun p hp => (hstrip hp).1
  have hrawf : ∀ p ∈ f.target, f.symm p ∈ B ↔ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 := by
    intro p hp
    have hp' : e.symm p ∈ c.source := hp.2
    change c (e.symm p) ∈ B ↔ _
    rw [hc hp', hraw p hp.1]
  obtain ⟨R₀, hR₀, hR₀fix⟩ := e.exists_homeomorph_smoothAbs_quadrant hA hε hraw hstripe
  obtain ⟨R₁, hR₁, hR₁fix⟩ := f.exists_homeomorph_smoothAbs_quadrant hB hε hrawf hstrip
  have hfix₀ (x : A) (hx : x.val ∉ e.source) : (R₀ x).val = x.val := by
    apply hR₀fix
    rintro ⟨p, hp, he⟩
    exact hx (he ▸ e.map_target (hstripe hp))
  have hfix₁ (y : B) (hy : y.val ∉ f.source) : (R₁ y).val = y.val := by
    apply hR₁fix
    rintro ⟨p, hp, he⟩
    exact hy (he ▸ f.map_target (hstrip hp))
  have hsource (x : A) (hx : x.val ∈ c.source) : c x.val ∈ f.source ↔ x.val ∈ e.source := by
    change (c x.val ∈ c.target ∧ c.symm (c x.val) ∈ e.source) ↔ _
    rw [c.left_inv hx]
    exact and_iff_right (c.map_source hx)
  have hmap (x : A) (hx : x.val ∈ c.source) : (R₀ x).val ∈ c.source := by
    by_cases hxe : x.val ∈ e.source
    · have hp : e x.val ∈ f.target := by
        refine ⟨e.map_source hxe, ?_⟩
        change e.symm (e x.val) ∈ c.source
        rwa [e.left_inv hxe]
      have hq : 0 ≤ (e x.val).2.1 ∧ 0 ≤ (e x.val).2.2 := by
        apply (hraw _ (e.map_source hxe)).mp
        rw [e.left_inv hxe]
        exact x.property
      have ht := f.smoothAbsQuadrantMap_coordinate_mem_target hε hstrip hp hq
      rw [hR₀ x hxe]
      exact ht.2
    · rwa [hfix₀ x hxe]
  have hcomm (x : A) (y : B) (hx : x.val ∈ c.source) (hy : y.val = c x.val) :
      (R₁ y).val = c (R₀ x).val := by
    by_cases hxe : x.val ∈ e.source
    · have hyf : y.val ∈ f.source := hy ▸ (hsource x hx).mpr hxe
      rw [hR₁ y hyf, hR₀ x hxe]
      change f.smoothAbsQuadrantMap ε y.val = c (e.smoothAbsQuadrantMap ε x.val)
      rw [hy]
      exact c.smoothAbsQuadrantMap_symm_trans e ε hx
    · have hyf : y.val ∉ f.source := by
        rw [hy]
        exact fun h => hxe ((hsource x hx).mp h)
      rw [hfix₁ y hyf, hfix₀ x hxe]
      exact hy
  refine ⟨R₀, R₁, hR₀, hfix₀, hR₁, hfix₁, hmap, hcomm, ?_⟩
  intro Q W hW hQ
  let V : Set A := {x | x.val ∈ c.source ∧ (R₀ x).val ∈ W}
  have hV : IsOpen V := (c.open_source.preimage continuous_subtype_val).inter
    (hW.preimage (continuous_subtype_val.comp R₀.continuous))
  obtain ⟨U, hU, hUV⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hV
  refine ⟨U ∩ c.source, hU.inter c.open_source, inter_subset_right, ?_, ?_⟩
  · intro x
    have hmem : x.val ∈ U ↔ x ∈ V := by
      change x ∈ Subtype.val ⁻¹' U ↔ x ∈ V
      rw [hUV]
    change (x.val ∈ U ∧ x.val ∈ c.source) ↔ _
    rw [hmem]
    exact ⟨fun h => h.1, fun h => ⟨h, h.1⟩⟩
  · intro x hx
    have hxV : x ∈ V := by
      rw [← hUV]
      exact hx.1
    let y : B := ⟨c x.val, (hc hx.2).mpr x.property⟩
    have hRy : R₁ y = Q (R₀ x) := by
      apply Subtype.ext
      rw [hQ _ hxV.2]
      exact hcomm x y hx.2 rfl
    exact (congrArg (fun z => (R₁.symm z).val) hRy.symm).trans
      (congrArg Subtype.val (R₁.symm_apply_apply y))


theorem exists_pos_lt_quadrant_strip_subset_target [CompactSpace P]
    (e : OpenPartialHomeomorph X (P × (ℝ × ℝ)))
    (hcorner : ∀ p : P, (p, 0, 0) ∈ e.target) {η : ℝ} (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ε < η ∧
      {p : P × (ℝ × ℝ) | 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε} ⊆ e.target := by
  obtain ⟨u, v, _, hv, hu, hzero, huv⟩ :=
    generalized_tube_lemma (isCompact_univ (X := P))
      (isCompact_singleton (x := ((0 : ℝ), (0 : ℝ)))) e.open_target
      (by
        rintro ⟨p, q⟩ ⟨_, hq⟩
        have hq' : q = (0, 0) := hq
        subst q
        exact hcorner p)
  obtain ⟨δ, hδ, hδv⟩ := Metric.isOpen_iff.mp hv (0, 0) (hzero (mem_singleton (0, 0)))
  let ε := min δ η / 2
  have hε : 0 < ε := half_pos (lt_min hδ hη)
  have hεδ : ε < δ := (half_lt_self (lt_min hδ hη)).trans_le (min_le_left _ _)
  have hεη : ε < η := (half_lt_self (lt_min hδ hη)).trans_le (min_le_right _ _)
  refine ⟨ε, hε, hεη, ?_⟩
  intro p hp
  apply huv
  refine ⟨hu (mem_univ p.1), hδv ?_⟩
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq,
    sub_zero, sub_zero, abs_of_nonneg hp.1, abs_of_nonneg hp.2.1]
  constructor <;> linarith [hp.1, hp.2.1, hp.2.2]


end OpenPartialHomeomorph

namespace PartialDiffeomorph

variable {E₀ E₁ E₂ : Type*}
  [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  {H₀ H₁ H₂ : Type*} [TopologicalSpace H₀] [TopologicalSpace H₁] [TopologicalSpace H₂]
  {I₀ : ModelWithCorners ℝ E₀ H₀} {I₁ : ModelWithCorners ℝ E₁ H₁}
  {I₂ : ModelWithCorners ℝ E₂ H₂}
  {X Y P : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace P]
  [ChartedSpace H₀ X] [ChartedSpace H₁ Y] [ChartedSpace H₂ (P × (ℝ × ℝ))]
  [T2Space X] [T2Space Y] [CompactSpace P]

theorem exists_partialDiffeomorph_unrounding_of_quadrant_charts
    (e₀ : PartialDiffeomorph I₀ I₂ X (P × (ℝ × ℝ)) ∞)
    (e₁ : PartialDiffeomorph I₁ I₂ Y (P × (ℝ × ℝ)) ∞)
    {A₀ : Set X} {A₁ : Set Y} (hA₀ : IsCompact A₀) (hA₁ : IsCompact A₁)
    {ε : ℝ} (hε : 0 < ε)
    (hraw₀ : ∀ p ∈ e₀.target, e₀.symm p ∈ A₀ ↔ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2)
    (hraw₁ : ∀ p ∈ e₁.target, e₁.symm p ∈ A₁ ↔ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2)
    (hstrip₀ : {p : P × (ℝ × ℝ) | 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε} ⊆
      e₀.target)
    (hstrip₁ : {p : P × (ℝ × ℝ) | 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε} ⊆
      e₁.target) :
    ∃ (R₀ : A₀ ≃ₜ e₀.toOpenPartialHomeomorph.smoothAbsQuadrantSet A₀ ε)
      (R₁ : A₁ ≃ₜ e₁.toOpenPartialHomeomorph.smoothAbsQuadrantSet A₁ ε),
      (∀ x : A₀, x.val ∈ e₀.source →
        (R₀ x).val = e₀.toOpenPartialHomeomorph.smoothAbsQuadrantMap ε x.val) ∧
      (∀ y : A₁, y.val ∈ e₁.source →
        (R₁ y).val = e₁.toOpenPartialHomeomorph.smoothAbsQuadrantMap ε y.val) ∧
      ∀ (Q : e₀.toOpenPartialHomeomorph.smoothAbsQuadrantSet A₀ ε →
          e₁.toOpenPartialHomeomorph.smoothAbsQuadrantSet A₁ ε)
        (W : Set X), IsOpen W →
        (∀ z, z.val ∈ W → (Q z).val = (e₀.trans e₁.symm) z.val) →
        ∃ F : PartialDiffeomorph I₀ I₁ X Y ∞,
          (∀ x : A₀, x.val ∈ F.source ↔
            x.val ∈ (e₀.trans e₁.symm).source ∧ (R₀ x).val ∈ W) ∧
          ∀ x : A₀, x.val ∈ F.source → F x.val = (R₁.symm (Q (R₀ x))).val := by
  obtain ⟨R₀, R₁, hR₀, hR₁, hR⟩ :=
    e₀.toOpenPartialHomeomorph.exists_homeomorph_smoothAbs_quadrant_comparison
      e₁.toOpenPartialHomeomorph hA₀ hA₁ hε hraw₀ hraw₁ hstrip₀ hstrip₁
  refine ⟨R₀, R₁, hR₀, hR₁, ?_⟩
  intro Q W hW hQ
  obtain ⟨U, hU, hUs, hmem, heq⟩ := hR Q W hW hQ
  let F := DifferentialGeometry.Topology.PartialDiffeomorph.restrict (e₀.trans e₁.symm) U hU
  have hFs : F.source = U := by
    change (e₀.trans e₁.symm).source ∩ U = U
    exact inter_eq_right.mpr hUs
  refine ⟨F, ?_, ?_⟩
  · intro x
    rw [hFs]
    exact hmem x
  · intro x hx
    exact (heq x (hFs ▸ hx)).symm


theorem exists_partialDiffeomorph_unrounding_of_corner_collar
    (c : PartialDiffeomorph I₀ I₁ X Y ∞)
    (e : PartialDiffeomorph I₀ I₂ X (P × (ℝ × ℝ)) ∞)
    {A : Set X} {B : Set Y} (hA : IsCompact A) (hB : IsCompact B)
    (hc : c.toOpenPartialHomeomorph.IsImage A B) {ε : ℝ} (hε : 0 < ε)
    (hraw : ∀ p ∈ e.target, e.symm p ∈ A ↔ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2)
    (hstrip : {p : P × (ℝ × ℝ) | 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε} ⊆
      (c.symm.trans e).target) :
    ∃ (R₀ : A ≃ₜ e.toOpenPartialHomeomorph.smoothAbsQuadrantSet A ε)
      (R₁ : B ≃ₜ (c.symm.trans e).toOpenPartialHomeomorph.smoothAbsQuadrantSet B ε),
      (∀ x : A, x.val ∈ e.source →
        (R₀ x).val = e.toOpenPartialHomeomorph.smoothAbsQuadrantMap ε x.val) ∧
      (∀ x : A, x.val ∉ e.source → (R₀ x).val = x.val) ∧
      (∀ y : B, y.val ∈ (c.symm.trans e).source →
        (R₁ y).val = (c.symm.trans e).toOpenPartialHomeomorph.smoothAbsQuadrantMap ε y.val) ∧
      (∀ y : B, y.val ∉ (c.symm.trans e).source → (R₁ y).val = y.val) ∧
      ∀ (Q : e.toOpenPartialHomeomorph.smoothAbsQuadrantSet A ε →
          (c.symm.trans e).toOpenPartialHomeomorph.smoothAbsQuadrantSet B ε)
        (W : Set X), IsOpen W → (∀ z, z.val ∈ W → (Q z).val = c z.val) →
        ∃ F : PartialDiffeomorph I₀ I₁ X Y ∞,
          (∀ x : A, x.val ∈ F.source ↔ x.val ∈ c.source ∧ (R₀ x).val ∈ W) ∧
          ∀ x : A, x.val ∈ F.source → F x.val = (R₁.symm (Q (R₀ x))).val := by
  obtain ⟨R₀, R₁, hR₀, hfix₀, hR₁, hfix₁, _, _, hR⟩ :=
    c.toOpenPartialHomeomorph.exists_homeomorph_smoothAbs_quadrant_collar
      e.toOpenPartialHomeomorph hA hB hc hε hraw hstrip
  refine ⟨R₀, R₁, hR₀, hfix₀, hR₁, hfix₁, ?_⟩
  intro Q W hW hQ
  obtain ⟨U, hU, hUs, hmem, heq⟩ := hR Q W hW hQ
  let F := DifferentialGeometry.Topology.PartialDiffeomorph.restrict c U hU
  have hFs : F.source = U := by
    change c.source ∩ U = U
    exact inter_eq_right.mpr hUs
  refine ⟨F, ?_, ?_⟩
  · intro x
    rw [hFs]
    exact hmem x
  · intro x hx
    exact (heq x (hFs ▸ hx)).symm

end PartialDiffeomorph

namespace OpenPartialHomeomorph

private theorem mem_smoothAbsQuadrantSet_iff_on_strip
    {X P : Type*} [TopologicalSpace X] [TopologicalSpace P]
    (e : OpenPartialHomeomorph X (P × (ℝ × ℝ))) {A : Set X} {ε : ℝ} (hε : 0 < ε)
    (hraw : ∀ p ∈ e.target, e.symm p ∈ A ↔ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2)
    (hstrip : {p : P × (ℝ × ℝ) | 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε} ⊆
      e.target) (x : X) :
    x ∈ e.smoothAbsQuadrantSet A ε ↔ x ∈ A ∧
      ∀ p : P × (ℝ × ℝ), 0 ≤ p.2.1 → 0 ≤ p.2.2 → p.2.1 + p.2.2 ≤ ε → e.symm p = x →
        Real.smoothAbs ε (p.2.1 - p.2.2) ≤ p.2.1 + p.2.2 := by
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · by_cases hxs : x ∈ e.source
      · have hh := (e.mem_smoothAbsQuadrantSet_iff A ε hxs).mp hx
        have hl := (Real.smoothAbs.sub_abs_mem_Icc hε ((e x).2.1 - (e x).2.2)).1
        have hn := neg_abs_le ((e x).2.1 - (e x).2.2)
        have hp := le_abs_self ((e x).2.1 - (e x).2.2)
        have hq : 0 ≤ (e x).2.1 ∧ 0 ≤ (e x).2.2 := by constructor <;> linarith
        have ha := (hraw (e x) (e.map_source hxs)).mpr hq
        rwa [e.left_inv hxs] at ha
      · exact (e.mem_smoothAbsQuadrantSet_iff_of_notMem_source A ε hxs).mp hx
    · intro p hu hv hs heq
      have hpt := hstrip ⟨hu, hv, hs⟩
      have hxs : x ∈ e.source := heq ▸ e.map_target hpt
      have he : e x = p := by rw [← heq, e.right_inv hpt]
      simpa only [he] using (e.mem_smoothAbsQuadrantSet_iff A ε hxs).mp hx
  · rintro ⟨hx, hsupport⟩
    by_cases hxs : x ∈ e.source
    · apply (e.mem_smoothAbsQuadrantSet_iff A ε hxs).mpr
      have hq : 0 ≤ (e x).2.1 ∧ 0 ≤ (e x).2.2 := by
        apply (hraw (e x) (e.map_source hxs)).mp
        rwa [e.left_inv hxs]
      by_cases hs : (e x).2.1 + (e x).2.2 ≤ ε
      · exact hsupport (e x) hq.1 hq.2 hs (e.left_inv hxs)
      · calc
          Real.smoothAbs ε ((e x).2.1 - (e x).2.2) =
              Real.smoothAbs ε |(e x).2.1 - (e x).2.2| := (Real.smoothAbs.abs hε.ne' _).symm
          _ ≤ Real.smoothAbs ε ((e x).2.1 + (e x).2.2) := by
            apply (Real.smoothAbs.strictMonoOn_Ici hε).monotoneOn
              (show |(e x).2.1 - (e x).2.2| ∈ Ici 0 from abs_nonneg ((e x).2.1 - (e x).2.2))
              (show (e x).2.1 + (e x).2.2 ∈ Ici 0 from add_nonneg hq.1 hq.2)
            rw [abs_le]
            constructor <;> linarith [hq.1, hq.2]
          _ = (e x).2.1 + (e x).2.2 := Real.smoothAbs.eq_self_of_le hε (le_of_not_ge hs)
    · exact (e.mem_smoothAbsQuadrantSet_iff_of_notMem_source A ε hxs).mpr hx

theorem smoothAbsQuadrantSet_eq_of_eqOn_symm
    {X P : Type*} [TopologicalSpace X] [TopologicalSpace P]
    (e₀ e₁ : OpenPartialHomeomorph X (P × (ℝ × ℝ))) {A : Set X} {ε : ℝ} (hε : 0 < ε)
    (hraw₀ : ∀ p ∈ e₀.target, e₀.symm p ∈ A ↔ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2)
    (hraw₁ : ∀ p ∈ e₁.target, e₁.symm p ∈ A ↔ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2)
    (hstrip₀ : {p : P × (ℝ × ℝ) | 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε} ⊆
      e₀.target)
    (hstrip₁ : {p : P × (ℝ × ℝ) | 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε} ⊆
      e₁.target)
    (hinv : EqOn e₀.symm e₁.symm
      {p : P × (ℝ × ℝ) | 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε}) :
    e₀.smoothAbsQuadrantSet A ε = e₁.smoothAbsQuadrantSet A ε := by
  ext x
  rw [mem_smoothAbsQuadrantSet_iff_on_strip e₀ hε hraw₀ hstrip₀ x,
    mem_smoothAbsQuadrantSet_iff_on_strip e₁ hε hraw₁ hstrip₁ x]
  apply and_congr_right
  intro _
  constructor
  · intro h p hu hv hs hp
    exact h p hu hv hs ((hinv ⟨hu, hv, hs⟩).trans hp)
  · intro h p hu hv hs hp
    exact h p hu hv hs ((hinv ⟨hu, hv, hs⟩).symm.trans hp)

end OpenPartialHomeomorph
