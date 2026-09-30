import DifferentialGeometry.Topology.Attachment.Basic
import DifferentialGeometry.Topology.Manifold.Attachment.AdjunctionSeparation
import DifferentialGeometry.Topology.Manifold.BallChart.Defs

open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : Type*} [TopologicalSpace K]
  {n : ℕ} {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace K N]

abbrev ConnectedSumQuotient (c : BallChart n I M) (d : BallChart n J N)
    (a : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  AdjunctionSpace c.boundaryMap (d.boundaryMap ∘ a)

namespace ConnectedSumQuotient

variable (c : BallChart n I M) (d : BallChart n J N)
  (a : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ≃ₜ
    Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)

def mk : c.Punctured ⊕ d.Punctured → ConnectedSumQuotient c d a :=
  adjunctionMk c.boundaryMap (d.boundaryMap ∘ a)

def inl : c.Punctured → ConnectedSumQuotient c d a :=
  adjunctionCell c.boundaryMap (d.boundaryMap ∘ a)

def inr : d.Punctured → ConnectedSumQuotient c d a :=
  adjunctionLower (d.boundaryMap ∘ a)

@[simp]
theorem mk_inl (x : c.Punctured) : mk c d a (Sum.inl x) = inl c d a x := rfl

@[simp]
theorem mk_inr (x : d.Punctured) : mk c d a (Sum.inr x) = inr c d a x := rfl

theorem boundary_eq (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    inl c d a (c.boundaryMap z) = inr c d a (d.boundaryMap (a z)) :=
  adjunction_coherence c.boundaryMap (d.boundaryMap ∘ a) z

theorem continuous_inl : Continuous (inl c d a) :=
  continuous_adjunctionCell c.boundaryMap (d.boundaryMap ∘ a)

theorem continuous_inr : Continuous (inr c d a) :=
  continuous_adjunctionLower c.boundaryMap (d.boundaryMap ∘ a)

theorem inl_injective : Function.Injective (inl c d a) :=
  Manifold.Attachment.adjunctionCell_injective c.boundaryMap (d.boundaryMap ∘ a)
    (d.boundaryMap_injective.comp a.injective)

theorem inr_injective : Function.Injective (inr c d a) :=
  Manifold.Attachment.adjunctionLower_injective c.boundaryMap (d.boundaryMap ∘ a)
    c.boundaryMap_injective

theorem isQuotientMap_mk : _root_.Topology.IsQuotientMap (mk c d a) :=
  isQuotientMap_adjunctionMk c.boundaryMap (d.boundaryMap ∘ a)

theorem jointly_surjective (z : ConnectedSumQuotient c d a) :
    (∃ x, inl c d a x = z) ∨ (∃ y, inr c d a y = z) := by
  have h := Manifold.Attachment.adjunction_inclusions_cover c.boundaryMap (d.boundaryMap ∘ a)
  change z ∈ Set.range (inl c d a) ∪ Set.range (inr c d a)
  rw [show Set.range (inl c d a) ∪ Set.range (inr c d a) = Set.univ from h]
  exact Set.mem_univ z

theorem inl_eq_inr_iff (p : c.Punctured) (q : d.Punctured) :
    inl c d a p = inr c d a q ↔
      ∃ z, c.boundaryMap z = p ∧ d.boundaryMap (a z) = q :=
  adjunction_cell_eq_lower_iff c.boundaryMap (d.boundaryMap ∘ a)
    (d.boundaryMap_injective.comp a.injective) p q

theorem inl_ne_inr_of_forall (p : c.Punctured) (q : d.Punctured)
    (h : ∀ z, c.boundaryMap z = p → d.boundaryMap (a z) ≠ q) :
    inl c d a p ≠ inr c d a q := by
  intro hpq
  obtain ⟨z, hz, hz'⟩ := (inl_eq_inr_iff c d a p q).mp hpq
  exact h z hz hz'

theorem nonempty_sphere_of_neZero [NeZero n] :
    Nonempty (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  let ⟨z, hz⟩ := NormedSpace.sphere_nonempty.mpr (by norm_num : (0:ℝ) ≤ 1)
  ⟨⟨z, hz⟩⟩

instance instT2Space [T2Space M] [T2Space N] : T2Space (ConnectedSumQuotient c d a) :=
  DifferentialGeometry.Topology.Manifold.Attachment.adjunction_t2Space c.boundaryMap
    (d.boundaryMap ∘ a)
    c.boundaryMap_injective (d.boundaryMap_injective.comp a.injective)
    c.continuous_boundaryMap (d.continuous_boundaryMap.comp a.continuous)

instance instCompactSpace [CompactSpace c.Punctured] [CompactSpace d.Punctured] :
    CompactSpace (ConnectedSumQuotient c d a) :=
  Quot.compactSpace

instance instConnectedSpace [ConnectedSpace c.Punctured] [ConnectedSpace d.Punctured]
    [Nonempty (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)] :
    ConnectedSpace (ConnectedSumQuotient c d a) :=
  DifferentialGeometry.Topology.connectedSpace_adjunctionSpace c.boundaryMap
    (d.boundaryMap ∘ a)

instance instPathConnectedSpace [PathConnectedSpace c.Punctured]
    [PathConnectedSpace d.Punctured]
    [Nonempty (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)] :
    PathConnectedSpace (ConnectedSumQuotient c d a) :=
  DifferentialGeometry.Topology.pathConnectedSpace_adjunctionSpace c.boundaryMap
    (d.boundaryMap ∘ a)

theorem isOpen_image_inl {U : Set c.Punctured} (hU : IsOpen U)
    (hdisj : ∀ z, c.boundaryMap z ∉ U) :
    IsOpen (inl c d a '' U) := by
  have hcoe : (adjunctionMk c.boundaryMap (d.boundaryMap ∘ a)) ⁻¹'
      (inl c d a '' U) = Sum.inl '' U := by
    ext s
    constructor
    · rintro ⟨p, hpU, hp⟩
      cases s with
      | inl x =>
          refine ⟨x, ?_, rfl⟩
          rwa [← (inl_injective c d a hp)]
      | inr y =>
          obtain ⟨z, hz, -⟩ := (inl_eq_inr_iff c d a p y).mp hp
          exact absurd (hz.symm ▸ hpU) (hdisj z)
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  change IsOpen[TopologicalSpace.coinduced
    (adjunctionMk c.boundaryMap (d.boundaryMap ∘ a)) inferInstance] (inl c d a '' U)
  rw [isOpen_coinduced, hcoe]
  exact isOpenMap_inl U hU

theorem isOpen_image_inr {V : Set d.Punctured} (hV : IsOpen V)
    (hdisj : ∀ z, d.boundaryMap z ∉ V) :
    IsOpen (inr c d a '' V) := by
  have hcoe : (adjunctionMk c.boundaryMap (d.boundaryMap ∘ a)) ⁻¹'
      (inr c d a '' V) = Sum.inr '' V := by
    ext s
    constructor
    · rintro ⟨q, hqV, hq⟩
      cases s with
      | inr y =>
          refine ⟨y, ?_, rfl⟩
          rwa [← (inr_injective c d a hq)]
      | inl x =>
          obtain ⟨z, -, hz⟩ := (inl_eq_inr_iff c d a x q).mp hq.symm
          exact absurd (hz.symm ▸ hqV) (hdisj (a z))
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
  change IsOpen[TopologicalSpace.coinduced
    (adjunctionMk c.boundaryMap (d.boundaryMap ∘ a)) inferInstance] (inr c d a '' V)
  rw [isOpen_coinduced, hcoe]
  exact isOpenMap_inr V hV

theorem isOpen_image_union {U : Set c.Punctured} {V : Set d.Punctured} (hU : IsOpen U)
    (hV : IsOpen V) (hdisjU : ∀ z, c.boundaryMap z ∉ U)
    (hdisjV : ∀ z, d.boundaryMap z ∉ V) :
    IsOpen (inl c d a '' U ∪ inr c d a '' V) :=
  (isOpen_image_inl c d a hU hdisjU).union (isOpen_image_inr c d a hV hdisjV)

end ConnectedSumQuotient

theorem frontier_half_le_subset_eq_zero {α : Type*} [TopologicalSpace α] (f : α → ℝ)
    (hf : Continuous f) : frontier {p : α | 0 ≤ f p} ⊆ {p | f p = 0} := by
  intro p hp
  have hcl : p ∈ closure {q : α | 0 ≤ f q} := frontier_subset_closure hp
  have hcl' : p ∈ closure ({q : α | 0 ≤ f q}ᶜ) := by
    have h : p ∈ frontier ({q : α | 0 ≤ f q}ᶜ) := by
      rwa [frontier_compl]
    exact frontier_subset_closure h
  have hge : 0 ≤ f p :=
    closure_minimal (fun q hq => hq) (isClosed_le continuous_const hf) hcl
  have hle : f p ≤ 0 := by
    refine closure_minimal (fun q hq => ?_) (isClosed_le hf continuous_const) hcl'
    have hq' : ¬ (0 ≤ f q) := hq
    exact le_of_lt (not_le.mp hq')
  exact le_antisymm hle hge

end DifferentialGeometry.Topology
