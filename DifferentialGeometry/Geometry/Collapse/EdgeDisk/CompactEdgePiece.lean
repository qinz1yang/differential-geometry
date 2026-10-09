import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Algebra.Order.Group
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# FDC02/FDC03 kernels: the compact edge piece and the relative remainder

Frozen blueprint master207B, theorem `thm:fibration-actual-compact-edge-piece` (FDC02, lines
7246–7283) and theorem `thm:fibration-actual-circle-remainder` (FDC03, lines 7285–7365).

* `isCompact_of_weak_limit_replacement` (FDC02): the edge piece `S = M₂ ∩ X₂` lies in the closed set
  `K = M₂ ∩ V` and every point of it has a witnessing edge index with `v_i = R_i`, `|u_i| < c_i`
  (EDP02). If every point of `K` satisfying the WEAK inequalities `v_i = R_i`, `|u_i| ≤ c_i` for some
  index is in `S` (the limit step: GAF06 with `≤`, (EZ), and FDC01's replacement index), then `S` is
  compact. Finiteness of the index set is the blueprint's "after a subsequence one selected index
  witnesses the base condition for every `q_n`"; the weak inequalities are the limits.
  `isCompact_image_of_weak_limit_replacement` adds compactness of the base `C₂ = f(S)`.
* `relativeRemoval_union_inter` (FDC03, (Last)/(LastFaces) at set level, also ZSP05's (RC)): in the
  ambient `Y = M₂`, for the closed `A = M^edge` the remainder `M₃ = Y \ int_Y A` satisfies
  `Y = A ∪ M₃`, `A ∩ M₃ = frontier_Y A`, `M₃` is closed, and `A`, `M₃` have disjoint interiors.
* `relativeRemoval_saturated` (FDC03): if `A = f⁻¹(A')` and its relative interior is cut out by a
  fibre-constant condition `f ∈ P` (for the edge piece: `T < 4Δ`), the remainder is saturated.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace DifferentialGeometry.Geometry.Collapse.EdgeDisk

/-- **FDC02 kernel.** A set described inside a closed set `K` of a compact space by finitely many
strict witnessing conditions `v_i = R_i, |u_i| < c_i`, and containing every point of `K` that
satisfies the corresponding weak conditions, is compact. -/
theorem isCompact_of_weak_limit_replacement {M ι : Type*} [TopologicalSpace M] [CompactSpace M]
    [Finite ι] {S K : Set M} (hK : IsClosed K) (hSK : S ⊆ K) (v u : ι → M → ℝ)
    (hv : ∀ i, Continuous (v i)) (hu : ∀ i, Continuous (u i)) (R c : ι → ℝ)
    (hwit : ∀ x ∈ S, ∃ i, v i x = R i ∧ |u i x| < c i)
    (hrepl : ∀ x ∈ K, ∀ i, v i x = R i → |u i x| ≤ c i → x ∈ S) : IsCompact S := by
  have heq : S = K ∩ ⋃ i, {x | v i x = R i ∧ |u i x| ≤ c i} := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, h1, h2⟩ := hwit x hx
      exact ⟨hSK hx, mem_iUnion.mpr ⟨i, h1, h2.le⟩⟩
    · rintro ⟨hxK, hx⟩
      obtain ⟨i, h1, h2⟩ := mem_iUnion.mp hx
      exact hrepl x hxK i h1 h2
  have hclosed : IsClosed (K ∩ ⋃ i, {x | v i x = R i ∧ |u i x| ≤ c i}) :=
    hK.inter (isClosed_iUnion_of_finite fun i =>
      (isClosed_eq (hv i) continuous_const).inter (isClosed_le (hu i).abs continuous_const))
  rw [heq]
  exact hclosed.isCompact

/-- **FDC02 kernel with its base.** Under the same hypotheses the image of the edge piece under a
continuous base map is compact. -/
theorem isCompact_image_of_weak_limit_replacement {M B ι : Type*} [TopologicalSpace M]
    [CompactSpace M] [TopologicalSpace B] [Finite ι] {S K : Set M} (hK : IsClosed K) (hSK : S ⊆ K)
    (v u : ι → M → ℝ) (hv : ∀ i, Continuous (v i)) (hu : ∀ i, Continuous (u i)) (R c : ι → ℝ)
    (hwit : ∀ x ∈ S, ∃ i, v i x = R i ∧ |u i x| < c i)
    (hrepl : ∀ x ∈ K, ∀ i, v i x = R i → |u i x| ≤ c i → x ∈ S) {f : M → B} (hf : Continuous f) :
    IsCompact S ∧ IsCompact (f '' S) := by
  have hS := isCompact_of_weak_limit_replacement hK hSK v u hv hu R c hwit hrepl
  exact ⟨hS, hS.image hf⟩

/-- **FDC03 kernel (relative removal).** Removing the interior of a closed set `A` from the ambient
space leaves a closed remainder that covers the rest, meets `A` exactly in its frontier, and has
interior disjoint from that of `A`. -/
theorem relativeRemoval_union_inter {Y : Type*} [TopologicalSpace Y] {A : Set Y}
    (hA : IsClosed A) :
    A ∪ (interior A)ᶜ = univ ∧ A ∩ (interior A)ᶜ = frontier A ∧ IsClosed (interior A)ᶜ ∧
      Disjoint (interior A) (interior (interior A)ᶜ) := by
  refine ⟨?_, ?_, isOpen_interior.isClosed_compl, ?_⟩
  · apply eq_univ_of_forall
    intro x
    by_cases hx : x ∈ A
    · exact Or.inl hx
    · exact Or.inr fun hxi => hx (interior_subset hxi)
  · rw [hA.frontier_eq]
    rfl
  · rw [interior_compl]
    exact disjoint_compl_right.mono_left subset_closure

/-- **FDC03 kernel (saturation of the remainder).** If `A = f⁻¹(A')` and its interior is cut out
by a fibre-constant condition `f ∈ P`, then the remainder `(interior A)ᶜ` is a full preimage. -/
theorem relativeRemoval_saturated {Y Z : Type*} [TopologicalSpace Y] (f : Y → Z) {A : Set Y}
    {A' P : Set Z} (hA : A = f ⁻¹' A') (hint : interior A = A ∩ f ⁻¹' P) :
    (interior A)ᶜ = f ⁻¹' (A' ∩ P)ᶜ := by
  rw [hint, hA, ← preimage_inter, preimage_compl]

end DifferentialGeometry.Geometry.Collapse.EdgeDisk
