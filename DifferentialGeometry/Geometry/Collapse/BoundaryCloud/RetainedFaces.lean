import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Compactness.Compact

/-!
# Retained internal torus faces and relative removal (blueprint 207B, BCG07, B:9471–9620)

Row-local kernels:
* `mem_preimage_iff_of_fiber` — every `π_j` retains the WHOLE physical block, so the GLOBAL frontier
  equation `E⁻¹{(u_b, v_b) ∈ T}` is saturated by whole fibres of `π_j E`.
* `eq_of_isClosed_of_isOpen_subtype` — a nonempty closed fibre that is relatively open in the
  connected torus `H_b` is all of `H_b`.
* `union_union_compl_interior`, `disjoint_compl_interior_of_isOpen_subset`,
  `isCompact_compl_interior` — the set algebra of `M₁ = M \ int(Z ∪ C)` in (BCG07.a): together with
  `Z ∪ C` it is the whole carrier, it misses any open `N ⊆ C` (so `M₁ ⊂ {d ≥ 35}`), and it is compact.
-/

set_option autoImplicit false
open Set

namespace DifferentialGeometry.Geometry.Collapse.BoundaryCloud

/-- Whole-fibre saturation of a global block equation: if the block functional `J` factors through
`π`, membership in `E⁻¹(J⁻¹ T)` is constant on the fibres of `π ∘ E`. -/
theorem mem_preimage_iff_of_fiber {M H B K : Type*} {E : M → H} (π : H → B) {J : H → K}
    (J' : B → K) (hJ : ∀ h, J h = J' (π h)) {T : Set K} {p q : M} (hpq : π (E p) = π (E q)) :
    p ∈ E ⁻¹' (J ⁻¹' T) ↔ q ∈ E ⁻¹' (J ⁻¹' T) := by
  simp only [mem_preimage, hJ, hpq]

variable {M : Type*} [TopologicalSpace M]

/-- BCG07: a nonempty closed subset of the connected set `Hs` that is relatively open in `Hs` is
all of `Hs` (a slim fibre meeting the cusp torus `H_b` is the whole torus). -/
theorem eq_of_isClosed_of_isOpen_subtype {Hs F : Set M} (hFH : F ⊆ Hs) (hconn : IsConnected Hs)
    (hne : F.Nonempty) (hclosed : IsClosed F)
    (hopen : IsOpen ((Subtype.val : Hs → M) ⁻¹' F)) : F = Hs := by
  have : ConnectedSpace Hs := isConnected_iff_connectedSpace.mp hconn
  obtain ⟨x, hx⟩ := hne
  have hclopen : IsClopen ((Subtype.val : Hs → M) ⁻¹' F) :=
    ⟨hclosed.preimage continuous_subtype_val, hopen⟩
  have huniv := hclopen.eq_univ ⟨⟨x, hFH hx⟩, hx⟩
  refine Subset.antisymm hFH fun y hy => ?_
  have : (⟨y, hy⟩ : Hs) ∈ (Subtype.val : Hs → M) ⁻¹' F := by rw [huniv]; exact mem_univ _
  exact this

/-- (BCG07.a): `Z ∪ C` together with `M₁ = M \ int(Z ∪ C)` is the whole carrier. -/
theorem union_union_compl_interior (Z C : Set M) : Z ∪ C ∪ (interior (Z ∪ C))ᶜ = univ := by
  refine eq_univ_of_forall fun x => ?_
  by_cases hx : x ∈ interior (Z ∪ C)
  · exact Or.inl (interior_subset hx)
  · exact Or.inr hx

/-- (BCG07): an open neighbourhood contained in a removed core does not meet `M₁`. -/
theorem disjoint_compl_interior_of_isOpen_subset {Z C N : Set M} (hN : IsOpen N) (hNC : N ⊆ C) :
    Disjoint N (interior (Z ∪ C))ᶜ :=
  disjoint_compl_right_iff_subset.mpr
    (interior_maximal (hNC.trans subset_union_right) hN)

/-- (BCG07): `M₁` is compact, being closed in the compact carrier. -/
theorem isCompact_compl_interior [CompactSpace M] (S : Set M) : IsCompact (interior S)ᶜ :=
  isOpen_interior.isClosed_compl.isCompact

end DifferentialGeometry.Geometry.Collapse.BoundaryCloud
