/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodCellBoundary
import DifferentialGeometry.Topology.Attachment.Union

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open Classical in
theorem exists_derivedNeighborhoodCell_attachment
    {n : ℕ} (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 2) K) (hLK : L.faces ⊆ K.faces)
    {s : Finset E} (hs : s ∈ K.faces) (hsL : s ∉ L.faces)
    (hproper : ∀ t : Finset E, t.Nonempty → t ⊂ s → t ∈ L.faces)
    {P : Set F} (A : Set P) {g : F → E}
    (hg : IsPLHomeomorphOn g P (derivedNeighborhoodCell K s).space)
    (htrace : (fun z : P => g z.val) '' A =
      (derivedNeighborhoodCell K s).space ∩ (derivedNeighborhood K L).space) :
    ∃ φ : A → (derivedNeighborhood K L).space, IsClosedEmbedding φ ∧
      (∀ z, (φ z : E) = g z.val.val) ∧
      (∀ z, (φ z : E) ∈ (boundaryComplex (n + 2) (derivedNeighborhood K L)).space) ∧
      ∃ e : AdjunctionSpace (Subtype.val : A → P) φ ≃ₜ
          (derivedNeighborhood K (subcomplexGeneratedBy K (insert s L.faces))).space,
        (∀ x, (e (adjunctionLower φ x) : E) = x) ∧
        ∀ z, (e (adjunctionCell Subtype.val φ z) : E) = g z.val := by
  classical
  let C := derivedNeighborhoodCell K s
  let N := derivedNeighborhood K L
  let _ : Finite N.faces := (derivedNeighborhood_faces_finite K L).to_subtype
  have hP : IsPLBall (n + 2) P :=
    (hK.isPLBall_derivedNeighborhoodCell hs).of_isPLHomeomorphOn hg.symm
  let _ : CompactSpace P := isCompact_iff_compactSpace.mp hP.isPolyhedron.isCompact
  let c : P → E := fun z => g z.val
  have hc : Continuous c :=
    continuousOn_iff_continuous_domRestrict.mp hg.isPiecewiseAffineOn.continuousOn
  have hci : Function.Injective c := fun x y h =>
    Subtype.ext (hg.bijOn.injOn x.property y.property h)
  have hpre (z : P) : c z ∈ N.space ↔ z ∈ A := by
    constructor
    · intro hz
      have hx : c z ∈ c '' A :=
        htrace.symm ▸ ⟨hg.bijOn.mapsTo z.property, hz⟩
      obtain ⟨w, hw, hwz⟩ := hx
      exact hci hwz ▸ hw
    · intro hz
      exact (htrace ▸ (mem_image_of_mem c hz)).2
  have hclosed : IsClosed N.space := (isPolyhedron_space N).isClosed
  have hA : IsClosed A := by
    have heq : A = c ⁻¹' N.space := Set.ext fun z => (hpre z).symm
    rw [heq]
    exact hclosed.preimage hc
  let _ : CompactSpace A := isCompact_iff_compactSpace.mp hA.isCompact
  let φ : A → N.space := fun z => ⟨c z.val, (hpre z.val).mpr z.property⟩
  have hφcont : Continuous φ := (hc.comp continuous_subtype_val).subtype_mk _
  have hφinj : Function.Injective φ := fun x y h =>
    Subtype.ext (hci (congrArg Subtype.val h))
  have hboundary (z : P) (hz : c z ∈ N.space) : z ∈ range (Subtype.val : A → P) :=
    ⟨⟨z, (hpre z).mp hz⟩, rfl⟩
  let e := adjunctionHomeomorphUnionImage (Subtype.val : A → P) φ c
    (fun _ => rfl) hci hc hboundary hclosed
  have hrange : range c = C.space := by
    apply Subset.antisymm
    · rintro _ ⟨z, rfl⟩
      exact hg.bijOn.mapsTo z.property
    · intro x hx
      obtain ⟨z, hz, hzx⟩ := hg.bijOn.surjOn hx
      exact ⟨⟨z, hz⟩, hzx⟩
  have hnext := derivedNeighborhood_space_of_insert_face K L hLK hs hproper
  have htarget : N.space ∪ range c =
      (derivedNeighborhood K (subcomplexGeneratedBy K (insert s L.faces))).space := by
    rw [hrange, hnext]
    exact union_comm _ _
  refine ⟨φ, hφcont.isClosedEmbedding hφinj, fun _ => rfl, ?_,
    e.trans (Homeomorph.setCongr htarget), ?_, ?_⟩
  · intro z
    apply derivedNeighborhoodCell_inter_subset_boundary_derivedNeighborhood K L hK hLK hs hsL
    exact ⟨hg.bijOn.mapsTo z.val.property, (φ z).property⟩
  · intro x
    exact congrArg Subtype.val
      (adjunctionHomeomorphUnionImage_lower _ φ c (fun _ => rfl) hci hc hboundary hclosed x)
  · intro z
    rfl

end DifferentialGeometry.Topology.PiecewiseLinear
