import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalDiffeomorphEmbedding
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import DifferentialGeometry.Topology.SphereSeparation.Bicollar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckAxialReflection
import DifferentialGeometry.Topology.SphereSeparation.SourceTheorems

section

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature (RealTimeInterval)
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology (ThreeSpace)
open DifferentialGeometry.Topology (SphereTwo)
open DifferentialGeometry.Topology.SphereSeparation (AxialInterval axialZero)

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {eps t : ℝ} {x : M}

def StrongNeck.bicollar (nk : StrongNeck S eps x t) :
    SphereTwo × AxialInterval eps⁻¹ → M :=
  fun z => nk.map (z.1, (z.2 : ℝ))

theorem StrongNeck.bicollar_isSmoothEmbedding (nk : StrongNeck S eps x t) :
    Manifold.IsSmoothEmbedding IC I3 ∞ nk.bicollar := by
  let inc : PartialDiffeomorph IC IC (SphereTwo × AxialInterval eps⁻¹) Cylinder ∞ :=
    DifferentialGeometry.Topology.PartialDiffeomorph.prod
      (Diffeomorph.refl I2 SphereTwo ∞).toPartialDiffeomorph
      (DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal
        (I := 𝓘(ℝ, ℝ)) (AxialInterval eps⁻¹)
        ⟨axialZero (inv_pos.mpr nk.eps_pos)⟩)
  have hsource (z : SphereTwo × AxialInterval eps⁻¹) :
      (z.1, (z.2 : ℝ)) ∈ nk.map.source :=
    nk.domain ⟨Set.mem_univ _, z.2.property⟩
  have hlocal : IsLocalDiffeomorph IC I3 ∞ nk.bicollar := by
    intro z
    refine ⟨inc.trans nk.map, ?_, ?_⟩
    · change (True ∧ True) ∧ (z.1, (z.2 : ℝ)) ∈ nk.map.source
      exact ⟨⟨trivial, trivial⟩, hsource z⟩
    · intro p _
      rfl
  apply KappaSolutions.localDiffeomorph_isSmoothEmbedding_of_injective hlocal
  intro z w hzw
  have hcoords : (z.1, (z.2 : ℝ)) = (w.1, (w.2 : ℝ)) :=
    nk.map.toPartialEquiv.injOn (hsource z) (hsource w) hzw
  apply Prod.ext
  · exact congrArg (fun p : Cylinder => p.1) hcoords
  · exact Subtype.ext (congrArg (fun p : Cylinder => p.2) hcoords)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature (RealTimeInterval)
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology (ThreeSpace)
open DifferentialGeometry.Topology (SphereTwo)
open DifferentialGeometry.Topology.SphereSeparation

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {eps t : ℝ} {x : M}

namespace StrongNeck

def bicollarSides (nk : StrongNeck S eps x t)
    (ψ : Diffeomorph I3 I3 M ThreeSpace ∞)
    (c : AxialInterval eps⁻¹) : SphereSides (sliceImage nk.bicollar c) :=
  bicollarSliceSidesOpenThreeSpace nk.bicollar nk.bicollar_isSmoothEmbedding ψ c

theorem axialReflection_bicollar (nk : StrongNeck S eps x t) :
    nk.axialReflection.bicollar = nk.bicollar ∘ reverseAxialSource eps⁻¹ := by
  funext p
  change nk.map (cylinderAxialReflection (p.1, (p.2 : ℝ))) =
    nk.map (p.1, -(p.2 : ℝ))
  rw [cylinderAxialReflection_apply]

theorem axialReflection_bicollar_zero_slice (nk : StrongNeck S eps x t) :
    sliceImage nk.axialReflection.bicollar (axialZero (inv_pos.mpr nk.eps_pos)) =
      sliceImage nk.bicollar (axialZero (inv_pos.mpr nk.eps_pos)) := by
  have hzero : ∀ p : SphereTwo,
      nk.axialReflection.bicollar (p, axialZero (inv_pos.mpr nk.eps_pos)) =
        nk.bicollar (p, axialZero (inv_pos.mpr nk.eps_pos)) := by
    intro p
    change nk.map (cylinderAxialReflection (p, 0)) = nk.map (p, 0)
    rw [cylinderAxialReflection_apply, neg_zero]
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hpzero : p.2 = axialZero (inv_pos.mpr nk.eps_pos) := hp.2
    refine ⟨(p.1, axialZero (inv_pos.mpr nk.eps_pos)), ⟨mem_univ _, rfl⟩, ?_⟩
    simpa only [← hpzero] using (hzero p.1).symm
  · rintro ⟨p, hp, rfl⟩
    have hpzero : p.2 = axialZero (inv_pos.mpr nk.eps_pos) := hp.2
    refine ⟨(p.1, axialZero (inv_pos.mpr nk.eps_pos)), ⟨mem_univ _, rfl⟩, ?_⟩
    simpa only [← hpzero] using hzero p.1

theorem axialReflection_bicollar_zero_sides (nk : StrongNeck S eps x t)
    (ψ : Diffeomorph I3 I3 M ThreeSpace ∞) :
    (nk.axialReflection.bicollarSides ψ (axialZero (inv_pos.mpr nk.eps_pos))).compactSide =
        (nk.bicollarSides ψ (axialZero (inv_pos.mpr nk.eps_pos))).compactSide ∧
      (nk.axialReflection.bicollarSides ψ (axialZero (inv_pos.mpr nk.eps_pos))).endSide =
        (nk.bicollarSides ψ (axialZero (inv_pos.mpr nk.eps_pos))).endSide := by
  let d := nk.bicollarSides ψ (axialZero (inv_pos.mpr nk.eps_pos))
  let d' := nk.axialReflection.bicollarSides ψ (axialZero (inv_pos.mpr nk.eps_pos))
  apply d.side_sets_unique_of_core_properties d'.compactSide d'.endSide
    d'.isOpen_compactSide d'.isOpen_endSide
    d'.isConnected_compactSide d'.isConnected_endSide d'.disjoint
  · exact d'.union_eq_compl.trans (congrArg compl nk.axialReflection_bicollar_zero_slice)
  · exact d'.isCompact_closure_compactSide
  · exact d'.not_isCompact_closure_endSide

theorem axialReflection_bicollar_lower_half (nk : StrongNeck S eps x t) :
    lowerHalfImage nk.axialReflection.bicollar (axialZero (inv_pos.mpr nk.eps_pos)) =
      upperHalfImage nk.bicollar (axialZero (inv_pos.mpr nk.eps_pos)) := by
  have hzero : DifferentialGeometry.Topology.SphereSeparation.axialReflection eps⁻¹
      (axialZero (inv_pos.mpr nk.eps_pos)) =
      axialZero (inv_pos.mpr nk.eps_pos) := by
    apply Subtype.ext
    exact neg_zero
  rw [axialReflection_bicollar, lowerHalfImage, Set.image_comp,
    reverseAxialSource_image_lowerHalfDomain, hzero]
  rfl

theorem axialReflection_bicollar_upper_half (nk : StrongNeck S eps x t) :
    upperHalfImage nk.axialReflection.bicollar (axialZero (inv_pos.mpr nk.eps_pos)) =
      lowerHalfImage nk.bicollar (axialZero (inv_pos.mpr nk.eps_pos)) := by
  have hzero : DifferentialGeometry.Topology.SphereSeparation.axialReflection eps⁻¹
      (axialZero (inv_pos.mpr nk.eps_pos)) =
      axialZero (inv_pos.mpr nk.eps_pos) := by
    apply Subtype.ext
    exact neg_zero
  rw [axialReflection_bicollar, upperHalfImage, Set.image_comp,
    reverseAxialSource_image_upperHalfDomain, hzero]
  rfl

theorem exists_axially_oriented (nk : StrongNeck S eps x t)
    (ψ : Diffeomorph I3 I3 M ThreeSpace ∞) :
    ∃ neck : StrongNeck S eps x t,
      (neck = nk ∨ neck = nk.axialReflection) ∧
        IsAxiallyOriented neck.bicollar (neck.bicollarSides ψ) := by
  let _ : T2Space M := ψ.symm.toHomeomorph.t2Space
  have ha : 0 < eps⁻¹ := inv_pos.mpr nk.eps_pos
  rcases (bicollar_sides_openThreeSpace ha nk.bicollar
    nk.bicollar_isSmoothEmbedding ψ).or with h | h
  · refine ⟨nk, Or.inl rfl, axiallyOriented_of_atZero ha nk.bicollar
      nk.bicollar_isSmoothEmbedding (nk.bicollarSides ψ) ?_⟩
    exact ⟨h.1, h.2⟩
  · refine ⟨nk.axialReflection, Or.inr rfl,
      axiallyOriented_of_atZero ha nk.axialReflection.bicollar
        nk.axialReflection.bicollar_isSmoothEmbedding
        (nk.axialReflection.bicollarSides ψ) ?_⟩
    obtain ⟨hcompact, hend⟩ := nk.axialReflection_bicollar_zero_sides ψ
    constructor
    · rw [nk.axialReflection_bicollar_lower_half, hcompact]
      exact h.2
    · rw [nk.axialReflection_bicollar_upper_half, hend]
      exact h.1

theorem bicollar_closed_slab (nk : StrongNeck S eps x t)
    (a b : AxialInterval eps⁻¹) :
    closedSlabImage nk.bicollar a b =
      nk.map '' (Set.univ ×ˢ Set.Icc (a : ℝ) (b : ℝ)) := by
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨(p.1, (p.2 : ℝ)), ⟨mem_univ _, hp.2⟩, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    let c : AxialInterval eps⁻¹ :=
      ⟨p.2, lt_of_lt_of_le a.2.1 hp.2.1, lt_of_le_of_lt hp.2.2 b.2.2⟩
    exact ⟨(p.1, c), ⟨mem_univ _, hp.2⟩, rfl⟩

theorem exists_oriented_slab_decomposition (nk : StrongNeck S eps x t)
    (ψ : Diffeomorph I3 I3 M ThreeSpace ∞) :
    ∃ neck : StrongNeck S eps x t,
      (neck = nk ∨ neck = nk.axialReflection) ∧
        ∀ a b : AxialInterval eps⁻¹, a < b →
          closure (neck.bicollarSides ψ b).compactSide =
              closure (neck.bicollarSides ψ a).compactSide ∪
                neck.map '' (Set.univ ×ˢ Set.Icc (a : ℝ) (b : ℝ)) ∧
          closure (neck.bicollarSides ψ a).compactSide ⊂
              (neck.bicollarSides ψ b).compactSide ∧
          closure (neck.bicollarSides ψ a).compactSide ⊂
              closure (neck.bicollarSides ψ b).compactSide ∧
          (neck.map '' (Set.univ ×ˢ Set.Icc (a : ℝ) (b : ℝ)))ᶜ =
              (neck.bicollarSides ψ a).compactSide ∪ (neck.bicollarSides ψ b).endSide ∧
          Disjoint (neck.bicollarSides ψ a).compactSide
            (neck.bicollarSides ψ b).endSide := by
  let _ : T2Space M := ψ.symm.toHomeomorph.t2Space
  obtain ⟨neck, hneck, haxial⟩ := nk.exists_axially_oriented ψ
  refine ⟨neck, hneck, ?_⟩
  intro a b hab
  have ha : 0 < eps⁻¹ := inv_pos.mpr neck.eps_pos
  obtain ⟨_, hslab, hsplit, hstrict, hstrictClosure⟩ :=
    bicollar_order_of_atZero ha neck.bicollar neck.bicollar_isSmoothEmbedding
      (neck.bicollarSides ψ) ⟨(haxial.at_zero ha).1, (haxial.at_zero ha).2⟩ hab
  rw [neck.bicollar_closed_slab] at hslab hsplit
  exact ⟨hslab, hstrict, hstrictClosure, hsplit.1, hsplit.2⟩

end StrongNeck

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end
