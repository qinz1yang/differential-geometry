import DifferentialGeometry.Geometry.Boundary.Manifold.CollaredQuotientAtlas
import DifferentialGeometry.Topology.Manifold.InteriorAtlas

open Set Function Topology
open scoped Manifold ContDiff

noncomputable section
set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Boundary

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

universe u v

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {X : Type u} [TopologicalSpace X] [ChartedSpace H X]
variable {ι : Type v} [Finite ι]

namespace CollaredGluing

variable {G : CollaredGluing I X ι}

theorem iUnion_block_subset_boundary [IsManifold I 1 X] :
    (⋃ i, (G.toBoundaryGluing).block i) ⊆ I.boundary X :=
  Set.iUnion_subset fun i => G.block_subset_boundary i

theorem interior_subset_compl_iUnion_block [IsManifold I 1 X] :
    I.interior X ⊆ (⋃ i, (G.toBoundaryGluing).block i)ᶜ := by
  intro x hx
  rw [Set.mem_compl_iff, Set.mem_iUnion]
  rintro ⟨i, hi⟩
  exact (I.disjoint_interior_boundary).le_bot ⟨hx, G.block_subset_boundary i hi⟩

theorem isInteriorPoint_of_mem_interior {x : X} (hx : x ∈ I.interior X) : I.IsInteriorPoint x := by
  rwa [ModelWithCorners.interior] at hx

theorem isOpenEmbedding_quotientMk_interior [IsManifold I 1 X] :
    IsOpenEmbedding (fun x : ↥(I.interior X) =>
      Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) (x : X)) := by
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ ?_
  · exact continuous_quotient_mk'.comp continuous_subtype_val
  · intro x y hxy
    refine Subtype.ext (G.toBoundaryGluing.eq_of_rel_of_notMem (fun i hi => ?_)
      ((Quotient.eq'' (s₁ := G.toBoundaryGluing.setoid)).mp hxy))
    exact G.interior_subset_compl_iUnion_block x.2 (Set.mem_iUnion.mpr ⟨i, hi⟩)
  · intro V hV
    have hopen : IsOpen (I.interior X) := I.isOpen_interior (n := 1) (by norm_num)
    have hV' : IsOpen (Subtype.val '' V) := hopen.isOpenMap_subtype_val V hV
    have hdisj : ∀ i, Disjoint (Subtype.val '' V) ((G.toBoundaryGluing).block i) := fun i =>
      Set.disjoint_left.mpr fun y hy hyb => by
        obtain ⟨v, hv, rfl⟩ := hy
        exact G.interior_subset_compl_iUnion_block v.2 (Set.mem_iUnion.mpr ⟨i, hyb⟩)
    have himg : (fun x : ↥(I.interior X) =>
        Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) (x : X)) '' V
        = Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) '' (Subtype.val '' V) :=
      Set.image_comp _ _ _
    rw [himg]
    exact G.isOpen_quotientMk_image_of_disjoint_blocks hV' hdisj

noncomputable def interiorPiece (G : CollaredGluing I X ι) [IsManifold I 1 X]
    (hne : Nonempty ↥(I.interior X)) :
    OpenPartialHomeomorph ↥(I.interior X) (Quotient G.toBoundaryGluing.setoid) := by
  letI := hne
  exact (G.isOpenEmbedding_quotientMk_interior).toOpenPartialHomeomorph
    (fun x : ↥(I.interior X) => Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) (x : X))

theorem interiorPiece_source [IsManifold I 1 X] (hne : Nonempty ↥(I.interior X)) :
    (G.interiorPiece hne).source = univ := by
  rw [interiorPiece]
  exact IsOpenEmbedding.toOpenPartialHomeomorph_source _ _

theorem interiorPiece_target [IsManifold I 1 X] (hne : Nonempty ↥(I.interior X)) :
    (G.interiorPiece hne).target
      = Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) '' I.interior X := by
  rw [interiorPiece, IsOpenEmbedding.toOpenPartialHomeomorph_target]
  rw [show (fun x : ↥(I.interior X) => Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) (x : X))
      = (fun y : X => Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) y) ∘ Subtype.val from rfl,
    Set.range_comp, Subtype.range_coe]

theorem interiorPiece_apply [IsManifold I 1 X] (hne : Nonempty ↥(I.interior X))
    (x : ↥(I.interior X)) :
    G.interiorPiece hne x = Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) (x : X) := by
  rw [interiorPiece]
  exact congrFun (IsOpenEmbedding.toOpenPartialHomeomorph_apply _ _) x

theorem interiorPiece_target_subset_ungluedLocus [IsManifold I 1 X]
    (hne : Nonempty ↥(I.interior X)) :
    (G.interiorPiece hne).target ⊆ G.ungluedLocus := by
  rw [G.interiorPiece_target hne, ungluedLocus]
  exact Set.image_mono G.interior_subset_compl_iUnion_block

theorem isInteriorPoint_intrinsicInterior [IsManifold I 1 X] (hn : (1 : ℕ∞ω) ≠ 0)
    (x : DifferentialGeometry.Manifold.intrinsicInterior I 1 hn (M := X)) :
    I.IsInteriorPoint x :=
  I.isInteriorPoint_iff_isInteriorPoint_val.mpr x.property

end CollaredGluing

section UnitInterval

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

theorem unitIntervalCollaredGluing_mem_interior :
    (⟨(1 : ℝ) / 2, by norm_num⟩ : Icc (0 : ℝ) 1) ∈ (𝓡∂ 1).interior (Icc (0 : ℝ) 1) := by
  rw [← ModelWithCorners.compl_boundary]
  intro hmem
  have h : (⟨(1 : ℝ) / 2, by norm_num⟩ : Icc (0 : ℝ) 1) ∈ ({⊥, ⊤} : Set (Icc (0 : ℝ) 1)) := by
    rw [← boundary_Icc]
    exact hmem
  rcases h with h | h <;>
    (have h' := congrArg (Subtype.val : Icc (0 : ℝ) 1 → ℝ) h
     norm_num at h')

theorem unitIntervalCollaredGluing_isInteriorPoint :
    (𝓡∂ 1).IsInteriorPoint (⟨(1 : ℝ) / 2, by norm_num⟩ : Icc (0 : ℝ) 1) :=
  CollaredGluing.isInteriorPoint_of_mem_interior unitIntervalCollaredGluing_mem_interior

theorem unitIntervalCollaredGluing_isOpenEmbedding_quotientMk_interior :
    IsOpenEmbedding (fun x : ↥((𝓡∂ 1).interior (Icc (0 : ℝ) 1)) =>
      Quotient.mk'' (s₁ := unitIntervalCollaredGluing.toBoundaryGluing.setoid)
        (x : Icc (0 : ℝ) 1)) :=
  CollaredGluing.isOpenEmbedding_quotientMk_interior (I := 𝓡∂ 1) (G := unitIntervalCollaredGluing)

theorem unitIntervalCollaredGluing_interior_nonempty :
    Nonempty ↥((𝓡∂ 1).interior (Icc (0 : ℝ) 1)) :=
  ⟨⟨(1 : ℝ) / 2, by norm_num⟩, unitIntervalCollaredGluing_mem_interior⟩

theorem unitIntervalCollaredGluing_interiorPiece_apply_half :
    (unitIntervalCollaredGluing.interiorPiece unitIntervalCollaredGluing_interior_nonempty)
        ⟨⟨(1 : ℝ) / 2, by norm_num⟩, unitIntervalCollaredGluing_mem_interior⟩
      = Quotient.mk'' (s₁ := unitIntervalCollaredGluing.toBoundaryGluing.setoid)
          (⟨(1 : ℝ) / 2, by norm_num⟩ : Icc (0 : ℝ) 1) :=
  CollaredGluing.interiorPiece_apply (I := 𝓡∂ 1) (G := unitIntervalCollaredGluing)
    unitIntervalCollaredGluing_interior_nonempty _

end UnitInterval

end DifferentialGeometry.Geometry.Boundary
