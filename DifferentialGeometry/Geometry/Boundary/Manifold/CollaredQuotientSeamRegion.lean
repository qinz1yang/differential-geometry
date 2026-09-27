import DifferentialGeometry.Geometry.Boundary.Manifold.CollaredGluingRegularity

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

private abbrev icoToIcc {a b : ℝ} (t : Ico a b) : Icc a b :=
  ⟨(t : ℝ), t.2.1, le_of_lt t.2.2⟩

private abbrev leftStrip (G : CollaredGluing I X ι) (i : ι) :
    ↥(G.left i).carrier × Ico (0 : ℝ) (G.ε i) → X :=
  fun p => G.collarLeft i (p.1, icoToIcc p.2)

private abbrev rightStrip (G : CollaredGluing I X ι) (i : ι) :
    ↥(G.right i).carrier × Ico (0 : ℝ) (G.ε i) → X :=
  fun p => G.collarRight i (p.1, icoToIcc p.2)

private theorem range_leftStrip (G : CollaredGluing I X ι) (i : ι) :
    range (leftStrip G i) = range (G.collarLeftOpen i) := by
  refine Set.ext fun x => ⟨?_, ?_⟩
  · rintro ⟨p, rfl⟩
    exact ⟨p, CollaredGluing.collarLeftOpen_apply G i p⟩
  · rintro ⟨p, rfl⟩
    exact ⟨p, (CollaredGluing.collarLeftOpen_apply G i p).symm⟩

private theorem range_rightStrip (G : CollaredGluing I X ι) (i : ι) :
    range (rightStrip G i) = range (G.collarRightOpen i) := by
  refine Set.ext fun x => ⟨?_, ?_⟩
  · rintro ⟨p, rfl⟩
    exact ⟨p, CollaredGluing.collarRightOpen_apply G i p⟩
  · rintro ⟨p, rfl⟩
    exact ⟨p, (CollaredGluing.collarRightOpen_apply G i p).symm⟩

theorem isOpen_range_collarLeftOpen_union_collarRightOpen (G : CollaredGluing I X ι)
    (h : G.CollarOpenEmbedding) (i : ι) :
    IsOpen (range (G.collarLeftOpen i) ∪ range (G.collarRightOpen i)) :=
  (isOpen_range_collarLeftOpen G h i).union (isOpen_range_collarRightOpen G h i)

theorem block_subset_range_collarLeft_union_collarRight (G : CollaredGluing I X ι)
    [IsManifold I 1 X] (i : ι) :
    (G.toBoundaryGluing).block i ⊆ range (G.collarLeft i) ∪ range (G.collarRight i) := by
  rintro x (hx | hx)
  · exact Or.inl ⟨(⟨x, hx⟩, ⟨0, le_rfl, (G.ε_pos i).le⟩), G.collarLeft_zero i ⟨x, hx⟩⟩
  · exact Or.inr ⟨(⟨x, hx⟩, ⟨0, le_rfl, (G.ε_pos i).le⟩), G.collarRight_zero i ⟨x, hx⟩⟩

private theorem mem_range_union_of_rel (G : CollaredGluing I X ι) [IsManifold I 1 X] {i : ι}
    {x y : X} (hxy : (G.toBoundaryGluing).rel x y)
    (hx : x ∈ range (G.collarLeftOpen i) ∪ range (G.collarRightOpen i)) :
    y ∈ range (G.collarLeftOpen i) ∪ range (G.collarRightOpen i) := by
  rw [← range_leftStrip G i, ← range_rightStrip G i] at hx ⊢
  rcases hx with ⟨⟨z, t⟩, hxeq⟩ | ⟨⟨z, t⟩, hxeq⟩
  · have hstrip : leftStrip G i (z, t) = G.collarLeft i (z, icoToIcc t) := rfl
    rw [← hxeq] at hxy
    rcases lt_or_eq_of_le t.2.1 with ht | ht
    · have hnb : ¬ I.IsBoundaryPoint (leftStrip G i (z, t)) := by
        rw [hstrip]
        exact CollaredGluing.collarLeft_inward G i z (icoToIcc t)
          (ht : (0 : ℝ) < (icoToIcc t : ℝ))
      have heq := (G.toBoundaryGluing).eq_of_rel_of_notMem
        (fun j => CollaredGluing.notMem_block_of_not_isBoundaryPoint G hnb j) hxy
      rw [← heq]
      exact Or.inl ⟨(z, t), rfl⟩
    · have hcast : icoToIcc t = ⟨0, le_rfl, (G.ε_pos i).le⟩ :=
        Subtype.ext (ht.symm : (icoToIcc t : ℝ) = 0)
      have hmem : leftStrip G i (z, t) ∈ (G.toBoundaryGluing).block i := by
        refine Or.inl ?_
        rw [hstrip, hcast, G.collarLeft_zero]
        exact z.2
      rcases CollaredGluing.rel_iff_of_mem_block G hmem hxy with heq | hflip
      · rw [heq]
        exact Or.inl ⟨(z, t), rfl⟩
      · refine Or.inr ⟨((G.attaching i z), ⟨(0 : ℝ), le_rfl, G.ε_pos i⟩), ?_⟩
        have hzero : rightStrip G i ((G.attaching i z), ⟨(0 : ℝ), le_rfl, G.ε_pos i⟩)
            = (G.attaching i z : X) := by
          rw [rightStrip]
          exact G.collarRight_zero i (G.attaching i z)
        rw [hzero]
        have hflipeq : (G.toBoundaryGluing).flip i (leftStrip G i (z, t))
            = (G.attaching i z : X) := by
          rw [hstrip, hcast, G.collarLeft_zero]
          exact (G.toBoundaryGluing).flip_of_mem_left z.2
        exact hflipeq.symm.trans hflip.symm
  · have hstrip : rightStrip G i (z, t) = G.collarRight i (z, icoToIcc t) := rfl
    rw [← hxeq] at hxy
    rcases lt_or_eq_of_le t.2.1 with ht | ht
    · have hnb : ¬ I.IsBoundaryPoint (rightStrip G i (z, t)) := by
        rw [hstrip]
        exact CollaredGluing.collarRight_inward G i z (icoToIcc t)
          (ht : (0 : ℝ) < (icoToIcc t : ℝ))
      have heq := (G.toBoundaryGluing).eq_of_rel_of_notMem
        (fun j => CollaredGluing.notMem_block_of_not_isBoundaryPoint G hnb j) hxy
      rw [← heq]
      exact Or.inr ⟨(z, t), rfl⟩
    · have hcast : icoToIcc t = ⟨0, le_rfl, (G.ε_pos i).le⟩ :=
        Subtype.ext (ht.symm : (icoToIcc t : ℝ) = 0)
      have hmem : rightStrip G i (z, t) ∈ (G.toBoundaryGluing).block i := by
        refine Or.inr ?_
        rw [hstrip, hcast, G.collarRight_zero]
        exact z.2
      rcases CollaredGluing.rel_iff_of_mem_block G hmem hxy with heq | hflip
      · rw [heq]
        exact Or.inr ⟨(z, t), rfl⟩
      · refine Or.inl ⟨((G.attaching i).symm z, ⟨(0 : ℝ), le_rfl, G.ε_pos i⟩), ?_⟩
        have hzero : leftStrip G i (((G.attaching i).symm z), ⟨(0 : ℝ), le_rfl, G.ε_pos i⟩)
            = ((G.attaching i).symm z : X) := by
          rw [leftStrip]
          exact G.collarLeft_zero i ((G.attaching i).symm z)
        rw [hzero]
        have hflipeq : (G.toBoundaryGluing).flip i (rightStrip G i (z, t))
            = ((G.attaching i).symm z : X) := by
          rw [hstrip, hcast, G.collarRight_zero]
          exact (G.toBoundaryGluing).flip_of_mem_right z.2
        exact hflipeq.symm.trans hflip.symm

theorem isOpen_quotientMk_image_range_collarOpen (G : CollaredGluing I X ι) [IsManifold I 1 X]
    (h : G.CollarOpenEmbedding) (i : ι) :
    IsOpen (Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) ''
      (range (G.collarLeftOpen i) ∪ range (G.collarRightOpen i))) := by
  refine Topology.isOpen_quotient_mk_image_of_saturated ?_
    (G.isOpen_range_collarLeftOpen_union_collarRightOpen h i)
  intro x y hxy
  exact ⟨fun hx => G.mem_range_union_of_rel hxy hx,
    fun hy => G.mem_range_union_of_rel ((G.toBoundaryGluing).setoid.symm hxy) hy⟩

theorem quotientMk_image_range_collarOpen_subset_range_seamChart (G : CollaredGluing I X ι)
    [IsManifold I 1 X] (i : ι) :
    Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) ''
        (range (G.collarLeftOpen i) ∪ range (G.collarRightOpen i))
      ⊆ range (G.seamChart i) := by
  rw [CollaredGluing.range_seamChart]
  refine Set.image_mono ?_
  refine union_subset_union ?_ ?_
  · exact range_comp_subset_range _ _
  · exact range_comp_subset_range _ _

end CollaredGluing

end DifferentialGeometry.Geometry.Boundary
