import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageLocalFacesVertJN74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageLocalFacesHorizJN74

/-!
# Draft 74, `local_faces`, step 6: the classification of the frontier points of `C₁`

Lane S-JUNCTIONS (by S-JUNCTIONS4), G25 part 1 (suffix `_JN74`). On any rows `R`, from the face
facts `F` (g3, g4), `rim_fibre`, `edge_region` and `edgeSet ⊆ M₂`: every `c ∈ ∂C₁` is of exactly the
types of the three local lemmas.

* `frontier_classification_JN74`: `c = rimBase c'` with `c' ∈ C₂ ∖ ∂C₂` (vertical, G23), or
  `c = rimBase e` for an endpoint `e` (corner), or the whole fibre of `c` meets a residual face and
  misses `M^edge` (horizontal, G24).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} {A : SmoothStageGeometry74 W E}
  {D : StageCutChoice74 A}

namespace StageCutRows74

variable (R : StageCutRows74 A D)

/-- **A vertical point of the fibre of `c` makes `c` a rim base point.** -/
theorem exists_rimBase_of_mem_vertical_JN74 (rimBase : R.edge.Base → R.circle.Base)
    (hrim : ∀ c ∈ R.edge.cbase, R.edge.rim c = R.circle.fibre (rimBase c))
    {c : R.circle.Base} {x : W.Carrier} (hxc : x ∈ R.circle.fibre c) (hxv : x ∈ R.edge.vertical) :
    ∃ c' ∈ R.edge.cbase, c = rimBase c' := by
  obtain ⟨z, ⟨hz1, hz2⟩, rfl⟩ := hxv
  have hxr : (z : W.Carrier) ∈ R.edge.rim (R.edge.proj z) := ⟨z, ⟨rfl, hz2⟩, rfl⟩
  rw [hrim _ hz1] at hxr
  obtain ⟨y₁, hy₁, hy₁x⟩ := hxc
  obtain ⟨y₂, hy₂, hy₂x⟩ := hxr
  have hy : y₁ = y₂ := Subtype.ext (hy₁x.trans hy₂x.symm)
  subst hy
  exact ⟨R.edge.proj z, hz1, hy₁.symm.trans hy₂⟩

/-- **The classification of the frontier points of `C₁`.** -/
theorem frontier_classification_JN74 (F : JunctionFaceFacts74 A D R)
    (rimBase : R.edge.Base → R.circle.Base)
    (hrim : ∀ c ∈ R.edge.cbase, R.edge.rim c = R.circle.fibre (rimBase c))
    (hreg : D.edgeSet ∩ D.M₃ = R.edge.vertical) (hsub : D.edgeSet ⊆ D.M₂)
    {c : R.circle.Base} (hc : c ∈ frontier R.circle.cbase) :
    (∃ c' ∈ R.edge.cbase, c' ∉ frontier R.edge.cbase ∧ c = rimBase c') ∨
      (∃ e : R.edge.EdgeEnd, c = rimBase e.1) ∨
      ∃ (x₀ : W.Carrier) (Fl : R.slimPieces.ResidualFace), x₀ ∈ R.circle.fibre c ∧
        x₀ ∈ R.slimPieces.residualSet Fl ∧ ∀ x ∈ R.circle.fibre c, x ∉ D.edgeSet := by
  classical
  have hrelint := R.relInt_edgeSet_eq_JN74 hreg hsub
  have hEc : IsClosed D.edgeSet := by
    rw [← R.edgePiece_eq]
    exact (R.edge.proper _ R.edge.cbase_compact).isClosed
  have hcm : c ∈ R.circle.cbase := R.circle.cbase_compact.isClosed.frontier_subset hc
  have hfibM : R.circle.fibre c ⊆ D.M₃ := (R.mem_cbase_iff_fibre_subset_JN74).1 hcm
  obtain ⟨x, hxc, hxi⟩ := R.exists_frontier_fibre_point_JN74 hc
  have hxM3 : x ∈ D.M₃ := hfibM hxc
  by_cases hfr : x ∈ frontier D.M₂
  · -- the point is on a residual face
    have hbd : x ∈ R.slimPieces.boundaryM2 := by rw [← F.frontier_M2]; exact hfr
    obtain ⟨Fl, hFl⟩ := mem_iUnion.1 hbd
    by_cases hnoE : ∀ y ∈ R.circle.fibre c, y ∉ D.edgeSet
    · exact Or.inr (Or.inr ⟨x, Fl, hxc, hFl, hnoE⟩)
    · push Not at hnoE
      obtain ⟨y, hyc, hyE⟩ := hnoE
      have hyv : y ∈ R.edge.vertical := by rw [← hreg]; exact ⟨hyE, hfibM hyc⟩
      obtain ⟨c', hc', hcc'⟩ := R.exists_rimBase_of_mem_vertical_JN74 rimBase hrim hyc hyv
      by_cases hnf : c' ∈ frontier R.edge.cbase
      · exact Or.inr (Or.inl ⟨⟨c', hnf⟩, hcc'⟩)
      · exfalso
        have hxr : x ∈ R.edge.rim c' := by rw [hrim c' hc', ← hcc']; exact hxc
        have hxint := R.rim_subset_interior_M₂_JN74 F hsub hc' hnf x hxr
        exact hfr.2 hxint
  · -- the point is in the interior of `M₂` and in the vertical face
    have hxM2 : x ∈ interior D.M₂ := by
      by_contra h
      exact hfr ⟨subset_closure hxM3.1, h⟩
    have hxE : x ∈ D.edgeSet := by
      by_contra hxE
      apply hxi
      refine mem_interior.2 ⟨interior D.M₂ ∩ (D.edgeSet)ᶜ, ?_,
        isOpen_interior.inter hEc.isOpen_compl, ⟨hxM2, hxE⟩⟩
      rintro y ⟨hyM, hyE⟩
      exact ⟨interior_subset hyM, fun hr => hyE (relInt_subset_JN74 hr)⟩
    have hxv : x ∈ R.edge.vertical := by rw [← hreg]; exact ⟨hxE, hxM3⟩
    obtain ⟨c', hc', hcc'⟩ := R.exists_rimBase_of_mem_vertical_JN74 rimBase hrim hxc hxv
    by_cases hnf : c' ∈ frontier R.edge.cbase
    · exact Or.inr (Or.inl ⟨⟨c', hnf⟩, hcc'⟩)
    · exact Or.inl ⟨c', hc', hnf, hcc'⟩

end StageCutRows74

end GC.GraphManifold.Assembly.FC39P0
