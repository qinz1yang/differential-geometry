/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryCaseOfCut

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem PLCrossSeamReading.exists_boundary_cover
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {chart : (ℝ × ℝ) × ℝ → M} {G : SingularTwoCell M}
    (R : PLCrossSeamReading chart G) (ec : loopCircle ≃ₜ frontier G.domain) :
    ∃ Ω₁ Ω₂ : Set loopCircle,
      IsClosed Ω₁ ∧ IsClosed Ω₂ ∧ Ω₁ ∪ Ω₂ = univ ∧
        ContinuousOn (fun θ => R.coord ↑(ec θ)) Ω₁ ∧
          (∀ θ ∈ Ω₁, ⇑G ↑(ec θ) ∈ chart '' spliceCylinder) ∧
            (∀ θ, ⇑G ↑(ec θ) ∈ chart '' spliceCylinder → θ ∈ Ω₁) ∧
              (∀ θ ∈ Ω₁ ∩ Ω₂, (R.coord ↑(ec θ)).2.1 ∈ spliceSquareBoundary) := by
  let e : loopCircle → EuclideanSpace ℝ (Fin 2) :=
    fun θ => ((ec θ : frontier G.domain) : EuclideanSpace ℝ (Fin 2))
  let Ω₁ : Set loopCircle := e ⁻¹' R.tubeSource
  let Ω₂ : Set loopCircle := closure Ω₁ᶜ
  have he : Continuous e := continuous_subtype_val.comp ec.continuous
  have hΩ₁ : IsClosed Ω₁ := R.isPolyhedron_source.isClosed.preimage he
  have hΩ₂ : IsClosed Ω₂ := isClosed_closure
  have hcover : Ω₁ ∪ Ω₂ = univ := by
    apply eq_univ_of_forall
    intro θ
    by_cases hθ : θ ∈ Ω₁
    · exact Or.inl hθ
    · exact Or.inr (subset_closure hθ)
  have hΩ₁tube : ∀ θ ∈ Ω₁, ⇑G ↑(ec θ) ∈ chart '' spliceCylinder := by
    intro θ hθ
    have hx : e θ ∈ R.tubeSource := hθ
    rw [R.tubeSource_eq] at hx
    exact hx.2
  have hΩ₁max : ∀ θ, ⇑G ↑(ec θ) ∈ chart '' spliceCylinder → θ ∈ Ω₁ := by
    intro θ hθ
    have hdom : e θ ∈ G.domain := G.frontier_subset_domain (ec θ).property
    have hx : e θ ∈ R.tubeSource := by
      rw [R.tubeSource_eq]
      exact ⟨hdom, hθ⟩
    exact hx
  have hpos : ContinuousOn R.coord R.sourcePos := by
    have h₂ : ContinuousOn (fun x => (R.coord x).2) R.sourcePos :=
      R.isPLHomeomorphOn_pos.isPiecewiseAffineOn.continuousOn
    have hpair : ContinuousOn (fun x => (true, (R.coord x).2)) R.sourcePos :=
      continuousOn_const.prodMk h₂
    exact hpair.congr fun x hx => Prod.ext (R.coord_fst_pos x hx) rfl
  have hneg : ContinuousOn R.coord R.sourceNeg := by
    have h₂ : ContinuousOn (fun x => (R.coord x).2) R.sourceNeg :=
      R.isPLHomeomorphOn_neg.isPiecewiseAffineOn.continuousOn
    have hpair : ContinuousOn (fun x => (false, (R.coord x).2)) R.sourceNeg :=
      continuousOn_const.prodMk h₂
    exact hpair.congr fun x hx => Prod.ext (R.coord_fst_neg x hx) rfl
  have hcoord : ContinuousOn R.coord R.tubeSource := by
    exact hpos.union_of_isClosed hneg R.isPolyhedron_sourcePos.isClosed
      R.isPolyhedron_sourceNeg.isClosed
  have hcocont : ContinuousOn (fun θ => R.coord ↑(ec θ)) Ω₁ := by
    have hmap : MapsTo e Ω₁ R.tubeSource := fun θ hθ => hθ
    simpa [Function.comp_def] using hcoord.comp he.continuousOn hmap
  have hface : closure (G.domain \ R.tubeSource) ⊆ R.face := by
    apply closure_minimal
    · intro x hx
      have hxdom : x ∈ R.tubeSource ∪ R.face := by
        rw [R.tubeSource_union_face]
        exact hx.1
      rcases hxdom with hxtube | hxface
      · exact (hx.2 hxtube).elim
      · exact hxface
    · exact R.isPolyhedron_face.isClosed
  have hfrontier : ∀ θ ∈ Ω₂, e θ ∈ closure (frontier G.domain \ R.tubeSource) := by
    intro θ hθ
    rw [mem_closure_iff] at hθ
    rw [mem_closure_iff]
    intro o ho hxo
    have hopen : IsOpen (e ⁻¹' o) := ho.preimage he
    have hθo : θ ∈ e ⁻¹' o := hxo
    obtain ⟨θ', hθ'o, hθ'not⟩ := hθ (e ⁻¹' o) hopen hθo
    refine ⟨e θ', hθ'o, ?_⟩
    exact ⟨(ec θ').property, hθ'not⟩
  have hlateral : ∀ θ ∈ Ω₁ ∩ Ω₂, (R.coord ↑(ec θ)).2.1 ∈ spliceSquareBoundary := by
    intro θ hθ
    have hxtube : e θ ∈ R.tubeSource := hθ.1
    have hsub : frontier G.domain \ R.tubeSource ⊆ G.domain \ R.tubeSource := by
      intro x hx
      exact ⟨G.frontier_subset_domain hx.1, hx.2⟩
    have hxf : e θ ∈ closure (G.domain \ R.tubeSource) :=
      closure_mono hsub (hfrontier θ hθ.2)
    have hxface : e θ ∈ R.face := hface hxf
    have hwall := R.overlap_lateral (e θ) ⟨hxtube, hxface⟩
    exact hwall.1
  exact ⟨Ω₁, Ω₂, hΩ₁, hΩ₂, hcover, hcocont, hΩ₁tube, hΩ₁max, hlateral⟩

end DifferentialGeometry.Topology.PiecewiseLinear
