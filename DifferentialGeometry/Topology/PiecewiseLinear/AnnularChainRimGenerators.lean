/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.AnnularChainRimCylinder
import DifferentialGeometry.Topology.PiecewiseLinear.IsSpineRevolutionOfOfMemCellInterior
import DifferentialGeometry.Topology.PiecewiseLinear.Moise308Nested
import DifferentialGeometry.Topology.FundamentalGroup.Retraction
import DifferentialGeometry.Topology.Homotopy.ConvexProduct

open Set Topology
open scoped ContinuousMap

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem fundamentalGroup_map_real_level_bijective
    {M X : Type*} [TopologicalSpace M] [TopologicalSpace X]
    {Y Z : Set X} (c : (M × ℝ) ≃ₜ Y) (t : ℝ)
    (hZ : range (fun x => (c (x, t) : X)) = Z) (hZY : Z ⊆ Y) (x : Z) :
    Function.Bijective (FundamentalGroup.map
      (⟨Set.inclusion hZY, continuous_inclusion hZY⟩ : C(Z, Y)) x) := by
  let f : M → X := fun p => (c (p, t) : X)
  have hf : IsEmbedding f := IsEmbedding.subtypeVal.comp
    (c.isEmbedding.comp (isEmbedding_prodMkLeft t))
  let eZ := hf.toHomeomorph.trans (Homeomorph.setCongr hZ)
  let ep := (Homeomorph.refl M).prodCongr (Homeomorph.Set.univ ℝ).symm
  let e := (c.symm.toHomotopyEquiv.trans (ep.toHomotopyEquiv.trans
    (DifferentialGeometry.HomotopyEquiv.productConvex M convex_univ ⟨t, mem_univ t⟩))).trans
      eZ.toHomotopyEquiv
  apply bijective_fundamentalGroup_map_of_homotopyEquiv_leftInverse e
  intro z
  have hz : (z : X) ∈ range (fun p => (c (p, t) : X)) := by
    rw [hZ]
    exact z.property
  obtain ⟨p, hp⟩ := hz
  have hiz : Set.inclusion hZY z = c (p, t) := Subtype.ext hp.symm
  apply Subtype.ext
  change (c ((c.symm (Set.inclusion hZY z)).1, t) : X) = z
  rw [hiz, c.symm_apply_apply]
  exact hp

variable {φ : E3 → E3} {Pt : ℤ → E3}
  {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' : E3}

theorem IsCanonicalTower.circle_image_subset_punctured_disk
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ) :
    φ '' J i ⊆ Dimg \ (Dbdimg ∪ {P'}) := by
  obtain ⟨c, hc⟩ := htw.exists_annuli_cylinder_homeomorph
  rw [← hc i]
  rintro _ ⟨x, rfl⟩
  exact (c (x, (i : ℝ))).property

theorem IsCanonicalTower.circle_fundamentalGroup_bijective
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ)
    (hsub : φ '' J i ⊆ Dimg \ (Dbdimg ∪ {P'})) (x : φ '' J i) :
    Function.Bijective (FundamentalGroup.map
      (⟨Set.inclusion hsub, continuous_inclusion hsub⟩ :
        C(φ '' J i, ↥(Dimg \ (Dbdimg ∪ {P'})))) x) := by
  obtain ⟨c, hc⟩ := htw.exists_annuli_cylinder_homeomorph
  exact fundamentalGroup_map_real_level_bijective c (i : ℝ) (hc i) hsub x

private theorem spine_image_of_embedding {f : E3 → E3} {V Z : Set E3}
    (hf : IsEmbedding (V.domRestrict f)) (hZ : IsSpine V Z) : IsSpine (f '' V) (f '' Z) := by
  obtain ⟨e, p, hp, hZ⟩ := hZ
  let ef := hf.toHomeomorph.trans (Homeomorph.setCongr (Set.range_domRestrict f V))
  refine ⟨e.trans ef, p, hp, ?_⟩
  rw [hZ]
  simp only [image_image]
  rfl

theorem IsCanonicalTower.outer_spine
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ) :
    IsSpine (φ '' S i) (φ '' J i) := by
  have hc := htw.config i
  have hSN : S i ⊆ ⋃ j : Fin 3, S (i + ((j : ℕ) : ℤ)) := by
    intro x hx
    exact mem_iUnion.mpr ⟨0, by simpa using hx⟩
  have hemb : IsEmbedding ((S i).domRestrict φ) :=
    hc.isEmbedding.comp (IsEmbedding.inclusion hSN)
  apply spine_image_of_embedding hemb
  have hsolid : S i = revolutionOf (Dp i) := by simpa using hc.base.solidEq (0 : Fin 3)
  have hcircle : J i = revolutionOf {Pt i} := by simpa using hc.base.circleEq (0 : Fin 4)
  rw [hsolid, hcircle]
  have hcell : IsTopologicalCellWithInterior 2 (Dp i) (Dpint i) := by
    simpa using hc.base.chain.cell (0 : Fin 3)
  have hhalf : ∀ p ∈ Dp i, p 2 = 0 ∧ 0 < p 0 := by
    simpa using hc.base.chain.halfPlane (0 : Fin 3)
  have hp : Pt i ∈ Dpint i := by
    simpa using hc.base.chain.segmentSubset (0 : Fin 3) (left_mem_segment ℝ _ _)
  exact isSpine_revolutionOf_of_mem_cellInterior hcell hhalf hp

end DifferentialGeometry.Topology.PiecewiseLinear
