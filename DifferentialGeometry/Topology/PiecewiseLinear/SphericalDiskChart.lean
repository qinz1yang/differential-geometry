/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskStraightening
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexHalfspaceCoordinates
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphOpen
import DifferentialGeometry.Topology.PiecewiseLinear.VertexChartTransport
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPLBall.exists_openPartialHomeomorph_boundary_disk {Y D O : Set E3}
    (hY : IsPLBall 3 Y) (hD : IsPLBall 2 D) (hDY : D ⊆ frontier Y)
    (hO : IsOpen O) (hDO : D ⊆ O) :
    ∃ e : OpenPartialHomeomorph E3 (ℝ × ℝ × ℝ),
      D ⊆ e.source ∧ e.source ⊆ O ∧
      IsPiecewiseAffineOn e e.source ∧ IsPiecewiseAffineOn e.symm e.target ∧
      (∀ x ∈ e.source, x ∈ frontier Y ↔ (e x).2.2 = 0) ∧
      (∀ x ∈ e.source, x ∈ Y ↔ 0 ≤ (e x).2.2) := by
  classical
  have hOn : O ∈ 𝓝ˢ[frontier Y] D :=
    mem_nhdsSetWithin.mpr ⟨O, hO, hDO, inter_subset_left⟩
  obtain ⟨D', hD', hD'Y, hD'n⟩ :=
    hY.isPLSphere_frontier.exists_isPLBall_neighborhood hD hDY hOn
  obtain ⟨W, hW, hDW, hWD'⟩ := mem_nhdsSetWithin.mp hD'n
  have havoid : ∀ x ∈ D, x ∉ closure (frontier Y \ D') := by
    have hcl : closure (frontier Y \ D') ⊆ Wᶜ :=
      closure_minimal (fun x hx hxW => hx.2 (hWD' ⟨hxW, hx.1⟩)) hW.isClosed_compl
    exact fun x hx hxcl => hcl hxcl (hDW hx)
  obtain ⟨T, a, f, hT, hcard, ha, hf, hfY, hfD'⟩ :=
    hY.exists_ambient_isPLHomeomorphOn_disk_to_simplex hD' (hD'Y.trans inter_subset_left)
  have hspan : affineSpan ℝ (range ((↑) : T → E3)) = ⊤ :=
    hT.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by
      simpa only [Fintype.card_coe, finrank_euclideanSpace, Fintype.card_fin] using hcard)
  let b : AffineBasis T ℝ E3 := ⟨(↑), hT, hspan⟩
  let aT : T := ⟨a, ha⟩
  have hbr : range b = (T : Set E3) := Subtype.range_coe
  have hnonneg (x : E3) :
      x ∈ convexHull ℝ (T : Set E3) ↔ ∀ i, 0 ≤ b.coord i x := by
    rw [← hbr, b.convexHull_eq_nonneg_coord]
    rfl
  have hface (v : T) (x : E3) :
      x ∈ convexHull ℝ (T.erase v.1 : Set E3) ↔
        (∀ i, 0 ≤ b.coord i x) ∧ b.coord v x = 0 := by
    have himage : b '' ((Finset.univ.erase v : Finset T) : Set T) =
        (T.erase v.1 : Set E3) := by
      ext y
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact Finset.mem_erase.mpr
          ⟨fun h => (Finset.mem_erase.mp hi).1 (Subtype.ext h), i.2⟩
      · intro hy
        refine ⟨⟨y, (Finset.mem_erase.mp hy).2⟩, ?_, rfl⟩
        exact Finset.mem_erase.mpr
          ⟨fun h => (Finset.mem_erase.mp hy).1 (congrArg Subtype.val h), Finset.mem_univ _⟩
    rw [← himage, mem_convexHull_image_affineBasis_iff]
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, not_not, forall_eq]
  have hfcl : f '' closure (frontier Y \ D') =
      closure (frontier (convexHull ℝ (T : Set E3)) \ convexHull ℝ (T.erase a : Set E3)) := by
    rw [f.image_closure, image_sdiff f.injective, f.image_frontier, hfY, hfD']
  have hposD : ∀ x ∈ D, ∀ i : T, i ≠ aT → 0 < b.coord i (f x) := by
    intro x hx i hia
    have hfx : f x ∈ convexHull ℝ (T : Set E3) := by
      rw [← hfY]
      exact mem_image_of_mem f (hY.isPolyhedron.isClosed.frontier_subset (hDY hx))
    have hn := (hnonneg (f x)).mp hfx
    by_contra hi
    have hzero : b.coord i (f x) = 0 := le_antisymm (not_lt.mp hi) (hn i)
    have hcl : f x ∈
        closure (frontier (convexHull ℝ (T : Set E3)) \
          convexHull ℝ (T.erase a : Set E3)) := by
      rw [closure_frontier_convexHull_sdiff_convexHull_erase T hT
        (by rw [← hbr]; exact hspan) ha,
        simplexAvoiding_singleton_space]
      exact mem_iUnion₂.mpr ⟨i.1,
        Finset.mem_erase.mpr ⟨fun h => hia (Subtype.ext h), i.2⟩,
        (hface i (f x)).mpr ⟨hn, hzero⟩⟩
    obtain ⟨y, hy, heq⟩ := hfcl.symm ▸ hcl
    exact havoid x hx (f.injective heq ▸ hy)
  obtain ⟨g, hg⟩ := exists_affineEquiv_prod_coord_of_affineBasis b
    (by simpa only [Fintype.card_coe] using hcard) aT
  let F : E3 ≃ₜ (ℝ × ℝ × ℝ) := f.trans g.toContinuousAffineEquiv.toHomeomorph
  have hgPL : IsPLHomeomorphOn g univ univ := by
    refine ⟨bijOn_univ.mpr g.bijective,
      isPiecewiseAffineOn_of_affine g.toAffineMap isOpen_univ, ?_⟩
    refine (isPiecewiseAffineOn_of_affine g.symm.toAffineMap isOpen_univ).congr ?_
    intro y _
    change Function.invFunOn (⇑g) univ y = g.symm y
    apply g.injective
    simpa only [g.apply_symm_apply] using
      (bijOn_univ.mpr g.bijective).invOn_invFunOn.2 (mem_univ y)
  have hF : IsPLHomeomorphOn F univ univ := hf.trans hgPL
  let V : Set E3 := {x | ∀ i : T, i ≠ aT → 0 < b.coord i x}
  have hV : IsOpen V := by
    simp only [V, ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro _
    exact isOpen_lt continuous_const (b.coord i).continuous_of_finiteDimensional
  let U : Set E3 := O ∩ f ⁻¹' V
  have hU : IsOpen U := hO.inter (hV.preimage f.continuous)
  have hDU : D ⊆ U := fun x hx => ⟨hDO hx, hposD x hx⟩
  have hFU : IsOpen (F '' U) := F.isOpenMap U hU
  have hFUpl := hF.restrict_isOpen hU (subset_univ U) hFU
  let e := hFUpl.toOpenPartialHomeomorph hU hFU
  have hYcoord : ∀ x ∈ U, x ∈ Y ↔ 0 ≤ (F x).2.2 := by
    intro x hx
    change x ∈ Y ↔ 0 ≤ (g (f x)).2.2
    rw [hg]
    have hmem : x ∈ Y ↔ f x ∈ convexHull ℝ (T : Set E3) := by
      rw [← hfY, f.injective.mem_set_image]
    rw [hmem, hnonneg]
    constructor
    · exact fun h => h aT
    · intro h i
      by_cases hi : i = aT
      · simpa only [hi] using h
      · exact (hx.2 i hi).le
  have hYimage : e.IsImage Y {z | 0 ≤ z.2.2} := by
    intro x hx
    exact (hYcoord x hx).symm
  have hfront : frontier {z : ℝ × ℝ × ℝ | 0 ≤ z.2.2} = {z | z.2.2 = 0} := by
    change frontier ((Prod.snd ∘ (Prod.snd : ℝ × ℝ × ℝ → ℝ × ℝ)) ⁻¹' Ici 0) = _
    rw [← (isOpenMap_snd.comp isOpenMap_snd).preimage_frontier_eq_frontier_preimage
      (continuous_snd.comp continuous_snd), frontier_Ici]
    rfl
  refine ⟨e, hDU, inter_subset_left, hFUpl.isPiecewiseAffineOn,
    hFUpl.isPiecewiseAffineOn_invFunOn, ?_, hYcoord⟩
  intro x hx
  have hb := hYimage.frontier hx
  rw [hfront] at hb
  exact hb.symm

end DifferentialGeometry.Topology.PiecewiseLinear
