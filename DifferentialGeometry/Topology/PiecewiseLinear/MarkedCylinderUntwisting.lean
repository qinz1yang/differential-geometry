/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ConeMarkedPrism
import DifferentialGeometry.Topology.PiecewiseLinear.DiskPseudoIsotopy
import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalClassification

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLPseudoIsotopicToId.exists_fixing_axis {u : E → E} {P : Set E}
    (hu : IsPLPseudoIsotopicToId u P) (hP : IsHPolytope P)
    {p : E} (hp : p ∈ interior P) (hup : u p = p) :
    ∃ Φ : E × ℝ → E × ℝ, IsPLHomeomorphOn Φ (P ×ˢ Icc 0 1) (P ×ˢ Icc 0 1) ∧
      (∀ x ∈ P, Φ (x, 0) = (x, 0)) ∧ (∀ x ∈ P, Φ (x, 1) = (u x, 1)) ∧
      EqOn Φ id ({p} ×ˢ Icc (0 : ℝ) 1) := by
  classical
  obtain ⟨Ψ, hΨ, hΨ0, hΨ1⟩ := hu
  have hC : IsHPolytope (P ×ˢ Icc (0 : ℝ) 1) := hP.prod isHPolytope_Icc
  have hclosed := hC.isCompact.isClosed
  have hpc : (p, (1 / 2 : ℝ)) ∈ interior (P ×ˢ Icc (0 : ℝ) 1) := by
    rw [interior_prod_eq, interior_Icc]
    exact ⟨hp, by norm_num⟩
  obtain ⟨K, hKfin, hKspace⟩ := hC.isPolyhedron_frontier.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hK : IsConeBase (p, (1 / 2 : ℝ)) K :=
    isConeBase_of_space_subset_frontier_convex hC.convex hclosed hpc K hKspace.subset
  have hcone : (coneComplex hK).space = P ×ˢ Icc (0 : ℝ) 1 :=
    coneComplex_space_eq_of_convex hC.convex hC.isCompact (interior_subset hpc) hK hKspace
  have hΨbd : IsPLHomeomorphOn Ψ K.space K.space := by
    have h := hΨ.restrict hC.isPolyhedron_frontier hclosed.frontier_subset
    rw [hΨ.image_frontier rfl hclosed hclosed] at h
    rwa [hKspace]
  have hcap (t : ℝ) (ht : t = 0 ∨ t = 1) : P ×ˢ {t} ⊆ K.space := by
    rw [hKspace, frontier_prod_eq, hP.isCompact.isClosed.closure_eq,
      isClosed_Icc.closure_eq, frontier_Icc zero_le_one]
    intro z hz
    exact Or.inl ⟨hz.1, hz.2.symm ▸ ht⟩
  have hpp : p ∈ P := interior_subset hp
  have hpair : ({(p, (0 : ℝ)), (p, 1)} : Set (E × ℝ)) ⊆ K.space := by
    intro z hz
    rcases mem_insert_iff.mp hz with rfl | hz
    · exact hcap 0 (Or.inl rfl) ⟨hpp, rfl⟩
    · exact mem_singleton_iff.mp hz ▸ hcap 1 (Or.inr rfl) ⟨hpp, rfl⟩
  have hfix : EqOn Ψ id ({(p, (0 : ℝ)), (p, 1)} : Set (E × ℝ)) := by
    intro z hz
    rcases mem_insert_iff.mp hz with rfl | hz
    · exact hΨ0 p hpp
    · rw [mem_singleton_iff.mp hz, hΨ1 p hpp, hup]
      rfl
  obtain ⟨Φ, hΦ, hΦΨ, -, hΦfix, -⟩ :=
    exists_isPLHomeomorphOn_coneComplex_fixing hK hK hΨbd hpair hfix
  refine ⟨Φ, hcone ▸ hΦ, fun x hx => ?_, fun x hx => ?_, ?_⟩
  · exact (hΦΨ (hcap 0 (Or.inl rfl) (show (x, 0) ∈ P ×ˢ {0} from ⟨hx, rfl⟩))).trans
      (hΨ0 x hx)
  · exact (hΦΨ (hcap 1 (Or.inr rfl) (show (x, 1) ∈ P ×ˢ {1} from ⟨hx, rfl⟩))).trans
      (hΨ1 x hx)
  · rwa [coneSet_prism_axis] at hΦfix

theorem IsCylindricalDiagram.exists_endMap_id_preserving_axis
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E × ℝ → F} {P : Set E} {S : Set F} (hf : IsCylindricalDiagram f P S)
    (hP : IsHPolytope P) {p : E} (hp : p ∈ interior P) {u : E → E}
    (hu : IsPLHomeomorphOn u P P) (hfu : ∀ x ∈ P, f (x, 0) = f (u x, 1))
    (hiso : IsPLPseudoIsotopicToId u P) (hup : u p = p) :
    ∃ g : E × ℝ → F, IsCylindricalDiagram g P S ∧
      (∀ x ∈ P, g (x, 0) = g (x, 1)) ∧
      g '' ({p} ×ˢ Icc (0 : ℝ) 1) = f '' ({p} ×ˢ Icc (0 : ℝ) 1) := by
  obtain ⟨Φ, hΦ, hΦ0, hΦ1, hfix⟩ := hiso.exists_fixing_axis hP hp hup
  refine ⟨f ∘ Φ, hf.comp_of_ends hP.isPolyhedron.isPLHomeomorphOn_id hu hΦ hΦ0 hΦ1,
    fun x hx => ?_, ?_⟩
  · change f (Φ (x, 0)) = f (Φ (x, 1))
    rw [hΦ0 x hx, hΦ1 x hx, hfu x hx]
  · rw [image_comp, hfix.image_eq, image_id]

theorem IsCylindricalDiagram.exists_endMap_id_preserving_axis_of_isOrientable
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : E × ℝ → F} {P : Set E} (hP : IsHPolytope P) (hPball : IsPLBall 2 P)
    (M : Geometry.SimplicialComplex ℝ F) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M) (hor : IsOrientable 3 M)
    (hf : IsCylindricalDiagram f P M.space) {p : E} (hp : p ∈ interior P)
    (hclosed : f (p, 0) = f (p, 1)) :
    ∃ g : E × ℝ → F, IsCylindricalDiagram g P M.space ∧
      (∀ x ∈ P, g (x, 0) = g (x, 1)) ∧
      g '' ({p} ×ˢ Icc (0 : ℝ) 1) = f '' ({p} ×ˢ Icc (0 : ℝ) 1) := by
  obtain ⟨u, hu, hfu⟩ := hf.exists_isPLHomeomorphOn_endMap hP.isPolyhedron
  have hpp := interior_subset hp
  have hup : u p = p :=
    hf.eq_of_eq_top (hu.bijOn.mapsTo hpp) hpp ((hfu p hpp).symm.trans hclosed)
  exact hf.exists_endMap_id_preserving_axis hP hp hu hfu
    (hf.isPLPseudoIsotopicToId_endMap hPball M hM hor hu hfu) hup

end DifferentialGeometry.Topology.PiecewiseLinear
