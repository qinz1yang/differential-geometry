/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryBranchTubeCharts

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem IsPLHomeomorphOn.restrict_preimage_isOpen {f : E → F} {P : Set E} {Q O : Set F}
    (hf : IsPLHomeomorphOn f P Q) (hP : IsOpen P) (hO : IsOpen O) :
    IsPLHomeomorphOn f (P ∩ f ⁻¹' O) (Q ∩ O) := by
  have hsub : P ∩ f ⁻¹' O ⊆ P := inter_subset_left
  have hP' : IsOpen (P ∩ f ⁻¹' O) :=
    hf.isPiecewiseAffineOn.continuousOn.isOpen_inter_preimage hP hO
  have hbij : BijOn f (P ∩ f ⁻¹' O) (Q ∩ O) := by
    refine ⟨fun x hx => ⟨hf.bijOn.mapsTo hx.1, hx.2⟩, hf.bijOn.injOn.mono hsub, ?_⟩
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hf.bijOn.surjOn hy.1
    refine ⟨x, ⟨hx, ?_⟩, hxy⟩
    change f x ∈ O
    rw [hxy]
    exact hy.2
  have hpa : IsPiecewiseAffineOn (Function.invFunOn f P) (Q ∩ O) :=
    fun y hy => (hf.isPiecewiseAffineOn_invFunOn y hy.1).inter_of_mem_nhds (hO.mem_nhds hy.2)
  refine ⟨hbij, hf.isPiecewiseAffineOn.mono hP' hsub, hpa.congr fun y hy => ?_⟩
  exact hf.bijOn.injOn (hbij.surjOn.mapsTo_invFunOn hy).1
    (hf.bijOn.surjOn.mapsTo_invFunOn hy.1)
    ((hbij.invOn_invFunOn.2 hy).trans (hf.bijOn.invOn_invFunOn.2 hy.1).symm)

open Classical in
theorem exists_isPLHomeomorphOn_val_symm_of_pl_transition
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hL : IsCombinatorialManifold 3 L) :
    letI := combinatorialChartedSpace L hL
    ∀ {e : OpenPartialHomeomorph L.space (EuclideanSpace ℝ (Fin 3))},
      e ∈ atlas (EuclideanSpace ℝ (Fin 3)) L.space →
      ∀ (g : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) F),
        IsPLHomeomorphOn g g.source g.target →
        ∃ Ω : Set E, IsOpen Ω ∧ Subtype.val ⁻¹' Ω = (e.trans g).source ∧
          IsPLHomeomorphOn (fun x => ((e.trans g).symm x : E)) (e.trans g).target
            (L.space ∩ Ω) := by
  let _ := combinatorialChartedSpace L hL
  have _ : HasGroupoid L.space (plGroupoid 3) := combinatorialChartedSpace_hasGroupoid L hL
  intro e he g hg
  have hemax : e ∈ (plGroupoid 3).maximalAtlas L.space :=
    StructureGroupoid.subset_maximalAtlas _ he
  let U := e.target ∩ g.source
  have hU : IsOpen U := e.open_target.inter g.open_source
  obtain ⟨Ω, hΩ, hΩeq, heU⟩ :=
    exists_isPLHomeomorphOn_val_symm_of_mem_maximalAtlas L hL hemax hU inter_subset_left
  have hginv : IsPLHomeomorphOn g.symm g.target g.source := by
    apply hg.symm.congr
    intro x hx
    exact g.injOn (g.map_target hx) (hg.bijOn.surjOn.mapsTo_invFunOn hx)
      ((g.right_inv hx).trans (hg.bijOn.invOn_invFunOn.2 hx).symm)
  have htarget : (e.trans g).target ⊆ g.target := by
    rw [OpenPartialHomeomorph.trans_target]
    exact inter_subset_left
  have himage : g.symm '' (e.trans g).target = U := by
    rw [OpenPartialHomeomorph.trans_target]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy.2, g.map_target hy.1⟩
    · intro hx
      refine ⟨g x, ⟨g.map_source hx.2, ?_⟩, g.left_inv hx.2⟩
      change g.symm (g x) ∈ e.target
      rw [g.left_inv hx.2]
      exact hx.1
  have hgU : IsPLHomeomorphOn g.symm (e.trans g).target U := by
    have h := hginv.restrict_isOpen (e.trans g).open_target htarget
      (by rw [himage]; exact hU)
    rwa [himage] at h
  refine ⟨Ω, hΩ, ?_, ?_⟩
  · rw [hΩeq, OpenPartialHomeomorph.trans_source]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨e.map_target hy.1, ?_⟩
      change e (e.symm y) ∈ g.source
      rw [e.right_inv hy.1]
      exact hy.2
    · intro hx
      exact ⟨e x, ⟨e.map_source hx.1, hx.2⟩, e.left_inv hx.1⟩
  · exact hgU.trans heU

end DifferentialGeometry.Topology.PiecewiseLinear
