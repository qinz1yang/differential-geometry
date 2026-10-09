/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ChartPiece
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOn
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.Moise304Producer

open Set Topology
open scoped Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

section MaximalAtlas

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

theorem isPLHomeomorphInto_symm_of_mem_maximalAtlas
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hc : c ∈ (plGroupoid n).maximalAtlas M) {D : Set (EuclideanSpace ℝ (Fin n))}
    (hD : IsPolyhedron D) (hDc : D ⊆ c.target) : IsPLHomeomorphInto n c.symm D := by
  have hmaps : c.symm '' D ⊆ c.source := by
    rintro _ ⟨x, hx, rfl⟩
    exact c.map_target (hDc hx)
  refine ⟨fun x hx => ?_, injOn_symm_of_subset_target c hDc, ?_⟩
  · rw [StructureGroupoid.liftPropWithinAt_self_source]
    refine ⟨(c.continuousOn_symm x (hDc hx)).mono hDc, ?_⟩
    set e := chartAt (EuclideanSpace ℝ (Fin n)) (c.symm x) with he
    have hT : c.symm ≫ₕ e ∈ plGroupoid n :=
      StructureGroupoid.compatible_of_mem_maximalAtlas_left hc
    have hxT : x ∈ (c.symm ≫ₕ e).source := by
      rw [OpenPartialHomeomorph.trans_source, c.symm_source]
      exact ⟨hDc hx, mem_chart_source _ _⟩
    have hpa : IsPiecewiseAffineWithinAt (c.symm ≫ₕ e) (univ ∩ (c.symm ≫ₕ e).source) x := by
      rw [univ_inter]
      exact (mem_plGroupoid_iff.mp hT).1 x hxT
    exact (hpa.of_inter_of_mem_nhds ((c.symm ≫ₕ e).open_source.mem_nhds hxT)).mono_of_isPolyhedron
      hD (subset_univ D)
  · rintro _ ⟨x₀, hx₀, rfl⟩
    refine ⟨c, ?_, fun x hx => c.right_inv (hDc hx)⟩
    have hy : c.symm x₀ ∈ c.source := c.map_target (hDc hx₀)
    change ChartedSpace.LiftPropWithinAt (piecewiseAffineProperty n n) c (c.symm '' D) (c.symm x₀)
    rw [StructureGroupoid.liftPropWithinAt_self_target]
    refine ⟨(c.continuousOn _ hy).mono hmaps, ?_⟩
    set e := chartAt (EuclideanSpace ℝ (Fin n)) (c.symm x₀) with he
    have hye : c.symm x₀ ∈ e.source := mem_chart_source _ _
    have hT : e.symm ≫ₕ c ∈ plGroupoid n :=
      StructureGroupoid.compatible_of_mem_maximalAtlas_right hc
    have hx₀T : x₀ ∈ (e.symm ≫ₕ c).target := by
      rw [OpenPartialHomeomorph.trans_target, e.symm_target]
      exact ⟨hDc hx₀, hye⟩
    obtain ⟨Q, hQ, hQT, hQx⟩ :=
      exists_isHPolytope_subset_mem_nhds ((e.symm ≫ₕ c).open_target.mem_nhds hx₀T)
    have hDQ : IsPolyhedron (D ∩ Q) := hD.inter hQ.isPolyhedron
    have hDQT : D ∩ Q ⊆ (e.symm ≫ₕ c).target := inter_subset_right.trans hQT
    have hsymm : IsPiecewiseAffineOn (e.symm ≫ₕ c).symm (D ∩ Q) :=
      (mem_plGroupoid_iff.mp hT).2.mono_of_isPolyhedron hDQ hDQT
    have hinj : InjOn (e.symm ≫ₕ c).symm (D ∩ Q) :=
      (e.symm ≫ₕ c).symm.injOn.mono (by rw [OpenPartialHomeomorph.symm_source]; exact hDQT)
    have hhom := isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hDQ hsymm hinj.bijOn_image
    have hTpa : IsPiecewiseAffineOn (e.symm ≫ₕ c) ((e.symm ≫ₕ c).symm '' (D ∩ Q)) := by
      refine hhom.2.2.congr ?_
      rintro _ ⟨w, hw, rfl⟩
      rw [hinj.leftInvOn_invFunOn hw]
      exact (e.symm ≫ₕ c).right_inv (hDQT hw)
    have hz₀ : e (c.symm x₀) ∈ (e.symm ≫ₕ c).symm '' (D ∩ Q) :=
      ⟨x₀, ⟨hx₀, mem_of_mem_nhds hQx⟩, rfl⟩
    have hsub : (e.symm ≫ₕ c).symm '' (D ∩ Q) ⊆ e.symm ⁻¹' (c.symm '' D) := by
      rintro _ ⟨w, hw, rfl⟩
      have hw' : c.symm w ∈ e.source := by
        have h := hDQT hw
        rw [OpenPartialHomeomorph.trans_target, e.symm_target] at h
        exact h.2
      change e.symm (e (c.symm w)) ∈ c.symm '' D
      rw [e.left_inv hw']
      exact ⟨w, hw.1, rfl⟩
    have hnhd : (e.symm ≫ₕ c).symm '' (D ∩ Q) ∈ 𝓝[e.symm ⁻¹' (c.symm '' D)] (e (c.symm x₀)) := by
      refine mem_nhdsWithin.mpr ⟨(e.symm ≫ₕ c).source ∩ (e.symm ≫ₕ c) ⁻¹' interior Q,
        (e.symm ≫ₕ c).isOpen_inter_preimage isOpen_interior, ⟨?_, ?_⟩, ?_⟩
      · rw [OpenPartialHomeomorph.trans_source, e.symm_source]
        refine ⟨e.map_source hye, ?_⟩
        change e.symm (e (c.symm x₀)) ∈ c.source
        rw [e.left_inv hye]
        exact hy
      · change c (e.symm (e (c.symm x₀))) ∈ interior Q
        rw [e.left_inv hye, c.right_inv (hDc hx₀)]
        exact mem_interior_iff_mem_nhds.mpr hQx
      · rintro z ⟨⟨hzT, hzQ⟩, ⟨w, hw, hwz⟩⟩
        have hTz : (e.symm ≫ₕ c) z = w := by
          change c (e.symm z) = w
          rw [← hwz, c.right_inv (hDc hw)]
        refine ⟨w, ⟨hw, ?_⟩, ?_⟩
        · rw [← hTz]
          exact interior_subset hzQ
        · rw [← hTz]
          exact (e.symm ≫ₕ c).left_inv hzT
    obtain ⟨ι, hι, C, A, hC, hCx⟩ := hTpa _ hz₀
    exact ⟨ι, hι, C, A, fun i => ⟨(hC i).1, (hC i).2.1.trans hsub, (hC i).2.2⟩,
      nhdsWithin_le_of_mem hnhd hCx⟩

end MaximalAtlas

theorem Moise305Tame.exists_isPLCellOn_of_mem_maximalAtlas
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    (hc : c ∈ (plGroupoid 3).maximalAtlas M) {C₁ C₂ : Set M} (hC₂ : C₂ ⊆ c.source)
    (hcell₁ : IsTopologicalCell 3 (c '' C₁)) (hcell₂ : IsTopologicalCell 3 (c '' C₂))
    (hC₁₂ : C₁ ⊆ interior C₂)
    (hshell : IsSphericalShell (closure (c '' C₂ \ c '' C₁)) (frontier (c '' C₁))
      (frontier (c '' C₂)))
    (hbi : IsBicollared (frontier (c '' C₂))) :
    ∃ C B : Set M, IsPLCellOn 3 C B ∧ C₁ ⊆ interior C ∧ C ⊆ interior C₂ := by
  have hint : interior C₂ ⊆ c.source := interior_subset.trans hC₂
  have hsub : c '' C₁ ⊆ interior (c '' C₂) :=
    (image_mono hC₁₂).trans (interior_maximal (image_mono interior_subset)
      (c.isOpen_image_of_subset_source isOpen_interior hint))
  obtain ⟨D, hD, hD₁, hD₂⟩ := moise305Tame _ _ hcell₁ hcell₂ hsub hshell hbi
  have hDt : D ⊆ c.target := by
    refine (hD₂.trans interior_subset).trans ?_
    rintro _ ⟨x, hx, rfl⟩
    exact c.map_source (hC₂ hx)
  obtain ⟨r, hr⟩ := id hD
  have hemb := isPLHomeomorphInto_symm_of_mem_maximalAtlas hc hD.isPolyhedron hDt
  refine ⟨c.symm '' D, c.symm '' (r '' stdSimplexBoundary 3), ⟨D, r, c.symm, hr, hemb, rfl, rfl⟩,
    ?_, ?_⟩
  · refine fun x hx => interior_maximal (image_mono interior_subset)
      (c.isOpen_image_symm_of_subset_target isOpen_interior (interior_subset.trans hDt)) ?_
    refine ⟨c x, hD₁ ⟨x, hx, rfl⟩, c.left_inv (hC₂ (interior_subset (hC₁₂ hx)))⟩
  · have hopen : IsOpen (c.symm '' interior (c '' C₂)) :=
      c.isOpen_image_symm_of_subset_target isOpen_interior
        (interior_subset.trans (image_subset_iff.mpr fun x hx => c.map_source (hC₂ hx)))
    exact (image_mono hD₂).trans (interior_maximal ((image_mono interior_subset).trans
      (c.symm_image_image_of_subset_source hC₂).subset) hopen)

end DifferentialGeometry.Topology.PiecewiseLinear
