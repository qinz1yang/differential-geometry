/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ChartImagePLCell
import DifferentialGeometry.Topology.PiecewiseLinear.PieceTransition
import DifferentialGeometry.Topology.PiecewiseLinear.PLModelCellRestriction

open Set Topology
open scoped Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem exists_maximalAtlas_chart_eventuallyEq_of_mem_atlas
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {e c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (he : e ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (hc : c ∈ (plGroupoid n).maximalAtlas M) {y : M}
    (hye : y ∈ e.source) (hyc : y ∈ c.source) :
    ∃ d : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)),
      d ∈ (plGroupoid n).maximalAtlas M ∧ y ∈ d.source ∧ d y = e y ∧
      (⇑d =ᶠ[𝓝 y] e) ∧ (⇑d.symm =ᶠ[𝓝 (e y)] e.symm) := by
  let τ := c.symm ≫ₕ e
  have hτ : τ ∈ plGroupoid n := (hc e he).1
  let d := c ≫ₕ τ
  refine ⟨d, ?_, ?_, ?_, ?_, ?_⟩
  · intro e' he'
    constructor
    · simpa only [d, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_assoc] using
        (plGroupoid n).trans ((plGroupoid n).symm hτ) (hc e' he').1
    · simpa only [d, OpenPartialHomeomorph.trans_assoc] using
        (plGroupoid n).trans (hc e' he').2 hτ
  · change y ∈ c.source ∩ c ⁻¹' τ.source
    refine ⟨hyc, ?_⟩
    change c y ∈ c.target ∩ c.symm ⁻¹' e.source
    exact ⟨c.map_source hyc, by rw [mem_preimage, c.left_inv hyc]; exact hye⟩
  · change e (c.symm (c y)) = e y
    rw [c.left_inv hyc]
  · filter_upwards [c.eventually_left_inverse hyc] with z hz
    change e (c.symm (c z)) = e z
    rw [hz]
  · have hcN : c.source ∈ 𝓝 (e.symm (e y)) := by
      rw [e.left_inv hye]
      exact c.open_source.mem_nhds hyc
    have hN := (e.continuousAt_symm (e.map_source hye)).preimage_mem_nhds hcN
    filter_upwards [hN] with z hz
    change c.symm (c (e.symm z)) = e.symm z
    exact c.left_inv hz

private theorem isPiecewiseAffineWithinAt_chart_symm_of_maximalAtlas
    {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
    {g : M → E3} {S : Set M} {y : M} (hg : IsPLWithinAt 3 3 g S y)
    {e c : OpenPartialHomeomorph M E3} (he : e ∈ atlas E3 M)
    (hc : c ∈ (plGroupoid 3).maximalAtlas M) (hye : y ∈ e.source)
    (hyc : y ∈ c.source) :
    IsPiecewiseAffineWithinAt (g ∘ e.symm) (e.target ∩ e.symm ⁻¹' S) (e y) := by
  obtain ⟨d, hd, hyd, hdy, -, hinv⟩ :=
    exists_maximalAtlas_chart_eventuallyEq_of_mem_atlas he hc hye hyc
  have hgcoord := hg.prop
  change IsPiecewiseAffineWithinAt (g ∘ (chartAt E3 y).symm)
    ((chartAt E3 y).symm ⁻¹' S) (chartAt E3 y y) at hgcoord
  have hcoord : IsPiecewiseAffineWithinAt (g ∘ d.symm) (d.symm ⁻¹' S) (d y) :=
    (piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_indep_chart_source_aux
      g hd hyd).mp hgcoord
  rw [hdy] at hcoord
  have hsets : (d.symm ⁻¹' S : Set E3) =ᶠ[𝓝 (e y)]
      (e.target ∩ e.symm ⁻¹' S : Set E3) := by
    filter_upwards [hinv, e.open_target.mem_nhds (e.map_source hye)] with z hz hzt
    change (d.symm z ∈ S) = (z ∈ e.target ∧ e.symm z ∈ S)
    apply propext
    rw [hz]
    exact ⟨fun h => ⟨hzt, h⟩, fun h => h.2⟩
  have hfun : (g ∘ d.symm) =ᶠ[𝓝 (e y)] (g ∘ e.symm) := by
    filter_upwards [hinv] with z hz
    exact congrArg g hz
  exact (piecewiseAffineProperty_localInvariantProp.congr_set_fun hsets hfun).mp hcoord

theorem IsPLSphere.isPolyhedralSphere_image_of_maximalAtlas_cover
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E3 M]
    {m : ℕ} {J P : Set E3} {u : E3 → M} (hJ : IsPLSphere m J)
    (hu : IsPLHomeomorphInto 3 u P) (hJP : J ⊆ P)
    (hcharts : ∀ y ∈ u '' J, ∃ c : OpenPartialHomeomorph M E3,
      c ∈ (plGroupoid 3).maximalAtlas M ∧ y ∈ c.source) :
    IsPolyhedralSphere (n := 3) m (u '' J) := by
  classical
  have huPL : IsPLOn 3 3 u J := hu.isPLOn.mono_of_isPolyhedron hJ.isPolyhedron hJP
  have huJ : IsPLHomeomorphInto 3 u J :=
    huPL.isPLHomeomorphInto_of_isCompact hJ.isPolyhedron.isCompact (hu.injOn.mono hJP)
  have hinv := huJ.isPLOn_inverse huJ.injOn.leftInvOn_invFunOn
  obtain ⟨K, hKfin, hKJ⟩ := hJ.isPolyhedron.exists_simplicialComplex
  let T : PLPieceIn E3 3 M (u '' J) :=
    { complex := K
      finite_faces := hKfin
      map := u
      bijOn := by rw [hKJ]; exact huJ.injOn.bijOn_image
      continuousOn := hKJ.symm ▸ huJ.continuousOn
      isPiecewiseAffineOn_chart := fun e he => by
        rw [hKJ]
        apply isPLOn_iff_isPiecewiseAffineOn.mp
        intro x hx
        obtain ⟨c, hc, huc⟩ := hcharts (u x) ⟨x, hx.1, rfl⟩
        obtain ⟨d, hd, hud, -, hde, -⟩ :=
          exists_maximalAtlas_chart_eventuallyEq_of_mem_atlas he hc hx.2 huc
        have hePL : IsPLAt 3 3 e (u x) :=
          piecewiseAffineProperty_localInvariantProp.liftPropAt_congr_of_eventuallyEq
            (isPLAt_of_mem_maximalAtlas hd hud) hde.symm
        have hN : J ∩ u ⁻¹' e.source ∈ 𝓝[J] x :=
          Filter.inter_mem self_mem_nhdsWithin
            ((huJ.continuousOn x hx.1).preimage_mem_nhdsWithin (e.open_source.mem_nhds hx.2))
        exact hePL.comp_isPLWithinAt
          (IsPLWithinAt.mono_of_mem_nhdsWithin (huPL x hx.1) inter_subset_left hN)
      isPiecewiseAffineOn_chart_symm := fun e he => by
        rw [hKJ]
        intro z hz
        obtain ⟨c, hc, hyc⟩ := hcharts (e.symm z) hz.2
        have hcoord := isPiecewiseAffineWithinAt_chart_symm_of_maximalAtlas
          (hinv (e.symm z) hz.2) he hc (e.map_target hz.1) hyc
        rwa [e.right_inv hz.1] at hcoord }
  exact isPolyhedralSphere_of_pieceIn T (hKJ.symm ▸ hJ)

end DifferentialGeometry.Topology.PiecewiseLinear
