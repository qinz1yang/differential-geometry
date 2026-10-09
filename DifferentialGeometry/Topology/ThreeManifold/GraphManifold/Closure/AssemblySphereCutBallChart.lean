import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelocation
import DifferentialGeometry.Topology.Manifold.ClosedBall.Extension
import DifferentialGeometry.Topology.Manifold.InteriorAtlas
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingOpenTarget
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph

/-!
# Chapter-14 assembly, L2-relative: the ball chart of an interior cap

Lane ASM-L2b, group G2b (first part). A smoothly embedded closed `3`-cell whose image lies in the
interior of a `3`-manifold (possibly with boundary) extends to a partial diffeomorphism from an
open subset of `ℝ³` containing the closed unit ball, with image in the interior.

* `extend_mem_interior_range_of_mem_maximalAtlas`: interior points are sent to the interior of the
  model range by every chart of the maximal atlas (Mathlib states this for atlas charts only;
  the proof is the same).
* `extendInteriorChart`, `extendInteriorChart_mem_maximalAtlas`: a chart of the maximal atlas,
  extended and restricted to the interior of its target, is a chart of the interior atlas
  (`Manifold.interiorChartedSpace`, `InteriorAtlas.lean`).
* `isSmoothEmbedding_interiorAtlas`: smooth embeddings into a manifold without boundary points stay
  smooth embeddings for the interior atlas.
* `exists_ballChart_of_closedCell_interior`: the extension, by
  `exists_partialDiffeomorph_extension_closedCell` (`Manifold/ClosedBall/Extension.lean:27`) applied
  in the intrinsic interior.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

section InteriorAtlas

variable {E F H H' M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]

/-- Every chart of the maximal atlas sends an interior point into the interior of the model range.
Mathlib's `ModelWithCorners.mem_interior_range_of_mem_interior_range_of_mem_atlas` states this for
atlas charts; the proof only uses maximal-atlas membership. -/
theorem extend_mem_interior_range_of_mem_maximalAtlas [IsManifold J ∞ N]
    {e : OpenPartialHomeomorph N H'} (he : e ∈ IsManifold.maximalAtlas J ∞ N) {x : N}
    (hex : x ∈ e.source) (hx : J.IsInteriorPoint x) : e.extend J x ∈ interior (range J) := by
  let e₀ := chartAt H' x
  have hex₀ : x ∈ e₀.source := mem_chart_source H' x
  have he₀ : e₀ ∈ IsManifold.maximalAtlas J ∞ N := IsManifold.chart_mem_maximalAtlas x
  have hx₀ : e₀.extend J x ∈ interior (e₀.extend J).target := J.isInteriorPoint_iff.mp hx
  let φ := J.extendCoordChange e₀ e
  have hφ : ContDiffOn ℝ ∞ φ φ.source := J.contDiffOn_extendCoordChange he₀ he
  have hφs : Function.Surjective (fderivWithin ℝ φ φ.source (e₀.extend J x)) :=
    (J.isInvertible_fderivWithin_extendCoordChange (by simp) he₀ he
      (by simp [e₀, hex₀, hex])).surjective
  have hφx : φ.source ∈ 𝓝 (e₀.extend J x) := by
    simp_rw [φ, ModelWithCorners.extendCoordChange, PartialEquiv.trans_source,
      PartialEquiv.symm_source, Filter.inter_mem_iff, mem_interior_iff_mem_nhds.1 hx₀, true_and,
      e.extend_source]
    exact e₀.extend_preimage_mem_nhds hex₀ <| e.open_source.mem_nhds hex
  rw [fderivWithin_of_mem_nhds hφx] at hφs
  rw [show e.extend J x = φ (e₀.extend J x) by simp [φ, e₀, hex₀]]
  exact ((hφ.differentiableOn (by simp)).differentiableAt hφx).mem_interior_convex_of_surjective_fderiv
    hφx J.convex_range J.isClosed_range J.nonempty_interior
    (φ.mapsTo.mono_right <| by simp [φ, inter_assoc]) hφs

variable (J) in
/-- A chart, extended to the model vector space and restricted to the interior of its target. -/
def extendInteriorChart (e : OpenPartialHomeomorph N H') : OpenPartialHomeomorph N F where
  toFun := e.extend J
  invFun := (e.extend J).symm
  source := e.source ∩ e.extend J ⁻¹' interior (e.extend J).target
  target := interior (e.extend J).target
  map_source' _ hy := hy.2
  map_target' y hy := by
    refine ⟨?_, ?_⟩
    · simpa only [e.extend_source] using (e.extend J).map_target (interior_subset hy)
    · change e.extend J ((e.extend J).symm y) ∈ interior (e.extend J).target
      rw [(e.extend J).right_inv (interior_subset hy)]
      exact hy
  left_inv' y hy := (e.extend J).left_inv (by simpa only [e.extend_source] using hy.1)
  right_inv' _ hy := (e.extend J).right_inv (interior_subset hy)
  open_source := e.isOpen_extend_preimage isOpen_interior
  open_target := isOpen_interior
  continuousOn_toFun := e.continuousOn_extend.mono (by
    rw [e.extend_source]
    exact inter_subset_left)
  continuousOn_invFun := e.continuousOn_extend_symm.mono interior_subset

omit [ChartedSpace H' N] in
theorem extendInteriorChart_apply (e : OpenPartialHomeomorph N H') (y : N) :
    extendInteriorChart J e y = J (e y) := rfl

/-- The restricted extension of a maximal-atlas chart belongs to the maximal atlas of the interior
atlas. -/
theorem extendInteriorChart_mem_maximalAtlas [IsManifold J ∞ N] [BoundarylessManifold J N]
    {e : OpenPartialHomeomorph N H'} (he : e ∈ IsManifold.maximalAtlas J ∞ N) :
    letI := DifferentialGeometry.Manifold.interiorChartedSpace J ∞ (M := N)
    extendInteriorChart J e ∈ IsManifold.maximalAtlas 𝓘(ℝ, F) ∞ N := by
  let := DifferentialGeometry.Manifold.interiorChartedSpace J ∞ (M := N)
  have := DifferentialGeometry.Manifold.interiorIsManifold J ∞ (M := N)
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · have h1 : ContMDiffOn J 𝓘(ℝ, F) ∞ (e.extend J) e.source := e.contMDiffOn_extend he
    exact h1.comp (DifferentialGeometry.Manifold.contMDiff_interiorAtlas_id J ∞).contMDiffOn
      (fun y hy => hy.1)
  · have h2 : ContMDiffOn 𝓘(ℝ, F) J ∞ (e.extend J).symm (J '' e.target) :=
      contMDiffOn_extend_symm he
    have hsub : interior (e.extend J).target ⊆ J '' e.target := by
      intro z hz
      have hz' := interior_subset hz
      rw [e.extend_target] at hz'
      exact ⟨J.symm z, hz'.1, J.right_inv hz'.2⟩
    exact (DifferentialGeometry.Manifold.contMDiff_id_interiorAtlas J ∞).comp_contMDiffOn
      (h2.mono hsub)

/-- A smooth embedding into a manifold without boundary points (for a model that may have
corners) is a smooth embedding for the interior atlas. -/
theorem isSmoothEmbedding_interiorAtlas [IsManifold J ∞ N] [BoundarylessManifold J N]
    {f : M → N} (hf : IsSmoothEmbedding I J ∞ f) :
    letI := DifferentialGeometry.Manifold.interiorChartedSpace J ∞ (M := N)
    IsSmoothEmbedding I 𝓘(ℝ, F) ∞ f := by
  let := DifferentialGeometry.Manifold.interiorChartedSpace J ∞ (M := N)
  have := DifferentialGeometry.Manifold.interiorIsManifold J ∞ (M := N)
  refine ⟨?_, hf.isEmbedding⟩
  obtain ⟨C, hC, hC', hImm⟩ := hf.isImmersion
  let := hC
  let := hC'
  refine IsImmersionOfComplement.isImmersion (F := C) ?_
  intro x
  let h := hImm x
  apply IsImmersionAtOfComplement.mk_of_continuousAt hf.isEmbedding.continuous.continuousAt
    h.equiv h.domChart (extendInteriorChart J h.codChart) h.mem_domChart_source ?_
    h.domChart_mem_maximalAtlas (extendInteriorChart_mem_maximalAtlas h.codChart_mem_maximalAtlas)
  · intro z hz
    exact h.writtenInCharts hz
  · refine ⟨h.mem_codChart_source, ?_⟩
    exact h.codChart.mem_interior_extend_target (h.codChart.map_source h.mem_codChart_source)
      (extend_mem_interior_range_of_mem_maximalAtlas h.codChart_mem_maximalAtlas
        h.mem_codChart_source BoundarylessManifold.isInteriorPoint)

end InteriorAtlas

section BallChart

local instance cellCharts_ASML2b : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  Handle.closedCellChartedSpaceSucc 2

local instance cellSmooth_ASML2b : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  Handle.closedCellIsManifold 2

variable {H M : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- **Ball chart of an interior cap.** A smooth embedding of the closed `3`-cell with image in the
interior extends to a partial diffeomorphism from an open subset of `ℝ³` containing the closed
unit ball, whose image lies in the interior. -/
theorem exists_ballChart_of_closedCell_interior (c : ClosedCell 3 → M)
    (hc : IsSmoothEmbedding (𝓡∂ 3) I ∞ c) (hcI : ∀ x, I.IsInteriorPoint (c x)) :
    ∃ φ : PartialDiffeomorph (𝓡 3) I (EuclideanSpace ℝ (Fin 3)) M ∞,
      Metric.closedBall 0 1 ⊆ φ.source ∧ (∀ y ∈ φ.target, I.IsInteriorPoint y) ∧
      ∀ x : ClosedCell 3, φ x.val = c x := by
  let U : TopologicalSpace.Opens M :=
    DifferentialGeometry.Manifold.intrinsicInterior I ∞ (by simp)
  have hUb : BoundarylessManifold I U :=
    DifferentialGeometry.Manifold.boundarylessManifold_intrinsicInterior I ∞ (by simp)
  let c' : ClosedCell 3 → U := fun x => ⟨c x, hcI x⟩
  have hc' : IsSmoothEmbedding (𝓡∂ 3) I ∞ c' :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_intoOpen (𝓡∂ 3) I U c' hc
  let := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  have := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  have hc'' : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ c' := isSmoothEmbedding_interiorAtlas hc'
  obtain ⟨φ, hsrc, hφ⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_partialDiffeomorph_extension_closedCell
      (m := 2) c' hc''
  let D := DifferentialGeometry.Manifold.interiorAtlasDiffeomorph I ∞ (M := U)
  have hne : Nonempty U := ⟨c' ⟨0, by simp⟩⟩
  let Φ := (φ.trans D.symm.toPartialDiffeomorph).trans
    (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph I U hne)
  refine ⟨Φ, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨hsrc hx, trivial⟩, trivial⟩
  · intro y hy
    have hy' : y ∈ (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph I U hne).target :=
      hy.1
    rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target] at hy'
    exact hy'
  · intro x
    change ((φ x.val : U) : M) = c x
    rw [hφ x]

end BallChart

end GC.GraphManifold.Assembly
