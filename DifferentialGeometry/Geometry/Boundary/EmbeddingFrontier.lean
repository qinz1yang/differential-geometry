import DifferentialGeometry.Geometry.Boundary.FullRankFactorization
import DifferentialGeometry.Topology.Manifold.ConnectedInterior
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Boundary

open DifferentialGeometry
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

variable {E H W F H' M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace W] [ChartedSpace H W] [HasSmoothBoundary E H I] [IsManifold I ∞ W]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H' M] [IsManifold J ∞ M]
  [BoundarylessManifold J M]

omit [HasSmoothBoundary E H I] [IsManifold I ∞ W] [IsManifold J ∞ M]
  [BoundarylessManifold J M] in
theorem mem_interior_range_of_injective_mfderiv
    (ι : W → M) {w : W} (hι : ContMDiffAt I J ∞ ι w)
    (hinj : Function.Injective (mfderiv I J ι w))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (hw : I.IsInteriorPoint w) : ι w ∈ interior (range ι) := by
  let p := extChartAt I w
  let q := extChartAt J (ι w)
  let g : E → F := q ∘ ι ∘ p.symm
  have hmodel : range I ∈ 𝓝 (p w) := mem_interior_iff_mem_nhds.mp hw
  have hg : ContDiffAt ℝ ∞ g (p w) :=
    (contMDiffAt_iff.mp hι).2.contDiffAt hmodel
  let D : E →L[ℝ] F := mfderiv I J ι w
  let A : E ≃L[ℝ] F := (D.toLinearMap.linearEquivOfInjective hinj hdim).toContinuousLinearEquiv
  have hd : HasFDerivAt g (A : E →L[ℝ] F) (p w) :=
    (hι.mdifferentiableAt (by decide)).hasMFDerivAt.2.hasFDerivAt hmodel
  have hmap : Filter.map g (𝓝 (p w)) = 𝓝 (q (ι w)) := by
    rw [(hg.hasStrictFDerivAt' hd (by simp)).map_nhds_eq_of_equiv]
    simp only [g, p, Function.comp_apply, extChartAt_to_inv]
  let U := p.target ∩ (ι ∘ p.symm) ⁻¹' q.source
  have hU : U ∈ 𝓝 (p w) := by
    apply inter_mem (mem_interior_iff_mem_nhds.mp (I.isInteriorPoint_iff.mp hw))
    have hιp : ContinuousAt ι (p.symm (p w)) := by
      simpa only [p, extChartAt_to_inv] using hι.continuousAt
    have hcont : ContinuousAt (ι ∘ p.symm) (p w) :=
      hιp.comp (continuousAt_extChartAt_symm w)
    apply hcont.preimage_mem_nhds
    simpa only [p, Function.comp_apply, extChartAt_to_inv] using
      (extChartAt_source_mem_nhds (I := J) (ι w))
  have himage : g '' U ∈ 𝓝 (q (ι w)) := by
    rw [← hmap]
    exact Filter.image_mem_map hU
  have hnear := (continuousAt_extChartAt (I := J) (ι w)).preimage_mem_nhds himage
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [hnear, extChartAt_source_mem_nhds (I := J) (ι w)] with y hy hys
  obtain ⟨z, hz, hzy⟩ := hy
  exact ⟨p.symm z, q.injOn hz.2 hys hzy⟩

theorem isInteriorPoint_of_mem_interior_range_of_fullRank_embedding
    (ι : W → M) (hι : ContMDiff I J ∞ ι) (hemb : IsEmbedding ι)
    (hinj : ∀ w, Function.Injective (mfderiv I J ι w))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    {w : W} (hw : ι w ∈ interior (range ι)) : I.IsInteriorPoint w := by
  classical
  let V : TopologicalSpace.Opens M := ⟨interior (range ι), isOpen_interior⟩
  have hpre (y : V) : ∃ x : W, ι x = (y : M) := by
    have hy : (y : M) ∈ range ι := interior_subset y.property
    exact hy
  choose g hg using hpre
  have hcomp : ι ∘ g = (Subtype.val : V → M) := funext hg
  have hgs : ContMDiff J I ∞ g := by
    apply (contMDiff_iff_comp_of_fullRank_embedding hι hemb hinj hdim g).mpr
    rw [hcomp]
    exact contMDiff_subtype_val
  let y : V := ⟨ι w, hw⟩
  have hgy : g y = w := hemb.injective (hg y)
  have hchain : (mfderiv I J ι (g y)).comp (mfderiv J I g y) =
      ContinuousLinearMap.id ℝ F := by
    rw [← mfderiv_comp y (hι.mdifferentiable (by decide) (g y))
      (hgs.mdifferentiable (by decide) y), hcomp, mfderiv_subtype_val]
  have hgi : Function.Injective (mfderiv J I g y) := by
    intro v z hvz
    have heq := congrArg (mfderiv I J ι (g y)) hvz
    change ((mfderiv I J ι (g y)).comp (mfderiv J I g y)) v =
      ((mfderiv I J ι (g y)).comp (mfderiv J I g y)) z at heq
    rw [hchain] at heq
    exact heq
  let A : F →L[ℝ] E := mfderiv J I g y
  have hsurj : Function.Surjective (mfderiv J I g y) :=
    (A.toLinearMap.linearEquivOfInjective hgi hdim.symm).surjective
  have hi := (hgs.mdifferentiable (by decide) y).isInteriorPoint_of_surjective_mfderiv
    hsurj (BoundarylessManifold.isInteriorPoint (I := J) (x := y))
  rwa [hgy] at hi

theorem image_interior_eq_of_fullRank_embedding
    (ι : W → M) (hι : ContMDiff I J ∞ ι) (hemb : IsEmbedding ι)
    (hinj : ∀ w, Function.Injective (mfderiv I J ι w))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    ι '' I.interior W = interior (range ι) := by
  apply Subset.antisymm
  · rintro _ ⟨w, hw, rfl⟩
    exact mem_interior_range_of_injective_mfderiv ι (hι w) (hinj w) hdim hw
  · intro y hy
    have hmem : y ∈ range ι := interior_subset hy
    obtain ⟨w, rfl⟩ := hmem
    exact ⟨w, isInteriorPoint_of_mem_interior_range_of_fullRank_embedding
      ι hι hemb hinj hdim hy, rfl⟩

theorem image_boundary_eq_frontier_of_fullRank_closedEmbedding
    (ι : W → M) (hι : ContMDiff I J ∞ ι) (hemb : IsClosedEmbedding ι)
    (hinj : ∀ w, Function.Injective (mfderiv I J ι w))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    ι '' I.boundary W = frontier (range ι) := by
  rw [← I.compl_interior, image_compl_eq_range_sdiff_image hemb.injective,
    image_interior_eq_of_fullRank_embedding ι hι hemb.isEmbedding hinj hdim,
    frontier, hemb.isClosed_range.closure_eq]

theorem closure_interior_range_of_fullRank_closedEmbedding
    (ι : W → M) (hι : ContMDiff I J ∞ ι) (hemb : IsClosedEmbedding ι)
    (hinj : ∀ w, Function.Injective (mfderiv I J ι w))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    closure (interior (range ι)) = range ι := by
  have hd : closure (I.interior W) = univ := dense_iff_closure_eq.mp
    (DifferentialGeometry.Topology.Manifold.dense_manifold_interior (I := I) (M := W))
  rw [← image_interior_eq_of_fullRank_embedding ι hι hemb.isEmbedding hinj hdim,
    hemb.isClosedMap.closure_image_eq_of_continuous hι.continuous, hd, image_univ]

theorem isPreconnected_interior_range_of_fullRank_embedding [PreconnectedSpace W]
    (ι : W → M) (hι : ContMDiff I J ∞ ι) (hemb : IsEmbedding ι)
    (hinj : ∀ w, Function.Injective (mfderiv I J ι w))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    IsPreconnected (interior (range ι)) := by
  rw [← image_interior_eq_of_fullRank_embedding ι hι hemb hinj hdim]
  exact (DifferentialGeometry.Topology.Manifold.isPreconnected_manifold_interior (I := I) (M := W)).image
    ι hι.continuous.continuousOn

end DifferentialGeometry.Geometry.Boundary
