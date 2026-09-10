import DifferentialGeometry.Geometry.Boundary.FullRankFactorization
import Mathlib.Geometry.Manifold.Diffeomorph

noncomputable section
open Set Topology Manifold
open scoped ContDiff

namespace DifferentialGeometry.Geometry.Boundary

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

variable {E H W F H' M G H'' P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace W] [ChartedSpace H W] [HasSmoothBoundary E H I] [IsManifold I ∞ W]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H' M] [IsManifold J ∞ M]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H''] {L : ModelWithCorners ℝ G H''}
  [TopologicalSpace P] [ChartedSpace H'' P]

theorem exists_diffeomorph_of_smooth_partial_equiv_to_range
    (ι : W → M) (hι : ContMDiff I J ∞ ι) (hemb : IsEmbedding ι)
    (hinj : ∀ w, Function.Injective (mfderiv I J ι w))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (e : PartialEquiv P M) (hes : e.source = univ) (het : e.target = range ι)
    (he : ContMDiff L J ∞ e) (hei : ContMDiffOn J L ∞ e.symm e.target) :
    ∃ D : Diffeomorph L I P W ∞, ∀ p, ι (D p) = e p := by
  have hmem (p : P) : e p ∈ range ι := by
    rw [← het]
    exact e.map_source (hes ▸ mem_univ p)
  choose f hf using hmem
  have hleft (p : P) : e.symm (ι (f p)) = p := by
    rw [hf]
    exact e.left_inv (hes ▸ mem_univ p)
  have hright (w : W) : f (e.symm (ι w)) = w := by
    apply hemb.injective
    rw [hf]
    exact e.right_inv (het ▸ mem_range_self w)
  have hfe : ι ∘ f = e := funext hf
  have hfs : ContMDiff L I ∞ f :=
    (contMDiff_iff_comp_of_fullRank_embedding hι hemb hinj hdim f).mpr (hfe ▸ he)
  have hgs : ContMDiff I L ∞ (fun w ↦ e.symm (ι w)) := by
    apply contMDiffOn_univ.mp
    exact hei.comp hι.contMDiffOn (fun w _ ↦ het ▸ mem_range_self w)
  let D : Diffeomorph L I P W ∞ :=
    { toEquiv :=
        { toFun := f
          invFun := fun w ↦ e.symm (ι w)
          left_inv := hleft
          right_inv := hright }
      contMDiff_toFun := hfs
      contMDiff_invFun := hgs }
  exact ⟨D, hf⟩

end DifferentialGeometry.Geometry.Boundary
