import DifferentialGeometry.Geometry.Boundary.FullRankFactorization
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.Homeomorph.Lemmas

noncomputable section
open Set Topology
open scoped Manifold ContDiff

namespace Poincare.Geometry.Boundary

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

variable {E H W F H' M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace W] [ChartedSpace H W] [HasSmoothBoundary E H I] [IsManifold I ∞ W]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H' M] [IsManifold J ∞ M]

def diffeomorphOfOpenSubsetRange
    (ι : W → M) (hι : ContMDiff I J ∞ ι) (hemb : IsEmbedding ι)
    (hinj : ∀ w, Function.Injective (mfderiv I J ι w))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (V : TopologicalSpace.Opens M) (hV : (V : Set M) ⊆ range ι) :
    (TopologicalSpace.Opens.comap ⟨ι, hι.continuous⟩ V) ≃ₘ⟮I, J⟯ V := by
  let U := TopologicalSpace.Opens.comap ⟨ι, hι.continuous⟩ V
  let e : U ≃ₜ V := hemb.homeomorphOfSubsetRange hV
  refine { toEquiv := e.toEquiv, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · apply (ContMDiff.subtypeVal_comp_iff V e).mp
    change ContMDiff I J ∞ (ι ∘ (Subtype.val : U → W))
    exact hι.comp contMDiff_subtype_val
  · apply (ContMDiff.subtypeVal_comp_iff U e.symm).mp
    apply (contMDiff_iff_comp_of_fullRank_embedding hι hemb hinj hdim
      ((Subtype.val : U → W) ∘ e.symm)).mpr
    have heq : ι ∘ ((Subtype.val : U → W) ∘ e.symm) = (Subtype.val : V → M) := by
      funext y
      change (e (e.symm y) : M) = (y : M)
      rw [e.apply_symm_apply]
    rw [heq]
    exact contMDiff_subtype_val

@[simp] theorem diffeomorphOfOpenSubsetRange_apply_coe
    (ι : W → M) (hι : ContMDiff I J ∞ ι) (hemb : IsEmbedding ι)
    (hinj : ∀ w, Function.Injective (mfderiv I J ι w))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (V : TopologicalSpace.Opens M) (hV : (V : Set M) ⊆ range ι)
    (w : TopologicalSpace.Opens.comap ⟨ι, hι.continuous⟩ V) :
    (diffeomorphOfOpenSubsetRange ι hι hemb hinj hdim V hV w : M) = ι (w : W) := rfl

theorem diffeomorphOfOpenSubsetRange_symm_apply_coe
    (ι : W → M) (hι : ContMDiff I J ∞ ι) (hemb : IsEmbedding ι)
    (hinj : ∀ w, Function.Injective (mfderiv I J ι w))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (V : TopologicalSpace.Opens M) (hV : (V : Set M) ⊆ range ι) (y : V) :
    ι ((diffeomorphOfOpenSubsetRange ι hι hemb hinj hdim V hV).symm y : W) = (y : M) := by
  rw [← diffeomorphOfOpenSubsetRange_apply_coe ι hι hemb hinj hdim V hV,
    Diffeomorph.apply_symm_apply]

end Poincare.Geometry.Boundary
