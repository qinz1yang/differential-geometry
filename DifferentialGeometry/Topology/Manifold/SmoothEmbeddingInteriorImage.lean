import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingInterior

set_option autoImplicit false

noncomputable section

open Set Manifold
open scoped Manifold ContDiff Topology

namespace Manifold

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  {f : M → N} {x : M}

theorem IsSmoothEmbedding.isInteriorPoint_of_mem_interior_range
    (hf : IsSmoothEmbedding I J ∞ f)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (hx : f x ∈ interior (range f)) (hfx : J.IsInteriorPoint (f x)) :
    I.IsInteriorPoint x := by
  let U : TopologicalSpace.Opens N := ⟨interior (range f), isOpen_interior⟩
  let y : U := ⟨f x, hx⟩
  have hsub : range (Subtype.val : U → N) ⊆ range f := by
    rintro _ ⟨z, rfl⟩
    exact interior_subset z.property
  let g : U → M := hf.lift (Subtype.val : U → N) hsub
  have hg : ContMDiff J I ∞ g :=
    hf.contMDiff_lift (contMDiff_subtype_val (I := J) (U := U)) hsub
  have hgy : g y = x := hf.isEmbedding.injective (hf.comp_lift hsub y)
  have hcomp : f ∘ g = (Subtype.val : U → N) := funext (hf.comp_lift hsub)
  have hfull : Function.Injective (mfderiv J J (f ∘ g) y) := by
    rw [hcomp]
    exact ((IsSmoothEmbedding.of_opens (I := J) (n := ∞) U).isImmersion.isImmersionAt y).injective_mfderiv
      (by simp)
  rw [mfderiv_comp y (hf.contMDiff.mdifferentiableAt (by simp))
    (hg.mdifferentiableAt (by simp))] at hfull
  have hinj : Function.Injective (mfderiv J I g y) := Function.Injective.of_comp hfull
  let L : F →L[ℝ] E := mfderiv J I g y
  have hsurj : Function.Surjective (mfderiv J I g y) :=
    (L.toLinearMap.linearEquivOfInjective hinj hdim.symm).surjective
  have hi : I.IsInteriorPoint (g y) :=
    (hg.mdifferentiableAt (by simp)).isInteriorPoint_of_surjective_mfderiv hsurj
      (J.isInteriorPoint_iff_isInteriorPoint_val.mpr hfx)
  rwa [hgy] at hi

end Manifold
