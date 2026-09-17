import DifferentialGeometry.Topology.Embedding.Extension
import DifferentialGeometry.Topology.Manifold.ImmersionCriterion
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingCompositionBoundary
import Mathlib.Geometry.Manifold.Instances.Icc

open Set
open scoped ContDiff Manifold Topology

namespace Manifold

theorem isImmersion_Icc_of_injective_mfderiv
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {a b : ℝ} [Fact (a < b)] {f : Icc a b → F}
    (hf : ContMDiff (𝓡∂ 1) 𝓘(ℝ, F) ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv (𝓡∂ 1) 𝓘(ℝ, F) f x)) :
    IsImmersion (𝓡∂ 1) 𝓘(ℝ, F) ∞ f := by
  let _ : ChartedSpace (EuclideanHalfSpace (0 + 1)) (Icc a b) :=
    inferInstanceAs (ChartedSpace (EuclideanHalfSpace 1) (Icc a b))
  let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
  have hi : IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ) ∞ (fun x : Icc a b => (x : ℝ)) :=
    isSmoothEmbedding_subtypeVal_Icc
  have hlocal (x : Icc a b) : IsImmersionAt (𝓡∂ 1) 𝓘(ℝ, F) ∞ f x := by
    obtain ⟨U, hU, hxU, G, hG, hGf⟩ := hi.exists_contDiffOn_local_extension_halfspace (d := 0) hf x
    have heq : G ∘ (fun x : Icc a b => (x : ℝ)) =ᶠ[𝓝 x] f := by
      filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds
        (hU.mem_nhds hxU)] with y hy
      exact hGf y hy
    have hGd := (hG.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)
    have hchain : mfderiv (𝓡∂ 1) 𝓘(ℝ, F) f x =
        (fderiv ℝ G (x : ℝ)).comp (mfderiv (𝓡∂ 1) 𝓘(ℝ) (fun y : Icc a b => (y : ℝ)) x) := by
      rw [← heq.mfderiv_eq]
      rw [mfderiv_comp x hGd.mdifferentiableAt (hi.contMDiff.mdifferentiableAt (by simp))]
      rw [mfderiv_eq_fderiv]
      rfl
    have hicoe := (hi.isImmersion.isImmersionAt x).injective_mfderiv (by simp)
    let _ : FiniteDimensional ℝ (TangentSpace (𝓡∂ 1) x) :=
      inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 1)))
    let _ : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ) (x : ℝ)) :=
      inferInstanceAs (FiniteDimensional ℝ ℝ)
    have hdim : Module.finrank ℝ (TangentSpace (𝓡∂ 1) x) =
        Module.finrank ℝ (TangentSpace 𝓘(ℝ) (x : ℝ)) := by
      change Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) = Module.finrank ℝ ℝ
      simp
    have hisurj : Function.Surjective
        (mfderiv (𝓡∂ 1) 𝓘(ℝ) (fun y : Icc a b => (y : ℝ)) x) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        hdim (f := (mfderiv (𝓡∂ 1) 𝓘(ℝ)
          (fun y : Icc a b => (y : ℝ)) x).toLinearMap)).mp hicoe
    have hGinj : Function.Injective (fderiv ℝ G (x : ℝ)) := by
      intro z w hzw
      obtain ⟨u, rfl⟩ := hisurj z
      obtain ⟨v, rfl⟩ := hisurj w
      apply congrArg (mfderiv (𝓡∂ 1) 𝓘(ℝ) (fun y : Icc a b => (y : ℝ)) x)
      apply hinj x
      rw [hchain]
      exact hzw
    let hGimm := DifferentialGeometry.Topology.Manifold.isImmersionAt_of_injective_hasFDerivAt
      (by simp : (∞ : ℕ∞ω) ≠ 0) hU hxU hG hGd.hasFDerivAt hGinj
    let hinc := hi.isImmersion.isImmersionAt x
    let _ : CompleteSpace hinc.complement :=
      Manifold.completeSpace_of_continuousLinearEquiv_prod hinc.equiv
    let _ : CompleteSpace hGimm.complement :=
      Manifold.completeSpace_of_continuousLinearEquiv_prod hGimm.equiv
    have hcomp := IsImmersionAtOfComplement.comp_of_isInteriorPoint_map
      hinc.isImmersionAtOfComplement_complement hGimm.isImmersionAtOfComplement_complement
      (by simp) (BoundarylessManifold.isInteriorPoint (I := 𝓘(ℝ)) (x := (x : ℝ)))
    exact hcomp.isImmersionAt.congr_of_eventuallyEq heq
  exact DifferentialGeometry.Topology.Manifold.isImmersion_of_isImmersionAt hlocal

end Manifold
