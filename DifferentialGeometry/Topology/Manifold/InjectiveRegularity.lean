import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

open Filter Set
open scoped Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G]
  {n : ℕ∞ω} {A : M → F →L[𝕜] G} {f : M → F} {x : M}

theorem ContMDiffWithinAt.of_clm_apply_of_injective
    {A : M → F →L[𝕜] G} {f : M → F} {u : Set M}
    (hA : ContMDiffWithinAt I 𝓘(𝕜, F →L[𝕜] G) n A u x)
    (hAf : ContMDiffWithinAt I 𝓘(𝕜, G) n (fun q => A q (f q)) u x)
    (hinj : Function.Injective (A x)) : ContMDiffWithinAt I 𝓘(𝕜, F) n f u x := by
  let _ : FiniteDimensional 𝕜 F := FiniteDimensional.of_injective (A x).toLinearMap hinj
  let _ : CompleteSpace F := FiniteDimensional.complete 𝕜 F
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective (A x).toLinearMap
    (LinearMap.ker_eq_bot_of_injective hinj)
  let B := L.toContinuousLinearMap
  have hBA : B.comp (A x) = ContinuousLinearMap.id 𝕜 F :=
    ContinuousLinearMap.ext fun v => LinearMap.congr_fun hL v
  let D := fun q => B.comp (A q)
  have hD : ContMDiffWithinAt I 𝓘(𝕜, F →L[𝕜] F) n D u x :=
    contMDiffWithinAt_const.clm_comp hA
  have hDp : (D x).IsInvertible := by
    rw [show D x = ContinuousLinearMap.id 𝕜 F from hBA]
    exact ⟨.refl 𝕜 F, rfl⟩
  have hInv := hDp.contDiffAt_map_inverse.comp_contMDiffWithinAt hD
  have h := hInv.clm_apply (B.contMDiff.contMDiffAt.comp_contMDiffWithinAt x hAf)
  apply h.congr_of_eventuallyEq
  · have hunit : ∀ᶠ q in 𝓝[u] x, IsUnit (D q) :=
      hD.continuousWithinAt (Units.isOpen.mem_nhds
        (by rw [show D x = ContinuousLinearMap.id 𝕜 F from hBA]; exact isUnit_one))
    filter_upwards [hunit] with q hq
    have hi : (D q).IsInvertible := ⟨ContinuousLinearEquiv.ofUnit hq.unit, hq.unit_spec⟩
    exact (hi.inverse_apply_self (f q)).symm
  · exact (hDp.inverse_apply_self (f x)).symm

theorem ContMDiffAt.of_clm_apply_of_injective
    (hA : ContMDiffAt I 𝓘(𝕜, F →L[𝕜] G) n A x)
    (hAf : ContMDiffAt I 𝓘(𝕜, G) n (fun y => A y (f y)) x)
    (hinj : Function.Injective (A x)) : ContMDiffAt I 𝓘(𝕜, F) n f x := by
  exact contMDiffWithinAt_univ.mp
    (hA.contMDiffWithinAt.of_clm_apply_of_injective hAf.contMDiffWithinAt hinj)

theorem ContMDiff.of_clm_apply_of_injective
    (hA : ContMDiff I 𝓘(𝕜, F →L[𝕜] G) n A)
    (hAf : ContMDiff I 𝓘(𝕜, G) n (fun y => A y (f y)))
    (hinj : ∀ y, Function.Injective (A y)) : ContMDiff I 𝓘(𝕜, F) n f :=
  fun y => (hA y).of_clm_apply_of_injective (hAf y) (hinj y)

theorem ContMDiffOn.of_clm_apply_of_injective
    {u : Set M}
    (hA : ContMDiffOn I 𝓘(𝕜, F →L[𝕜] G) n A u)
    (hAf : ContMDiffOn I 𝓘(𝕜, G) n (fun y => A y (f y)) u)
    (hinj : ∀ y ∈ u, Function.Injective (A y)) : ContMDiffOn I 𝓘(𝕜, F) n f u :=
  fun y hy => (hA y hy).of_clm_apply_of_injective (hAf y hy) (hinj y hy)
