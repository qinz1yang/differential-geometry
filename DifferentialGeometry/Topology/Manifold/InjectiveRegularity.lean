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

theorem ContMDiffAt.of_clm_apply_of_injective
    (hA : ContMDiffAt I 𝓘(𝕜, F →L[𝕜] G) n A x)
    (hAf : ContMDiffAt I 𝓘(𝕜, G) n (fun y => A y (f y)) x)
    (hinj : Function.Injective (A x)) : ContMDiffAt I 𝓘(𝕜, F) n f x := by
  let _ : FiniteDimensional 𝕜 F := FiniteDimensional.of_injective (A x).toLinearMap hinj
  let _ : CompleteSpace F := FiniteDimensional.complete 𝕜 F
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective (A x).toLinearMap
    (LinearMap.ker_eq_bot_of_injective hinj)
  let B := L.toContinuousLinearMap
  have hBA : B.comp (A x) = ContinuousLinearMap.id 𝕜 F :=
    ContinuousLinearMap.ext fun v => LinearMap.congr_fun hL v
  let D := fun y => B.comp (A y)
  have hD : ContMDiffAt I 𝓘(𝕜, F →L[𝕜] F) n D x := contMDiffAt_const.clm_comp hA
  have hDx : (D x).IsInvertible := by rw [show D x = ContinuousLinearMap.id 𝕜 F from hBA]; exact ⟨.refl 𝕜 F, rfl⟩
  have hInv := hDx.contDiffAt_map_inverse.comp_contMDiffAt hD
  have h := hInv.clm_apply (B.contMDiff.contMDiffAt.comp x hAf)
  apply h.congr_of_eventuallyEq
  have hunit : ∀ᶠ y in 𝓝 x, IsUnit (D y) :=
    hD.continuousAt (Units.isOpen.mem_nhds (by rw [show D x = ContinuousLinearMap.id 𝕜 F from hBA]; exact isUnit_one))
  filter_upwards [hunit] with y hy
  have hi : (D y).IsInvertible := ⟨ContinuousLinearEquiv.ofUnit hy.unit, hy.unit_spec⟩
  exact (hi.inverse_apply_self (f y)).symm

theorem ContMDiff.of_clm_apply_of_injective
    (hA : ContMDiff I 𝓘(𝕜, F →L[𝕜] G) n A)
    (hAf : ContMDiff I 𝓘(𝕜, G) n (fun y => A y (f y)))
    (hinj : ∀ y, Function.Injective (A y)) : ContMDiff I 𝓘(𝕜, F) n f :=
  fun y => (hA y).of_clm_apply_of_injective (hAf y) (hinj y)
