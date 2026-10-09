import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# An injective, open-at-every-point immersion on an open set is a partial diffeomorphism
(lane S-COLLAR, G1, suffix `_HCOL`)

`exists_partialDiffeomorph_of_open_injOn_immersion_HCOL`: let `f : M → N` be an immersion at every
point of an open set `S`, injective on `S`, and open at every point of `S`
(`𝓝 (f y) ≤ map f (𝓝 y)`).  Then `f` is a `C^∞` partial diffeomorphism with source `S` and target
`f '' S`.  There is NO boundary hypothesis: the inverse is smooth because it is continuous and its
composite with the immersion `f` is the identity (`ContMDiffAt.iff_comp_isImmersionAt`).  Together
with `IsImmersionAt.nhds_le_map_of_halfSpace_HCOL` this is the inverse function theorem for models
with boundary.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Topology
open scoped Manifold ContDiff

namespace Manifold

universe u

variable {E : Type*} {E'' : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E'' G}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  {f : M → N}

/-- **Partial diffeomorphism from an injective open immersion on an open set.** -/
theorem exists_partialDiffeomorph_of_open_injOn_immersion_HCOL [Nonempty M] {S : Set M}
    (hS : IsOpen S) (hf : ∀ y ∈ S, IsImmersionAt I J ∞ f y)
    (hopen : ∀ y ∈ S, 𝓝 (f y) ≤ Filter.map f (𝓝 y)) (hinj : InjOn f S) :
    ∃ d : PartialDiffeomorph I J M N ∞,
      d.source = S ∧ d.target = f '' S ∧ (d : M → N) = f := by
  have hsm : ∀ y ∈ S, ContMDiffAt I J ∞ f y := fun y hy => (hf y hy).contMDiffAt
  let e₀ := hinj.toPartialEquiv f S
  have hopenmap : IsOpenMap (S.domRestrict f) := by
    apply IsOpenMap.of_nhds_le
    intro y
    change 𝓝 (f y.1) ≤ Filter.map (f ∘ Subtype.val) (𝓝 y)
    rw [← Filter.map_map, hS.isOpenEmbedding_subtypeVal.map_nhds_eq]
    exact hopen y.1 y.2
  let e := OpenPartialHomeomorph.ofContinuousOpenRestrict e₀
    (fun y hy => (hsm y hy).continuousAt.continuousWithinAt) hopenmap hS
  have hi : ContMDiffOn J I ∞ e.symm e.target := by
    intro y hy
    have hx : e.symm y ∈ S := e.map_target hy
    have himm : IsImmersionAt I J ∞ f (e.symm y) := hf _ hx
    have hcont : ContinuousAt e.symm y := e.continuousAt_symm hy
    have hcomp : ContMDiffAt J J ∞ (f ∘ e.symm) y := by
      have hid : ContMDiffAt J J ∞ (id : N → N) y := contMDiffAt_id
      refine hid.congr_of_eventuallyEq ?_
      filter_upwards [e.open_target.mem_nhds hy] with z hz
      exact e.right_inv hz
    exact ((ContMDiffAt.iff_comp_isImmersionAt (f := e.symm) (x := y) (φ := f) himm).mpr
      ⟨hcont, hcomp⟩).contMDiffWithinAt
  exact ⟨{ toPartialEquiv := e.toPartialEquiv
           open_source := hS
           open_target := e.open_target
           contMDiffOn_toFun := fun y hy => (hsm y hy).contMDiffWithinAt
           contMDiffOn_invFun := hi }, rfl, rfl, rfl⟩

end Manifold
