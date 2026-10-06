import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# The tangent plane of a fibre slice of a product chart (lane O-G6C, G2i)

For a smooth embedding `φ : E × F → M` (a product chart) and a point `w₀` of the fibre model, the
plane `slicePlane_G6C φ x₀ w₀ = dφ_{(x₀, w₀)}({0} × T F)`:

* `finrank_slicePlane_G6C`: it has the dimension of the fibre (immersion);
* `mfderiv_eq_zero_of_mem_slicePlane_G6C`: the differential of every map that is constant on the
  slice `φ(x₀, ·)` vanishes on it.
-/

set_option autoImplicit false

open Set Function Manifold
open scoped ContDiff Manifold

noncomputable section

namespace DifferentialGeometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {EF HF F : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] [TopologicalSpace HF]
  {IF : ModelWithCorners ℝ EF HF} [TopologicalSpace F] [ChartedSpace HF F]
  {EM HM M : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ EM HM} [TopologicalSpace M] [ChartedSpace HM M]

/-- The tangent plane `dφ_{(x₀, w₀)}({0} × T F)` of the fibre slice of a product chart. -/
def slicePlane_G6C (φ : E × F → M) (x₀ : E) (w₀ : F) :
    Submodule ℝ (TangentSpace I (φ (x₀, w₀))) :=
  Submodule.map (mfderiv (𝓘(ℝ, E).prod IF) I φ (x₀, w₀)).toLinearMap
    (LinearMap.range (LinearMap.inr ℝ E EF))

/-- **The slice plane has the dimension of the fibre.** -/
theorem finrank_slicePlane_G6C {φ : E × F → M}
    (hφ : IsSmoothEmbedding (𝓘(ℝ, E).prod IF) I ∞ φ) (x₀ : E) (w₀ : F) :
    Module.finrank ℝ (slicePlane_G6C (IF := IF) (I := I) φ x₀ w₀) = Module.finrank ℝ EF := by
  have hinj := hφ.isImmersion.mfderiv_injective (by simp) (x₀, w₀)
  unfold slicePlane_G6C
  rw [← (Submodule.equivMapOfInjective _ hinj _).finrank_eq]
  exact LinearMap.finrank_range_of_inj LinearMap.inr_injective

/-- **The differential of a map constant on the slice vanishes on the slice plane.** -/
theorem mfderiv_eq_zero_of_mem_slicePlane_G6C {φ : E × F → M} {x₀ : E} {w₀ : F}
    (hφ : MDifferentiableAt (𝓘(ℝ, E).prod IF) I φ (x₀, w₀))
    {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] {G : M → EG}
    (hG : MDifferentiableAt I 𝓘(ℝ, EG) G (φ (x₀, w₀)))
    (hconst : ∀ w, G (φ (x₀, w)) = G (φ (x₀, w₀))) :
    ∀ v ∈ slicePlane_G6C (IF := IF) (I := I) φ x₀ w₀, mfderiv I 𝓘(ℝ, EG) G (φ (x₀, w₀)) v = 0 := by
  rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
  have hι : MDifferentiableAt IF (𝓘(ℝ, E).prod IF) (fun w : F => (x₀, w)) w₀ :=
    mdifferentiableAt_const.prodMk mdifferentiableAt_id
  have hφι : MDifferentiableAt IF I (φ ∘ fun w : F => (x₀, w)) w₀ := hφ.comp w₀ hι
  have h1 := mfderiv_comp w₀ (hG : MDifferentiableAt I 𝓘(ℝ, EG) G (φ ((fun w : F => (x₀, w)) w₀)))
    hφι
  have h2 := mfderiv_comp w₀ hφ hι
  have h3' : mfderiv IF (𝓘(ℝ, E).prod IF) (fun w : F => (x₀, w)) w₀ =
      (0 : TangentSpace IF w₀ →L[ℝ] E).prod (ContinuousLinearMap.id ℝ (TangentSpace IF w₀)) :=
    ((hasMFDerivAt_const (I := IF) (I' := 𝓘(ℝ, E)) x₀ w₀).prodMk (hasMFDerivAt_id w₀)).mfderiv
  have hc : G ∘ (φ ∘ fun w : F => (x₀, w)) = fun _ => G (φ (x₀, w₀)) := funext hconst
  have h4 : mfderiv IF 𝓘(ℝ, EG) (G ∘ (φ ∘ fun w : F => (x₀, w))) w₀ (u : TangentSpace IF w₀) =
      0 := by
    rw [hc, mfderiv_const]
    rfl
  rw [h1, h2, h3'] at h4
  exact h4

end DifferentialGeometry.Topology
