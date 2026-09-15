import Mathlib.Geometry.Manifold.ContMDiff.Basic

section

open scoped Manifold ContDiff

namespace Function.LeftInverse

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀]
  {H₀ : Type*} [TopologicalSpace H₀] {I₀ : ModelWithCorners 𝕜 E₀ H₀}
  {M₀ : Type*} [TopologicalSpace M₀] [ChartedSpace H₀ M₀]
variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  {H₁ : Type*} [TopologicalSpace H₁] {I₁ : ModelWithCorners 𝕜 E₁ H₁}
  {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
variable {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  {H₂ : Type*} [TopologicalSpace H₂] {I₂ : ModelWithCorners 𝕜 E₂ H₂}
  {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]

theorem contMDiffOn_of_comp {f : M₁ → M₂} {r : M₂ → M₁}
    (hleft : LeftInverse r f) {g : M₀ → M₁} {s : Set M₀} {u : Set M₂} {n : ℕ∞ω}
    (hr : ContMDiffOn I₂ I₁ n r u) (hg : ContMDiffOn I₀ I₂ n (f ∘ g) s)
    (hmem : Set.MapsTo (f ∘ g) s u) : ContMDiffOn I₀ I₁ n g s := by
  exact (hr.comp hg hmem).congr (fun x _ => (hleft (g x)).symm)

theorem contMDiff_of_comp {f : M₁ → M₂} {r : M₂ → M₁}
    (hleft : LeftInverse r f) {g : M₀ → M₁} {u : Set M₂} {n : ℕ∞ω}
    (hr : ContMDiffOn I₂ I₁ n r u) (hg : ContMDiff I₀ I₂ n (f ∘ g))
    (hmem : ∀ x, f (g x) ∈ u) : ContMDiff I₀ I₁ n g := by
  exact contMDiffOn_univ.mp
    (hleft.contMDiffOn_of_comp hr hg.contMDiffOn (fun x _ => hmem x))

end Function.LeftInverse

end
