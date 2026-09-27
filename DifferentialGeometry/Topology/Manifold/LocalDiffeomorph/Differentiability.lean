import Mathlib.Geometry.Manifold.LocalDiffeomorph


noncomputable section

open scoped ContDiff Manifold Topology

namespace IsLocalDiffeomorphAt

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E₁ E₂ E₃ : Type*}
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃]
  {H₁ H₂ H₃ : Type*} [TopologicalSpace H₁] [TopologicalSpace H₂]
  [TopologicalSpace H₃]
  {I₁ : ModelWithCorners 𝕜 E₁ H₁} {I₂ : ModelWithCorners 𝕜 E₂ H₂}
  {I₃ : ModelWithCorners 𝕜 E₃ H₃}
  {M₁ M₂ M₃ : Type*}
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
  [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  [TopologicalSpace M₃] [ChartedSpace H₃ M₃]
  {n : ℕ∞ω}

theorem mdifferentiableAt_of_comp
    {q : M₁ → M₂} {x : M₁} (hq : IsLocalDiffeomorphAt I₁ I₂ n q x)
    (hn : n ≠ 0) {f : M₂ → M₃} (hf : MDifferentiableAt I₁ I₃ (f ∘ q) x) :
    MDifferentiableAt I₂ I₃ f (q x) := by
  have hinverse : hq.localInverse (q x) = x :=
    hq.localInverse_left_inv hq.localInverse_mem_target
  have hf' : MDifferentiableAt I₁ I₃ (f ∘ q) (hq.localInverse (q x)) := by
    rwa [hinverse]
  apply (hf'.comp (q x) (hq.localInverse_mdifferentiableAt hn)).congr_of_eventuallyEq
  filter_upwards [hq.localInverse_eventuallyEq_right] with y hy
  change f y = f (q (hq.localInverse y))
  change q (hq.localInverse y) = y at hy
  rw [hy]

theorem mdifferentiableAt_comp_iff
    {q : M₁ → M₂} {x : M₁} (hq : IsLocalDiffeomorphAt I₁ I₂ n q x)
    (hn : n ≠ 0) {f : M₂ → M₃} :
    MDifferentiableAt I₁ I₃ (f ∘ q) x ↔ MDifferentiableAt I₂ I₃ f (q x) := by
  constructor
  · exact hq.mdifferentiableAt_of_comp hn
  · intro hf
    exact hf.comp x (hq.mdifferentiableAt hn)

end IsLocalDiffeomorphAt
