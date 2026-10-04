import DifferentialGeometry.Topology.Manifold.RegularLevel.Sublevel

/-!
# Diffeomorphisms of regular sublevels induced by ambient maps

Two regular sublevels `{f₁ ≤ a₁} ⊆ M₁` and `{f₂ ≤ a₂} ⊆ M₂` carry the manifold-with-boundary
structure `sublevelChartedSpace` (models over `MorseModel (m + 1)`). A map into such a sublevel
is smooth exactly when its composite with the inclusion is smooth (`contMDiff_sublevel_iff`).
Hence ambient maps `ψ`, `φ`, smooth on open neighbourhoods of the two sublevels and mutually
inverse between them, restrict to a diffeomorphism of the sublevels
(`exists_sublevel_diffeomorph_of_contMDiffOn`). No smoothness up to the boundary has to be checked
by hand, and the structure does not depend on anything but the ambient smooth maps.
-/

set_option autoImplicit false

noncomputable section

open Set DifferentialGeometry.Topology.Morse
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Manifold.RegularLevel

/-- **Ambient maps restrict to a diffeomorphism of regular sublevels.** If `ψ : M₁ → M₂` and
`φ : M₂ → M₁` are smooth on open sets containing `{f₁ ≤ a₁}` and `{f₂ ≤ a₂}`, map these sublevels
into each other and are mutually inverse on them, then `x ↦ ψ x` is a diffeomorphism of the two
sublevels with their regular-sublevel structures. -/
theorem exists_sublevel_diffeomorph_of_contMDiffOn {m : ℕ}
    {H₁ H₂ M₁ M₂ : Type*} [TopologicalSpace H₁] [TopologicalSpace H₂]
    [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
    (I₁ : ModelWithCorners ℝ (MorseModel (m + 1)) H₁)
    (I₂ : ModelWithCorners ℝ (MorseModel (m + 1)) H₂)
    [I₁.Boundaryless] [I₂.Boundaryless] [IsManifold I₁ ∞ M₁] [IsManifold I₂ ∞ M₂]
    {f₁ : M₁ → ℝ} {a₁ : ℝ} (hf₁ : ContMDiff I₁ 𝓘(ℝ, ℝ) ∞ f₁)
    (hr₁ : ∀ x, f₁ x = a₁ → mfderiv I₁ 𝓘(ℝ, ℝ) f₁ x ≠ 0)
    {f₂ : M₂ → ℝ} {a₂ : ℝ} (hf₂ : ContMDiff I₂ 𝓘(ℝ, ℝ) ∞ f₂)
    (hr₂ : ∀ x, f₂ x = a₂ → mfderiv I₂ 𝓘(ℝ, ℝ) f₂ x ≠ 0)
    {ψ : M₁ → M₂} {φ : M₂ → M₁} {U₁ : Set M₁} {U₂ : Set M₂} (hU₁ : IsOpen U₁)
    (hU₂ : IsOpen U₂) (hS₁ : {x | f₁ x ≤ a₁} ⊆ U₁) (hS₂ : {y | f₂ y ≤ a₂} ⊆ U₂)
    (hψ : ContMDiffOn I₁ I₂ ∞ ψ U₁) (hφ : ContMDiffOn I₂ I₁ ∞ φ U₂)
    (hψS : ∀ x, f₁ x ≤ a₁ → f₂ (ψ x) ≤ a₂) (hφS : ∀ y, f₂ y ≤ a₂ → f₁ (φ y) ≤ a₁)
    (hφψ : ∀ x, f₁ x ≤ a₁ → φ (ψ x) = x) (hψφ : ∀ y, f₂ y ≤ a₂ → ψ (φ y) = y) :
    let _ := sublevelChartedSpace I₁ hf₁ hr₁
    let _ := sublevelChartedSpace I₂ hf₂ hr₂
    ∃ Φ : Diffeomorph (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m)
      {x : M₁ // f₁ x ≤ a₁} {y : M₂ // f₂ y ≤ a₂} ∞, ∀ x, (Φ x : M₂) = ψ x := by
  let _ := sublevelChartedSpace I₁ hf₁ hr₁
  let _ := sublevelChartedSpace I₂ hf₂ hr₂
  have hfwd : ContMDiff (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m) ∞
      (fun x : {x : M₁ // f₁ x ≤ a₁} => (⟨ψ x, hψS x x.2⟩ : {y : M₂ // f₂ y ≤ a₂})) := by
    apply (contMDiff_sublevel_iff I₂ (morseModelWithCornersHalfSpace m) hf₂ hr₂ le_rfl).mpr
    intro x
    exact (hψ.contMDiffAt (hU₁.mem_nhds (hS₁ x.2))).comp x
      (contMDiff_sublevel_inclusion I₁ hf₁ hr₁ x)
  have hbwd : ContMDiff (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m) ∞
      (fun y : {y : M₂ // f₂ y ≤ a₂} => (⟨φ y, hφS y y.2⟩ : {x : M₁ // f₁ x ≤ a₁})) := by
    apply (contMDiff_sublevel_iff I₁ (morseModelWithCornersHalfSpace m) hf₁ hr₁ le_rfl).mpr
    intro y
    exact (hφ.contMDiffAt (hU₂.mem_nhds (hS₂ y.2))).comp y
      (contMDiff_sublevel_inclusion I₂ hf₂ hr₂ y)
  exact ⟨{ toFun := fun x => ⟨ψ x, hψS x x.2⟩
           invFun := fun y => ⟨φ y, hφS y y.2⟩
           left_inv := fun x => Subtype.ext (hφψ x x.2)
           right_inv := fun y => Subtype.ext (hψφ y y.2)
           contMDiff_toFun := hfwd
           contMDiff_invFun := hbwd }, fun _ => rfl⟩

end DifferentialGeometry.Manifold.RegularLevel
