import DifferentialGeometry.Topology.Morse.RegularZeroAtlas
import DifferentialGeometry.Topology.Manifold.RegularZero.Tangent

set_option autoImplicit false
noncomputable section
open Set Filter Function
open scoped Manifold ContDiff Topology
namespace Poincare.Morse
variable {A B C : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup C] [NormedSpace ℝ C]
  {S : Set A}


theorem injective_fderiv_zeroFiberChart_symm (g : A → B)
    (Φ : PartialDiffeomorph 𝓘(ℝ, A) 𝓘(ℝ, B × C) A (B × C) 1)
    (hΦ : ∀ y, (Φ y).1 = g y) (hΦS : Φ.source ⊆ S)
    (a : {y : A // y ∈ S ∧ g y = 0}) {z : C}
    (hz : z ∈ (zeroFiberChart g Φ hΦ hΦS a).target) :
    Injective (fderiv ℝ (fun u => ((zeroFiberChart g Φ hΦ hΦS a).symm u).val) z) :=
  Poincare.Manifold.RegularZero.injective_fderiv_fiberChart_symm one_ne_zero g Φ hΦ hΦS a hz

section FiniteDimension
variable [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] {g : A → B}


theorem mfderiv_regularZero_inclusion (hs : IsOpen S) (hg : ContDiffOn ℝ 1 g S)
    (hr : ∀ x ∈ S, g x = 0 → Surjective (fderiv ℝ g x)) (x : {y : A // y ∈ S ∧ g y = 0}) :
    let _ := regularZeroChartedSpace hs hg hr
    (show (Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ) →L[ℝ] A from
      mfderiv 𝓘(ℝ, Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ) 𝓘(ℝ, A)
        (Subtype.val : {y : A // y ∈ S ∧ g y = 0} → A) x) =
      fderiv ℝ (fun u => ((regularZeroChart hs hg hr x).symm u).val)
        (regularZeroChart hs hg hr x x) :=
  Poincare.Manifold.RegularZero.mfderiv_inclusion one_ne_zero hs hg hr x


theorem injective_mfderiv_regularZero_inclusion (hs : IsOpen S) (hg : ContDiffOn ℝ 1 g S)
    (hr : ∀ x ∈ S, g x = 0 → Surjective (fderiv ℝ g x)) (x : {y : A // y ∈ S ∧ g y = 0}) :
    let _ := regularZeroChartedSpace hs hg hr
    Injective (mfderiv 𝓘(ℝ, Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ) 𝓘(ℝ, A)
      (Subtype.val : {y : A // y ∈ S ∧ g y = 0} → A) x) :=
  Poincare.Manifold.RegularZero.injective_mfderiv_inclusion one_ne_zero hs hg hr x


theorem range_mfderiv_regularZero_inclusion (hs : IsOpen S) (hg : ContDiffOn ℝ 1 g S)
    (hr : ∀ x ∈ S, g x = 0 → Surjective (fderiv ℝ g x)) (x : {y : A // y ∈ S ∧ g y = 0}) :
    let _ := regularZeroChartedSpace hs hg hr
    LinearMap.range (show (Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ) →ₗ[ℝ] A from
      (mfderiv 𝓘(ℝ, Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ) 𝓘(ℝ, A)
        (Subtype.val : {y : A // y ∈ S ∧ g y = 0} → A) x).toLinearMap) =
      (fderiv ℝ g x.val).ker :=
  Poincare.Manifold.RegularZero.range_mfderiv_inclusion one_ne_zero hs hg hr x

end FiniteDimension
end Poincare.Morse
