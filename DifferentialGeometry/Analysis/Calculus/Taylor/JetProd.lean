import DifferentialGeometry.Analysis.Calculus.Taylor.CubicJet
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Second-order jets of pairs and of first-order prolongations

Equal second-order jets survive pairing, and a `C²` function of `(φ y, Dφ y, y)` has a
second-order jet at `y₀` determined by the third-order jet of `φ` at `y₀`. Used to compare the
chart representatives of pulled-back metrics under jet replacement.
-/

set_option autoImplicit false

noncomputable section

open Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

private theorem jetProd_key {A : E → F} {B : E → G} {x₀ : E} (hA : ContDiffAt ℝ 2 A x₀)
    (hB : ContDiffAt ℝ 2 B x₀) :
    fderiv ℝ (fun x => (A x, B x)) x₀ = (fderiv ℝ A x₀).prod (fderiv ℝ B x₀) ∧
      fderiv ℝ (fderiv ℝ (fun x => (A x, B x))) x₀ =
        ((ContinuousLinearMap.prodₗᵢ ℝ (𝕜 := ℝ) (E := E) (F := F) (G := G)).toLinearIsometry.toContinuousLinearMap).comp
          ((fderiv ℝ (fderiv ℝ A) x₀).prod (fderiv ℝ (fderiv ℝ B) x₀)) := by
  have hAd : DifferentiableAt ℝ A x₀ := hA.differentiableAt (by norm_num)
  have hBd : DifferentiableAt ℝ B x₀ := hB.differentiableAt (by norm_num)
  refine ⟨hAd.fderiv_prodMk hBd, ?_⟩
  have hAev : ∀ᶠ x in 𝓝 x₀, DifferentiableAt ℝ A x :=
    (hA.eventually (by simp)).mono fun z hz => hz.differentiableAt (by norm_num)
  have hBev : ∀ᶠ x in 𝓝 x₀, DifferentiableAt ℝ B x :=
    (hB.eventually (by simp)).mono fun z hz => hz.differentiableAt (by norm_num)
  let P := (ContinuousLinearMap.prodₗᵢ ℝ (𝕜 := ℝ) (E := E) (F := F) (G := G)).toLinearIsometry.toContinuousLinearMap
  have heq : fderiv ℝ (fun x => (A x, B x)) =ᶠ[𝓝 x₀] fun x => P (fderiv ℝ A x, fderiv ℝ B x) := by
    filter_upwards [hAev, hBev] with x hx hx'
    exact hx.fderiv_prodMk hx'
  have hA' : HasFDerivAt (fderiv ℝ A) (fderiv ℝ (fderiv ℝ A) x₀) x₀ :=
    ((hA.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hB' : HasFDerivAt (fderiv ℝ B) (fderiv ℝ (fderiv ℝ B) x₀) x₀ :=
    ((hB.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  rw [heq.fderiv_eq]
  exact (P.hasFDerivAt.comp x₀ (hA'.prodMk hB')).fderiv

/-- **Second-order jets of pairs.** Pairing two maps with equal second-order jets with two other
maps with equal second-order jets gives maps with equal second-order jets. -/
theorem jet2_prodMk_eq {A₁ A₂ : E → F} {B₁ B₂ : E → G} {x₀ : E} (hA₁ : ContDiffAt ℝ 2 A₁ x₀)
    (hA₂ : ContDiffAt ℝ 2 A₂ x₀) (hB₁ : ContDiffAt ℝ 2 B₁ x₀) (hB₂ : ContDiffAt ℝ 2 B₂ x₀)
    (hA1 : fderiv ℝ A₁ x₀ = fderiv ℝ A₂ x₀)
    (hA2 : fderiv ℝ (fderiv ℝ A₁) x₀ = fderiv ℝ (fderiv ℝ A₂) x₀)
    (hB1 : fderiv ℝ B₁ x₀ = fderiv ℝ B₂ x₀)
    (hB2 : fderiv ℝ (fderiv ℝ B₁) x₀ = fderiv ℝ (fderiv ℝ B₂) x₀) :
    fderiv ℝ (fun x => (A₁ x, B₁ x)) x₀ = fderiv ℝ (fun x => (A₂ x, B₂ x)) x₀ ∧
      fderiv ℝ (fderiv ℝ (fun x => (A₁ x, B₁ x))) x₀ =
        fderiv ℝ (fderiv ℝ (fun x => (A₂ x, B₂ x))) x₀ := by
  obtain ⟨a1, a2⟩ := jetProd_key hA₁ hB₁
  obtain ⟨b1, b2⟩ := jetProd_key hA₂ hB₂
  exact ⟨by rw [a1, b1, hA1, hB1], by rw [a2, b2, hA2, hB2]⟩

/-- **Second-order jets of first-order prolongations.** If `φ₁` and `φ₂` are `C³` at `y₀` with the
same third-order jet there, then for every `Θ` of class `C²` at `(φ₁ y₀, Dφ₁ y₀, y₀)` the maps
`y ↦ Θ (φᵢ y, Dφᵢ y, y)` are `C²` at `y₀` with the same second-order jet. -/
theorem jet2_comp_prolong_eq (Θ : F × (E →L[ℝ] F) × E → G) {φ₁ φ₂ : E → F} {y₀ : E}
    (hΘ : ContDiffAt ℝ 2 Θ (φ₁ y₀, fderiv ℝ φ₁ y₀, y₀))
    (hφ₁ : ContDiffAt ℝ 3 φ₁ y₀) (hφ₂ : ContDiffAt ℝ 3 φ₂ y₀) (h0 : φ₁ y₀ = φ₂ y₀)
    (h1 : fderiv ℝ φ₁ y₀ = fderiv ℝ φ₂ y₀)
    (h2 : fderiv ℝ (fderiv ℝ φ₁) y₀ = fderiv ℝ (fderiv ℝ φ₂) y₀)
    (h3 : fderiv ℝ (fderiv ℝ (fderiv ℝ φ₁)) y₀ = fderiv ℝ (fderiv ℝ (fderiv ℝ φ₂)) y₀) :
    ContDiffAt ℝ 2 (fun y => Θ (φ₁ y, fderiv ℝ φ₁ y, y)) y₀ ∧
      ContDiffAt ℝ 2 (fun y => Θ (φ₂ y, fderiv ℝ φ₂ y, y)) y₀ ∧
      Θ (φ₁ y₀, fderiv ℝ φ₁ y₀, y₀) = Θ (φ₂ y₀, fderiv ℝ φ₂ y₀, y₀) ∧
      fderiv ℝ (fun y => Θ (φ₁ y, fderiv ℝ φ₁ y, y)) y₀ =
        fderiv ℝ (fun y => Θ (φ₂ y, fderiv ℝ φ₂ y, y)) y₀ ∧
      fderiv ℝ (fderiv ℝ (fun y => Θ (φ₁ y, fderiv ℝ φ₁ y, y))) y₀ =
        fderiv ℝ (fderiv ℝ (fun y => Θ (φ₂ y, fderiv ℝ φ₂ y, y))) y₀ := by
  have hd₁ : ContDiffAt ℝ 2 (fderiv ℝ φ₁) y₀ := hφ₁.fderiv_right (by norm_num)
  have hd₂ : ContDiffAt ℝ 2 (fderiv ℝ φ₂) y₀ := hφ₂.fderiv_right (by norm_num)
  have hid : ContDiffAt ℝ 2 (fun y : E => y) y₀ := contDiffAt_id
  have hp₁ : ContDiffAt ℝ 2 (fun y => (fderiv ℝ φ₁ y, y)) y₀ := hd₁.prodMk hid
  have hp₂ : ContDiffAt ℝ 2 (fun y => (fderiv ℝ φ₂ y, y)) y₀ := hd₂.prodMk hid
  obtain ⟨q1, q2⟩ := jet2_prodMk_eq hd₁ hd₂ hid hid h2 h3 rfl rfl
  have hJ₁ : ContDiffAt ℝ 2 (fun y => (φ₁ y, fderiv ℝ φ₁ y, y)) y₀ :=
    (hφ₁.of_le (by norm_num)).prodMk hp₁
  have hJ₂ : ContDiffAt ℝ 2 (fun y => (φ₂ y, fderiv ℝ φ₂ y, y)) y₀ :=
    (hφ₂.of_le (by norm_num)).prodMk hp₂
  obtain ⟨j1, j2⟩ := jet2_prodMk_eq (hφ₁.of_le (by norm_num)) (hφ₂.of_le (by norm_num)) hp₁ hp₂
    h1 h2 q1 q2
  have hJ0 : (φ₁ y₀, fderiv ℝ φ₁ y₀, y₀) = (φ₂ y₀, fderiv ℝ φ₂ y₀, y₀) := by rw [h0, h1]
  obtain ⟨c1, c2⟩ := jet2_comp_eq Θ (J₁ := fun y => (φ₁ y, fderiv ℝ φ₁ y, y))
    (J₂ := fun y => (φ₂ y, fderiv ℝ φ₂ y, y)) (x₀ := y₀) hΘ hJ₁ hJ₂ hJ0 j1 j2
  refine ⟨hΘ.comp y₀ hJ₁, (hJ0 ▸ hΘ).comp y₀ hJ₂, by rw [hJ0], c1, c2⟩

end DifferentialGeometry.Analysis
