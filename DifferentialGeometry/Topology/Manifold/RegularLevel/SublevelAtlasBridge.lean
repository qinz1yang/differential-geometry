import DifferentialGeometry.Topology.Manifold.RegularLevel.SublevelTransfer
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.RegularSublevelAtlas
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Maps

/-!
# The two regular-sublevel structures agree (model change `MorseHalfSpace m ↔ 𝓡∂ (m + 1)`)

Lane F7-LFR51, item P2 of the LFR54 → chapter-14 `ZeroModel` path. Chapter 13 gives the closed disc
cores their boundary charts through `RegularLevel.sublevelChartedSpace` (model
`morseModelWithCornersHalfSpace m`, e.g. LC45 / X84 and the closed disc bundles), while the chapter-14
pieces and the fixed models (`solidTorusCarrier`, `mobiusBundleCarrier`) use
`SmoothBoundaryAtlas.regularSublevel` (model `𝓡∂ (m + 1)`). For one regular sublevel `{f ≤ a}` of a
boundaryless manifold modelled on `MorseModel (m + 1)`, the identity is a diffeomorphism between the
two structures (`exists_sublevel_diffeomorph_regularSublevelAtlas`); hence so is any composite with
a sublevel diffeomorphism (`exists_regularSublevelAtlas_diffeomorph_of_contMDiffOn`).
-/

set_option autoImplicit false

noncomputable section

open Set DifferentialGeometry.Topology.Morse
open scoped Manifold ContDiff

namespace DifferentialGeometry.Manifold.RegularLevel

variable {m : ℕ} {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ (MorseModel (m + 1)) H) [IsManifold I ∞ M]

/-- `MorseModel (m + 1)` has dimension `m + 1`. -/
theorem finrank_morseModel : Module.finrank ℝ (MorseModel (m + 1)) = m + 1 :=
  Module.finrank_fin_fun ℝ

/-- **Model change on one regular sublevel.** The identity of `{f ≤ a}` is a diffeomorphism from
the regular-sublevel charts (`MorseHalfSpace m`) to the smooth boundary atlas charts
(`𝓡∂ (m + 1)`). -/
theorem exists_sublevel_diffeomorph_regularSublevelAtlas [I.Boundaryless] {f : M → ℝ} {a : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    letI := sublevelChartedSpace I hf hr
    letI := (DifferentialGeometry.Topology.SmoothBoundaryAtlas.regularSublevel I (n := m)
      finrank_morseModel hf a hr).toChartedSpace
    ∃ Φ : Diffeomorph (morseModelWithCornersHalfSpace m) (𝓡∂ (m + 1))
      {x : M // f x ≤ a} ({x | f x ≤ a} : Set M) ∞, ∀ x, (Φ x).val = x.val := by
  let _ := sublevelChartedSpace I hf hr
  let _ := sublevelIsManifold I hf hr
  let C := DifferentialGeometry.Topology.SmoothBoundaryAtlas.regularSublevel I (n := m)
    finrank_morseModel hf a hr
  let _ := C.toChartedSpace
  let _ := C.isManifold
  have hfwd : ContMDiff (morseModelWithCornersHalfSpace m) (𝓡∂ (m + 1)) ∞
      (fun x : {x : M // f x ≤ a} => (⟨x.val, x.2⟩ : ({x | f x ≤ a} : Set M))) :=
    (C.contMDiff_iff_subtype_val _).mpr (contMDiff_sublevel_inclusion I hf hr)
  have hbwd : ContMDiff (𝓡∂ (m + 1)) (morseModelWithCornersHalfSpace m) ∞
      (fun x : ({x | f x ≤ a} : Set M) => (⟨x.val, x.2⟩ : {x : M // f x ≤ a})) :=
    (contMDiff_sublevel_iff I (𝓡∂ (m + 1)) hf hr le_rfl).mpr C.contMDiff_subtype_val
  exact ⟨{ toFun := fun x => ⟨x.val, x.2⟩
           invFun := fun x => ⟨x.val, x.2⟩
           left_inv := fun _ => rfl
           right_inv := fun _ => rfl
           contMDiff_toFun := hfwd
           contMDiff_invFun := hbwd }, fun _ => rfl⟩

/-- **Ambient maps restrict to a diffeomorphism onto the boundary-atlas sublevel.** As
`exists_sublevel_diffeomorph_of_contMDiffOn`, with the target sublevel carrying the smooth boundary
atlas (`𝓡∂ (m + 1)`) used by the chapter-14 pieces and fixed models. -/
theorem exists_regularSublevelAtlas_diffeomorph_of_contMDiffOn
    {H₁ M₁ : Type*} [TopologicalSpace H₁] [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    (I₁ : ModelWithCorners ℝ (MorseModel (m + 1)) H₁) [I₁.Boundaryless] [IsManifold I₁ ∞ M₁]
    [I.Boundaryless]
    {f₁ : M₁ → ℝ} {a₁ : ℝ} (hf₁ : ContMDiff I₁ 𝓘(ℝ, ℝ) ∞ f₁)
    (hr₁ : ∀ x, f₁ x = a₁ → mfderiv I₁ 𝓘(ℝ, ℝ) f₁ x ≠ 0)
    {f : M → ℝ} {a : ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    {ψ : M₁ → M} {φ : M → M₁} {U₁ : Set M₁} {U : Set M} (hU₁ : IsOpen U₁)
    (hU : IsOpen U) (hS₁ : {x | f₁ x ≤ a₁} ⊆ U₁) (hS : {y | f y ≤ a} ⊆ U)
    (hψ : ContMDiffOn I₁ I ∞ ψ U₁) (hφ : ContMDiffOn I I₁ ∞ φ U)
    (hψS : ∀ x, f₁ x ≤ a₁ → f (ψ x) ≤ a) (hφS : ∀ y, f y ≤ a → f₁ (φ y) ≤ a₁)
    (hφψ : ∀ x, f₁ x ≤ a₁ → φ (ψ x) = x) (hψφ : ∀ y, f y ≤ a → ψ (φ y) = y) :
    letI := sublevelChartedSpace I₁ hf₁ hr₁
    letI := (DifferentialGeometry.Topology.SmoothBoundaryAtlas.regularSublevel I (n := m)
      finrank_morseModel hf a hr).toChartedSpace
    ∃ Φ : Diffeomorph (morseModelWithCornersHalfSpace m) (𝓡∂ (m + 1))
      {x : M₁ // f₁ x ≤ a₁} ({y | f y ≤ a} : Set M) ∞, ∀ x, (Φ x).val = ψ x.val := by
  let _ := sublevelChartedSpace I₁ hf₁ hr₁
  let _ := sublevelChartedSpace I hf hr
  let C := DifferentialGeometry.Topology.SmoothBoundaryAtlas.regularSublevel I (n := m)
    finrank_morseModel hf a hr
  let _ := C.toChartedSpace
  obtain ⟨Φ₁, hΦ₁⟩ := exists_sublevel_diffeomorph_of_contMDiffOn I₁ I hf₁ hr₁ hf hr hU₁ hU
    hS₁ hS hψ hφ hψS hφS hφψ hψφ
  obtain ⟨Φ₂, hΦ₂⟩ := exists_sublevel_diffeomorph_regularSublevelAtlas I hf hr
  exact ⟨Φ₁.trans Φ₂, fun x => (hΦ₂ (Φ₁ x)).trans (hΦ₁ x)⟩

end DifferentialGeometry.Manifold.RegularLevel
