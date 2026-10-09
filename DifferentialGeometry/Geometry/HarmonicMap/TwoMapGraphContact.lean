import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

set_option autoImplicit false

noncomputable section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

private theorem graph_tangent_eq_of_range_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : E →L[ℝ] ℂ) (L₁ L₂ : ℂ →L[ℝ] E) (R₁ R₂ : ℂ →L[ℝ] ℂ)
    (h₁ : P.comp (L₁.comp R₁) = ContinuousLinearMap.id ℝ ℂ)
    (h₂ : P.comp (L₂.comp R₂) = ContinuousLinearMap.id ℝ ℂ)
    (hrange : LinearMap.range L₂.toLinearMap ≤ LinearMap.range L₁.toLinearMap) :
    L₁.comp R₁ = L₂.comp R₂ := by
  have hsurj : Function.Surjective (P.comp L₁) := by
    intro v
    exact ⟨R₁ v, congrArg (fun A : ℂ →L[ℝ] ℂ => A v) h₁⟩
  have hinj : Function.Injective (P.comp L₁) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mpr hsurj
  ext v
  obtain ⟨w, hw⟩ := hrange (LinearMap.mem_range_self L₂.toLinearMap (R₂ v))
  change L₁ w = L₂ (R₂ v) at hw
  have heq : R₁ v = w := by
    apply hinj
    change P (L₁ (R₁ v)) = P (L₁ w)
    rw [hw]
    exact (congrArg (fun A : ℂ →L[ℝ] ℂ => A v) h₁).trans
      (congrArg (fun A : ℂ →L[ℝ] ℂ => A v) h₂).symm
  change L₁ (R₁ v) = L₂ (R₂ v)
  rw [heq, hw]

private theorem graph_coordinate_derivatives
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : ℂ → E} {a : ℂ} (hX : DifferentiableAt ℝ X a)
    (P : E →L[ℝ] ℂ) (height : E →L[ℝ] ℝ)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = P ∘ X)
    (ha : a ∈ e.source) (hei : DifferentiableAt ℝ e.symm (P (X a))) (x₀ : E) :
    P.comp ((fderiv ℝ X a).comp (fderiv ℝ e.symm (P (X a)))) =
        ContinuousLinearMap.id ℝ ℂ ∧
      fderiv ℝ (fun y => height (X (e.symm y) - x₀)) (P (X a)) =
        height.comp ((fderiv ℝ X a).comp (fderiv ℝ e.symm (P (X a)))) := by
  let y := P (X a)
  have hy : y ∈ e.target := by
    change (P ∘ X) a ∈ e.target
    rw [← he]
    exact e.map_source ha
  have hleft : e.symm y = a := by
    change e.symm ((P ∘ X) a) = a
    rw [← he]
    exact e.left_inv ha
  have hX' : DifferentiableAt ℝ X (e.symm y) := by rwa [hleft]
  have hprojection : HasFDerivAt (P ∘ X) (P.comp (fderiv ℝ X a)) (e.symm y) := by
    rw [hleft]
    exact P.hasFDerivAt.comp a hX.hasFDerivAt
  have heq : (fun w => (P ∘ X) (e.symm w)) =ᶠ[𝓝 y] id := by
    filter_upwards [e.open_target.mem_nhds hy] with w hw
    rw [← he]
    exact e.right_inv hw
  have hFR : (P.comp (fderiv ℝ X a)).comp (fderiv ℝ e.symm y) =
      ContinuousLinearMap.id ℝ ℂ :=
    ((hprojection.comp y hei.hasFDerivAt).congr_of_eventuallyEq heq.symm).unique
      (hasFDerivAt_id y)
  have hheight := height.hasFDerivAt.comp y
    ((hX'.hasFDerivAt.comp y hei.hasFDerivAt).sub_const x₀)
  rw [hleft] at hheight
  refine ⟨?_, hheight.fderiv⟩
  rw [← ContinuousLinearMap.comp_assoc]
  exact hFR

/-- Distinct immersed maps with a common tangent plane have equal chart-height
values and full derivatives in the same projection coordinates. Only a tangent
range inclusion is needed once both actual projection inverse germs exist.
The source points may coincide, and no source disjointness or common-map
assumption is imposed. -/
theorem chart_height_value_fderiv_eq_of_tangent_range_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    {F₁ F₂ : ℂ → M} (p : M)
    (proj : E →L[ℝ] ℂ) (height : E →L[ℝ] ℝ)
    (e₁ e₂ : OpenPartialHomeomorph ℂ ℂ)
    (he₁ : (e₁ : ℂ → ℂ) = fun z => proj (extChartAt 𝓘(ℝ, E) p (F₁ z)))
    (he₂ : (e₂ : ℂ → ℂ) = fun z => proj (extChartAt 𝓘(ℝ, E) p (F₂ z)))
    {a b : ℂ} (ha : a ∈ e₁.source) (hb : b ∈ e₂.source)
    (hF₁ : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₁ a)
    (hF₂ : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₂ b)
    (hc₁ : F₁ a ∈ (chartAt E p).source)
    (hei₁ : DifferentiableAt ℝ e₁.symm (proj (extChartAt 𝓘(ℝ, E) p (F₁ a))))
    (hei₂ : DifferentiableAt ℝ e₂.symm (proj (extChartAt 𝓘(ℝ, E) p (F₂ b))))
    (hvalue : F₁ a = F₂ b)
    (hrange : LinearMap.range
        (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₂ b).toLinearMap ≤
      LinearMap.range
        (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₁ a).toLinearMap)
    (x₀ : E) :
    let X₁ : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (F₁ z)
    let X₂ : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (F₂ z)
    let y := proj (X₁ a)
    let h₁ : ℂ → ℝ := fun w => height (X₁ (e₁.symm w) - x₀)
    let h₂ : ℂ → ℝ := fun w => height (X₂ (e₂.symm w) - x₀)
    h₁ y = h₂ y ∧ fderiv ℝ h₁ y = fderiv ℝ h₂ y := by
  intro X₁ X₂ y h₁ h₂
  have hXvalue : X₁ a = X₂ b := congrArg (extChartAt 𝓘(ℝ, E) p) hvalue
  have hy : proj (X₁ a) = proj (X₂ b) := congrArg proj hXvalue
  have he₁a : e₁.symm y = a := by
    change e₁.symm ((fun z => proj (X₁ z)) a) = a
    rw [← he₁]
    exact e₁.left_inv ha
  have he₂b : e₂.symm y = b := by
    change e₂.symm (proj (X₁ a)) = b
    rw [hy]
    change e₂.symm ((fun z => proj (X₂ z)) b) = b
    rw [← he₂]
    exact e₂.left_inv hb
  have hc₁' := (contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞) hc₁).mdifferentiableAt
    (by simp)
  have hc₂ : F₂ b ∈ (chartAt E p).source := hvalue ▸ hc₁
  have hc₂' := (contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞) hc₂).mdifferentiableAt
    (by simp)
  have hX₁ : DifferentiableAt ℝ X₁ a := (hc₁'.comp a hF₁).differentiableAt
  have hX₂ : DifferentiableAt ℝ X₂ b := (hc₂'.comp b hF₂).differentiableAt
  let C (q : M) : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) p) q
  let D₁ : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₁ a
  let D₂ : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₂ b
  have hDX₁ : fderiv ℝ X₁ a = (C (F₁ a)).comp D₁ := by
    have h := mfderiv_comp a hc₁' hF₁
    rw [mfderiv_eq_fderiv] at h
    exact h
  have hDX₂ : fderiv ℝ X₂ b = (C (F₂ b)).comp D₂ := by
    have h := mfderiv_comp b hc₂' hF₂
    rw [mfderiv_eq_fderiv] at h
    exact h
  have hrangeX : LinearMap.range (fderiv ℝ X₂ b).toLinearMap ≤
      LinearMap.range (fderiv ℝ X₁ a).toLinearMap := by
    rintro v ⟨w, rfl⟩
    obtain ⟨t, ht⟩ := hrange (LinearMap.mem_range_self D₂.toLinearMap w)
    change D₁ t = D₂ w at ht
    refine ⟨t, ?_⟩
    rw [hDX₁, hDX₂]
    change C (F₁ a) (D₁ t) = C (F₂ b) (D₂ w)
    rw [ht, hvalue]
  obtain ⟨hP₁, hh₁⟩ := graph_coordinate_derivatives hX₁ proj height e₁ he₁ ha hei₁ x₀
  obtain ⟨hP₂, hh₂⟩ := graph_coordinate_derivatives hX₂ proj height e₂ he₂ hb hei₂ x₀
  rw [← hy] at hP₂ hh₂
  have hT := graph_tangent_eq_of_range_le proj (fderiv ℝ X₁ a) (fderiv ℝ X₂ b)
    (fderiv ℝ e₁.symm y) (fderiv ℝ e₂.symm y) hP₁ hP₂ hrangeX
  refine ⟨?_, ?_⟩
  · change height (X₁ (e₁.symm y) - x₀) = height (X₂ (e₂.symm y) - x₀)
    rw [he₁a, he₂b, hXvalue]
  · change fderiv ℝ (fun w => height (X₁ (e₁.symm w) - x₀)) y =
      fderiv ℝ (fun w => height (X₂ (e₂.symm w) - x₀)) y
    rw [hh₁, hh₂, hT]

end DifferentialGeometry.Geometry
