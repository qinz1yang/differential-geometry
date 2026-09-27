import DifferentialGeometry.Analysis.Spectral.FiniteDimensional.SmoothBilinearEigenpair
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

noncomputable section
open Set
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Manifold

theorem exists_contMDiff_bilinear_normalized_eigenpair
    {P H M E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    [TopologicalSpace H] {I : ModelWithCorners ℝ P H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (A : M → E →L[ℝ] E) (B : M → E →L[ℝ] E →L[ℝ] ℝ)
    {U : Set M} (hU : IsOpen U)
    (hA : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞ A U)
    (hB : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ B U)
    {p₀ : M} (hp₀ : p₀ ∈ U) (hsym : ∀ u v : E, B p₀ u v = B p₀ v u)
    (hself : ∀ u v : E, B p₀ (A p₀ u) v = B p₀ u (A p₀ v))
    (μ₀ : ℝ) (w₀ : E) (hw₀ : B p₀ w₀ w₀ = 1) (heigen : A p₀ w₀ = μ₀ • w₀)
    (hsimple : Module.End.eigenspace (A p₀).toLinearMap μ₀ = Submodule.span ℝ {w₀}) :
    ∃ V : Set M, IsOpen V ∧ p₀ ∈ V ∧ V ⊆ U ∧
      ∃ (μ : M → ℝ) (w : M → E), ContMDiffOn I 𝓘(ℝ) ∞ μ V ∧
        ContMDiffOn I 𝓘(ℝ, E) ∞ w V ∧ μ p₀ = μ₀ ∧ w p₀ = w₀ ∧
        ∀ p ∈ V, B p (w p) (w p) = 1 ∧ A p (w p) = μ p • w p := by
  let c : OpenPartialHomeomorph M P :=
    { toPartialEquiv := extChartAt I p₀
      open_source := isOpen_extChartAt_source p₀
      open_target := isOpen_extChartAt_target p₀
      continuousOn_toFun := continuousOn_extChartAt p₀
      continuousOn_invFun := continuousOn_extChartAt_symm p₀ }
  have hp : p₀ ∈ c.source := mem_extChartAt_source p₀
  let D := c.target ∩ c.symm ⁻¹' U
  have hD : IsOpen D := c.isOpen_inter_preimage_symm hU
  have hpD : c p₀ ∈ D := ⟨c.map_source hp, by
    change c.symm (c p₀) ∈ U
    rwa [c.left_inv hp]⟩
  have hc : ContMDiffOn I 𝓘(ℝ, P) ∞ c c.source :=
    (contMDiffOn_extChartAt (I := I) (x := p₀)).mono (fun z hz ↦ by
      have hz' : z ∈ (extChartAt I p₀).source := hz
      simpa only [extChartAt_source] using hz')
  have hci : ContMDiffOn 𝓘(ℝ, P) I ∞ c.symm D :=
    (contMDiffOn_extChartAt_symm (I := I) p₀).mono inter_subset_left
  obtain ⟨W, hWo, hpW, hWD, μ, w, hμ, hw, hμ₀, hw₀', heq⟩ :=
    DifferentialGeometry.Analysis.exists_smooth_bilinear_normalized_eigenpair
      (A ∘ c.symm) (B ∘ c.symm) hD
      (hA.comp hci (fun _ hz ↦ hz.2)).contDiffOn
      (hB.comp hci (fun _ hz ↦ hz.2)).contDiffOn hpD
      (by simpa only [Function.comp_apply, c.left_inv hp] using hsym)
      (by simpa only [Function.comp_apply, c.left_inv hp] using hself)
      μ₀ w₀ (by simpa only [Function.comp_apply, c.left_inv hp] using hw₀)
      (by simpa only [Function.comp_apply, c.left_inv hp] using heigen)
      (by simpa only [Function.comp_apply, c.left_inv hp] using hsimple)
  let V := c.source ∩ c ⁻¹' W
  refine ⟨V, c.isOpen_inter_preimage hWo, ⟨hp, hpW⟩, ?_, μ ∘ c, w ∘ c,
    hμ.contMDiffOn.comp (hc.mono inter_subset_left) (fun _ hz ↦ hz.2),
    hw.contMDiffOn.comp (hc.mono inter_subset_left) (fun _ hz ↦ hz.2), hμ₀, hw₀', ?_⟩
  · intro z hz
    have hu := (hWD hz.2).2
    change c.symm (c z) ∈ U at hu
    rwa [c.left_inv hz.1] at hu
  · intro z hz
    simpa only [Function.comp_apply, c.left_inv hz.1] using heq (c z) hz.2

end DifferentialGeometry.Topology.Manifold
