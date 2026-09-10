import DifferentialGeometry.Topology.Morse.RelativePerturbationDifferential
import DifferentialGeometry.Topology.Morse.RegularZeroAtlas
import DifferentialGeometry.Topology.Morse.CriticalImageNull

set_option autoImplicit false
noncomputable section
open Set Function Filter
open scoped Manifold ContDiff Topology BigOperators
namespace Poincare.Morse
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ}

omit [FiniteDimensional ℝ E] in
private theorem regularPerturbationDomain_regular {f : E → ℝ} {φ : Fin n → E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) :
    ∀ q ∈ regularPerturbationDomain φ, perturbationDifferential f φ q = 0 →
      Surjective (fderiv ℝ (perturbationDifferential f φ) q) :=
  fun q hq _ => surjective_fderiv_perturbationDifferential hf hφ q hq.2

@[reducible]
private def reindexZeroAtlas {Z : Type*} [TopologicalSpace Z] {k l : ℕ} (h : k = l)
    (C : ChartedSpace (Fin k → ℝ) Z) : ChartedSpace (Fin l → ℝ) Z := h ▸ C


@[reducible]
def perturbationZeroChartedSpace {f : E → ℝ} {φ : Fin n → E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) :
    ChartedSpace (Fin n → ℝ)
      {q : (Fin n → ℝ) × E // q ∈ regularPerturbationDomain φ ∧ perturbationDifferential f φ q = 0} :=
  reindexZeroAtlas (perturbationZero_finrank (E := E) (n := n)) (
    regularZeroChartedSpace (isOpen_regularPerturbationDomain hφ)
      ((contDiff_perturbationDifferential hf hφ).of_le (by simp)).contDiffOn
      (regularPerturbationDomain_regular hf hφ))


theorem perturbationZeroIsManifold {f : E → ℝ} {φ : Fin n → E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) :
    let _ := perturbationZeroChartedSpace hf hφ
    IsManifold 𝓘(ℝ, Fin n → ℝ) 1
      {q : (Fin n → ℝ) × E // q ∈ regularPerturbationDomain φ ∧ perturbationDifferential f φ q = 0} := by
  let C := regularZeroChartedSpace (isOpen_regularPerturbationDomain hφ)
    ((contDiff_perturbationDifferential hf hφ).of_le (by simp)).contDiffOn
    (regularPerturbationDomain_regular hf hφ)
  have hh : ∀ (d : ℕ) (hd : Module.finrank ℝ ((Fin n → ℝ) × E) -
      Module.finrank ℝ (E →L[ℝ] ℝ) = d),
      let _ : ChartedSpace (Fin d → ℝ)
        {q : (Fin n → ℝ) × E // q ∈ regularPerturbationDomain φ ∧ perturbationDifferential f φ q = 0} := reindexZeroAtlas hd C
      IsManifold 𝓘(ℝ, Fin d → ℝ) 1
        {q : (Fin n → ℝ) × E // q ∈ regularPerturbationDomain φ ∧ perturbationDifferential f φ q = 0} := by
    intro d hd
    cases hd
    exact regularZeroIsManifold _ _ _
  exact hh n (perturbationZero_finrank (E := E) (n := n))


theorem contMDiff_perturbationZero_inclusion {f : E → ℝ} {φ : Fin n → E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) :
    let _ := perturbationZeroChartedSpace hf hφ
    ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, (Fin n → ℝ) × E) 1
      (Subtype.val : {q : (Fin n → ℝ) × E // q ∈ regularPerturbationDomain φ ∧
        perturbationDifferential f φ q = 0} → (Fin n → ℝ) × E) := by
  let C := regularZeroChartedSpace (isOpen_regularPerturbationDomain hφ)
    ((contDiff_perturbationDifferential hf hφ).of_le (by simp)).contDiffOn
    (regularPerturbationDomain_regular hf hφ)
  have hh : ∀ (d : ℕ) (hd : Module.finrank ℝ ((Fin n → ℝ) × E) -
      Module.finrank ℝ (E →L[ℝ] ℝ) = d),
      let _ : ChartedSpace (Fin d → ℝ)
        {q : (Fin n → ℝ) × E // q ∈ regularPerturbationDomain φ ∧ perturbationDifferential f φ q = 0} := reindexZeroAtlas hd C
      ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, (Fin n → ℝ) × E) 1
        (Subtype.val : {q : (Fin n → ℝ) × E // q ∈ regularPerturbationDomain φ ∧
          perturbationDifferential f φ q = 0} → (Fin n → ℝ) × E) := by
    intro d hd
    cases hd
    exact contMDiff_regularZero_inclusion _ _ _
  exact hh n (perturbationZero_finrank (E := E) (n := n))


theorem contMDiff_perturbationZero_projection {f : E → ℝ} {φ : Fin n → E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) :
    let _ := perturbationZeroChartedSpace hf hφ
    ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) 1
      (fun q : {q : (Fin n → ℝ) × E // q ∈ regularPerturbationDomain φ ∧
        perturbationDifferential f φ q = 0} => q.val.1) := by
  let _ := perturbationZeroChartedSpace hf hφ
  exact (ContinuousLinearMap.fst ℝ (Fin n → ℝ) E).contDiff.contMDiff.comp
    (contMDiff_perturbationZero_inclusion hf hφ)


theorem ae_regular_perturbationZero_projection {f : E → ℝ} {φ : Fin n → E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hφ : ∀ i, ContDiff ℝ ∞ (φ i))
    [MeasurableSpace (Fin n → ℝ)] [BorelSpace (Fin n → ℝ)]
    (μ : MeasureTheory.Measure (Fin n → ℝ)) [MeasureTheory.Measure.IsAddHaarMeasure μ] :
    let _ := perturbationZeroChartedSpace hf hφ
    ∀ᵐ p ∂μ, ∀ q : {q : (Fin n → ℝ) × E // q ∈ regularPerturbationDomain φ ∧
        perturbationDifferential f φ q = 0}, q.val.1 = p →
      Surjective (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ)
        (fun y : {q : (Fin n → ℝ) × E // q ∈ regularPerturbationDomain φ ∧
          perturbationDifferential f φ q = 0} => y.val.1) q) := by
  let _ := perturbationZeroChartedSpace hf hφ
  let _ := perturbationZeroIsManifold hf hφ
  exact ae_regular_values μ ((contMDiff_perturbationZero_projection hf hφ).mdifferentiable one_ne_zero)

end Poincare.Morse
