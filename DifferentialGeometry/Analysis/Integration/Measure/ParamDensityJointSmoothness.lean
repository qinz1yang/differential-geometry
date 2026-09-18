import DifferentialGeometry.Analysis.Integration.Measure.Parametric.Evaluation
import DifferentialGeometry.Analysis.Calculus.Matrix.Determinant
import DifferentialGeometry.Bundle.PartialMfderiv.Parameter
import Mathlib.Geometry.Manifold.VectorBundle.Hom

noncomputable section

open Bundle DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff Topology Matrix.Norms.Elementwise

namespace DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P] [IsManifold IP 1 P]

theorem contMDiffAt_paramGramMatrix_joint
    (g : SmoothRiemannianMetric I M) {Φ : P → E → M} {p₀ : P × E} {n : ℕ∞}
    (hΦ : ContMDiffAt (IP.prod 𝓘(ℝ, E)) I ((n : ℕ∞ω) + 1) (Function.uncurry Φ) p₀) :
    ContMDiffAt (IP.prod 𝓘(ℝ, E))
      𝓘(ℝ, Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) n
      (fun p : P × E => fun i j => paramGramMatrix g (Φ p.1) p.2 i j) p₀ := by
  have hn : (n : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hΦn := hΦ.of_le (le_add_of_nonneg_right zero_le_one)
  have hg := (g.contMDiff.contMDiffAt.of_le hn).comp p₀ hΦn
  have hv (i : Fin (Module.finrank ℝ E)) :
      ContMDiffAt (IP.prod 𝓘(ℝ, E)) I.tangent n
        (fun p : P × E => (⟨Φ p.1 p.2,
          mfderiv 𝓘(ℝ, E) I (Φ p.1) p.2 (chartModelBasis E i)⟩ : TangentBundle I M)) p₀ :=
    hΦ.partial_mfderiv_apply (by
      rw [contMDiffAt_totalSpace]
      exact ⟨contMDiffAt_snd, by simpa using contMDiffAt_const⟩) le_rfl
  refine contMDiffAt_pi_space.mpr fun i => contMDiffAt_pi_space.mpr fun j => ?_
  have hinner : ContMDiffAt (IP.prod 𝓘(ℝ, E)) (I.prod 𝓘(ℝ, ℝ)) n
      (fun p : P × E => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) (Φ p.1 p.2)
        (g.inner (Φ p.1 p.2)
          (mfderiv 𝓘(ℝ, E) I (Φ p.1) p.2 (chartModelBasis E i))
          (mfderiv 𝓘(ℝ, E) I (Φ p.1) p.2 (chartModelBasis E j)))) p₀ :=
    hg.clm_bundle_apply₂ (hv i) (hv j)
  have hvalue := (contMDiffAt_totalSpace.mp hinner).2
  simpa only [paramGramMatrix_apply, Bundle.Trivial.fiberBundle_trivializationAt',
    Bundle.Trivial.trivialization_apply] using hvalue

theorem contMDiffAt_paramDensity_joint
    (g : SmoothRiemannianMetric I M) {Φ : P → E → M} {p₀ : P × E} {n : ℕ∞}
    (hΦ : ContMDiffAt (IP.prod 𝓘(ℝ, E)) I ((n : ℕ∞ω) + 1) (Function.uncurry Φ) p₀)
    (hdet : (paramGramMatrix g (Φ p₀.1) p₀.2).det ≠ 0) :
    ContMDiffAt (IP.prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) n
      (fun p : P × E => paramDensity g (Φ p.1) p.2) p₀ := by
  have hGram := contMDiffAt_paramGramMatrix_joint g hΦ
  have hdet' := (Matrix.contDiff_det (𝕜 := ℝ) (R := ℝ) (ι := Fin (Module.finrank ℝ E)) (n := (n : ℕ∞ω))).contMDiff.contMDiffAt.comp p₀ hGram
  exact (Real.contDiffAt_sqrt hdet).contMDiffAt.comp p₀ hdet'

theorem continuousAt_paramDensity_joint
    (g : SmoothRiemannianMetric I M) {Φ : P → E → M} {p₀ : P × E}
    (hΦ : ContMDiffAt (IP.prod 𝓘(ℝ, E)) I 1 (Function.uncurry Φ) p₀) :
    ContinuousAt (fun p : P × E => paramDensity g (Φ p.1) p.2) p₀ := by
  have hGram := (contMDiffAt_paramGramMatrix_joint g (n := 0) hΦ).continuousAt
  exact Real.continuous_sqrt.continuousAt.comp
    ((Matrix.contDiff_det (𝕜 := ℝ) (R := ℝ) (ι := Fin (Module.finrank ℝ E))
      (n := 0)).continuous.continuousAt.comp hGram)

end DifferentialGeometry.Integral.Measure
