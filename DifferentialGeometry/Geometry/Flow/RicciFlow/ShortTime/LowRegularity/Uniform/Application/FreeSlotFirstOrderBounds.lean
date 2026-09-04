import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Curvature.SlotFreeOperatorBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.CurvatureJetOne

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private noncomputable def sfOneGridC (C₀ C₁ : ℝ) (i : ℕ) : ℝ :=
  if i = 0 then (3 : ℝ) ^ 4 * C₀ ^ 2
  else (3 : ℝ) ^ 5 * C₁ ^ 2

theorem sfOne_grid_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ C : ℕ → ℝ, (∀ i : ℕ, 0 ≤ C i) ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (i : ℕ), i < 2 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 1 (3 + i) x
              ((iteratedCovGrad (I := I) g 1 3 i
                (slotFreeOpCc (I := I) (M := M) g 1)).toSection x) ≤
            C i := by
  classical
  obtain ⟨Kb₀, hKb₀_nonneg, hKb₀⟩ :=
    exists_uniform_riemannOp_LeviCivita_gNorm_bound
      (I := I) (M := M) gBase
  obtain ⟨Kb₁, hKb₁_nonneg, hKb₁⟩ :=
    exists_curvJet_sup (I := I) (M := M) gBase 1
  have hKb₁' : ∀ x : M,
      Real.sqrt (normSq0S (I := I) gBase x 5
        (iterCov (I := I) gBase 4
          (metricRm04 (I := I) (M := M) gBase) 1 x)) ≤ Kb₁ := by
    intro x
    simpa using hKb₁ x
  let C₀ : ℝ :=
    Λ ^ 2 * (riemannDiffC Λ Λ Λ + Real.sqrt Kb₀)
  let C₁ : ℝ := rmOneOpC Λ Kb₀ Kb₁
  let C : ℕ → ℝ := sfOneGridC C₀ C₁
  have hC₀ : 0 ≤ C₀ := by
    dsimp only [C₀, riemannDiffC]
    positivity
  have hC₁ : 0 ≤ C₁ := by
    dsimp only [C₁]
    exact rmOneOpC_nonneg (le_trans zero_le_one hΛ) hKb₁_nonneg
  refine ⟨C, ?_, ?_⟩
  · intro i
    dsimp only [C, sfOneGridC]
    split <;> positivity
  · intro g hEq hjet i hi x
    have hcomp : ∀ (y : M) (v : TangentSpace I y),
        Λ⁻¹ * gBase.inner y v v ≤ g.inner y v v ∧
          g.inner y v v ≤ Λ * gBase.inner y v v :=
      fun y v ↦ hEq.2 y (Set.mem_univ y) v
    have hjet₁ := hjet 1 (by norm_num)
    have hjet₂ := hjet 2 (by norm_num)
    have hjet₃ := hjet 3 (by norm_num)
    interval_cases i
    · have hR₀ := uniformCurvSup_of (I := I) (M := M)
        gBase g hΛ hKb₀_nonneg hKb₀ hcomp hjet₁ hjet₂
      have hz := sfOne_riemannianFiberNormSq_zero (I := I) (M := M) g hC₀ hR₀ x
      rw [hDim] at hz
      with_unfolding_all
        exact hz
    · have hR₁ := uniformRmOpOne_of (I := I) (M := M)
        gBase g hΛ hKb₀_nonneg hKb₀ hKb₁_nonneg hKb₁'
          hcomp hjet₁ hjet₂ hjet₃
      have ho := sfOne_riemannianFiberNormSq_one (I := I) (M := M) g hC₁ hR₁ x
      rw [hDim] at ho
      with_unfolding_all
        exact ho

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
