import DifferentialGeometry.Analysis.Elliptic.WeakLaplacian
import DifferentialGeometry.Analysis.Sobolev.Intrinsic.Lipschitz.Basic

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Operator.IsLaplacianLEDistributionalOn

open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.IntrinsicLp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (∞ : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem neg_integral_bound_mul_le_integral_gradient_pairing
    (g : SmoothRiemannianMetric I M)
    {u b : M → Real} {U : Set M} {L : NNReal}
    (h : IsLaplacianLEDistributionalOn (I := I) g u b U)
    (hu : ∀ x y, edist (u x) (u y) ≤ (L : ENNReal) *
      riemannianEDistOf (I := I) g x y)
    (φ : C^∞⟮I, M; Real⟯)
    (hφ : φ ∈ compactlySupportedSmoothFunctions I M)
    (hφU : tsupport (φ : M → Real) ⊆ U)
    (hφ0 : ∀ x : M, 0 ≤ φ x) :
    -(∫ x, b x * φ x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
      ∫ x, tangentSectionAction (I := I) (gradG (I := I) g φ) u x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  have hgrad_cs : HasCompactSupport
      (gradG (I := I) g φ :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :=
    hasCompactSupport_grad_g (I := I) g φ hφ
  have hgreen :=
    (integrable_tangentSectionAction_and_integral_eq_neg_integral_smul_divergence_of_lipschitz
      (I := I) g (gradG (I := I) g φ) hgrad_cs hu).2
  calc
    -(∫ x, b x * φ x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
        -(∫ x, u x * ΔG (I := I) g φ x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) :=
      neg_le_neg (h.test_le φ hφ hφU hφ0)
    _ = ∫ x, tangentSectionAction (I := I) (gradG (I := I) g φ) u x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
      simpa only [Δ_g_def] using hgreen.symm

theorem integral_gradient_pairing_nonneg
    (g : SmoothRiemannianMetric I M)
    {u : M → Real} {U : Set M} {L : NNReal}
    (h : IsLaplacianLEDistributionalOn (I := I) g u (fun _ ↦ 0) U)
    (hu : ∀ x y, edist (u x) (u y) ≤ (L : ENNReal) *
      riemannianEDistOf (I := I) g x y)
    (φ : C^∞⟮I, M; Real⟯)
    (hφ : φ ∈ compactlySupportedSmoothFunctions I M)
    (hφU : tsupport (φ : M → Real) ⊆ U)
    (hφ0 : ∀ x : M, 0 ≤ φ x) :
    0 ≤ ∫ x, tangentSectionAction (I := I) (gradG (I := I) g φ) u x
      ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  simpa only [zero_mul, integral_zero, neg_zero] using
    h.neg_integral_bound_mul_le_integral_gradient_pairing
      (I := I) g hu φ hφ hφU hφ0

end DifferentialGeometry.Geometry.Operator.IsLaplacianLEDistributionalOn
