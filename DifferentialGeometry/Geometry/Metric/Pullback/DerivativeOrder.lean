import DifferentialGeometry.Geometry.Metric.Pullback.FiniteCoefficients
import DifferentialGeometry.Geometry.Metric.FiniteLedger.Curvature
import DifferentialGeometry.Geometry.Metric.FiniteLedger.Coefficient
import DifferentialGeometry.Analysis.FiniteDimensional.Coercivity

set_option autoImplicit false

noncomputable section

open Bundle Set
open scoped Manifold ContDiff

namespace Bundle.ContMDiffRiemannianMetric

variable {V E H M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]

theorem isCoercive_pullback_inner {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    {f : V → M} {x : V} (hf : Function.Injective (mfderiv 𝓘(ℝ, V) I f x : V →L[ℝ] E)) :
    IsCoercive (E := V) ((g.inner (f x) : E →L[ℝ] E →L[ℝ] ℝ).bilinearComp
      (E := E) (F := E) (E' := V) (F' := V)
      (mfderiv 𝓘(ℝ, V) I f x : V →L[ℝ] E)
      (mfderiv 𝓘(ℝ, V) I f x : V →L[ℝ] E)) := by
  apply ContinuousLinearMap.isCoercive_of_posDef
  intro v hv
  apply g.pos
  intro hzero
  apply hv
  apply hf
  exact hzero.trans (map_zero (mfderiv 𝓘(ℝ, V) I f x)).symm

theorem contDiffOn_pullback_christoffel {n s : ℕ∞ω} {K : ℕ}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (hKn : (K : ℕ∞ω) ≤ n) (hKs : (K : ℕ∞ω) + 1 ≤ s) (hK : 1 ≤ K)
    {f : V → M} {U : Set V} (hU : IsOpen U)
    (hf : ContMDiffOn 𝓘(ℝ, V) I s f U)
    (himm : ∀ x ∈ U, Function.Injective (mfderiv 𝓘(ℝ, V) I f x : V →L[ℝ] E)) :
    let _ : AddCommGroup (V →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
    let _ : AddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
    let b : V → V →L[ℝ] V →L[ℝ] ℝ := fun y => (g.inner (f y) : E →L[ℝ] E →L[ℝ] ℝ).bilinearComp
      (E := E) (F := E) (E' := V) (F' := V)
      (mfderiv 𝓘(ℝ, V) I f y : V →L[ℝ] E)
      (mfderiv 𝓘(ℝ, V) I f y : V →L[ℝ] E)
    ContDiffOn ℝ ((K - 1 : ℕ) : ℕ∞ω)
      (fun y => DifferentialGeometry.MetricKoszul.raisedKoszulOp (E := V)
        (b y) (fderiv ℝ b y)) U := by
  exact DifferentialGeometry.Geometry.christoffel_contDiffOn (E := V) hU
    (g.contDiffOn_pullback_inner hKn hKs hU hf)
    (fun x hx => g.isCoercive_pullback_inner (himm x hx)) hK

theorem contDiffOn_pullback_curvature {n s : ℕ∞ω} {K : ℕ}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (hKn : (K : ℕ∞ω) ≤ n) (hKs : (K : ℕ∞ω) + 1 ≤ s) (hK : 2 ≤ K)
    {f : V → M} {U : Set V} (hU : IsOpen U)
    (hf : ContMDiffOn 𝓘(ℝ, V) I s f U)
    (himm : ∀ x ∈ U, Function.Injective (mfderiv 𝓘(ℝ, V) I f x : V →L[ℝ] E))
    (X Y Z W : V) :
    let b : V → V →L[ℝ] V →L[ℝ] ℝ := fun y => (g.inner (f y) : E →L[ℝ] E →L[ℝ] ℝ).bilinearComp
      (E := E) (F := E) (E' := V) (F' := V)
      (mfderiv 𝓘(ℝ, V) I f y : V →L[ℝ] E)
      (mfderiv 𝓘(ℝ, V) I f y : V →L[ℝ] E)
    ContDiffOn ℝ ((K - 2 : ℕ) : ℕ∞ω)
      (fun y => DifferentialGeometry.Analysis.coefficientRm04 b y X Y Z W) U := by
  exact DifferentialGeometry.Analysis.coefficientRm04_contDiffOn hU
    (g.contDiffOn_pullback_inner hKn hKs hU hf)
    (fun x hx => g.isCoercive_pullback_inner (himm x hx)) hK X Y Z W

end Bundle.ContMDiffRiemannianMetric
