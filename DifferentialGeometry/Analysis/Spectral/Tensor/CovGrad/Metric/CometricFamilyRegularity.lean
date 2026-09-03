import DifferentialGeometry.Geometry.Metric.Family.InverseMetricSmoothness
import DifferentialGeometry.Bundle.ContinuousLinearMapSection.ParametricSmoothness
import DifferentialGeometry.Tensor.RSTensor.ParametricSmoothness
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Metric.CometricDoubleTrace

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator


noncomputable section


open Set Function Bundle DifferentialGeometry.Tensor0SBundle
open scoped Topology Manifold BigOperators ContDiff Matrix

namespace DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Spectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M]

namespace MetricFamilySmoothOn

theorem cometricRaiseSlot0Fib_jointContMDiffOn (s : ℕ)
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (Y : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace (s + 2) I p.1)
    (hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (s + 2) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (s + 2) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (s + 2) I z) p.1 (Y p))
      ((Set.univ : Set M) ×ˢ D.regular)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 1 (s + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 1 (s + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 1 (s + 1) I z) p.1
        (cometricRaiseSlot0Fib (I := I) (g_fam p.2) s p.1 (Y p)))
      ((Set.univ : Set M) ×ˢ D.regular) := by
  apply contMDiffOn_clm_section_of_apply (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 1 ℝ E)
    (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 1 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
    (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace (s + 1) I x)
    (φ := fun p : M × ℝ => (show Tensor0SBundle.Tensor0SSpace 1 I p.1 →L[ℝ]
        Tensor0SBundle.Tensor0SSpace (s + 1) I p.1 from
      cometricRaiseSlot0Fib (I := I) (g_fam p.2) s p.1 (Y p)))
    (S := D.regular)
  intro β
  have hsharp := inverseMetricSharpFib_jointContMDiffOn (I := I) g_fam hG
  have hβjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z) p.1 (β p.1))
      ((Set.univ : Set M) ×ˢ D.regular) := by
    have hβM : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 1 ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z) x (β x)) := β.contMDiff
    exact hβM.comp_contMDiffOn contMDiffOn_fst
  have hsharpβ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
        (inverseMetricSharpFib (I := I) (g_fam p.2) p.1 (β p.1)))
      ((Set.univ : Set M) ×ˢ D.regular) :=
    ContMDiffOn.clm_bundle_apply (b := Prod.fst) hsharp hβjoint
  set sharpβ : ∀ p : M × ℝ, TangentSpace I p.1 :=
    fun p => inverseMetricSharpFib (I := I) (g_fam p.2) p.1 (β p.1)
  have hraise := interiorProductField_jointContMDiffOn_vecJoint (I := I) (s := s + 1)
    (S := D.regular) (X := sharpβ) hsharpβ (α := fun p => Y p) hY
  refine hraise.congr (fun p _ => ?_)
  change TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
      (E := fun z : M => Tensor0SBundle.Tensor0SSpace (s + 1) I z) p.1
      (Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) (s + 1) p.1
        (sharpβ p) (Y p)) =
    TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
      (E := fun z : M => Tensor0SBundle.Tensor0SSpace (s + 1) I z) p.1
      ((show Tensor0SBundle.Tensor0SSpace 1 I p.1 →L[ℝ]
          Tensor0SBundle.Tensor0SSpace (s + 1) I p.1 from
        cometricRaiseSlot0Fib (I := I) (g_fam p.2) s p.1 (Y p)) (β p.1))
  congr 1

theorem cometricDoubleTraceFib_jointContMDiffOn (p : ℕ)
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (Y : ∀ q : M × ℝ, Tensor0SBundle.Tensor0SSpace (p + 2) I q.1)
    (hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (p + 2) ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (p + 2) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (p + 2) I z) q.1 (Y q))
      ((Set.univ : Set M) ×ˢ D.regular)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel p ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel p ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace p I z) q.1
        (cometricDoubleTraceFib (I := I) (g_fam q.2) p q.1 (Y q)))
      ((Set.univ : Set M) ×ˢ D.regular) := by
  have hraise := cometricRaiseSlot0Fib_jointContMDiffOn (I := I) p g_fam hG Y hY
  have htrace := contractTraceField_jointContMDiffOn (I := I) 0 p
    (S := D.regular)
    (fun q : M × ℝ => cometricRaiseSlot0Fib (I := I) (g_fam q.2) p q.1 (Y q))
    hraise
  have hunit : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 0 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 0 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 0 I z) q.1
        (DifferentialGeometry.Geometry.Connection.unitZeroSec (I := I) (M := M) q.1))
      ((Set.univ : Set M) ×ˢ D.regular) :=
    (DifferentialGeometry.Geometry.Connection.unitZeroSec (I := I)
      (M := M)).contMDiff.comp_contMDiffOn
      contMDiffOn_fst
  have htraceUnit := ContMDiffOn.clm_bundle_apply (b := Prod.fst) htrace hunit
  refine htraceUnit.congr (fun q _ => ?_)
  congr 1
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  beta_reduce
  rw [cometricDoubleTraceFib_toModel]
  rw [← model_contract_trace_raiseSlot0ModelL (E := E) p
    (cometricLmodel (I := I) (g_fam q.2) q.1)
    (Tensor0SBundle.Tensor0SSpace.toModel (Y q))]
  rw [contract_trace_unitZero_toModel (I := I) p q.1
    (cometricRaiseSlot0Fib (I := I) (g_fam q.2) p q.1 (Y q))]
  congr 1

end MetricFamilySmoothOn

end DifferentialGeometry.Geometry.Curvature
