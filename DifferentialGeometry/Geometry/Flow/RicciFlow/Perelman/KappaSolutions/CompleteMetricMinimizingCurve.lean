import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import DifferentialGeometry.Geometry.Comparison.DistanceHessianLocal
import DifferentialGeometry.Bundle.FiberBundleHausdorff

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

theorem completeMetric_exists_minimizing_curve
    (g : SmoothRiemannianMetric I N) (hcomplete : RiemannianMetricComplete (I := I) g)
    (p q : N) (hfin : riemannianEDistOf (I := I) g p q ≠ ⊤) :
    ∃ γ : ℝ → N, ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 1) ∧
      γ 0 = p ∧ γ 1 = q ∧
      metricPathELength (I := I) g γ 0 1 = riemannianEDistOf (I := I) g p q := by
  let _ : IsManifold I 1 N := IsManifold.of_le (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace N := Manifold.metrizableSpace I N
  let _ : T3Space N := inferInstance
  let _ : RiemannianBundle (fun x : N => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : N => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace N := EMetricSpace.ofRiemannianMetric I N
  let _ : PseudoEMetricSpace N := (EMetricSpace.ofRiemannianMetric I N).toPseudoEMetricSpace
  let _ : CompleteSpace N := hcomplete.complete
  have hEnorm : IsMetricNorm (I := I) g :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm g x v
  have hfin' : riemannianEDist I p q ≠ ⊤ := by
    simpa [riemannianEDistOf] using hfin
  obtain ⟨v, hvexp, hvnorm⟩ := minExp_of_ne_top g hEnorm p q hfin'
  let γ : ℝ → N := intrinsicGeodesic (I := I) g hEnorm p v
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 1) :=
    (intrinsicGeodesic_contMDiffOn (I := I) g hEnorm p v).mono (subset_univ _)
  have hγ0 : γ 0 = p := intrinsicGeodesic_zero (I := I) g hEnorm p v
  have hγ1 : γ 1 = q := by
    change intrinsicGeodesic (I := I) g hEnorm p v 1 = q
    rw [← expMapIntrinsic_def]
    exact hvexp
  refine ⟨γ, hγ, hγ0, hγ1, ?_⟩
  rw [metricPathELength_eq]
  calc
    _ = ∫⁻ _ in Ioo (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt (g.inner p v v)) := by
      refine setLIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
      exact congrArg (fun z : ℝ => ENNReal.ofReal (Real.sqrt z))
        (intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p v t)
    _ = ENNReal.ofReal (Real.sqrt (g.inner p v v)) := by
      rw [setLIntegral_const, Real.volume_Ioo]
      norm_num
    _ = riemannianEDist I p q := by
      rw [hvnorm]
      exact ENNReal.ofReal_toReal hfin'
    _ = riemannianEDistOf (I := I) g p q :=
      (riemannianEDistOf_eq_riemannianEDist g hEnorm p q).symm

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
