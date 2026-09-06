import DifferentialGeometry.Analysis.InnerProductSpace.HilbertSchmidt
import DifferentialGeometry.Geometry.Metric.BundlePullback
import DifferentialGeometry.Geometry.Metric.MetricFiberData.Hom
import DifferentialGeometry.Geometry.Metric.MetricFiberData.Topology

noncomputable section

namespace Bundle

variable {B : Type*} (U V : B → Type*)
  [∀ x, NormedAddCommGroup (U x)] [∀ x, InnerProductSpace ℝ (U x)]
  [∀ x, FiniteDimensional ℝ (U x)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]

def homRiemannianMetric : RiemannianMetric (fun x => U x →L[ℝ] V x) :=
  (RiemannianMetric.ofInnerProductSpace (fun x =>
    PiLp 2 (fun _ : Fin (Module.finrank ℝ (U x)) => V x))).pullback id
      (fun x => (stdOrthonormalBasis ℝ (U x)).continuousLinearMapEquiv)

@[simp] theorem homRiemannianMetric_inner (x : B) (A C : U x →L[ℝ] V x) :
    (homRiemannianMetric U V).inner x A C = ContinuousLinearMap.hilbertSchmidtInner A C := by
  exact (ContinuousLinearMap.hilbertSchmidtInner_eq_inner
    (stdOrthonormalBasis ℝ (U x)) A C).symm

theorem homRiemannianMetric_inner_eq_sum {ι : Type*} [Fintype ι]
    (x : B) (b : OrthonormalBasis ι ℝ (U x)) (A C : U x →L[ℝ] V x) :
    (homRiemannianMetric U V).inner x A C =
      ∑ i, inner ℝ (A (b i)) (C (b i)) := by
  rw [homRiemannianMetric_inner, ContinuousLinearMap.hilbertSchmidtInner_eq_sum b]

open DifferentialGeometry.Tensor0SBundle in
theorem homRiemannianMetric_eq_metricFiberData [∀ x, FiniteDimensional ℝ (V x)] :
    homRiemannianMetric U V = MetricFiberData.riemannianMetric (fun x =>
      MetricFiberData.homCLM (MetricFiberData.ofInnerProductSpace (F := U x))
        (MetricFiberData.ofInnerProductSpace (F := V x))) := by
  apply RiemannianMetric.ext
  intro x A C
  rw [homRiemannianMetric_inner_eq_sum U V x (stdOrthonormalBasis ℝ (U x))]
  exact (MetricFiberData.hom_inner_eq_sum_orthonormalBasis
    (stdOrthonormalBasis ℝ (U x)) A.toLinearMap C.toLinearMap).symm

variable {B' : Type*} (U' V' : B' → Type*)
  [∀ x, NormedAddCommGroup (U' x)] [∀ x, InnerProductSpace ℝ (U' x)]
  [∀ x, FiniteDimensional ℝ (U' x)]
  [∀ x, NormedAddCommGroup (V' x)] [∀ x, InnerProductSpace ℝ (V' x)]

theorem homRiemannianMetric_inner_congr
    (x : B) (y : B') (eU : U x ≃ₗᵢ[ℝ] U' y) (eV : V x →ₗᵢ[ℝ] V' y)
    (A C : U x →L[ℝ] V x) :
    (homRiemannianMetric U' V').inner y
        (eV.toContinuousLinearMap.comp (A.comp eU.symm.toContinuousLinearEquiv.toContinuousLinearMap))
        (eV.toContinuousLinearMap.comp (C.comp eU.symm.toContinuousLinearEquiv.toContinuousLinearMap)) =
      (homRiemannianMetric U V).inner x A C := by
  simp only [homRiemannianMetric_inner]
  exact ContinuousLinearMap.hilbertSchmidtInner_congr eU eV A C

end Bundle
