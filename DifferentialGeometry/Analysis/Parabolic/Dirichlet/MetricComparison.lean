import DifferentialGeometry.Analysis.Parabolic.Dirichlet.Galerkin
import DifferentialGeometry.Geometry.Curvature.Bochner.ScalarBochner
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Operator.WithBoundary
open DifferentialGeometry.Geometry.Curvature

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [T2Space M] [CompactSpace M] in
private theorem integral_le_smul_measure
    {μ ν : Measure M} {C : ℝ≥0∞}
    (hC0 : C ≠ 0) (hCtop : C ≠ ⊤) (hμν : μ ≤ C • ν)
    {f : M → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hfint : Integrable f ν) :
    ∫ x, f x ∂μ ≤ C.toReal * ∫ x, f x ∂ν := by
  have hfC : Integrable f (C • ν) :=
    (integrable_smul_measure hC0 hCtop).2 hfint
  calc
    ∫ x, f x ∂μ ≤ ∫ x, f x ∂(C • ν) :=
      integral_mono_measure hμν (Filter.Eventually.of_forall hf0) hfC
    _ = C.toReal * ∫ x, f x ∂ν := by
      rw [integral_smul_measure, smul_eq_mul]

private theorem dirichletMass_self_integrable
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (u : SmoothScalarDirichlet q) :
    Integrable (fun x : M ↦ u.toFun x * u.toFun x)
      (riemannianVolumeMeasure (I := I_half n) (M := M) h) := by
  let _ : IsFiniteMeasure
      (riemannianVolumeMeasure (I := I_half n) (M := M) h) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I_half n) (M := M) h
  exact (u.smooth.continuous.mul u.smooth.continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem dirichletMass_self_le_of_volume
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (C : ℝ≥0∞) (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      C • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (u : SmoothScalarDirichlet q) :
    dirichletMass h u u ≤ C.toReal * dirichletMass q u u := by
  exact integral_le_smul_measure hC0 hCtop hvol
    (fun x ↦ mul_self_nonneg (u.toFun x))
    (dirichletMass_self_integrable q u)

omit [T2Space M] [CompactSpace M] in
private theorem dirichletEnergyDensity_eq_normSq
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (u : SmoothScalarDirichlet q) (x : M) :
    h.inner x
        (gradFun (I := I_half n) h u.toFun x)
        (gradFun (I := I_half n) h u.toFun x) =
      DifferentialGeometry.Tensor0SBundle.normSq0S
        (I := I_half n) h x 1
        (differential1FormFun (I := I_half n) u.toFun x) := by
  rw [DifferentialGeometry.Tensor0SBundle.normSq0S_eq_inner]
  exact (inner0S_differential1FormFun_pair_eq_grad_inner
      (I := I_half n) h u.toFun u.toFun x).symm

omit [T2Space M] [CompactSpace M] in
private theorem dirichletEnergyDensity_continuous
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (u : SmoothScalarDirichlet q) :
    Continuous (fun x : M ↦ h.inner x
      (gradFun (I := I_half n) h u.toFun x)
      (gradFun (I := I_half n) h u.toFun x)) :=
  continuous_g_inner_gradFun_gradFun h u.smooth u.smooth

private theorem dirichletEnergyDensity_integrable
    {q : SmoothRiemannianMetric (I_half n) M}
    (h k : SmoothRiemannianMetric (I_half n) M)
    (u : SmoothScalarDirichlet q) :
    Integrable (fun x : M ↦ h.inner x
      (gradFun (I := I_half n) h u.toFun x)
      (gradFun (I := I_half n) h u.toFun x))
      (riemannianVolumeMeasure (I := I_half n) (M := M) k) := by
  let _ : IsFiniteMeasure
      (riemannianVolumeMeasure (I := I_half n) (M := M) k) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I_half n) (M := M) k
  exact (dirichletEnergyDensity_continuous h u).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem dirichletEnergy_self_le_of_metric_and_volume
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) q ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) h)
    (u : SmoothScalarDirichlet q) :
    dirichletEnergy q u u ≤
      Cv.toReal * Cg * dirichletEnergy h u u := by
  have hpoint : ∀ x : M,
      q.inner x
          (gradFun (I := I_half n) q u.toFun x)
          (gradFun (I := I_half n) q u.toFun x) ≤
        Cg * h.inner x
          (gradFun (I := I_half n) h u.toFun x)
          (gradFun (I := I_half n) h u.toFun x) := by
    intro x
    have hsymm := DifferentialGeometry.Tensor0SBundle.metric_equiv_symm
      (I := I_half n) q h x hCg (hequiv x)
    have hnorm := DifferentialGeometry.Tensor0SBundle.normSq0S_upper_le_of_equiv
      (I := I_half n) h q x 1 hCg hsymm
      (differential1FormFun (I := I_half n) u.toFun x)
    rw [pow_one] at hnorm
    simpa only [dirichletEnergyDensity_eq_normSq] using hnorm
  have hqint := dirichletEnergyDensity_integrable q q u
  have hhqint := (dirichletEnergyDensity_integrable h q u).const_mul Cg
  have hhint := (dirichletEnergyDensity_integrable h h u).const_mul Cg
  unfold dirichletEnergy
  calc
    ∫ x, q.inner x
          (gradFun (I := I_half n) q u.toFun x)
          (gradFun (I := I_half n) q u.toFun x)
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) q) ≤
        ∫ x, Cg * h.inner x
          (gradFun (I := I_half n) h u.toFun x)
          (gradFun (I := I_half n) h u.toFun x)
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) q) :=
      integral_mono hqint hhqint hpoint
    _ ≤ Cv.toReal * ∫ x, Cg * h.inner x
          (gradFun (I := I_half n) h u.toFun x)
          (gradFun (I := I_half n) h u.toFun x)
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) h) :=
      integral_le_smul_measure hCv0 hCvtop hvol
        (fun x ↦ mul_nonneg (le_trans zero_le_one hCg) (by
          by_cases hv : gradFun (I := I_half n) h u.toFun x = 0
          · rw [hv]
            simp
          · exact (h.pos x _ hv).le)) hhint
    _ = Cv.toReal * Cg * ∫ x, h.inner x
          (gradFun (I := I_half n) h u.toFun x)
          (gradFun (I := I_half n) h u.toFun x)
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) h) := by
      rw [integral_const_mul]
      ring

end DifferentialGeometry.Analysis.Parabolic.Dirichlet

end
