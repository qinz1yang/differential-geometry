import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletH1Compl
import DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.Gradient
import DifferentialGeometry.Geometry.Operator.WithBoundary.GradientContinuity

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal NNReal
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary
open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Integral.DivergenceTheorem (tangentSectionAction)
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Operator

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

def dirichletMass
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (u v : SmoothScalarDirichlet q) : ℝ :=
  ∫ x, u.toFun x * v.toFun x
    ∂(riemannianVolumeMeasure (I := I_half n) (M := M) h)

theorem dirichletMass_integrable
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (u v : SmoothScalarDirichlet q) :
    Integrable (fun x : M => u.toFun x * v.toFun x)
      (riemannianVolumeMeasure (I := I_half n) (M := M) h) := by
  let _ : IsFiniteMeasure
      (riemannianVolumeMeasure (I := I_half n) (M := M) h) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I_half n) (M := M) h
  exact (u.smooth.continuous.mul v.smooth.continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem dirichletMass_add_left
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (u₁ u₂ v : SmoothScalarDirichlet q) :
    dirichletMass h (u₁ + u₂) v =
      dirichletMass h u₁ v + dirichletMass h u₂ v := by
  unfold dirichletMass
  simp only [InteriorSmoothScalar.toFun_add_apply, add_mul]
  exact integral_add (dirichletMass_integrable h u₁ v)
    (dirichletMass_integrable h u₂ v)

theorem dirichletMass_smul_left
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (c : ℝ) (u v : SmoothScalarDirichlet q) :
    dirichletMass h (c • u) v = c * dirichletMass h u v := by
  unfold dirichletMass
  simp only [InteriorSmoothScalar.toFun_smul_apply, mul_assoc, integral_const_mul]

theorem dirichletMass_symm
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (u v : SmoothScalarDirichlet q) :
    dirichletMass h u v = dirichletMass h v u := by
  unfold dirichletMass
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact mul_comm _ _

theorem dirichletMass_add_right
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (u v₁ v₂ : SmoothScalarDirichlet q) :
    dirichletMass h u (v₁ + v₂) =
      dirichletMass h u v₁ + dirichletMass h u v₂ := by
  rw [dirichletMass_symm, dirichletMass_add_left,
    dirichletMass_symm h v₁ u, dirichletMass_symm h v₂ u]

theorem dirichletMass_smul_right
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (c : ℝ) (u v : SmoothScalarDirichlet q) :
    dirichletMass h u (c • v) = c * dirichletMass h u v := by
  rw [dirichletMass_symm, dirichletMass_smul_left,
    dirichletMass_symm h v u]

def dirichletEnergy
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (u v : SmoothScalarDirichlet q) : ℝ :=
  ∫ x, h.inner x
      (gradFun (I := I_half n) h u.toFun x)
      (gradFun (I := I_half n) h v.toFun x)
    ∂(riemannianVolumeMeasure (I := I_half n) (M := M) h)

theorem dirichletEnergy_integrable
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (u v : SmoothScalarDirichlet q) :
    Integrable (fun x : M => h.inner x
        (gradFun (I := I_half n) h u.toFun x)
        (gradFun (I := I_half n) h v.toFun x))
      (riemannianVolumeMeasure (I := I_half n) (M := M) h) := by
  let gu := DifferentialGeometry.Geometry.Operator.WithBoundary.gradGWithBoundarySection
    (I := I_half n) h u.smooth u.interior_support
  let gv := DifferentialGeometry.Geometry.Operator.WithBoundary.gradGWithBoundarySection
    (I := I_half n) h v.smooth v.interior_support
  have hcont : Continuous (fun x : M => h.inner x (gu x) (gv x)) :=
    TangentBundle.continuous_g_inner_of_smooth_sections (I := I_half n) h gu gv
  let _ : IsFiniteMeasure
      (riemannianVolumeMeasure (I := I_half n) (M := M) h) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I_half n) (M := M) h
  simpa only [gu, gv,
    DifferentialGeometry.Geometry.Operator.WithBoundary.grad_g_with_boundary_section_apply] using
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem dirichletEnergy_add_left
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (u₁ u₂ v : SmoothScalarDirichlet q) :
    dirichletEnergy h (u₁ + u₂) v =
      dirichletEnergy h u₁ v + dirichletEnergy h u₂ v := by
  unfold dirichletEnergy
  have hgrad : ∀ x : M,
      gradFun (I := I_half n) h (u₁ + u₂).toFun x =
        gradFun (I := I_half n) h u₁.toFun x +
          gradFun (I := I_half n) h u₂.toFun x := by
    intro x
    exact gradFun_add (I := I_half n) h
      (u₁.smooth.mdifferentiable (by simp) x)
      (u₂.smooth.mdifferentiable (by simp) x)
  simp_rw [hgrad, map_add]
  exact integral_add (dirichletEnergy_integrable h u₁ v)
    (dirichletEnergy_integrable h u₂ v)

theorem dirichletEnergy_smul_left
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (c : ℝ) (u v : SmoothScalarDirichlet q) :
    dirichletEnergy h (c • u) v = c * dirichletEnergy h u v := by
  unfold dirichletEnergy
  have hgrad : ∀ x : M,
      gradFun (I := I_half n) h (c • u).toFun x =
        c • gradFun (I := I_half n) h u.toFun x := by
    intro x
    change gradFun (I := I_half n) h (c • u.toFun) x =
      c • gradFun (I := I_half n) h u.toFun x
    exact DifferentialGeometry.Geometry.Connection.gradFun_const_smul
      (I := I_half n) h c (u.smooth.mdifferentiable (by simp) x)
  simp_rw [hgrad, map_smul]
  exact integral_const_mul c _

theorem dirichletEnergy_symm
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (u v : SmoothScalarDirichlet q) :
    dirichletEnergy h u v = dirichletEnergy h v u := by
  unfold dirichletEnergy
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact h.symm x _ _

theorem dirichletEnergy_add_right
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (u v₁ v₂ : SmoothScalarDirichlet q) :
    dirichletEnergy h u (v₁ + v₂) =
      dirichletEnergy h u v₁ + dirichletEnergy h u v₂ := by
  rw [dirichletEnergy_symm, dirichletEnergy_add_left,
    dirichletEnergy_symm h v₁ u, dirichletEnergy_symm h v₂ u]

theorem dirichletEnergy_smul_right
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (c : ℝ) (u v : SmoothScalarDirichlet q) :
    dirichletEnergy h u (c • v) = c * dirichletEnergy h u v := by
  rw [dirichletEnergy_symm, dirichletEnergy_smul_left,
    dirichletEnergy_symm h v u]

theorem dirichletEnergy_self_nonneg
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (u : SmoothScalarDirichlet q) :
    0 ≤ dirichletEnergy h u u := by
  unfold dirichletEnergy
  exact integral_nonneg fun x =>
    SmoothRiemannianMetric_inner_self_nonneg h x _

def dirichletDrift
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (u v : SmoothScalarDirichlet q) : ℝ :=
  ∫ x, h.inner x (X x) (gradFun (I := I_half n) h u.toFun x) * v.toFun x
    ∂(riemannianVolumeMeasure (I := I_half n) (M := M) h)

theorem dirichletDrift_integrable
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (u v : SmoothScalarDirichlet q) :
    Integrable (fun x : M =>
      h.inner x (X x) (gradFun (I := I_half n) h u.toFun x) * v.toFun x)
      (riemannianVolumeMeasure (I := I_half n) (M := M) h) := by
  let gu := DifferentialGeometry.Geometry.Operator.WithBoundary.gradGWithBoundarySection
    (I := I_half n) h u.smooth u.interior_support
  have hinner : Continuous (fun x : M => h.inner x (X x) (gu x)) :=
    TangentBundle.continuous_g_inner_of_smooth_sections (I := I_half n) h X gu
  let _ : IsFiniteMeasure
      (riemannianVolumeMeasure (I := I_half n) (M := M) h) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I_half n) (M := M) h
  have hint := (hinner.mul v.smooth.continuous).integrable_of_hasCompactSupport
    (μ := riemannianVolumeMeasure (I := I_half n) (M := M) h)
    (HasCompactSupport.of_compactSpace _)
  refine hint.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [gu, Pi.mul_apply,
    DifferentialGeometry.Geometry.Operator.WithBoundary.grad_g_with_boundary_section_apply]

theorem dirichletDrift_add_left
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (u₁ u₂ v : SmoothScalarDirichlet q) :
    dirichletDrift h X (u₁ + u₂) v =
      dirichletDrift h X u₁ v + dirichletDrift h X u₂ v := by
  unfold dirichletDrift
  have hgrad : ∀ x : M,
      gradFun (I := I_half n) h (u₁ + u₂).toFun x =
        gradFun (I := I_half n) h u₁.toFun x +
          gradFun (I := I_half n) h u₂.toFun x := by
    intro x
    exact gradFun_add (I := I_half n) h
      (u₁.smooth.mdifferentiable (by simp) x)
      (u₂.smooth.mdifferentiable (by simp) x)
  simp_rw [hgrad, map_add, add_mul]
  exact integral_add (dirichletDrift_integrable h X u₁ v)
    (dirichletDrift_integrable h X u₂ v)

theorem dirichletDrift_smul_left
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (c : ℝ) (u v : SmoothScalarDirichlet q) :
    dirichletDrift h X (c • u) v = c * dirichletDrift h X u v := by
  unfold dirichletDrift
  have hgrad : ∀ x : M,
      gradFun (I := I_half n) h (c • u).toFun x =
        c • gradFun (I := I_half n) h u.toFun x := by
    intro x
    change gradFun (I := I_half n) h (c • u.toFun) x =
      c • gradFun (I := I_half n) h u.toFun x
    exact DifferentialGeometry.Geometry.Connection.gradFun_const_smul
      (I := I_half n) h c (u.smooth.mdifferentiable (by simp) x)
  rw [show (fun x : M =>
      h.inner x (X x) (gradFun (I := I_half n) h (c • u).toFun x) * v.toFun x) =
      fun x => c *
        (h.inner x (X x) (gradFun (I := I_half n) h u.toFun x) * v.toFun x) by
    funext x
    rw [hgrad, map_smul, smul_eq_mul]
    ring]
  exact integral_const_mul c _

theorem dirichletDrift_add_right
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (u v₁ v₂ : SmoothScalarDirichlet q) :
    dirichletDrift h X u (v₁ + v₂) =
      dirichletDrift h X u v₁ + dirichletDrift h X u v₂ := by
  unfold dirichletDrift
  simp only [InteriorSmoothScalar.toFun_add_apply, mul_add]
  exact integral_add (dirichletDrift_integrable h X u v₁)
    (dirichletDrift_integrable h X u v₂)

theorem dirichletDrift_smul_right
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (c : ℝ) (u v : SmoothScalarDirichlet q) :
    dirichletDrift h X u (c • v) = c * dirichletDrift h X u v := by
  unfold dirichletDrift
  rw [show (fun x : M => h.inner x (X x)
      (gradFun (I := I_half n) h u.toFun x) * (c • v).toFun x) =
      fun x => c *
        (h.inner x (X x) (gradFun (I := I_half n) h u.toFun x) * v.toFun x) by
    funext x
    rw [InteriorSmoothScalar.toFun_smul_apply]
    ring]
  exact integral_const_mul c _

def dirichletWeakForm
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : ℝ) (u v : SmoothScalarDirichlet q) : ℝ :=
  -dirichletEnergy h u v + dirichletDrift h X u v - a * dirichletMass h u v

theorem dirichletWeakForm_add_left
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : ℝ) (u₁ u₂ v : SmoothScalarDirichlet q) :
    dirichletWeakForm h X a (u₁ + u₂) v =
      dirichletWeakForm h X a u₁ v + dirichletWeakForm h X a u₂ v := by
  unfold dirichletWeakForm
  rw [dirichletEnergy_add_left, dirichletDrift_add_left, dirichletMass_add_left]
  ring

theorem dirichletWeakForm_smul_left
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a c : ℝ) (u v : SmoothScalarDirichlet q) :
    dirichletWeakForm h X a (c • u) v = c * dirichletWeakForm h X a u v := by
  unfold dirichletWeakForm
  rw [dirichletEnergy_smul_left, dirichletDrift_smul_left,
    dirichletMass_smul_left]
  ring

theorem dirichletWeakForm_add_right
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : ℝ) (u v₁ v₂ : SmoothScalarDirichlet q) :
    dirichletWeakForm h X a u (v₁ + v₂) =
      dirichletWeakForm h X a u v₁ + dirichletWeakForm h X a u v₂ := by
  unfold dirichletWeakForm
  rw [dirichletEnergy_add_right, dirichletDrift_add_right, dirichletMass_add_right]
  ring

theorem dirichletWeakForm_smul_right
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a c : ℝ) (u v : SmoothScalarDirichlet q) :
    dirichletWeakForm h X a u (c • v) = c * dirichletWeakForm h X a u v := by
  unfold dirichletWeakForm
  rw [dirichletEnergy_smul_right, dirichletDrift_smul_right,
    dirichletMass_smul_right]
  ring

theorem dirichletMass_self_nonneg
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (u : SmoothScalarDirichlet q) :
    0 ≤ dirichletMass h u u := by
  unfold dirichletMass
  exact integral_nonneg fun x => mul_self_nonneg (u.toFun x)

end DifferentialGeometry.Analysis.Parabolic.Dirichlet

end
