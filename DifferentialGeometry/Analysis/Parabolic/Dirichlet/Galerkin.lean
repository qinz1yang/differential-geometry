import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletH1Compl
import DifferentialGeometry.Analysis.Integration.Measure.FamilyContinuity
import DifferentialGeometry.Analysis.ODE.StateCoerciveMass
import DifferentialGeometry.Geometry.Connection.ChartBridge.Gradient
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal NNReal
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary
open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
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

private lemma dirichletMass_integrable
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

private lemma dirichletEnergy_integrable
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

private lemma dirichletDrift_integrable
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

theorem dirichletMass_time_cont
    {q : SmoothRiemannianMetric (I_half n) M}
    (g : ℝ → SmoothRiemannianMetric (I_half n) M)
    {K : Set ℝ} (hK : IsCompact K)
    (hcont : ∀ (x₀ : M)
      (i j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))), ContinuousOn
      (fun p : ℝ × M => chartGramMatrix (I := I_half n) (g p.1) x₀ p.2 i j)
      (K ×ˢ (trivializationAt (EuclideanSpace ℝ (Fin n))
        (TangentSpace (I_half n)) x₀).baseSet))
    (u v : SmoothScalarDirichlet q) :
    ContinuousOn (fun t => dirichletMass (g t) u v) K := by
  unfold dirichletMass
  apply integral_family_cont (I := I_half n) (M := M) hK hcont
  exact (u.smooth.continuous.mul v.smooth.continuous).continuousOn.comp
    continuousOn_snd (fun _ _ => Set.mem_univ _)

omit [T2Space M] [CompactSpace M] in
private lemma integral_le_smul_measure
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

theorem dirichletMass_self_rev
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (C : ℝ≥0∞) (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) q ≤
      C • riemannianVolumeMeasure (I := I_half n) (M := M) h)
    (u : SmoothScalarDirichlet q) :
    dirichletMass q u u ≤ C.toReal * dirichletMass h u u := by
  exact integral_le_smul_measure hC0 hCtop hvol
    (fun x => mul_self_nonneg (u.toFun x))
    (dirichletMass_integrable h u u)

section Finite

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

def dirichletFinMass
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (J : V →ₗ[ℝ] SmoothScalarDirichlet q) :
    V →L[ℝ] V →L[ℝ] ℝ :=
  (LinearMap.mk₂ ℝ
    (fun u v => dirichletMass h (J u) (J v))
    (fun u₁ u₂ v => by simp only [map_add, dirichletMass_add_left])
    (fun c u v => by simp only [map_smul, dirichletMass_smul_left, smul_eq_mul])
    (fun u v₁ v₂ => by simp only [map_add, dirichletMass_add_right])
    (fun c u v => by
      simp only [map_smul, dirichletMass_smul_right, smul_eq_mul])).toContinuousBilinearMap

@[simp] theorem dirichletFinMass_apply
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (J : V →ₗ[ℝ] SmoothScalarDirichlet q) (u v : V) :
    dirichletFinMass h J u v = dirichletMass h (J u) (J v) := rfl

def dirichletFinEnergy
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (J : V →ₗ[ℝ] SmoothScalarDirichlet q) :
    V →L[ℝ] V →L[ℝ] ℝ :=
  (LinearMap.mk₂ ℝ
    (fun u v => dirichletEnergy h (J u) (J v))
    (fun u₁ u₂ v => by simp only [map_add, dirichletEnergy_add_left])
    (fun c u v => by simp only [map_smul, dirichletEnergy_smul_left, smul_eq_mul])
    (fun u v₁ v₂ => by simp only [map_add, dirichletEnergy_add_right])
    (fun c u v => by
      simp only [map_smul, dirichletEnergy_smul_right, smul_eq_mul])).toContinuousBilinearMap

@[simp] theorem dirichletFinEnergy_apply
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (J : V →ₗ[ℝ] SmoothScalarDirichlet q) (u v : V) :
    dirichletFinEnergy h J u v = dirichletEnergy h (J u) (J v) := rfl

theorem dirichletFinEnergy_self_nonneg
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (J : V →ₗ[ℝ] SmoothScalarDirichlet q) (u : V) :
    0 ≤ dirichletFinEnergy h J u u := by
  rw [dirichletFinEnergy_apply]
  exact dirichletEnergy_self_nonneg h (J u)

def dirichletFinDrift
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (J : V →ₗ[ℝ] SmoothScalarDirichlet q) :
    V →L[ℝ] V →L[ℝ] ℝ :=
  (LinearMap.mk₂ ℝ
    (fun u v => dirichletDrift h X (J u) (J v))
    (fun u₁ u₂ v => by simp only [map_add, dirichletDrift_add_left])
    (fun c u v => by simp only [map_smul, dirichletDrift_smul_left, smul_eq_mul])
    (fun u v₁ v₂ => by simp only [map_add, dirichletDrift_add_right])
    (fun c u v => by
      simp only [map_smul, dirichletDrift_smul_right, smul_eq_mul])).toContinuousBilinearMap

@[simp] theorem dirichletFinDrift_apply
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (J : V →ₗ[ℝ] SmoothScalarDirichlet q) (u v : V) :
    dirichletFinDrift h X J u v = dirichletDrift h X (J u) (J v) := rfl

def dirichletFinWeakForm
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : ℝ) (J : V →ₗ[ℝ] SmoothScalarDirichlet q) :
    V →L[ℝ] V →L[ℝ] ℝ :=
  (LinearMap.mk₂ ℝ
    (fun u v => dirichletWeakForm h X a (J u) (J v))
    (fun u₁ u₂ v => by simp only [map_add, dirichletWeakForm_add_left])
    (fun c u v => by simp only [map_smul, dirichletWeakForm_smul_left, smul_eq_mul])
    (fun u v₁ v₂ => by simp only [map_add, dirichletWeakForm_add_right])
    (fun c u v => by
      simp only [map_smul, dirichletWeakForm_smul_right, smul_eq_mul])).toContinuousBilinearMap

@[simp] theorem dirichletFinWeakForm_apply
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : ℝ) (J : V →ₗ[ℝ] SmoothScalarDirichlet q) (u v : V) :
    dirichletFinWeakForm h X a J u v =
      dirichletWeakForm h X a (J u) (J v) := rfl

theorem dirichletFinMass_cont
    {q : SmoothRiemannianMetric (I_half n) M}
    (g : ℝ → SmoothRiemannianMetric (I_half n) M)
    {K : Set ℝ} (hK : IsCompact K)
    (hcont : ∀ (x₀ : M)
      (i j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))), ContinuousOn
      (fun p : ℝ × M => chartGramMatrix (I := I_half n) (g p.1) x₀ p.2 i j)
      (K ×ˢ (trivializationAt (EuclideanSpace ℝ (Fin n))
        (TangentSpace (I_half n)) x₀).baseSet))
    (J : V →ₗ[ℝ] SmoothScalarDirichlet q) :
    ContinuousOn (fun t => dirichletFinMass (g t) J) K := by
  rw [continuousOn_clm_apply]
  intro u
  rw [continuousOn_clm_apply]
  intro v
  simpa only [dirichletFinMass_apply] using
    dirichletMass_time_cont g hK hcont (J u) (J v)

theorem dirichletFinMass_lower
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (C : ℝ≥0∞) (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) q ≤
      C • riemannianVolumeMeasure (I := I_half n) (M := M) h)
    (J : V →ₗ[ℝ] SmoothScalarDirichlet q)
    (horth : ∀ u : V, dirichletMass q (J u) (J u) = ‖u‖ ^ 2)
    (u : V) :
    C.toReal⁻¹ * ‖u‖ * ‖u‖ ≤ dirichletFinMass h J u u := by
  have hCr : 0 < C.toReal := ENNReal.toReal_pos hC0 hCtop
  have hrev := dirichletMass_self_rev h C hC0 hCtop hvol (J u)
  rw [horth u] at hrev
  calc
    C.toReal⁻¹ * ‖u‖ * ‖u‖ = C.toReal⁻¹ * ‖u‖ ^ 2 := by ring
    _ ≤ dirichletMass h (J u) (J u) := (inv_mul_le_iff₀ hCr).2 hrev
    _ = dirichletFinMass h J u u := by rw [dirichletFinMass_apply]

end Finite

section FiniteFamily

variable {ι : Type*} [Fintype ι]

def dirichletFinIncl
    {q : SmoothRiemannianMetric (I_half n) M}
    (φ : ι → SmoothScalarDirichlet q) :
    EuclideanSpace ℝ ι →ₗ[ℝ] SmoothScalarDirichlet q := by
  classical
  exact
    { toFun := fun u => ∑ i, u i • φ i
      map_add' := fun u v => by
        simp only [WithLp.ofLp_add, Pi.add_apply, add_smul,
          Finset.sum_add_distrib]
      map_smul' := fun c u => by
        simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, mul_smul,
          Finset.smul_sum, RingHom.id_apply] }

omit [T2Space M] [CompactSpace M] in
@[simp] theorem dirichletFinIncl_apply
    {q : SmoothRiemannianMetric (I_half n) M}
    (φ : ι → SmoothScalarDirichlet q) (u : EuclideanSpace ℝ ι) :
    dirichletFinIncl φ u = ∑ i, u i • φ i := rfl

theorem dirichletFinIncl_orth
    {q : SmoothRiemannianMetric (I_half n) M}
    (φ : ι → SmoothScalarDirichlet q)
    (hφ : Orthonormal ℝ (fun i => smoothToLpDirichlet q (φ i)))
    (u : EuclideanSpace ℝ ι) :
    dirichletMass q (dirichletFinIncl φ u) (dirichletFinIncl φ u) = ‖u‖ ^ 2 := by
  rw [show dirichletMass q (dirichletFinIncl φ u) (dirichletFinIncl φ u) =
      ‖smoothToLpDirichlet q (dirichletFinIncl φ u)‖ ^ 2 from
    (dirichletFinIncl φ u).norm_smoothToLp_sq.symm]
  rw [← real_inner_self_eq_norm_sq]
  rw [dirichletFinIncl_apply]
  simp only [map_sum, map_smul]
  rw [hφ.inner_sum (fun i => u i) (fun i => u i) Finset.univ]
  simp only [RCLike.conj_to_real]
  rw [EuclideanSpace.norm_sq_eq]
  congr 1
  funext i
  rw [Real.norm_eq_abs, sq_abs]
  ring

end FiniteFamily

section FiniteHilbert

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V] [FiniteDimensional ℝ V]

omit [CompleteSpace V] in
theorem dirichletFinMass_coercive
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (C : ℝ≥0∞) (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) q ≤
      C • riemannianVolumeMeasure (I := I_half n) (M := M) h)
    (J : V →ₗ[ℝ] SmoothScalarDirichlet q)
    (horth : ∀ u : V, dirichletMass q (J u) (J u) = ‖u‖ ^ 2) :
    IsCoercive (dirichletFinMass h J) := by
  refine ⟨C.toReal⁻¹, inv_pos.mpr (ENNReal.toReal_pos hC0 hCtop), ?_⟩
  exact dirichletFinMass_lower h C hC0 hCtop hvol J horth

theorem dirichletFin_exists
    {q : SmoothRiemannianMetric (I_half n) M}
    (g : ℝ → SmoothRiemannianMetric (I_half n) M)
    {T : ℝ} (hT : 0 < T)
    (hcont : ∀ (x₀ : M)
      (i j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))), ContinuousOn
      (fun p : ℝ × M => chartGramMatrix (I := I_half n) (g p.1) x₀ p.2 i j)
      (Icc (0 : ℝ) T ×ˢ (trivializationAt (EuclideanSpace ℝ (Fin n))
        (TangentSpace (I_half n)) x₀).baseSet))
    (C : ℝ≥0∞) (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hvol : ∀ t ∈ Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_half n) (M := M) q ≤
        C • riemannianVolumeMeasure (I := I_half n) (M := M) (g t))
    (J : V →ₗ[ℝ] SmoothScalarDirichlet q)
    (horth : ∀ u : V, dirichletMass q (J u) (J u) = ‖u‖ ^ 2)
    (resid : ℝ → V → (V →L[ℝ] ℝ)) {A : ℝ} {L : ℝ≥0}
    (hA : 0 ≤ A)
    (hlip : ∀ t ∈ Icc (0 : ℝ) T, LipschitzWith L (resid t))
    (hres_cont : ∀ v : V, ContinuousOn (fun t => resid t v) (Icc (0 : ℝ) T))
    (haff : ∀ t ∈ Icc (0 : ℝ) T, ∀ v : V,
      ‖resid t v‖ ≤ A + (L : ℝ) * ‖v‖)
    (v₀ : V) :
    ∃ γ : ℝ → V, γ 0 = v₀ ∧ ContinuousOn γ (Icc (0 : ℝ) T) ∧
      ∀ t, (ht : t ∈ Ico (0 : ℝ) T) →
        HasDerivWithinAt γ
          ((dirichletFinMass_coercive (g t) C hC0 hCtop
              (hvol t ⟨ht.1, le_of_lt ht.2⟩) J horth).sharpCLM
            (resid t (γ t)))
          (Ici (0 : ℝ)) t := by
  have hCr : 0 < C.toReal := ENNReal.toReal_pos hC0 hCtop
  let mass : ℝ → V →L[ℝ] V →L[ℝ] ℝ := fun t => dirichletFinMass (g t) J
  have hmass : ContinuousOn mass (Icc (0 : ℝ) T) :=
    dirichletFinMass_cont g isCompact_Icc hcont J
  have hcoer : ∀ t ∈ Icc (0 : ℝ) T, ∀ v : V,
      C.toReal⁻¹ * ‖v‖ * ‖v‖ ≤ mass t v v := by
    intro t ht v
    exact dirichletFinMass_lower (g t) C hC0 hCtop (hvol t ht) J horth v
  simpa only [mass] using
    (DifferentialGeometry.Analysis.ODE.coerciveMassODE_exists
      (mass := mass) (resid := resid) hT (inv_pos.mpr hCr)
      hA hmass hcoer hlip hres_cont haff v₀)

end FiniteHilbert

end DifferentialGeometry.Analysis.Parabolic.Dirichlet

end
