import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Restriction
import Mathlib.Geometry.Manifold.Instances.Sphere
import DifferentialGeometry.Bundle.Section

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Geometry.Metric
section General
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem metricCovDeriv_eq_on_open
    (h₁ h₂ gRef : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    (hU : ∀ y : M, y ∈ U → ∀ v w : TangentSpace I y,
      h₁.inner y v w = h₂.inner y v w) (m : ℕ) (x : U) :
    metricCovDeriv h₁ gRef m (x : M) = metricCovDeriv h₂ gRef m (x : M) := by
  have heq : h₁.restrictOpen U = h₂.restrictOpen U :=
    SmoothRiemannianMetric.ext_inner (fun y v w => hU y y.2 v w)
  have hres (k : SmoothRiemannianMetric I M) (slots : Fin (m + 2) → TangentSpace I x) :
      metricCovDeriv (k.restrictOpen U) (gRef.restrictOpen U) m x slots =
        metricCovDeriv k gRef m (x : M) slots := by
    simpa only [metricCovDeriv_eq_covDerivOfField] using
      covDerivOfField_restrictOpen gRef U
        (Tensor0SBundle.metricTensorField (k.restrictOpen U))
        (Tensor0SBundle.metricTensorField k) (fun y slots => rfl) m x slots
  ext slots
  rw [← hres h₁ slots, ← hres h₂ slots, heq]

theorem metricCovDeriv_eq_of_eqOn_open_closure
    (h₁ h₂ gRef : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    (hU : ∀ y : M, y ∈ U → ∀ v w : TangentSpace I y,
      h₁.inner y v w = h₂.inner y v w)
    (x : M) (hx : x ∈ closure (U : Set M)) (m : ℕ) :
    metricCovDeriv h₁ gRef m x = metricCovDeriv h₂ gRef m x := by
  classical
  ext slots
  let W : Fin (m + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) := fun i =>
    (ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x (slots i)).choose
  have hW : ∀ i, W i x = slots i := fun i =>
    (ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x (slots i)).choose_spec
  have hcont (k : SmoothRiemannianMetric I M) :
      Continuous (fun y : M => metricCovDeriv k gRef m y (fun i => W i y)) := by
    have hd : ContMDiff I 𝓘(ℝ) ∞
        (fun y : M => metricCovDeriv k gRef m y (fun i => W i y)) := fun y =>
      Tensor0SBundle.tensor0SField_eval_smooth_slots_contMDiffAt
        (metricCovDeriv k gRef m) W y
    exact hd.continuous
  have hvals : EqOn
      (fun y : M => metricCovDeriv h₁ gRef m y (fun i => W i y))
      (fun y : M => metricCovDeriv h₂ gRef m y (fun i => W i y)) U := by
    intro y hy
    exact congrArg (fun A => A (fun i => W i y))
      (metricCovDeriv_eq_on_open h₁ h₂ gRef U hU m ⟨y, hy⟩)
  have hat := hvals.closure (hcont h₁) (hcont h₂) hx
  simpa only [hW] using hat
end General

section Cylinder
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2 + 1)]
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private abbrev Cyl := Metric.sphere (0 : E) 1 × ℝ

theorem metricCovDeriv_eq_at_height_zero_of_eq_on_negative
    (U : TopologicalSpace.Opens (Cyl (E := E)))
    (h₁ h₂ gRef : SmoothRiemannianMetric IC U)
    (heq : ∀ y : U, (y : Cyl (E := E)).2 < 0 → ∀ v w : TangentSpace IC y,
      h₁.inner y v w = h₂.inner y v w)
    (x : U) (hx : (x : Cyl (E := E)).2 = 0) (m : ℕ) :
    metricCovDeriv h₁ gRef m x = metricCovDeriv h₂ gRef m x := by
  let V : TopologicalSpace.Opens U :=
    ⟨{y : U | (y : Cyl (E := E)).2 < 0},
      isOpen_lt (continuous_snd.comp continuous_subtype_val) continuous_const⟩
  have hopen : IsOpenMap (fun y : U => (y : Cyl (E := E)).2) :=
    isOpenMap_snd.comp U.isOpen.isOpenEmbedding_subtypeVal.isOpenMap
  have hx0 : (x : Cyl (E := E)).2 ∈ closure (Iio (0 : ℝ)) := by
    rw [closure_Iio, hx]
    exact (show (0 : ℝ) ≤ 0 from le_rfl)
  have hclosure : x ∈ closure (V : Set U) :=
    hopen.preimage_closure_subset_closure_preimage hx0
  exact metricCovDeriv_eq_of_eqOn_open_closure h₁ h₂ gRef V heq x hclosure m
end Cylinder
end DifferentialGeometry.Geometry.Metric
