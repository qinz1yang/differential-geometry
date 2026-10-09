import DifferentialGeometry.Geometry.Metric.BundleMusical
import DifferentialGeometry.Geometry.Connection.Trivial
import DifferentialGeometry.Geometry.Connection.HomBundle.Basic

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.HomConnectionGen

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I 1 F V]

theorem homBundleCovariantDerivativeGen_innerSL
    (cov : CovariantDerivative I F V) (hcov : cov.IsMetricCompatible)
    {σ : ∀ y, V y} {x : M}
    (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, F)) (T% σ) x)
    (v : TangentSpace I x) :
    homBundleCovariantDerivativeGen I M F V ℝ (Bundle.Trivial M ℝ)
      cov (CovariantDerivative.trivial I M ℝ) (fun y => innerSL ℝ (σ y)) x v =
      innerSL ℝ (cov σ x v) := by
  ext w
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x v
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := F) (V := V) (n := (⊤ : ℕ∞)) x w
  rw [← hX, ← hY]
  rw [homBundleCovariantDerivativeGen_apply_of_mdifferentiableAt I M F V ℝ
    (Bundle.Trivial M ℝ) cov (CovariantDerivative.trivial I M ℝ)
    (fun y => innerSL ℝ (σ y)) hσ.innerSL_bundle X.mdifferentiableAt Y.mdifferentiableAt]
  change mvfderiv I (fun y => inner ℝ (σ y) (Y y)) x (X x) -
    inner ℝ (σ x) (cov (fun y => Y y) x (X x)) =
      inner ℝ (cov σ x (X x)) (Y x)
  rw [hcov.mvfderiv_inner_eq (fun y => X y) hσ Y.mdifferentiableAt]
  abel

end DifferentialGeometry.HomConnectionGen
