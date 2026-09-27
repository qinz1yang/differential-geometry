import DifferentialGeometry.Geometry.Connection.ParallelTransport.Piecewise
import Mathlib.Analysis.Convex.Basic

open Bundle Set
open scoped Manifold ContDiff

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle 1 F V I]
  {A : Type*}

structure IsParallelClosedConvexFamily (cov : A → CovariantDerivative I F V)
    (K : Set (TotalSpace F V)) : Prop where
  isClosed : IsClosed K
  nonempty : ∀ x, {v : V x | (⟨x, v⟩ : TotalSpace F V) ∈ K}.Nonempty
  convex : ∀ x, Convex ℝ {v : V x | (⟨x, v⟩ : TotalSpace F V) ∈ K}
  isParallel : ∀ a, (cov a).IsParallelSet K

theorem IsParallelClosedConvexFamily.isClosed_fiber
    {cov : A → CovariantDerivative I F V} {K : Set (TotalSpace F V)}
    (hK : IsParallelClosedConvexFamily cov K) (x : M) :
    IsClosed {v : V x | (⟨x, v⟩ : TotalSpace F V) ∈ K} :=
  hK.isClosed.preimage (FiberBundle.continuous_totalSpaceMk F V x)

theorem IsParallelClosedConvexFamily.image_eq_of_piecewise_parallel
    {cov : A → CovariantDerivative I F V} {K : Set (TotalSpace F V)}
    (hK : IsParallelClosedConvexFamily cov K) (s : A)
    {γ : ℝ → M} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b)
    (T : ∀ t : ℝ, V (γ t₀) ≃L[ℝ] V (γ t)) (hT₀ : ∀ v, T t₀ v = v)
    (hT : ∀ v, (cov s).IsPiecewiseParallelOn γ (fun t => T t v) a b)
    {t : ℝ} (ht : t ∈ Icc a b) :
    T t '' {v : V (γ t₀) | (⟨γ t₀, v⟩ : TotalSpace F V) ∈ K} =
      {v : V (γ t) | (⟨γ t, v⟩ : TotalSpace F V) ∈ K} :=
  (hK.isParallel s).image_eq_of_piecewise_parallel ht₀ T hT₀ hT ht

theorem isParallelClosedConvexFamily_univ (cov : A → CovariantDerivative I F V) :
    IsParallelClosedConvexFamily cov univ :=
  ⟨isClosed_univ, fun _ => ⟨0, mem_univ _⟩,
    fun _ => convex_univ, fun _ => ⟨fun _ _ _ _ _ _ _ => mem_univ _⟩⟩

theorem IsParallelClosedConvexFamily.ne_empty
    {cov : A → CovariantDerivative I F V} {K : Set (TotalSpace F V)}
    (hK : IsParallelClosedConvexFamily cov K) (x : M) : K ≠ ∅ := by
  obtain ⟨v, hv⟩ := hK.nonempty x
  intro h
  change (⟨x, v⟩ : TotalSpace F V) ∈ K at hv
  rw [h] at hv
  exact hv

end CovariantDerivative
