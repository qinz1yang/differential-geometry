import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.LeftRightNhds


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open scoped ContDiff Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [∀ x, FiniteDimensional ℝ (V x)] [FiberBundle F V]


theorem covariantDerivative_mem_at_left_endpoint
    (cov : ℝ → CovariantDerivative I F V) (K : (x : M) → Submodule ℝ (V x))
    {a b : ℝ} (hab : a < b) (σ : (x : M) → V x) (x : M) (Y : TangentSpace I x)
    (hcont : ContinuousWithinAt (fun t => cov t σ x Y) (Iio b) b)
    (hmem : ∀ t ∈ Ioo a b, cov t σ x Y ∈ K x) : cov b σ x Y ∈ K x := by
  apply (K x).closed_of_finiteDimensional.mem_of_tendsto hcont
  filter_upwards [Ioo_mem_nhdsLT hab] with t ht
  exact hmem t ht


theorem covariantDerivative_preserves_at_left_endpoint
    (cov : ℝ → CovariantDerivative I F V) (K : (x : M) → Submodule ℝ (V x))
    {a b : ℝ} (hab : a < b)
    (hcont : ∀ U : Set M, IsOpen U → ∀ σ : (x : M) → V x,
      ContMDiffOn I (I.prod 𝓘(ℝ, F)) ∞ (fun x => TotalSpace.mk' F x (σ x)) U →
      (∀ x ∈ U, σ x ∈ K x) → ∀ x ∈ U, ∀ Y : TangentSpace I x,
        ContinuousWithinAt (fun t => cov t σ x Y) (Iio b) b)
    (hparallel : ∀ t ∈ Ioo a b, ∀ U : Set M, IsOpen U → ∀ σ : (x : M) → V x,
      ContMDiffOn I (I.prod 𝓘(ℝ, F)) ∞ (fun x => TotalSpace.mk' F x (σ x)) U →
      (∀ x ∈ U, σ x ∈ K x) → ∀ x ∈ U, ∀ Y : TangentSpace I x,
        cov t σ x Y ∈ K x) :
    ∀ U : Set M, IsOpen U → ∀ σ : (x : M) → V x,
      ContMDiffOn I (I.prod 𝓘(ℝ, F)) ∞ (fun x => TotalSpace.mk' F x (σ x)) U →
      (∀ x ∈ U, σ x ∈ K x) → ∀ x ∈ U, ∀ Y : TangentSpace I x,
        cov b σ x Y ∈ K x := by
  intro U hU σ hσ hK x hx Y
  exact covariantDerivative_mem_at_left_endpoint cov K hab σ x Y
    (hcont U hU σ hσ hK x hx Y)
    (fun t ht => hparallel t ht U hU σ hσ hK x hx Y)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
