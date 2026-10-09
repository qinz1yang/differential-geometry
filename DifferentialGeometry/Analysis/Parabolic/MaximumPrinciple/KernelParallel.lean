import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.PositiveSystem
import DifferentialGeometry.Geometry.Connection.ParallelTransport.SubbundleInvariance

set_option autoImplicit false

noncomputable section

open Bundle CovariantDerivative Set
open scoped Manifold ContDiff Topology InnerProductSpace

namespace PositiveSystem

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

theorem kernel_isParallelSet_of_constant_range_rank
    (g : ℝ → SmoothRiemannianMetric I M)
    (cov : ℝ → CovariantDerivative I F V)
    [∀ t, ContMDiffCovariantDerivative (cov t) ∞]
    (hcov : ∀ t, (cov t).IsMetricCompatible)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M ↦ V x →L[ℝ] V x)⟯)
    {a b : ℝ}
    (hAspace : ContMDiffOnSpacetimeEndomorphism
      (I := I) (F := F) (V := V) (n := ∞)
      (fun t x ↦ A t x) (Ioo a b ×ˢ (Set.univ : Set M)))
    (q : ℕ) (hrange : ∀ t ∈ Ioo a b, ∀ x,
      Module.finrank ℝ (A t x).range = q)
    (hApos : ∀ t ∈ Ioo a b, ∀ x, (A t x).IsPositive)
    (X : ℝ → (x : M) → TangentSpace I x)
    (reaction : ℝ → (x : M) →
      (V x →L[ℝ] V x) → V x →L[ℝ] V x)
    (hreactionNull : ∀ t x,
      satisfiesNullEigenvectorCondition (reaction t x))
    (hevolution : ∀ t ∈ Ioo a b, ∀ x,
      HasDerivAt (fun s ↦ A s x)
        (rawBundleEndomorphismConnLap (I := I) (g t) (cov t)
            (fun y ↦ A t y) x +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V (cov t) (cov t) (fun y ↦ A t y) x (X t x) +
          reaction t x (A t x)) t) :
    ∀ t ∈ Ioo a b,
      (cov t).IsParallelSet {p : TotalSpace F V | A t p.1 p.2 = 0} := by
  have hrigidity := kernel_rigidity_of_constant_range_rank g cov hcov A hAspace q hrange
    (fun t ht x => (hApos t ht x).toLinearMap.isSymmetric) hApos X reaction hreactionNull
    (fun t ht x => (hevolution t ht x).differentiableAt)
    (fun t ht x => (hevolution t ht x).deriv)
  intro t ht
  let _ : ∀ x, FiniteDimensional ℝ (V x) :=
    fun x => VectorBundle.finiteDimensional ℝ F V x
  have hker : ∀ x, Module.finrank ℝ (A t x).ker = Module.finrank ℝ F - q := by
    intro x
    have hdim := ((trivializationAt F V x).linearEquivAt ℝ x
      (mem_baseSet_trivializationAt F V x)).finrank_eq
    have hsum := (A t x).toLinearMap.finrank_range_add_finrank_ker
    have hrank := hrange t ht x
    omega
  obtain ⟨K, _, hK⟩ := ContMDiffVectorSubbundle.exists_smooth_kernel
    (fun x => A t x) (A t).contMDiff _ hker
  have hinv : IsCovariantlyInvariantSubmoduleFamily (cov t) K.fiber := by
    have hKeq : K.fiber = fun x => (A t x).ker := funext hK
    rw [hKeq]
    exact hrigidity.2.1 t ht
  have hparallel := K.isParallelSet_of_covariantly_invariant
    (cov t) hinv (inferInstance : ContMDiffCovariantDerivative (cov t) ∞)
  convert hparallel using 1
  ext p
  change A t p.proj p.snd = 0 ↔ p.snd ∈ K.fiber p.proj
  rw [hK]
  rfl

end PositiveSystem
