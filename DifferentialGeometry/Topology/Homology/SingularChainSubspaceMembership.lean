import DifferentialGeometry.Topology.Homology.CollapseQuotientComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CubeTetrahedralChainBridge

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set Module
open scoped Topology Simplicial

universe u

namespace DifferentialGeometry.Topology

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {X : Type u} [TopologicalSpace X]

private theorem moduleCat_sum_apply {ι : Type*} {M N : ModuleCat.{u} ℤ} (s : Finset ι)
    (f : ι → (M ⟶ N)) (x : M) : s.sum f x = s.sum (fun i => f i x) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha]

theorem integralSimplexChain_symm_mem_chainsIn (n : ℕ) (A : Set X)
    (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) (hσ : ∀ t, σ t ∈ A) :
    integralSimplexChain n ((integralSingularSimplexEquiv n X).symm σ) ∈
      integralSingularChainsIn n A := by
  refine Submodule.subset_span ⟨(integralSingularSimplexEquiv n X).symm σ, ?_, rfl⟩
  rintro _ ⟨t, rfl⟩
  rw [Equiv.apply_symm_apply]
  exact hσ t

theorem singularSimplexChain_apply_one_eq_integralSimplexChain (n : ℕ)
    (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    singularSimplexChain σ (ULift.up (1 : ℤ)) =
      integralSimplexChain n ((integralSingularSimplexEquiv n X).symm σ) := rfl

theorem integralCoefficients_smul_apply {N : ModuleCat.{0} ℤ} (c : ℤ)
    (f : integralCoefficients.{0} ⟶ N) (x : integralCoefficients.{0}) :
    (c • f) x = c • f x := by
  simp only [ModuleCat.hom_smul, LinearMap.smul_apply]

theorem not_bijective_zsmul_integralRelativeHomology_three_singleton_cube
    (b : Fin 3 → unitInterval)
    (x : integralRelativeHomology 3 ({b} : Set (Fin 3 → unitInterval))) :
    ¬ Function.Bijective fun z : ℤ => z • x := by
  intro h
  have h0 : x = 0 :=
    @Subsingleton.elim _ (subsingleton_integralRelativeHomology_three_singleton_cube b) x 0
  have hz : (0 : ℤ) • x = (1 : ℤ) • x := by
    rw [h0]
    simp
  exact zero_ne_one (h.1 hz)

end DifferentialGeometry.Topology
