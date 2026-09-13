import DifferentialGeometry.Topology.Homology.Cochains
import DifferentialGeometry.Topology.Homology.PathChains
import DifferentialGeometry.Topology.Homology.SimplexBoundary

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Module
open scoped Simplicial Topology

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

theorem integralSingularCoboundary_apply (i j : ℕ) (ψ : integralSingularCochain i X)
    (c : (integralSingularChains X).X j) :
    integralSingularCoboundary X i j ψ c = ψ ((integralSingularChains X).d j i c) := by
  simp only [integralSingularCoboundary, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply]

theorem integralSingularCocycle_boundary_apply (n : ℕ) (φ : integralSingularCochain (n + 1) X)
    (hφ : integralSingularCoboundary X (n + 1) (n + 2) φ = 0)
    (c : (integralSingularChains X).X (n + 2)) :
    φ ((integralSingularChains X).d (n + 2) (n + 1) c) = 0 := by
  have h := LinearMap.congr_fun hφ c
  simpa only [integralSingularCoboundary, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
    LinearMap.zero_apply] using h

def integralVertexPathCone [PathConnectedSpace X] (a : X) :
    (integralSingularChains X).X 0 →ₗ[ℤ] (integralSingularChains X).X 1 :=
  (integralSingularChainBasis 0 X).constr (M' := (integralSingularChains X).X 1) ℕ
    (fun σ => integralPathChain (PathConnectedSpace.somePath a (TopCat.toSSetObj₀Equiv σ)))

theorem integralVertexPathCone_simplex [PathConnectedSpace X] (a : X)
    (σ : integralSingularSimplex 0 X) :
    integralVertexPathCone a (integralSimplexChain 0 σ) =
      integralPathChain (PathConnectedSpace.somePath a (TopCat.toSSetObj₀Equiv σ)) := by
  rw [← integralSingularChainBasis_apply]
  exact (integralSingularChainBasis 0 X).constr_basis ℕ _ σ

def integralVertexCollapse (a : X) :
    (integralSingularChains X).X 0 →ₗ[ℤ] (integralSingularChains X).X 0 :=
  (integralSingularChainBasis 0 X).constr (M' := (integralSingularChains X).X 0) ℕ
    (fun _ => integralVertexChain a)

theorem integralVertexCollapse_simplex (a : X) (σ : integralSingularSimplex 0 X) :
    integralVertexCollapse a (integralSimplexChain 0 σ) = integralVertexChain a := by
  rw [← integralSingularChainBasis_apply]
  exact (integralSingularChainBasis 0 X).constr_basis ℕ _ σ

theorem integralVertexCollapse_boundary_simplex (a : X) (σ : integralSingularSimplex 1 X) :
    integralVertexCollapse a ((integralSingularChains X).d 1 0 (integralSimplexChain 1 σ)) = 0 := by
  rw [integralSimplexChain_boundary_one, map_sub, integralVertexCollapse_simplex,
    integralVertexCollapse_simplex, sub_self]

theorem integralVertexCollapse_boundary (a : X) :
    (integralVertexCollapse a).comp ((integralSingularChains X).d 1 0).hom = 0 := by
  apply (integralSingularChainBasis 1 X).ext
  intro σ
  rw [integralSingularChainBasis_apply, LinearMap.comp_apply, LinearMap.zero_apply]
  exact integralVertexCollapse_boundary_simplex a σ

theorem integralVertexPathCone_boundary [PathConnectedSpace X] (a : X) :
    ((integralSingularChains X).d 1 0).hom.comp (integralVertexPathCone a) =
      LinearMap.id - integralVertexCollapse a := by
  apply (integralSingularChainBasis 0 X).ext
  intro σ
  rw [integralSingularChainBasis_apply, LinearMap.comp_apply, LinearMap.sub_apply,
    LinearMap.id_apply, integralVertexPathCone_simplex, integralPathChain_boundary,
    integralVertexCollapse_simplex, integralVertexChain, Equiv.symm_apply_apply]

theorem integralCycleRetraction_mem [PathConnectedSpace X] (a : X)
    (c : (integralSingularChains X).X 1) :
    (integralSingularChains X).d 1 0
      (c - integralVertexPathCone a ((integralSingularChains X).d 1 0 c)) = 0 := by
  rw [map_sub]
  have h := LinearMap.congr_fun (integralVertexPathCone_boundary a)
    ((integralSingularChains X).d 1 0 c)
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply] at h
  have hb := LinearMap.congr_fun (integralVertexCollapse_boundary a) c
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hb
  rw [h, hb, sub_zero, sub_self]

def integralCycleRetraction [PathConnectedSpace X] (a : X) :
    (integralSingularChains X).X 1 →ₗ[ℤ] integralSingularCycles 0 X :=
  LinearMap.codRestrict (integralSingularCycles 0 X)
    (LinearMap.id - (integralVertexPathCone a).comp ((integralSingularChains X).d 1 0).hom)
    (fun c => by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
      exact integralCycleRetraction_mem a c)

theorem integralCycleRetraction_coe [PathConnectedSpace X] (a : X)
    (c : (integralSingularChains X).X 1) :
    ((integralCycleRetraction a c : integralSingularCycles 0 X) :
      (integralSingularChains X).X 1) =
      c - integralVertexPathCone a ((integralSingularChains X).d 1 0 c) := by
  rw [integralCycleRetraction, LinearMap.codRestrict_apply, LinearMap.sub_apply,
    LinearMap.id_apply, LinearMap.comp_apply]

theorem integralCycleRetraction_cycle [PathConnectedSpace X] (a : X)
    (z : integralSingularCycles 0 X) : integralCycleRetraction a z.val = z := by
  apply Subtype.ext
  rw [integralCycleRetraction_coe]
  have hz : (integralSingularChains X).d 1 0 z.val = 0 := z.property
  rw [hz, map_zero, sub_zero]

theorem integralCycleRetraction_boundary [PathConnectedSpace X] (a : X)
    (c : (integralSingularChains X).X 2) :
    integralCycleRetraction a ((integralSingularChains X).d 2 1 c) =
      integralSingularBoundaryToCycles 0 X c := by
  have hd : (integralSingularChains X).d 1 0 ((integralSingularChains X).d 2 1 c) = 0 := by
    have h := congrArg (fun f : (integralSingularChains X).X 2 ⟶
      (integralSingularChains X).X 0 => f c) ((integralSingularChains X).d_comp_d 2 1 0)
    change (integralSingularChains X).d 1 0 ((integralSingularChains X).d 2 1 c) = 0 at h
    exact h
  rw [integralCycleRetraction_cycle a ⟨(integralSingularChains X).d 2 1 c, hd⟩]
  rfl

theorem integralVertexPathCone_sub_cycle_mem [PathConnectedSpace X] (a : X)
    (c : (integralSingularChains X).X 1) :
    (integralSingularChains X).d 1 0
      (integralVertexPathCone a ((integralSingularChains X).d 1 0 c) - c) = 0 := by
  rw [map_sub]
  have h := LinearMap.congr_fun (integralVertexPathCone_boundary a)
    ((integralSingularChains X).d 1 0 c)
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply] at h
  have hb := LinearMap.congr_fun (integralVertexCollapse_boundary a) c
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hb
  rw [h, hb, sub_zero, sub_self]

def integralSingularCycleClass (n : ℕ) (X : Type u) [TopologicalSpace X]
    (z : integralSingularCycles n X) : integralSingularHomology (n + 1) X :=
  (integralSingularHomologyCycleEquiv n X).symm (Submodule.Quotient.mk z)

theorem integralSingularCycleClass_boundary (n : ℕ) (X : Type u) [TopologicalSpace X]
    (c : (integralSingularChains X).X (n + 2)) :
    integralSingularCycleClass n X (integralSingularBoundaryToCycles n X c) = 0 := by
  rw [integralSingularCycleClass, AddEquiv.symm_apply_eq, map_zero]
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨c, rfl⟩

theorem integralSingularCycleClass_surjective (n : ℕ) (X : Type u) [TopologicalSpace X]
    (y : integralSingularHomology (n + 1) X) :
    ∃ z : integralSingularCycles n X, integralSingularCycleClass n X z = y := by
  obtain ⟨z, hz⟩ := Submodule.mkQ_surjective (integralSingularBoundaryToCycles n X).range
    ((integralSingularHomologyCycleEquiv n X) y)
  refine ⟨z, ?_⟩
  rw [integralSingularCycleClass, Submodule.mkQ_apply] at *
  rw [hz, AddEquiv.symm_apply_apply]

theorem integralSingularCycleClass_eq_zero_iff (n : ℕ) (X : Type u) [TopologicalSpace X]
    (z : integralSingularCycles n X) :
    integralSingularCycleClass n X z = 0 ↔
      ∃ c : (integralSingularChains X).X (n + 2),
        integralSingularBoundaryToCycles n X c = z := by
  constructor
  · intro h
    rw [integralSingularCycleClass, AddEquiv.symm_apply_eq, map_zero] at h
    exact (Submodule.Quotient.mk_eq_zero _).mp h
  · rintro ⟨c, rfl⟩
    exact integralSingularCycleClass_boundary n X c

def integralCocycleEvaluationOnCycles (n : ℕ) :
    integralSingularCochain (n + 1) X →ₗ[ℤ]
      (integralSingularCycles n X →ₗ[ℤ] ULift.{u} ℤ) :=
  LinearMap.lcomp (S := ℤ) (N := ULift.{u} ℤ) (M := integralSingularCycles n X)
    (M₂ := (integralSingularChains X).X (n + 1)) (Submodule.subtype (integralSingularCycles n X))

def integralCocycleEvaluation (n : ℕ) :
    integralSingularCochain (n + 1) X →ₗ[ℤ] (integralSingularCycles n X →ₗ[ℤ] ℤ) :=
  ((LinearEquiv.arrowCongr (LinearEquiv.refl ℤ (integralSingularCycles n X))
    (ULift.moduleEquiv (R := ℤ) (M := ℤ))).toLinearMap).comp (integralCocycleEvaluationOnCycles n)

theorem integralCocycleEvaluationOnCycles_apply (n : ℕ) (φ : integralSingularCochain (n + 1) X)
    (z : integralSingularCycles n X) :
    integralCocycleEvaluationOnCycles n φ z = φ z.val := rfl

theorem integralCocycleEvaluation_apply (n : ℕ) (φ : integralSingularCochain (n + 1) X)
    (z : integralSingularCycles n X) :
    integralCocycleEvaluation n φ z = ULift.moduleEquiv (R := ℤ) (M := ℤ) (φ z.val) := by
  rw [integralCocycleEvaluation, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.arrowCongr_apply, LinearEquiv.refl_symm, LinearEquiv.refl_apply,
    integralCocycleEvaluationOnCycles_apply, ULift.moduleEquiv_apply]

theorem integralSingularBoundaryToCycles_coe (n : ℕ) (c : (integralSingularChains X).X (n + 2)) :
    ((integralSingularBoundaryToCycles n X c : integralSingularCycles n X) :
      (integralSingularChains X).X (n + 1)) =
      (integralSingularChains X).d (n + 2) (n + 1) c := rfl

theorem integralCocycleEvaluation_boundary (n : ℕ) (φ : integralSingularCochain (n + 1) X)
    (hφ : integralSingularCoboundary X (n + 1) (n + 2) φ = 0)
    (c : (integralSingularChains X).X (n + 2)) :
    integralCocycleEvaluation n φ (integralSingularBoundaryToCycles n X c) = 0 := by
  rw [integralCocycleEvaluation_apply, integralSingularBoundaryToCycles_coe,
    integralSingularCocycle_boundary_apply n φ hφ c, map_zero]

theorem integralCoboundary_evaluation_apply (ψ : integralSingularCochain 0 X)
    (z : integralSingularCycles 0 X) :
    integralCocycleEvaluation 0 (integralSingularCoboundary X 0 1 ψ) z = 0 := by
  rw [integralCocycleEvaluation_apply]
  have hz : (integralSingularChains X).d 1 0 z.val = 0 := z.property
  rw [integralSingularCoboundary_apply, hz, map_zero, map_zero]

def integralCocycleOfCycleFunctional [PathConnectedSpace X] (a : X)
    (g : integralSingularCycles 0 X →ₗ[ℤ] ℤ) : integralSingularCochain 1 X :=
  (ULift.moduleEquiv (R := ℤ) (M := ℤ)).symm.toLinearMap.comp
    (g.comp (integralCycleRetraction a))

theorem integralCocycleOfCycleFunctional_apply [PathConnectedSpace X] (a : X)
    (g : integralSingularCycles 0 X →ₗ[ℤ] ℤ) (c : (integralSingularChains X).X 1) :
    integralCocycleOfCycleFunctional a g c =
      (ULift.moduleEquiv (R := ℤ) (M := ℤ)).symm (g (integralCycleRetraction a c)) := by
  rw [integralCocycleOfCycleFunctional, LinearMap.comp_apply, LinearMap.comp_apply]
  rfl

theorem integralCocycleOfCycleFunctional_cocycle [PathConnectedSpace X] (a : X)
    (g : integralSingularCycles 0 X →ₗ[ℤ] ℤ)
    (hg : ∀ c : (integralSingularChains X).X 2,
      g (integralSingularBoundaryToCycles 0 X c) = 0) :
    integralSingularCoboundary X 1 2 (integralCocycleOfCycleFunctional a g) = 0 := by
  apply LinearMap.ext
  intro c
  rw [integralSingularCoboundary_apply, integralCocycleOfCycleFunctional_apply,
    integralCycleRetraction_boundary, hg, map_zero, LinearMap.zero_apply]

theorem integralCocycleEvaluation_cycleFunctional [PathConnectedSpace X] (a : X)
    (g : integralSingularCycles 0 X →ₗ[ℤ] ℤ) (z : integralSingularCycles 0 X) :
    integralCocycleEvaluation 0 (integralCocycleOfCycleFunctional a g) z = g z := by
  rw [integralCocycleEvaluation_apply, integralCocycleOfCycleFunctional_apply,
    integralCycleRetraction_cycle]
  simp only [ULift.moduleEquiv_apply, ULift.moduleEquiv_symm_apply]

theorem exists_cocycle_evaluation_eq_of_forall_boundary_eq_zero [PathConnectedSpace X]
    (g : integralSingularCycles 0 X →ₗ[ℤ] ℤ)
    (hg : ∀ c : (integralSingularChains X).X 2,
      g (integralSingularBoundaryToCycles 0 X c) = 0) :
    ∃ φ : integralSingularCochain 1 X, integralSingularCoboundary X 1 2 φ = 0 ∧
      ∀ z : integralSingularCycles 0 X, integralCocycleEvaluation 0 φ z = g z := by
  let a : X := Classical.choice (inferInstance : Nonempty X)
  exact ⟨integralCocycleOfCycleFunctional a g,
    integralCocycleOfCycleFunctional_cocycle a g hg,
    integralCocycleEvaluation_cycleFunctional a g⟩

theorem integralCocycle_eq_coboundary_of_evaluation_eq_zero [PathConnectedSpace X]
    (φ : integralSingularCochain 1 X)
    (h : ∀ z : integralSingularCycles 0 X, integralCocycleEvaluation 0 φ z = 0) :
    ∃ ψ : integralSingularCochain 0 X, integralSingularCoboundary X 0 1 ψ = φ := by
  let a : X := Classical.choice (inferInstance : Nonempty X)
  refine ⟨φ.comp (integralVertexPathCone a), ?_⟩
  apply LinearMap.ext
  intro c
  rw [integralSingularCoboundary_apply, LinearMap.comp_apply]
  have hz := h ⟨integralVertexPathCone a ((integralSingularChains X).d 1 0 c) - c,
    integralVertexPathCone_sub_cycle_mem a c⟩
  have hz' : φ (integralVertexPathCone a ((integralSingularChains X).d 1 0 c) - c) = 0 := by
    refine (ULift.moduleEquiv (R := ℤ) (M := ℤ)).injective ?_
    simpa only [integralCocycleEvaluation_apply, Subtype.coe_mk, map_zero] using hz
  rw [map_sub, sub_eq_zero] at hz'
  exact hz'

theorem exists_cycle_evaluation_ne_zero_of_not_coboundary [PathConnectedSpace X]
    (φ : integralSingularCochain 1 X)
    (hφ : ¬ ∃ ψ : integralSingularCochain 0 X, integralSingularCoboundary X 0 1 ψ = φ) :
    ∃ z : integralSingularCycles 0 X, integralCocycleEvaluation 0 φ z ≠ 0 := by
  by_contra h
  exact hφ (integralCocycle_eq_coboundary_of_evaluation_eq_zero φ
    (fun z => by by_contra hz; exact h ⟨z, hz⟩))

theorem eq_zero_of_subsingleton_cohomologyOne [PathConnectedSpace X]
    (h : Subsingleton (integralSingularCohomology 1 X))
    (g : integralSingularCycles 0 X →ₗ[ℤ] ℤ)
    (hg : ∀ c : (integralSingularChains X).X 2,
      g (integralSingularBoundaryToCycles 0 X c) = 0) : g = 0 := by
  let a : X := Classical.choice (inferInstance : Nonempty X)
  obtain ⟨ψ, hψ⟩ := (integralSingularCohomology_one_vanishing_iff X).mp h
    (integralCocycleOfCycleFunctional a g)
    (integralCocycleOfCycleFunctional_cocycle a g hg)
  apply LinearMap.ext
  intro z
  rw [LinearMap.zero_apply, ← integralCocycleEvaluation_cycleFunctional a g z, ← hψ]
  exact integralCoboundary_evaluation_apply ψ z

theorem noZeroSMulDivisors_homologyOneDual (n : ℕ) :
    NoZeroSMulDivisors ℤ (integralSingularHomology (n + 1) X →ₗ[ℤ] ℤ) where
  eq_zero_or_eq_zero_of_smul_eq_zero {c f} h := by
    rcases smul_eq_zero.mp h with hc | hf
    · exact Or.inl hc
    · refine Or.inr ?_
      apply LinearMap.ext
      intro y
      have hy := LinearMap.congr_fun hf y
      simpa only [LinearMap.smul_apply, LinearMap.zero_apply] using hy

end DifferentialGeometry.Topology
