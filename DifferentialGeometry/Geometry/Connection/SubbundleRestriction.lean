import DifferentialGeometry.Geometry.Connection.Subbundle
import Mathlib.Analysis.Normed.Module.ContinuousInverse
import DifferentialGeometry.Bundle.SmoothSubbundle.Hom

set_option autoImplicit false

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
variable [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
variable [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
variable [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
variable [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

namespace ContMDiffVectorSubbundle

private def fiberRetraction
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := ∞)) (x : M) :
    V x →L[ℝ] S.fiber x := by
  let _ : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
  let _ : T2Space (V x) := FiberBundle.t2Space F V x
  exact (ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional
    (f := (S.fiber x).subtypeL) (S.fiber x).injective_subtype).leftInverse

private theorem fiberRetraction_apply
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := ∞))
    (x : M) (v : S.fiber x) : S.fiberRetraction x (v : V x) = v := by
  let _ : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
  let _ : T2Space (V x) := FiberBundle.t2Space F V x
  exact (ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional
    (f := (S.fiber x).subtypeL) (S.fiber x).injective_subtype).leftInverse_leftInverse v

private def projectedCovariantDerivative
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := ∞))
    (cov : CovariantDerivative I F V) :
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    CovariantDerivative I (Fin S.rank → ℝ) (fun x => S.fiber x) := by
  letI := S.totalSpaceTopology
  letI := S.fiberBundle
  letI := S.vector_bundle
  letI := S.contMDiffVectorBundle
  let D := fun (σ : (x : M) → S.fiber x) (x : M) =>
    (S.fiberRetraction x).comp (cov (fun y => (σ y : V y)) x)
  have hinc {σ : (x : M) → S.fiber x} {x : M}
      (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, Fin S.rank → ℝ))
        (fun y => TotalSpace.mk' (Fin S.rank → ℝ) y (σ y)) x) :
      MDifferentiableAt I (I.prod 𝓘(ℝ, F))
        (fun y => TotalSpace.mk' F y (σ y : V y)) x :=
    ((S.contMDiff_subtypeVal (TotalSpace.mk' (Fin S.rank → ℝ) x (σ x))).mdifferentiableAt
      (by simp)).comp x hσ
  refine ⟨D, ?_, ?_⟩
  · intro σ τ x hσ hτ _
    apply ContinuousLinearMap.ext
    intro v
    have h := congrArg (fun A : TangentSpace I x →L[ℝ] V x => S.fiberRetraction x (A v))
      (cov.isCovariantDerivativeOnUniv.add (hinc hσ) (hinc hτ))
    rw [show (fun y => (σ y : V y)) + (fun y => (τ y : V y)) =
      (fun y => (σ y : V y) + (τ y : V y)) by rfl] at h
    simpa only [D, ContinuousLinearMap.comp_apply, add_apply, map_add,
      Pi.add_apply, Submodule.coe_add] using h
  · intro σ f x hσ hf _
    apply ContinuousLinearMap.ext
    intro v
    have h := congrArg (fun A : TangentSpace I x →L[ℝ] V x => S.fiberRetraction x (A v))
      (cov.isCovariantDerivativeOnUniv.leibniz (hinc hσ) hf)
    rw [Pi.smul_def'] at h
    simpa only [D, ContinuousLinearMap.comp_apply, add_apply,
      smul_apply, ContinuousLinearMap.smulRight_apply, map_add, map_smul,
      Pi.smul_apply', Submodule.coe_smul, fiberRetraction_apply] using h

private theorem projectedCovariantDerivative_apply
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := ∞))
    (cov : CovariantDerivative I F V) (σ : (x : M) → S.fiber x)
    (x : M) (v : TangentSpace I x) :
    S.projectedCovariantDerivative cov σ x v =
      S.fiberRetraction x (cov (fun y => (σ y : V y)) x v) := rfl

private theorem projectedCovariantDerivative_subtypeVal
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := ∞))
    (cov : CovariantDerivative I F V)
    (hcov : DifferentialGeometry.Geometry.Connection.IsCovariantlyInvariantSubmoduleFamily cov S.fiber) :
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    ∀ (σ : Cₛ^∞⟮I; Fin S.rank → ℝ, fun x => S.fiber x⟯) (x : M) (v : TangentSpace I x),
      (S.projectedCovariantDerivative cov σ x v : V x) =
        cov (fun y => (σ y : V y)) x v := by
  let _ := S.totalSpaceTopology
  let _ := S.fiberBundle
  intro σ x v
  let τ : Cₛ^∞⟮I; F, V⟯ :=
    ⟨fun y => (σ y : V y), (S.contMDiff_section_iff σ).mp σ.contMDiff⟩
  have hmem : cov τ x v ∈ S.fiber x :=
    hcov τ univ isOpen_univ (fun y _ => (σ y).property) x (mem_univ x) v
  have h := congrArg Subtype.val (S.fiberRetraction_apply x (⟨cov τ x v, hmem⟩ : S.fiber x))
  simpa only [projectedCovariantDerivative_apply, τ, ContMDiffSection.coeFn_mk] using h

private theorem exists_covariantDerivative_subtypeVal
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := ∞))
    (cov : CovariantDerivative I F V)
    (hcov : DifferentialGeometry.Geometry.Connection.IsCovariantlyInvariantSubmoduleFamily cov S.fiber) :
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    ∃ D : CovariantDerivative I (Fin S.rank → ℝ) (fun x => S.fiber x),
      ∀ (σ : Cₛ^∞⟮I; Fin S.rank → ℝ, fun x => S.fiber x⟯)
        (x : M) (v : TangentSpace I x),
        (D σ x v : V x) = cov (fun y => (σ y : V y)) x v := by
  let _ := S.totalSpaceTopology
  let _ := S.fiberBundle
  exact ⟨S.projectedCovariantDerivative cov, S.projectedCovariantDerivative_subtypeVal cov hcov⟩

end ContMDiffVectorSubbundle

namespace CovariantDerivative

def restrict
    (cov : CovariantDerivative I F V)
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := ∞))
    (hS : DifferentialGeometry.Geometry.Connection.IsCovariantlyInvariantSubmoduleFamily cov S.fiber) :
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    CovariantDerivative I (Fin S.rank → ℝ) (fun x => S.fiber x) :=
  (S.exists_covariantDerivative_subtypeVal cov hS).choose

theorem restrict_subtypeVal
    (cov : CovariantDerivative I F V)
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := ∞))
    (hS : DifferentialGeometry.Geometry.Connection.IsCovariantlyInvariantSubmoduleFamily cov S.fiber) :
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    ∀ (σ : Cₛ^∞⟮I; Fin S.rank → ℝ, fun x => S.fiber x⟯)
      (x : M) (v : TangentSpace I x),
      (cov.restrict S hS σ x v : V x) = cov (fun y => (σ y : V y)) x v :=
  (S.exists_covariantDerivative_subtypeVal cov hS).choose_spec

theorem subtypeL_comp_restrict
    (cov : CovariantDerivative I F V)
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := ∞))
    (hS : DifferentialGeometry.Geometry.Connection.IsCovariantlyInvariantSubmoduleFamily cov S.fiber) :
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    ∀ (σ : Cₛ^∞⟮I; Fin S.rank → ℝ, fun x => S.fiber x⟯) (x : M),
      (S.fiber x).subtypeL.comp (cov.restrict S hS σ x) =
        cov (fun y => (σ y : V y)) x := by
  let _ := S.totalSpaceTopology
  let _ := S.fiberBundle
  intro σ x
  apply ContinuousLinearMap.ext
  exact cov.restrict_subtypeVal S hS σ x

theorem contMDiff_restrict [IsManifold I ∞ M]
    (cov : CovariantDerivative I F V)
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := ∞))
    (hS : DifferentialGeometry.Geometry.Connection.IsCovariantlyInvariantSubmoduleFamily cov S.fiber)
    (hD : ContMDiffCovariantDerivative cov ∞) :
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    letI := S.vector_bundle
    ContMDiffCovariantDerivative (cov.restrict S hS) ∞ := by
  let _ := S.totalSpaceTopology
  let _ := S.fiberBundle
  let _ := S.vector_bundle
  let _ := S.contMDiffVectorBundle
  refine ⟨⟨?_⟩⟩
  intro σ hσ
  have hσ' : ContMDiff I (I.prod 𝓘(ℝ, Fin S.rank → ℝ)) ∞
      (fun x => TotalSpace.mk' (Fin S.rank → ℝ) x (σ x)) := by
    simpa [contMDiffOn_univ] using hσ
  let τ : Cₛ^∞⟮I; Fin S.rank → ℝ, fun x => S.fiber x⟯ := ⟨σ, hσ'⟩
  have hamb : ContMDiffOn I (I.prod 𝓘(ℝ, F)) (∞ + 1)
      (fun x => TotalSpace.mk' F x (σ x : V x)) univ := by
    simpa using ((S.contMDiff_section_iff σ).mp hσ').contMDiffOn
  have hA := hD.contMDiff.contMDiff hamb
  apply (S.contMDiffOn_hom_section_iff (cov.restrict S hS σ) univ).mpr
  apply hA.congr
  intro x hx
  congr 1
  apply ContinuousLinearMap.ext
  intro v
  exact cov.restrict_subtypeVal S hS τ x v

end CovariantDerivative
