import DifferentialGeometry.Geometry.Connection.SubbundleRestriction
import DifferentialGeometry.Geometry.Connection.Hessian

set_option autoImplicit false

noncomputable section

open Bundle
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

namespace CovariantDerivative

theorem restrict_hessian_subtypeVal
    (cov : CovariantDerivative I F V) [hcov : ContMDiffCovariantDerivative cov ∞]
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := ∞))
    (hS : DifferentialGeometry.Geometry.Connection.IsCovariantlyInvariantSubmoduleFamily cov S.fiber)
    (base : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    letI := S.vector_bundle
    ∀ (σ : Cₛ^∞⟮I; Fin S.rank → ℝ, fun x => S.fiber x⟯)
      (x : M) (X Y : TangentSpace I x),
      ((cov.restrict S hS).hessian base σ x X Y : V x) =
        cov.hessian base (fun y => (σ y : V y)) x X Y := by
  let _ := S.totalSpaceTopology
  let _ := S.fiberBundle
  let _ := S.vector_bundle
  let _ := S.contMDiffVectorBundle
  intro σ x X Y
  let D := cov.restrict S hS
  have hD : ContMDiffCovariantDerivative D ∞ := cov.contMDiff_restrict S hS hcov
  let τ : Cₛ^∞⟮I; F, V⟯ :=
    ⟨fun y => (σ y : V y), (S.contMDiff_section_iff σ).mp σ.contMDiff⟩
  have hDσ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] (Fin S.rank → ℝ))) ∞
      (fun y => TotalSpace.mk' (E →L[ℝ] (Fin S.rank → ℝ)) y (D σ y)) :=
    contMDiffOn_univ.mp (hD.contMDiff.contMDiff (by simpa using σ.contMDiff.contMDiffOn))
  have hDτ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun y => TotalSpace.mk' (E →L[ℝ] F) y (cov τ y)) :=
    contMDiffOn_univ.mp (hcov.contMDiff.contMDiff (by simpa using τ.contMDiff.contMDiffOn))
  obtain ⟨Z, hZ⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x Y
  let η : Cₛ^∞⟮I; Fin S.rank → ℝ, fun x => S.fiber x⟯ :=
    ⟨fun y => D σ y (Z y), hDσ.clm_bundle_apply Z.contMDiff⟩
  have hη : (fun y => (η y : V y)) = fun y => cov τ y (Z y) := by
    funext y
    exact cov.restrict_subtypeVal S hS σ y (Z y)
  change (D.hessian base σ x X Y : V x) = cov.hessian base τ x X Y
  rw [← hZ, D.hessian_apply base (hDσ.mdifferentiableAt (by simp)) Z.mdifferentiableAt,
    cov.hessian_apply base (hDτ.mdifferentiableAt (by simp)) Z.mdifferentiableAt,
    Submodule.coe_sub]
  change (D η x X : V x) - (D σ x (base Z x X) : V x) = _
  rw [cov.restrict_subtypeVal S hS η, cov.restrict_subtypeVal S hS σ, hη]
  rfl

end CovariantDerivative
