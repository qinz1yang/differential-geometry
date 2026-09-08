import DifferentialGeometry.Geometry.Connection.SubbundleRestriction
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Hom

set_option autoImplicit false
noncomputable section
open Bundle Set
open scoped Manifold ContDiff
namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

theorem homBundleCovariantDerivativeGen_subtypeL_restrict
    (cov : CovariantDerivative I F V)
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := ∞))
    (hS : DifferentialGeometry.Geometry.Connection.IsCovariantlyInvariantSubmoduleFamily cov S.fiber) :
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    letI := S.vector_bundle
    let _ := S.contMDiffVectorBundle
    DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen I M (Fin S.rank → ℝ)
      (fun x => S.fiber x) F V (cov.restrict S hS) cov
      (fun x => (S.fiber x).subtypeL) = 0 := by
  let _ := S.totalSpaceTopology
  let _ := S.fiberBundle
  let _ := S.vector_bundle
  let _ := S.contMDiffVectorBundle
  funext x
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro u
  obtain ⟨σ, hσ⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := Fin S.rank → ℝ) (V := fun x => S.fiber x) (n := (⊤ : ℕ∞)) x u
  have h := DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen_apply
    I M (Fin S.rank → ℝ) (fun x => S.fiber x) F V
    (cov.restrict S hS) cov
    (⟨fun y => (S.fiber y).subtypeL,
      ContMDiff.clm_bundle_of_map (φ := fun y => (S.fiber y).subtypeL) S.contMDiff_subtypeVal⟩ :
      Cₛ^∞⟮I; (Fin S.rank → ℝ) →L[ℝ] F,
        (fun x => S.fiber x →L[ℝ] V x)⟯)
    σ x v
  rw [hσ] at h
  have hr := cov.restrict_subtypeVal S hS σ x v
  change (S.fiber x).subtypeL (cov.restrict S hS σ x v) =
    cov (fun y => (S.fiber y).subtypeL (σ y)) x v at hr
  change _ = 0
  have h' :
      ((DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen I M (Fin S.rank → ℝ)
          (fun x => S.fiber x) F V (cov.restrict S hS) cov
          (fun y => (S.fiber y).subtypeL) x v) u) =
        cov (fun y => (S.fiber y).subtypeL (σ y)) x v -
          (S.fiber x).subtypeL (cov.restrict S hS σ x v) := by
    convert h using 1 <;> rfl
  rw [h', hr, sub_self]

end CovariantDerivative

namespace ContMDiffVectorSubbundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]

theorem isParallelSet_of_covariantly_invariant
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := ∞))
    (cov : CovariantDerivative I F V)
    (hS : DifferentialGeometry.Geometry.Connection.IsCovariantlyInvariantSubmoduleFamily cov S.fiber)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞) :
    cov.IsParallelSet {p : TotalSpace F V | p.2 ∈ S.fiber p.1} := by
  let _ := S.totalSpaceTopology
  let _ := S.fiberBundle
  let _ := S.vector_bundle
  let _ := S.contMDiffVectorBundle
  have hparallel := CovariantDerivative.homBundleCovariantDerivativeGen_subtypeL_restrict
    cov S hS
  have hinc := ContMDiff.clm_bundle_of_map
    (φ := fun x => (S.fiber x).subtypeL) S.contMDiff_subtypeVal
  have hwhole : (cov.restrict S hS).IsParallelSet
      (Set.univ : Set (TotalSpace (Fin S.rank → ℝ) (fun x => S.fiber x))) := by
    refine ⟨?_⟩
    intro a b t₀ γ Z ht₀ hγ hZ hp hi t ht
    exact Set.mem_univ _
  have h := hwhole.image (cov.contMDiff_restrict S hS hcov) hcov
    (fun x => (S.fiber x).subtypeL) (hinc.mdifferentiable (by simp)) hparallel
  convert h using 1
  ext p
  constructor
  · intro hp
    exact ⟨⟨p.1, ⟨p.2, hp⟩⟩, Set.mem_univ _, rfl⟩
  · rintro ⟨⟨x, v⟩, _, rfl⟩
    exact v.2

end ContMDiffVectorSubbundle
