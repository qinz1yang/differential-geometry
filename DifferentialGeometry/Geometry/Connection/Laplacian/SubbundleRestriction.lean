import DifferentialGeometry.Geometry.Connection.SubbundleRestriction
import DifferentialGeometry.Geometry.Connection.Laplacian.VectorBundle

set_option autoImplicit false

noncomputable section

open Bundle CovariantDerivative
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

namespace DifferentialGeometry.Geometry.Connection

theorem rawBundleConnLap_restrict_subtypeVal
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I F V) [hcov : ContMDiffCovariantDerivative cov ∞]
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := ∞))
    (hS : IsCovariantlyInvariantSubmoduleFamily cov S.fiber) :
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    ∀ (σ : Cₛ^∞⟮I; Fin S.rank → ℝ, fun x => S.fiber x⟯) (x : M),
      (rawBundleConnLap g (cov.restrict S hS) σ x : V x) =
        rawBundleConnLap g cov (fun y => (σ y : V y)) x := by
  let _ := S.totalSpaceTopology
  let _ := S.fiberBundle
  let _ := S.vector_bundle
  let _ := S.contMDiffVectorBundle
  intro σ x
  have hD := cov.contMDiff_restrict S hS hcov
  have hDσ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] (Fin S.rank → ℝ))) ∞
      (fun y => TotalSpace.mk' (E →L[ℝ] (Fin S.rank → ℝ)) y (cov.restrict S hS σ y)) :=
    contMDiffOn_univ.mp (hD.contMDiff.contMDiff (by simpa using σ.contMDiff.contMDiffOn))
  rw [rawBundleConnLap_def, rawBundleConnLap_def, Submodule.coe_sum]
  apply Finset.sum_congr rfl
  intro i hi
  let _ : NeZero (Module.finrank ℝ E) :=
    ⟨Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩
  let Z : Cₛ^∞⟮I; E, TangentSpace I⟯ :=
    ⟨smoothOrthoFrame g x i, smoothOrthoFrame_smooth g x i⟩
  let η : Cₛ^∞⟮I; Fin S.rank → ℝ, fun x => S.fiber x⟯ :=
    ⟨fun y => cov.restrict S hS σ y (Z y), hDσ.clm_bundle_apply Z.contMDiff⟩
  have hη : (fun y => (η y : V y)) =
      fun y => cov (fun z => (σ z : V z)) y (Z y) := by
    funext y
    exact cov.restrict_subtypeVal S hS σ y (Z y)
  rw [Submodule.coe_sub]
  change (cov.restrict S hS η x (Z x) : V x) -
    (cov.restrict S hS σ x (LeviCivita g Z x (Z x)) : V x) = _
  rw [cov.restrict_subtypeVal S hS η, cov.restrict_subtypeVal S hS σ, hη]
  rfl

end DifferentialGeometry.Geometry.Connection
