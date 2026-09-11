import DifferentialGeometry.Analysis.Calculus.InjectiveDerivative
import DifferentialGeometry.Geometry.Connection.Laplacian.SelfAdjointRestriction

set_option autoImplicit false

noncomputable section

open Bundle
open DifferentialGeometry DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

theorem hasDerivWithinAt_selfAdjoint_of_subtype
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (hcov : cov.IsMetricCompatible) :
    let S := selfAdjointSubbundle (I := I) (F := F) (V := V) (n := ∞)
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    ∀ (A : ℝ → ∀ y, S.fiber y) (t : ℝ),
      ContMDiff I (I.prod 𝓘(ℝ, Fin S.rank → ℝ)) ∞
        (fun y => TotalSpace.mk' (Fin S.rank → ℝ) y (A t y)) →
      ∀ (x : M) (Q : S.fiber x) (J : Set ℝ),
      HasDerivWithinAt (fun s => (A s x : V x →L[ℝ] V x))
        (rawBundleEndomorphismConnLap g cov (fun y => (A t y : V y →L[ℝ] V y)) x +
          (Q : V x →L[ℝ] V x)) J t →
      HasDerivWithinAt (fun s => A s x)
        (rawBundleConnLap g (cov.selfAdjoint hcov) (A t) x + Q) J t := by
  dsimp only
  let S := selfAdjointSubbundle (I := I) (F := F) (V := V) (n := ∞)
  let := S.totalSpaceTopology
  let := S.fiberBundle
  intro A t hA x Q J hd
  let : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
  let At : Cₛ^∞⟮I; Fin S.rank → ℝ, fun y => S.fiber y⟯ := ⟨A t, hA⟩
  have hlap := rawBundleConnLap_selfAdjoint_subtypeVal g cov hcov At x
  apply (S.fiber x).subtypeL.hasDerivWithinAt_of_injective Subtype.val_injective
  convert hd using 1 <;> try rfl
  rw [map_add]
  exact congrArg (fun R : V x →L[ℝ] V x => R + (Q : V x →L[ℝ] V x)) hlap

end CovariantDerivative
