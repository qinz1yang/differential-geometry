import DifferentialGeometry.Geometry.Connection.SubbundlePullback
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.ExteriorPower
import DifferentialGeometry.Geometry.Connection.TensorNabla.AlternatingEndomorphismPullback

noncomputable section

open Bundle
open scoped Manifold ContDiff RealInnerProductSpace

namespace DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

theorem isCovariantlyInvariantSubmoduleFamily_musical_iff
    (cov : CovariantDerivative I F V) (hcov : cov.IsMetricCompatible)
    (k : ℕ) (S : ∀ x, Submodule ℝ (⋀[ℝ]^k (V x))) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := Bundle.ExteriorPower.totalSpaceTopology F V k
    letI := Bundle.ExteriorPower.fiberBundle F V k
    letI := Bundle.ExteriorPower.vector_bundle F V k
    letI := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V k
    IsCovariantlyInvariantSubmoduleFamily (CovariantDerivative.alternating cov k)
      (fun x => (S x).map (exteriorPower.musicalEquiv (E := V x) k).toLinearMap) ↔
    IsCovariantlyInvariantSubmoduleFamily (cov.exteriorPower k) S := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := Bundle.ExteriorPower.totalSpaceTopology F V k
  let := Bundle.ExteriorPower.fiberBundle F V k
  let := Bundle.ExteriorPower.vector_bundle F V k
  let := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V k
  have hmus := Bundle.ExteriorPower.contMDiff_musicalEquiv (IB := I) (n := ∞) F V k
  apply isCovariantlyInvariantSubmoduleFamily_map_iff
    (fun x => exteriorPower.musicalEquiv (E := V x) k) hmus
    (cov.exteriorPower k) (CovariantDerivative.alternating cov k) ?_ S
  intro u x X
  exact (hcov.exteriorPower_musicalEquiv k u x X u.mdifferentiableAt).symm

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {W : M → Type*} [TopologicalSpace (TotalSpace G W)]
  [∀ x, NormedAddCommGroup (W x)] [∀ x, NormedSpace ℝ (W x)]
  [FiberBundle G W] [VectorBundle ℝ G W] [ContMDiffVectorBundle ∞ G W I]

theorem isCovariantlyInvariantSubmoduleFamily_musical_pullback
    (cov : CovariantDerivative I G W)
    (ι : ∀ x, V x ≃L[ℝ] W x)
    (hι : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] G)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] G) x (ι x).toContinuousLinearMap))
    (k : ℕ) (S : ∀ x, Submodule ℝ (⋀[ℝ]^k (V x))) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := Bundle.ExteriorPower.totalSpaceTopology F V k
    letI := Bundle.ExteriorPower.fiberBundle F V k
    letI := Bundle.ExteriorPower.vector_bundle F V k
    letI := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V k
    let D := CovariantDerivative.pullbackFiberwiseLinearEquiv
      (fun x => (ι x).toLinearEquiv) (hι.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).clm_bundle_map
      cov
    D.IsMetricCompatible →
    IsCovariantlyInvariantSubmoduleFamily (D.exteriorPower k) S →
    IsCovariantlyInvariantSubmoduleFamily (CovariantDerivative.alternating cov k)
      (fun x => (S x).map
        (((exteriorPower.musicalEquiv (E := V x) k).trans
          ((ι x).continuousAlternatingMapCongrLeft (ι := Fin k))).toLinearMap)) := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := Bundle.ExteriorPower.totalSpaceTopology F V k
  let := Bundle.ExteriorPower.fiberBundle F V k
  let := Bundle.ExteriorPower.vector_bundle F V k
  let := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V k
  intro D hD hS
  let e := fun x => (exteriorPower.musicalEquiv (E := V x) k).trans
    ((ι x).continuousAlternatingMapCongrLeft (ι := Fin k))
  have hmus := Bundle.ExteriorPower.contMDiff_musicalEquiv (IB := I) (n := ∞) F V k
  have hcongr := ContMDiff.alternating_bundle_congrLeft ι hι k
  have he : ContMDiff I (I.prod 𝓘(ℝ, (⋀[ℝ]^k F) →L[ℝ] G [⋀^Fin k]→L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' ((⋀[ℝ]^k F) →L[ℝ] G [⋀^Fin k]→L[ℝ] ℝ) x
        (e x).toContinuousLinearMap) := hcongr.clm_bundle_comp hmus
  apply isCovariantlyInvariantSubmoduleFamily_map e he (D.exteriorPower k)
    (CovariantDerivative.alternating cov k) ?_ S hS
  intro u x X
  have hmu := hmus.clm_bundle_apply u.contMDiff
  have h := CovariantDerivative.alternating_congrLeft ι
    (hι.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)) cov k
    (hmu.mdifferentiableAt (by simp)) X
  have hm := hD.exteriorPower_musicalEquiv k u x X u.mdifferentiableAt
  exact h.trans (congrArg ((ι x).continuousAlternatingMapCongrLeft (ι := Fin k)) hm.symm)

end DifferentialGeometry.Geometry.Connection
