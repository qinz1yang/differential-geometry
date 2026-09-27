import DifferentialGeometry.Analysis.Parabolic.SelfAdjointEvolution
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.ExteriorPower

set_option autoImplicit false

noncomputable section

open Bundle
open DifferentialGeometry DifferentialGeometry.Geometry.Connection
open scoped Bundle Manifold ContDiff

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

theorem IsMetricCompatible.hasDerivWithinAt_exteriorPower_selfAdjoint
    {cov : CovariantDerivative I F V}
    [ContMDiffCovariantDerivative cov ∞] (hc : cov.IsMetricCompatible)
    (g : SmoothRiemannianMetric I M) (k : ℕ) :
    letI : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
    letI := Bundle.ExteriorPower.totalSpaceTopology F V k
    letI := Bundle.ExteriorPower.fiberBundle F V k
    letI := Bundle.ExteriorPower.vector_bundle F V k
    letI := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V k
    letI := Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := ∞) F V k
    let S := selfAdjointSubbundle (I := I) (F := ⋀[ℝ]^k F)
      (V := fun y => ⋀[ℝ]^k (V y)) (n := ∞)
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    ∀ (A : ℝ → ∀ y, S.fiber y) (t : ℝ),
      ContMDiff I (I.prod 𝓘(ℝ, Fin S.rank → ℝ)) ∞
        (fun y => TotalSpace.mk' (Fin S.rank → ℝ) y (A t y)) →
      ∀ (x : M) (Q : S.fiber x) (J : Set ℝ),
      HasDerivWithinAt (fun s => (A s x : (⋀[ℝ]^k (V x)) →L[ℝ] ⋀[ℝ]^k (V x)))
        (rawBundleEndomorphismConnLap g (cov.exteriorPower k)
          (fun y => (A t y : (⋀[ℝ]^k (V y)) →L[ℝ] ⋀[ℝ]^k (V y))) x +
          (Q : (⋀[ℝ]^k (V x)) →L[ℝ] ⋀[ℝ]^k (V x))) J t →
      HasDerivWithinAt (fun s => A s x)
        (rawBundleConnLap (F := Fin S.rank → ℝ) (V := fun y => S.fiber y) g
          ((cov.exteriorPower k).selfAdjoint (F := ⋀[ℝ]^k F)
            (V := fun y => ⋀[ℝ]^k (V y)) (hc.exteriorPower k)) (A t) x + Q) J t := by
  dsimp only
  let : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
  let := Bundle.ExteriorPower.totalSpaceTopology F V k
  let := Bundle.ExteriorPower.fiberBundle F V k
  let := Bundle.ExteriorPower.vector_bundle F V k
  let := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V k
  let := Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := ∞) F V k
  let : ContMDiffCovariantDerivative (cov.exteriorPower k) ∞ := cov.exteriorPower_contMDiff k
  exact hasDerivWithinAt_selfAdjoint_of_subtype
    (F := ⋀[ℝ]^k F) (V := fun y => ⋀[ℝ]^k (V y)) g (cov.exteriorPower k)
    (hc.exteriorPower k)

end CovariantDerivative
