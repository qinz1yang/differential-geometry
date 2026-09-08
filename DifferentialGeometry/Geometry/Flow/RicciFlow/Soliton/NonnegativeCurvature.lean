import DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.Solution
import DifferentialGeometry.Geometry.Curvature.AlgebraicCurvatureOperatorConeMetric

import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.CurvatureRank
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.CurvatureKernel
import DifferentialGeometry.Geometry.Curvature.DimensionThree.ExteriorRank

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff BigOperators
namespace DifferentialGeometry.PDE.RicciFlow.Soliton
open DifferentialGeometry.Geometry Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

theorem canonicalMetric_curvatureOperator_nonnegative
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯)
    (sigma : ℝ) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton g f sigma)
    (hcone : ∀ y : M, metricAlgebraicCurvatureTensorAt g y ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    {t : ℝ} (ht : t ∈ canonicalTimeDomain sigma) (x : M) :
    metricAlgebraicCurvatureTensorAt (canonicalMetric g f sigma hcomplete hsol ht) x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) := by
  let Phi := canonicalFlowDiffeomorph g f sigma hcomplete hsol (canonicalFlowParameter sigma t)
  rw [metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff]
  intro n c v w
  have hbase := (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
    g (Phi x)).mp (hcone (Phi x)) n c
      (fun i => mfderiv I I Phi x (v i)) (fun i => mfderiv I I Phi x (w i))
  have hRm (i j : Fin n) :
      metricRm04StdAt (canonicalMetric g f sigma hcomplete hsol ht) x
        (v i) (w i) (w j) (v j) =
      (1 - sigma * t) * metricRm04StdAt g (Phi x)
        (mfderiv I I Phi x (v i)) (mfderiv I I Phi x (w i))
        (mfderiv I I Phi x (w j)) (mfderiv I I Phi x (v j)) := by
    exact canonicalMetric_metricRm04 g f sigma hcomplete hsol ht x
      (![v i, w i, w j, v j])
  simp_rw [hRm]
  have heq : (∑ i, ∑ j, c i * c j * ((1 - sigma * t) *
      metricRm04StdAt g (Phi x) (mfderiv I I Phi x (v i)) (mfderiv I I Phi x (w i))
        (mfderiv I I Phi x (w j)) (mfderiv I I Phi x (v j)))) =
      (1 - sigma * t) * (∑ i, ∑ j, c i * c j *
      metricRm04StdAt g (Phi x) (mfderiv I I Phi x (v i)) (mfderiv I I Phi x (w i))
        (mfderiv I I Phi x (w j)) (mfderiv I I Phi x (v j))) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [heq]
  exact mul_nonneg (mem_canonicalTimeDomain_iff.mp ht).le hbase

end DifferentialGeometry.PDE.RicciFlow.Soliton

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

namespace DifferentialGeometry.Geometry

open Curvature Curvature.DimensionThree
open DifferentialGeometry.PDE.RicciFlow
  (IsSolutionOn
    curvatureOperatorImageAt_finrank_eq_at_later_time
    curvatureOperatorImageAt_finrank_trichotomy_at_later_time)
open DifferentialGeometry.PDE.RicciFlow.Soliton
  (zero_mem_canonicalTimeDomain canonicalMetricFamily canonicalMetricFamily_eq canonicalMetric_curvatureOperator_nonnegative canonicalTimeDomain canonicalSolutionOn canonicalSolutionOn_metric_zero
    canonicalSolutionOn_isSolutionOn canonicalSolutionOn_complete)

private theorem exists_nonnegative_canonical_slab
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) (σ : ℝ)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f σ)
    (hcone : ∀ y : M, metricAlgebraicCurvatureTensorAt g y ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    ∃ (D : RealTimeInterval) (S : DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D),
      IsSolutionOn S ∧ ∃ s : ℝ, s < 0 ∧ Icc s 0 ⊆ D.regular ∧
      (∀ r ∈ Icc s 0, ∀ x : M,
        (⟨metricRm04At (S.family.metric r) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) ∧
      S.family.metric 0 = g := by
  have hopen : IsOpen (canonicalTimeDomain σ) :=
    isOpen_lt continuous_const (continuous_const.sub (continuous_const.mul continuous_id))
  obtain ⟨a, b, hzero, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hopen.mem_nhds (zero_mem_canonicalTimeDomain σ))
  let D := RealTimeInterval.openInterval a b 0 hzero
  have hD : D.carrier ⊆ canonicalTimeDomain σ := hsub
  let S := canonicalSolutionOn (I := I) g f σ hcomplete hsol D
  have hS : IsSolutionOn S := canonicalSolutionOn_isSolutionOn g f σ hcomplete hsol D hD
  have hreg : Icc (a / 2) 0 ⊆ D.regular := by
    intro t ht
    change a < t ∧ t < b
    constructor <;> linarith [hzero.1, hzero.2, ht.1, ht.2]
  have hR : ∀ r ∈ Icc (a / 2) 0, ∀ x,
      (⟨metricRm04At (S.family.metric r) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩ :
        algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) := by
    intro r hr x
    have hrD : r ∈ canonicalTimeDomain σ := hD (D.regular_subset (hreg hr))
    change metricAlgebraicCurvatureTensorAt (canonicalMetricFamily g f σ hcomplete hsol r) x ∈ _
    rw [canonicalMetricFamily_eq g f σ hcomplete hsol hrD]
    exact canonicalMetric_curvatureOperator_nonnegative g f σ hcomplete hsol hcone hrD x
  exact ⟨D, S, hS, a / 2, by linarith [hzero.1], hreg, hR,
    canonicalSolutionOn_metric_zero g f σ hcomplete hsol D⟩

theorem gradientRicciSoliton_curvatureOperatorImageAt_finrank_eq_of_nonnegative
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) (σ : ℝ)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f σ) (hdim : Module.finrank ℝ E = 3)
    (hcone : ∀ y : M, metricAlgebraicCurvatureTensorAt g y ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (x y : M) :
    Module.finrank ℝ (curvatureOperatorImageAt g x
      ⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩) =
      Module.finrank ℝ (curvatureOperatorImageAt g y
        ⟨metricRm04At g y, metricRm04At_mem_algebraicCurvatureTensorSubmodule g y⟩) := by
  obtain ⟨D, S, hS, s, hs, hreg, hR, hzero⟩ :=
    exists_nonnegative_canonical_slab g f σ hcomplete hsol hcone
  have heq := curvatureOperatorImageAt_finrank_eq_at_later_time S hS hdim
    hs hreg hR x y
  rw [hzero] at heq
  exact heq

theorem gradientRicciSoliton_metricCurvatureOperatorRankAt_eq_of_nonnegative
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) (σ : ℝ)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f σ) (hdim : Module.finrank ℝ E = 3)
    (hcone : ∀ y : M, metricAlgebraicCurvatureTensorAt g y ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (x y : M) :
    DimensionThree.metricCurvatureOperatorRankAt g x hdim =
      DimensionThree.metricCurvatureOperatorRankAt g y hdim := by
  rw [metricCurvatureOperatorRankAt_eq_curvatureOperatorImageAt_finrank g x hdim, metricCurvatureOperatorRankAt_eq_curvatureOperatorImageAt_finrank g y hdim]
  exact gradientRicciSoliton_curvatureOperatorImageAt_finrank_eq_of_nonnegative g f σ hcomplete hsol hdim hcone x y

theorem gradientRicciSoliton_curvatureOperatorImageAt_finrank_trichotomy_of_nonnegative
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) (σ : ℝ)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f σ) (hdim : Module.finrank ℝ E = 3)
    (hcone : ∀ y : M, metricAlgebraicCurvatureTensorAt g y ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (x : M) :
    let q := Module.finrank ℝ (curvatureOperatorImageAt g x
      ⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩)
    q = 0 ∨ q = 1 ∨ q = 3 := by
  obtain ⟨D, S, hS, s, hs, hreg, hR, hzero⟩ :=
    exists_nonnegative_canonical_slab g f σ hcomplete hsol hcone
  have heq := curvatureOperatorImageAt_finrank_trichotomy_at_later_time S hS hdim
    hs hreg hR x
  rw [hzero] at heq
  exact heq


theorem gradientRicciSoliton_metricCurvatureOperatorRankAt_trichotomy_of_nonnegative
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) (σ : ℝ)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f σ) (hdim : Module.finrank ℝ E = 3)
    (hcone : ∀ y : M, metricAlgebraicCurvatureTensorAt g y ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (x : M) :
    metricCurvatureOperatorRankAt g x hdim = 0 ∨
      metricCurvatureOperatorRankAt g x hdim = 1 ∨
      metricCurvatureOperatorRankAt g x hdim = 3 := by
  rw [metricCurvatureOperatorRankAt_eq_curvatureOperatorImageAt_finrank g x hdim]
  exact gradientRicciSoliton_curvatureOperatorImageAt_finrank_trichotomy_of_nonnegative g f σ hcomplete hsol hdim hcone x


theorem gradientRicciSoliton_curvatureOperatorKernelAt_parallel_of_nonnegative
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) (σ : ℝ)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f σ) (hdim : Module.finrank ℝ E = 3)
    (hcone : ∀ y : M, metricAlgebraicCurvatureTensorAt g y ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    Connection.IsParallelContinuousAlternatingSubmoduleFamily g
      (fun x => curvatureOperatorKernelAt g x
        ⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩) := by
  obtain ⟨D, S, hS, s, hs, hreg, hR, hzero⟩ :=
    exists_nonnegative_canonical_slab g f σ hcomplete hsol hcone
  have heq := DifferentialGeometry.PDE.RicciFlow.curvatureOperatorKernelAt_parallel_at_later_time S hS hdim
    hs hreg hR
  rw [hzero] at heq
  exact heq

end DifferentialGeometry.Geometry
