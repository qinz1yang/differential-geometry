import DifferentialGeometry.Geometry.Curvature.RicciRayleigh
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardSolutionRealization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CurvatureOperator

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology BigOperators ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem PartialStandardSolution.upperRicciTensorAt_eq_sec
    (S : PartialStandardSolution) (t : ℝ) (x : E3) :
    upperRicciTensorAt (S.metric t) x = ricciUpperBoundSec S.toSolutionOn t x := by
  rw [ricci_upper_bound_sec_at_point]
  change
    (metricScalarAt (S.metric t) x / 2) • metricTensorField (S.metric t) x -
        metricRicciAt (S.metric t) x =
      ((1 / 2 : ℝ) * metricScalarAt (S.metric t) x) •
        metricTensorField (S.metric t) x - metricRicci (S.metric t) x
  rw [metricRicci_apply]
  congr 1
  congr 1
  ring

theorem PartialStandardSolution.leastUpperRicciAt_continuousOn
    (S : PartialStandardSolution) :
    ContinuousOn (fun p : ℝ × E3 => leastUpperRicciAt (S.metric p.1) p.2)
      (S.domain ×ˢ (univ : Set E3)) := by
  let P := ↥(S.domain ×ˢ (univ : Set E3))
  have hp : Continuous (fun z : P × ↥(Metric.sphere (0 : E3) 1) => z.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have hv : Continuous (fun z : P × ↥(Metric.sphere (0 : E3) 1) => (z.2 : E3)) :=
    continuous_subtype_val.comp continuous_snd
  have hg : Continuous (fun z : P × ↥(Metric.sphere (0 : E3) 1) =>
      cartesianMetricFamily S.metric z.1.val) :=
    S.smooth.continuousOn.comp_continuous hp (fun z => z.1.property)
  have hRic : Continuous (fun z : P × ↥(Metric.sphere (0 : E3) 1) =>
      cartesianRicciFamily S.metric z.1.val) :=
    S.ricci_contDiffOn.continuousOn.comp_continuous hp (fun z => z.1.property)
  have hsc : Continuous (fun z : P × ↥(Metric.sphere (0 : E3) 1) =>
      metricScalarAt (S.metric z.1.val.1) z.1.val.2) :=
    S.scalar_contDiffOn.continuousOn.comp_continuous hp (fun z => z.1.property)
  have hd : Continuous (fun z : P × ↥(Metric.sphere (0 : E3) 1) =>
      (S.metric z.1.val.1).inner z.1.val.2 (z.2 : E3) (z.2 : E3)) :=
    (hg.clm_apply hv).clm_apply hv
  have hRq : Continuous (fun z : P × ↥(Metric.sphere (0 : E3) 1) =>
      ricciTensor (S.metric z.1.val.1) z.1.val.2 (z.2 : E3) (z.2 : E3)) :=
    (hRic.clm_apply hv).clm_apply hv
  have hquot : Continuous (fun z : P × ↥(Metric.sphere (0 : E3) 1) =>
      upperRicciRayleighAt (S.metric z.1.val.1) z.1.val.2 z.2.val) :=
    (((hsc.div_const 2).mul hd).sub hRq).div hd
      (fun z => ne_of_gt ((S.metric z.1.val.1).pos z.1.val.2 z.2.val
        (Metric.ne_of_mem_sphere z.2.property one_ne_zero)))
  have hmin : Continuous (fun p : P => leastUpperRicciAt (S.metric p.val.1) p.val.2) := by
    have h :=
      (isCompact_univ : IsCompact (Set.univ : Set ↥(Metric.sphere (0 : E3) 1))).continuous_sInf
          (f := fun p : P => fun v : ↥(Metric.sphere (0 : E3) 1) =>
            upperRicciRayleighAt (S.metric p.val.1) p.val.2 v.val)
          hquot
    simpa only [leastUpperRicciAt, Set.image_univ] using h
  exact continuousOn_iff_continuous_domRestrict.mpr hmin

theorem PartialStandardSolution.neg_leastUpperRicciAt_continuousOn
    (S : PartialStandardSolution) :
    ContinuousOn (fun p : ℝ × E3 => -leastUpperRicciAt (S.metric p.1) p.2)
      (S.domain ×ˢ (univ : Set E3)) :=
  S.leastUpperRicciAt_continuousOn.neg

theorem PartialStandardSolution.leastUpperRicciAt_zero_nonneg
    (S : PartialStandardSolution) (x : E3) :
    0 ≤ leastUpperRicciAt (S.metric 0) x := by
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 :=
    finrank_euclideanSpace_fin
  have hcone :
      metricAlgebraicCurvatureTensorAt (S.toSolutionOn.base.metric 0) x ∈
        algebraicCurvatureOperatorNonnegativeCone := by
    change metricAlgebraicCurvatureTensorAt (S.metric 0) x ∈
      algebraicCurvatureOperatorNonnegativeCone
    rw [S.initial]
    exact DifferentialGeometry.PDE.RicciFlow.StandardCap.metric_curvatureOperator_nonnegative x
  have hupper := ricci_upper_bound_of_metric_curvature_operator_nonnegative
    S.toSolutionOn (t := 0) (x := x) hdim hcone
  apply leastUpperRicciAt_nonneg_of_ricci_upper
  intro v
  have h := hupper v
  change metricRicciAt (S.metric 0) x (vec2 (I := 𝓡 3) v v) ≤
    (metricScalarAt (S.metric 0) x / 2) * (S.metric 0).inner x v v at h
  rwa [metricRicciAt_apply_eq_ricciTensor (S.metric 0) x v v] at h

theorem PartialStandardSolution.curvatureOperator_nonneg_of_leastUpperRicciAt_nonneg
    (S : PartialStandardSolution) (t : ℝ) (x : E3)
    (hmin : 0 ≤ leastUpperRicciAt (S.metric t) x) :
    metricAlgebraicCurvatureTensorAt (S.metric t) x ∈
      algebraicCurvatureOperatorNonnegativeCone := by
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 :=
    finrank_euclideanSpace_fin
  apply metric_curvature_operator_nonnegative_of_ricci_upper_bound_at
    S.toSolutionOn (t := t) (x := x) hdim
  intro v
  change metricRicciAt (S.metric t) x (vec2 (I := 𝓡 3) v v) ≤
    (metricScalarAt (S.metric t) x / 2) * (S.metric t).inner x v v
  rw [metricRicciAt_apply_eq_ricciTensor]
  exact ricci_upper_of_leastUpperRicciAt_nonneg (S.metric t) x hmin v

theorem PartialStandardSolution.exists_upperRicciRayleigh_bounds_closed
    (S : PartialStandardSolution) (T : ℝ)
    (hT : 0 ≤ T) (hTl : ENNReal.ofReal T < S.lifetime) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ t ∈ Icc 0 T, ∀ x : E3,
        Real.sqrt (normSq0S (S.metric t) x 4 (metricRm04 (S.metric t) x)) ≤ K) ∧
      (∀ t ∈ Icc 0 T, ∀ x : E3,
        -leastUpperRicciAt (S.metric t) x ≤ 8 * K) ∧
      (∀ t ∈ Icc 0 T, ∀ x : E3,
        ∀ basis : Module.Basis (Fin 3) ℝ (TangentSpace (𝓡 3) x),
        OrthonormalBasisAt (I := 𝓡 3) (S.metric t) x basis →
        ∀ r : ℝ,
          metricRicciAt (S.metric t) x
            (vec2 (I := 𝓡 3) (basis 0) (basis 0)) = r →
          r ≤ 3 * K) := by
  obtain ⟨K, hK, hRm⟩ := S.curvature_bound T hT hTl
  refine ⟨K, hK, hRm, ?_, ?_⟩
  · intro t ht x
    exact (neg_le_abs (leastUpperRicciAt (S.metric t) x)).trans
      (abs_leastUpperRicciAt_le_eight_mul_of_rm (S.metric t) x K (hRm t ht x))
  · intro t ht x basis horth r hr
    exact (le_abs_self r).trans
      (ricciEigenvalue_abs_le_three_mul_of_rm
        (S.metric t) x K (hRm t ht x) basis horth r hr)

theorem PartialStandardSolution.eventually_shifted_upperRicci_lower_support
    (S : PartialStandardSolution) (t : ℝ) (x : E3)
    (V : E3 → E3) (hV : ContinuousAt V x) (hVx : V x ≠ 0)
    (ell : ℝ) (K : Set (ℝ × E3)) :
    ∀ᶠ p in 𝓝[K] (t, x),
      -(ell +
        (upperRicciTensorAt (S.metric p.1) p.2
            (vec2 (I := 𝓡 3) (V p.2) (V p.2)) -
          ell * (S.metric p.1).inner p.2 (V p.2) (V p.2)) /
            (S.metric p.1).inner p.2 (V p.2) (V p.2)) ≤
        -leastUpperRicciAt (S.metric p.1) p.2 := by
  have hsnd : Filter.Tendsto (fun p : ℝ × E3 => p.2)
      (𝓝[K] (t, x)) (𝓝 x) :=
    continuous_snd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  filter_upwards [hsnd.eventually (hV.eventually_ne hVx)] with p hp
  rw [shifted_upperRicciRayleighAt_eq (S.metric p.1) p.2 (V p.2) hp ell]
  exact neg_le_neg (leastUpperRicciAt_le_rayleigh (S.metric p.1) p.2 (V p.2) hp)
end DifferentialGeometry.PDE.RicciFlow
