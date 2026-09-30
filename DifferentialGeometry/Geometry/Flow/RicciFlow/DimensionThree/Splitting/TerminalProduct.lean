import DifferentialGeometry.Geometry.Curvature.DimensionTwo.RicciScalar
import DifferentialGeometry.Geometry.Curvature.Line
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionTwo.TerminalRound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.ProductFactor
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction

noncomputable section
open Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M] {D : RealTimeInterval}

theorem product_flow_metric_eq_of_terminal_scalar_constant
    (S : SolutionOn (I := I.prod 𝓘(ℝ)) (M := M × ℝ) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 2) {a b σ : ℝ} (hab : a < b) (hσ : 0 ≤ σ)
    (hcar : Icc a b ⊆ D.carrier) (hreg : Ioo a b ⊆ D.regular)
    (hprod : ∀ t ∈ Icc a b, S.family.metric t =
      ((S.family.metric t).sliceFst (0 : ℝ)).prod (euclideanMetric (E := ℝ)))
    (hterminal : ∀ x : M, S.scalar b (x,0) = σ) :
    ∀ t ∈ Icc a b, ∀ x : M, ∀ z : ℝ,
      ∀ (v w : TangentSpace I x) (c d : ℝ),
      (S.family.metric t).inner (x,z) (v,c) (w,d) =
        (1 + σ * (b - t)) * (S.family.metric b).inner (x,0) (v,0) (w,0) + c * d := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let U := S.timeRestrict (RealTimeInterval.closed a b hab.le)
  have hU : IsSolutionOn U := isSolutionOn_timeRestrict hS hcar hreg
  let T : SolutionOn (I := I) (M := M) (RealTimeInterval.closed a b hab.le) :=
    { base.metric := fun t => (S.family.metric t).sliceFst (0 : ℝ) }
  have hT : IsSolutionOn T := isSolutionOn_sliceFst_of_prod_euclidean U hU hprod
  have hscalar (x : M) : T.scalar b x = σ := by
    have hh := hterminal x
    change metricScalarAt (S.family.metric b) (x,0) = σ at hh
    rw [hprod b ⟨hab.le,le_rfl⟩,metricScalarAt_productMetric,
      metricScalarAt_eq_zero_of_finrank_le_one (euclideanMetric (E := ℝ))
        (by simp : Module.finrank ℝ ℝ ≤ 1),add_zero] at hh
    exact hh
  have hmetric := surface_metric_eq_scale_of_terminal_scalar_constant T hT hdim hab hσ
    Subset.rfl Subset.rfl hscalar
  intro t ht x z v w c d
  rw [hprod t ht]
  erw [SmoothRiemannianMetric.prod_inner]
  have hs := hmetric t ht x v w
  change ((S.family.metric t).sliceFst (0 : ℝ)).inner x v w =
    (1 + σ * (b-t)) * ((S.family.metric b).sliceFst (0 : ℝ)).inner x v w at hs
  rw [hs,SmoothRiemannianMetric.sliceFst_inner]
  congr 1
  exact (DifferentialGeometry.euclideanMetric_inner z c d).trans (by change d * c = c * d; exact mul_comm _ _)

end DifferentialGeometry.PDE.RicciFlow

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M] {D : RealTimeInterval}

theorem product_flow_metric_inner_eq_affine_ricci_of_terminal_scalar_constant
    (S : SolutionOn (I := I.prod 𝓘(ℝ)) (M := M × ℝ) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 2) {a b σ : ℝ} (hab : a < b) (hσ : 0 ≤ σ)
    (hcar : Icc a b ⊆ D.carrier) (hreg : Ioo a b ⊆ D.regular)
    (hprod : ∀ t ∈ Icc a b, S.family.metric t =
      ((S.family.metric t).sliceFst (0 : ℝ)).prod (euclideanMetric (E := ℝ)))
    (hterminal : ∀ x : M, S.scalar b (x, 0) = σ) :
    ∀ t ∈ Icc a b, ∀ x : M × ℝ, ∀ v w : TangentSpace (I.prod 𝓘(ℝ)) x,
      (S.family.metric t).inner x v w =
        (S.family.metric b).inner x v w +
          2 * (b - t) * ricciTensor (S.family.metric b) x v w := by
  have hb : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  have hscalar (x : M) : metricScalarAt ((S.family.metric b).sliceFst (0 : ℝ)) x = σ := by
    have h := hterminal x
    change metricScalarAt (S.family.metric b) (x, 0) = σ at h
    rw [hprod b hb, metricScalarAt_productMetric,
      metricScalarAt_eq_zero_of_finrank_le_one (euclideanMetric (E := ℝ))
        (by simp : Module.finrank ℝ ℝ ≤ 1), add_zero] at h
    exact h
  rintro t ht ⟨x, z⟩ ⟨v, c⟩ ⟨w, d⟩
  have hprofile := product_flow_metric_eq_of_terminal_scalar_constant S hS hdim hab hσ
    hcar hreg hprod hterminal t ht x z v w c d
  rw [hprofile]
  conv_rhs =>
    erw [hprod b hb, SmoothRiemannianMetric.prod_inner, ricciTensor_productMetric,
      ricciTensor_line_eq_zero,
      ricciTensor_eq_half_metricScalarAt_mul_inner_of_finrank_eq_two _ hdim,
      hscalar]
  erw [SmoothRiemannianMetric.sliceFst_inner]
  change _ = _ + inner ℝ c d + _
  rw [Real.inner_apply]
  ring

end DifferentialGeometry.PDE.RicciFlow
