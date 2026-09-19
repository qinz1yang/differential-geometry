import DifferentialGeometry.Geometry.Operator.Gradient.NormSquared

set_option autoImplicit false
noncomputable section
open Bundle Set Filter
open scoped Manifold ContDiff BigOperators Topology
namespace DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem normGradSqFun_eq_chartInvGram_sum
    (g : SmoothRiemannianMetric I M) (α : M) {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hxint : extChartAt I α x ∈ interior (extChartAt I α).target) :
    normGradSqFun g f x =
      ∑ k : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α x k i *
          partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x) *
          partialDeriv (E := E) k (scalarOnE (I := I) α f) (extChartAt I α x) := by
  have hxchart : x ∈ (chartAt H α).source := by
    rwa [trivializationAt_baseSet_eq_chartAt_source (I := I)] at hx
  rw [normGradSqFun_def, inner_gradFun,
    ← gradChartLocal_eq_gradFun g α hf hx hxint]
  change (mvfderiv (I := I) f x)
    (∑ k : Fin (Module.finrank ℝ E), gradChartCoeff g α f k x • chartBasisVecFiber α k x) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul]
  change gradChartCoeff g α f k x *
    (mvfderiv (I := I) f x) (chartBasisVecFiber α k x) = _
  have hdf : mvfderiv (I := I) f x (chartBasisVecFiber α k x) =
      partialDeriv (E := E) k (scalarOnE (I := I) α f) (extChartAt I α x) :=
    mfderiv_chartBasisVecFiber_of_mdifferentiableAt α hf hxchart hxint k
  rw [hdf]
  exact Finset.sum_mul _ _ _

theorem normGradSqFun_comp_extChartAt
    (g : SmoothRiemannianMetric I M) (α : M) {f : E → ℝ} {x : M}
    (hx : x ∈ (chartAt H α).source)
    (hxint : extChartAt I α x ∈ interior (extChartAt I α).target)
    (hf : DifferentiableAt ℝ f (extChartAt I α x)) :
    normGradSqFun g (f ∘ extChartAt I α) x =
      ∑ k : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k i (extChartAt I α x) *
          fderiv ℝ f (extChartAt I α x) (chartModelBasis E i) *
          fderiv ℝ f (extChartAt I α x) (chartModelBasis E k) := by
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rwa [trivializationAt_baseSet_eq_chartAt_source (I := I)]
  have hxsrc : x ∈ (extChartAt I α).source := by
    rwa [extChartAt_source_eq_chartAt_source (I := I)]
  have hfM : MDifferentiableAt I 𝓘(ℝ, ℝ) (f ∘ extChartAt I α) x :=
    hf.mdifferentiableAt.comp x (mdifferentiableAt_extChartAt hx)
  have heq : scalarOnE (I := I) α (f ∘ extChartAt I α) =ᶠ[𝓝 (extChartAt I α x)] f := by
    filter_upwards [isOpen_interior.mem_nhds hxint] with y hy
    change f (extChartAt I α ((extChartAt I α).symm y)) = f y
    rw [(extChartAt I α).right_inv (interior_subset hy)]
  rw [normGradSqFun_eq_chartInvGram_sum g α hfM hbase hxint]
  simp only [partialDeriv, heq.fderiv_eq, chartInvGramOnE_def, (extChartAt I α).left_inv hxsrc]

end DifferentialGeometry.Geometry.Operator
