import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.Symbol.Formula
open DifferentialGeometry.Geometry.Curvature


noncomputable section

open Set Function
open scoped Topology ContDiff Matrix Manifold

namespace DifferentialGeometry
namespace PDE
namespace DeTurck
namespace RicciLinearization

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

section Output

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M] in
private lemma centeredChartTangentBasis_repr_apply_add (x : M)
    (v₁ v₂ : TangentSpace I x)
    (i : Fin (Module.finrank ℝ E)) :
    (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr (v₁ + v₂) i =
      (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v₁ i +
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v₂ i := by
  rw [← Module.Basis.coord_apply, ← Module.Basis.coord_apply, ← Module.Basis.coord_apply,
    map_add]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M] in
private lemma centeredChartTangentBasis_repr_apply_smul (x : M) (a : ℝ)
    (v : TangentSpace I x)
    (i : Fin (Module.finrank ℝ E)) :
    (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr (a • v) i =
      a * (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v i := by
  rw [← Module.Basis.coord_apply, ← Module.Basis.coord_apply, map_smul, smul_eq_mul]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M] in
def ricciSymbolOutput (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
  (LinearMap.mk₂ ℝ
    (fun v w : TangentSpace I x =>
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v i *
            (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr w k *
            ricciSymbolComp (I := I) g x ξ t i k)
    (fun v₁ v₂ w => by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [centeredChartTangentBasis_repr_apply_add]
      ring)
    (fun a v w => by
      rw [smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [centeredChartTangentBasis_repr_apply_smul]
      ring)
    (fun v w₁ w₂ => by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [centeredChartTangentBasis_repr_apply_add]
      ring)
    (fun a v w => by
      rw [smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [centeredChartTangentBasis_repr_apply_smul]
      ring) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma ricciSymbolOutput_apply_apply (g : SmoothRiemannianMetric I M) (x : M)
    (ξ : E) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (v w : TangentSpace I x) :
    ricciSymbolOutput (I := I) g x ξ t v w =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v i *
            (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr w k *
            ricciSymbolComp (I := I) g x ξ t i k := rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma ricciSymbolOutput_add (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t t' : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) :
    ricciSymbolOutput (I := I) g x ξ (t + t') =
      ricciSymbolOutput (I := I) g x ξ t + ricciSymbolOutput (I := I) g x ξ t' := by
  ext v w
  rw [LinearMap.add_apply, LinearMap.add_apply, ricciSymbolOutput_apply_apply,
    ricciSymbolOutput_apply_apply, ricciSymbolOutput_apply_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [ricciSymbolComp_add]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma ricciSymbolOutput_smul (g : SmoothRiemannianMetric I M) (x : M) (ξ : E) (a : ℝ)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) :
    ricciSymbolOutput (I := I) g x ξ (a • t) =
      a • ricciSymbolOutput (I := I) g x ξ t := by
  ext v w
  rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul,
    ricciSymbolOutput_apply_apply, ricciSymbolOutput_apply_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [ricciSymbolComp_smul]
  ring

end Output

section Bundle

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M] in
def ricciSymbol (g : SmoothRiemannianMetric I M) : TensorSymbol (E := E) I M :=
  fun x ξ =>
    { toFun := fun t => ricciSymbolOutput (I := I) g x ξ t
      map_add' := fun t t' => ricciSymbolOutput_add (I := I) g x ξ t t'
      map_smul' := fun a t => by
        simpa using ricciSymbolOutput_smul (I := I) g x ξ a t }

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma ricciSymbol_apply (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) :
    ricciSymbol (I := I) g x ξ t = ricciSymbolOutput (I := I) g x ξ t := rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem ricciSymbol_apply_apply (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i k : Fin (Module.finrank ℝ E)) :
    (ricciSymbol (I := I) g x ξ t)
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x i)
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x k) =
      ricciSymbolComp (I := I) g x ξ t i k := by
  classical
  rw [ricciSymbol_apply, ricciSymbolOutput_apply_apply]
  rw [(DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr_self,
    (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr_self]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single k]
    · rw [Finsupp.single_eq_same, Finsupp.single_eq_same]
      ring
    · intro k' _ hk'
      rw [Finsupp.single_eq_of_ne hk']
      ring
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  · intro i' _ hi'
    rw [Finsupp.single_eq_of_ne hi']
    simp
  · intro hi
    exact absurd (Finset.mem_univ i) hi

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem ricciSymbol_apply_eq_closedForm (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i k : Fin (Module.finrank ℝ E)) :
    (ricciSymbol (I := I) g x ξ t)
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x i)
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x k) =
      (1 / 2 : ℝ) * ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i *
          raisedFormContraction (I := I) g x ξ t k) +
        (1 / 2 : ℝ) * ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ k *
          raisedFormContractionSnd (I := I) g x ξ t i) -
        (1 / 2 : ℝ) * (metricCovectorNormSq (I := I) g x ξ *
          formComp (I := I) x t i k) -
        (1 / 2 : ℝ) * ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i *
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ k * formMetricTrace (I := I) g x t) := by
  rw [ricciSymbol_apply_apply, ricciSymbolComp_eq_closedForm]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem ricciSymbol_apply_symm (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (ht : ∀ v w, t v w = t w v) (v w : TangentSpace I x) :
    (ricciSymbol (I := I) g x ξ t) v w = (ricciSymbol (I := I) g x ξ t) w v := by
  rw [ricciSymbol_apply, ricciSymbolOutput_apply_apply,
    ricciSymbolOutput_apply_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [ricciSymbolComp_symm (I := I) g x ξ t ht k i]
  ring

end Bundle

end RicciLinearization
end DeTurck
end PDE
end DifferentialGeometry
