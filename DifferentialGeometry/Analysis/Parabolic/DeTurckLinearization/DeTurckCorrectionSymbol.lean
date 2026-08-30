import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.DeTurckCorrectionSymbolFormula
open DifferentialGeometry.Geometry.Curvature


noncomputable section

open Set Function
open scoped Topology ContDiff Matrix Manifold

namespace DifferentialGeometry
namespace PDE
namespace DeTurck
namespace DeTurckLinearization

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [hSigma : SigmaCompactSpace M] [hT2 : T2Space M]
  [hBoundaryless : BoundarylessManifold I M]

section Output

omit [NeZero (Module.finrank ℝ E)] hSigma hT2 hBoundaryless in
private lemma centeredChartTangentBasis_repr_apply_add (x : M)
    (v₁ v₂ : TangentSpace I x)
    (i : Fin (Module.finrank ℝ E)) :
    (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr (v₁ + v₂) i =
      (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v₁ i +
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v₂ i := by
  exact congrArg
    (fun p : Fin (Module.finrank ℝ E) →₀ ℝ => p i)
    ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr.map_add v₁ v₂)

omit [NeZero (Module.finrank ℝ E)] hSigma hT2 hBoundaryless in
private lemma centeredChartTangentBasis_repr_apply_smul (x : M)
    (a : ℝ) (v : TangentSpace I x)
    (i : Fin (Module.finrank ℝ E)) :
    (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr (a • v) i =
      a * (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v i := by
  have h := congrArg
    (fun p : Fin (Module.finrank ℝ E) →₀ ℝ => p i)
    ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr.map_smul a v)
  simpa only [Finsupp.smul_apply, smul_eq_mul] using h

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
    [BoundarylessManifold I M] in
def deTurckCorrectionSymbolOutput (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
  (LinearMap.mk₂ ℝ
    (fun v w : TangentSpace I x =>
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v i *
            (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr w j *
            deTurckCorrSymbolComp (I := I) g x ξ t i j)
    (fun v₁ v₂ w => by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [centeredChartTangentBasis_repr_apply_add]
      ring)
    (fun a v w => by
      rw [smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [centeredChartTangentBasis_repr_apply_smul]
      ring)
    (fun v w₁ w₂ => by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [centeredChartTangentBasis_repr_apply_add]
      ring)
    (fun a v w => by
      rw [smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [centeredChartTangentBasis_repr_apply_smul]
      ring) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma deTurckCorrectionSymbolOutput_apply_apply (g : SmoothRiemannianMetric I M)
    (x : M) (ξ : E) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (v w : TangentSpace I x) :
    deTurckCorrectionSymbolOutput (I := I) g x ξ t v w =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v i *
            (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr w j *
            deTurckCorrSymbolComp (I := I) g x ξ t i j := rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma deTurckCorrectionSymbolOutput_add (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t t' : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) :
    deTurckCorrectionSymbolOutput (I := I) g x ξ (t + t') =
      deTurckCorrectionSymbolOutput (I := I) g x ξ t +
        deTurckCorrectionSymbolOutput (I := I) g x ξ t' := by
  ext v w
  rw [LinearMap.add_apply, LinearMap.add_apply, deTurckCorrectionSymbolOutput_apply_apply,
    deTurckCorrectionSymbolOutput_apply_apply, deTurckCorrectionSymbolOutput_apply_apply,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [deTurckCorrSymbolComp_add]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma deTurckCorrectionSymbolOutput_smul (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (a : ℝ) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) :
    deTurckCorrectionSymbolOutput (I := I) g x ξ (a • t) =
      a • deTurckCorrectionSymbolOutput (I := I) g x ξ t := by
  ext v w
  rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul,
    deTurckCorrectionSymbolOutput_apply_apply, deTurckCorrectionSymbolOutput_apply_apply,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [deTurckCorrSymbolComp_smul]
  ring

end Output

section Bundle

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
    [BoundarylessManifold I M] in
def deTurckCorrectionSymbol (g : SmoothRiemannianMetric I M) :
    TensorSymbol (E := E) I M :=
  fun x ξ =>
    { toFun := fun t => deTurckCorrectionSymbolOutput (I := I) g x ξ t
      map_add' := fun t t' => deTurckCorrectionSymbolOutput_add (I := I) g x ξ t t'
      map_smul' := fun a t => by
        simpa using deTurckCorrectionSymbolOutput_smul (I := I) g x ξ a t }

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma deTurckCorrectionSymbol_apply (g : SmoothRiemannianMetric I M) (x : M)
    (ξ : E) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) :
    deTurckCorrectionSymbol (I := I) g x ξ t =
      deTurckCorrectionSymbolOutput (I := I) g x ξ t := rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem deTurckCorrectionSymbol_apply_apply (g : SmoothRiemannianMetric I M) (x : M)
    (ξ : E) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i j : Fin (Module.finrank ℝ E)) :
    (deTurckCorrectionSymbol (I := I) g x ξ t)
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x i)
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x j) =
      deTurckCorrSymbolComp (I := I) g x ξ t i j := by
  classical
  rw [deTurckCorrectionSymbol_apply, deTurckCorrectionSymbolOutput_apply_apply]
  rw [(DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr_self,
    (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr_self]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · rw [Finsupp.single_eq_same, Finsupp.single_eq_same]
      ring
    · intro j' _ hj'
      rw [Finsupp.single_eq_of_ne hj']
      ring
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  · intro i' _ hi'
    rw [Finsupp.single_eq_of_ne hi']
    simp
  · intro hi
    exact absurd (Finset.mem_univ i) hi

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem deTurckCorrectionSymbol_apply_eq_closedForm (g : SmoothRiemannianMetric I M)
    (x : M) (ξ : E) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i j : Fin (Module.finrank ℝ E)) :
    (deTurckCorrectionSymbol (I := I) g x ξ t)
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x i)
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x j) =
      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i *
          raisedFormContractionSnd (I := I) g x ξ t j +
        (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j *
          raisedFormContractionSnd (I := I) g x ξ t i -
        (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j *
          formMetricTrace (I := I) g x t := by
  rw [deTurckCorrectionSymbol_apply_apply, deTurckCorrSymbolComp_eq_closedForm]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem deTurckCorrectionSymbol_apply_symm (g : SmoothRiemannianMetric I M) (x : M)
    (ξ : E) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (v w : TangentSpace I x) :
    (deTurckCorrectionSymbol (I := I) g x ξ t) v w =
      (deTurckCorrectionSymbol (I := I) g x ξ t) w v := by
  rw [deTurckCorrectionSymbol_apply, deTurckCorrectionSymbolOutput_apply_apply,
    deTurckCorrectionSymbolOutput_apply_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [deTurckCorrSymbolComp_symm (I := I) g x ξ t j i]
  ring

end Bundle

end DeTurckLinearization
end DeTurck
end PDE
end DifferentialGeometry
