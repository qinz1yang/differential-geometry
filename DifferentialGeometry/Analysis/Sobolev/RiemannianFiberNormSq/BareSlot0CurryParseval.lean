import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.SlotSplitParsevalBridge
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradParallelNaturality
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection


noncomputable section


open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Elliptic

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

noncomputable def tensor0SToTensorRS {s : ℕ} (x : M) (C : Tensor0SSpace s I x) :
    TensorRSSpace 0 s I x :=
  (tensor00Scalar (I := I) (M := M) x).smulRight C


omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma tensor0SAsRS_apply {s : ℕ} (x : M) (C : Tensor0SSpace s I x)
    (τ : Tensor0SSpace 0 I x) :
    (tensor0SToTensorRS (I := I) (M := M) x C :
        Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) τ =
      tensor00Scalar (I := I) (M := M) x τ • C := by
  change ((tensor00Scalar (I := I) (M := M) x).smulRight C) τ = _
  rw [ContinuousLinearMap.smulRight_apply]


omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma coframeS_zero_eq_unitZeroSec
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n) :
    coframeS (I := I) (M := M) g x 0 e K₀ = unitZeroSec (I := I) (M := M) x := by
  classical
  apply tensor0SSpace_ext (𝕜 := ℝ) 0 x
  intro u
  rw [coframeS_apply (I := I) (M := M) g x 0 e K₀ u]
  rw [Fin.prod_univ_zero]
  rw [show ((unitZeroSec (I := I) (M := M) x) u : ℝ) =
      Tensor0SSpace.toModel (unitZeroSec (I := I) (M := M) x) u from rfl]
  rw [unitZeroSec_apply (I := I) (M := M) x, Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.constOfIsEmpty_apply]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M] in
private lemma tensor01_comp
    (g : SmoothRiemannianMetric I M) (x : M)
    (W : TensorRSSpace 0 1 I x) {n : ℕ}
    (e : Fin n → TangentSpace I x) (J : Fin 1 → Fin n)
    (K₀ : Fin 0 → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g x 0 1 W n e K₀ J =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from W)
          (unitZeroSec (I := I) (M := M) x))
        (fun i : Fin 1 ↦ e (J i)) := by
  classical
  unfold fiberNormSqComponent
  rw [show ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
        (fun l : Fin 0 ↦ g.inner x (e (K₀ l))) : Tensor0SSpace 0 I x) =
      coframeS (I := I) (M := M) g x 0 e K₀ from rfl]
  rw [coframeS_zero_eq_unitZeroSec (I := I) (M := M) g x e K₀]
  rfl

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M] in
theorem sq_unit_eval_le
    (g : SmoothRiemannianMetric I M) (x : M)
    (W : TensorRSSpace 0 1 I x) (X : TangentSpace I x) :
    (Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from W)
          (unitZeroSec (I := I) (M := M) x))
        (fun _ : Fin 1 ↦ X)) ^ 2 ≤
      g.inner x X X *
        riemannianFiberNormSq (I := I) (M := M) g 0 1 x W := by
  classical
  obtain ⟨n, e, _bse, _hn, _hbse, _horth, hpars, hexpand, hrfns⟩ :=
    tangent_orthonormalBasisS_witness (I := I) (M := M) g 1 x
  let vec : Fin 1 → TangentSpace I x := fun _ ↦ X
  let B : ContinuousMultilinearMap ℝ (fun _ : Fin 1 ↦ E) ℝ :=
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from W)
        (unitZeroSec (I := I) (M := M) x))
  let coef : (Fin 1 → Fin n) → ℝ := fun J ↦
    ∏ i : Fin 1, g.inner x (e (J i)) (vec i)
  let comp : (Fin 1 → Fin n) → ℝ := fun J ↦
    B (fun i : Fin 1 ↦ e (J i))
  have hvalue : B vec = ∑ J : Fin 1 → Fin n, coef J * comp J := by
    have hrw : B vec = B (fun i : Fin 1 ↦
        ∑ j : Fin n, g.inner x (e j) (vec i) • e j) := by
      congr 1
      funext i
      exact hexpand (vec i)
    rw [hrw, ContinuousMultilinearMap.map_sum]
    refine Finset.sum_congr rfl (fun J _ ↦ ?_)
    dsimp only [coef, comp]
    simpa only [smul_eq_mul] using
      B.map_smul_univ
        (fun i : Fin 1 ↦ g.inner x (e (J i)) (vec i))
        (fun i : Fin 1 ↦ (show E from e (J i)))
  have hcs : (∑ J : Fin 1 → Fin n, coef J * comp J) ^ 2 ≤
      (∑ J : Fin 1 → Fin n, coef J ^ 2) *
        ∑ J : Fin 1 → Fin n, comp J ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ coef comp
  have hcoef : (∑ J : Fin 1 → Fin n, coef J ^ 2) = g.inner x X X := by
    have hpow (J : Fin 1 → Fin n) : coef J ^ 2 =
        ∏ i : Fin 1, g.inner x (e (J i)) (vec i) ^ 2 := by
      dsimp only [coef]
      rw [← Finset.prod_pow]
    rw [Finset.sum_congr rfl (fun J _ ↦ hpow J)]
    rw [show (∑ J : Fin 1 → Fin n,
          ∏ i : Fin 1, g.inner x (e (J i)) (vec i) ^ 2) =
        ∑ J ∈ Fintype.piFinset (fun _ : Fin 1 ↦ (Finset.univ : Finset (Fin n))),
          ∏ i : Fin 1, g.inner x (e (J i)) (vec i) ^ 2 by
      rw [Fintype.piFinset_univ]]
    rw [← Finset.prod_univ_sum
      (fun _ : Fin 1 ↦ (Finset.univ : Finset (Fin n)))
      (fun i j ↦ g.inner x (e j) (vec i) ^ 2)]
    rw [Fin.prod_univ_one, hpars (vec 0)]
  have hcomp : (∑ J : Fin 1 → Fin n, comp J ^ 2) =
      riemannianFiberNormSq (I := I) (M := M) g 0 1 x W := by
    rw [hrfns W]
    rw [Fintype.sum_unique (fun K : Fin 0 → Fin n ↦
      ∑ J : Fin 1 → Fin n,
        fiberNormSqSummand (I := I) (M := M) g x 0 1 W n e K J)]
    refine Finset.sum_congr rfl (fun J _ ↦ ?_)
    dsimp only [comp]
    rw [fiberNormSqSummand_eq_component_sq,
      tensor01_comp (I := I) (M := M) g x W e J (default : Fin 0 → Fin n)]
  change (B vec) ^ 2 ≤ _
  rw [hvalue]
  calc
    (∑ J : Fin 1 → Fin n, coef J * comp J) ^ 2
        ≤ (∑ J : Fin 1 → Fin n, coef J ^ 2) *
            ∑ J : Fin 1 → Fin n, comp J ^ 2 := hcs
    _ = g.inner x X X *
        riemannianFiberNormSq (I := I) (M := M) g 0 1 x W := by
      rw [hcoef, hcomp]


omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma slot0Curry_eq_tensor0SToTensorRS_curry_unitZeroSec
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n)
    (T : TensorRSSpace 0 (s + 1) I x) (a : Fin n) :
    slot0Curry (I := I) (M := M) g x s e K₀ T a =
      tensor0SToTensorRS (I := I) (M := M) x
        (tensor0S_curry (I := I) (M := M) s x
          ((T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x)
            (unitZeroSec (I := I) (M := M) x)) (e a)) := by
  unfold slot0Curry tensor0SToTensorRS
  rw [show ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
        (fun k => g.inner x (e (K₀ k))) : Tensor0SSpace 0 I x) =
      coframeS (I := I) (M := M) g x 0 e K₀ from rfl]
  rw [coframeS_zero_eq_unitZeroSec (I := I) (M := M) g x e K₀]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem riemannianFiberNormSq_succ_eq_sum_bareSlot0Curry
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (T : TensorRSSpace 0 (s + 1) I x) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x T =
        ∑ a : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (tensor0SToTensorRS (I := I) (M := M) x
              (tensor0S_curry (I := I) (M := M) s x
                ((T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x)
                  (unitZeroSec (I := I) (M := M) x)) (e a))) := by
  classical
  obtain ⟨n, e, K₀, hn, hsplit⟩ :=
    riemannianFiberNormSq_succ_eq_sum_slot0Curry (I := I) (M := M) g s x T
  refine ⟨n, e, hn, ?_⟩
  rw [hsplit]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [slot0Curry_eq_tensor0SToTensorRS_curry_unitZeroSec (I := I) (M := M) g x s e K₀ T a]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem riemannianFiberNormSq_three_eq_sum_bareSlot0Curry
    (g : SmoothRiemannianMetric I M) (x : M)
    (T : TensorRSSpace 0 3 I x) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      riemannianFiberNormSq (I := I) (M := M) g 0 3 x T =
        ∑ a : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 2 x
            (tensor0SToTensorRS (I := I) (M := M) x
              (tensor0S_curry (I := I) (M := M) 2 x
                ((T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x)
                  (unitZeroSec (I := I) (M := M) x)) (e a))) :=
  riemannianFiberNormSq_succ_eq_sum_bareSlot0Curry (I := I) (M := M) g 2 x T

end Elliptic
end Analysis
end DifferentialGeometry

end
