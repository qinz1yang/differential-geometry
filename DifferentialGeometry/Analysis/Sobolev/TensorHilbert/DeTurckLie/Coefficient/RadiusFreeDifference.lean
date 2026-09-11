import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLie.Coefficient.L2JetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckVectorField.RadiusFree
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearity.Basic

noncomputable section

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Spectral.MetricRealization
  (gFibreOpBound ccTensorBilinSymm ccTensorBilin ccTensorBilin_apply ccTensorBilinSymm_apply
    ccTensorBilinSymm_symm)
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Combinatorics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem exists_deTurckLieConnectionDifferenceDerivativeCoefficient_iteratedCovGrad_normSq_perOrder_radiusFree_bound
    (g₀ g_bg : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    {Λ₀ : ℝ} (hΛ₀0 : 0 ≤ Λ₀) :
    ∃ Ktop : ℕ → ℝ, (∀ i, 0 ≤ Ktop i) ∧ ∃ Flow : ℕ → ℝ, (∀ i, 0 ≤ Flow i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ₀ ^ 2)
        (i : ℕ),
        ‖iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieConnectionDifferenceDerivCoeffField (I := I) g₀ g₁ g_bg)‖ ^ 2 ≤
          Ktop i * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 +
          Flow i * (1 + ∑ j ∈ Finset.range (i + 3),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨Ktop_a, hKtop_a_nn, Kc_a, hKc_a_nn, hfield⟩ :=
    exists_deTurckLieConnectionDifferenceDerivativeCoefficient_iteratedCovGrad_fiberNormSq_topOrderSeparated_bound (I := I) (M := M) g₀ g_bg hδ₀
  obtain ⟨K_rf, hK_rf_nn, hK_rf⟩ :=
    antidiagonalTupleGrid_integral_radiusFree (I := I) (M := M) g₀ hΛ₀0
  refine ⟨fun i => Ktop_a * operatorFieldApplicationGdiag (E := E) i * operatorFieldApplicationGdiag (E := E) i,
    fun i => mul_nonneg (mul_nonneg hKtop_a_nn (operatorFieldApplicationGdiag_nonneg (E := E) i))
      (operatorFieldApplicationGdiag_nonneg (E := E) i),
    fun i => Kc_a i * ∑ k ∈ Finset.range (i + 3), K_rf k,
    fun i => mul_nonneg (hKc_a_nn i) (Finset.sum_nonneg fun k _ => hK_rf_nn k), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hsup i
  have : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  set S' : ℝ := ∑ j ∈ Finset.range (i + 3),
    ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 with hS'_def
  have hS'_nn : 0 ≤ S' := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieConnectionDifferenceDerivCoeffField (I := I) g₀ g₁ g_bg)).toSection x) ≤
        (Ktop_a * operatorFieldApplicationGdiag (E := E) i * operatorFieldApplicationGdiag (E := E) i) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x) +
          Kc_a i * antidiagonalTupleGridPartialSum
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 3) :=
    fun x => hfield g₁ P htie hδ_le hδ0 hδ i x
  have hAG : ∀ k : ℕ,
      MeasureTheory.Integrable
          (fun x => Combinatorics.antidiagonalTupleGrid
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) k)
          (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
        (∫ x, Combinatorics.antidiagonalTupleGrid
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) k
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
          K_rf k * (1 + ‖iteratedCovGrad (I := I) g₀ 0 2 k P‖ ^ 2) := by
    intro k
    have hExpand : (fun x => Combinatorics.antidiagonalTupleGrid
          (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) k)
        = (fun x => ∑ nn ∈ Finset.range (k + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple nn k,
            ∏ m : Fin nn, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) := by
      funext x; rw [Combinatorics.antidiagonalTupleGrid]
    rw [hExpand]; exact hK_rf P hsup k
  have hwin_int : MeasureTheory.Integrable
      (fun x => antidiagonalTupleGridPartialSum
        (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 3))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    rw [show (fun x => antidiagonalTupleGridPartialSum
        (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 3)) =
      (fun x => ∑ k ∈ Finset.range (i + 3),
        Combinatorics.antidiagonalTupleGrid
          (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) k) from by rfl]
    exact MeasureTheory.integrable_finsetSum _ (fun k _ => (hAG k).1)
  have htop_int : MeasureTheory.Integrable (fun x =>
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + (i + 2))
      (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P)
  have hbridge := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + i)
    (iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieConnectionDifferenceDerivCoeffField (I := I) g₀ g₁ g_bg))
    (fun x => (Ktop_a * operatorFieldApplicationGdiag (E := E) i * operatorFieldApplicationGdiag (E := E) i) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)
      + Kc_a i * antidiagonalTupleGridPartialSum
          (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 3))
    ((htop_int.const_mul (Ktop_a * operatorFieldApplicationGdiag (E := E) i * operatorFieldApplicationGdiag (E := E) i)).add
      (hwin_int.const_mul (Kc_a i))) hpt
  rw [MeasureTheory.integral_add
      (htop_int.const_mul (Ktop_a * operatorFieldApplicationGdiag (E := E) i * operatorFieldApplicationGdiag (E := E) i))
      (hwin_int.const_mul (Kc_a i)),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hbridge
  have hnormsq : ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    rw [SmoothCcTensor.norm_def, tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  have hwin_bd : (∫ x, antidiagonalTupleGridPartialSum
      (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 3)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
      (∑ k ∈ Finset.range (i + 3), K_rf k) * (1 + S') := by
    rw [show (fun x => antidiagonalTupleGridPartialSum
        (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 3)) =
      (fun x => ∑ k ∈ Finset.range (i + 3),
        Combinatorics.antidiagonalTupleGrid
          (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) k) from by rfl]
    rw [MeasureTheory.integral_finsetSum _ (fun k _ => (hAG k).1), Finset.sum_mul]
    refine Finset.sum_le_sum (fun k hk => ?_)
    refine le_trans (hAG k).2 ?_
    have hkS' : ‖iteratedCovGrad (I := I) g₀ 0 2 k P‖ ^ 2 ≤ S' :=
      Finset.single_le_sum (f := fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_range.mpr (by rw [Finset.mem_range] at hk; omega))
    refine mul_le_mul_of_nonneg_left ?_ (hK_rf_nn k)
    linarith
  calc ‖iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieConnectionDifferenceDerivCoeffField (I := I) g₀ g₁ g_bg)‖ ^ 2
      ≤ (Ktop_a * operatorFieldApplicationGdiag (E := E) i * operatorFieldApplicationGdiag (E := E) i) *
          (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
        + Kc_a i * (∫ x, antidiagonalTupleGridPartialSum
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 3)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) := hbridge
    _ = (Ktop_a * operatorFieldApplicationGdiag (E := E) i * operatorFieldApplicationGdiag (E := E) i) *
          ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2
        + Kc_a i * (∫ x, antidiagonalTupleGridPartialSum
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 3)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) := by rw [hnormsq]
    _ ≤ (Ktop_a * operatorFieldApplicationGdiag (E := E) i * operatorFieldApplicationGdiag (E := E) i) *
          ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2
        + Kc_a i * ((∑ k ∈ Finset.range (i + 3), K_rf k) * (1 + S')) := by
        have hmul := mul_le_mul_of_nonneg_left hwin_bd (hKc_a_nn i)
        linarith [hmul]
    _ = Ktop_a * operatorFieldApplicationGdiag (E := E) i * operatorFieldApplicationGdiag (E := E) i *
          ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2
        + (Kc_a i * ∑ k ∈ Finset.range (i + 3), K_rf k) * (1 + S') := by ring

theorem exists_deTurckLieCovariantDerivativeInsertion_iteratedCovGrad_normSq_perOrder_radiusFree_bound
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    {Λ₀ : ℝ} (hΛ₀0 : 0 ≤ Λ₀) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Flow : ℕ → ℝ, (∀ i, 0 ≤ Flow i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ₀ ^ 2)
        (i : ℕ), i ≤ a →
        ‖iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieCovariantDerivativeInsertionField (I := I) g₀ g₁ g_bg)‖ ^ 2 ≤
          Ktop * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 +
          Flow i * (1 + ∑ j ∈ Finset.range (i + 3),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨Kb_top, hKb_top_nn, Kb_flow, hKb_flow_nn, hwalpha⟩ :=
    deTurckVectorFieldCovariantDerivativeLowered_iteratedCovGrad_norm_sq_topOrderSeparated (I := I) (M := M) g₀ g_bg a hδ₀ hΛ₀0
  have h4fr_nn : (0 : ℝ) ≤ 4 * (Module.finrank ℝ E : ℝ) := by positivity
  refine ⟨4 * (Module.finrank ℝ E : ℝ) * Kb_top, mul_nonneg h4fr_nn hKb_top_nn,
    fun i => 4 * (Module.finrank ℝ E : ℝ) * Kb_flow i,
    fun i => mul_nonneg h4fr_nn (hKb_flow_nn i), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hsup i hi
  have hdlb := normSq_iteratedCovGrad_deTurckLieCovariantDerivativeInsertionField_le (I := I) (M := M) g₀ g₁ g_bg i
  rw [norm_iteratedCovGrad_deTurckVectorFieldCovariantDerivativeEndomorphismInsert_eq_deTurckVectorFieldCovariantDerivativeLowered (I := I) (M := M) g₀ g₁ g_bg i] at hdlb
  have hwa := hwalpha g₁ P htie hδ_le hδ0 hδ hsup i hi
  calc ‖iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieCovariantDerivativeInsertionField (I := I) g₀ g₁ g_bg)‖ ^ 2
      ≤ 4 * (Module.finrank ℝ E : ℝ) *
          ‖iteratedCovGrad (I := I) g₀ 0 2 i (deTurckVectorFieldCovariantDerivativeLowered (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 := hdlb
    _ ≤ 4 * (Module.finrank ℝ E : ℝ) *
          (Kb_top * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 +
            Kb_flow i * (1 + ∑ j ∈ Finset.range (i + 3),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hwa h4fr_nn
    _ = 4 * (Module.finrank ℝ E : ℝ) * Kb_top *
            ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 +
          4 * (Module.finrank ℝ E : ℝ) * Kb_flow i * (1 + ∑ j ∈ Finset.range (i + 3),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by ring

theorem deTurckLieCoeffField_perOrder_l2_radiusFree
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    {Λ₀ : ℝ} (hΛ₀0 : 0 ≤ Λ₀) :
    ∃ Atop : ℕ → ℝ, (∀ i, 0 ≤ Atop i) ∧ ∃ Alow : ℕ → ℝ, (∀ i, 0 ≤ Alow i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        (_hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          ((ccTensor02Symm (I := I) (M := M) g₀ T).toSection x) ≤ Λ₀ ^ 2)
        (i : ℕ) (_hi : i ≤ a),
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
          Atop i * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2)
              (ccTensor02Symm (I := I) (M := M) g₀ T)‖ ^ 2 +
          Alow i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j (ccTensor02Symm (I := I) (M := M) g₀ T)‖ ^ 2) := by
  classical
  obtain ⟨Ka_top, hKa_top_nn, Ka_low, hKa_low_nn, hDLa⟩ :=
    exists_deTurckLieConnectionDifferenceDerivativeCoefficient_iteratedCovGrad_normSq_perOrder_radiusFree_bound (I := I) (M := M) g₀ g_bg hδ₀ hΛ₀0
  obtain ⟨Kb_top, hKb_top_nn, Kb_low, hKb_low_nn, hDLb⟩ :=
    exists_deTurckLieCovariantDerivativeInsertion_iteratedCovGrad_normSq_perOrder_radiusFree_bound (I := I) (M := M) g₀ g_bg a hδ₀ hΛ₀0
  refine ⟨fun i => 2 * Ka_top i + 2 * Kb_top + (2 * Ka_low i + 2 * Kb_low i),
    fun i => by
      have := hKa_top_nn i; have := hKb_top_nn; have := hKa_low_nn i; have := hKb_low_nn i
      linarith,
    fun i => 2 * Ka_low i + 2 * Kb_low i,
    fun i => by have := hKa_low_nn i; have := hKb_low_nn i; linarith, ?_⟩
  intro g₁ T δ hδ_le hδ0 hδ htie hsup i hi
  set P : SmoothCcTensor g₀ 0 2 := ccTensor02Symm (I := I) (M := M) g₀ T with hP_def
  have htie' : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w := by
    intro y v w
    rw [hP_def,
      DifferentialGeometry.Analysis.Spectral.ccTensorBilinSymm_ccTensor02Symm_apply
        (I := I) (M := M) g₀ T y v w]
    exact htie y v w
  have hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ := by
    rw [hP_def]
    exact DifferentialGeometry.Analysis.Spectral.gFibreOpBound_ccTensor02Symm
      (I := I) (M := M) g₀ T hδ
  have ha := hDLa g₁ P htie' hδ_le hδ0 hδ' hsup i
  have hb := hDLb g₁ P htie' hδ_le hδ0 hδ' hsup i hi
  have hcomb : ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
      2 * ‖iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieConnectionDifferenceDerivCoeffField (I := I) g₀ g₁ g_bg)‖ ^ 2 +
        2 * ‖iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieCovariantDerivativeInsertionField (I := I) g₀ g₁ g_bg)‖ ^ 2 := by
    have hgrad : iteratedCovGrad (I := I) g₀ 2 2 i
          (deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg)
        = iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieConnectionDifferenceDerivCoeffField (I := I) g₀ g₁ g_bg)
          + iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieCovariantDerivativeInsertionField (I := I) g₀ g₁ g_bg) := by
      rw [← deTurckLieConnectionDifferenceDerivCoeffField_add_deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g₀ g₁ g_bg,
        iteratedCovGrad_add]
    rw [hgrad]
    nlinarith only [norm_add_le
        (iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieConnectionDifferenceDerivCoeffField (I := I) g₀ g₁ g_bg))
        (iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieCovariantDerivativeInsertionField (I := I) g₀ g₁ g_bg)),
      norm_nonneg (iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieConnectionDifferenceDerivCoeffField (I := I) g₀ g₁ g_bg)),
      norm_nonneg (iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieCovariantDerivativeInsertionField (I := I) g₀ g₁ g_bg)),
      norm_nonneg (iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieConnectionDifferenceDerivCoeffField (I := I) g₀ g₁ g_bg)
          + iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieCovariantDerivativeInsertionField (I := I) g₀ g₁ g_bg)),
      sq_nonneg (‖iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieConnectionDifferenceDerivCoeffField (I := I) g₀ g₁ g_bg)‖ -
        ‖iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieCovariantDerivativeInsertionField (I := I) g₀ g₁ g_bg)‖)]
  have hsplit : (∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) =
      (∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) +
        ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 := by
    rw [show i + 3 = (i + 2) + 1 from rfl, Finset.sum_range_succ]
  rw [hsplit] at ha hb
  calc ‖iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2
      ≤ 2 * ‖iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieConnectionDifferenceDerivCoeffField (I := I) g₀ g₁ g_bg)‖ ^ 2 +
          2 * ‖iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieCovariantDerivativeInsertionField (I := I) g₀ g₁ g_bg)‖ ^ 2 :=
        hcomb
    _ ≤ 2 * (Ka_top i * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 +
            Ka_low i * (1 +
              ((∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) +
                ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2))) +
          2 * (Kb_top * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 +
            Kb_low i * (1 +
              ((∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) +
                ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2))) := by
        have h1 := mul_le_mul_of_nonneg_left ha (by norm_num : (0 : ℝ) ≤ 2)
        have h2 := mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 2)
        linarith [h1, h2]
    _ = (2 * Ka_top i + 2 * Kb_top + (2 * Ka_low i + 2 * Kb_low i)) *
          ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 +
        (2 * Ka_low i + 2 * Kb_low i) * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by ring

theorem deTurckLieCoeffField_summed_l2_radiusFree
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Klow : ℝ, 0 ≤ Klow ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w),
        ∑ i ∈ Finset.range (a + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
          Ktop * (∑ j ∈ Finset.range (a + 3),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j (ccTensor02Symm (I := I) (M := M) g₀ T)‖ ^ 2) +
          Klow * (1 + ∑ j ∈ Finset.range (a + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j (ccTensor02Symm (I := I) (M := M) g₀ T)‖ ^ 2) := by
  classical
  obtain ⟨Atop, hAtop_nn, Alow, hAlow_nn, hper⟩ :=
    deTurckLieCoeffField_perOrder_l2_radiusFree (I := I) (M := M) g₀ g_bg a hδ₀
      (Λ₀ := max 0 ((Module.finrank ℝ E : ℝ) * δ₀)) (le_max_left _ _)
  refine ⟨∑ i ∈ Finset.range (a + 1), Atop i,
    Finset.sum_nonneg (fun i _ => hAtop_nn i), ?_⟩
  refine ⟨∑ i ∈ Finset.range (a + 1), Alow i,
    Finset.sum_nonneg (fun i _ => hAlow_nn i), ?_⟩
  intro g₁ T δ hδ_le hδ htie
  by_cases hM : Nonempty M
  · obtain ⟨x₀⟩ := hM
    have hδ0 : 0 ≤ δ := by
      obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x₀, v ≠ 0 := by
        have : Nontrivial (TangentSpace I x₀) := by
          have hfr : 0 < Module.finrank ℝ (TangentSpace I x₀) := by
            have heq : Module.finrank ℝ (TangentSpace I x₀) = Module.finrank ℝ E := rfl
            rw [heq]; exact Nat.pos_of_ne_zero (NeZero.ne _)
          exact Module.nontrivial_of_finrank_pos hfr
        exact exists_ne 0
      have hpos : 0 < g₀.inner x₀ v v := g₀.pos x₀ v hv
      have hbound := hδ x₀ v v
      have hsqrt_pos : 0 < Real.sqrt (g₀.inner x₀ v v) := Real.sqrt_pos.mpr hpos
      have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀ T x₀ v v| := abs_nonneg _
      by_contra hδc
      have hδc' : δ < 0 := lt_of_not_ge hδc
      have hrhs_neg : δ * Real.sqrt (g₀.inner x₀ v v) * Real.sqrt (g₀.inner x₀ v v) < 0 := by
        have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 :=
          mul_neg_of_neg_of_pos hδc' hsqrt_pos
        exact mul_neg_of_neg_of_pos h1 hsqrt_pos
      linarith [le_trans habs_nn hbound]
    have hδ₀0 : 0 ≤ δ₀ := le_trans hδ0 hδ_le
    have hmaxeq : max 0 ((Module.finrank ℝ E : ℝ) * δ₀) = (Module.finrank ℝ E : ℝ) * δ₀ :=
      max_eq_right (mul_nonneg (Nat.cast_nonneg _) hδ₀0)
    have hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        ((ccTensor02Symm (I := I) (M := M) g₀ T).toSection x) ≤
        (max 0 ((Module.finrank ℝ E : ℝ) * δ₀)) ^ 2 := by
      intro x
      rw [hmaxeq]
      exact riemannianFiberNormSq_ccTensor02Symm_zero_le_fibreSmall (I := I) (M := M) g₀ hδ₀0 T hδ_le hδ0 hδ x
    have hper' : ∀ i, i ≤ a →
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
          Atop i * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2)
              (ccTensor02Symm (I := I) (M := M) g₀ T)‖ ^ 2 +
          Alow i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j (ccTensor02Symm (I := I) (M := M) g₀ T)‖ ^ 2) :=
      fun i hi => hper g₁ T hδ_le hδ0 hδ htie hsup i hi
    set w : ℕ → ℝ := fun j =>
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (ccTensor02Symm (I := I) (M := M) g₀ T)‖ ^ 2 with hw
    have hw_nn : ∀ j, 0 ≤ w j := fun j => sq_nonneg _
    calc ∑ i ∈ Finset.range (a + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2
        ≤ ∑ i ∈ Finset.range (a + 1),
            (Atop i * w (i + 2) + Alow i * (1 + ∑ j ∈ Finset.range (i + 2), w j)) := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          exact hper' i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
      _ = (∑ i ∈ Finset.range (a + 1), Atop i * w (i + 2)) +
            ∑ i ∈ Finset.range (a + 1), Alow i * (1 + ∑ j ∈ Finset.range (i + 2), w j) := by
          rw [Finset.sum_add_distrib]
      _ ≤ (∑ i ∈ Finset.range (a + 1), Atop i) * (∑ j ∈ Finset.range (a + 3), w j) +
            (∑ i ∈ Finset.range (a + 1), Alow i) * (1 + ∑ j ∈ Finset.range (a + 2), w j) := by
          refine add_le_add ?_ ?_
          · calc ∑ i ∈ Finset.range (a + 1), Atop i * w (i + 2)
                ≤ ∑ i ∈ Finset.range (a + 1), Atop i * (∑ j ∈ Finset.range (a + 3), w j) := by
                  refine Finset.sum_le_sum (fun i hi => ?_)
                  have hi' : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
                  refine mul_le_mul_of_nonneg_left ?_ (hAtop_nn i)
                  exact Finset.single_le_sum (f := fun j => w j) (fun j _ => hw_nn j)
                    (Finset.mem_range.mpr (by omega))
              _ = (∑ i ∈ Finset.range (a + 1), Atop i) * (∑ j ∈ Finset.range (a + 3), w j) := by
                  rw [Finset.sum_mul]
          · calc ∑ i ∈ Finset.range (a + 1), Alow i * (1 + ∑ j ∈ Finset.range (i + 2), w j)
                ≤ ∑ i ∈ Finset.range (a + 1),
                    Alow i * (1 + ∑ j ∈ Finset.range (a + 2), w j) := by
                  refine Finset.sum_le_sum (fun i hi => ?_)
                  have hi' : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
                  refine mul_le_mul_of_nonneg_left ?_ (hAlow_nn i)
                  have hsub : Finset.range (i + 2) ⊆ Finset.range (a + 2) := by
                    intro x hx; rw [Finset.mem_range] at hx ⊢; omega
                  have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hw_nn j)
                  linarith
              _ = (∑ i ∈ Finset.range (a + 1), Alow i) *
                    (1 + ∑ j ∈ Finset.range (a + 2), w j) := by
                  rw [Finset.sum_mul]
  · have hM' : IsEmpty M := not_nonempty_iff.mp hM
    have hL0 : ∑ i ∈ Finset.range (a + 1),
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 = 0 := by
      refine Finset.sum_eq_zero (fun i _ => ?_)
      have hz : ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg)‖ = 0 := by
        rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
          MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
      rw [hz]; ring
    rw [hL0]
    have h1 : 0 ≤ (∑ i ∈ Finset.range (a + 1), Atop i) *
        (∑ j ∈ Finset.range (a + 3),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j (ccTensor02Symm (I := I) (M := M) g₀ T)‖ ^ 2) :=
      mul_nonneg (Finset.sum_nonneg (fun i _ => hAtop_nn i))
        (Finset.sum_nonneg (fun j _ => sq_nonneg _))
    have h2 : 0 ≤ (∑ i ∈ Finset.range (a + 1), Alow i) *
        (1 + ∑ j ∈ Finset.range (a + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j (ccTensor02Symm (I := I) (M := M) g₀ T)‖ ^ 2) := by
      refine mul_nonneg (Finset.sum_nonneg (fun i _ => hAlow_nn i)) ?_
      have : 0 ≤ ∑ j ∈ Finset.range (a + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j (ccTensor02Symm (I := I) (M := M) g₀ T)‖ ^ 2 :=
        Finset.sum_nonneg (fun j _ => sq_nonneg _)
      linarith
    linarith

end Connection
end Integral
end DifferentialGeometry
