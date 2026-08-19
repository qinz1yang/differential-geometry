import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckVectorFieldEndomorphismInsertionBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.Lowered
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.ResidualFree

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Topology Bundle Manifold DifferentialGeometry.Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (metricPerturbationPath)
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

open DifferentialGeometry.Analysis.Spectral.DeTurck in
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert in
set_option backward.isDefEq.respectTransparency false in
theorem cometricCastG0_order0sup_jetL2_radiusFree
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (_ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    {Λ₀ : ℝ} (hΛ₀0 : 0 ≤ Λ₀) :
    ∃ (Λ : ℝ) (Flow : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ Flow i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ₀ ^ 2),
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 1 x
            ((cometricCastG0 (I := I) g₀ g₁).toSection x) ≤ Λ ^ 2) ∧
        ∀ (i : ℕ), i ≤ a + 1 →
          ∑ l ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 3 1 l (cometricCastG0 (I := I) g₀ g₁)‖ ^ 2 ≤
            Flow i * (1 + ∑ j ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  set Φ : SmoothCcTensor g₀ 3 1 := cometricDoubleTraceField (I := I) g₀ 1 with hΦ_def
  obtain ⟨C_base, hC_base_nn, hC_base⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_zero_metricComparisonDifferenceEndomorphismField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨K_rf, hK_rf_nn, hK_rf⟩ :=
    antidiagonalTupleGrid_integral_radiusFree (I := I) (M := M) g₀ hΛ₀0
  have hSΦ_ex : ∀ i : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 3 1 i Φ).toSection x) ≤ K :=
    fun i => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 3 (1 + i)
      (iteratedCovGrad (I := I) g₀ 3 1 i Φ)
  choose SΦ hSΦ_nn hSΦ using hSΦ_ex
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  set KW_rf : ℕ → ℝ := fun q => fr ^ 2 * C_base q * K_rf q with hKW_def
  have hKW_nn : ∀ q, 0 ≤ KW_rf q := by
    intro q; simp only [hKW_def]
    exact mul_nonneg (mul_nonneg (sq_nonneg fr) (hC_base_nn q)) (hK_rf_nn q)
  set aL : ℕ → ℝ := fun l => ‖iteratedCovGrad (I := I) g₀ 3 1 l Φ‖ ^ 2 with haL_def
  set kd : ℕ → ℝ := fun l => operatorFieldApplicationGdiag (E := E) l *
    (∑ i' ∈ Finset.range (l + 1), SΦ i') * (∑ q ∈ Finset.range (l + 1), KW_rf q) with hkd_def
  have hkd_nn : ∀ l, 0 ≤ kd l := by
    intro l; simp only [hkd_def]
    exact mul_nonneg (mul_nonneg (operatorFieldApplicationGdiag_nonneg _)
      (Finset.sum_nonneg (fun i' _ => hSΦ_nn i'))) (Finset.sum_nonneg (fun q _ => hKW_nn q))
  set ΛT2 : ℝ := fr ^ 2 * C_base 0 with hΛT2_def
  have hΛT2_nn : 0 ≤ ΛT2 := by rw [hΛT2_def]; exact mul_nonneg (sq_nonneg fr) (hC_base_nn 0)
  refine ⟨Real.sqrt (2 * SΦ 0 + 2 * (SΦ 0 * ΛT2)),
    fun i => ∑ l ∈ Finset.range (i + 1), (2 * aL l + 2 * kd l), Real.sqrt_nonneg _,
    fun i => Finset.sum_nonneg (fun l _ => by
      have h1 : 0 ≤ aL l := by simp only [haL_def]; positivity
      have h2 : 0 ≤ kd l := hkd_nn l
      linarith), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hsup
  set W : SmoothCcTensor g₀ 3 3 :=
    endoSlotZeroCcTensor (I := I) (M := M) g₀ 2
      (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁) with hW_def
  have hid : cometricCastG0 (I := I) g₀ g₁ =
      Φ + ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W := by
    have h := cometricCastG0_eq_doubleTrace_add_ccOperatorFieldComp (I := I) g₀ g₁
    rw [← hΦ_def, ← hW_def] at h
    exact h
  have hΛT : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 3 x (W.toSection x) ≤ ΛT2 := by
    intro x
    have h1 := riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) g₀ 2
      (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁) 0 x
    simp only [iteratedCovGrad_zero] at h1
    rw [← hW_def, ← hfr_def] at h1
    have h2 := hC_base g₁ P htie hδ_le hδ0 hδ 0 x
    simp only [iteratedCovGrad_zero] at h2
    have hgrid0 : (∑ n ∈ Finset.range (0 + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n 0,
        ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) = 1 := by simp
    rw [hgrid0, mul_one] at h2
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 3 3 x (W.toSection x)
        ≤ fr ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
            ((slotInsertEndoCc (I := I) (M := M) g₀ 0
              (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)).toSection x) := h1
      _ ≤ fr ^ 2 * C_base 0 := mul_le_mul_of_nonneg_left h2 (sq_nonneg fr)
      _ = ΛT2 := hΛT2_def.symm
  have hstep2 : ∀ q : ℕ,
      ‖iteratedCovGrad (I := I) g₀ 3 3 q W‖ ^ 2 ≤
        KW_rf q * (1 + ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2) := by
    intro q
    have hpt : ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + q) x
            ((iteratedCovGrad (I := I) g₀ 3 3 q W).toSection x) ≤
          fr ^ 2 * C_base q *
            (∑ n ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n q,
              ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) := by
      intro x
      have h1 := riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) g₀ 2
        (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁) q x
      rw [← hW_def, ← hfr_def] at h1
      have h2 := hC_base g₁ P htie hδ_le hδ0 hδ q x
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + q) x
            ((iteratedCovGrad (I := I) g₀ 3 3 q W).toSection x)
          ≤ fr ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + q) x
              ((iteratedCovGrad (I := I) g₀ 1 1 q
                (slotInsertEndoCc (I := I) (M := M) g₀ 0
                  (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁))).toSection x) := h1
        _ ≤ fr ^ 2 * (C_base q *
              (∑ n ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n q,
                ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))) :=
              mul_le_mul_of_nonneg_left h2 (sq_nonneg fr)
        _ = fr ^ 2 * C_base q *
              (∑ n ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n q,
                ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) := by ring
    obtain ⟨hgi, hgb⟩ := hK_rf P hsup q
    have hint : MeasureTheory.Integrable
        (fun x => fr ^ 2 * C_base q *
          (∑ n ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n q,
            ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) := hgi.const_mul _
    have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 3 (3 + q)
      (iteratedCovGrad (I := I) g₀ 3 3 q W) _ hint hpt
    refine le_trans hkey ?_
    rw [MeasureTheory.integral_const_mul]
    rw [hKW_def]
    calc fr ^ 2 * C_base q *
          (∫ x, ∑ n ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n q,
            ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
        ≤ fr ^ 2 * C_base q * (K_rf q * (1 + ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hgb (mul_nonneg (sq_nonneg fr) (hC_base_nn q))
      _ = fr ^ 2 * C_base q * K_rf q * (1 + ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2) := by ring
  refine ⟨?_, ?_⟩
  · intro x
    rw [Real.sq_sqrt (by
      have := hSΦ_nn 0
      have := mul_nonneg (hSΦ_nn 0) hΛT2_nn
      linarith : (0 : ℝ) ≤ 2 * SΦ 0 + 2 * (SΦ 0 * ΛT2))]
    rw [hid, SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 3 1 x
      (Φ.toSection x) ((ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W).toSection x)) ?_
    have hΦ0 : riemannianFiberNormSq (I := I) (M := M) g₀ 3 1 x (Φ.toSection x) ≤ SΦ 0 := by
      have h := hSΦ 0 x
      simp only [iteratedCovGrad_zero] at h
      exact h
    have hDIFF0 : riemannianFiberNormSq (I := I) (M := M) g₀ 3 1 x
        ((ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W).toSection x) ≤ SΦ 0 * ΛT2 := by
      refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 3 3 1 x
        (Φ.toSection x) (W.toSection x)) ?_
      exact mul_le_mul hΦ0 (hΛT x) (riemannianFiberNormSq_nonneg _ _ _ _ _) (hSΦ_nn 0)
    linarith
  · intro i hi
    set S : ℝ := ∑ j ∈ Finset.range (i + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 with hS_def
    have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hstep3 : ∀ l : ℕ, l ≤ i →
        ‖iteratedCovGrad (I := I) g₀ 3 1 l (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W)‖ ^ 2 ≤
          kd l * (1 + S) := by
      intro l hl
      have hpt : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + l) x
              ((iteratedCovGrad (I := I) g₀ 3 1 l
                (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W)).toSection x) ≤
            (operatorFieldApplicationGdiag (E := E) l * (∑ i' ∈ Finset.range (l + 1), SΦ i')) *
              (∑ q ∈ Finset.range (l + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + q) x
                  ((iteratedCovGrad (I := I) g₀ 3 3 q W).toSection x)) := by
        intro x
        refine le_trans (riemannianFiberNormSq_iteratedCovGrad_operatorFieldComposition_diagonalProductGrid_rankLeft_le
          (I := I) (M := M) g₀ l 3 3 1 Φ W x) ?_
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (operatorFieldApplicationGdiag_nonneg _)
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum (fun i' _ => ?_)
        refine mul_le_mul (hSΦ i' x) ?_
          (Finset.sum_nonneg (fun q _ => riemannianFiberNormSq_nonneg _ _ _ _ _)) (hSΦ_nn i')
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_
          (fun q _ _ => riemannianFiberNormSq_nonneg _ _ _ _ _)
        intro q hq
        rw [Finset.mem_range] at hq ⊢
        omega
      have hint : MeasureTheory.Integrable
          (fun x => (operatorFieldApplicationGdiag (E := E) l * (∑ i' ∈ Finset.range (l + 1), SΦ i')) *
            (∑ q ∈ Finset.range (l + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + q) x
                ((iteratedCovGrad (I := I) g₀ 3 3 q W).toSection x)))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
        apply MeasureTheory.Integrable.const_mul
        apply MeasureTheory.integrable_finset_sum
        intro q _
        exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 3 (3 + q)
          (iteratedCovGrad (I := I) g₀ 3 3 q W)
      have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 3 (1 + l)
        (iteratedCovGrad (I := I) g₀ 3 1 l (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W)) _ hint hpt
      refine le_trans hkey ?_
      rw [MeasureTheory.integral_const_mul,
        MeasureTheory.integral_finset_sum _ (fun q _ =>
          integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 3 (3 + q)
            (iteratedCovGrad (I := I) g₀ 3 3 q W))]
      have hconv : ∀ q ∈ Finset.range (l + 1),
          (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + q) x
              ((iteratedCovGrad (I := I) g₀ 3 3 q W).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
          ‖iteratedCovGrad (I := I) g₀ 3 3 q W‖ ^ 2 := by
        intro q _
        rw [SmoothCcTensor.norm_def,
          tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 3 (3 + q)
            (iteratedCovGrad (I := I) g₀ 3 3 q W)]
      rw [Finset.sum_congr rfl hconv]
      have hWsum : (∑ q ∈ Finset.range (l + 1), ‖iteratedCovGrad (I := I) g₀ 3 3 q W‖ ^ 2) ≤
          (∑ q ∈ Finset.range (l + 1), KW_rf q) * (1 + S) := by
        calc (∑ q ∈ Finset.range (l + 1), ‖iteratedCovGrad (I := I) g₀ 3 3 q W‖ ^ 2)
            ≤ ∑ q ∈ Finset.range (l + 1),
                KW_rf q * (1 + ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2) :=
              Finset.sum_le_sum (fun q _ => hstep2 q)
          _ ≤ ∑ q ∈ Finset.range (l + 1), KW_rf q * (1 + S) := by
              refine Finset.sum_le_sum (fun q hq => ?_)
              refine mul_le_mul_of_nonneg_left ?_ (hKW_nn q)
              have hqle : q ≤ i := le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)) hl
              have hjmem : ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2 ≤ S :=
                Finset.single_le_sum (f := fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)
                  (fun j _ => sq_nonneg _) (Finset.mem_range.mpr (by omega))
              linarith
          _ = (∑ q ∈ Finset.range (l + 1), KW_rf q) * (1 + S) := by rw [Finset.sum_mul]
      calc (operatorFieldApplicationGdiag (E := E) l * (∑ i' ∈ Finset.range (l + 1), SΦ i')) *
            (∑ q ∈ Finset.range (l + 1), ‖iteratedCovGrad (I := I) g₀ 3 3 q W‖ ^ 2)
          ≤ (operatorFieldApplicationGdiag (E := E) l * (∑ i' ∈ Finset.range (l + 1), SΦ i')) *
              ((∑ q ∈ Finset.range (l + 1), KW_rf q) * (1 + S)) :=
            mul_le_mul_of_nonneg_left hWsum
              (mul_nonneg (operatorFieldApplicationGdiag_nonneg _) (Finset.sum_nonneg (fun i' _ => hSΦ_nn i')))
        _ = kd l * (1 + S) := by rw [hkd_def]; ring
    have hterm : ∀ l ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 3 1 l (cometricCastG0 (I := I) g₀ g₁)‖ ^ 2 ≤
          (2 * aL l + 2 * kd l) * (1 + S) := by
      intro l hl
      have hl_i : l ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
      rw [hid, iteratedCovGrad_add]
      have hKDl := hstep3 l hl_i
      have haLl : aL l = ‖iteratedCovGrad (I := I) g₀ 3 1 l Φ‖ ^ 2 := by simp only [haL_def]
      have hkd_l_nn : 0 ≤ kd l := hkd_nn l
      have haL_l_nn : 0 ≤ aL l := by simp only [haL_def]; positivity
      have hsq := pow_le_pow_left₀ (norm_nonneg (iteratedCovGrad (I := I) g₀ 3 1 l Φ +
          iteratedCovGrad (I := I) g₀ 3 1 l (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W)))
        (norm_add_le (iteratedCovGrad (I := I) g₀ 3 1 l Φ)
          (iteratedCovGrad (I := I) g₀ 3 1 l (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W))) 2
      nlinarith [hsq, hKDl, haLl, hS_nn, hkd_l_nn, haL_l_nn,
        sq_nonneg (‖iteratedCovGrad (I := I) g₀ 3 1 l Φ‖ -
          ‖iteratedCovGrad (I := I) g₀ 3 1 l (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W)‖),
        mul_nonneg hkd_l_nn hS_nn, mul_nonneg haL_l_nn hS_nn]
    calc ∑ l ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 3 1 l (cometricCastG0 (I := I) g₀ g₁)‖ ^ 2
        ≤ ∑ l ∈ Finset.range (i + 1), (2 * aL l + 2 * kd l) * (1 + S) :=
          Finset.sum_le_sum hterm
      _ = (∑ l ∈ Finset.range (i + 1), (2 * aL l + 2 * kd l)) * (1 + S) := by rw [Finset.sum_mul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma metricComparisonEndomorphism_self_rf (g₀ : SmoothRiemannianMetric I M) (x : M) :
    metricComparisonEndomorphism (I := I) g₀ g₀ x =
      ContinuousLinearMap.id ℝ (TangentSpace I x) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [metricComparisonEndomorphism_apply, inverseMetricSharpFib_g0FlatCLM, ContinuousLinearMap.id_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma metricComparisonEndomorphismField_decomp_rf (g₀ g₁ : SmoothRiemannianMetric I M) :
    metricComparisonEndomorphismField (I := I) (M := M) g₀ g₁ =
      metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁ +
        metricComparisonEndomorphismField (I := I) (M := M) g₀ g₀ := by
  apply ContMDiffSection.ext
  intro x
  rw [show ((metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁ +
        metricComparisonEndomorphismField (I := I) (M := M) g₀ g₀) x) =
      metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁ x +
        metricComparisonEndomorphismField (I := I) (M := M) g₀ g₀ x from by
    rw [ContMDiffSection.coe_add]; rfl]
  apply ContinuousLinearMap.ext
  intro v
  rw [metricComparisonEndomorphismField_apply, ContinuousLinearMap.add_apply]
  rw [show (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁ x) =
      metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x from rfl]
  rw [metricComparisonEndomorphismField_apply, metricComparisonEndomorphism_self_rf, ContinuousLinearMap.id_apply]
  rw [metricComparisonEndomorphism_eq_diff_add_id]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma slotInsertEndoCc_add_rf (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    slotInsertEndoCc (I := I) (M := M) g₀ s (A + B) =
      slotInsertEndoCc (I := I) (M := M) g₀ s A +
        slotInsertEndoCc (I := I) (M := M) g₀ s B := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((slotInsertEndoCc (I := I) (M := M) g₀ s A +
        slotInsertEndoCc (I := I) (M := M) g₀ s B).toSection x) =
      (slotInsertEndoCc (I := I) (M := M) g₀ s A).toSection x +
        (slotInsertEndoCc (I := I) (M := M) g₀ s B).toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [ContinuousLinearMap.add_apply]
  simp only [slotInsertEndoCc_toSection]
  rw [show ((A + B) x) = A x + B x from by rw [ContMDiffSection.coe_add]; rfl]
  rw [slotInsertEndoFib_add_left, ContinuousLinearMap.add_apply]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma sharpFlatEndoCc_eq_insert_fullRaised_rf (g₀ g₁ : SmoothRiemannianMetric I M) :
    sharpFlatEndoCc (I := I) g₀ g₁ =
      slotInsertEndoCc (I := I) (M := M) g₀ 0
        (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext 1 1 x
  intro om
  apply cotangentToDualLinear_injective (I := I) (x := x)
  apply LinearMap.ext
  intro w
  rw [cotangentToDualLinear_apply, cotangentToDualLinear_apply]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₁)).toSection x) om =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (metricComparisonEndomorphism (I := I) g₀ g₁ x) om from rfl]
  rw [cotangentToDual_slotInsertEndoFib' (I := I) (M := M) x
    (metricComparisonEndomorphism (I := I) g₀ g₁ x) om w]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (sharpFlatEndoCc (I := I) g₀ g₁).toSection x) om =
      g0FlatCLM (I := I) g₀ x (inverseMetricSharpFib (I := I) g₁ x om) from rfl]
  rw [cotangentToDual_g0FlatCLM]
  rw [show cotangentToDual (I := I) om (metricComparisonEndomorphism (I := I) g₀ g₁ x w) =
      g₁.inner x (inverseMetricSharpFib (I := I) g₁ x om)
        (metricComparisonEndomorphism (I := I) g₀ g₁ x w) from by
    rw [← cotangentToDualLinear_apply]
    exact (inverseMetricSharpFib_inner (I := I) g₁ x om
      (metricComparisonEndomorphism (I := I) g₀ g₁ x w)).symm]
  rw [show metricComparisonEndomorphism (I := I) g₀ g₁ x w =
      inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x w) from by
    rw [metricComparisonEndomorphism_apply]]
  rw [g₁.symm x (inverseMetricSharpFib (I := I) g₁ x om)
    (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x w))]
  rw [inverseMetricSharpFib_inner (I := I) g₁ x (g0FlatCLM (I := I) g₀ x w)
    (inverseMetricSharpFib (I := I) g₁ x om)]
  rw [cotangentToDualLinear_apply, cotangentToDual_g0FlatCLM]
  rw [g₀.symm x w (inverseMetricSharpFib (I := I) g₁ x om)]

set_option backward.isDefEq.respectTransparency false in
theorem sharpFlatEndoCc_lowOrder_jetL2_radiusFree
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (_ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    {Λ₀ : ℝ} (hΛ₀0 : 0 ≤ Λ₀) :
    ∃ (Λ : ℝ) (Flow : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ Flow i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ₀ ^ 2),
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
            ((sharpFlatEndoCc (I := I) g₀ g₁).toSection x) ≤ Λ ^ 2) ∧
        ∀ (i : ℕ), i ≤ a + 1 →
          ∑ q ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 1 1 q (sharpFlatEndoCc (I := I) g₀ g₁)‖ ^ 2 ≤
            Flow i * (1 + ∑ j ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  set IdIns : SmoothCcTensor g₀ 1 1 :=
    slotInsertEndoCc (I := I) (M := M) g₀ 0
      (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₀) with hIdIns_def
  obtain ⟨C_base, hC_base_nn, hC_base⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_zero_metricComparisonDifferenceEndomorphismField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨K_rf, hK_rf_nn, hK_rf⟩ :=
    antidiagonalTupleGrid_integral_radiusFree (I := I) (M := M) g₀ hΛ₀0
  have hSId_ex : ∀ n : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 1 n IdIns).toSection x) ≤ K :=
    fun n => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 1 (1 + n)
      (iteratedCovGrad (I := I) g₀ 1 1 n IdIns)
  choose SId hSId_nn hSId using hSId_ex
  set KW : ℕ → ℝ := fun q => C_base q * K_rf q with hKW_def
  have hKW_nn : ∀ q, 0 ≤ KW q := fun q => mul_nonneg (hC_base_nn q) (hK_rf_nn q)
  set FId : ℕ → ℝ := fun q => ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖ ^ 2 with hFId_def
  have hFId_nn : ∀ q, 0 ≤ FId q := fun q => sq_nonneg _
  refine ⟨Real.sqrt (2 * C_base 0 + 2 * SId 0),
    fun i => ∑ q ∈ Finset.range (i + 1), (2 * KW q + 2 * FId q), Real.sqrt_nonneg _,
    fun i => Finset.sum_nonneg (fun q _ => by
      have := hKW_nn q; have := hFId_nn q; linarith), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hsup
  set DiffIns : SmoothCcTensor g₀ 1 1 :=
    slotInsertEndoCc (I := I) (M := M) g₀ 0
      (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁) with hDiffIns_def
  have hdecomp : sharpFlatEndoCc (I := I) g₀ g₁ = DiffIns + IdIns := by
    rw [sharpFlatEndoCc_eq_insert_fullRaised_rf (I := I) (M := M) g₀ g₁,
      metricComparisonEndomorphismField_decomp_rf (I := I) (M := M) g₀ g₁,
      slotInsertEndoCc_add_rf (I := I) (M := M) g₀ 0]
  have hDiff_pt : ∀ (n : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 1 n DiffIns).toSection x) ≤
        C_base n *
          (∑ m ∈ Finset.range (n + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple m n,
            ∏ k : Fin m, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e k) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e k) P).toSection x)) := by
    intro n x
    have h2 := hC_base g₁ P htie hδ_le hδ0 hδ n x
    simpa only [hDiffIns_def] using h2
  have hDiff2 : ∀ q : ℕ,
      ‖iteratedCovGrad (I := I) g₀ 1 1 q DiffIns‖ ^ 2 ≤
        KW q * (1 + ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2) := by
    intro q
    obtain ⟨hgi, hgb⟩ := hK_rf P hsup q
    have hint : MeasureTheory.Integrable
        (fun x => C_base q *
          (∑ m ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple m q,
            ∏ k : Fin m, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e k) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e k) P).toSection x)))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) := hgi.const_mul _
    have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀
      1 (1 + q) (iteratedCovGrad (I := I) g₀ 1 1 q DiffIns) _ hint (fun x => hDiff_pt q x)
    refine le_trans hkey ?_
    rw [MeasureTheory.integral_const_mul, hKW_def]
    calc C_base q *
          (∫ x, ∑ m ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple m q,
            ∏ k : Fin m, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e k) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e k) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
        ≤ C_base q * (K_rf q * (1 + ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hgb (hC_base_nn q)
      _ = C_base q * K_rf q * (1 + ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2) := by ring
  refine ⟨?_, ?_⟩
  · intro x
    rw [Real.sq_sqrt (by have := hC_base_nn 0; have := hSId_nn 0; linarith :
      (0 : ℝ) ≤ 2 * C_base 0 + 2 * SId 0)]
    rw [hdecomp, SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 1 x
      (DiffIns.toSection x) (IdIns.toSection x)) ?_
    have hD0 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (DiffIns.toSection x) ≤
        C_base 0 := by
      have h := hDiff_pt 0 x
      simp only [iteratedCovGrad_zero] at h
      have hgrid0 : (∑ m ∈ Finset.range (0 + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple m 0,
          ∏ k : Fin m, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e k) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e k) P).toSection x)) = 1 := by simp
      rw [hgrid0, mul_one] at h
      exact h
    have hI0 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (IdIns.toSection x) ≤ SId 0 := by
      have h := hSId 0 x
      simp only [iteratedCovGrad_zero] at h
      exact h
    linarith
  · intro i hi
    set S : ℝ := ∑ j ∈ Finset.range (i + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 with hS_def
    have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hterm : ∀ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 1 1 q (sharpFlatEndoCc (I := I) g₀ g₁)‖ ^ 2 ≤
          (2 * KW q + 2 * FId q) * (1 + S) := by
      intro q hq
      have hq_i : q ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
      rw [hdecomp, iteratedCovGrad_add]
      have hDq := hDiff2 q
      have hFIdq : FId q = ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖ ^ 2 := by simp only [hFId_def]
      have hKW_q_nn : 0 ≤ KW q := hKW_nn q
      have hFId_q_nn : 0 ≤ FId q := hFId_nn q
      have hPqS : ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2 ≤ S :=
        Finset.single_le_sum (f := fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)
          (fun j _ => sq_nonneg _) (Finset.mem_range.mpr (by omega))
      have hsq := pow_le_pow_left₀ (norm_nonneg (iteratedCovGrad (I := I) g₀ 1 1 q DiffIns +
          iteratedCovGrad (I := I) g₀ 1 1 q IdIns))
        (norm_add_le (iteratedCovGrad (I := I) g₀ 1 1 q DiffIns)
          (iteratedCovGrad (I := I) g₀ 1 1 q IdIns)) 2
      nlinarith [hsq, hDq, hFIdq, hKW_q_nn, hFId_q_nn, hS_nn, hPqS,
        sq_nonneg (‖iteratedCovGrad (I := I) g₀ 1 1 q DiffIns‖ -
          ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖),
        mul_nonneg hKW_q_nn hS_nn, mul_nonneg hFId_q_nn hS_nn]
    calc ∑ q ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 1 1 q (sharpFlatEndoCc (I := I) g₀ g₁)‖ ^ 2
        ≤ ∑ q ∈ Finset.range (i + 1), (2 * KW q + 2 * FId q) * (1 + S) :=
          Finset.sum_le_sum hterm
      _ = (∑ q ∈ Finset.range (i + 1), (2 * KW q + 2 * FId q)) * (1 + S) := by rw [Finset.sum_mul]

theorem connectionDifferenceSection_lowOrder_jetL2_radiusFree
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (_ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    {Λ₀ : ℝ} (hΛ₀0 : 0 ≤ Λ₀) :
    ∃ Flow : ℕ → ℝ, (∀ i, 0 ≤ Flow i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ₀ ^ 2),
        ∀ (i : ℕ), i ≤ a + 1 →
          ∑ q ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 1 2 q (connectionDifferenceSection (I := I) g₁ g₀)‖ ^ 2 ≤
            Flow i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨Kt0, hKt0_nn, Kc0, hKc0_nn, hbot⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_connectionDifferenceSection_topOrderSeparated_le (I := I) (M := M) g₀ hδ₀
  obtain ⟨K_rf, hK_rf_nn, hK_rf⟩ :=
    antidiagonalTupleGrid_integral_radiusFree (I := I) (M := M) g₀ hΛ₀0
  set D : ℕ → ℝ := fun q => (2 * Kt0 + 2 * Kc0 q * (q : ℝ)) * K_rf (q + 1) with hD_def
  have hD_nn : ∀ q, 0 ≤ D q := by
    intro q; simp only [hD_def]
    have := hKt0_nn; have := hKc0_nn q; have := hK_rf_nn (q + 1); positivity
  refine ⟨fun i => ∑ q ∈ Finset.range (i + 1), D q,
    fun i => Finset.sum_nonneg (fun q _ => hD_nn q), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hsup i hi
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
        = (fun x => ∑ n ∈ Finset.range (k + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
            ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) := by
      funext x; rw [Combinatorics.antidiagonalTupleGrid]
    rw [hExpand]; exact hK_rf P hsup k
  have hL2 : ∀ q : ℕ,
      ‖iteratedCovGrad (I := I) g₀ 1 2 q (connectionDifferenceSection (I := I) g₁ g₀)‖ ^ 2 ≤
        D q * (1 + ‖iteratedCovGrad (I := I) g₀ 0 2 (q + 1) P‖ ^ 2) := by
    intro q
    have hpt : ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + q) x
            ((iteratedCovGrad (I := I) g₀ 1 2 q (connectionDifferenceSection (I := I) g₁ g₀)).toSection x) ≤
          (2 * Kt0 + 2 * Kc0 q * (q : ℝ)) * Combinatorics.antidiagonalTupleGrid
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (q + 1) := by
      intro x
      set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
      have hb : ∀ l, 0 ≤ b l :=
        fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
      have heng := hbot g₁ P htie hδ_le hδ0 hδ q x
      set Hd : SmoothCcTensor g₀ 1 (2 + q) :=
        ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 (2 + q)
          (iteratedCovGrad (I := I) g₀ 1 2 q (raisedKoszul (I := I) g₀ g₁))
          (sharpFlatEndoCc (I := I) g₀ g₁) with hHd_def
      have hbq1_grid : b (q + 1) ≤ Combinatorics.antidiagonalTupleGrid b (q + 1) := by
        have hsf := Combinatorics.single_factor_mul_antidiagonalTupleGrid_le b hb 0 (q + 1)
          (by omega)
        rwa [Combinatorics.antidiagonalTupleGrid_zero, mul_one, Nat.zero_add] at hsf
      have hrem_fold : (∑ k ∈ Finset.range q,
            b (q - k) * Combinatorics.antidiagonalTupleGrid b (k + 1)) ≤
          (q : ℝ) * Combinatorics.antidiagonalTupleGrid b (q + 1) := by
        calc (∑ k ∈ Finset.range q,
              b (q - k) * Combinatorics.antidiagonalTupleGrid b (k + 1))
            ≤ ∑ _k ∈ Finset.range q, Combinatorics.antidiagonalTupleGrid b (q + 1) := by
              refine Finset.sum_le_sum (fun k hk => ?_)
              rw [Finset.mem_range] at hk
              have hsf := Combinatorics.single_factor_mul_antidiagonalTupleGrid_le b hb
                (k + 1) (q - k) (by omega)
              rwa [show (k + 1) + (q - k) = q + 1 from by omega] at hsf
          _ = (q : ℝ) * Combinatorics.antidiagonalTupleGrid b (q + 1) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hsplit_eq :
          (iteratedCovGrad (I := I) g₀ 1 2 q (connectionDifferenceSection (I := I) g₁ g₀)).toSection x =
            Hd.toSection x +
              (iteratedCovGrad (I := I) g₀ 1 2 q (connectionDifferenceSection (I := I) g₁ g₀) -
                Hd).toSection x := by
        simp only [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]; abel
      rw [hsplit_eq]
      refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (2 + q) x
        (Hd.toSection x) _) ?_
      have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + q) x (Hd.toSection x) ≤
          Kt0 * Combinatorics.antidiagonalTupleGrid b (q + 1) :=
        le_trans heng.1 (mul_le_mul_of_nonneg_left hbq1_grid hKt0_nn)
      have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + q) x
          ((iteratedCovGrad (I := I) g₀ 1 2 q (connectionDifferenceSection (I := I) g₁ g₀) -
            Hd).toSection x) ≤
          Kc0 q * ((q : ℝ) * Combinatorics.antidiagonalTupleGrid b (q + 1)) :=
        le_trans heng.2 (mul_le_mul_of_nonneg_left hrem_fold (hKc0_nn q))
      have hgrid_nn : 0 ≤ Combinatorics.antidiagonalTupleGrid b (q + 1) :=
        Combinatorics.antidiagonalTupleGrid_nonneg b hb (q + 1)
      nlinarith [h1, h2, hgrid_nn, hKc0_nn q, hKt0_nn]
    obtain ⟨hAGint, hAGbd⟩ := hAG (q + 1)
    have hFint := hAGint.const_mul (2 * Kt0 + 2 * Kc0 q * (q : ℝ))
    have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 1 (2 + q)
      (iteratedCovGrad (I := I) g₀ 1 2 q (connectionDifferenceSection (I := I) g₁ g₀)) _ hFint hpt
    rw [MeasureTheory.integral_const_mul] at hkey
    refine le_trans hkey ?_
    rw [hD_def]
    calc (2 * Kt0 + 2 * Kc0 q * (q : ℝ)) *
          (∫ x, Combinatorics.antidiagonalTupleGrid
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (q + 1)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
        ≤ (2 * Kt0 + 2 * Kc0 q * (q : ℝ)) *
            (K_rf (q + 1) * (1 + ‖iteratedCovGrad (I := I) g₀ 0 2 (q + 1) P‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hAGbd
            (by have := hKt0_nn; have := hKc0_nn q; positivity)
      _ = (2 * Kt0 + 2 * Kc0 q * (q : ℝ)) * K_rf (q + 1) *
            (1 + ‖iteratedCovGrad (I := I) g₀ 0 2 (q + 1) P‖ ^ 2) := by ring
  set S' : ℝ := ∑ j ∈ Finset.range (i + 2),
    ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 with hS'_def
  have hS'_nn : 0 ≤ S' := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  calc ∑ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 1 2 q (connectionDifferenceSection (I := I) g₁ g₀)‖ ^ 2
      ≤ ∑ q ∈ Finset.range (i + 1),
          D q * (1 + ‖iteratedCovGrad (I := I) g₀ 0 2 (q + 1) P‖ ^ 2) :=
        Finset.sum_le_sum (fun q _ => hL2 q)
    _ ≤ ∑ q ∈ Finset.range (i + 1), D q * (1 + S') := by
        refine Finset.sum_le_sum (fun q hq => ?_)
        refine mul_le_mul_of_nonneg_left ?_ (hD_nn q)
        have hqle : q + 1 < i + 2 := by have := Finset.mem_range.mp hq; omega
        have : ‖iteratedCovGrad (I := I) g₀ 0 2 (q + 1) P‖ ^ 2 ≤ S' :=
          Finset.single_le_sum (f := fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)
            (fun j _ => sq_nonneg _) (Finset.mem_range.mpr hqle)
        linarith
    _ = (∑ q ∈ Finset.range (i + 1), D q) * (1 + S') := by rw [Finset.sum_mul]

theorem metricLoweredConnectionDifference_lowOrder_iteratedCovGrad_norm_sq_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    {Λ₀ : ℝ} (hΛ₀0 : 0 ≤ Λ₀) :
    ∃ Flow : ℕ → ℝ, (∀ i, 0 ≤ Flow i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ₀ ^ 2),
        ∀ (i : ℕ), i ≤ a + 1 →
          ∑ q ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 3 q (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
            Flow i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨Flow_cd, hFcd_nn, hcd⟩ :=
    connectionDifferenceSection_lowOrder_jetL2_radiusFree (I := I) (M := M) g₀ a ha_super hδ₀ hΛ₀0
  set FBackground : ℕ → ℝ := fun q =>
    ‖iteratedCovGrad (I := I) g₀ 0 3 q (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g_bg)‖ ^ 2 with hFBackground_def
  have hFBackground_nn : ∀ q, 0 ≤ FBackground q := fun q => sq_nonneg _
  refine ⟨fun i => 2 * Flow_cd i + 2 * ∑ q ∈ Finset.range (i + 1), FBackground q,
    fun i => by
      have := hFcd_nn i
      have : 0 ≤ ∑ q ∈ Finset.range (i + 1), FBackground q := Finset.sum_nonneg (fun q _ => hFBackground_nn q)
      positivity, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hsup i hi
  set S' : ℝ := ∑ j ∈ Finset.range (i + 2),
    ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 with hS'_def
  have hS'_nn : 0 ≤ S' := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hper : ∀ q : ℕ,
      ‖iteratedCovGrad (I := I) g₀ 0 3 q (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
        2 * ‖iteratedCovGrad (I := I) g₀ 0 3 q (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)‖ ^ 2 +
          2 * ‖iteratedCovGrad (I := I) g₀ 0 3 q (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g_bg)‖ ^ 2 := by
    intro q
    have htri : ‖iteratedCovGrad (I := I) g₀ 0 3 q (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)‖ ≤
        ‖iteratedCovGrad (I := I) g₀ 0 3 q (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)‖ +
          ‖iteratedCovGrad (I := I) g₀ 0 3 q (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g_bg)‖ := by
      rw [metricLoweredConnectionDifference, iteratedCovGrad_sub]
      exact norm_sub_le _ _
    nlinarith [htri, norm_nonneg (iteratedCovGrad (I := I) g₀ 0 3 q (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)),
      norm_nonneg (iteratedCovGrad (I := I) g₀ 0 3 q (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)),
      norm_nonneg (iteratedCovGrad (I := I) g₀ 0 3 q (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g_bg)),
      sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 3 q (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)‖ -
        ‖iteratedCovGrad (I := I) g₀ 0 3 q (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g_bg)‖)]
  have hg1 : (∑ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 3 q (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)‖ ^ 2) ≤
      Flow_cd i * (1 + S') := by
    have hcongr : (∑ q ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 3 q (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)‖ ^ 2) =
        ∑ q ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 1 2 q (connectionDifferenceSection (I := I) g₁ g₀)‖ ^ 2 :=
      Finset.sum_congr rfl (fun q _ => by
        rw [norm_iteratedCovGrad_connectionDifferenceLoweredCc_eq_connectionDifferenceSection (I := I) (M := M) g₀ g₁ q])
    rw [hcongr]
    exact hcd g₁ P htie hδ_le hδ0 hδ hsup i hi
  have hbg : (∑ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 3 q (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g_bg)‖ ^ 2) =
      ∑ q ∈ Finset.range (i + 1), FBackground q := rfl
  calc ∑ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 3 q (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2
      ≤ ∑ q ∈ Finset.range (i + 1),
          (2 * ‖iteratedCovGrad (I := I) g₀ 0 3 q (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)‖ ^ 2 +
            2 * ‖iteratedCovGrad (I := I) g₀ 0 3 q (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g_bg)‖ ^ 2) :=
        Finset.sum_le_sum (fun q _ => hper q)
    _ = 2 * (∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 3 q (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)‖ ^ 2) +
          2 * (∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 3 q (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g_bg)‖ ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ 2 * (Flow_cd i * (1 + S')) + 2 * ((∑ q ∈ Finset.range (i + 1), FBackground q) * (1 + S')) := by
        rw [hbg]
        have hone : (1 : ℝ) ≤ 1 + S' := by linarith
        have hbg_nn : 0 ≤ ∑ q ∈ Finset.range (i + 1), FBackground q :=
          Finset.sum_nonneg (fun q _ => hFBackground_nn q)
        nlinarith [hg1, hbg_nn, hone, mul_nonneg hbg_nn hS'_nn]
    _ = (2 * Flow_cd i + 2 * ∑ q ∈ Finset.range (i + 1), FBackground q) * (1 + S') := by ring

lemma riemannianFiberNormSq_iteratedCovGrad_cometricCastG0_antidiagonalTupleGridWindow_rf
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Kcg : ℕ → ℝ, (∀ l, 0 ≤ Kcg l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (l : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + l) x
            ((iteratedCovGrad (I := I) g₀ 3 1 l (cometricCastG0 (I := I) g₀ g₁)).toSection x) ≤
          Kcg l * Combinatorics.antidiagonalTupleGridWindow
            (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (l + 1) := by
  classical
  set Φ : SmoothCcTensor g₀ 3 1 := cometricDoubleTraceField (I := I) g₀ 1 with hΦ_def
  obtain ⟨C_base, hC_base_nn, hC_base⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_zero_metricComparisonDifferenceEndomorphismField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  have hSΦ_ex : ∀ i : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 3 1 i Φ).toSection x) ≤ K :=
    fun i => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 3 (1 + i)
      (iteratedCovGrad (I := I) g₀ 3 1 i Φ)
  choose SΦ hSΦ_nn hSΦ using hSΦ_ex
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  refine ⟨fun l => 2 * SΦ l + 2 * (operatorFieldApplicationGdiag (E := E) l * (∑ i' ∈ Finset.range (l + 1), SΦ i') *
      (fr ^ 2 * ∑ q ∈ Finset.range (l + 1), C_base q)), ?_, ?_⟩
  · intro l
    have h1 : 0 ≤ SΦ l := hSΦ_nn l
    have h2 : 0 ≤ ∑ i' ∈ Finset.range (l + 1), SΦ i' := Finset.sum_nonneg (fun i' _ => hSΦ_nn i')
    have h3 : 0 ≤ ∑ q ∈ Finset.range (l + 1), C_base q := Finset.sum_nonneg (fun q _ => hC_base_nn q)
    have h4 : 0 ≤ operatorFieldApplicationGdiag (E := E) l := operatorFieldApplicationGdiag_nonneg (E := E) l
    positivity
  · intro g₁ P htie δ hδ_le hδ0 hδ l x
    set bP : ℕ → ℝ := fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x) with hbP_def
    have hbP_nn : ∀ j, 0 ≤ bP j :=
      fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
    set antidiagonalTupleGridWindow : ℝ := Combinatorics.antidiagonalTupleGridWindow bP (l + 1) with hantidiagonalTupleGridWindow_def
    have hantidiagonalTupleGridWindow_one : (1 : ℝ) ≤ antidiagonalTupleGridWindow :=
      Combinatorics.one_le_antidiagonalTupleGridWindow bP hbP_nn (by omega)
    set W : SmoothCcTensor g₀ 3 3 :=
      endoSlotZeroCcTensor (I := I) (M := M) g₀ 2
        (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁) with hW_def
    have hWq : ∀ q : ℕ,
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + q) x
          ((iteratedCovGrad (I := I) g₀ 3 3 q W).toSection x) ≤
          fr ^ 2 * C_base q * Combinatorics.antidiagonalTupleGrid bP q := by
      intro q
      have h1 := riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) g₀ 2
        (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁) q x
      rw [← hW_def, ← hfr_def] at h1
      have h2 := hC_base g₁ P htie hδ_le hδ0 hδ q x
      have hgrideq : (∑ n ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n q,
            ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) =
          Combinatorics.antidiagonalTupleGrid bP q := rfl
      rw [hgrideq] at h2
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + q) x
            ((iteratedCovGrad (I := I) g₀ 3 3 q W).toSection x)
          ≤ fr ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + q) x
              ((iteratedCovGrad (I := I) g₀ 1 1 q
                (slotInsertEndoCc (I := I) (M := M) g₀ 0
                  (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁))).toSection x) := h1
        _ ≤ fr ^ 2 * (C_base q * Combinatorics.antidiagonalTupleGrid bP q) :=
            mul_le_mul_of_nonneg_left h2 (sq_nonneg fr)
        _ = fr ^ 2 * C_base q * Combinatorics.antidiagonalTupleGrid bP q := by ring
    have hid : cometricCastG0 (I := I) g₀ g₁ = Φ + ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W := by
      have h := cometricCastG0_eq_doubleTrace_add_ccOperatorFieldComp (I := I) g₀ g₁
      rw [← hΦ_def, ← hW_def] at h
      exact h
    have hB : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + l) x
        ((iteratedCovGrad (I := I) g₀ 3 1 l (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W)).toSection x) ≤
        (operatorFieldApplicationGdiag (E := E) l * (∑ i' ∈ Finset.range (l + 1), SΦ i') *
          (fr ^ 2 * ∑ q ∈ Finset.range (l + 1), C_base q)) * antidiagonalTupleGridWindow := by
      refine le_trans (riemannianFiberNormSq_iteratedCovGrad_operatorFieldComposition_diagonalProductGrid_rankLeft_le
        (I := I) (M := M) g₀ l 3 3 1 Φ W x) ?_
      rw [mul_assoc, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (operatorFieldApplicationGdiag_nonneg (E := E) l)
      have hqsum : ∀ i' : ℕ, (∑ q ∈ Finset.range (l + 1 - i'),
            riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + q) x
              ((iteratedCovGrad (I := I) g₀ 3 3 q W).toSection x)) ≤
          (fr ^ 2 * ∑ q ∈ Finset.range (l + 1), C_base q) * antidiagonalTupleGridWindow := by
        intro i'
        calc (∑ q ∈ Finset.range (l + 1 - i'),
              riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + q) x
                ((iteratedCovGrad (I := I) g₀ 3 3 q W).toSection x))
            ≤ ∑ q ∈ Finset.range (l + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + q) x
                  ((iteratedCovGrad (I := I) g₀ 3 3 q W).toSection x) := by
              refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) ?_
              exact fun q _ _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 3 (3 + q) x _
          _ ≤ ∑ q ∈ Finset.range (l + 1),
                fr ^ 2 * C_base q * Combinatorics.antidiagonalTupleGrid bP q :=
              Finset.sum_le_sum (fun q _ => hWq q)
          _ ≤ ∑ q ∈ Finset.range (l + 1), fr ^ 2 * C_base q * antidiagonalTupleGridWindow := by
              refine Finset.sum_le_sum (fun q hq => ?_)
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (sq_nonneg fr) (hC_base_nn q))
              rw [hantidiagonalTupleGridWindow_def]
              exact Combinatorics.antidiagonalTupleGrid_le_window bP hbP_nn
                (by rw [Finset.mem_range] at hq; omega)
          _ = (fr ^ 2 * ∑ q ∈ Finset.range (l + 1), C_base q) * antidiagonalTupleGridWindow := by
              rw [Finset.mul_sum, Finset.sum_mul]
      calc (∑ i' ∈ Finset.range (l + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i') x
              ((iteratedCovGrad (I := I) g₀ 3 1 i' Φ).toSection x) *
              ∑ q ∈ Finset.range (l + 1 - i'),
                riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + q) x
                  ((iteratedCovGrad (I := I) g₀ 3 3 q W).toSection x))
          ≤ ∑ i' ∈ Finset.range (l + 1),
              SΦ i' * ((fr ^ 2 * ∑ q ∈ Finset.range (l + 1), C_base q) * antidiagonalTupleGridWindow) := by
            refine Finset.sum_le_sum (fun i' _ => ?_)
            refine mul_le_mul (hSΦ i' x) (hqsum i')
              (Finset.sum_nonneg (fun q _ =>
                riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 3 (3 + q) x _))
              (hSΦ_nn i')
        _ = (∑ i' ∈ Finset.range (l + 1), SΦ i') *
              ((fr ^ 2 * ∑ q ∈ Finset.range (l + 1), C_base q) * antidiagonalTupleGridWindow) := by rw [Finset.sum_mul]
    rw [hid, iteratedCovGrad_add]
    rw [show ((iteratedCovGrad (I := I) g₀ 3 1 l Φ +
          iteratedCovGrad (I := I) g₀ 3 1 l (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W)).toSection x) =
        (iteratedCovGrad (I := I) g₀ 3 1 l Φ).toSection x +
          (iteratedCovGrad (I := I) g₀ 3 1 l (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W)).toSection x
        from by rw [SmoothCcTensor.toSection_add]; rfl]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 3 (1 + l) x _ _) ?_
    have hA : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + l) x
        ((iteratedCovGrad (I := I) g₀ 3 1 l Φ).toSection x) ≤ SΦ l := hSΦ l x
    have hSΦl_le : SΦ l ≤ SΦ l * antidiagonalTupleGridWindow := le_mul_of_one_le_right (hSΦ_nn l) hantidiagonalTupleGridWindow_one
    calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + l) x
            ((iteratedCovGrad (I := I) g₀ 3 1 l Φ).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + l) x
            ((iteratedCovGrad (I := I) g₀ 3 1 l
              (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W)).toSection x)
        ≤ 2 * (SΦ l * antidiagonalTupleGridWindow) +
            2 * ((operatorFieldApplicationGdiag (E := E) l * (∑ i' ∈ Finset.range (l + 1), SΦ i') *
              (fr ^ 2 * ∑ q ∈ Finset.range (l + 1), C_base q)) * antidiagonalTupleGridWindow) := by
          linarith [hA, hB, hSΦl_le]
      _ = (2 * SΦ l + 2 * (operatorFieldApplicationGdiag (E := E) l * (∑ i' ∈ Finset.range (l + 1), SΦ i') *
            (fr ^ 2 * ∑ q ∈ Finset.range (l + 1), C_base q))) * antidiagonalTupleGridWindow := by ring

lemma riemannianFiberNormSq_iteratedCovGrad_connectionDifferenceSection_antidiagonalTupleGridWindow_rf
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ccd : ℕ → ℝ, (∀ l, 0 ≤ Ccd l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (l : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 2 l (connectionDifferenceSection (I := I) g₁ g₀)).toSection x) ≤
          Ccd l * Combinatorics.antidiagonalTupleGridWindow
            (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (l + 2) := by
  classical
  obtain ⟨Kt0, hKt0_nn, Kc0, hKc0_nn, hbot⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_connectionDifferenceSection_topOrderSeparated_le (I := I) (M := M) g₀ hδ₀
  refine ⟨fun l => 2 * Kt0 + 2 * Kc0 l * (l : ℝ),
    fun l => by have := hKt0_nn; have := hKc0_nn l; positivity, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ l x
  set b : ℕ → ℝ := fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
    ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x) with hb_def
  have hb : ∀ j, 0 ≤ b j :=
    fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  have heng := hbot g₁ P htie hδ_le hδ0 hδ l x
  set Hd : SmoothCcTensor g₀ 1 (2 + l) :=
    ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 (2 + l)
      (iteratedCovGrad (I := I) g₀ 1 2 l (raisedKoszul (I := I) g₀ g₁))
      (sharpFlatEndoCc (I := I) g₀ g₁) with hHd_def
  have hbq1_grid : b (l + 1) ≤ Combinatorics.antidiagonalTupleGrid b (l + 1) := by
    have hsf := Combinatorics.single_factor_mul_antidiagonalTupleGrid_le b hb 0 (l + 1) (by omega)
    rwa [Combinatorics.antidiagonalTupleGrid_zero, mul_one, Nat.zero_add] at hsf
  have hrem_fold : (∑ k ∈ Finset.range l,
        b (l - k) * Combinatorics.antidiagonalTupleGrid b (k + 1)) ≤
      (l : ℝ) * Combinatorics.antidiagonalTupleGrid b (l + 1) := by
    calc (∑ k ∈ Finset.range l, b (l - k) * Combinatorics.antidiagonalTupleGrid b (k + 1))
        ≤ ∑ _k ∈ Finset.range l, Combinatorics.antidiagonalTupleGrid b (l + 1) := by
          refine Finset.sum_le_sum (fun k hk => ?_)
          rw [Finset.mem_range] at hk
          have hsf := Combinatorics.single_factor_mul_antidiagonalTupleGrid_le b hb
            (k + 1) (l - k) (by omega)
          rwa [show (k + 1) + (l - k) = l + 1 from by omega] at hsf
      _ = (l : ℝ) * Combinatorics.antidiagonalTupleGrid b (l + 1) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hgrid_grid : Combinatorics.antidiagonalTupleGrid b (l + 1) ≤
      Combinatorics.antidiagonalTupleGridWindow b (l + 2) :=
    Combinatorics.antidiagonalTupleGrid_le_window b hb (by omega)
  have hgrid_nn : 0 ≤ Combinatorics.antidiagonalTupleGrid b (l + 1) :=
    Combinatorics.antidiagonalTupleGrid_nonneg b hb (l + 1)
  have hsplit_eq :
      (iteratedCovGrad (I := I) g₀ 1 2 l (connectionDifferenceSection (I := I) g₁ g₀)).toSection x =
        Hd.toSection x +
          (iteratedCovGrad (I := I) g₀ 1 2 l (connectionDifferenceSection (I := I) g₁ g₀) - Hd).toSection x := by
    simp only [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]; abel
  rw [hsplit_eq]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (2 + l) x
    (Hd.toSection x) _) ?_
  have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x (Hd.toSection x) ≤
      Kt0 * Combinatorics.antidiagonalTupleGrid b (l + 1) :=
    le_trans heng.1 (mul_le_mul_of_nonneg_left hbq1_grid hKt0_nn)
  have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 1 2 l (connectionDifferenceSection (I := I) g₁ g₀) - Hd).toSection x) ≤
      Kc0 l * ((l : ℝ) * Combinatorics.antidiagonalTupleGrid b (l + 1)) :=
    le_trans heng.2 (mul_le_mul_of_nonneg_left hrem_fold (hKc0_nn l))
  have hstep : 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x (Hd.toSection x) +
      2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 1 2 l (connectionDifferenceSection (I := I) g₁ g₀) - Hd).toSection x) ≤
      (2 * Kt0 + 2 * Kc0 l * (l : ℝ)) * Combinatorics.antidiagonalTupleGrid b (l + 1) := by
    nlinarith [h1, h2, hgrid_nn, hKc0_nn l, hKt0_nn]
  refine le_trans hstep ?_
  refine mul_le_mul_of_nonneg_left hgrid_grid ?_
  have := hKt0_nn; have := hKc0_nn l; positivity

lemma riemannianFiberNormSq_iteratedCovGrad_metricLoweredConnectionDifference_le_antidiagonalTupleGridWindow
    (g₀ g_bg : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Kwx : ℕ → ℝ, (∀ l, 0 ≤ Kwx l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (l : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 3 l (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
          Kwx l * Combinatorics.antidiagonalTupleGridWindow
            (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (l + 2) := by
  classical
  obtain ⟨Ccd, hCcd_nn, hcd⟩ := riemannianFiberNormSq_iteratedCovGrad_connectionDifferenceSection_antidiagonalTupleGridWindow_rf (I := I) (M := M) g₀ hδ₀
  have hSBackground_ex : ∀ l : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 3 l (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g_bg)).toSection x) ≤ K :=
    fun l => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 0 (3 + l)
      (iteratedCovGrad (I := I) g₀ 0 3 l (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g_bg))
  choose SBackground hSBackground_nn hSBackground using hSBackground_ex
  refine ⟨fun l => 2 * Ccd l + 2 * SBackground l,
    fun l => by have := hCcd_nn l; have := hSBackground_nn l; linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ l x
  have hbP_nn : ∀ j, 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x) :=
    fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  have hantidiagonalTupleGridWindow_one : (1 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow
      (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (l + 2) :=
    Combinatorics.one_le_antidiagonalTupleGridWindow _ hbP_nn (by omega)
  have hsplit : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 3 l (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 3 l (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 3 l (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g_bg)).toSection x) := by
    rw [metricLoweredConnectionDifference, iteratedCovGrad_sub]
    rw [show ((iteratedCovGrad (I := I) g₀ 0 3 l (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁) -
          iteratedCovGrad (I := I) g₀ 0 3 l (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g_bg)).toSection x) =
        (iteratedCovGrad (I := I) g₀ 0 3 l (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)).toSection x -
          (iteratedCovGrad (I := I) g₀ 0 3 l (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g_bg)).toSection x
        from by rw [SmoothCcTensor.toSection_sub]; rfl]
    exact riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 0 (3 + l) x _ _
  have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 3 l (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)).toSection x) ≤
      Ccd l * Combinatorics.antidiagonalTupleGridWindow
        (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (l + 2) := by
    rw [metricLoweredConnectionDifferenceCoefficient_fiber_norm_sq_eq (I := I) (M := M) g₀ g₁ l x]
    exact hcd g₁ P htie hδ_le hδ0 hδ l x
  have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 3 l (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g_bg)).toSection x) ≤
      SBackground l := hSBackground l x
  have hCcd_l_nn : 0 ≤ Ccd l := hCcd_nn l
  have hSBackground_l_nn : 0 ≤ SBackground l := hSBackground_nn l
  nlinarith [hsplit, h1, h2, hantidiagonalTupleGridWindow_one, hCcd_l_nn, hSBackground_l_nn,
    mul_nonneg hCcd_l_nn (le_trans zero_le_one hantidiagonalTupleGridWindow_one),
    mul_nonneg hSBackground_l_nn (le_trans zero_le_one hantidiagonalTupleGridWindow_one)]

theorem deTurckVectorFieldCovector_lowOrder_iteratedCovGrad_norm_sq_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (_ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    {Λ₀ : ℝ} (hΛ₀0 : 0 ≤ Λ₀) :
    ∃ Flow : ℕ → ℝ, (∀ i, 0 ≤ Flow i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ₀ ^ 2),
        ∀ (i : ℕ), i ≤ a + 1 →
          ∑ q ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 1 q (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
            Flow i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨Kcg, hKcg_nn, hcg⟩ := riemannianFiberNormSq_iteratedCovGrad_cometricCastG0_antidiagonalTupleGridWindow_rf (I := I) (M := M) g₀ hδ₀
  obtain ⟨Kwx, hKwx_nn, hwx⟩ := riemannianFiberNormSq_iteratedCovGrad_metricLoweredConnectionDifference_le_antidiagonalTupleGridWindow (I := I) (M := M) g₀ g_bg hδ₀
  obtain ⟨K_rf, hK_rf_nn, hK_rf⟩ :=
    antidiagonalTupleGrid_integral_radiusFree (I := I) (M := M) g₀ hΛ₀0
  set Komega : ℕ → ℝ := fun n => operatorFieldApplicationGdiag (E := E) n *
    ∑ i' ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
      Kcg i' * Kwx l * Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1)
    with hKomega_def
  have hKomega_nn : ∀ n, 0 ≤ Komega n := by
    intro n; simp only [hKomega_def]
    refine mul_nonneg (operatorFieldApplicationGdiag_nonneg _) (Finset.sum_nonneg (fun i' _ =>
      Finset.sum_nonneg (fun l _ => ?_)))
    exact mul_nonneg (mul_nonneg (hKcg_nn i') (hKwx_nn l))
      (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg i' (l + 1))
  refine ⟨fun i => ∑ q ∈ Finset.range (i + 1), Komega q * ∑ k ∈ Finset.range (q + 2), K_rf k,
    fun i => Finset.sum_nonneg (fun q _ => mul_nonneg (hKomega_nn q)
      (Finset.sum_nonneg (fun k _ => hK_rf_nn k))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hsup i hi
  have hpt : ∀ (n : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + n) x
          ((iteratedCovGrad (I := I) g₀ 0 1 n (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
        Komega n * Combinatorics.antidiagonalTupleGridWindow
          (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (n + 2) := by
    intro n x
    set bP : ℕ → ℝ := fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x) with hbP_def
    have hbP_nn : ∀ j, 0 ≤ bP j :=
      fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
    have hleib := operatorFieldApplication_iteratedCovGrad_diagonalProductGrid_le (I := I) (M := M) g₀ 3 1
      (cometricCastG0 (I := I) g₀ g₁) (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg) n x
    refine le_trans hleib ?_
    rw [hKomega_def, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (operatorFieldApplicationGdiag_nonneg (E := E) n)
    have hterm : ∀ i' ∈ Finset.range (n + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i') x
            ((iteratedCovGrad (I := I) g₀ 3 1 i' (cometricCastG0 (I := I) g₀ g₁)).toSection x) *
          ∑ l ∈ Finset.range (n + 1 - i'),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 3 l (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
        ∑ l ∈ Finset.range (n + 1),
          (Kcg i' * Kwx l * Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1)) *
            Combinatorics.antidiagonalTupleGridWindow bP (n + 2) := by
      intro i' hi'
      have hi'n : i' ≤ n := by rw [Finset.mem_range] at hi'; omega
      have hcgi := hcg g₁ P htie hδ_le hδ0 hδ i' x
      rw [Finset.mul_sum]
      refine le_trans (Finset.sum_le_sum (fun l hl => ?_))
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun l _ _ => ?_))
      swap
      · exact mul_nonneg (mul_nonneg (mul_nonneg (hKcg_nn i') (hKwx_nn l))
          (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg i' (l + 1)))
          (Combinatorics.antidiagonalTupleGridWindow_nonneg bP hbP_nn (n + 2))
      · have hwxl := hwx g₁ P htie hδ_le hδ0 hδ l x
        have hmul := Combinatorics.antidiagonalTupleGridWindow_mul_le bP hbP_nn i' (l + 1)
        have hmono := Combinatorics.antidiagonalTupleGridWindow_mono bP hbP_nn
          (show i' + (l + 1) + 1 ≤ n + 2 by rw [Finset.mem_range] at hl; omega)
        have hprod : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i') x
              ((iteratedCovGrad (I := I) g₀ 3 1 i' (cometricCastG0 (I := I) g₀ g₁)).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 3 l (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
            (Kcg i' * Combinatorics.antidiagonalTupleGridWindow bP (i' + 1)) *
              (Kwx l * Combinatorics.antidiagonalTupleGridWindow bP (l + 2)) :=
          mul_le_mul hcgi hwxl (riemannianFiberNormSq_nonneg _ _ _ _ _)
            (mul_nonneg (hKcg_nn i')
              (Combinatorics.antidiagonalTupleGridWindow_nonneg bP hbP_nn (i' + 1)))
        have hwc_nn : 0 ≤ Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1) :=
          Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg i' (l + 1)
        have hantidiagonalTupleGridWindown_nn : 0 ≤ Combinatorics.antidiagonalTupleGridWindow bP (n + 2) :=
          Combinatorics.antidiagonalTupleGridWindow_nonneg bP hbP_nn (n + 2)
        calc riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i') x
                ((iteratedCovGrad (I := I) g₀ 3 1 i' (cometricCastG0 (I := I) g₀ g₁)).toSection x) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 3 l (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
            ≤ (Kcg i' * Combinatorics.antidiagonalTupleGridWindow bP (i' + 1)) *
                (Kwx l * Combinatorics.antidiagonalTupleGridWindow bP (l + 2)) := hprod
          _ = Kcg i' * Kwx l * (Combinatorics.antidiagonalTupleGridWindow bP (i' + 1) *
                Combinatorics.antidiagonalTupleGridWindow bP (l + 2)) := by ring
          _ ≤ Kcg i' * Kwx l * (Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1) *
                Combinatorics.antidiagonalTupleGridWindow bP (i' + (l + 1) + 1)) := by
              refine mul_le_mul_of_nonneg_left hmul (mul_nonneg (hKcg_nn i') (hKwx_nn l))
          _ ≤ Kcg i' * Kwx l * (Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1) *
                Combinatorics.antidiagonalTupleGridWindow bP (n + 2)) := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hKcg_nn i') (hKwx_nn l))
              exact mul_le_mul_of_nonneg_left hmono hwc_nn
          _ = (Kcg i' * Kwx l * Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1)) *
                Combinatorics.antidiagonalTupleGridWindow bP (n + 2) := by ring
    calc ∑ i' ∈ Finset.range (n + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i') x
              ((iteratedCovGrad (I := I) g₀ 3 1 i' (cometricCastG0 (I := I) g₀ g₁)).toSection x) *
            ∑ l ∈ Finset.range (n + 1 - i'),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 3 l (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
        ≤ ∑ i' ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
            (Kcg i' * Kwx l * Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1)) *
              Combinatorics.antidiagonalTupleGridWindow bP (n + 2) :=
          Finset.sum_le_sum hterm
      _ = (∑ i' ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
            Kcg i' * Kwx l * Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1)) *
            Combinatorics.antidiagonalTupleGridWindow bP (n + 2) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl (fun i' _ => by rw [Finset.sum_mul])
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
  have hL2 : ∀ n : ℕ,
      ‖iteratedCovGrad (I := I) g₀ 0 1 n (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
        Komega n * ∑ k ∈ Finset.range (n + 2),
          K_rf k * (1 + ‖iteratedCovGrad (I := I) g₀ 0 2 k P‖ ^ 2) := by
    intro n
    have hwin_int : MeasureTheory.Integrable
        (fun x => Combinatorics.antidiagonalTupleGridWindow
          (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (n + 2))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
      simp only [Combinatorics.antidiagonalTupleGridWindow]
      exact MeasureTheory.integrable_finset_sum _ (fun k _ => (hAG k).1)
    have hFint : MeasureTheory.Integrable
        (fun x => Komega n * Combinatorics.antidiagonalTupleGridWindow
          (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (n + 2))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) := hwin_int.const_mul _
    have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 0 (1 + n)
      (iteratedCovGrad (I := I) g₀ 0 1 n (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg)) _ hFint
      (fun x => hpt n x)
    rw [MeasureTheory.integral_const_mul] at hkey
    refine le_trans hkey ?_
    refine mul_le_mul_of_nonneg_left ?_ (hKomega_nn n)
    have hwin_bd : (∫ x, Combinatorics.antidiagonalTupleGridWindow
        (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (n + 2)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        ∑ k ∈ Finset.range (n + 2),
          K_rf k * (1 + ‖iteratedCovGrad (I := I) g₀ 0 2 k P‖ ^ 2) := by
      simp only [Combinatorics.antidiagonalTupleGridWindow]
      rw [MeasureTheory.integral_finset_sum _ (fun k _ => (hAG k).1)]
      exact Finset.sum_le_sum (fun k _ => (hAG k).2)
    exact hwin_bd
  set S' : ℝ := ∑ j ∈ Finset.range (i + 2),
    ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 with hS'_def
  have hS'_nn : 0 ≤ S' := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  calc ∑ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 1 q (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2
      ≤ ∑ q ∈ Finset.range (i + 1),
          Komega q * ∑ k ∈ Finset.range (q + 2),
            K_rf k * (1 + ‖iteratedCovGrad (I := I) g₀ 0 2 k P‖ ^ 2) :=
        Finset.sum_le_sum (fun q _ => hL2 q)
    _ ≤ ∑ q ∈ Finset.range (i + 1),
          (Komega q * ∑ k ∈ Finset.range (q + 2), K_rf k) * (1 + S') := by
        refine Finset.sum_le_sum (fun q hq => ?_)
        have hqi : q ≤ i := by rw [Finset.mem_range] at hq; omega
        have hinner : (∑ k ∈ Finset.range (q + 2),
              K_rf k * (1 + ‖iteratedCovGrad (I := I) g₀ 0 2 k P‖ ^ 2)) ≤
            (∑ k ∈ Finset.range (q + 2), K_rf k) * (1 + S') := by
          rw [Finset.sum_mul]
          refine Finset.sum_le_sum (fun k hk => ?_)
          have hkS' : ‖iteratedCovGrad (I := I) g₀ 0 2 k P‖ ^ 2 ≤ S' :=
            Finset.single_le_sum (f := fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)
              (fun j _ => sq_nonneg _) (Finset.mem_range.mpr (by rw [Finset.mem_range] at hk; omega))
          refine mul_le_mul_of_nonneg_left ?_ (hK_rf_nn k)
          linarith
        calc Komega q * ∑ k ∈ Finset.range (q + 2),
              K_rf k * (1 + ‖iteratedCovGrad (I := I) g₀ 0 2 k P‖ ^ 2)
            ≤ Komega q * ((∑ k ∈ Finset.range (q + 2), K_rf k) * (1 + S')) :=
              mul_le_mul_of_nonneg_left hinner (hKomega_nn q)
          _ = (Komega q * ∑ k ∈ Finset.range (q + 2), K_rf k) * (1 + S') := by ring
    _ = (∑ q ∈ Finset.range (i + 1), Komega q * ∑ k ∈ Finset.range (q + 2), K_rf k) * (1 + S') := by
        rw [Finset.sum_mul]

private lemma exists_riemannianFiberNormSq_connectionDifference_topsep_rf
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ l, 0 ≤ Kc l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (l : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 2 l (connectionDifferenceSection (I := I) g₁ g₀)).toSection x) ≤
          Ktop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (l + 1)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (l + 1) P).toSection x) +
          Kc l * Combinatorics.antidiagonalTupleGridWindow
            (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (l + 2) := by
  classical
  obtain ⟨Kt0, hKt0_nn, Kc0, hKc0_nn, hbot⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_connectionDifferenceSection_topOrderSeparated_le (I := I) (M := M) g₀ hδ₀
  refine ⟨2 * Kt0, mul_nonneg (by norm_num) hKt0_nn, fun l => 2 * Kc0 l * (l : ℝ),
    fun l => mul_nonneg (mul_nonneg (by norm_num) (hKc0_nn l)) (Nat.cast_nonneg l), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ l x
  set b : ℕ → ℝ := fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
    ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x) with hb_def
  have hb : ∀ j, 0 ≤ b j :=
    fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  have heng := hbot g₁ P htie hδ_le hδ0 hδ l x
  set Hd : SmoothCcTensor g₀ 1 (2 + l) :=
    ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 (2 + l)
      (iteratedCovGrad (I := I) g₀ 1 2 l (raisedKoszul (I := I) g₀ g₁))
      (sharpFlatEndoCc (I := I) g₀ g₁) with hHd_def
  have hrem_fold : (∑ k ∈ Finset.range l,
        b (l - k) * Combinatorics.antidiagonalTupleGrid b (k + 1)) ≤
      (l : ℝ) * Combinatorics.antidiagonalTupleGrid b (l + 1) := by
    calc (∑ k ∈ Finset.range l, b (l - k) * Combinatorics.antidiagonalTupleGrid b (k + 1))
        ≤ ∑ _k ∈ Finset.range l, Combinatorics.antidiagonalTupleGrid b (l + 1) := by
          refine Finset.sum_le_sum (fun k hk => ?_)
          rw [Finset.mem_range] at hk
          have hsf := Combinatorics.single_factor_mul_antidiagonalTupleGrid_le b hb
            (k + 1) (l - k) (by omega)
          rwa [show (k + 1) + (l - k) = l + 1 from by omega] at hsf
      _ = (l : ℝ) * Combinatorics.antidiagonalTupleGrid b (l + 1) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hgrid_grid : Combinatorics.antidiagonalTupleGrid b (l + 1) ≤
      Combinatorics.antidiagonalTupleGridWindow b (l + 2) :=
    Combinatorics.antidiagonalTupleGrid_le_window b hb (by omega)
  have hgrid_nn : 0 ≤ Combinatorics.antidiagonalTupleGrid b (l + 1) :=
    Combinatorics.antidiagonalTupleGrid_nonneg b hb (l + 1)
  have hsplit_eq :
      (iteratedCovGrad (I := I) g₀ 1 2 l (connectionDifferenceSection (I := I) g₁ g₀)).toSection x =
        Hd.toSection x +
          (iteratedCovGrad (I := I) g₀ 1 2 l (connectionDifferenceSection (I := I) g₁ g₀) - Hd).toSection x := by
    simp only [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]; abel
  rw [hsplit_eq]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (2 + l) x
    (Hd.toSection x) _) ?_
  have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x (Hd.toSection x) ≤
      Kt0 * b (l + 1) := heng.1
  have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 1 2 l (connectionDifferenceSection (I := I) g₁ g₀) - Hd).toSection x) ≤
      Kc0 l * ((l : ℝ) * Combinatorics.antidiagonalTupleGrid b (l + 1)) :=
    le_trans heng.2 (mul_le_mul_of_nonneg_left hrem_fold (hKc0_nn l))
  have hb1_nn : 0 ≤ b (l + 1) := hb (l + 1)
  have h2' : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 1 2 l (connectionDifferenceSection (I := I) g₁ g₀) - Hd).toSection x) ≤
      Kc0 l * ((l : ℝ) * Combinatorics.antidiagonalTupleGridWindow b (l + 2)) :=
    le_trans h2 (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hgrid_grid (Nat.cast_nonneg l)) (hKc0_nn l))
  calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x (Hd.toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 2 l (connectionDifferenceSection (I := I) g₁ g₀) - Hd).toSection x)
      ≤ 2 * (Kt0 * b (l + 1)) +
          2 * (Kc0 l * ((l : ℝ) * Combinatorics.antidiagonalTupleGridWindow b (l + 2))) := by
        linarith [h1, h2']
    _ = (2 * Kt0) * b (l + 1) +
          (2 * Kc0 l * (l : ℝ)) * Combinatorics.antidiagonalTupleGridWindow b (l + 2) := by ring

theorem connectionDifference_L2_topsep_rf
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (_ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    {Λ₀ : ℝ} (hΛ₀0 : 0 ≤ Λ₀) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Flow : ℕ → ℝ, (∀ n, 0 ≤ Flow n) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ₀ ^ 2),
        ∀ n : ℕ, n ≤ a + 1 →
          ‖iteratedCovGrad (I := I) g₀ 1 2 n (connectionDifferenceSection (I := I) g₁ g₀)‖ ^ 2 ≤
            Ktop * ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P‖ ^ 2 +
            Flow n * (1 + ∑ j ∈ Finset.range (n + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨Ktop_pt, hKtop_pt_nn, Kc_pt, hKc_pt_nn, hpt⟩ :=
    exists_riemannianFiberNormSq_connectionDifference_topsep_rf (I := I) (M := M) g₀ hδ₀
  obtain ⟨K_rf, hK_rf_nn, hK_rf⟩ :=
    antidiagonalTupleGrid_integral_radiusFree (I := I) (M := M) g₀ hΛ₀0
  refine ⟨Ktop_pt, hKtop_pt_nn,
    fun n => Kc_pt n * ∑ k ∈ Finset.range (n + 2), K_rf k,
    fun n => mul_nonneg (hKc_pt_nn n) (Finset.sum_nonneg fun k _ => hK_rf_nn k), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hsup n hn
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  set S' : ℝ := ∑ j ∈ Finset.range (n + 2),
    ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 with hS'_def
  have hS'_nn : 0 ≤ S' := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
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
      (fun x => Combinatorics.antidiagonalTupleGridWindow
        (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (n + 2))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    simp only [Combinatorics.antidiagonalTupleGridWindow]
    exact MeasureTheory.integrable_finset_sum _ (fun k _ => (hAG k).1)
  have htop_int : MeasureTheory.Integrable (fun x =>
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (n + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + (n + 1))
      (iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P)
  have hbridge := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 1 (2 + n)
    (iteratedCovGrad (I := I) g₀ 1 2 n (connectionDifferenceSection (I := I) g₁ g₀))
    (fun x => Ktop_pt * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (n + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P).toSection x)
      + Kc_pt n * Combinatorics.antidiagonalTupleGridWindow
        (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (n + 2))
    ((htop_int.const_mul Ktop_pt).add (hwin_int.const_mul (Kc_pt n)))
    (fun x => hpt g₁ P htie hδ_le hδ0 hδ n x)
  rw [MeasureTheory.integral_add (htop_int.const_mul Ktop_pt) (hwin_int.const_mul (Kc_pt n)),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hbridge
  have hnormsq : ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (n + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    rw [SmoothCcTensor.norm_def, tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  have hwin_bd : (∫ x, Combinatorics.antidiagonalTupleGridWindow
      (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (n + 2)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
      (∑ k ∈ Finset.range (n + 2), K_rf k) * (1 + S') := by
    simp only [Combinatorics.antidiagonalTupleGridWindow]
    rw [MeasureTheory.integral_finset_sum _ (fun k _ => (hAG k).1), Finset.sum_mul]
    refine Finset.sum_le_sum (fun k hk => ?_)
    refine le_trans (hAG k).2 ?_
    have hkS' : ‖iteratedCovGrad (I := I) g₀ 0 2 k P‖ ^ 2 ≤ S' :=
      Finset.single_le_sum (f := fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_range.mpr (by rw [Finset.mem_range] at hk; omega))
    refine mul_le_mul_of_nonneg_left ?_ (hK_rf_nn k)
    linarith
  calc ‖iteratedCovGrad (I := I) g₀ 1 2 n (connectionDifferenceSection (I := I) g₁ g₀)‖ ^ 2
      ≤ Ktop_pt * (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (n + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
        + Kc_pt n * (∫ x, Combinatorics.antidiagonalTupleGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (n + 2)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) := hbridge
    _ = Ktop_pt * ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P‖ ^ 2
        + Kc_pt n * (∫ x, Combinatorics.antidiagonalTupleGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (n + 2)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) := by rw [hnormsq]
    _ ≤ Ktop_pt * ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P‖ ^ 2
        + Kc_pt n * ((∑ k ∈ Finset.range (n + 2), K_rf k) * (1 + S')) := by
        have hmul := mul_le_mul_of_nonneg_left hwin_bd (hKc_pt_nn n)
        linarith [hmul]
    _ = Ktop_pt * ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P‖ ^ 2
        + (Kc_pt n * ∑ k ∈ Finset.range (n + 2), K_rf k) * (1 + S') := by ring

theorem metricLoweredConnectionDifference_iteratedCovGrad_norm_sq_topOrderSeparated
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    {Λ₀ : ℝ} (hΛ₀0 : 0 ≤ Λ₀) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Flow : ℕ → ℝ, (∀ n, 0 ≤ Flow n) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ₀ ^ 2),
        ∀ n : ℕ, n ≤ a + 1 →
          ‖iteratedCovGrad (I := I) g₀ 0 3 n (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
            Ktop * ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P‖ ^ 2 +
            Flow n * (1 + ∑ j ∈ Finset.range (n + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨Ktop_cd, hKtop_cd_nn, Flow_cd, hFcd_nn, hcd⟩ :=
    connectionDifference_L2_topsep_rf (I := I) (M := M) g₀ a ha_super hδ₀ hΛ₀0
  refine ⟨2 * Ktop_cd, mul_nonneg (by norm_num) hKtop_cd_nn,
    fun n => 2 * Flow_cd n +
      2 * ‖iteratedCovGrad (I := I) g₀ 0 3 n (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g_bg)‖ ^ 2,
    fun n => add_nonneg (mul_nonneg (by norm_num) (hFcd_nn n))
      (mul_nonneg (by norm_num) (sq_nonneg _)), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hsup n hn
  set S' : ℝ := ∑ j ∈ Finset.range (n + 2),
    ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 with hS'_def
  have hS'_nn : 0 ≤ S' := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hone : (1 : ℝ) ≤ 1 + S' := by linarith
  have hA : ‖iteratedCovGrad (I := I) g₀ 0 3 n (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)‖ ^ 2 ≤
      Ktop_cd * ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P‖ ^ 2 + Flow_cd n * (1 + S') := by
    rw [norm_iteratedCovGrad_connectionDifferenceLoweredCc_eq_connectionDifferenceSection (I := I) (M := M) g₀ g₁ n]
    exact hcd g₁ P htie hδ_le hδ0 hδ hsup n hn
  have htri : ‖iteratedCovGrad (I := I) g₀ 0 3 n (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)‖ ≤
      ‖iteratedCovGrad (I := I) g₀ 0 3 n (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)‖ +
        ‖iteratedCovGrad (I := I) g₀ 0 3 n (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g_bg)‖ := by
    rw [metricLoweredConnectionDifference, iteratedCovGrad_sub]
    exact norm_sub_le _ _
  have hbg_fold : ‖iteratedCovGrad (I := I) g₀ 0 3 n (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g_bg)‖ ^ 2 ≤
      ‖iteratedCovGrad (I := I) g₀ 0 3 n (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g_bg)‖ ^ 2 * (1 + S') :=
    le_mul_of_one_le_right (sq_nonneg _) hone
  nlinarith [htri, hA, hbg_fold,
    norm_nonneg (iteratedCovGrad (I := I) g₀ 0 3 n (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)),
    norm_nonneg (iteratedCovGrad (I := I) g₀ 0 3 n (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)),
    norm_nonneg (iteratedCovGrad (I := I) g₀ 0 3 n (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g_bg)),
    sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 3 n (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)‖ -
      ‖iteratedCovGrad (I := I) g₀ 0 3 n (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g_bg)‖),
    hFcd_nn n, hS'_nn, mul_nonneg (hFcd_nn n) hS'_nn]

private lemma cometricCastG0_wXi_twoArm_fold_rf
    (g₀ g_bg : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Klower : ℕ → ℝ, (∀ n, 0 ≤ Klower n) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (n : ℕ) (x : M),
        (∑ i' ∈ Finset.range (n + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i') x
              ((iteratedCovGrad (I := I) g₀ 3 1 i' (cometricCastG0 (I := I) g₀ g₁)).toSection x) *
            ∑ l ∈ Finset.range (n + 1 - i'),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 3 l
                  (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)).toSection x)) ≤
          Klower n * Combinatorics.antidiagonalTupleGridWindow
            (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (n + 2) := by
  classical
  obtain ⟨Kcg, hKcg_nn, hcg⟩ := riemannianFiberNormSq_iteratedCovGrad_cometricCastG0_antidiagonalTupleGridWindow_rf (I := I) (M := M) g₀ hδ₀
  obtain ⟨Kwx, hKwx_nn, hwx⟩ := riemannianFiberNormSq_iteratedCovGrad_metricLoweredConnectionDifference_le_antidiagonalTupleGridWindow (I := I) (M := M) g₀ g_bg hδ₀
  refine ⟨fun n => ∑ i' ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
      Kcg i' * Kwx l * Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1),
    fun n => Finset.sum_nonneg (fun i' _ => Finset.sum_nonneg (fun l _ =>
      mul_nonneg (mul_nonneg (hKcg_nn i') (hKwx_nn l))
        (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg i' (l + 1)))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ n x
  set bP : ℕ → ℝ := fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
    ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x) with hbP_def
  have hbP_nn : ∀ j, 0 ≤ bP j :=
    fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  have hterm : ∀ i' ∈ Finset.range (n + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i') x
          ((iteratedCovGrad (I := I) g₀ 3 1 i' (cometricCastG0 (I := I) g₀ g₁)).toSection x) *
        ∑ l ∈ Finset.range (n + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 3 l (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
      ∑ l ∈ Finset.range (n + 1),
        (Kcg i' * Kwx l * Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1)) *
          Combinatorics.antidiagonalTupleGridWindow bP (n + 2) := by
    intro i' hi'
    have hi'n : i' ≤ n := by rw [Finset.mem_range] at hi'; omega
    have hcgi := hcg g₁ P htie hδ_le hδ0 hδ i' x
    rw [Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum (fun l hl => ?_))
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun l _ _ => ?_))
    swap
    · exact mul_nonneg (mul_nonneg (mul_nonneg (hKcg_nn i') (hKwx_nn l))
        (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg i' (l + 1)))
        (Combinatorics.antidiagonalTupleGridWindow_nonneg bP hbP_nn (n + 2))
    · have hwxl := hwx g₁ P htie hδ_le hδ0 hδ l x
      have hmul := Combinatorics.antidiagonalTupleGridWindow_mul_le bP hbP_nn i' (l + 1)
      have hmono := Combinatorics.antidiagonalTupleGridWindow_mono bP hbP_nn
        (show i' + (l + 1) + 1 ≤ n + 2 by rw [Finset.mem_range] at hl; omega)
      have hwc_nn : 0 ≤ Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1) :=
        Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg i' (l + 1)
      have hantidiagonalTupleGridWindown_nn : 0 ≤ Combinatorics.antidiagonalTupleGridWindow bP (n + 2) :=
        Combinatorics.antidiagonalTupleGridWindow_nonneg bP hbP_nn (n + 2)
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i') x
              ((iteratedCovGrad (I := I) g₀ 3 1 i' (cometricCastG0 (I := I) g₀ g₁)).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 3 l (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
          ≤ (Kcg i' * Combinatorics.antidiagonalTupleGridWindow bP (i' + 1)) *
              (Kwx l * Combinatorics.antidiagonalTupleGridWindow bP (l + 2)) :=
            mul_le_mul hcgi hwxl (riemannianFiberNormSq_nonneg _ _ _ _ _)
              (mul_nonneg (hKcg_nn i')
                (Combinatorics.antidiagonalTupleGridWindow_nonneg bP hbP_nn (i' + 1)))
        _ = Kcg i' * Kwx l * (Combinatorics.antidiagonalTupleGridWindow bP (i' + 1) *
              Combinatorics.antidiagonalTupleGridWindow bP (l + 2)) := by ring
        _ ≤ Kcg i' * Kwx l * (Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1) *
              Combinatorics.antidiagonalTupleGridWindow bP (i' + (l + 1) + 1)) := by
            exact mul_le_mul_of_nonneg_left hmul (mul_nonneg (hKcg_nn i') (hKwx_nn l))
        _ ≤ Kcg i' * Kwx l * (Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1) *
              Combinatorics.antidiagonalTupleGridWindow bP (n + 2)) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hKcg_nn i') (hKwx_nn l))
            exact mul_le_mul_of_nonneg_left hmono hwc_nn
        _ = (Kcg i' * Kwx l * Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1)) *
              Combinatorics.antidiagonalTupleGridWindow bP (n + 2) := by ring
  calc ∑ i' ∈ Finset.range (n + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i') x
            ((iteratedCovGrad (I := I) g₀ 3 1 i' (cometricCastG0 (I := I) g₀ g₁)).toSection x) *
          ∑ l ∈ Finset.range (n + 1 - i'),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 3 l (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
      ≤ ∑ i' ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
          (Kcg i' * Kwx l * Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1)) *
            Combinatorics.antidiagonalTupleGridWindow bP (n + 2) :=
        Finset.sum_le_sum hterm
    _ = (∑ i' ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
          Kcg i' * Kwx l * Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1)) *
          Combinatorics.antidiagonalTupleGridWindow bP (n + 2) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun i' _ => by rw [Finset.sum_mul])

private lemma exists_riemannianFiberNormSq_wOmega_topsep_rf
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    {Λ₀ : ℝ} (hΛ₀0 : 0 ≤ Λ₀) :
    ∃ Kc_top : ℝ, 0 ≤ Kc_top ∧ ∃ Kwin : ℕ → ℝ, (∀ n, 0 ≤ Kwin n) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ₀ ^ 2)
        (n : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + n) x
            ((iteratedCovGrad (I := I) g₀ 0 1 n (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
          Kc_top * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
              ((iteratedCovGrad (I := I) g₀ 0 3 n (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)).toSection x) +
          Kwin n * Combinatorics.antidiagonalTupleGridWindow
            (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (n + 2) := by
  classical
  obtain ⟨ΛC, FlowC, hΛC_nn, hFlowC_nn, hCg⟩ :=
    cometricCastG0_order0sup_jetL2_radiusFree (I := I) (M := M) g₀ a ha_super hδ₀ hΛ₀0
  obtain ⟨Klower, hKlower_nn, hfold⟩ :=
    cometricCastG0_wXi_twoArm_fold_rf (I := I) (M := M) g₀ g_bg hδ₀
  refine ⟨2 * ΛC ^ 2, mul_nonneg (by norm_num) (sq_nonneg ΛC),
    fun n => 2 * ((n : ℝ) * operatorFieldApplicationGdiag (E := E) n * Klower n),
    fun n => mul_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (operatorFieldApplicationGdiag_nonneg (E := E) n)) (hKlower_nn n)), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hsup n x
  have hCsup := (hCg g₁ P htie hδ_le hδ0 hδ hsup).1
  have hwform : deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg =
      ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 1 (cometricCastG0 (I := I) g₀ g₁)
        (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg) := by
    rw [show deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg =
        operatorFieldApply (I := I) (M := M) g₀ 3 1 (cometricCastG0 (I := I) g₀ g₁)
          (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg) from rfl]
    exact (operatorFieldComposition_zero_eq_operatorFieldApply (I := I) (M := M) g₀ 3 1 (cometricCastG0 (I := I) g₀ g₁)
      (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)).symm
  rw [hwform, iteratedCovGrad_operatorFieldComposition_eq_argCorner_add_lower (I := I) (M := M) g₀ 0 3 1
    (cometricCastG0 (I := I) g₀ g₁) (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg) n]
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (1 + n) x _ _) ?_
  have hcorner : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + n) x
      ((ccOperatorFieldComp (I := I) (M := M) g₀ 0 (3 + n) (1 + n)
        (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 3 1 (cometricCastG0 (I := I) g₀ g₁) n n)
        (iteratedCovGrad (I := I) g₀ 0 3 n
          (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg))).toSection x) ≤
      ΛC ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)).toSection x) := by
    refine le_trans (riemannianFiberNormSq_operatorFieldComposition_operatorFieldApplicationLeibnizPsi_diag_le (I := I) (M := M) g₀ 0 3 1
      (cometricCastG0 (I := I) g₀ g₁) n
      (iteratedCovGrad (I := I) g₀ 0 3 n (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)) x) ?_
    exact mul_le_mul_of_nonneg_right (hCsup x)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + n) x _)
  have hlower : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + n) x
      ((∑ k ∈ Finset.range n,
        ccOperatorFieldComp (I := I) (M := M) g₀ 0 (3 + k) (1 + n)
          (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 3 1 (cometricCastG0 (I := I) g₀ g₁) n k)
          (iteratedCovGrad (I := I) g₀ 0 3 k
            (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg))).toSection x) ≤
      ((n : ℝ) * operatorFieldApplicationGdiag (E := E) n) *
        ∑ i ∈ Finset.range (n + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i) x
              ((iteratedCovGrad (I := I) g₀ 3 1 i (cometricCastG0 (I := I) g₀ g₁)).toSection x)
            * ∑ l ∈ Finset.range (n + 1 - i),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 3 l
                    (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)).toSection x) := by
    refine le_trans (riemannianFiberNormSq_operatorFieldComposition_argLower_le (I := I) (M := M) g₀ 0 3 1
      (cometricCastG0 (I := I) g₀ g₁) (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg) n x) ?_
    refine mul_le_mul_of_nonneg_left ?_
      (mul_nonneg (Nat.cast_nonneg n) (operatorFieldApplicationGdiag_nonneg (E := E) n))
    set A : ℕ → ℝ := fun i => riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i) x
      ((iteratedCovGrad (I := I) g₀ 3 1 i (cometricCastG0 (I := I) g₀ g₁)).toSection x)
      with hA_def
    set B : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 3 l (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
      with hB_def
    have hA_nn : ∀ i, 0 ≤ A i := fun i => riemannianFiberNormSq_nonneg _ _ _ _ _
    have hB_nn : ∀ l, 0 ≤ B l := fun l => riemannianFiberNormSq_nonneg _ _ _ _ _
    have hstep1 : ∑ k ∈ Finset.range n,
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + (n - k)) x
              ((iteratedCovGrad (I := I) g₀ 3 1 (n - k)
                (cometricCastG0 (I := I) g₀ g₁)).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + k) x
              ((iteratedCovGrad (I := I) g₀ 0 3 k
                (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
        ∑ k ∈ Finset.range n, A (n - k) * ∑ l ∈ Finset.range (n + 1 - (n - k)), B l := by
      refine Finset.sum_le_sum (fun k hk => ?_)
      rw [Finset.mem_range] at hk
      refine mul_le_mul_of_nonneg_left ?_ (hA_nn (n - k))
      exact Finset.single_le_sum (fun l _ => hB_nn l)
        (Finset.mem_range.mpr (by omega))
    have hstep2 : ∑ k ∈ Finset.range n, A (n - k) * ∑ l ∈ Finset.range (n + 1 - (n - k)), B l =
        ∑ k ∈ Finset.range n, A (k + 1) * ∑ l ∈ Finset.range (n + 1 - (k + 1)), B l := by
      rw [← Finset.sum_range_reflect
        (fun k => A (k + 1) * ∑ l ∈ Finset.range (n + 1 - (k + 1)), B l) n]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      rw [Finset.mem_range] at hk
      have hk1 : n - 1 - k + 1 = n - k := by omega
      rw [hk1]
    have hstep3 : ∑ k ∈ Finset.range n, A (k + 1) * ∑ l ∈ Finset.range (n + 1 - (k + 1)), B l ≤
        ∑ i ∈ Finset.range (n + 1), A i * ∑ l ∈ Finset.range (n + 1 - i), B l := by
      rw [Finset.sum_range_succ' (fun i => A i * ∑ l ∈ Finset.range (n + 1 - i), B l) n]
      have h0 : 0 ≤ A 0 * ∑ l ∈ Finset.range (n + 1 - 0), B l :=
        mul_nonneg (hA_nn 0) (Finset.sum_nonneg fun l _ => hB_nn l)
      linarith
    calc ∑ k ∈ Finset.range n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + (n - k)) x
                ((iteratedCovGrad (I := I) g₀ 3 1 (n - k)
                  (cometricCastG0 (I := I) g₀ g₁)).toSection x) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + k) x
                ((iteratedCovGrad (I := I) g₀ 0 3 k
                  (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
          ≤ ∑ k ∈ Finset.range n, A (n - k) * ∑ l ∈ Finset.range (n + 1 - (n - k)), B l := hstep1
        _ = ∑ k ∈ Finset.range n, A (k + 1) * ∑ l ∈ Finset.range (n + 1 - (k + 1)), B l := hstep2
        _ ≤ ∑ i ∈ Finset.range (n + 1), A i * ∑ l ∈ Finset.range (n + 1 - i), B l := hstep3
  have hlower_fold : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + n) x
      ((∑ k ∈ Finset.range n,
        ccOperatorFieldComp (I := I) (M := M) g₀ 0 (3 + k) (1 + n)
          (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 3 1 (cometricCastG0 (I := I) g₀ g₁) n k)
          (iteratedCovGrad (I := I) g₀ 0 3 k
            (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg))).toSection x) ≤
      ((n : ℝ) * operatorFieldApplicationGdiag (E := E) n) * (Klower n *
        Combinatorics.antidiagonalTupleGridWindow
          (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (n + 2)) :=
    le_trans hlower (mul_le_mul_of_nonneg_left (hfold g₁ P htie hδ_le hδ0 hδ n x)
      (mul_nonneg (Nat.cast_nonneg n) (operatorFieldApplicationGdiag_nonneg (E := E) n)))
  have hgrid_nn : 0 ≤ Combinatorics.antidiagonalTupleGridWindow
      (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (n + 2) :=
    Combinatorics.antidiagonalTupleGridWindow_nonneg _
      (fun j => riemannianFiberNormSq_nonneg _ _ _ _ _) (n + 2)
  nlinarith [hcorner, hlower_fold,
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + n) x
      ((iteratedCovGrad (I := I) g₀ 0 3 n (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)).toSection x),
    hgrid_nn]

theorem deTurckVectorFieldCovector_iteratedCovGrad_norm_sq_topOrderSeparated
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    {Λ₀ : ℝ} (hΛ₀0 : 0 ≤ Λ₀) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Flow : ℕ → ℝ, (∀ n, 0 ≤ Flow n) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ₀ ^ 2),
        ∀ n : ℕ, n ≤ a + 1 →
          ‖iteratedCovGrad (I := I) g₀ 0 1 n (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
            Ktop * ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P‖ ^ 2 +
            Flow n * (1 + ∑ j ∈ Finset.range (n + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨Ktop_xi, hKtop_xi_nn, Flow_xi, hFlow_xi_nn, hxi⟩ :=
    metricLoweredConnectionDifference_iteratedCovGrad_norm_sq_topOrderSeparated (I := I) (M := M) g₀ g_bg a ha_super hδ₀ hΛ₀0
  obtain ⟨Kc_top, hKc_top_nn, Kwin, hKwin_nn, hpt_gen⟩ :=
    exists_riemannianFiberNormSq_wOmega_topsep_rf (I := I) (M := M) g₀ g_bg a ha_super hδ₀ hΛ₀0
  obtain ⟨K_rf, hK_rf_nn, hK_rf⟩ :=
    antidiagonalTupleGrid_integral_radiusFree (I := I) (M := M) g₀ hΛ₀0
  refine ⟨Kc_top * Ktop_xi, mul_nonneg hKc_top_nn hKtop_xi_nn,
    fun n => Kc_top * Flow_xi n + Kwin n * ∑ k ∈ Finset.range (n + 2), K_rf k,
    fun n => add_nonneg (mul_nonneg hKc_top_nn (hFlow_xi_nn n))
      (mul_nonneg (hKwin_nn n) (Finset.sum_nonneg fun k _ => hK_rf_nn k)), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hsup n hn
  set S' : ℝ := ∑ j ∈ Finset.range (n + 2),
    ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 with hS'_def
  have hS'_nn : 0 ≤ S' := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + n) x
          ((iteratedCovGrad (I := I) g₀ 0 1 n (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
        Kc_top * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
            ((iteratedCovGrad (I := I) g₀ 0 3 n (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
          + Kwin n * Combinatorics.antidiagonalTupleGridWindow
              (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
                ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (n + 2) :=
    fun x => hpt_gen g₁ P htie hδ_le hδ0 hδ hsup n x
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
      (fun x => Combinatorics.antidiagonalTupleGridWindow
        (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (n + 2))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    simp only [Combinatorics.antidiagonalTupleGridWindow]
    exact MeasureTheory.integrable_finset_sum _ (fun k _ => (hAG k).1)
  have hwxi_int : MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (3 + n)
      (iteratedCovGrad (I := I) g₀ 0 3 n (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg))
  have hbridge := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 0 (1 + n)
    (iteratedCovGrad (I := I) g₀ 0 1 n (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg))
    (fun x => Kc_top * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
          ((iteratedCovGrad (I := I) g₀ 0 3 n (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
        + Kwin n *
          Combinatorics.antidiagonalTupleGridWindow
            (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (n + 2))
    ((hwxi_int.const_mul (Kc_top)).add
      (hwin_int.const_mul (Kwin n)))
    hpt
  rw [MeasureTheory.integral_add (hwxi_int.const_mul (Kc_top))
      (hwin_int.const_mul (Kwin n)),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hbridge
  have hwxi_eq : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
      ‖iteratedCovGrad (I := I) g₀ 0 3 n (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def, tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  have hwin_bd : (∫ x, Combinatorics.antidiagonalTupleGridWindow
      (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (n + 2)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
      (∑ k ∈ Finset.range (n + 2), K_rf k) * (1 + S') := by
    simp only [Combinatorics.antidiagonalTupleGridWindow]
    rw [MeasureTheory.integral_finset_sum _ (fun k _ => (hAG k).1), Finset.sum_mul]
    refine Finset.sum_le_sum (fun k hk => ?_)
    refine le_trans (hAG k).2 ?_
    have hkS' : ‖iteratedCovGrad (I := I) g₀ 0 2 k P‖ ^ 2 ≤ S' :=
      Finset.single_le_sum (f := fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_range.mpr (by rw [Finset.mem_range] at hk; omega))
    refine mul_le_mul_of_nonneg_left ?_ (hK_rf_nn k)
    linarith
  have htop := hxi g₁ P htie hδ_le hδ0 hδ hsup n hn
  have hcoef1_nn : 0 ≤ Kc_top := hKc_top_nn
  have hcoef2_nn : 0 ≤ Kwin n := hKwin_nn n
  calc ‖iteratedCovGrad (I := I) g₀ 0 1 n (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2
      ≤ Kc_top * (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
            ((iteratedCovGrad (I := I) g₀ 0 3 n (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
        + Kwin n *
          (∫ x, Combinatorics.antidiagonalTupleGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (n + 2)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) := hbridge
    _ = Kc_top * ‖iteratedCovGrad (I := I) g₀ 0 3 n (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2
        + Kwin n *
          (∫ x, Combinatorics.antidiagonalTupleGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (n + 2)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) := by rw [hwxi_eq]
    _ ≤ Kc_top * (Ktop_xi * ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P‖ ^ 2 +
            Flow_xi n * (1 + S'))
        + Kwin n *
          ((∑ k ∈ Finset.range (n + 2), K_rf k) * (1 + S')) := by
        have h1 := mul_le_mul_of_nonneg_left htop hcoef1_nn
        have h2 := mul_le_mul_of_nonneg_left hwin_bd hcoef2_nn
        linarith [h1, h2]
    _ = Kc_top * Ktop_xi * ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P‖ ^ 2
        + (Kc_top * Flow_xi n +
            Kwin n *
              ∑ k ∈ Finset.range (n + 2), K_rf k) * (1 + S') := by ring

private lemma riemannianFiberNormSq_iteratedCovGrad_wOmega_antidiagonalTupleGridWindow_rf
    (g₀ g_bg : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Kwo : ℕ → ℝ, (∀ n, 0 ≤ Kwo n) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (n : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + n) x
            ((iteratedCovGrad (I := I) g₀ 0 1 n (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
          Kwo n * Combinatorics.antidiagonalTupleGridWindow
            (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (n + 2) := by
  classical
  obtain ⟨Klower, hKlower_nn, hfold⟩ :=
    cometricCastG0_wXi_twoArm_fold_rf (I := I) (M := M) g₀ g_bg hδ₀
  refine ⟨fun n => operatorFieldApplicationGdiag (E := E) n * Klower n,
    fun n => mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) n) (hKlower_nn n), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ n x
  refine le_trans (operatorFieldApplication_iteratedCovGrad_diagonalProductGrid_le (I := I) (M := M) g₀ 3 1
    (cometricCastG0 (I := I) g₀ g₁) (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg) n x) ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hfold g₁ P htie hδ_le hδ0 hδ n x) (operatorFieldApplicationGdiag_nonneg (E := E) n)

private lemma wCA_wOmega_twoArm_fold_rf
    (g₀ g_bg : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ KB : ℕ → ℝ, (∀ i, 0 ≤ KB i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        (∑ n ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
              ((iteratedCovGrad (I := I) g₀ 1 2 n (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)).toSection x) *
            ∑ l ∈ Finset.range (i + 1 - n),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 1 l
                  (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg)).toSection x)) ≤
          KB i * Combinatorics.antidiagonalTupleGridWindow
            (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (i + 3) := by
  classical
  obtain ⟨Ccd, hCcd_nn, hcd⟩ := riemannianFiberNormSq_iteratedCovGrad_connectionDifferenceSection_antidiagonalTupleGridWindow_rf (I := I) (M := M) g₀ hδ₀
  obtain ⟨Kwo, hKwo_nn, hwo⟩ := riemannianFiberNormSq_iteratedCovGrad_wOmega_antidiagonalTupleGridWindow_rf (I := I) (M := M) g₀ g_bg hδ₀
  refine ⟨fun i => ∑ n ∈ Finset.range (i + 1), ∑ l ∈ Finset.range (i + 1),
      Ccd n * Kwo l * Combinatorics.antidiagonalTupleGridWindowMulConst (n + 1) (l + 1),
    fun i => Finset.sum_nonneg (fun n _ => Finset.sum_nonneg (fun l _ =>
      mul_nonneg (mul_nonneg (hCcd_nn n) (hKwo_nn l))
        (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg (n + 1) (l + 1)))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ i x
  set bP : ℕ → ℝ := fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
    ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x) with hbP_def
  have hbP_nn : ∀ j, 0 ≤ bP j :=
    fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  have hwca : ∀ m : ℕ, riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + m) x
      ((iteratedCovGrad (I := I) g₀ 1 2 m (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)).toSection x) ≤
      Ccd m * Combinatorics.antidiagonalTupleGridWindow bP (m + 2) := by
    intro m
    rw [riemannianFiberNormSq_iteratedCovGrad_connectionDifferenceRaisedEndomorphism_eq_connectionDifferenceSection (I := I) (M := M) g₀ g₁ m x]
    exact hcd g₁ P htie hδ_le hδ0 hδ m x
  have hterm : ∀ n ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)).toSection x) *
        ∑ l ∈ Finset.range (i + 1 - n),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 1 l
              (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
      ∑ l ∈ Finset.range (i + 1),
        (Ccd n * Kwo l * Combinatorics.antidiagonalTupleGridWindowMulConst (n + 1) (l + 1)) *
          Combinatorics.antidiagonalTupleGridWindow bP (i + 3) := by
    intro n hn
    have hni : n ≤ i := by rw [Finset.mem_range] at hn; omega
    have hwcan := hwca n
    rw [Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum (fun l hl => ?_))
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun l _ _ => ?_))
    swap
    · exact mul_nonneg (mul_nonneg (mul_nonneg (hCcd_nn n) (hKwo_nn l))
        (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg (n + 1) (l + 1)))
        (Combinatorics.antidiagonalTupleGridWindow_nonneg bP hbP_nn (i + 3))
    · have hwol := hwo g₁ P htie hδ_le hδ0 hδ l x
      have hmul := Combinatorics.antidiagonalTupleGridWindow_mul_le bP hbP_nn (n + 1) (l + 1)
      have hmono := Combinatorics.antidiagonalTupleGridWindow_mono bP hbP_nn
        (show (n + 1) + (l + 1) + 1 ≤ i + 3 by rw [Finset.mem_range] at hl; omega)
      have hwc_nn : 0 ≤ Combinatorics.antidiagonalTupleGridWindowMulConst (n + 1) (l + 1) :=
        Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg (n + 1) (l + 1)
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
              ((iteratedCovGrad (I := I) g₀ 1 2 n (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 1 l
                (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
          ≤ (Ccd n * Combinatorics.antidiagonalTupleGridWindow bP (n + 2)) *
              (Kwo l * Combinatorics.antidiagonalTupleGridWindow bP (l + 2)) :=
            mul_le_mul hwcan hwol (riemannianFiberNormSq_nonneg _ _ _ _ _)
              (mul_nonneg (hCcd_nn n)
                (Combinatorics.antidiagonalTupleGridWindow_nonneg bP hbP_nn (n + 2)))
        _ = Ccd n * Kwo l * (Combinatorics.antidiagonalTupleGridWindow bP (n + 2) *
              Combinatorics.antidiagonalTupleGridWindow bP (l + 2)) := by ring
        _ ≤ Ccd n * Kwo l * (Combinatorics.antidiagonalTupleGridWindowMulConst (n + 1) (l + 1) *
              Combinatorics.antidiagonalTupleGridWindow bP ((n + 1) + (l + 1) + 1)) := by
            exact mul_le_mul_of_nonneg_left hmul (mul_nonneg (hCcd_nn n) (hKwo_nn l))
        _ ≤ Ccd n * Kwo l * (Combinatorics.antidiagonalTupleGridWindowMulConst (n + 1) (l + 1) *
              Combinatorics.antidiagonalTupleGridWindow bP (i + 3)) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hCcd_nn n) (hKwo_nn l))
            exact mul_le_mul_of_nonneg_left hmono hwc_nn
        _ = (Ccd n * Kwo l * Combinatorics.antidiagonalTupleGridWindowMulConst (n + 1) (l + 1)) *
              Combinatorics.antidiagonalTupleGridWindow bP (i + 3) := by ring
  calc ∑ n ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
            ((iteratedCovGrad (I := I) g₀ 1 2 n (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)).toSection x) *
          ∑ l ∈ Finset.range (i + 1 - n),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 1 l
                (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
      ≤ ∑ n ∈ Finset.range (i + 1), ∑ l ∈ Finset.range (i + 1),
          (Ccd n * Kwo l * Combinatorics.antidiagonalTupleGridWindowMulConst (n + 1) (l + 1)) *
            Combinatorics.antidiagonalTupleGridWindow bP (i + 3) :=
        Finset.sum_le_sum hterm
    _ = (∑ n ∈ Finset.range (i + 1), ∑ l ∈ Finset.range (i + 1),
          Ccd n * Kwo l * Combinatorics.antidiagonalTupleGridWindowMulConst (n + 1) (l + 1)) *
          Combinatorics.antidiagonalTupleGridWindow bP (i + 3) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun n _ => by rw [Finset.sum_mul])

lemma deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference_iteratedCovGrad_norm_sq_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (_ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    {Λ₀ : ℝ} (hΛ₀0 : 0 ≤ Λ₀) :
    ∃ FlowB : ℕ → ℝ, (∀ i, 0 ≤ FlowB i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ₀ ^ 2)
        (i : ℕ),
        ‖iteratedCovGrad (I := I) g₀ 0 2 i (deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
          FlowB i * (1 + ∑ j ∈ Finset.range (i + 3),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨KB, hKB_nn, hfoldB⟩ := wCA_wOmega_twoArm_fold_rf (I := I) (M := M) g₀ g_bg hδ₀
  obtain ⟨K_rf, hK_rf_nn, hK_rf⟩ :=
    antidiagonalTupleGrid_integral_radiusFree (I := I) (M := M) g₀ hΛ₀0
  refine ⟨fun i => (operatorFieldApplicationGdiag (E := E) i * KB i) * ∑ k ∈ Finset.range (i + 3), K_rf k,
    fun i => mul_nonneg (mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) i) (hKB_nn i))
      (Finset.sum_nonneg fun k _ => hK_rf_nn k), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hsup i
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  set S' : ℝ := ∑ j ∈ Finset.range (i + 3),
    ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 with hS'_def
  have hS'_nn : 0 ≤ S' := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 2 i (deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
        (operatorFieldApplicationGdiag (E := E) i * KB i) * Combinatorics.antidiagonalTupleGridWindow
          (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (i + 3) := by
    intro x
    refine le_trans (operatorFieldApplication_iteratedCovGrad_diagonalProductGrid_le (I := I) (M := M) g₀ 1 2
      (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁) (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg) i x) ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hfoldB g₁ P htie hδ_le hδ0 hδ i x)
      (operatorFieldApplicationGdiag_nonneg (E := E) i)
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
      (fun x => Combinatorics.antidiagonalTupleGridWindow
        (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 3))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    simp only [Combinatorics.antidiagonalTupleGridWindow]
    exact MeasureTheory.integrable_finset_sum _ (fun k _ => (hAG k).1)
  have hbridge := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 0 (2 + i)
    (iteratedCovGrad (I := I) g₀ 0 2 i (deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg))
    (fun x => (operatorFieldApplicationGdiag (E := E) i * KB i) * Combinatorics.antidiagonalTupleGridWindow
      (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 3))
    (hwin_int.const_mul (operatorFieldApplicationGdiag (E := E) i * KB i)) hpt
  rw [MeasureTheory.integral_const_mul] at hbridge
  have hwin_bd : (∫ x, Combinatorics.antidiagonalTupleGridWindow
      (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 3)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
      (∑ k ∈ Finset.range (i + 3), K_rf k) * (1 + S') := by
    simp only [Combinatorics.antidiagonalTupleGridWindow]
    rw [MeasureTheory.integral_finset_sum _ (fun k _ => (hAG k).1), Finset.sum_mul]
    refine Finset.sum_le_sum (fun k hk => ?_)
    refine le_trans (hAG k).2 ?_
    have hkS' : ‖iteratedCovGrad (I := I) g₀ 0 2 k P‖ ^ 2 ≤ S' :=
      Finset.single_le_sum (f := fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_range.mpr (by rw [Finset.mem_range] at hk; omega))
    refine mul_le_mul_of_nonneg_left ?_ (hK_rf_nn k)
    linarith
  calc ‖iteratedCovGrad (I := I) g₀ 0 2 i (deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2
      ≤ (operatorFieldApplicationGdiag (E := E) i * KB i) * (∫ x, Combinatorics.antidiagonalTupleGridWindow
          (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 3)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) := hbridge
    _ ≤ (operatorFieldApplicationGdiag (E := E) i * KB i) * ((∑ k ∈ Finset.range (i + 3), K_rf k) * (1 + S')) :=
        mul_le_mul_of_nonneg_left hwin_bd
          (mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) i) (hKB_nn i))
    _ = ((operatorFieldApplicationGdiag (E := E) i * KB i) * ∑ k ∈ Finset.range (i + 3), K_rf k) * (1 + S') := by ring

theorem deTurckVectorFieldCovariantDerivativeLowered_iteratedCovGrad_norm_sq_topOrderSeparated
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    {Λ₀ : ℝ} (hΛ₀0 : 0 ≤ Λ₀) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Flow : ℕ → ℝ, (∀ i, 0 ≤ Flow i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ₀ ^ 2)
        (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 0 2 i (deTurckVectorFieldCovariantDerivativeLowered (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
            Ktop * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 +
            Flow i * (1 + ∑ j ∈ Finset.range (i + 3),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨Ktop_om, hKtop_om_nn, Flow_om, hFlow_om_nn, hom⟩ :=
    deTurckVectorFieldCovector_iteratedCovGrad_norm_sq_topOrderSeparated (I := I) (M := M) g₀ g_bg a ha_super hδ₀ hΛ₀0
  obtain ⟨FlowB, hFlowB_nn, hB⟩ :=
    deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference_iteratedCovGrad_norm_sq_le (I := I) (M := M) g₀ g_bg a ha_super hδ₀ hΛ₀0
  refine ⟨2 * Ktop_om, mul_nonneg (by norm_num) hKtop_om_nn,
    fun i => 2 * Flow_om (i + 1) + 2 * FlowB i,
    fun i => by have := hFlow_om_nn (i + 1); have := hFlowB_nn i; linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hsup i hi
  set S' : ℝ := ∑ j ∈ Finset.range (i + 3),
    ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 with hS'_def
  have hS'_nn : 0 ≤ S' := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hA : ‖iteratedCovGrad (I := I) g₀ 0 2 i (deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
      Ktop_om * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 + Flow_om (i + 1) * (1 + S') := by
    rw [norm_iteratedCovGrad_deTurckVectorFieldCovariantDerivativeLoweredBase_eq_succ_deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg i, hS'_def]
    exact hom g₁ P htie hδ_le hδ0 hδ hsup (i + 1) (by omega)
  have hBi : ‖iteratedCovGrad (I := I) g₀ 0 2 i (deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
      FlowB i * (1 + S') := by
    rw [hS'_def]; exact hB g₁ P htie hδ_le hδ0 hδ hsup i
  have htri : ‖iteratedCovGrad (I := I) g₀ 0 2 i (deTurckVectorFieldCovariantDerivativeLowered (I := I) (M := M) g₀ g₁ g_bg)‖ ≤
      ‖iteratedCovGrad (I := I) g₀ 0 2 i (deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g₀ g₁ g_bg)‖ +
        ‖iteratedCovGrad (I := I) g₀ 0 2 i (deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)‖ := by
    rw [deTurckVectorFieldCovariantDerivativeLowered, iteratedCovGrad_add]
    exact norm_add_le _ _
  nlinarith [htri, hA, hBi,
    norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 i (deTurckVectorFieldCovariantDerivativeLowered (I := I) (M := M) g₀ g₁ g_bg)),
    norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 i (deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g₀ g₁ g_bg)),
    norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 i (deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)),
    sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 2 i (deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g₀ g₁ g_bg)‖ -
      ‖iteratedCovGrad (I := I) g₀ 0 2 i (deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)‖),
    hFlow_om_nn (i + 1), hFlowB_nn i, hS'_nn]

end DifferentialGeometry.Integral.Connection
