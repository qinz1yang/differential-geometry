import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CovariantJet.PointwiseBounds
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckVectorField.EndomorphismInsertion.Bounds
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.Curvature.DecompositionMonomialBounds

noncomputable section


open MeasureTheory Set Filter Topology Bundle Manifold DifferentialGeometry.Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Elliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem contRiemannianFiberNormSq (g₀ : SmoothRiemannianMetric I M) {r s : ℕ}
    (S : SmoothCcTensor g₀ r s) :
    Continuous (fun x : M => riemannianFiberNormSq (I := I) (M := M) g₀ r s x
      (S.toSection x)) := by
  have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M) S
  refine hc.congr (fun x => ?_)
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ r s x
      (S.toSection x),
    ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M) S x]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
private theorem intCapMul (g₀ : SmoothRiemannianMetric I M) {r s t : ℕ}
    (A : SmoothCcTensor g₀ r s) (B : SmoothCcTensor g₀ r t) {Λ : ℝ}
    (hA : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ r s x
      (A.toSection x) ≤ Λ ^ 2) :
    (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ r s x (A.toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ r t x (B.toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤ Λ ^ 2 * ‖B‖ ^ 2 := by
  classical
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  let : MeasurableSpace M := borel M
  have : BorelSpace M := ⟨rfl⟩
  have : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  set μ : MeasureTheory.Measure M := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ
  have : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  have hBint : MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ r t x (B.toSection x)) μ := by
    rw [hμ]
    exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ r t B
  have hprod : MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ r s x (A.toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ r t x (B.toSection x)) μ :=
    ((contRiemannianFiberNormSq (I := I) (M := M) g₀ A).mul
      (contRiemannianFiberNormSq (I := I) (M := M) g₀ B)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hmono : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ r s x (A.toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ r t x (B.toSection x) ∂μ) ≤
      ∫ x, Λ ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ r t x (B.toSection x) ∂μ := by
    refine MeasureTheory.integral_mono hprod (hBint.const_mul _) (fun x => ?_)
    exact mul_le_mul_of_nonneg_right (hA x)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ r t x _)
  refine hmono.trans ?_
  rw [MeasureTheory.integral_const_mul]
  have hnorm : ‖B‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ r t x (B.toSection x) ∂μ := by
    rw [SmoothCcTensor.norm_def, hμ]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ r t B
  rw [hnorm]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
private theorem normSqSmul (g₀ : SmoothRiemannianMetric I M) {r s : ℕ} (c : ℝ)
    (S : SmoothCcTensor g₀ r s) :
    ‖(c • S : SmoothCcTensor g₀ r s)‖ ^ 2 = c ^ 2 * ‖S‖ ^ 2 := by
  classical
  have h1 : ‖(c • S : SmoothCcTensor g₀ r s)‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ r s x ((c • S).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    rw [SmoothCcTensor.norm_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ r s _
  have h2 : ‖S‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ r s x (S.toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    rw [SmoothCcTensor.norm_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ r s S
  rw [h1, h2, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  dsimp only
  rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
    DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_smul (I := I) (M := M) g₀ r s x c _]

theorem gridIntUnit (g₀ : SmoothRiemannianMetric I M) (rb sb : ℕ) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (P : SmoothCcTensor g₀ rb sb) {Λ₀ : ℝ}, 0 ≤ Λ₀ → Λ₀ ≤ 1 →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ rb sb x
          (P.toSection x) ≤ Λ₀ ^ 2) →
        ∀ (i : ℕ), 1 ≤ i → ∀ (n : ℕ), n ≤ i → ∀ (e : Fin n → ℕ), (∑ m, e m) = i →
          (∫ x, ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ rb (sb + e m) x
                  ((iteratedCovGrad (I := I) g₀ rb sb (e m) P).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            K i * ‖iteratedCovGrad (I := I) g₀ rb sb i P‖ ^ 2 := by
  classical
  set Cgn : ℕ → ℝ := fun k =>
    if h : 1 ≤ k then
      (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ rb sb k h).choose
    else 0 with hCgn
  have hCgn_nn : ∀ k, 0 ≤ Cgn k := by
    intro k
    simp only [hCgn]
    split_ifs with h
    · exact (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ rb sb k h).choose_spec.1
    · exact le_refl 0
  refine ⟨fun i => (i : ℝ) * (max (Cgn i) 1) ^ (7 * i), ?_, ?_⟩
  · intro i
    refine mul_nonneg (Nat.cast_nonneg i) (pow_nonneg ?_ _)
    exact le_trans zero_le_one (le_max_right _ _)
  · intro P Λ₀ hΛ₀0 hΛ₀1 hsup i hi1 n hn e he
    have hC_nn : 0 ≤ Cgn i := hCgn_nn i
    have hGN := (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
      (I := I) (M := M) g₀ rb sb i hi1).choose_spec.2 P Λ₀ hΛ₀0 hsup
    have hCeq : (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ rb sb i hi1).choose = Cgn i := by
      simp only [hCgn, dif_pos hi1]
    rw [hCeq] at hGN
    have hmain := grid_prod_int_le (I := I) (M := M) g₀ P
      (R := ‖iteratedCovGrad (I := I) g₀ rb sb i P‖) (norm_nonneg _) i hi1 hΛ₀0 hsup
      (le_refl _) hC_nn hGN n hn e he
    refine hmain.2.trans ?_
    have hmax : max Λ₀ (max (Cgn i) 1) = max (Cgn i) 1 :=
      max_eq_right (le_trans hΛ₀1 (le_max_right _ _))
    rw [hmax]

theorem gridIntTwo (g₀ : SmoothRiemannianMetric I M) (rb sb : ℕ) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (P : SmoothCcTensor g₀ rb sb) {Λ₀ : ℝ}, 0 ≤ Λ₀ → Λ₀ ≤ 1 →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ rb sb x
          (P.toSection x) ≤ Λ₀ ^ 2) →
        ∀ (i d₁ d₂ : ℕ), 2 ≤ i → d₁ + d₂ = i →
          (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ rb (sb + d₁) x
                  ((iteratedCovGrad (I := I) g₀ rb sb d₁ P).toSection x) *
                riemannianFiberNormSq (I := I) (M := M) g₀ rb (sb + d₂) x
                  ((iteratedCovGrad (I := I) g₀ rb sb d₂ P).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            K i * ‖iteratedCovGrad (I := I) g₀ rb sb i P‖ ^ 2 := by
  classical
  obtain ⟨K, hK_nn, hK⟩ := gridIntUnit (I := I) (M := M) g₀ rb sb
  refine ⟨K, hK_nn, ?_⟩
  intro P Λ₀ hΛ₀0 hΛ₀1 hsup i d₁ d₂ hi2 hd
  have hi1 : 1 ≤ i := by omega
  have h := hK P hΛ₀0 hΛ₀1 hsup i hi1 2 hi2 ![d₁, d₂] (by
    rw [Fin.sum_univ_two]; exact hd)
  refine le_trans (le_of_eq ?_) h
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  dsimp only
  rw [Fin.prod_univ_two]
  rfl

private lemma gridIntGrad_high_tail (Λ₁ Rtop K : ℝ)
    (hRtop : 0 ≤ Rtop ^ 2) (hK : 0 ≤ K) :
    K * (max Λ₁ 1 ^ 2 * Rtop ^ 2) ≤ max K 1 * (1 + Λ₁ ^ 2) * Rtop ^ 2 := by
  have hΛsq : max Λ₁ 1 ^ 2 ≤ 1 + Λ₁ ^ 2 := by
    rcases le_total Λ₁ 1 with h | h
    · rw [max_eq_right h]; nlinarith only [sq_nonneg Λ₁]
    · rw [max_eq_left h]; nlinarith
  have hKmax : K ≤ max K 1 := le_max_left _ _
  have hstep : K * (max Λ₁ 1 ^ 2 * Rtop ^ 2) ≤ K * ((1 + Λ₁ ^ 2) * Rtop ^ 2) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hΛsq hRtop) hK
  refine hstep.trans ?_
  have hpos : 0 ≤ (1 + Λ₁ ^ 2) * Rtop ^ 2 := mul_nonneg (by positivity) hRtop
  nlinarith only [mul_le_mul_of_nonneg_right hKmax hpos]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private lemma gridIntGrad_low
    (g₀ : SmoothRiemannianMetric I M)
    (K2 : ℕ → ℝ)
    (P : SmoothCcTensor g₀ 0 2) {Λ₁ : ℝ}
    (hcap : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
      ((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x) ≤ Λ₁ ^ 2)
    (m d₁ d₂ : ℕ) (hm2 : ¬ 2 ≤ m) (hd : d₁ + d₂ = m) :
    (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + d₁)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (1 + d₁) P).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + d₂)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (1 + d₂) P).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
      max (K2 m) 1 * (1 + Λ₁ ^ 2) * ‖iteratedCovGrad (I := I) g₀ 0 2 (1 + m) P‖ ^ 2 := by
  classical
  set Rtop : ℝ := ‖iteratedCovGrad (I := I) g₀ 0 2 (1 + m) P‖ with hRtop
  have hRtop_nn : (0 : ℝ) ≤ Rtop ^ 2 := sq_nonneg _
  have hΛsq_nn : (0 : ℝ) ≤ Λ₁ ^ 2 := sq_nonneg _
  have hone_le : (1 : ℝ) ≤ max (K2 m) 1 := le_max_right _ _
  have hcase : (1 + d₁) = 1 ∧ (1 + d₂) = 1 + m ∨
      (1 + d₂) = 1 ∧ (1 + d₁) = 1 + m := by omega
  have hpos : (0 : ℝ) ≤ (1 + Λ₁ ^ 2) * Rtop ^ 2 :=
    mul_nonneg (by linarith [hΛsq_nn]) hRtop_nn
  have hfin : Λ₁ ^ 2 * Rtop ^ 2 ≤ max (K2 m) 1 * (1 + Λ₁ ^ 2) * Rtop ^ 2 := by
    calc Λ₁ ^ 2 * Rtop ^ 2 ≤ (1 + Λ₁ ^ 2) * Rtop ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) hRtop_nn
      _ ≤ max (K2 m) 1 * ((1 + Λ₁ ^ 2) * Rtop ^ 2) := le_mul_of_one_le_left hpos hone_le
      _ = max (K2 m) 1 * (1 + Λ₁ ^ 2) * Rtop ^ 2 := by ring
  rcases hcase with ⟨h1, h2'⟩ | ⟨h1, h2'⟩
  · have hd1 : d₁ = 0 := by omega
    have hd2 : d₂ = m := by omega
    subst d₁; subst d₂
    exact le_trans (intCapMul (I := I) (M := M) g₀
      (iteratedCovGrad (I := I) g₀ 0 2 1 P)
      (iteratedCovGrad (I := I) g₀ 0 2 (1 + m) P) hcap) hfin
  · have hd1 : d₂ = 0 := by omega
    have hd2 : d₁ = m := by omega
    subst d₁; subst d₂
    have hcomm : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + m)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (1 + m) P).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
            ((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x) ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
        ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
              ((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + m)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (1 + m) P).toSection x) ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      ring
    rw [hcomm]
    exact le_trans (intCapMul (I := I) (M := M) g₀
      (iteratedCovGrad (I := I) g₀ 0 2 1 P)
      (iteratedCovGrad (I := I) g₀ 0 2 (1 + m) P) hcap) hfin

theorem gridIntGrad (g₀ : SmoothRiemannianMetric I M) :
    ∃ K : ℕ → ℝ, (∀ k, 0 ≤ K k) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2) {Λ₁ : ℝ}, 0 ≤ Λ₁ →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
          ((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x) ≤ Λ₁ ^ 2) →
        ∀ (k c₁ c₂ : ℕ), 1 ≤ c₁ → 1 ≤ c₂ → c₁ + c₂ = k + 1 →
          (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + c₁) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 c₁ P).toSection x) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + c₂) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 c₂ P).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            K k * (1 + Λ₁ ^ 2) * ‖iteratedCovGrad (I := I) g₀ 0 2 k P‖ ^ 2 := by
  classical
  obtain ⟨K2, hK2_nn, h2⟩ := gridIntTwo (I := I) (M := M) g₀ 0 (2 + 1)
  refine ⟨fun k => max (K2 (k - 1)) 1, fun k => le_trans zero_le_one (le_max_right _ _), ?_⟩
  intro P Λ₁ hΛ₁0 hcap k c₁ c₂ hc₁ hc₂ hsum
  obtain ⟨m, rfl⟩ : ∃ m, k = 1 + m := ⟨k - 1, by omega⟩
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  let : MeasurableSpace M := borel M
  have : BorelSpace M := ⟨rfl⟩
  have : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  set μ : MeasureTheory.Measure M := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ
  have : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  set Rtop : ℝ := ‖iteratedCovGrad (I := I) g₀ 0 2 (1 + m) P‖ with hRtop
  have hRtop_nn : (0 : ℝ) ≤ Rtop ^ 2 := sq_nonneg _
  have hKidx : (1 + m) - 1 = m := by omega
  have hK2m_nn : 0 ≤ K2 m := hK2_nn m
  have hΛsq_nn : (0 : ℝ) ≤ Λ₁ ^ 2 := sq_nonneg _
  simp only [hKidx]
  have hKmax : K2 m ≤ max (K2 m) 1 := le_max_left _ _
  have hone_le : (1 : ℝ) ≤ max (K2 m) 1 := le_max_right _ _
  by_cases hm2 : 2 ≤ m
  · set Λ : ℝ := max Λ₁ 1 with hΛdef
    have hΛ1 : (1 : ℝ) ≤ Λ := le_max_right _ _
    have hΛ_pos : (0 : ℝ) < Λ := lt_of_lt_of_le zero_lt_one hΛ1
    have hΛ_ne : Λ ≠ 0 := ne_of_gt hΛ_pos
    set u : SmoothCcTensor g₀ 0 (2 + 1) := iteratedCovGrad (I := I) g₀ 0 2 1 P with hu
    set v : SmoothCcTensor g₀ 0 (2 + 1) := (Λ⁻¹ : ℝ) • u with hv
    have hvsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
        (v.toSection x) ≤ (1 : ℝ) ^ 2 := by
      intro x
      have hsm : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x (v.toSection x) =
          (Λ⁻¹) ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
            (u.toSection x) := by
        rw [hv, SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
          DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_smul (I := I) (M := M) g₀ 0 (2 + 1) x (Λ⁻¹) _]
      rw [hsm]
      have hcapx : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x (u.toSection x) ≤
          Λ ^ 2 := by
        refine le_trans (hcap x) ?_
        have hle : Λ₁ ≤ Λ := le_max_left _ _
        nlinarith only [hΛ₁0, hle, hΛ1]
      have hinv_nn : (0 : ℝ) ≤ (Λ⁻¹) ^ 2 := sq_nonneg _
      have hmul : (Λ⁻¹) ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
          (u.toSection x) ≤ (Λ⁻¹) ^ 2 * Λ ^ 2 :=
        mul_le_mul_of_nonneg_left hcapx hinv_nn
      refine hmul.trans (le_of_eq ?_)
      field_simp
    have hjet : ∀ (d : ℕ) (x : M),
        Λ ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 1) + d) x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + 1) d v).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + d)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (1 + d) P).toSection x) := by
      intro d x
      rw [hv, DifferentialGeometry.Analysis.Sobolev.iteratedCovGrad_smul_real
        (I := I) (M := M) g₀ 0 (2 + 1) d (Λ⁻¹) u,
        SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
        DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_smul (I := I) (M := M) g₀ 0 ((2 + 1) + d) x (Λ⁻¹) _, hu,
        riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 2 1 d P x]
      field_simp
    have htop : Λ ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 (2 + 1) m v‖ ^ 2 = Rtop ^ 2 := by
      rw [hv, DifferentialGeometry.Analysis.Sobolev.iteratedCovGrad_smul_real
        (I := I) (M := M) g₀ 0 (2 + 1) m (Λ⁻¹) u,
        normSqSmul (I := I) (M := M) g₀ (Λ⁻¹) _, hu,
        iteratedCovGrad_norm_comp (I := I) (M := M) g₀ 0 2 1 m P, ← hRtop]
      field_simp
    obtain ⟨d₁, rfl⟩ : ∃ d, c₁ = 1 + d := ⟨c₁ - 1, by omega⟩
    obtain ⟨d₂, rfl⟩ : ∃ d, c₂ = 1 + d := ⟨c₂ - 1, by omega⟩
    have hdsum : d₁ + d₂ = m := by omega
    have hgrid := h2 v (Λ₀ := 1) zero_le_one (le_refl 1) hvsup m d₁ d₂ hm2 hdsum
    have hlhs : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + d₁)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (1 + d₁) P).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + d₂)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (1 + d₂) P).toSection x) ∂μ) =
        Λ ^ 4 * ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 1) + d₁) x
              ((iteratedCovGrad (I := I) g₀ 0 (2 + 1) d₁ v).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 1) + d₂) x
              ((iteratedCovGrad (I := I) g₀ 0 (2 + 1) d₂ v).toSection x) ∂μ := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      dsimp only
      rw [← hjet d₁ x, ← hjet d₂ x]
      ring
    rw [hlhs]
    have hΛ4_nn : (0 : ℝ) ≤ Λ ^ 4 := by positivity
    refine le_trans (mul_le_mul_of_nonneg_left hgrid hΛ4_nn) ?_
    have hcollapse : Λ ^ 4 * (K2 m * ‖iteratedCovGrad (I := I) g₀ 0 (2 + 1) m v‖ ^ 2) =
        K2 m * (Λ ^ 2 * (Λ ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 (2 + 1) m v‖ ^ 2)) := by
      ring
    rw [hcollapse, htop]
    exact gridIntGrad_high_tail Λ₁ Rtop (K2 m) hRtop_nn hK2m_nn
  · obtain ⟨d₁, rfl⟩ : ∃ d, c₁ = 1 + d := ⟨c₁ - 1, by omega⟩
    obtain ⟨d₂, rfl⟩ : ∃ d, c₂ = 1 + d := ⟨c₂ - 1, by omega⟩
    have hdsum : d₁ + d₂ = m := by omega
    exact gridIntGrad_low (I := I) (M := M) g₀ K2 P hcap m d₁ d₂ hm2 hdsum

theorem gridIntPull (g₀ : SmoothRiemannianMetric I M) :
    ∃ K : ℕ → ℝ, (∀ k, 0 ≤ K k) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2) {Λ₀ Λ₁ : ℝ}, 0 ≤ Λ₀ → Λ₀ ≤ 1 →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          (P.toSection x) ≤ Λ₀ ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
          ((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x) ≤ Λ₁ ^ 2) →
        ∀ (k : ℕ), 1 ≤ k → ∀ (n : ℕ), n ≤ k → ∀ (e : Fin n → ℕ), (∑ m, e m) = k →
          (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x) *
                ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            Λ₁ ^ 2 * (K k * ‖iteratedCovGrad (I := I) g₀ 0 2 k P‖ ^ 2) := by
  classical
  obtain ⟨K, hK_nn, hK⟩ := gridIntUnit (I := I) (M := M) g₀ 0 2
  refine ⟨K, hK_nn, ?_⟩
  intro P Λ₀ Λ₁ hΛ₀0 hΛ₀1 hsup hcap k hk1 n hn e he
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  let : MeasurableSpace M := borel M
  have : BorelSpace M := ⟨rfl⟩
  have : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  have hGcont : Continuous (fun x : M => ∏ m : Fin n,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) :=
    continuous_finsetProd _ (fun m _ => contRiemannianFiberNormSq (I := I) (M := M) g₀ _)
  have hGint : MeasureTheory.Integrable (fun x : M => ∏ m : Fin n,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    hGcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hPint : MeasureTheory.Integrable (fun x : M =>
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
          ((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x) *
        ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    ((contRiemannianFiberNormSq (I := I) (M := M) g₀ _).mul hGcont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hmono := MeasureTheory.integral_mono hPint (hGint.const_mul (Λ₁ ^ 2)) (fun x => by
    exact mul_le_mul_of_nonneg_right (hcap x)
      (Finset.prod_nonneg (fun m _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + e m) x _)))
  rw [MeasureTheory.integral_const_mul] at hmono
  refine hmono.trans ?_
  exact mul_le_mul_of_nonneg_left (hK P hΛ₀0 hΛ₀1 hsup k hk1 n hn e he) (sq_nonneg Λ₁)

omit [BoundarylessManifold I M] in
theorem gradCapLin (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ c : ℝ, 0 ≤ c ∧
      ∀ (T : SmoothCcTensor g₀ 0 2) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
            ((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x) ≤
          c * ∑ j ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g₀ 0 2 (1 + j) T‖ ^ 2 := by
  classical
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
      (I := I) (M := M) g₀ 0 (2 + 1)
  have hw : Module.finrank ℝ E / 2 + 2 = 3 := by omega
  refine ⟨C ^ 2, by positivity, ?_⟩
  intro T x
  refine le_trans (hC (iteratedCovGrad (I := I) g₀ 0 2 1 T) x) ?_
  rw [hw]
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (sq_nonneg C)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [iteratedCovGrad_norm_comp (I := I) (M := M) g₀ 0 2 1 j T]

end DifferentialGeometry.Integral.Connection

end
