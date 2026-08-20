import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H3GridIntegral
import DifferentialGeometry.Analysis.Sobolev.BoundedFactorProductGrid
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RemainderCoeffPerOrderJetEnvelopes

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
      [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem grad_shift_norm
    (g : SmoothRiemannianMetric I M) (s j : Nat) (T : SmoothCcTensor g 0 s) :
    norm (iteratedCovGrad (I := I) g 0 (s + 1) j
        (covGrad (I := I) (M := M) g 0 s T)) =
      norm (iteratedCovGrad (I := I) g 0 s (j + 1) T) := by
  have hsq :
      norm (iteratedCovGrad (I := I) g 0 (s + 1) j
          (covGrad (I := I) (M := M) g 0 s T)) ^ 2 =
        norm (iteratedCovGrad (I := I) g 0 s (j + 1) T) ^ 2 := by
    rw [← DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm
        (I := I) (M := M) g
        (iteratedCovGrad (I := I) g 0 (s + 1) j
          (covGrad (I := I) (M := M) g 0 s T)),
      ← DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm
        (I := I) (M := M) g (iteratedCovGrad (I := I) g 0 s (j + 1) T),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq
        (I := I) (M := M) g ((s + 1) + j)
        (iteratedCovGrad (I := I) g 0 (s + 1) j
          (covGrad (I := I) (M := M) g 0 s T)),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq
        (I := I) (M := M) g (s + (j + 1))
        (iteratedCovGrad (I := I) g 0 s (j + 1) T)]
    refine MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun x => ?_))
    exact riemannianFiberNormSq_iteratedCovGrad_covGrad_comm_rs
      (I := I) (M := M) g 0 s j T x
  nlinarith [norm_nonneg
    (iteratedCovGrad (I := I) g 0 (s + 1) j
      (covGrad (I := I) (M := M) g 0 s T)),
    norm_nonneg (iteratedCovGrad (I := I) g 0 s (j + 1) T)]

private theorem bfg_four_eq (b : Nat -> Real) :
    Combinatorics.boundedFactorGrid b 3 4 =
      (2 * b 1 * b 3 + b 2 ^ 2) +
      (6 * b 0 * b 1 * b 3 + 3 * b 0 * b 2 ^ 2 +
        3 * b 1 ^ 2 * b 2) +
      (12 * b 0 ^ 2 * b 1 * b 3 + 6 * b 0 ^ 2 * b 2 ^ 2 +
        12 * b 0 * b 1 ^ 2 * b 2 + b 1 ^ 4) := by
  have h1 :
      (∑ e ∈ (Finset.Nat.antidiagonalTuple 1 4).filter
        (fun e => forall m, e m <= 3), ∏ m, b (e m)) = 0 := by
    change
      (((List.Nat.antidiagonalTuple 1 4).filter
        (fun e => forall m, e m <= 3)).map fun e => ∏ m, b (e m)).sum = 0
    norm_num [List.Nat.antidiagonalTuple, Fin.forall_fin_succ,
      Fin.prod_univ_succ, Matrix.cons_val_two, List.filter_cons,
      List.map_cons, List.sum_cons]
  have h2 :
      (∑ e ∈ (Finset.Nat.antidiagonalTuple 2 4).filter
        (fun e => forall m, e m <= 3), ∏ m, b (e m)) =
        2 * b 1 * b 3 + b 2 ^ 2 := by
    change
      (((List.Nat.antidiagonalTuple 2 4).filter
        (fun e => forall m, e m <= 3)).map fun e => ∏ m, b (e m)).sum = _
    norm_num [List.Nat.antidiagonalTuple, Fin.forall_fin_succ,
      Fin.prod_univ_succ, Matrix.cons_val_two, List.filter_cons,
      List.map_cons, List.sum_cons]
    ring
  have h3 :
      (∑ e ∈ (Finset.Nat.antidiagonalTuple 3 4).filter
        (fun e => forall m, e m <= 3), ∏ m, b (e m)) =
        6 * b 0 * b 1 * b 3 + 3 * b 0 * b 2 ^ 2 +
          3 * b 1 ^ 2 * b 2 := by
    change
      (((List.Nat.antidiagonalTuple 3 4).filter
        (fun e => forall m, e m <= 3)).map fun e => ∏ m, b (e m)).sum = _
    norm_num [List.Nat.antidiagonalTuple, Fin.forall_fin_succ,
      Fin.prod_univ_succ, Matrix.cons_val_two, List.filter_cons,
      List.map_cons, List.sum_cons]
    ring
  have h4 :
      (∑ e ∈ (Finset.Nat.antidiagonalTuple 4 4).filter
        (fun e => forall m, e m <= 3), ∏ m, b (e m)) =
        12 * b 0 ^ 2 * b 1 * b 3 + 6 * b 0 ^ 2 * b 2 ^ 2 +
          12 * b 0 * b 1 ^ 2 * b 2 + b 1 ^ 4 := by
    change
      (((List.Nat.antidiagonalTuple 4 4).filter
        (fun e => forall m, e m <= 3)).map fun e => ∏ m, b (e m)).sum = _
    norm_num [List.Nat.antidiagonalTuple, Fin.forall_fin_succ,
      Fin.prod_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      List.filter_cons, List.map_cons, List.sum_cons]
    ring
  unfold Combinatorics.boundedFactorGrid
  simp only [Finset.sum_range_succ, Finset.Nat.antidiagonalTuple_zero_succ,
    Finset.filter_empty, Finset.sum_empty, h1, h2, h3, h4]
  ring

private theorem bfg_four_le
    (b : Nat -> Real) (hb : forall j, 0 <= b j) (Q : Real)
    (hQ : 1 <= Q) (hb0 : b 0 <= Q) (hb1 : b 1 <= Q) :
    Combinatorics.boundedFactorGrid b 3 4 <=
      46 * Q ^ 2 *
        (b 1 * (b 1 + b 2 + b 3) + b 2 * (b 1 + b 2) + b 3 * b 1) := by
  let G : Real :=
    b 1 * (b 1 + b 2 + b 3) + b 2 * (b 1 + b 2) + b 3 * b 1
  have hQ0 : 0 <= Q := le_trans zero_le_one hQ
  have hG0 : 0 <= G := by
    dsimp [G]
    exact add_nonneg
      (add_nonneg
        (mul_nonneg (hb 1) (add_nonneg (add_nonneg (hb 1) (hb 2)) (hb 3)))
        (mul_nonneg (hb 2) (add_nonneg (hb 1) (hb 2))))
      (mul_nonneg (hb 3) (hb 1))
  have hQsq : 1 <= Q ^ 2 := by
    simpa only [one_pow] using pow_le_pow_left₀ zero_le_one hQ 2
  have hGQ : G <= Q * G := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hQ hG0
  have hQG : Q * G <= Q ^ 2 * G := by
    simpa only [one_mul, pow_two, mul_assoc] using
      mul_le_mul_of_nonneg_right hQ (mul_nonneg hQ0 hG0)
  have hGQ2 : G <= Q ^ 2 * G := hGQ.trans hQG
  have h13 : b 1 * b 3 <= G := by
    dsimp [G]
    nlinarith only [mul_nonneg (hb 1) (hb 1), mul_nonneg (hb 1) (hb 2),
      mul_nonneg (hb 2) (hb 1), mul_nonneg (hb 2) (hb 2),
      mul_nonneg (hb 3) (hb 1)]
  have h22 : b 2 ^ 2 <= G := by
    dsimp [G]
    nlinarith only [mul_nonneg (hb 1) (hb 1), mul_nonneg (hb 1) (hb 2),
      mul_nonneg (hb 1) (hb 3), mul_nonneg (hb 2) (hb 1),
      mul_nonneg (hb 3) (hb 1)]
  have h12 : b 1 * b 2 <= G := by
    dsimp [G]
    nlinarith only [mul_nonneg (hb 1) (hb 1), mul_nonneg (hb 1) (hb 3),
      mul_nonneg (hb 2) (hb 1), mul_nonneg (hb 2) (hb 2),
      mul_nonneg (hb 3) (hb 1)]
  have h11 : b 1 ^ 2 <= G := by
    dsimp [G]
    nlinarith only [mul_nonneg (hb 1) (hb 2), mul_nonneg (hb 1) (hb 3),
      mul_nonneg (hb 2) (hb 1), mul_nonneg (hb 2) (hb 2),
      mul_nonneg (hb 3) (hb 1)]
  have hb0sq : b 0 ^ 2 <= Q ^ 2 :=
    pow_le_pow_left₀ (hb 0) hb0 2
  have hb1sq : b 1 ^ 2 <= Q ^ 2 :=
    pow_le_pow_left₀ (hb 1) hb1 2
  have hb01 : b 0 * b 1 <= Q ^ 2 := by
    calc
      b 0 * b 1 <= Q * Q := mul_le_mul hb0 hb1 (hb 1) hQ0
      _ = Q ^ 2 := by ring
  have t13 : b 1 * b 3 <= Q ^ 2 * G := h13.trans hGQ2
  have t22 : b 2 ^ 2 <= Q ^ 2 * G := h22.trans hGQ2
  have t013 : b 0 * b 1 * b 3 <= Q ^ 2 * G := by
    calc
      b 0 * b 1 * b 3 = b 0 * (b 1 * b 3) := by ring
      _ <= Q * G := mul_le_mul hb0 h13 (mul_nonneg (hb 1) (hb 3)) hQ0
      _ <= Q ^ 2 * G := hQG
  have t022 : b 0 * b 2 ^ 2 <= Q ^ 2 * G := by
    calc
      b 0 * b 2 ^ 2 <= Q * G :=
        mul_le_mul hb0 h22 (sq_nonneg (b 2)) hQ0
      _ <= Q ^ 2 * G := hQG
  have t112 : b 1 ^ 2 * b 2 <= Q ^ 2 * G := by
    calc
      b 1 ^ 2 * b 2 = b 1 * (b 1 * b 2) := by ring
      _ <= Q * G := mul_le_mul hb1 h12 (mul_nonneg (hb 1) (hb 2)) hQ0
      _ <= Q ^ 2 * G := hQG
  have t0013 : b 0 ^ 2 * b 1 * b 3 <= Q ^ 2 * G := by
    calc
      b 0 ^ 2 * b 1 * b 3 = b 0 ^ 2 * (b 1 * b 3) := by ring
      _ <= Q ^ 2 * G :=
        mul_le_mul hb0sq h13 (mul_nonneg (hb 1) (hb 3)) (sq_nonneg Q)
  have t0022 : b 0 ^ 2 * b 2 ^ 2 <= Q ^ 2 * G :=
    mul_le_mul hb0sq h22 (sq_nonneg (b 2)) (sq_nonneg Q)
  have t0112 : b 0 * b 1 ^ 2 * b 2 <= Q ^ 2 * G := by
    calc
      b 0 * b 1 ^ 2 * b 2 = (b 0 * b 1) * (b 1 * b 2) := by ring
      _ <= Q ^ 2 * G :=
        mul_le_mul hb01 h12 (mul_nonneg (hb 1) (hb 2)) (sq_nonneg Q)
  have t1111 : b 1 ^ 4 <= Q ^ 2 * G := by
    calc
      b 1 ^ 4 = b 1 ^ 2 * b 1 ^ 2 := by ring
      _ <= Q ^ 2 * G :=
        mul_le_mul hb1sq h11 (sq_nonneg (b 1)) (sq_nonneg Q)
  change Combinatorics.boundedFactorGrid b 3 4 <= 46 * Q ^ 2 * G
  rw [bfg_four_eq]
  nlinarith only [t13, t22, t013, t022, t112, t0013, t0022, t0112, t1111]

private theorem h3_bfg_four_int
    (hDim : Module.finrank Real E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ K : Real -> Real,
      (forall A, 0 <= A -> 0 <= K A) ∧
      forall (P : SmoothCcTensor g 0 2) (A : Real), 0 <= A ->
        (∑ j ∈ Finset.range 4,
          norm (iteratedCovGrad (I := I) g 0 2 j P) ^ 2) <= A ^ 2 ->
        MeasureTheory.Integrable
            (fun x => Combinatorics.boundedFactorGrid
              (fun l => riemannianFiberNormSq (I := I) (M := M) g 0 (2 + l) x
                ((iteratedCovGrad (I := I) g 0 2 l P).toSection x)) 3 4)
            (riemannianVolumeMeasure (I := I) (M := M) g) ∧
          (∫ x, Combinatorics.boundedFactorGrid
              (fun l => riemannianFiberNormSq (I := I) (M := M) g 0 (2 + l) x
              ((iteratedCovGrad (I := I) g 0 2 l P).toSection x)) 3 4
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) <= K A := by
  classical
  haveI : IsFiniteMeasure
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  obtain ⟨C0, hC0, hpt0⟩ :=
    exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
      (I := I) (M := M) g 0 2
  obtain ⟨C1, hC1, hpt1⟩ :=
    exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
      (I := I) (M := M) g 0 3
  obtain ⟨Cp, hCp, hpair⟩ :=
    exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
      (I := I) (M := M) g 0 0 3 3 2
  let Q : Real -> Real := fun A =>
    max 1 (max ((C0 * A) ^ 2) ((C1 * A) ^ 2))
  let G : Real -> Real := fun A =>
    Cp * (2 * (C1 * A) ^ 2 * A ^ 2)
  let K : Real -> Real := fun A => 46 * (Q A) ^ 2 * G A
  have hQ : forall A, 1 <= Q A := fun A => le_max_left _ _
  have hG : forall A, 0 <= A -> 0 <= G A := by
    intro A hA
    dsimp [G]
    positivity
  refine ⟨K, fun A hA => mul_nonneg
    (mul_nonneg (by norm_num) (sq_nonneg (Q A))) (hG A hA), ?_⟩
  intro P A hA hPjet
  let b : M -> Nat -> Real := fun x l =>
    riemannianFiberNormSq (I := I) (M := M) g 0 (2 + l) x
      ((iteratedCovGrad (I := I) g 0 2 l P).toSection x)
  have hb : forall (x : M) l, 0 <= b x l :=
    fun x l => riemannianFiberNormSq_nonneg
      (I := I) (M := M) g 0 (2 + l) x _
  have hrange : Finset.range (Module.finrank Real E / 2 + 2) =
      Finset.range 3 := by
    rw [hDim]
  have hP0jet :
      (∑ j ∈ Finset.range 3,
        norm (iteratedCovGrad (I := I) g 0 2 j P) ^ 2) <= A ^ 2 :=
    (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (by omega))
      (fun j _ _ => sq_nonneg _)).trans hPjet
  have hb0 : forall x : M, b x 0 <= (C0 * A) ^ 2 := by
    intro x
    have hx := hpt0 P x
    rw [hrange] at hx
    calc
      b x 0 <= C0 ^ 2 * (∑ j ∈ Finset.range 3,
          norm (iteratedCovGrad (I := I) g 0 2 j P) ^ 2) := by
        simpa only [b, Nat.reduceAdd, iteratedCovGrad_zero] using hx
      _ <= C0 ^ 2 * A ^ 2 :=
        mul_le_mul_of_nonneg_left hP0jet (sq_nonneg C0)
      _ = (C0 * A) ^ 2 := by ring
  let V : SmoothCcTensor g 0 3 :=
    covGrad (I := I) (M := M) g 0 2 P
  have hVjet :
      (∑ j ∈ Finset.range 3,
        norm (iteratedCovGrad (I := I) g 0 3 j V) ^ 2) <= A ^ 2 := by
    have hPjet' := hPjet
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hPjet'
    dsimp [V]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [grad_shift_norm (I := I) (M := M) g 2 0 P,
      grad_shift_norm (I := I) (M := M) g 2 1 P,
      grad_shift_norm (I := I) (M := M) g 2 2 P]
    nlinarith [hPjet', sq_nonneg
      (norm (iteratedCovGrad (I := I) g 0 2 0 P))]
  have hb1 : forall x : M, b x 1 <= (C1 * A) ^ 2 := by
    intro x
    have hx := hpt1 V x
    rw [hrange] at hx
    calc
      b x 1 =
          riemannianFiberNormSq (I := I) (M := M) g 0 3 x
            (V.toSection x) := by
        dsimp [b, V]
      _ <= C1 ^ 2 * (∑ j ∈ Finset.range 3,
          norm (iteratedCovGrad (I := I) g 0 3 j V) ^ 2) := hx
      _ <= C1 ^ 2 * A ^ 2 :=
        mul_le_mul_of_nonneg_left hVjet (sq_nonneg C1)
      _ = (C1 * A) ^ 2 := by ring
  have hb0Q : forall x, b x 0 <= Q A := fun x =>
    (hb0 x).trans (le_trans (le_max_left _ _) (le_max_right _ _))
  have hb1Q : forall x, b x 1 <= Q A := fun x =>
    (hb1 x).trans (le_trans (le_max_right _ _) (le_max_right _ _))
  let pair : M -> Real := fun x =>
    ∑ i ∈ Finset.range 3,
      riemannianFiberNormSq (I := I) (M := M) g 0 (3 + i) x
          ((iteratedCovGrad (I := I) g 0 3 i V).toSection x) *
        ∑ l ∈ Finset.range (3 - i),
          riemannianFiberNormSq (I := I) (M := M) g 0 (3 + l) x
            ((iteratedCovGrad (I := I) g 0 3 l V).toSection x)
  have hL : 0 <= C1 * A := mul_nonneg hC1 hA
  obtain ⟨hpair_int, hpair_bound⟩ :=
    hpair V V (C1 * A) (C1 * A) hL hL hb1 hb1
  have hpair_int' : MeasureTheory.Integrable pair
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    simpa only [pair] using hpair_int
  have hpair_bound' :
      (∫ x, pair x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) <=
        G A := by
    calc
      _ <= Cp * ((C1 * A) ^ 2 * (∑ i ∈ Finset.range 3,
              norm (iteratedCovGrad (I := I) g 0 3 i V) ^ 2) +
            (C1 * A) ^ 2 * (∑ l ∈ Finset.range 3,
              norm (iteratedCovGrad (I := I) g 0 3 l V) ^ 2)) := by
        simpa only [pair] using hpair_bound
      _ <= Cp * (2 * (C1 * A) ^ 2 * A ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hCp
        have hmul := mul_le_mul_of_nonneg_left hVjet (sq_nonneg (C1 * A))
        nlinarith
      _ = G A := by rfl
  have hshift : forall m x,
      riemannianFiberNormSq (I := I) (M := M) g 0 (3 + m) x
          ((iteratedCovGrad (I := I) g 0 3 m V).toSection x) =
        b x (m + 1) := by
    intro m x
    dsimp [V, b]
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      riemannianFiberNormSq_iteratedCovGrad_covGrad_comm_rs
        (I := I) (M := M) g 0 2 m P x
  have hpair_eq : forall x,
      pair x =
        b x 1 * (b x 1 + b x 2 + b x 3) +
          b x 2 * (b x 1 + b x 2) + b x 3 * b x 1 := by
    intro x
    simp only [pair]
    simp_rw [hshift]
    norm_num [Finset.sum_range_succ]
  have hfour_le : forall x,
      Combinatorics.boundedFactorGrid (b x) 3 4 <=
        46 * (Q A) ^ 2 * pair x := by
    intro x
    rw [hpair_eq x]
    exact bfg_four_le (b x) (hb x) (Q A) (hQ A) (hb0Q x) (hb1Q x)
  have hbcont : forall l, Continuous (fun x => b x l) := by
    intro l
    have hc := Integral.L2.SmoothCcTensor.continuous_inner_self
      (I := I) (M := M) (iteratedCovGrad (I := I) g 0 2 l P)
    refine hc.congr (fun x => ?_)
    change tensorInnerPointwise (I := I) (M := M) g 0 (2 + l) x
        ((iteratedCovGrad (I := I) g 0 2 l P).toFun x)
        ((iteratedCovGrad (I := I) g 0 2 l P).toFun x) = b x l
    dsimp [b]
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise
        (I := I) (M := M) g 0 (2 + l) x
        ((iteratedCovGrad (I := I) g 0 2 l P).toSection x),
      ← Integral.L2.SmoothCcTensor.toFun_apply
        (I := I) (M := M) (iteratedCovGrad (I := I) g 0 2 l P) x]
  have hfour_cont :
      Continuous (fun x => Combinatorics.boundedFactorGrid (b x) 3 4) := by
    simp only [Combinatorics.boundedFactorGrid]
    refine continuous_finset_sum _ (fun n _ => ?_)
    refine continuous_finset_sum _ (fun e _ => ?_)
    exact continuous_finset_prod _ (fun m _ => hbcont (e m))
  have hfour_int : MeasureTheory.Integrable
      (fun x => Combinatorics.boundedFactorGrid (b x) 3 4)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    hfour_cont.integrable_of_hasCompactSupport
      (μ := riemannianVolumeMeasure (I := I) (M := M) g)
      (HasCompactSupport.of_compactSpace _)
  refine ⟨hfour_int, ?_⟩
  calc
    (∫ x, Combinatorics.boundedFactorGrid (b x) 3 4
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
        <= ∫ x, 46 * (Q A) ^ 2 * pair x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
      MeasureTheory.integral_mono hfour_int
        (hpair_int'.const_mul (46 * (Q A) ^ 2)) hfour_le
    _ = 46 * (Q A) ^ 2 *
        (∫ x, pair x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
      rw [MeasureTheory.integral_const_mul]
    _ <= 46 * (Q A) ^ 2 * G A :=
      mul_le_mul_of_nonneg_left hpair_bound'
        (mul_nonneg (by norm_num) (sq_nonneg (Q A)))
    _ = K A := by rfl

theorem h3_bfg5_int
    (hDim : Module.finrank Real E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ K : Real -> Real,
      (forall A, 0 <= A -> 0 <= K A) ∧
      forall (P : SmoothCcTensor g 0 2) (A : Real), 0 <= A ->
        (∑ j ∈ Finset.range 4,
          norm (iteratedCovGrad (I := I) g 0 2 j P) ^ 2) <= A ^ 2 ->
        MeasureTheory.Integrable
            (fun x => Combinatorics.boundedFactorGridWindow
              (fun l => riemannianFiberNormSq (I := I) (M := M) g 0 (2 + l) x
                ((iteratedCovGrad (I := I) g 0 2 l P).toSection x)) 3 5)
            (riemannianVolumeMeasure (I := I) (M := M) g) ∧
          (∫ x, Combinatorics.boundedFactorGridWindow
              (fun l => riemannianFiberNormSq (I := I) (M := M) g 0 (2 + l) x
                ((iteratedCovGrad (I := I) g 0 2 l P).toSection x)) 3 5
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) <= K A := by
  classical
  obtain ⟨Klo, hKlo, hlo⟩ := h3_grid_int (I := I) (M := M) hDim g
  obtain ⟨K4, hK4, hfour⟩ := h3_bfg_four_int (I := I) (M := M) hDim g
  let K : Real -> Real := fun A =>
    (∑ k ∈ Finset.range 4, Klo A k) + K4 A
  refine ⟨K, ?_, ?_⟩
  · intro A hA
    exact add_nonneg
      (Finset.sum_nonneg (fun k _ => hKlo A hA k)) (hK4 A hA)
  · intro P A hA hPjet
    let b : M -> Nat -> Real := fun x l =>
      riemannianFiberNormSq (I := I) (M := M) g 0 (2 + l) x
        ((iteratedCovGrad (I := I) g 0 2 l P).toSection x)
    have hlow : forall k, k < 4 ->
        MeasureTheory.Integrable
            (fun x => Combinatorics.boundedFactorGrid (b x) 3 k)
            (riemannianVolumeMeasure (I := I) (M := M) g) ∧
          (∫ x, Combinatorics.boundedFactorGrid (b x) 3 k
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) <= Klo A k := by
      intro k hk
      have h := hlo P A hA hPjet k (by omega)
      change MeasureTheory.Integrable
          (fun x => Combinatorics.antidiagonalTupleGrid (b x) k)
          (riemannianVolumeMeasure (I := I) (M := M) g) ∧
        (∫ x, Combinatorics.antidiagonalTupleGrid (b x) k
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) <= Klo A k at h
      have heq : forall x,
          Combinatorics.antidiagonalTupleGrid (b x) k =
            Combinatorics.boundedFactorGrid (b x) 3 k := fun x =>
        Combinatorics.antidiagonalTupleGrid_eq_boundedFactorGrid
          (b x) (by omega)
      simpa only [heq] using h
    have hfour' :
        MeasureTheory.Integrable
            (fun x => Combinatorics.boundedFactorGrid (b x) 3 4)
            (riemannianVolumeMeasure (I := I) (M := M) g) ∧
          (∫ x, Combinatorics.boundedFactorGrid (b x) 3 4
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) <= K4 A := by
      simpa only [b] using hfour P A hA hPjet
    have hlow_int : MeasureTheory.Integrable
        (fun x => ∑ k ∈ Finset.range 4,
          Combinatorics.boundedFactorGrid (b x) 3 k)
        (riemannianVolumeMeasure (I := I) (M := M) g) :=
      MeasureTheory.integrable_finset_sum (Finset.range 4)
        (fun k hk => (hlow k (Finset.mem_range.mp hk)).1)
    have hwindow : forall x,
        Combinatorics.boundedFactorGridWindow (b x) 3 5 =
          (∑ k ∈ Finset.range 4,
            Combinatorics.boundedFactorGrid (b x) 3 k) +
            Combinatorics.boundedFactorGrid (b x) 3 4 := by
      intro x
      rw [Combinatorics.boundedFactorGridWindow, Finset.sum_range_succ]
    refine ⟨?_, ?_⟩
    · change MeasureTheory.Integrable
        (fun x => Combinatorics.boundedFactorGridWindow (b x) 3 5)
        (riemannianVolumeMeasure (I := I) (M := M) g)
      simpa only [hwindow] using hlow_int.add hfour'.1
    · calc
        (∫ x, Combinatorics.boundedFactorGridWindow (b x) 3 5
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
            ∫ x, ((∑ k ∈ Finset.range 4,
              Combinatorics.boundedFactorGrid (b x) 3 k) +
                Combinatorics.boundedFactorGrid (b x) 3 4)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
          exact MeasureTheory.integral_congr_ae
            (Filter.Eventually.of_forall hwindow)
        _ = (∫ x, ∑ k ∈ Finset.range 4,
              Combinatorics.boundedFactorGrid (b x) 3 k
                ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
            ∫ x, Combinatorics.boundedFactorGrid (b x) 3 4
              ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
          MeasureTheory.integral_add hlow_int hfour'.1
        _ = (∑ k ∈ Finset.range 4,
              ∫ x, Combinatorics.boundedFactorGrid (b x) 3 k
                ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
            ∫ x, Combinatorics.boundedFactorGrid (b x) 3 4
              ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
          rw [MeasureTheory.integral_finset_sum _
            (fun k hk => (hlow k (Finset.mem_range.mp hk)).1)]
        _ <= (∑ k ∈ Finset.range 4, Klo A k) + K4 A := by
          exact add_le_add
            (Finset.sum_le_sum
              (fun k hk => (hlow k (Finset.mem_range.mp hk)).2))
            hfour'.2
        _ = K A := by rfl

theorem h2_of_bfg5
    (hDim : Module.finrank Real E = 3)
    (g : SmoothRiemannianMetric I M) {r s : Nat} (C : Nat -> Real)
    (hC : forall i, 0 <= C i) :
    ∃ B : Real -> Real,
      (forall A, 0 <= A -> 0 <= B A) ∧
      forall (P : SmoothCcTensor g 0 2) (Phi : SmoothCcTensor g r s)
        (A : Real), 0 <= A ->
        (∑ j ∈ Finset.range 4,
          norm (iteratedCovGrad (I := I) g 0 2 j P) ^ 2) <= A ^ 2 ->
        (forall (i : Nat), i < 3 -> forall x : M,
          riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
              ((iteratedCovGrad (I := I) g r s i Phi).toSection x) <=
            C i * Combinatorics.boundedFactorGridWindow
              (fun l => riemannianFiberNormSq (I := I) (M := M) g 0 (2 + l) x
                ((iteratedCovGrad (I := I) g 0 2 l P).toSection x))
              (i + 1) (i + 3)) ->
        (∑ i ∈ Finset.range 3,
          norm (iteratedCovGrad (I := I) g r s i Phi) ^ 2) <= (B A) ^ 2 := by
  classical
  obtain ⟨K, hK, hwindow⟩ := h3_bfg5_int (I := I) (M := M) hDim g
  let Q : Real -> Real := fun A =>
    (∑ i ∈ Finset.range 3, C i) * K A
  let B : Real -> Real := fun A => Real.sqrt (Q A)
  have hCsum : 0 <= ∑ i ∈ Finset.range 3, C i :=
    Finset.sum_nonneg fun i _ => hC i
  have hQ : forall A, 0 <= A -> 0 <= Q A := by
    intro A hA
    exact mul_nonneg hCsum (hK A hA)
  refine ⟨B, fun A _ => Real.sqrt_nonneg _, ?_⟩
  intro P Phi A hA hPjet hPhi
  obtain ⟨hwindow_int, hwindow_bound⟩ := hwindow P A hA hPjet
  let b : M -> Nat -> Real := fun x l =>
    riemannianFiberNormSq (I := I) (M := M) g 0 (2 + l) x
      ((iteratedCovGrad (I := I) g 0 2 l P).toSection x)
  have hb : forall x l, 0 <= b x l := by
    intro x l
    exact riemannianFiberNormSq_nonneg
      (I := I) (M := M) g 0 (2 + l) x _
  have hwindow_int' : MeasureTheory.Integrable
      (fun x => Combinatorics.boundedFactorGridWindow (b x) 3 5)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    simpa only [b] using hwindow_int
  have hwindow_bound' :
      (∫ x, Combinatorics.boundedFactorGridWindow (b x) 3 5
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) <= K A := by
    simpa only [b] using hwindow_bound
  have hterm : forall i, i < 3 ->
      norm (iteratedCovGrad (I := I) g r s i Phi) ^ 2 <= C i * K A := by
    intro i hi
    have hmono : forall x,
        Combinatorics.boundedFactorGridWindow (b x) (i + 1) (i + 3) <=
          Combinatorics.boundedFactorGridWindow (b x) 3 5 := by
      intro x
      exact Combinatorics.boundedFactorGridWindow_mono
        (b x) (hb x) (by omega) (by omega)
    have hscaled_int : MeasureTheory.Integrable
        (fun x => C i * Combinatorics.boundedFactorGridWindow (b x) 3 5)
        (riemannianVolumeMeasure (I := I) (M := M) g) :=
      hwindow_int'.const_mul (C i)
    have hpoint : forall x,
        riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
            ((iteratedCovGrad (I := I) g r s i Phi).toSection x) <=
          C i * Combinatorics.boundedFactorGridWindow (b x) 3 5 := by
      intro x
      exact (hPhi i hi x).trans
        (mul_le_mul_of_nonneg_left (hmono x) (hC i))
    have hnorm := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
      (I := I) (M := M) g r (s + i)
      (iteratedCovGrad (I := I) g r s i Phi)
      (fun x => C i * Combinatorics.boundedFactorGridWindow (b x) 3 5)
      hscaled_int hpoint
    calc
      norm (iteratedCovGrad (I := I) g r s i Phi) ^ 2 <=
          ∫ x, C i * Combinatorics.boundedFactorGridWindow (b x) 3 5
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := hnorm
      _ = C i * (∫ x, Combinatorics.boundedFactorGridWindow (b x) 3 5
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
          rw [MeasureTheory.integral_const_mul]
      _ <= C i * K A := mul_le_mul_of_nonneg_left hwindow_bound' (hC i)
  have hsum :
      (∑ i ∈ Finset.range 3,
        norm (iteratedCovGrad (I := I) g r s i Phi) ^ 2) <=
        ∑ i ∈ Finset.range 3, C i * K A :=
    Finset.sum_le_sum fun i hi => hterm i (Finset.mem_range.mp hi)
  change _ <= (B A) ^ 2
  rw [show (B A) ^ 2 = Q A by
    simp only [B, Real.sq_sqrt (hQ A hA)]]
  calc
    _ <= ∑ i ∈ Finset.range 3, C i * K A := hsum
    _ = (∑ i ∈ Finset.range 3, C i) * K A := by
      rw [Finset.sum_mul]
    _ = Q A := by rfl

theorem h2_of_bfg5_top
    (hDim : Module.finrank Real E = 3)
    (g : SmoothRiemannianMetric I M) {r s : Nat}
    (Ctop C : Nat -> Real) (hC : forall i, 0 <= C i) :
    ∃ B : Real -> Real,
      (forall A, 0 <= A -> 0 <= B A) ∧
      forall (P : SmoothCcTensor g 0 2) (Phi : SmoothCcTensor g r s)
        (A : Real), 0 <= A ->
        (∑ j ∈ Finset.range 4,
          norm (iteratedCovGrad (I := I) g 0 2 j P) ^ 2) <= A ^ 2 ->
        (forall (i : Nat), i < 3 -> forall x : M,
          riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
              ((iteratedCovGrad (I := I) g r s i Phi).toSection x) <=
            Ctop i *
                riemannianFiberNormSq (I := I) (M := M) g 0 (2 + (i + 2)) x
                  ((iteratedCovGrad (I := I) g 0 2 (i + 2) P).toSection x) +
              C i * Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g 0 2 l P).toSection x))
                (i + 1) (i + 3)) ->
        (∑ i ∈ Finset.range 3,
          norm (iteratedCovGrad (I := I) g r s i Phi) ^ 2) <=
            (∑ i ∈ Finset.range 3,
              Ctop i * norm (iteratedCovGrad (I := I) g 0 2 (i + 2) P) ^ 2) +
              (B A) ^ 2 := by
  classical
  obtain ⟨K, hK, hwindow⟩ := h3_bfg5_int (I := I) (M := M) hDim g
  let Q : Real -> Real := fun A =>
    (∑ i ∈ Finset.range 3, C i) * K A
  let B : Real -> Real := fun A => Real.sqrt (Q A)
  have hCsum : 0 <= ∑ i ∈ Finset.range 3, C i :=
    Finset.sum_nonneg fun i _ => hC i
  have hQ : forall A, 0 <= A -> 0 <= Q A := by
    intro A hA
    exact mul_nonneg hCsum (hK A hA)
  refine ⟨B, fun A _ => Real.sqrt_nonneg _, ?_⟩
  intro P Phi A hA hPjet hPhi
  obtain ⟨hwindow_int, hwindow_bound⟩ := hwindow P A hA hPjet
  let b : M -> Nat -> Real := fun x l =>
    riemannianFiberNormSq (I := I) (M := M) g 0 (2 + l) x
      ((iteratedCovGrad (I := I) g 0 2 l P).toSection x)
  have hb : forall x l, 0 <= b x l := by
    intro x l
    exact riemannianFiberNormSq_nonneg
      (I := I) (M := M) g 0 (2 + l) x _
  have hwindow_int' : MeasureTheory.Integrable
      (fun x => Combinatorics.boundedFactorGridWindow (b x) 3 5)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    simpa only [b] using hwindow_int
  have hwindow_bound' :
      (∫ x, Combinatorics.boundedFactorGridWindow (b x) 3 5
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) <= K A := by
    simpa only [b] using hwindow_bound
  have hterm : forall i, i < 3 ->
      norm (iteratedCovGrad (I := I) g r s i Phi) ^ 2 <=
        Ctop i * norm (iteratedCovGrad (I := I) g 0 2 (i + 2) P) ^ 2 +
          C i * K A := by
    intro i hi
    let head : M -> Real := fun x =>
      riemannianFiberNormSq (I := I) (M := M) g 0 (2 + (i + 2)) x
        ((iteratedCovGrad (I := I) g 0 2 (i + 2) P).toSection x)
    have hhead_int : MeasureTheory.Integrable head
        (riemannianVolumeMeasure (I := I) (M := M) g) :=
      integrable_riemannianFiberNormSq_toSection
        (I := I) (M := M) g 0 (2 + (i + 2))
        (iteratedCovGrad (I := I) g 0 2 (i + 2) P)
    have hmono : forall x,
        Combinatorics.boundedFactorGridWindow (b x) (i + 1) (i + 3) <=
          Combinatorics.boundedFactorGridWindow (b x) 3 5 := by
      intro x
      exact Combinatorics.boundedFactorGridWindow_mono
        (b x) (hb x) (by omega) (by omega)
    have hscaled_int : MeasureTheory.Integrable
        (fun x => Ctop i * head x +
          C i * Combinatorics.boundedFactorGridWindow (b x) 3 5)
        (riemannianVolumeMeasure (I := I) (M := M) g) :=
      (hhead_int.const_mul (Ctop i)).add (hwindow_int'.const_mul (C i))
    have hpoint : forall x,
        riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
            ((iteratedCovGrad (I := I) g r s i Phi).toSection x) <=
          Ctop i * head x +
            C i * Combinatorics.boundedFactorGridWindow (b x) 3 5 := by
      intro x
      have hbase := hPhi i hi x
      change _ <= Ctop i * head x +
        C i * Combinatorics.boundedFactorGridWindow (b x) (i + 1) (i + 3)
        at hbase
      exact hbase.trans
        (add_le_add (le_refl _)
          (mul_le_mul_of_nonneg_left (hmono x) (hC i)))
    have hnorm := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
      (I := I) (M := M) g r (s + i)
      (iteratedCovGrad (I := I) g r s i Phi)
      (fun x => Ctop i * head x +
        C i * Combinatorics.boundedFactorGridWindow (b x) 3 5)
      hscaled_int hpoint
    have hhead :
        (∫ x, head x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
          norm (iteratedCovGrad (I := I) g 0 2 (i + 2) P) ^ 2 := by
      rw [SmoothCcTensor.norm_def (I := I) (M := M)
          (iteratedCovGrad (I := I) g 0 2 (i + 2) P),
        tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
          (I := I) (M := M) g 0 (2 + (i + 2))
          (iteratedCovGrad (I := I) g 0 2 (i + 2) P)]
    calc
      norm (iteratedCovGrad (I := I) g r s i Phi) ^ 2 <=
          ∫ x, (Ctop i * head x +
            C i * Combinatorics.boundedFactorGridWindow (b x) 3 5)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := hnorm
      _ = Ctop i * (∫ x, head x
              ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
            C i * (∫ x, Combinatorics.boundedFactorGridWindow (b x) 3 5
              ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
          rw [MeasureTheory.integral_add (hhead_int.const_mul (Ctop i))
            (hwindow_int'.const_mul (C i)),
            MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      _ = Ctop i * norm (iteratedCovGrad (I := I) g 0 2 (i + 2) P) ^ 2 +
            C i * (∫ x, Combinatorics.boundedFactorGridWindow (b x) 3 5
              ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
          rw [hhead]
      _ <= Ctop i * norm (iteratedCovGrad (I := I) g 0 2 (i + 2) P) ^ 2 +
            C i * K A :=
          add_le_add (le_refl _)
            (mul_le_mul_of_nonneg_left hwindow_bound' (hC i))
  have hsum :
      (∑ i ∈ Finset.range 3,
        norm (iteratedCovGrad (I := I) g r s i Phi) ^ 2) <=
        ∑ i ∈ Finset.range 3,
          (Ctop i * norm (iteratedCovGrad (I := I) g 0 2 (i + 2) P) ^ 2 +
            C i * K A) :=
    Finset.sum_le_sum fun i hi => hterm i (Finset.mem_range.mp hi)
  rw [show (B A) ^ 2 = Q A by
    simp only [B, Real.sq_sqrt (hQ A hA)]]
  calc
    _ <= ∑ i ∈ Finset.range 3,
        (Ctop i * norm (iteratedCovGrad (I := I) g 0 2 (i + 2) P) ^ 2 +
          C i * K A) := hsum
    _ = (∑ i ∈ Finset.range 3,
          Ctop i * norm (iteratedCovGrad (I := I) g 0 2 (i + 2) P) ^ 2) +
        (∑ i ∈ Finset.range 3, C i * K A) := by
      rw [Finset.sum_add_distrib]
    _ = (∑ i ∈ Finset.range 3,
          Ctop i * norm (iteratedCovGrad (I := I) g 0 2 (i + 2) P) ^ 2) +
        Q A := by
      simp only [Q, Finset.sum_mul]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
