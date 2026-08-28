import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckVectorFieldCovariantDerivative
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckVectorFieldL2JetBoundRaisedKoszulJetNorm

noncomputable section


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
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem diagonalProductTerm_integral_le
    (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    {R : ℝ} (hR : 0 ≤ R)
    (i : ℕ) (hi1 : 1 ≤ i)
    {Λ : ℝ} (hΛ_nn : 0 ≤ Λ)
    (hΛsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ ^ 2)
    (hNi : ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ≤ R)
    {C : ℝ} (hC_nn : 0 ≤ C)
    (hGNP : ∀ j : ℕ, 0 < j → j < i →
      (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ ((i : ℝ) / (j : ℝ))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((j : ℝ) / (i : ℝ)) ≤
        C * Λ ^ (2 * (1 - (j : ℝ) / (i : ℝ))) * R ^ (2 * (j : ℝ) / (i : ℝ)))
    (n : ℕ) (hn_le : n ≤ i) (e : Fin n → ℕ) (he : ∑ m, e m = i) :
    MeasureTheory.Integrable
        (fun x => ∏ m : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
      (∫ x, ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        (i : ℝ) * (max Λ (max R (max C 1))) ^ (7 * i) := by
  classical
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  let : MeasurableSpace M := borel M
  have : BorelSpace M := ⟨rfl⟩
  have : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  set μ : MeasureTheory.Measure M := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ
  have : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  have hi_pos : 0 < i := hi1
  have hiR_pos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi_pos
  have hiR_ne : (i : ℝ) ≠ 0 := ne_of_gt hiR_pos
  have hnn : ∀ (j : ℕ) (x : M),
      0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x) :=
    fun j x => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  have hcont : ∀ j : ℕ, Continuous (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) := by
    intro j
    have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ 0 2 j P)
    refine hc.congr (fun x => ?_)
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x),
      ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M)
        (iteratedCovGrad (I := I) g₀ 0 2 j P) x]
  have hint : ∀ j : ℕ, MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) μ := by
    intro j
    rw [hμ]
    exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + j)
      (iteratedCovGrad (I := I) g₀ 0 2 j P)
  have hint_rpow : ∀ (j : ℕ) (p : ℝ), 0 ≤ p → MeasureTheory.Integrable
      (fun x => (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ p) μ := by
    intro j p hp
    have hcp : Continuous (fun x => (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ p) :=
      (hcont j).rpow_const (fun x => Or.inr hp)
    exact hcp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint_prod : MeasureTheory.Integrable
      (fun x => ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) μ := by
    have hcp : Continuous (fun x => ∏ m : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) :=
      continuous_finsetProd Finset.univ (fun m _ => hcont (e m))
    exact hcp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨hint_prod, ?_⟩
  set Mbar : ℝ := max Λ (max R (max C 1)) with hMbar
  have hMbar1 : (1 : ℝ) ≤ Mbar :=
    le_trans (le_max_right C 1) (le_trans (le_max_right R _) (le_max_right Λ _))
  have hMbar_nn : 0 ≤ Mbar := le_trans zero_le_one hMbar1
  have hΛ_le : Λ ≤ Mbar := le_max_left _ _
  have hR_le : R ≤ Mbar := le_trans (le_max_left R _) (le_max_right Λ _)
  have hC_le : C ≤ Mbar :=
    le_trans (le_trans (le_max_left C 1) (le_max_right R _)) (le_max_right Λ _)
  set Sset : Finset (Fin n) := Finset.univ.filter (fun m => 0 < e m) with hSset
  set Zset : Finset (Fin n) := Finset.univ.filter (fun m => ¬ (0 < e m)) with hZset
  have hsplit : ∀ x : M,
      (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) =
        (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) *
          (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) := by
    intro x
    rw [hSset, hZset]
    exact (Finset.prod_filter_mul_prod_filter_not Finset.univ (fun m => 0 < e m)
      (fun m => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))).symm
  have hZbound : ∀ x : M,
      (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤ Λ ^ (2 * Zset.card) := by
    intro x
    calc (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        ≤ ∏ _m ∈ Zset, Λ ^ 2 := by
          apply Finset.prod_le_prod (fun m _ => hnn (e m) x)
          intro m hm
          have hem0 : e m = 0 := by have := (Finset.mem_filter.mp hm).2; omega
          rw [hem0]; exact hΛsup x
      _ = Λ ^ (2 * Zset.card) := by rw [Finset.prod_const, ← pow_mul]
  have hZsum0 : ∑ m ∈ Zset, e m = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    have := (Finset.mem_filter.mp hm).2; omega
  have hSsum : ∑ m ∈ Sset, e m = i := by
    have h := Finset.sum_filter_add_sum_filter_not Finset.univ (fun m => 0 < e m) e
    rw [← hSset, ← hZset, hZsum0, add_zero, he] at h
    exact h
  have hScard_pos : 1 ≤ Sset.card := by
    rcases Nat.eq_zero_or_pos Sset.card with h0 | hp
    · exfalso
      rw [Finset.card_eq_zero] at h0
      rw [h0, Finset.sum_empty] at hSsum
      omega
    · exact hp
  rcases Nat.lt_or_ge Sset.card 2 with hScard_lt2 | hScard_ge2
  · have hScard1 : Sset.card = 1 := by omega
    obtain ⟨m₀, hm₀⟩ := Finset.card_eq_one.mp hScard1
    have hem₀ : e m₀ = i := by
      have hss : ∑ m ∈ Sset, e m = e m₀ := by rw [hm₀, Finset.sum_singleton]
      rw [hss] at hSsum; exact hSsum
    have hSprod : ∀ x : M,
        (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) := by
      intro x; rw [hm₀, Finset.prod_singleton, hem₀]
    have hpt : ∀ x : M,
        (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤
          Λ ^ (2 * Zset.card) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) := by
      intro x
      rw [hsplit x, hSprod x]
      calc (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x)) *
            (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
          ≤ (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x)) * Λ ^ (2 * Zset.card) :=
            mul_le_mul_of_nonneg_left (hZbound x) (hnn i x)
        _ = Λ ^ (2 * Zset.card) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) := mul_comm _ _
    have hintFi : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ) ≤ R ^ 2 := by
      have heq : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ) =
          ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ 2 := by
        rw [SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 i P), hμ]
        exact (tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i)
          ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection)).symm
      rw [heq]
      nlinarith only [hNi, norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 i P), hR]
    have hΛZ_nn : 0 ≤ Λ ^ (2 * Zset.card) := pow_nonneg hΛ_nn _
    calc (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) ∂μ)
        ≤ ∫ x, Λ ^ (2 * Zset.card) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ :=
          MeasureTheory.integral_mono hint_prod ((hint i).const_mul _) hpt
      _ = Λ ^ (2 * Zset.card) * ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ Λ ^ (2 * Zset.card) * R ^ 2 := mul_le_mul_of_nonneg_left hintFi hΛZ_nn
      _ ≤ (i : ℝ) * Mbar ^ (7 * i) := by
          have hZle : Zset.card ≤ i := le_trans (Finset.card_le_univ _) (by simpa using hn_le)
          have e1 : Λ ^ (2 * Zset.card) ≤ Mbar ^ (2 * i) :=
            le_trans (pow_le_pow_left₀ hΛ_nn hΛ_le _)
              (pow_le_pow_right₀ hMbar1 (by omega))
          have e2 : R ^ 2 ≤ Mbar ^ 2 := pow_le_pow_left₀ hR hR_le 2
          have e3 : Mbar ^ (2 * i) * Mbar ^ 2 ≤ Mbar ^ (7 * i) := by
            rw [← pow_add]
            exact pow_le_pow_right₀ hMbar1 (by omega)
          have e4 : Λ ^ (2 * Zset.card) * R ^ 2 ≤ Mbar ^ (2 * i) * Mbar ^ 2 :=
            mul_le_mul e1 e2 (by positivity) (by positivity)
          have e5 : Mbar ^ (7 * i) ≤ (i : ℝ) * Mbar ^ (7 * i) := by
            have : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
            nlinarith only [pow_nonneg hMbar_nn (7 * i), this]
          calc Λ ^ (2 * Zset.card) * R ^ 2 ≤ Mbar ^ (2 * i) * Mbar ^ 2 := e4
            _ ≤ Mbar ^ (7 * i) := e3
            _ ≤ (i : ℝ) * Mbar ^ (7 * i) := e5
  · have hem_lt : ∀ m ∈ Sset, e m < i := by
      intro m hm
      have hmpos : 0 < e m := (Finset.mem_filter.mp hm).2
      have hadd : e m + ∑ m' ∈ Sset.erase m, e m' = ∑ m' ∈ Sset, e m' :=
        Finset.add_sum_erase Sset e hm
      rw [hSsum] at hadd
      have herase_ne : (Sset.erase m).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem hm]; omega
      obtain ⟨m', hm'⟩ := herase_ne
      have hm'S : m' ∈ Sset := Finset.mem_of_mem_erase hm'
      have hm'pos : 1 ≤ e m' := (Finset.mem_filter.mp hm'S).2
      have hle : e m' ≤ ∑ m'' ∈ Sset.erase m, e m'' :=
        Finset.single_le_sum (fun k _ => Nat.zero_le _) hm'
      omega
    have hAMGM : ∀ x : M,
        (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤
          ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) := by
      intro x
      have hw_nn : ∀ m ∈ Sset, 0 ≤ (e m : ℝ) / i := fun m _ => by positivity
      have hw_sum : ∑ m ∈ Sset, (e m : ℝ) / i = 1 := by
        rw [← Finset.sum_div]
        rw [show (∑ m ∈ Sset, (e m : ℝ)) = ((i : ℕ) : ℝ) from by
          rw [← Nat.cast_sum]; exact_mod_cast hSsum]
        exact div_self hiR_ne
      have hz_nn : ∀ m ∈ Sset, 0 ≤ (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) :=
        fun m _ => Real.rpow_nonneg (hnn (e m) x) _
      have hAM := Real.geom_mean_le_arith_mean_weighted Sset (fun m => (e m : ℝ) / i)
        (fun m => (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)))
        hw_nn hw_sum hz_nn
      have hLHS : (∏ m ∈ Sset, ((riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)))
            ^ ((e m : ℝ) / i)) =
          ∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) := by
        apply Finset.prod_congr rfl
        intro m hm
        have hmpos : 0 < e m := (Finset.mem_filter.mp hm).2
        have hemR_ne : (e m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hmpos.ne'
        rw [← Real.rpow_mul (hnn (e m) x)]
        rw [show ((i : ℝ) / (e m : ℝ)) * ((e m : ℝ) / i) = 1 by field_simp]
        rw [Real.rpow_one]
      rw [hLHS] at hAM
      exact hAM
    have hfactor : ∀ m ∈ Sset,
        (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) ≤
          Mbar ^ (5 * i) := by
      intro m hm
      have hmpos : 0 < e m := (Finset.mem_filter.mp hm).2
      have hem_lt_i : e m < i := hem_lt m hm
      have hemR_pos : (0 : ℝ) < (e m : ℝ) := by exact_mod_cast hmpos
      have hemR_ne : (e m : ℝ) ≠ 0 := ne_of_gt hemR_pos
      have hgn := hGNP (e m) hmpos hem_lt_i
      set Ival : ℝ := ∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ
        with hIval
      have hIval_nn : 0 ≤ Ival := by
        rw [hIval]; exact integral_nonneg (fun x => Real.rpow_nonneg (hnn (e m) x) _)
      have hθ_nn : 0 ≤ (e m : ℝ) / i := by positivity
      have hθ_le1 : (e m : ℝ) / i ≤ 1 := by
        rw [div_le_one hiR_pos]; exact_mod_cast Nat.le_of_lt hem_lt_i
      have hexp1_nn : 0 ≤ 2 * (1 - (e m : ℝ) / i) := by linarith only [hθ_le1]
      have hexp1_le : 2 * (1 - (e m : ℝ) / i) ≤ 2 := by linarith only [hθ_nn]
      have hexp2_nn : 0 ≤ 2 * (e m : ℝ) / i := by positivity
      have hexp2_le : 2 * (e m : ℝ) / i ≤ 2 := by
        rw [mul_div_assoc]
        linarith only [hθ_le1]
      have hΛpow : Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar ^ (2 : ℕ) := by
        calc Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar ^ (2 * (1 - (e m : ℝ) / i)) :=
              Real.rpow_le_rpow hΛ_nn hΛ_le hexp1_nn
          _ ≤ Mbar ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hMbar1 hexp1_le
          _ = Mbar ^ (2 : ℕ) := by rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hRpow : R ^ (2 * (e m : ℝ) / i) ≤ Mbar ^ (2 : ℕ) := by
        calc R ^ (2 * (e m : ℝ) / i) ≤ Mbar ^ (2 * (e m : ℝ) / i) :=
              Real.rpow_le_rpow hR hR_le hexp2_nn
          _ ≤ Mbar ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hMbar1 hexp2_le
          _ = Mbar ^ (2 : ℕ) := by rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hbase_le : C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i) ≤
          Mbar ^ (5 : ℕ) := by
        have h1 : C * Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar * Mbar ^ (2 : ℕ) :=
          mul_le_mul hC_le hΛpow (Real.rpow_nonneg hΛ_nn _) hMbar_nn
        have h2 : C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i) ≤
            Mbar * Mbar ^ (2 : ℕ) * Mbar ^ (2 : ℕ) :=
          mul_le_mul h1 hRpow (Real.rpow_nonneg hR _) (by positivity)
        calc C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i)
            ≤ Mbar * Mbar ^ (2 : ℕ) * Mbar ^ (2 : ℕ) := h2
          _ = Mbar ^ (5 : ℕ) := by ring
      have hbase_nn : 0 ≤ C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i) := by
        apply mul_nonneg (mul_nonneg hC_nn (Real.rpow_nonneg hΛ_nn _)) (Real.rpow_nonneg hR _)
      have hIval_eq : Ival = (Ival ^ ((e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) := by
        rw [← Real.rpow_mul hIval_nn]
        rw [show ((e m : ℝ) / i) * ((i : ℝ) / (e m : ℝ)) = 1 by field_simp]
        rw [Real.rpow_one]
      have hM5_one : (1 : ℝ) ≤ Mbar ^ (5 : ℕ) :=
        le_trans hMbar1 (le_self_pow₀ hMbar1 (by norm_num))
      have hidiv : (i : ℝ) / (e m : ℝ) ≤ (i : ℝ) :=
        div_le_self hiR_pos.le (by exact_mod_cast hmpos)
      calc Ival = (Ival ^ ((e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) := hIval_eq
        _ ≤ (C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) :=
            Real.rpow_le_rpow (Real.rpow_nonneg hIval_nn _) hgn (by positivity)
        _ ≤ (Mbar ^ (5 : ℕ)) ^ ((i : ℝ) / (e m : ℝ)) :=
            Real.rpow_le_rpow hbase_nn hbase_le (by positivity)
        _ ≤ (Mbar ^ (5 : ℕ)) ^ ((i : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le hM5_one hidiv
        _ = (Mbar ^ (5 : ℕ)) ^ (i : ℕ) := by rw [Real.rpow_natCast]
        _ = Mbar ^ (5 * i) := by rw [← pow_mul]
    have hSsum_factor : ∑ m ∈ Sset, ((e m : ℝ) / i) *
        (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) ≤
        Mbar ^ (5 * i) := by
      have hw_nn : ∀ m ∈ Sset, 0 ≤ (e m : ℝ) / i := fun m _ => by positivity
      have hw_sum : ∑ m ∈ Sset, (e m : ℝ) / i = 1 := by
        rw [← Finset.sum_div]
        rw [show (∑ m ∈ Sset, (e m : ℝ)) = ((i : ℕ) : ℝ) from by
          rw [← Nat.cast_sum]; exact_mod_cast hSsum]
        exact div_self hiR_ne
      calc ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ)
          ≤ ∑ m ∈ Sset, ((e m : ℝ) / i) * Mbar ^ (5 * i) := by
            apply Finset.sum_le_sum
            intro m hm
            exact mul_le_mul_of_nonneg_left (hfactor m hm) (hw_nn m hm)
        _ = (∑ m ∈ Sset, (e m : ℝ) / i) * Mbar ^ (5 * i) := by rw [Finset.sum_mul]
        _ = Mbar ^ (5 * i) := by rw [hw_sum, one_mul]
    have hpt2 : ∀ x : M,
        (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤
          Λ ^ (2 * Zset.card) * ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) := by
      intro x
      rw [hsplit x]
      have hZnn : 0 ≤ ∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) :=
        Finset.prod_nonneg (fun m _ => hnn (e m) x)
      have hsum_nn : 0 ≤ ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) :=
        Finset.sum_nonneg (fun m _ => mul_nonneg (by positivity) (Real.rpow_nonneg (hnn (e m) x) _))
      calc (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) *
            (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
          ≤ (∑ m ∈ Sset, ((e m : ℝ) / i) *
              (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ))) *
              Λ ^ (2 * Zset.card) :=
            mul_le_mul (hAMGM x) (hZbound x) hZnn hsum_nn
        _ = Λ ^ (2 * Zset.card) * ∑ m ∈ Sset, ((e m : ℝ) / i) *
              (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) :=
            mul_comm _ _
    have hsum_int : MeasureTheory.Integrable
        (fun x => ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ))) μ := by
      apply MeasureTheory.integrable_finsetSum
      intro m _
      exact (hint_rpow (e m) ((i : ℝ) / (e m : ℝ)) (by positivity)).const_mul _
    have hint_eq : (∫ x, ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) =
        ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) := by
      rw [MeasureTheory.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro m _; rw [MeasureTheory.integral_const_mul]
      · intro m _
        exact (hint_rpow (e m) ((i : ℝ) / (e m : ℝ)) (by positivity)).const_mul _
    have hΛZ_nn : 0 ≤ Λ ^ (2 * Zset.card) := pow_nonneg hΛ_nn _
    calc (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) ∂μ)
        ≤ ∫ x, Λ ^ (2 * Zset.card) * ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ :=
          MeasureTheory.integral_mono hint_prod (hsum_int.const_mul _) hpt2
      _ = Λ ^ (2 * Zset.card) * ∫ x, ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ Λ ^ (2 * Zset.card) * Mbar ^ (5 * i) := by
          rw [hint_eq]
          exact mul_le_mul_of_nonneg_left hSsum_factor hΛZ_nn
      _ ≤ (i : ℝ) * Mbar ^ (7 * i) := by
          have hZle : Zset.card ≤ i := le_trans (Finset.card_le_univ _) (by simpa using hn_le)
          have e1 : Λ ^ (2 * Zset.card) ≤ Mbar ^ (2 * i) :=
            le_trans (pow_le_pow_left₀ hΛ_nn hΛ_le _) (pow_le_pow_right₀ hMbar1 (by omega))
          have e3 : Mbar ^ (2 * i) * Mbar ^ (5 * i) = Mbar ^ (7 * i) := by
            rw [← pow_add]; congr 1; ring
          have e4 : Λ ^ (2 * Zset.card) * Mbar ^ (5 * i) ≤ Mbar ^ (2 * i) * Mbar ^ (5 * i) :=
            mul_le_mul_of_nonneg_right e1 (by positivity)
          have e5 : Mbar ^ (7 * i) ≤ (i : ℝ) * Mbar ^ (7 * i) := by
            have : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
            nlinarith only [pow_nonneg hMbar_nn (7 * i), this]
          calc Λ ^ (2 * Zset.card) * Mbar ^ (5 * i) ≤ Mbar ^ (2 * i) * Mbar ^ (5 * i) := e4
            _ = Mbar ^ (7 * i) := e3
            _ ≤ (i : ℝ) * Mbar ^ (7 * i) := e5

private theorem diagonalProductGrid_riemannianFiberNormSq_integral_ballUniform_succ
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a + 1 →
          MeasureTheory.Integrable
              (fun x => ∑ n ∈ Finset.range (i + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
                  ∏ m : Fin n,
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
              (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
            (∫ x, ∑ n ∈ Finset.range (i + 1),
                  ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
                    ∏ m : Fin n,
                      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤ K i := by
  classical
  have : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨Cemb, hCemb_nn, hCemb⟩ :=
    DifferentialGeometry.Analysis.Spectral.deTurckSmoothRemainderDiff_supercritical_pointwise_jet_le_fixedWindow
      (I := I) (M := M) g₀ a ha_super
  set Lam : ℝ := Cemb * Real.sqrt ((a + 1 + 1 : ℕ) : ℝ) * R with hLam
  have hLam_nn : 0 ≤ Lam := by rw [hLam]; positivity
  set Cgn : ℕ → ℝ := fun k =>
    if h : 1 ≤ k then
      (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 2 k h).choose
    else 0 with hCgn
  have hCgn_nn : ∀ k, 0 ≤ Cgn k := by
    intro k
    simp only [hCgn]
    split_ifs with h
    · exact (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 2 k h).choose_spec.1
    · exact le_refl 0
  set Gfun : ℕ → ℝ := fun k => (k : ℝ) * (max Lam (max R (max (Cgn k) 1))) ^ (7 * k) with hGfun
  have hGfun_nn : ∀ k, 0 ≤ Gfun k := by
    intro k
    rw [hGfun]
    apply mul_nonneg (Nat.cast_nonneg k)
    apply pow_nonneg
    exact le_trans zero_le_one
      (le_trans (le_max_right (Cgn k) 1) (le_trans (le_max_right R _) (le_max_right Lam _)))
  set vol : ℝ := ((riemannianVolumeMeasure (I := I) (M := M) g₀) Set.univ).toReal with hvol
  have hvol_nn : 0 ≤ vol := ENNReal.toReal_nonneg
  refine ⟨fun k => (∑ n ∈ Finset.range (k + 1),
      ((Finset.Nat.antidiagonalTuple n k).card : ℝ)) * Gfun k + vol, ?_, ?_⟩
  · intro k
    exact add_nonneg
      (mul_nonneg (Finset.sum_nonneg (fun n _ => Nat.cast_nonneg _)) (hGfun_nn k)) hvol_nn
  · intro P hPball i hi
    by_cases hi0 : i = 0
    · subst hi0
      have hgrid0 : (fun x => ∑ n ∈ Finset.range (0 + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n 0, ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) = (fun _ : M => (1 : ℝ)) := by
        funext x
        simp only [Nat.zero_add, Finset.sum_range_one, Finset.Nat.antidiagonalTuple_zero_zero,
          Finset.sum_singleton, Finset.univ_eq_empty, Finset.prod_empty]
      refine ⟨?_, ?_⟩
      · rw [hgrid0]; exact MeasureTheory.integrable_const 1
      · rw [hgrid0, MeasureTheory.integral_const, smul_eq_mul, mul_one,
          MeasureTheory.measureReal_def, ← hvol]
        exact le_add_of_nonneg_left
          (mul_nonneg (Finset.sum_nonneg (fun n _ => Nat.cast_nonneg _)) (hGfun_nn 0))
    · have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
      have hNi : ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ≤ R := hPball i (by omega)
      have hΛsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤
          Lam ^ 2 := by
        intro x
        have hsum_le : ∑ j ∈ Finset.range (a + 1 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 ≤ ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
          calc ∑ j ∈ Finset.range (a + 1 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2
              ≤ ∑ j ∈ Finset.range (a + 1 + 1), R ^ 2 := by
                apply Finset.sum_le_sum
                intro j hj
                have hjle : j ≤ a + 2 := by have := Finset.mem_range.mp hj; omega
                nlinarith [norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 j P), hPball j hjle, hR]
            _ = ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have hsingle : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤
            ∑ m ∈ Finset.range 3, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x) := by
          have h0mem : (0 : ℕ) ∈ Finset.range 3 := by norm_num
          have hsl := Finset.single_le_sum
            (f := fun m => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x))
            (fun m _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + m) x _) h0mem
          simpa using hsl
        have hLam2 : Lam ^ 2 = Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
          rw [hLam, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
        have hchain : ∑ m ∈ Finset.range 3, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x) ≤ Lam ^ 2 := by
          refine le_trans (hCemb P x) ?_
          rw [hLam2]
          calc Cemb ^ 2 * ∑ j ∈ Finset.range (a + 1 + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2
              ≤ Cemb ^ 2 * (((a + 1 + 1 : ℕ) : ℝ) * R ^ 2) :=
                mul_le_mul_of_nonneg_left hsum_le (by positivity)
            _ = Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by ring
        exact le_trans hsingle hchain
      have hGNspec := (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 2 i hi1).choose_spec.2
      have hGNP : ∀ j : ℕ, 0 < j → j < i →
          (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ ((i : ℝ) / (j : ℝ))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((j : ℝ) / (i : ℝ)) ≤
            Cgn i * Lam ^ (2 * (1 - (j : ℝ) / (i : ℝ))) * R ^ (2 * (j : ℝ) / (i : ℝ)) := by
        intro j hj0 hji
        have hb := hGNspec P Lam hLam_nn hΛsup j hj0 hji
        have hchoose : (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
            (I := I) (M := M) g₀ 0 2 i hi1).choose = Cgn i := by
          rw [hCgn]; simp only [dif_pos hi1]
        rw [hchoose] at hb
        refine le_trans hb ?_
        have hnorm : Integral.L2.tensorL2Norm (I := I) (M := M) g₀ 0 (2 + i)
            (iteratedCovGrad (I := I) g₀ 0 2 i P).toFun = ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ :=
          (SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 i P)).symm
        rw [hnorm]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (norm_nonneg _) hNi (by positivity))
          (mul_nonneg (hCgn_nn i) (Real.rpow_nonneg hLam_nn _))
      have hPT : ∀ n ∈ Finset.range (i + 1), ∀ e ∈ Finset.Nat.antidiagonalTuple n i,
          MeasureTheory.Integrable (fun x => ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
          (∫ x, ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤ Gfun i := by
        intro n hn e he
        have hn_le : n ≤ i := by have := Finset.mem_range.mp hn; omega
        have hsum_e : ∑ m, e m = i := Finset.Nat.mem_antidiagonalTuple.mp he
        have hres := diagonalProductTerm_integral_le (I := I) (M := M) g₀ P hR i hi1 hLam_nn hΛsup
          hNi (hCgn_nn i) hGNP n hn_le e hsum_e
        simpa only [hGfun] using hres
      have hgrid_int : MeasureTheory.Integrable (fun x => ∑ n ∈ Finset.range (i + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n i, ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
        apply MeasureTheory.integrable_finsetSum
        intro n hn
        apply MeasureTheory.integrable_finsetSum
        intro e he
        exact (hPT n hn e he).1
      refine ⟨hgrid_int, ?_⟩
      rw [MeasureTheory.integral_finsetSum _
        (fun n hn => MeasureTheory.integrable_finsetSum _ (fun e he => (hPT n hn e he).1))]
      have hinner : ∀ n ∈ Finset.range (i + 1),
          (∫ x, ∑ e ∈ Finset.Nat.antidiagonalTuple n i, ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
          ∑ e ∈ Finset.Nat.antidiagonalTuple n i, ∫ x, ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
        intro n hn
        exact MeasureTheory.integral_finsetSum _ (fun e he => (hPT n hn e he).1)
      rw [Finset.sum_congr rfl hinner]
      have hle1 : ∑ n ∈ Finset.range (i + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
            (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
          ∑ n ∈ Finset.range (i + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n i, Gfun i := by
        apply Finset.sum_le_sum; intro n hn
        apply Finset.sum_le_sum; intro e he
        exact (hPT n hn e he).2
      have heq2 : ∑ n ∈ Finset.range (i + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n i, Gfun i =
          (∑ n ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n i).card : ℝ)) * Gfun i := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro n _
        rw [Finset.sum_const, nsmul_eq_mul]
      refine le_trans hle1 ?_
      rw [heq2]
      exact le_add_of_nonneg_right hvol_nn

open DifferentialGeometry.Analysis.Spectral.DeTurck in
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert in
theorem cometricCastG0_order0sup_jetL2_succ_generic
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (F : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 1 x
            ((cometricCastG0 (I := I) g₀ g₁).toSection x) ≤ Λ ^ 2) ∧
        ∀ (i : ℕ), i ≤ a + 1 →
          ∑ l ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 3 1 l (cometricCastG0 (I := I) g₀ g₁)‖ ^ 2 ≤ F i := by
  classical
  set Φ : SmoothCcTensor g₀ 3 1 := cometricDoubleTraceField (I := I) g₀ 1 with hΦ_def
  obtain ⟨C_base, hC_base_nn, hC_base⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_zero_metricComparisonDifferenceEndomorphismField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨K_mos, hK_mos_nn, hK_mos⟩ :=
    diagonalProductGrid_riemannianFiberNormSq_integral_ballUniform_succ
      (I := I) (M := M) g₀ a ha_super hR
  have hSΦ_ex : ∀ i : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 3 1 i Φ).toSection x) ≤ K :=
    fun i => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 3 (1 + i)
      (iteratedCovGrad (I := I) g₀ 3 1 i Φ)
  choose SΦ hSΦ_nn hSΦ using hSΦ_ex
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  set KW : ℕ → ℝ := fun q => fr ^ 2 * C_base q * K_mos q with hKW_def
  set FW : ℕ → ℝ := fun i => ∑ q ∈ Finset.range (i + 1), KW q with hFW_def
  set KD : ℕ → ℝ := fun l => operatorFieldApplicationGdiag (E := E) l *
    (∑ i' ∈ Finset.range (l + 1), SΦ i') * FW l with hKD_def
  set aL : ℕ → ℝ :=
    fun l => ‖iteratedCovGrad (I := I) g₀ 3 1 l Φ‖ ^ 2 with haL_def
  set Ff : ℕ → ℝ :=
    fun i => ∑ l ∈ Finset.range (i + 1), (2 * aL l + 2 * KD l) with hFf_def
  set ΛT2 : ℝ := fr ^ 2 * C_base 0 with hΛT2_def
  have hFnn : ∀ i, 0 ≤ Ff i := by
    intro i
    simp only [hFf_def]
    apply Finset.sum_nonneg
    intro l _
    have h1 : 0 ≤ aL l := by simp only [haL_def]; positivity
    have h2 : 0 ≤ KD l := by
      simp only [hKD_def, hFW_def, hKW_def]
      refine mul_nonneg (mul_nonneg (operatorFieldApplicationGdiag_nonneg _)
        (Finset.sum_nonneg (fun i' _ => hSΦ_nn i'))) ?_
      exact Finset.sum_nonneg (fun q _ =>
        mul_nonneg (mul_nonneg (by positivity) (hC_base_nn q)) (hK_mos_nn q))
    linarith
  refine ⟨Real.sqrt (2 * SΦ 0 + 2 * (SΦ 0 * ΛT2)), Ff, Real.sqrt_nonneg _, hFnn, ?_⟩
  · intro g₁ P δ hδ_le hδ htie hPball
    by_cases hMne : Nonempty M
    · obtain ⟨x₀⟩ := hMne
      have hδ0 : 0 ≤ δ := by
        obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x₀, v ≠ 0 := by
          have : Nontrivial (TangentSpace I x₀) := by
            have hfr' : 0 < Module.finrank ℝ (TangentSpace I x₀) := by
              have heq : Module.finrank ℝ (TangentSpace I x₀) = Module.finrank ℝ E := rfl
              rw [heq]; exact Nat.pos_of_ne_zero (NeZero.ne _)
            exact Module.nontrivial_of_finrank_pos hfr'
          exact exists_ne 0
        have hpos : 0 < g₀.inner x₀ v v := g₀.pos x₀ v hv
        have hbound := hδ x₀ v v
        have hsqrt_pos : 0 < Real.sqrt (g₀.inner x₀ v v) := Real.sqrt_pos.mpr hpos
        have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀ P x₀ v v| := abs_nonneg _
        by_contra hδc
        have hδc' : δ < 0 := lt_of_not_ge hδc
        have hrhs_neg : δ * Real.sqrt (g₀.inner x₀ v v) * Real.sqrt (g₀.inner x₀ v v) < 0 := by
          have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 := mul_neg_of_neg_of_pos hδc' hsqrt_pos
          exact mul_neg_of_neg_of_pos h1 hsqrt_pos
        linarith [le_trans habs_nn hbound]
      set W : SmoothCcTensor g₀ 3 3 :=
        endoSlotZeroCcTensor (I := I) (M := M) g₀ 2
          (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)
        with hW_def
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
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) = 1 := by
          simp
        rw [hgrid0, mul_one] at h2
        calc riemannianFiberNormSq (I := I) (M := M) g₀ 3 3 x (W.toSection x)
            ≤ fr ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
                ((slotInsertEndoCc (I := I) (M := M) g₀ 0
                  (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)).toSection x) := h1
          _ ≤ fr ^ 2 * C_base 0 := mul_le_mul_of_nonneg_left h2 (sq_nonneg fr)
          _ = ΛT2 := hΛT2_def.symm
      have hstep2 : ∀ q : ℕ, q ≤ a + 1 →
          ‖iteratedCovGrad (I := I) g₀ 3 3 q W‖ ^ 2 ≤ KW q := by
        intro q hq
        obtain ⟨hgi, hgb⟩ := hK_mos P hPball q hq
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
        have hint : MeasureTheory.Integrable
            (fun x => fr ^ 2 * C_base q *
              (∑ n ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n q,
                ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) := hgi.const_mul _
        have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 3 (3 + q)
          (iteratedCovGrad (I := I) g₀ 3 3 q W) _ hint hpt
        refine le_trans hkey ?_
        rw [MeasureTheory.integral_const_mul, hKW_def]
        exact mul_le_mul_of_nonneg_left hgb (mul_nonneg (sq_nonneg fr) (hC_base_nn q))
      have hstep3 : ∀ l : ℕ, l ≤ a + 1 →
          ‖iteratedCovGrad (I := I) g₀ 3 1 l (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W)‖ ^ 2 ≤
            KD l := by
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
          apply MeasureTheory.integrable_finsetSum
          intro q _
          exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 3 (3 + q)
            (iteratedCovGrad (I := I) g₀ 3 3 q W)
        have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 3 (1 + l)
          (iteratedCovGrad (I := I) g₀ 3 1 l (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W)) _ hint hpt
        refine le_trans hkey ?_
        rw [MeasureTheory.integral_const_mul,
          MeasureTheory.integral_finsetSum _ (fun q _ =>
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
        simp only [hKD_def]
        refine mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (operatorFieldApplicationGdiag_nonneg _) (Finset.sum_nonneg (fun i' _ => hSΦ_nn i')))
        simp only [hFW_def]
        exact Finset.sum_le_sum (fun q hq => hstep2 q (by rw [Finset.mem_range] at hq; omega))
      refine ⟨?_, ?_⟩
      · intro x
        have hΛT2_nn : 0 ≤ ΛT2 := by rw [hΛT2_def]; exact mul_nonneg (sq_nonneg fr) (hC_base_nn 0)
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
        simp only [hFf_def]
        refine Finset.sum_le_sum (fun l hl => ?_)
        have hl_a : l ≤ a + 1 := by rw [Finset.mem_range] at hl; omega
        rw [hid, iteratedCovGrad_add]
        have hKDl := hstep3 l hl_a
        have haLl : aL l = ‖iteratedCovGrad (I := I) g₀ 3 1 l Φ‖ ^ 2 := by simp only [haL_def]
        have hsq := pow_le_pow_left₀ (norm_nonneg (iteratedCovGrad (I := I) g₀ 3 1 l Φ +
            iteratedCovGrad (I := I) g₀ 3 1 l (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W)))
          (norm_add_le (iteratedCovGrad (I := I) g₀ 3 1 l Φ)
            (iteratedCovGrad (I := I) g₀ 3 1 l (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W))) 2
        nlinarith only [hsq, hKDl, haLl,
          sq_nonneg (‖iteratedCovGrad (I := I) g₀ 3 1 l Φ‖ -
            ‖iteratedCovGrad (I := I) g₀ 3 1 l (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W)‖)]
    · have hem : IsEmpty M := not_nonempty_iff.mp hMne
      refine ⟨fun x => (hem.false x).elim, ?_⟩
      intro i hi
      have hz : ∀ l : ℕ,
          ‖iteratedCovGrad (I := I) g₀ 3 1 l (cometricCastG0 (I := I) g₀ g₁)‖ = 0 := by
        intro l
        rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
          MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
      have hsum0 : (∑ l ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 3 1 l (cometricCastG0 (I := I) g₀ g₁)‖ ^ 2) = 0 := by
        apply Finset.sum_eq_zero
        intro l _
        rw [hz l]; ring
      rw [hsum0]
      exact hFnn i

omit [BoundarylessManifold I M] in
private theorem exists_window_pointwise_jet_le (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R) :
    ∃ Λw : ℝ, 0 ≤ Λw ∧
      ∀ (P : SmoothCcTensor g₀ 0 2),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ j : ℕ, j ≤ 2 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x) ≤ Λw ^ 2 := by
  obtain ⟨Cemb, hCemb_nn, hCemb⟩ :=
    DifferentialGeometry.Analysis.Spectral.deTurckSmoothRemainderDiff_supercritical_pointwise_jet_le_fixedWindow
      (I := I) (M := M) g₀ a ha_super
  refine ⟨Cemb * Real.sqrt ((a + 1 + 1 : ℕ) : ℝ) * R, by positivity, ?_⟩
  intro P hPball j hj x
  have hsum_le : ∑ i ∈ Finset.range (a + 1 + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ 2 ≤ ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
    calc ∑ i ∈ Finset.range (a + 1 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ 2
        ≤ ∑ _i ∈ Finset.range (a + 1 + 1), R ^ 2 := by
          apply Finset.sum_le_sum
          intro i hi
          have hile : i ≤ a + 2 := by have := Finset.mem_range.mp hi; omega
          nlinarith [norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 i P), hPball i hile, hR]
      _ = ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hwin := hCemb P x
  have hjmem : j ∈ Finset.range 3 := Finset.mem_range.mpr (by omega)
  have hsingle : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x) ≤
      ∑ m ∈ Finset.range 3, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x) :=
    Finset.single_le_sum
      (f := fun m => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x))
      (fun m _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + m) x _) hjmem
  have hLam2 : (Cemb * Real.sqrt ((a + 1 + 1 : ℕ) : ℝ) * R) ^ 2 =
      Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  rw [hLam2]
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)
      ≤ ∑ m ∈ Finset.range 3, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x) := hsingle
    _ ≤ Cemb ^ 2 * ∑ i ∈ Finset.range (a + 1 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ 2 := hwin
    _ ≤ Cemb ^ 2 * (((a + 1 + 1 : ℕ) : ℝ) * R ^ 2) :=
        mul_le_mul_of_nonneg_left hsum_le (by positivity)
    _ = Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by ring

private theorem raisedKoszul_riemannianFiberNormSq_lowOrder_le (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ n : ℕ, n ≤ 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
            ((iteratedCovGrad (I := I) g₀ 1 2 n (raisedKoszul (I := I) g₀ g₁)).toSection x) ≤
          Λ := by
  obtain ⟨Λw, hΛw_nn, hΛw⟩ :=
    exists_window_pointwise_jet_le (I := I) (M := M) g₀ a ha_super hR
  refine ⟨10 * Λw ^ 2, by positivity, ?_⟩
  intro g₁ P htie hPball n hn x
  have hTjet : ∀ j : ℕ, j ≤ 1 + 1 → ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) y
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection y) ≤ Λw ^ 2 :=
    fun j hj y => hΛw P hPball j (by omega) y
  have hkos := riemannianFiberNormSq_iteratedCovGrad_koszulCovecCc_le (I := I) (M := M) g₀ 1 P hTjet n hn x
  have heqr : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
      ((iteratedCovGrad (I := I) g₀ 1 2 n (raisedKoszul (I := I) g₀ g₁)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n (koszulCovecCc (I := I) g₀ P)).toSection x) := by
    rw [raisedKoszul_eq_cometricRaiseSlot0Field_koszulCovecCc (I := I) g₀ g₁ P htie]
    exact riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_koszul_eq (I := I) g₀ P n x
  rw [heqr]
  exact hkos

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [CompactSpace M] [T2Space M] in
private lemma metricComparisonEndomorphism_self' (g₀ : SmoothRiemannianMetric I M) (x : M) :
    metricComparisonEndomorphism (I := I) g₀ g₀ x =
      ContinuousLinearMap.id ℝ (TangentSpace I x) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [metricComparisonEndomorphism_apply, inverseMetricSharpFib_g0FlatCLM, ContinuousLinearMap.id_apply]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [CompactSpace M] in
omit [I.Boundaryless] in
private lemma metricComparisonEndomorphismField_decomp' (g₀ g₁ : SmoothRiemannianMetric I M) :
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
  rw [metricComparisonEndomorphismField_apply, add_apply]
  rw [show (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁ x) =
      metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x from rfl]
  rw [metricComparisonEndomorphismField_apply, metricComparisonEndomorphism_self', ContinuousLinearMap.id_apply]
  rw [metricComparisonEndomorphism_eq_diff_add_id]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma slotInsertEndoCc_add' (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
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
  rw [add_apply]
  simp only [slotInsertEndoCc_toSection]
  rw [show ((A + B) x) = A x + B x from by rw [ContMDiffSection.coe_add]; rfl]
  rw [slotInsertEndoFib_add_left, add_apply]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private lemma sharpFlatEndoCc_eq_insert_fullRaised (g₀ g₁ : SmoothRiemannianMetric I M) :
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

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [CompactSpace M] [SigmaCompactSpace M] in
private lemma window_grid_le (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (n : ℕ) {Λw : ℝ}
    (hwin : ∀ j : ℕ, j ≤ n → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x) ≤ Λw ^ 2)
    (x : M) :
    (∑ m ∈ Finset.range (n + 1),
      ∑ e ∈ Finset.Nat.antidiagonalTuple m n,
        ∏ k : Fin m,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e k) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e k) P).toSection x)) ≤
      (∑ m ∈ Finset.range (n + 1),
        ((Finset.Nat.antidiagonalTuple m n).card : ℝ)) * max (Λw ^ 2) 1 ^ n := by
  have hmax1 : (1 : ℝ) ≤ max (Λw ^ 2) 1 := le_max_right _ _
  have hmax_nn : (0 : ℝ) ≤ max (Λw ^ 2) 1 := le_trans zero_le_one hmax1
  have hterm : ∀ m ∈ Finset.range (n + 1), ∀ e ∈ Finset.Nat.antidiagonalTuple m n,
      (∏ k : Fin m,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e k) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e k) P).toSection x)) ≤
        max (Λw ^ 2) 1 ^ n := by
    intro m hm e he
    have hsum_e : ∑ k, e k = n := Finset.Nat.mem_antidiagonalTuple.mp he
    have hek_le : ∀ k : Fin m, e k ≤ n := by
      intro k
      rw [← hsum_e]
      exact Finset.single_le_sum (fun k' _ => Nat.zero_le _) (Finset.mem_univ k)
    have hprod1 : (∏ k : Fin m,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e k) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e k) P).toSection x)) ≤
        ∏ _k : Fin m, max (Λw ^ 2) 1 := by
      apply Finset.prod_le_prod
      · intro k _
        exact riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + e k) x _
      · intro k _
        exact le_trans (hwin (e k) (hek_le k) x) (le_max_left _ _)
    have hm_le : m ≤ n := by have := Finset.mem_range.mp hm; omega
    calc (∏ k : Fin m,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e k) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e k) P).toSection x))
        ≤ ∏ _k : Fin m, max (Λw ^ 2) 1 := hprod1
      _ = max (Λw ^ 2) 1 ^ m := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ max (Λw ^ 2) 1 ^ n := pow_le_pow_right₀ hmax1 hm_le
  calc (∑ m ∈ Finset.range (n + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple m n,
          ∏ k : Fin m,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e k) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e k) P).toSection x))
      ≤ ∑ m ∈ Finset.range (n + 1),
          ∑ _e ∈ Finset.Nat.antidiagonalTuple m n, max (Λw ^ 2) 1 ^ n := by
        apply Finset.sum_le_sum
        intro m hm
        apply Finset.sum_le_sum
        intro e he
        exact hterm m hm e he
    _ = (∑ m ∈ Finset.range (n + 1),
          ((Finset.Nat.antidiagonalTuple m n).card : ℝ)) * max (Λw ^ 2) 1 ^ n := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro m _
        rw [Finset.sum_const, nsmul_eq_mul]

private theorem sharpFlatEndoCc_lowOrder_jetL2_succ_generic
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ F : ℕ → ℝ), (∀ n, 0 ≤ Λ n) ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ n : ℕ, n ≤ 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + n) x
            ((iteratedCovGrad (I := I) g₀ 1 1 n
              (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤ Λ n) ∧
        (∀ i : ℕ, i ≤ a + 1 →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 1 1 q (sharpFlatEndoCc (I := I) g₀ g₁)‖ ^ 2 ≤ F i) := by
  classical
  obtain ⟨C_base, hC_base_nn, hC_base⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_zero_metricComparisonDifferenceEndomorphismField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨K_mos, hK_mos_nn, hK_mos⟩ :=
    diagonalProductGrid_riemannianFiberNormSq_integral_ballUniform_succ (I := I) (M := M) g₀ a ha_super hR
  obtain ⟨Λw, hΛw_nn, hΛw⟩ :=
    exists_window_pointwise_jet_le (I := I) (M := M) g₀ a ha_super hR
  set IdIns : SmoothCcTensor g₀ 1 1 :=
    slotInsertEndoCc (I := I) (M := M) g₀ 0
      (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₀) with hIdIns_def
  have hSId_ex : ∀ n : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 1 n IdIns).toSection x) ≤ K :=
    fun n => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 1 (1 + n)
      (iteratedCovGrad (I := I) g₀ 1 1 n IdIns)
  choose SId hSId_nn hSId using hSId_ex
  set Gw : ℕ → ℝ := fun n => (∑ m ∈ Finset.range (n + 1),
    ((Finset.Nat.antidiagonalTuple m n).card : ℝ)) * max (Λw ^ 2) 1 ^ n with hGw_def
  have hGw_nn : ∀ n, 0 ≤ Gw n := by
    intro n
    rw [hGw_def]
    apply mul_nonneg (Finset.sum_nonneg (fun m _ => Nat.cast_nonneg _))
    apply pow_nonneg
    exact le_trans zero_le_one (le_max_right _ _)
  set FId : ℕ → ℝ := fun q => ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖ ^ 2 with hFId_def
  have hFId_nn : ∀ q, 0 ≤ FId q := fun q => sq_nonneg _
  refine ⟨fun n => 2 * (C_base n * Gw n) + 2 * SId n,
    fun i => ∑ q ∈ Finset.range (i + 1), (2 * (C_base q * K_mos q) + 2 * FId q),
    fun n => add_nonneg
      (mul_nonneg (by norm_num) (mul_nonneg (hC_base_nn n) (hGw_nn n)))
      (mul_nonneg (by norm_num) (hSId_nn n)),
    fun i => Finset.sum_nonneg (fun q _ => add_nonneg
      (mul_nonneg (by norm_num) (mul_nonneg (hC_base_nn q) (hK_mos_nn q)))
      (mul_nonneg (by norm_num) (hFId_nn q))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  set DiffIns : SmoothCcTensor g₀ 1 1 :=
    slotInsertEndoCc (I := I) (M := M) g₀ 0
      (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁) with hDiffIns_def
  have hdecomp : sharpFlatEndoCc (I := I) g₀ g₁ = DiffIns + IdIns := by
    rw [sharpFlatEndoCc_eq_insert_fullRaised (I := I) (M := M) g₀ g₁,
      metricComparisonEndomorphismField_decomp' (I := I) (M := M) g₀ g₁,
      slotInsertEndoCc_add' (I := I) (M := M) g₀ 0]
  have hDiff_pt : ∀ n : ℕ, ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 1 n DiffIns).toSection x) ≤
      C_base n * ∑ m ∈ Finset.range (n + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple m n,
          ∏ k : Fin m,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e k) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e k) P).toSection x) :=
    fun n x => hC_base g₁ P htie hδ_le hδ0 hδ n x
  refine ⟨?_, ?_⟩
  · intro n hn x
    have hsplit : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 1 n (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + n) x
            ((iteratedCovGrad (I := I) g₀ 1 1 n DiffIns).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + n) x
            ((iteratedCovGrad (I := I) g₀ 1 1 n IdIns).toSection x) := by
      rw [hdecomp, iteratedCovGrad_add]
      rw [show ((iteratedCovGrad (I := I) g₀ 1 1 n DiffIns +
            iteratedCovGrad (I := I) g₀ 1 1 n IdIns).toSection x) =
          (iteratedCovGrad (I := I) g₀ 1 1 n DiffIns).toSection x +
            (iteratedCovGrad (I := I) g₀ 1 1 n IdIns).toSection x from by
        rw [SmoothCcTensor.toSection_add]; rfl]
      exact riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (1 + n) x _ _
    have hwin_n : ∀ j : ℕ, j ≤ n → ∀ y : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) y
          ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection y) ≤ Λw ^ 2 :=
      fun j hj y => hΛw P hPball j (by omega) y
    have hgrid := window_grid_le (I := I) (M := M) g₀ P n hwin_n x
    have hDn : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 1 n DiffIns).toSection x) ≤ C_base n * Gw n :=
      le_trans (hDiff_pt n x) (by
        rw [hGw_def]
        exact mul_le_mul_of_nonneg_left hgrid (hC_base_nn n))
    have hIn := hSId n x
    linarith [hsplit, hDn, hIn]
  · intro i hi
    have hterm : ∀ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 1 1 q (sharpFlatEndoCc (I := I) g₀ g₁)‖ ^ 2 ≤
          2 * (C_base q * K_mos q) + 2 * FId q := by
      intro q hq
      have hq_le : q ≤ a + 1 := by have := Finset.mem_range.mp hq; omega
      obtain ⟨hgi, hgb⟩ := hK_mos P hPball q hq_le
      have hDq : ‖iteratedCovGrad (I := I) g₀ 1 1 q DiffIns‖ ^ 2 ≤ C_base q * K_mos q := by
        have hint : MeasureTheory.Integrable
            (fun x => C_base q *
              (∑ m ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple m q,
                ∏ k : Fin m, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e k) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e k) P).toSection x)))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) := hgi.const_mul _
        have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀
          1 (1 + q) (iteratedCovGrad (I := I) g₀ 1 1 q DiffIns) _ hint (fun x => hDiff_pt q x)
        refine le_trans hkey ?_
        rw [MeasureTheory.integral_const_mul]
        exact mul_le_mul_of_nonneg_left hgb (hC_base_nn q)
      have htri : ‖iteratedCovGrad (I := I) g₀ 1 1 q (sharpFlatEndoCc (I := I) g₀ g₁)‖ ≤
          ‖iteratedCovGrad (I := I) g₀ 1 1 q DiffIns‖ +
            ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖ := by
        rw [hdecomp, iteratedCovGrad_add]
        exact norm_add_le _ _
      have hFIdq : FId q = ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖ ^ 2 := rfl
      nlinarith only [htri, hDq, hFIdq.ge,
        norm_nonneg (iteratedCovGrad (I := I) g₀ 1 1 q DiffIns),
        norm_nonneg (iteratedCovGrad (I := I) g₀ 1 1 q IdIns),
        norm_nonneg (iteratedCovGrad (I := I) g₀ 1 1 q (sharpFlatEndoCc (I := I) g₀ g₁)),
        sq_nonneg (‖iteratedCovGrad (I := I) g₀ 1 1 q DiffIns‖ -
          ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖)]
    exact Finset.sum_le_sum hterm

theorem connectionDifferenceSection_lowOrder_jetL2_succ_generic
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ F : ℕ → ℝ), (∀ n, 0 ≤ Λ n) ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ n : ℕ, n ≤ 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
            ((iteratedCovGrad (I := I) g₀ 1 2 n
              (connectionDifferenceSection (I := I) g₁ g₀)).toSection x) ≤ Λ n) ∧
        (∀ i : ℕ, i ≤ a + 1 →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 1 2 q (connectionDifferenceSection (I := I) g₁ g₀)‖ ^ 2 ≤ F i) := by
  classical
  obtain ⟨ΛK, FK, hΛK_nn, hFK_nn, hK⟩ :=
    raisedKoszul_order0sup_jetL2_succ_generic (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨ΛKlow, hΛKlow_nn, hKlow⟩ :=
    raisedKoszul_riemannianFiberNormSq_lowOrder_le (I := I) (M := M) g₀ a ha_super hR
  obtain ⟨ΛS, FS, hΛS_nn, hFS_nn, hS⟩ :=
    sharpFlatEndoCc_lowOrder_jetL2_succ_generic (I := I) (M := M) g₀ a ha_super hR hδ₀
  have hTA_ex : ∀ q : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g₀ 1 2) (T : SmoothCcTensor g₀ 1 1)
        (ΛS' ΛT' : ℝ), 0 ≤ ΛS' → 0 ≤ ΛT' →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x (S.toSection x) ≤ ΛS' ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (T.toSection x) ≤ ΛT' ^ 2) →
        MeasureTheory.Integrable
            (fun x => ∑ i ∈ Finset.range (q + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 i S).toSection x)
                * ∑ l ∈ Finset.range (q + 1 - i),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                      ((iteratedCovGrad (I := I) g₀ 1 1 l T).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
          (∫ x, (∑ i ∈ Finset.range (q + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 i S).toSection x)
                * ∑ l ∈ Finset.range (q + 1 - i),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                      ((iteratedCovGrad (I := I) g₀ 1 1 l T).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            C * (ΛT' ^ 2 * ∑ i ∈ Finset.range (q + 1),
                  ‖iteratedCovGrad (I := I) g₀ 1 2 i S‖ ^ 2
                + ΛS' ^ 2 * ∑ l ∈ Finset.range (q + 1),
                  ‖iteratedCovGrad (I := I) g₀ 1 1 l T‖ ^ 2) := by
    intro q
    obtain ⟨C, hC_nn, hC⟩ :=
      exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
        (I := I) (M := M) g₀ 1 1 2 1 q
    exact ⟨C, hC_nn, fun S T ΛS' ΛT' h1 h2 h3 h4 => hC S T ΛS' ΛT' h1 h2 h3 h4⟩
  choose CT hCT_nn hCT using hTA_ex
  refine ⟨fun n => operatorFieldApplicationGdiag (E := E) n *
      ((∑ i ∈ Finset.range (n + 1), ΛKlow) * (∑ l ∈ Finset.range (n + 1), ΛS l)),
    fun i => ∑ q ∈ Finset.range (i + 1),
      operatorFieldApplicationGdiag (E := E) q * (CT q * (ΛS 0 * FK q + ΛK ^ 2 * FS q)),
    fun n => by
      apply mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) n)
      exact mul_nonneg (Finset.sum_nonneg fun _ _ => hΛKlow_nn)
        (Finset.sum_nonneg fun l _ => hΛS_nn l),
    fun i => Finset.sum_nonneg fun q _ => by
      apply mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) q)
      apply mul_nonneg (hCT_nn q)
      exact add_nonneg (mul_nonneg (hΛS_nn 0) (hFK_nn q))
        (mul_nonneg (sq_nonneg _) (hFS_nn q)), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  obtain ⟨hKsup, hKsum⟩ := hK g₁ P hδ_le hδ htie hPball
  obtain ⟨hSlow, hSsum⟩ := hS g₁ P htie hδ_le hδ0 hδ hPball
  have hid : connectionDifferenceSection (I := I) g₁ g₀ =
      ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 2 (raisedKoszul (I := I) g₀ g₁)
        (sharpFlatEndoCc (I := I) g₀ g₁) :=
    connectionDifferenceSection_eq_operatorFieldComposition_raisedKoszul_sharpFlatEndoCc (I := I) (M := M) g₀ g₁
  refine ⟨?_, ?_⟩
  · intro n hn x
    rw [hid]
    refine le_trans (riemannianFiberNormSq_iteratedCovGrad_operatorFieldComposition_diagonalProductGrid_rankLeft_le
      (I := I) (M := M) g₀ n 1 1 2 (raisedKoszul (I := I) g₀ g₁)
      (sharpFlatEndoCc (I := I) g₀ g₁) x) ?_
    refine mul_le_mul_of_nonneg_left ?_ (operatorFieldApplicationGdiag_nonneg (E := E) n)
    have hKn : ∀ i' ∈ Finset.range (n + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i') x
            ((iteratedCovGrad (I := I) g₀ 1 2 i' (raisedKoszul (I := I) g₀ g₁)).toSection x)
          * ∑ l ∈ Finset.range (n + 1 - i'),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                ((iteratedCovGrad (I := I) g₀ 1 1 l
                  (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
        ΛKlow * ∑ l ∈ Finset.range (n + 1), ΛS l := by
      intro i' hi'
      have hi'n : i' ≤ n := by have := Finset.mem_range.mp hi'; omega
      have hKfac := hKlow g₁ P htie hPball i' (by omega) x
      have hSfac : (∑ l ∈ Finset.range (n + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 1 l
              (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x)) ≤
          ∑ l ∈ Finset.range (n + 1), ΛS l := by
        calc (∑ l ∈ Finset.range (n + 1 - i'),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                ((iteratedCovGrad (I := I) g₀ 1 1 l
                  (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x))
            ≤ ∑ l ∈ Finset.range (n + 1 - i'), ΛS l :=
              Finset.sum_le_sum (fun l hl => hSlow l (by
                have := Finset.mem_range.mp hl; omega) x)
          _ ≤ ∑ l ∈ Finset.range (n + 1), ΛS l :=
              Finset.sum_le_sum_of_subset_of_nonneg
                (fun z hz => Finset.mem_range.mpr
                  (lt_of_lt_of_le (Finset.mem_range.mp hz) (Nat.sub_le (n + 1) i')))
                (fun l _ _ => hΛS_nn l)
      exact mul_le_mul hKfac hSfac
        (Finset.sum_nonneg fun l _ => riemannianFiberNormSq_nonneg _ _ _ _ _)
        hΛKlow_nn
    refine le_trans (Finset.sum_le_sum hKn) (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    ring
  · intro i hi
    have hterm : ∀ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 1 2 q (connectionDifferenceSection (I := I) g₁ g₀)‖ ^ 2 ≤
          operatorFieldApplicationGdiag (E := E) q * (CT q * (ΛS 0 * FK q + ΛK ^ 2 * FS q)) := by
      intro q hq
      have hq_le : q ≤ a + 1 := by have := Finset.mem_range.mp hq; omega
      have hS0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
          ((sharpFlatEndoCc (I := I) g₀ g₁).toSection x) ≤ (Real.sqrt (ΛS 0)) ^ 2 := by
        intro x
        rw [Real.sq_sqrt (hΛS_nn 0)]
        have h := hSlow 0 (by omega) x
        simpa only [iteratedCovGrad_zero] using h
      have hKs : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
          ((raisedKoszul (I := I) g₀ g₁).toSection x) ≤ ΛK ^ 2 := hKsup
      obtain ⟨hgrid_int, hgrid_bound⟩ := hCT q (raisedKoszul (I := I) g₀ g₁)
        (sharpFlatEndoCc (I := I) g₀ g₁) ΛK (Real.sqrt (ΛS 0)) hΛK_nn
        (Real.sqrt_nonneg _) hKs hS0
      rw [hid]
      have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀
        1 (2 + q)
        (iteratedCovGrad (I := I) g₀ 1 2 q
          (ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 2 (raisedKoszul (I := I) g₀ g₁)
            (sharpFlatEndoCc (I := I) g₀ g₁)))
        (fun x => operatorFieldApplicationGdiag (E := E) q *
          ∑ n ∈ Finset.range (q + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
                ((iteratedCovGrad (I := I) g₀ 1 2 n (raisedKoszul (I := I) g₀ g₁)).toSection x)
              * ∑ l ∈ Finset.range (q + 1 - n),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                    ((iteratedCovGrad (I := I) g₀ 1 1 l
                      (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x))
        (hgrid_int.const_mul (operatorFieldApplicationGdiag (E := E) q))
        (fun x => riemannianFiberNormSq_iteratedCovGrad_operatorFieldComposition_diagonalProductGrid_rankLeft_le
          (I := I) (M := M) g₀ q 1 1 2 (raisedKoszul (I := I) g₀ g₁)
          (sharpFlatEndoCc (I := I) g₀ g₁) x)
      refine le_trans hkey ?_
      rw [MeasureTheory.integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ (operatorFieldApplicationGdiag_nonneg (E := E) q)
      refine le_trans hgrid_bound ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCT_nn q)
      have h1 : (Real.sqrt (ΛS 0)) ^ 2 = ΛS 0 := Real.sq_sqrt (hΛS_nn 0)
      rw [h1]
      have hKsq := hKsum q hq_le
      have hSsq := hSsum q hq_le
      have e1 : ΛS 0 * (∑ n ∈ Finset.range (q + 1),
          ‖iteratedCovGrad (I := I) g₀ 1 2 n (raisedKoszul (I := I) g₀ g₁)‖ ^ 2) ≤
          ΛS 0 * FK q := mul_le_mul_of_nonneg_left hKsq (hΛS_nn 0)
      have e2 : ΛK ^ 2 * (∑ l ∈ Finset.range (q + 1),
          ‖iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁)‖ ^ 2) ≤
          ΛK ^ 2 * FS q := mul_le_mul_of_nonneg_left hSsq (sq_nonneg ΛK)
      linarith [e1, e2]
    exact Finset.sum_le_sum hterm

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private lemma connectionDifferenceSection_eq_cometricRaiseSlot0Field' (g₀ g₁ : SmoothRiemannianMetric I M) :
    connectionDifferenceSection (I := I) g₁ g₀ =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
        (domDomCongrSection (I := I) g₀ (finRotate 3) (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)) := by
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [connectionDifferenceSection_toSection, cometricRaiseSlot0Field_toSection]
  apply tensorRSSpace_ext 1 2 x
  intro om
  apply ContinuousMultilinearMap.ext
  intro YZ
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g₀ x om with hu
  set D : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (domDomCongrSection (I := I) g₀ (finRotate 3)
        (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)).toSection x)
      (unitTensor (I := I) (M := M) x) with hDdef
  have hLHS : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        connectionDifferenceFib (I := I) g₁ g₀ x) om YZ =
      g₀.inner x u (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (YZ 0) (YZ 1)) := by
    rw [connectionDifferenceFib_apply_eval]
    rw [show om (fun _ : Fin 1 => PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (YZ 0) (YZ 1)) =
        cotangentToDual (I := I) (x := x) om
          (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (YZ 0) (YZ 1)) from
      (cotangentToDual_apply (I := I) om _).symm]
    rw [show cotangentToDual (I := I) (x := x) om
          (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (YZ 0) (YZ 1)) =
        cotangentToDualLinear (I := I) (x := x) om
          (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (YZ 0) (YZ 1)) from rfl]
    rw [← inverseMetricSharpFib_inner (I := I) g₀ x om
      (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (YZ 0) (YZ 1)), ← hu]
  have hRHS : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        cometricRaiseSlot0Fib (I := I) g₀ 1 x D) om YZ =
      Tensor0SSpace.toModel D
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x u)
          (fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ k))) := by
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 1 x D om]
    rw [show (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (1 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) D YZ : ℝ) =
        Tensor0SSpace.toModel
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (1 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) D)
          (fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ k)) from by
      rw [Tensor0SSpace.toModel_apply_model_vector]
      congr 1]
    rw [interior_product_toModel_eval' (I := I) (M := M) (1 + 1) x
      (inverseMetricSharpFib (I := I) g₀ x om) D YZ, ← hu]
  refine hLHS.trans (Eq.trans ?_ hRHS.symm)
  have hum : unitModel (I := I) (M := M) g₀ 3
      (domDomCongrSection (I := I) g₀ (finRotate 3) (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)) x =
      Tensor0SSpace.toModel D := rfl
  rw [show Tensor0SSpace.toModel D
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x u)
          (fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ k))) =
        unitModel (I := I) (M := M) g₀ 3
          (domDomCongrSection (I := I) g₀ (finRotate 3) (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)) x
          (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x
            ((![u, YZ 0, YZ 1] : Fin 3 → TangentSpace I x) i)) from by
    rw [hum]; congr 1; funext k; fin_cases k <;> rfl]
  rw [domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x
        ((![u, YZ 0, YZ 1] : Fin 3 → TangentSpace I x) ((finRotate 3) i))) =
      (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x
        ((![YZ 0, YZ 1, u] : Fin 3 → TangentSpace I x) i)) from by
    funext i
    fin_cases i <;> rfl]
  rw [connectionDifferenceLoweredCc_unitModel_apply']
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  rw [g₀.symm x u (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (YZ 0) (YZ 1))]

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma riemannianFiberNormSq_iteratedCovGrad_connectionDifferenceLoweredCc_eq_connectionDifferenceSection
    (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 2 n (connectionDifferenceSection (I := I) g₁ g₀)).toSection x) := by
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)).toSection x)
      = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
          ((iteratedCovGrad (I := I) g₀ 0 3 n
            (domDomCongrSection (I := I) g₀ (finRotate 3)
              (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁))).toSection x) :=
        (riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
          (finRotate 3) (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁) n x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
              (domDomCongrSection (I := I) g₀ (finRotate 3)
                (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)))).toSection x) :=
        (riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 1
          (domDomCongrSection (I := I) g₀ (finRotate 3)
            (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)) n x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n (connectionDifferenceSection (I := I) g₁ g₀)).toSection x) := by
        rw [connectionDifferenceSection_eq_cometricRaiseSlot0Field']

omit [NeZero (Module.finrank ℝ E)] in
lemma norm_iteratedCovGrad_connectionDifferenceLoweredCc_eq_connectionDifferenceSection
    (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 0 3 n (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)‖ =
      ‖iteratedCovGrad (I := I) g₀ 1 2 n (connectionDifferenceSection (I := I) g₁ g₀)‖ := by
  refine raisedKoszul_norm_eq_of_sq_eq (norm_nonneg _) (norm_nonneg _) ?_
  rw [SmoothCcTensor.norm_def, SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact riemannianFiberNormSq_iteratedCovGrad_connectionDifferenceLoweredCc_eq_connectionDifferenceSection (I := I) (M := M) g₀ g₁ n x

omit [NeZero (Module.finrank ℝ E)] in
omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma riemannianFiberNormSq_neg_local'
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (-v) =
      riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (-v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_neg]
  rw [← neg_one_smul ℝ (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
        (r := r) (s := s) (x := x) v),
    tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
  ring

theorem metricLoweredConnectionDifference_lowOrder_iteratedCovGrad_norm_sq_succ_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ F : ℕ → ℝ), (∀ n, 0 ≤ Λ n) ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ n : ℕ, n ≤ 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
            ((iteratedCovGrad (I := I) g₀ 0 3 n
              (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤ Λ n) ∧
        (∀ i : ℕ, i ≤ a + 1 →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 3 q (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
              F i) := by
  classical
  obtain ⟨ΛC, FC, hΛC_nn, hFC_nn, hC⟩ :=
    connectionDifferenceSection_lowOrder_jetL2_succ_generic (I := I) (M := M) g₀ a ha_super hR hδ₀
  have hSBackground_ex : ∀ n : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g_bg)).toSection x) ≤
        K :=
    fun n => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 0 (3 + n)
      (iteratedCovGrad (I := I) g₀ 0 3 n (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g_bg))
  choose SBackground hSBackground_nn hSBackground using hSBackground_ex
  set FBackground : ℕ → ℝ :=
    fun q => ‖iteratedCovGrad (I := I) g₀ 0 3 q (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g_bg)‖ ^ 2
    with hFBackground_def
  have hFBackground_nn : ∀ q, 0 ≤ FBackground q := fun q => sq_nonneg _
  refine ⟨fun n => 2 * ΛC n + 2 * SBackground n,
    fun i => ∑ q ∈ Finset.range (i + 1), (2 * FC i + 2 * FBackground q),
    fun n => add_nonneg (mul_nonneg (by norm_num) (hΛC_nn n))
      (mul_nonneg (by norm_num) (hSBackground_nn n)),
    fun i => Finset.sum_nonneg (fun q _ => add_nonneg
      (mul_nonneg (by norm_num) (hFC_nn i)) (mul_nonneg (by norm_num) (hFBackground_nn q))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  obtain ⟨hClow, hCsum⟩ := hC g₁ P htie hδ_le hδ0 hδ hPball
  refine ⟨?_, ?_⟩
  · intro n hn x
    have hsplit : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n
          (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
            ((iteratedCovGrad (I := I) g₀ 0 3 n (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)).toSection x)
          + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
            ((iteratedCovGrad (I := I) g₀ 0 3 n
              (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g_bg)).toSection x) := by
      rw [metricLoweredConnectionDifference, iteratedCovGrad_sub]
      rw [show ((iteratedCovGrad (I := I) g₀ 0 3 n (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁) -
            iteratedCovGrad (I := I) g₀ 0 3 n (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g_bg)).toSection x) =
          (iteratedCovGrad (I := I) g₀ 0 3 n (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)).toSection x +
            -((iteratedCovGrad (I := I) g₀ 0 3 n
              (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g_bg)).toSection x) from by
        rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
          sub_eq_add_neg]]
      refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (3 + n) x _ _) ?_
      rw [riemannianFiberNormSq_neg_local']
    have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)).toSection x) ≤
        ΛC n := by
      rw [riemannianFiberNormSq_iteratedCovGrad_connectionDifferenceLoweredCc_eq_connectionDifferenceSection (I := I) (M := M) g₀ g₁ n x]
      exact hClow n hn x
    linarith [hsplit, h1, hSBackground n x]
  · intro i hi
    have hterm : ∀ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 3 q (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
          2 * FC i + 2 * FBackground q := by
      intro q hq
      have h1 : ‖iteratedCovGrad (I := I) g₀ 0 3 q (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)‖ ^ 2 ≤
          FC i := by
        rw [norm_iteratedCovGrad_connectionDifferenceLoweredCc_eq_connectionDifferenceSection (I := I) (M := M) g₀ g₁ q]
        refine le_trans ?_ (hCsum i hi)
        exact Finset.single_le_sum
          (f := fun q' => ‖iteratedCovGrad (I := I) g₀ 1 2 q'
            (connectionDifferenceSection (I := I) g₁ g₀)‖ ^ 2)
          (fun q' _ => sq_nonneg _) hq
      have htri : ‖iteratedCovGrad (I := I) g₀ 0 3 q (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)‖ ≤
          ‖iteratedCovGrad (I := I) g₀ 0 3 q (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)‖ +
            ‖iteratedCovGrad (I := I) g₀ 0 3 q (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g_bg)‖ := by
        rw [metricLoweredConnectionDifference, iteratedCovGrad_sub]
        exact norm_sub_le _ _
      have hFBackgroundq : FBackground q =
          ‖iteratedCovGrad (I := I) g₀ 0 3 q (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g_bg)‖ ^ 2 := rfl
      nlinarith only [htri, h1, hFBackgroundq.ge,
        norm_nonneg (iteratedCovGrad (I := I) g₀ 0 3 q (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)),
        norm_nonneg (iteratedCovGrad (I := I) g₀ 0 3 q (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g_bg)),
        norm_nonneg (iteratedCovGrad (I := I) g₀ 0 3 q (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)),
        sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 3 q (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)‖ -
          ‖iteratedCovGrad (I := I) g₀ 0 3 q (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g_bg)‖)]
    exact Finset.sum_le_sum hterm

theorem cometricCastG0_riemannianFiberNormSq_lowOrder_le (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℕ → ℝ, (∀ n, 0 ≤ Λ n) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ n : ℕ, n ≤ 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + n) x
            ((iteratedCovGrad (I := I) g₀ 3 1 n
              (cometricCastG0 (I := I) g₀ g₁)).toSection x) ≤ Λ n := by
  classical
  obtain ⟨C_base, hC_base_nn, hC_base⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_zero_metricComparisonDifferenceEndomorphismField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨Λw, hΛw_nn, hΛw⟩ :=
    exists_window_pointwise_jet_le (I := I) (M := M) g₀ a ha_super hR
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  set Φ : SmoothCcTensor g₀ 3 1 := cometricDoubleTraceField (I := I) g₀ 1 with hΦ_def
  have hSΦ_ex : ∀ n : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + n) x
        ((iteratedCovGrad (I := I) g₀ 3 1 n Φ).toSection x) ≤ K :=
    fun n => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 3 (1 + n)
      (iteratedCovGrad (I := I) g₀ 3 1 n Φ)
  choose SΦ hSΦ_nn hSΦ using hSΦ_ex
  set Gw : ℕ → ℝ := fun n => (∑ m ∈ Finset.range (n + 1),
    ((Finset.Nat.antidiagonalTuple m n).card : ℝ)) * max (Λw ^ 2) 1 ^ n with hGw_def
  have hGw_nn : ∀ n, 0 ≤ Gw n := by
    intro n
    rw [hGw_def]
    apply mul_nonneg (Finset.sum_nonneg (fun m _ => Nat.cast_nonneg _))
    apply pow_nonneg
    exact le_trans zero_le_one (le_max_right _ _)
  refine ⟨fun n => 2 * SΦ n + 2 * (operatorFieldApplicationGdiag (E := E) n *
      ((∑ i' ∈ Finset.range (n + 1), SΦ i') *
        (∑ l ∈ Finset.range (n + 1), fr ^ 2 * (C_base l * Gw l)))),
    fun n => add_nonneg (mul_nonneg (by norm_num) (hSΦ_nn n))
      (mul_nonneg (by norm_num) (mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) n)
        (mul_nonneg (Finset.sum_nonneg fun i' _ => hSΦ_nn i')
          (Finset.sum_nonneg fun l _ => mul_nonneg (sq_nonneg fr)
            (mul_nonneg (hC_base_nn l) (hGw_nn l)))))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball n hn x
  set W33 : SmoothCcTensor g₀ 3 3 :=
    endoSlotZeroCcTensor (I := I) (M := M) g₀ 2
      (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)
    with hW33_def
  have hwin_n : ∀ j : ℕ, j ≤ n → ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) y
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection y) ≤ Λw ^ 2 :=
    fun j hj y => hΛw P hPball j (by omega) y
  have hW33_pt : ∀ l : ℕ, l ≤ n → ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + l) y
        ((iteratedCovGrad (I := I) g₀ 3 3 l W33).toSection y) ≤
      fr ^ 2 * (C_base l * Gw l) := by
    intro l hl y
    have h1 := riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) g₀ 2
      (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁) l y
    rw [← hW33_def, ← hfr_def] at h1
    have h2 := hC_base g₁ P htie hδ_le hδ0 hδ l y
    have hwin_l : ∀ j : ℕ, j ≤ l → ∀ z : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) z
          ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection z) ≤ Λw ^ 2 :=
      fun j hj z => hwin_n j (by omega) z
    have hgrid := window_grid_le (I := I) (M := M) g₀ P l hwin_l y
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + l) y
          ((iteratedCovGrad (I := I) g₀ 3 3 l W33).toSection y)
        ≤ fr ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) y
            ((iteratedCovGrad (I := I) g₀ 1 1 l
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁))).toSection y) := h1
      _ ≤ fr ^ 2 * (C_base l *
            (∑ m ∈ Finset.range (l + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple m l,
              ∏ k : Fin m, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e k) y
                ((iteratedCovGrad (I := I) g₀ 0 2 (e k) P).toSection y))) :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg fr)
      _ ≤ fr ^ 2 * (C_base l * Gw l) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg fr)
          rw [hGw_def]
          exact mul_le_mul_of_nonneg_left hgrid (hC_base_nn l)
  have hid : cometricCastG0 (I := I) g₀ g₁ =
      Φ + ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W33 := by
    have h := cometricCastG0_eq_doubleTrace_add_ccOperatorFieldComp (I := I) g₀ g₁
    rw [← hΦ_def, ← hW33_def] at h
    exact h
  have hsplit : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + n) x
      ((iteratedCovGrad (I := I) g₀ 3 1 n (cometricCastG0 (I := I) g₀ g₁)).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + n) x
          ((iteratedCovGrad (I := I) g₀ 3 1 n Φ).toSection x)
        + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + n) x
          ((iteratedCovGrad (I := I) g₀ 3 1 n
            (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W33)).toSection x) := by
    rw [hid, iteratedCovGrad_add]
    rw [show ((iteratedCovGrad (I := I) g₀ 3 1 n Φ +
          iteratedCovGrad (I := I) g₀ 3 1 n
            (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W33)).toSection x) =
        (iteratedCovGrad (I := I) g₀ 3 1 n Φ).toSection x +
          (iteratedCovGrad (I := I) g₀ 3 1 n
            (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W33)).toSection x from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    exact riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 3 (1 + n) x _ _
  have happ : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + n) x
      ((iteratedCovGrad (I := I) g₀ 3 1 n
        (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W33)).toSection x) ≤
      operatorFieldApplicationGdiag (E := E) n *
        ((∑ i' ∈ Finset.range (n + 1), SΦ i') *
          (∑ l ∈ Finset.range (n + 1), fr ^ 2 * (C_base l * Gw l))) := by
    refine le_trans (riemannianFiberNormSq_iteratedCovGrad_operatorFieldComposition_diagonalProductGrid_rankLeft_le
      (I := I) (M := M) g₀ n 3 3 1 Φ W33 x) ?_
    refine mul_le_mul_of_nonneg_left ?_ (operatorFieldApplicationGdiag_nonneg (E := E) n)
    have hkn : ∀ i' ∈ Finset.range (n + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i') x
            ((iteratedCovGrad (I := I) g₀ 3 1 i' Φ).toSection x)
          * ∑ l ∈ Finset.range (n + 1 - i'),
              riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + l) x
                ((iteratedCovGrad (I := I) g₀ 3 3 l W33).toSection x) ≤
        SΦ i' * ∑ l ∈ Finset.range (n + 1), fr ^ 2 * (C_base l * Gw l) := by
      intro i' hi'
      refine mul_le_mul (hSΦ i' x) ?_
        (Finset.sum_nonneg fun l _ => riemannianFiberNormSq_nonneg _ _ _ _ _) (hSΦ_nn i')
      calc (∑ l ∈ Finset.range (n + 1 - i'),
            riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + l) x
              ((iteratedCovGrad (I := I) g₀ 3 3 l W33).toSection x))
          ≤ ∑ l ∈ Finset.range (n + 1 - i'), fr ^ 2 * (C_base l * Gw l) :=
            Finset.sum_le_sum (fun l hl => hW33_pt l (by
              have := Finset.mem_range.mp hl; omega) x)
        _ ≤ ∑ l ∈ Finset.range (n + 1), fr ^ 2 * (C_base l * Gw l) :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (fun z hz => Finset.mem_range.mpr
                (lt_of_lt_of_le (Finset.mem_range.mp hz) (Nat.sub_le (n + 1) i')))
              (fun l _ _ => mul_nonneg (sq_nonneg fr)
                (mul_nonneg (hC_base_nn l) (hGw_nn l)))
    refine le_trans (Finset.sum_le_sum hkn) (le_of_eq ?_)
    rw [← Finset.sum_mul]
  have hΦn := hSΦ n x
  linarith [hsplit, happ, hΦn]

theorem deTurckVectorFieldCovector_lowOrder_iteratedCovGrad_norm_sq_succ_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ F : ℕ → ℝ), (∀ n, 0 ≤ Λ n) ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ n : ℕ, n ≤ 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + n) x
            ((iteratedCovGrad (I := I) g₀ 0 1 n
              (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤ Λ n) ∧
        (∀ i : ℕ, i ≤ a + 1 →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 1 q (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
              F i) := by
  classical
  obtain ⟨ΛCsup, FC, hΛCsup_nn, hFC_nn, hCgen⟩ :=
    cometricCastG0_order0sup_jetL2_succ_generic (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨ΛClow, hΛClow_nn, hClow⟩ :=
    cometricCastG0_riemannianFiberNormSq_lowOrder_le (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨ΛX, FX, hΛX_nn, hFX_nn, hXgen⟩ :=
    metricLoweredConnectionDifference_lowOrder_iteratedCovGrad_norm_sq_succ_le (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  have hTA_ex : ∀ q : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g₀ 3 1) (T : SmoothCcTensor g₀ 0 3)
        (ΛS' ΛT' : ℝ), 0 ≤ ΛS' → 0 ≤ ΛT' →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 1 x (S.toSection x) ≤ ΛS' ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x (T.toSection x) ≤ ΛT' ^ 2) →
        MeasureTheory.Integrable
            (fun x => ∑ i ∈ Finset.range (q + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i) x
                  ((iteratedCovGrad (I := I) g₀ 3 1 i S).toSection x)
                * ∑ l ∈ Finset.range (q + 1 - i),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                      ((iteratedCovGrad (I := I) g₀ 0 3 l T).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
          (∫ x, (∑ i ∈ Finset.range (q + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i) x
                  ((iteratedCovGrad (I := I) g₀ 3 1 i S).toSection x)
                * ∑ l ∈ Finset.range (q + 1 - i),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                      ((iteratedCovGrad (I := I) g₀ 0 3 l T).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            C * (ΛT' ^ 2 * ∑ i ∈ Finset.range (q + 1),
                  ‖iteratedCovGrad (I := I) g₀ 3 1 i S‖ ^ 2
                + ΛS' ^ 2 * ∑ l ∈ Finset.range (q + 1),
                  ‖iteratedCovGrad (I := I) g₀ 0 3 l T‖ ^ 2) := by
    intro q
    obtain ⟨C, hC_nn, hC⟩ :=
      exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
        (I := I) (M := M) g₀ 3 0 1 3 q
    exact ⟨C, hC_nn, fun S T ΛS' ΛT' h1 h2 h3 h4 => hC S T ΛS' ΛT' h1 h2 h3 h4⟩
  choose CT hCT_nn hCT using hTA_ex
  refine ⟨fun n => operatorFieldApplicationGdiag (E := E) n *
      ((∑ i' ∈ Finset.range (n + 1), ΛClow i') * (∑ l ∈ Finset.range (n + 1), ΛX l)),
    fun i => ∑ q ∈ Finset.range (i + 1),
      operatorFieldApplicationGdiag (E := E) q * (CT q * (ΛX 0 * FC q + ΛCsup ^ 2 * FX q)),
    fun n => mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) n)
      (mul_nonneg (Finset.sum_nonneg fun i' _ => hΛClow_nn i')
        (Finset.sum_nonneg fun l _ => hΛX_nn l)),
    fun i => Finset.sum_nonneg fun q _ => mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) q)
      (mul_nonneg (hCT_nn q) (add_nonneg (mul_nonneg (hΛX_nn 0) (hFC_nn q))
        (mul_nonneg (sq_nonneg _) (hFX_nn q)))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  obtain ⟨hCsup, hCsum⟩ := hCgen g₁ P hδ_le hδ htie hPball
  obtain ⟨hXlow, hXsum⟩ := hXgen g₁ P htie hδ_le hδ0 hδ hPball
  have hform : deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg =
      operatorFieldApply (I := I) (M := M) g₀ 3 1 (cometricCastG0 (I := I) g₀ g₁)
        (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg) := rfl
  refine ⟨?_, ?_⟩
  · intro n hn x
    rw [hform]
    refine le_trans (operatorFieldApplication_iteratedCovGrad_diagonalProductGrid_le (I := I) (M := M) g₀ 3 1
      (cometricCastG0 (I := I) g₀ g₁) (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg) n x) ?_
    refine mul_le_mul_of_nonneg_left ?_ (operatorFieldApplicationGdiag_nonneg (E := E) n)
    have hkn : ∀ i' ∈ Finset.range (n + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i') x
            ((iteratedCovGrad (I := I) g₀ 3 1 i' (cometricCastG0 (I := I) g₀ g₁)).toSection x)
          * ∑ l ∈ Finset.range (n + 1 - i'),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 3 l
                  (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
        ΛClow i' * ∑ l ∈ Finset.range (n + 1), ΛX l := by
      intro i' hi'
      have hi'n : i' ≤ n := by have := Finset.mem_range.mp hi'; omega
      refine mul_le_mul (hClow g₁ P htie hδ_le hδ0 hδ hPball i' (by omega) x) ?_
        (Finset.sum_nonneg fun l _ => riemannianFiberNormSq_nonneg _ _ _ _ _) (hΛClow_nn i')
      calc (∑ l ∈ Finset.range (n + 1 - i'),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 3 l
                (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)).toSection x))
          ≤ ∑ l ∈ Finset.range (n + 1 - i'), ΛX l :=
            Finset.sum_le_sum (fun l hl => hXlow l (by
              have := Finset.mem_range.mp hl; omega) x)
        _ ≤ ∑ l ∈ Finset.range (n + 1), ΛX l :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (fun z hz => Finset.mem_range.mpr
                (lt_of_lt_of_le (Finset.mem_range.mp hz) (Nat.sub_le (n + 1) i')))
              (fun l _ _ => hΛX_nn l)
    refine le_trans (Finset.sum_le_sum hkn) (le_of_eq ?_)
    rw [← Finset.sum_mul]
  · intro i hi
    have hterm : ∀ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 1 q (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
          operatorFieldApplicationGdiag (E := E) q * (CT q * (ΛX 0 * FC q + ΛCsup ^ 2 * FX q)) := by
      intro q hq
      have hq_le : q ≤ a + 1 := by have := Finset.mem_range.mp hq; omega
      have hX0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
          ((metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg).toSection x) ≤ (Real.sqrt (ΛX 0)) ^ 2 := by
        intro x
        rw [Real.sq_sqrt (hΛX_nn 0)]
        have h := hXlow 0 (by omega) x
        simpa only [iteratedCovGrad_zero] using h
      obtain ⟨hgrid_int, hgrid_bound⟩ := hCT q (cometricCastG0 (I := I) g₀ g₁)
        (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg) ΛCsup (Real.sqrt (ΛX 0)) hΛCsup_nn
        (Real.sqrt_nonneg _) hCsup hX0
      rw [hform]
      have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀
        0 (1 + q)
        (iteratedCovGrad (I := I) g₀ 0 1 q
          (operatorFieldApply (I := I) (M := M) g₀ 3 1 (cometricCastG0 (I := I) g₀ g₁)
            (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)))
        (fun x => operatorFieldApplicationGdiag (E := E) q *
          ∑ n ∈ Finset.range (q + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + n) x
                ((iteratedCovGrad (I := I) g₀ 3 1 n
                  (cometricCastG0 (I := I) g₀ g₁)).toSection x)
              * ∑ l ∈ Finset.range (q + 1 - n),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                    ((iteratedCovGrad (I := I) g₀ 0 3 l
                      (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)).toSection x))
        (hgrid_int.const_mul (operatorFieldApplicationGdiag (E := E) q))
        (fun x => operatorFieldApplication_iteratedCovGrad_diagonalProductGrid_le (I := I) (M := M) g₀ 3 1
          (cometricCastG0 (I := I) g₀ g₁) (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg) q x)
      refine le_trans hkey ?_
      rw [MeasureTheory.integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ (operatorFieldApplicationGdiag_nonneg (E := E) q)
      refine le_trans hgrid_bound ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCT_nn q)
      have h1 : (Real.sqrt (ΛX 0)) ^ 2 = ΛX 0 := Real.sq_sqrt (hΛX_nn 0)
      rw [h1]
      have e1 : ΛX 0 * (∑ n ∈ Finset.range (q + 1),
          ‖iteratedCovGrad (I := I) g₀ 3 1 n (cometricCastG0 (I := I) g₀ g₁)‖ ^ 2) ≤
          ΛX 0 * FC q := mul_le_mul_of_nonneg_left (hCsum q hq_le) (hΛX_nn 0)
      have e2 : ΛCsup ^ 2 * (∑ l ∈ Finset.range (q + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 3 l (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2) ≤
          ΛCsup ^ 2 * FX q := mul_le_mul_of_nonneg_left (hXsum q hq_le) (sq_nonneg ΛCsup)
      linarith [e1, e2]
    exact Finset.sum_le_sum hterm

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma riemannianFiberNormSq_iteratedCovGrad_connectionDifferenceRaisedEndomorphism_eq_connectionDifferenceSection (g₀ g₁ : SmoothRiemannianMetric I M)
    (n : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 2 n (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 2 n (connectionDifferenceSection (I := I) g₁ g₀)).toSection x) := by
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 2 n (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)).toSection x)
      = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
          ((iteratedCovGrad (I := I) g₀ 0 3 n
            (domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
              (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁))).toSection x) := by
        rw [connectionDifferenceRaisedEndomorphism]
        exact riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 1
          (domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
            (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)) n x
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
          ((iteratedCovGrad (I := I) g₀ 0 3 n (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)).toSection x) :=
        riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
          (Equiv.swap (1 : Fin 3) 2) (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁) n x
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n (connectionDifferenceSection (I := I) g₁ g₀)).toSection x) :=
        riemannianFiberNormSq_iteratedCovGrad_connectionDifferenceLoweredCc_eq_connectionDifferenceSection (I := I) (M := M) g₀ g₁ n x

omit [NeZero (Module.finrank ℝ E)] in
lemma norm_iteratedCovGrad_connectionDifferenceRaisedEndomorphism_eq_connectionDifferenceSection (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 1 2 n (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)‖ =
      ‖iteratedCovGrad (I := I) g₀ 1 2 n (connectionDifferenceSection (I := I) g₁ g₀)‖ := by
  refine raisedKoszul_norm_eq_of_sq_eq (norm_nonneg _) (norm_nonneg _) ?_
  rw [SmoothCcTensor.norm_def, SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact riemannianFiberNormSq_iteratedCovGrad_connectionDifferenceRaisedEndomorphism_eq_connectionDifferenceSection (I := I) (M := M) g₀ g₁ n x

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma riemannianFiberNormSq_iteratedCovGrad_wAlphaA_eq_succ_wOmega (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 2 i
          (deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g₀ g₁ g_bg)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + (i + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 1 (i + 1)
          (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg)).toSection x) := by
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 2 i
          (deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
      = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 2 i
            (covGrad (I := I) (M := M) g₀ 0 1
              (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg))).toSection x) := by
        rw [deTurckVectorFieldCovariantDerivativeLoweredBase]
        exact riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
          (Equiv.swap (0 : Fin 2) 1)
          (covGrad (I := I) (M := M) g₀ 0 1 (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg)) i x
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + (i + 1)) x
          ((iteratedCovGrad (I := I) g₀ 0 1 (i + 1)
            (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg)).toSection x) :=
        riemannianFiberNormSq_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 0 1 i
          (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg) x

omit [NeZero (Module.finrank ℝ E)] in
lemma norm_iteratedCovGrad_deTurckVectorFieldCovariantDerivativeLoweredBase_eq_succ_deTurckVectorFieldCovector (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (i : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 0 2 i (deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g₀ g₁ g_bg)‖ =
      ‖iteratedCovGrad (I := I) g₀ 0 1 (i + 1) (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg)‖ := by
  refine raisedKoszul_norm_eq_of_sq_eq (norm_nonneg _) (norm_nonneg _) ?_
  rw [SmoothCcTensor.norm_def, SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact riemannianFiberNormSq_iteratedCovGrad_wAlphaA_eq_succ_wOmega (I := I) (M := M) g₀ g₁ g_bg i x

theorem deTurckVectorFieldCovariantDerivativeLowered_covariantJetNormSq_zero_bound
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ0 : ℝ) (F : ℕ → ℝ), 0 ≤ Λ0 ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
            ((deTurckVectorFieldCovariantDerivativeLowered (I := I) (M := M) g₀ g₁ g_bg).toSection x) ≤ Λ0) ∧
        (∀ i : ℕ, i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 0 2 i (deTurckVectorFieldCovariantDerivativeLowered (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
            F i) := by
  classical
  obtain ⟨ΛO, FO, hΛO_nn, hFO_nn, hOgen⟩ :=
    deTurckVectorFieldCovector_lowOrder_iteratedCovGrad_norm_sq_succ_le (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  obtain ⟨ΛCd, FCd, hΛCd_nn, hFCd_nn, hCdgen⟩ :=
    connectionDifferenceSection_lowOrder_jetL2_succ_generic (I := I) (M := M) g₀ a ha_super hR hδ₀
  have hTA_ex : ∀ q : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g₀ 1 2) (T : SmoothCcTensor g₀ 0 1)
        (ΛS' ΛT' : ℝ), 0 ≤ ΛS' → 0 ≤ ΛT' →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x (S.toSection x) ≤ ΛS' ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 1 x (T.toSection x) ≤ ΛT' ^ 2) →
        MeasureTheory.Integrable
            (fun x => ∑ i ∈ Finset.range (q + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 i S).toSection x)
                * ∑ l ∈ Finset.range (q + 1 - i),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + l) x
                      ((iteratedCovGrad (I := I) g₀ 0 1 l T).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
          (∫ x, (∑ i ∈ Finset.range (q + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 i S).toSection x)
                * ∑ l ∈ Finset.range (q + 1 - i),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + l) x
                      ((iteratedCovGrad (I := I) g₀ 0 1 l T).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            C * (ΛT' ^ 2 * ∑ i ∈ Finset.range (q + 1),
                  ‖iteratedCovGrad (I := I) g₀ 1 2 i S‖ ^ 2
                + ΛS' ^ 2 * ∑ l ∈ Finset.range (q + 1),
                  ‖iteratedCovGrad (I := I) g₀ 0 1 l T‖ ^ 2) := by
    intro q
    obtain ⟨C, hC_nn, hC⟩ :=
      exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
        (I := I) (M := M) g₀ 1 0 2 1 q
    exact ⟨C, hC_nn, fun S T ΛS' ΛT' h1 h2 h3 h4 => hC S T ΛS' ΛT' h1 h2 h3 h4⟩
  choose CT hCT_nn hCT using hTA_ex
  refine ⟨2 * ΛO 1 + 2 * (operatorFieldApplicationGdiag (E := E) 0 * (ΛCd 0 * ΛO 0)),
    fun i => 2 * FO (i + 1) +
      2 * (operatorFieldApplicationGdiag (E := E) i * (CT i * (ΛO 0 * FCd i + ΛCd 0 * FO i))),
    add_nonneg (mul_nonneg (by norm_num) (hΛO_nn 1))
      (mul_nonneg (by norm_num) (mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) 0)
        (mul_nonneg (hΛCd_nn 0) (hΛO_nn 0)))),
    fun i => add_nonneg (mul_nonneg (by norm_num) (hFO_nn (i + 1)))
      (mul_nonneg (by norm_num) (mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) i)
        (mul_nonneg (hCT_nn i) (add_nonneg (mul_nonneg (hΛO_nn 0) (hFCd_nn i))
          (mul_nonneg (hΛCd_nn 0) (hFO_nn i)))))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  obtain ⟨hOlow, hOsum⟩ := hOgen g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hCdlow, hCdsum⟩ := hCdgen g₁ P htie hδ_le hδ0 hδ hPball
  have hwCAlow : ∀ n : ℕ, n ≤ 1 → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 2 n (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)).toSection x) ≤
      ΛCd n := by
    intro n hn x
    rw [riemannianFiberNormSq_iteratedCovGrad_connectionDifferenceRaisedEndomorphism_eq_connectionDifferenceSection (I := I) (M := M) g₀ g₁ n x]
    exact hCdlow n hn x
  have hwCAsum : ∀ i : ℕ, i ≤ a + 1 →
      ∑ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 1 2 q (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤ FCd i := by
    intro i hi
    refine le_trans (le_of_eq (Finset.sum_congr rfl (fun q _ => ?_))) (hCdsum i hi)
    rw [norm_iteratedCovGrad_connectionDifferenceRaisedEndomorphism_eq_connectionDifferenceSection (I := I) (M := M) g₀ g₁ q]
  have hBform : deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg =
      operatorFieldApply (I := I) (M := M) g₀ 1 2 (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)
        (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg) := rfl
  have hBlow : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        ((deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg).toSection x) ≤
      operatorFieldApplicationGdiag (E := E) 0 * (ΛCd 0 * ΛO 0) := by
    intro x
    have hg := operatorFieldApplication_iteratedCovGrad_diagonalProductGrid_le (I := I) (M := M) g₀ 1 2
      (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁) (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg) 0 x
    have hgoal : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        ((deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 0) x
          ((iteratedCovGrad (I := I) g₀ 0 2 0
            (operatorFieldApply (I := I) (M := M) g₀ 1 2 (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)
              (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg))).toSection x) := by
      rw [hBform, iteratedCovGrad_zero]
    rw [hgoal]
    refine le_trans hg ?_
    have hsum0 : (∑ i ∈ Finset.range (0 + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 2 i (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)).toSection x)
          * ∑ l ∈ Finset.range (0 + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 1 l
                  (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg)).toSection x)) ≤
        ΛCd 0 * ΛO 0 := by
      rw [Finset.sum_range_one, Finset.sum_range_one]
      exact mul_le_mul (hwCAlow 0 (by omega) x) (hOlow 0 (by omega) x)
        (riemannianFiberNormSq_nonneg _ _ _ _ _) (hΛCd_nn 0)
    exact mul_le_mul_of_nonneg_left hsum0 (operatorFieldApplicationGdiag_nonneg (E := E) 0)
  have hBsum : ∀ i : ℕ, i ≤ a →
      ‖iteratedCovGrad (I := I) g₀ 0 2 i (deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
        operatorFieldApplicationGdiag (E := E) i * (CT i * (ΛO 0 * FCd i + ΛCd 0 * FO i)) := by
    intro i hi
    have hO0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 1 x
        ((deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg).toSection x) ≤ (Real.sqrt (ΛO 0)) ^ 2 := by
      intro x
      rw [Real.sq_sqrt (hΛO_nn 0)]
      have h := hOlow 0 (by omega) x
      simpa only [iteratedCovGrad_zero] using h
    have hCA0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
        ((connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁).toSection x) ≤ (Real.sqrt (ΛCd 0)) ^ 2 := by
      intro x
      rw [Real.sq_sqrt (hΛCd_nn 0)]
      have h := hwCAlow 0 (by omega) x
      simpa only [iteratedCovGrad_zero] using h
    obtain ⟨hgrid_int, hgrid_bound⟩ := hCT i (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)
      (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg) (Real.sqrt (ΛCd 0)) (Real.sqrt (ΛO 0))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hCA0 hO0
    rw [hBform]
    have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀
      0 (2 + i)
      (iteratedCovGrad (I := I) g₀ 0 2 i
        (operatorFieldApply (I := I) (M := M) g₀ 1 2 (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)
          (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg)))
      (fun x => operatorFieldApplicationGdiag (E := E) i *
        ∑ n ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
              ((iteratedCovGrad (I := I) g₀ 1 2 n (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)).toSection x)
            * ∑ l ∈ Finset.range (i + 1 - n),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 1 l
                    (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg)).toSection x))
      (hgrid_int.const_mul (operatorFieldApplicationGdiag (E := E) i))
      (fun x => operatorFieldApplication_iteratedCovGrad_diagonalProductGrid_le (I := I) (M := M) g₀ 1 2
        (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁) (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg) i x)
    refine le_trans hkey ?_
    rw [MeasureTheory.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (operatorFieldApplicationGdiag_nonneg (E := E) i)
    refine le_trans hgrid_bound ?_
    refine mul_le_mul_of_nonneg_left ?_ (hCT_nn i)
    rw [Real.sq_sqrt (hΛO_nn 0), Real.sq_sqrt (hΛCd_nn 0)]
    have e1 : ΛO 0 * (∑ n ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 1 2 n (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)‖ ^ 2) ≤
        ΛO 0 * FCd i := mul_le_mul_of_nonneg_left (hwCAsum i (by omega)) (hΛO_nn 0)
    have e2 : ΛCd 0 * (∑ l ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 1 l (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2) ≤
        ΛCd 0 * FO i := mul_le_mul_of_nonneg_left (hOsum i (by omega)) (hΛCd_nn 0)
    linarith [e1, e2]
  refine ⟨?_, ?_⟩
  · intro x
    have hA0 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        ((deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g₀ g₁ g_bg).toSection x) ≤ ΛO 1 := by
      have h := riemannianFiberNormSq_iteratedCovGrad_wAlphaA_eq_succ_wOmega (I := I) (M := M) g₀ g₁ g_bg 0 x
      have h0 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          ((deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g₀ g₁ g_bg).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 0) x
            ((iteratedCovGrad (I := I) g₀ 0 2 0
              (deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g₀ g₁ g_bg)).toSection x) := by
        rw [iteratedCovGrad_zero]
      rw [h0, h]
      exact hOlow 1 (by omega) x
    have hsplit : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        ((deTurckVectorFieldCovariantDerivativeLowered (I := I) (M := M) g₀ g₁ g_bg).toSection x) ≤
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
            ((deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g₀ g₁ g_bg).toSection x)
          + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
            ((deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg).toSection x) := by
      rw [deTurckVectorFieldCovariantDerivativeLowered]
      rw [show ((deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g₀ g₁ g_bg +
            deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg).toSection x) =
          (deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g₀ g₁ g_bg).toSection x +
            (deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg).toSection x from by
        rw [SmoothCcTensor.toSection_add]; rfl]
      exact riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 2 x _ _
    linarith [hsplit, hA0, hBlow x]
  · intro i hi
    have hAi : ‖iteratedCovGrad (I := I) g₀ 0 2 i
        (deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤ FO (i + 1) := by
      rw [norm_iteratedCovGrad_deTurckVectorFieldCovariantDerivativeLoweredBase_eq_succ_deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg i]
      refine le_trans ?_ (hOsum (i + 1) (by omega))
      exact Finset.single_le_sum
        (f := fun q => ‖iteratedCovGrad (I := I) g₀ 0 1 q
          (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2)
        (fun q _ => sq_nonneg _) (Finset.mem_range.mpr (by omega))
    have hBi := hBsum i hi
    have htri : ‖iteratedCovGrad (I := I) g₀ 0 2 i (deTurckVectorFieldCovariantDerivativeLowered (I := I) (M := M) g₀ g₁ g_bg)‖ ≤
        ‖iteratedCovGrad (I := I) g₀ 0 2 i (deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g₀ g₁ g_bg)‖ +
          ‖iteratedCovGrad (I := I) g₀ 0 2 i (deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)‖ := by
      rw [deTurckVectorFieldCovariantDerivativeLowered, iteratedCovGrad_add]
      exact norm_add_le _ _
    nlinarith only [htri, hAi, hBi,
      norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 i (deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g₀ g₁ g_bg)),
      norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 i (deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)),
      norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 i (deTurckVectorFieldCovariantDerivativeLowered (I := I) (M := M) g₀ g₁ g_bg)),
      sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 2 i
          (deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g₀ g₁ g_bg)‖ -
        ‖iteratedCovGrad (I := I) g₀ 0 2 i (deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)‖)]

omit [SigmaCompactSpace M] in
lemma riemannianFiberNormSq_iteratedCovGrad_deTurckVectorFieldCovariantDerivativeEndomorphismInsert_eq_deTurckVectorFieldCovariantDerivativeLowered (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 1 i
          (deTurckVectorFieldCovariantDerivativeEndomorphismInsert (I := I) (M := M) g₀ g₁ g_bg)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 2 i
          (deTurckVectorFieldCovariantDerivativeLowered (I := I) (M := M) g₀ g₁ g_bg)).toSection x) := by
  rw [deTurckVectorFieldCovariantDerivativeEndomorphismInsert_eq_cometricRaise_deTurckVectorFieldCovariantDerivativeLowered (I := I) (M := M) g₀ g₁ g_bg]
  exact riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 0
    (deTurckVectorFieldCovariantDerivativeLowered (I := I) (M := M) g₀ g₁ g_bg) i x

lemma norm_iteratedCovGrad_deTurckVectorFieldCovariantDerivativeEndomorphismInsert_eq_deTurckVectorFieldCovariantDerivativeLowered (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (i : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 1 1 i
        (deTurckVectorFieldCovariantDerivativeEndomorphismInsert (I := I) (M := M) g₀ g₁ g_bg)‖ =
      ‖iteratedCovGrad (I := I) g₀ 0 2 i (deTurckVectorFieldCovariantDerivativeLowered (I := I) (M := M) g₀ g₁ g_bg)‖ := by
  refine raisedKoszul_norm_eq_of_sq_eq (norm_nonneg _) (norm_nonneg _) ?_
  rw [SmoothCcTensor.norm_def, SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact riemannianFiberNormSq_iteratedCovGrad_deTurckVectorFieldCovariantDerivativeEndomorphismInsert_eq_deTurckVectorFieldCovariantDerivativeLowered (I := I) (M := M) g₀ g₁ g_bg i x

end DifferentialGeometry.Integral.Connection

end
