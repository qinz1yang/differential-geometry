import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingSharpC0JetSum

/-!
# Low-order antidiagonal jet-grid integrals in dimension three

This file extracts the part of the general high-order tame grid argument that
only uses the first four intrinsic `L2` jets.  It is the low-regularity input
needed for coefficients depending polynomially on a metric two-jet.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- On a closed three-manifold, every antidiagonal polynomial jet grid up to
a prescribed order `a ≥ 2` has a uniform integral bound from the intrinsic
`L2` jet through order `a`.  The lower endpoint `a = 2` is the key algebra
estimate used to keep moving trace factors independent of the top `H3` norm. -/
theorem low_grid_int
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 ≤ a) :
    ∃ K : ℝ → ℕ → ℝ,
      (∀ A : ℝ, 0 ≤ A → ∀ k : ℕ, 0 ≤ K A k) ∧
      ∀ (P : SmoothCcTensor g 0 2) (A : ℝ), 0 ≤ A →
        (∑ j ∈ Finset.range (a + 1),
          ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) ≤ A ^ 2 →
        ∀ k : ℕ, k ≤ a →
          MeasureTheory.Integrable
              (fun x => ∑ n ∈ Finset.range (k + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                  ∏ m : Fin n,
                    riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x))
              (riemannianVolumeMeasure (I := I) (M := M) g) ∧
            (∫ x, ∑ n ∈ Finset.range (k + 1),
                  ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                    ∏ m : Fin n,
                      riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
                        ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤ K A k := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  obtain ⟨Cpt, hCpt, hpt⟩ :=
    DifferentialGeometry.PDE.RicciFlow.
      exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
        (I := I) (M := M) g 0 2
  let Cgn : ℕ → ℝ := fun k =>
    if hk : 1 ≤ k then
      (DifferentialGeometry.Analysis.Sobolev.Tensor.
        exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
          (I := I) (M := M) g 0 2 k hk).choose
    else 0
  have hCgn : ∀ k, 0 ≤ Cgn k := by
    intro k
    simp only [Cgn]
    split_ifs with hk
    · exact (DifferentialGeometry.Analysis.Sobolev.Tensor.
        exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
          (I := I) (M := M) g 0 2 k hk).choose_spec.1
    · exact le_rfl
  let vol : ℝ :=
    ((riemannianVolumeMeasure (I := I) (M := M) g) Set.univ).toReal
  have hvol : 0 ≤ vol := ENNReal.toReal_nonneg
  let K : ℝ → ℕ → ℝ := fun A k =>
    if k = 0 then vol else
      (∑ n ∈ Finset.range (k + 1),
        ((Finset.Nat.antidiagonalTuple n k).card : ℝ)) *
        ((k : ℝ) * (max (Cpt * A) (max (Cgn k) 1)) ^ (7 * k) * A ^ 2)
  have hK : ∀ A : ℝ, 0 ≤ A → ∀ k : ℕ, 0 ≤ K A k := by
    intro A hA k
    simp only [K]
    split_ifs
    · exact hvol
    · exact mul_nonneg
        (Finset.sum_nonneg (fun n _ => Nat.cast_nonneg _))
        (mul_nonneg
          (mul_nonneg (Nat.cast_nonneg k)
            (pow_nonneg (le_trans zero_le_one
              (le_trans (le_max_right (Cgn k) 1)
                (le_max_right (Cpt * A) _))) _))
          (sq_nonneg A))
  refine ⟨K, hK, ?_⟩
  intro P A hA hPjet k hka
  by_cases hk0 : k = 0
  · subst k
    have hgrid : (fun x => ∑ n ∈ Finset.range (0 + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n 0, ∏ m : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x)) =
        (fun _ : M => (1 : ℝ)) := by
      funext x
      simp only [Nat.zero_add, Finset.sum_range_one,
        Finset.Nat.antidiagonalTuple_zero_zero, Finset.sum_singleton,
        Finset.univ_eq_empty, Finset.prod_empty]
    refine ⟨?_, ?_⟩
    · rw [hgrid]
      exact MeasureTheory.integrable_const 1
    · rw [hgrid, MeasureTheory.integral_const, smul_eq_mul, mul_one,
        MeasureTheory.measureReal_def]
      simp only [K, if_pos rfl, vol]
  · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
    have hrange : Finset.range (Module.finrank ℝ E / 2 + 2) =
        Finset.range 3 := by rw [hDim]
    let Lam : ℝ := Cpt * A
    have hLam : 0 ≤ Lam := mul_nonneg hCpt hA
    have hsub : (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) ≤ A ^ 2 := by
      exact (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.mpr (by omega))
        (fun j _ _ => sq_nonneg _)).trans hPjet
    have hLamSup : ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x (P.toSection x) ≤
          Lam ^ 2 := by
      intro x
      have hx := hpt P x
      rw [hrange] at hx
      calc
        _ ≤ Cpt ^ 2 * (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) := hx
        _ ≤ Cpt ^ 2 * A ^ 2 :=
          mul_le_mul_of_nonneg_left hsub (sq_nonneg Cpt)
        _ = Lam ^ 2 := by simp only [Lam]; ring
    have hsingle : ‖iteratedCovGrad (I := I) g 0 2 k P‖ ^ 2 ≤ A ^ 2 := by
      have hmem : k ∈ Finset.range (a + 1) := Finset.mem_range.mpr (by omega)
      exact (Finset.single_le_sum
        (f := fun j : ℕ => ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2)
        (fun j _ => sq_nonneg _) hmem).trans hPjet
    have htop : ‖iteratedCovGrad (I := I) g 0 2 k P‖ ≤ A := by
      nlinarith [norm_nonneg (iteratedCovGrad (I := I) g 0 2 k P)]
    have hGNspec := (DifferentialGeometry.Analysis.Sobolev.Tensor.
      exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g 0 2 k hk1).choose_spec.2
    have hGNP : ∀ j : ℕ, 0 < j → j < k →
        (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (2 + j) x
                ((iteratedCovGrad (I := I) g 0 2 j P).toSection x)) ^
              ((k : ℝ) / (j : ℝ))
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ^
              ((j : ℝ) / (k : ℝ)) ≤
          Cgn k * Lam ^ (2 * (1 - (j : ℝ) / (k : ℝ))) *
            ‖iteratedCovGrad (I := I) g 0 2 k P‖ ^
              (2 * (j : ℝ) / (k : ℝ)) := by
      intro j hj0 hjk
      have hb := hGNspec P Lam hLam hLamSup j hj0 hjk
      have hchoose : (DifferentialGeometry.Analysis.Sobolev.Tensor.
          exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
            (I := I) (M := M) g 0 2 k hk1).choose = Cgn k := by
        simp only [Cgn, dif_pos hk1]
      rw [hchoose] at hb
      have hnorm : tensorL2Norm (I := I) g 0 (2 + k)
          (iteratedCovGrad (I := I) g 0 2 k P).toFun =
          ‖iteratedCovGrad (I := I) g 0 2 k P‖ :=
        (SmoothCcTensor.norm_def
          (iteratedCovGrad (I := I) g 0 2 k P)).symm
      rw [hnorm] at hb
      exact hb
    let G : ℝ :=
      (k : ℝ) * (max Lam (max (Cgn k) 1)) ^ (7 * k) * A ^ 2
    have hterm : ∀ n ∈ Finset.range (k + 1),
        ∀ e ∈ Finset.Nat.antidiagonalTuple n k,
          MeasureTheory.Integrable
              (fun x => ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x))
              (riemannianVolumeMeasure (I := I) (M := M) g) ∧
            (∫ x, ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤ G := by
      intro n hn e he
      have hn_le : n ≤ k := by
        have := Finset.mem_range.mp hn
        omega
      have hsum : ∑ m, e m = k := Finset.Nat.mem_antidiagonalTuple.mp he
      have hres := grid_prod_int_le (I := I) (M := M) g P hA k hk1
        hLam hLamSup htop (hCgn k) hGNP n hn_le e hsum
      refine ⟨hres.1, hres.2.trans ?_⟩
      simp only [G]
    have hint : MeasureTheory.Integrable
        (fun x => ∑ n ∈ Finset.range (k + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
            ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g) := by
      apply MeasureTheory.integrable_finset_sum
      intro n hn
      apply MeasureTheory.integrable_finset_sum
      intro e he
      exact (hterm n hn e he).1
    refine ⟨hint, ?_⟩
    rw [MeasureTheory.integral_finset_sum _
      (fun n hn => MeasureTheory.integrable_finset_sum _
        (fun e he => (hterm n hn e he).1))]
    have hinner : ∀ n ∈ Finset.range (k + 1),
        (∫ x, ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
            ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
        ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
          ∫ x, ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
      intro n hn
      exact MeasureTheory.integral_finset_sum _ (fun e he => (hterm n hn e he).1)
    rw [Finset.sum_congr rfl hinner]
    calc
      ∑ n ∈ Finset.range (k + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
            ∫ x, ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g)
          ≤ ∑ n ∈ Finset.range (k + 1),
              ∑ _e ∈ Finset.Nat.antidiagonalTuple n k, G := by
            apply Finset.sum_le_sum
            intro n hn
            apply Finset.sum_le_sum
            intro e he
            exact (hterm n hn e he).2
      _ = (∑ n ∈ Finset.range (k + 1),
            ((Finset.Nat.antidiagonalTuple n k).card : ℝ)) * G := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro n _
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = K A k := by
          simp only [K, if_neg hk0, G, Lam]

/-- The intrinsic `H2` algebra form of `low_grid_int`. -/
theorem h2_grid_int
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℝ → ℕ → ℝ,
      (∀ A : ℝ, 0 ≤ A → ∀ k : ℕ, 0 ≤ K A k) ∧
      ∀ (P : SmoothCcTensor g 0 2) (A : ℝ), 0 ≤ A →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) ≤ A ^ 2 →
        ∀ k : ℕ, k ≤ 2 →
          MeasureTheory.Integrable
              (fun x => ∑ n ∈ Finset.range (k + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                  ∏ m : Fin n,
                    riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x))
              (riemannianVolumeMeasure (I := I) (M := M) g) ∧
            (∫ x, ∑ n ∈ Finset.range (k + 1),
                  ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                    ∏ m : Fin n,
                      riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
                        ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤ K A k := by
  simpa only [Nat.reduceAdd] using
    low_grid_int (I := I) (M := M) hDim g 2 (by omega)

/-- The total-order-three antidiagonal grid is linear in the top `H3` jet
once the lower `H2` jet is fixed.  More precisely, its integral is bounded
by `K R * A ^ 2`, where `R` controls the jets through order two and `A`
controls only the third derivative.  This is the tame endpoint that is lost
if the lower pointwise bound is formed from the full `H3` norm. -/
theorem h3_top_grid_int
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ K R) ∧
      ∀ (P : SmoothCcTensor g 0 2) (R A : ℝ), 0 ≤ R → 0 ≤ A →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) ≤ R ^ 2 →
        ‖iteratedCovGrad (I := I) g 0 2 3 P‖ ≤ A →
        MeasureTheory.Integrable
            (fun x => ∑ n ∈ Finset.range 4,
              ∑ e ∈ Finset.Nat.antidiagonalTuple n 3,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g) ∧
          (∫ x, ∑ n ∈ Finset.range 4,
                ∑ e ∈ Finset.Nat.antidiagonalTuple n 3,
                  ∏ m : Fin n,
                    riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤ K R * A ^ 2 := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  obtain ⟨Cpt, hCpt, hpt⟩ :=
    DifferentialGeometry.PDE.RicciFlow.
      exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
        (I := I) (M := M) g 0 2
  obtain ⟨Cgn, hCgn, hGNspec⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Tensor.
      exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g 0 2 3 (by omega)
  let count : ℝ := ∑ n ∈ Finset.range 4,
    ((Finset.Nat.antidiagonalTuple n 3).card : ℝ)
  let K : ℝ → ℝ := fun R =>
    count * ((3 : ℝ) * (max (Cpt * R) (max Cgn 1)) ^ 21)
  have hcount : 0 ≤ count := by
    exact Finset.sum_nonneg fun n _ => Nat.cast_nonneg _
  have hK : ∀ R : ℝ, 0 ≤ R → 0 ≤ K R := by
    intro R hR
    exact mul_nonneg hcount (mul_nonneg (by norm_num)
      (pow_nonneg (le_trans zero_le_one
        (le_trans (le_max_right Cgn 1) (le_max_right (Cpt * R) _))) _))
  refine ⟨K, hK, ?_⟩
  intro P R A hR hA hP2 htop
  have hrange : Finset.range (Module.finrank ℝ E / 2 + 2) =
      Finset.range 3 := by rw [hDim]
  let Lam : ℝ := Cpt * R
  have hLam : 0 ≤ Lam := mul_nonneg hCpt hR
  have hLamSup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x (P.toSection x) ≤
        Lam ^ 2 := by
    intro x
    have hx := hpt P x
    rw [hrange] at hx
    calc
      _ ≤ Cpt ^ 2 * (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) := hx
      _ ≤ Cpt ^ 2 * R ^ 2 :=
        mul_le_mul_of_nonneg_left hP2 (sq_nonneg Cpt)
      _ = Lam ^ 2 := by simp only [Lam]; ring
  have hGNP : ∀ j : ℕ, 0 < j → j < 3 →
      (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (2 + j) x
              ((iteratedCovGrad (I := I) g 0 2 j P).toSection x)) ^
            ((3 : ℝ) / (j : ℝ))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ^
            ((j : ℝ) / (3 : ℝ)) ≤
        Cgn * Lam ^ (2 * (1 - (j : ℝ) / (3 : ℝ))) *
          A ^ (2 * (j : ℝ) / (3 : ℝ)) := by
    intro j hj0 hj3
    have hb := hGNspec P Lam hLam hLamSup j hj0 hj3
    have hnorm : tensorL2Norm (I := I) g 0 5
        (iteratedCovGrad (I := I) g 0 2 3 P).toFun =
        ‖iteratedCovGrad (I := I) g 0 2 3 P‖ :=
      (SmoothCcTensor.norm_def
        (iteratedCovGrad (I := I) g 0 2 3 P)).symm
    rw [hnorm] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) htop (by positivity))
      (mul_nonneg hCgn (Real.rpow_nonneg hLam _)))
  let G : ℝ :=
    (3 : ℝ) * (max Lam (max Cgn 1)) ^ 21 * A ^ 2
  have hterm : ∀ n ∈ Finset.range 4,
      ∀ e ∈ Finset.Nat.antidiagonalTuple n 3,
        MeasureTheory.Integrable
            (fun x => ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g) ∧
          (∫ x, ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤ G := by
    intro n hn e he
    have hn_le : n ≤ 3 := by
      have := Finset.mem_range.mp hn
      omega
    have hsum : ∑ m, e m = 3 := Finset.Nat.mem_antidiagonalTuple.mp he
    have hres := grid_prod_int_le (I := I) (M := M) g P hA 3 (by omega)
      hLam hLamSup htop hCgn hGNP n hn_le e hsum
    simpa only [G, Nat.cast_ofNat, Nat.reduceMul] using hres
  have hint : MeasureTheory.Integrable
      (fun x => ∑ n ∈ Finset.range 4,
        ∑ e ∈ Finset.Nat.antidiagonalTuple n 3,
          ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    apply MeasureTheory.integrable_finset_sum
    intro n hn
    apply MeasureTheory.integrable_finset_sum
    intro e he
    exact (hterm n hn e he).1
  refine ⟨hint, ?_⟩
  rw [MeasureTheory.integral_finset_sum _
    (fun n hn => MeasureTheory.integrable_finset_sum _
      (fun e he => (hterm n hn e he).1))]
  have hinner : ∀ n ∈ Finset.range 4,
      (∫ x, ∑ e ∈ Finset.Nat.antidiagonalTuple n 3,
          ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∑ e ∈ Finset.Nat.antidiagonalTuple n 3,
        ∫ x, ∏ m : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    intro n hn
    exact MeasureTheory.integral_finset_sum _ (fun e he => (hterm n hn e he).1)
  rw [Finset.sum_congr rfl hinner]
  calc
    ∑ n ∈ Finset.range 4,
        ∑ e ∈ Finset.Nat.antidiagonalTuple n 3,
          ∫ x, ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)
        ≤ ∑ n ∈ Finset.range 4,
            ∑ _e ∈ Finset.Nat.antidiagonalTuple n 3, G := by
          apply Finset.sum_le_sum
          intro n hn
          apply Finset.sum_le_sum
          intro e he
          exact (hterm n hn e he).2
    _ = count * G := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro n _
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = K R * A ^ 2 := by
        simp only [count, G, K, Lam]
        ring

/-- The intrinsic `H3` specialization used by coefficient fields whose first
jet still contains a metric two-jet. -/
theorem h3_grid_int
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℝ → ℕ → ℝ,
      (∀ A : ℝ, 0 ≤ A → ∀ k : ℕ, 0 ≤ K A k) ∧
      ∀ (P : SmoothCcTensor g 0 2) (A : ℝ), 0 ≤ A →
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) ≤ A ^ 2 →
        ∀ k : ℕ, k ≤ 3 →
          MeasureTheory.Integrable
              (fun x => ∑ n ∈ Finset.range (k + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                  ∏ m : Fin n,
                    riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x))
              (riemannianVolumeMeasure (I := I) (M := M) g) ∧
            (∫ x, ∑ n ∈ Finset.range (k + 1),
                  ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                    ∏ m : Fin n,
                      riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
                        ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤ K A k := by
  simpa only [Nat.reduceAdd] using
    low_grid_int (I := I) (M := M) hDim g 3 (by omega)

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
