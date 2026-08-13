import DifferentialGeometry.Analysis.Heat.Semigroup.SpectralBounds
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Defs
import Mathlib.Data.Nat.Choose.Sum

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace HeatEquation

private lemma one_add_pow_mul_resolvent_pow_cancel
    (r lam x : ℝ) (k : ℕ) (h : r * (1 + lam) = 1) :
    (1 + lam) ^ k * x * r ^ k = x := by
  have hpow : (1 + lam) ^ k * r ^ k = 1 := by
    rw [← mul_pow, mul_comm, h, one_pow]
  calc
    (1 + lam) ^ k * x * r ^ k = ((1 + lam) ^ k * r ^ k) * x := by ring
    _ = x := by rw [hpow, one_mul]

private theorem map_eq_of_hilbertBasis_diagonal
    {ι X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (b : HilbertBasis ι ℝ X) (T : X →L[ℝ] X) (d : ι → ℝ) (u v : X)
    (hbasis : ∀ i, T (b i) = d i • b i)
    (hcoeff : ∀ i, (b.repr v) i * d i = (b.repr u) i) :
    T v = u := by
  have hmap : HasSum (fun i => (b.repr v) i • T (b i)) (T v) := by
    simpa only [map_smul] using (b.hasSum_repr v).mapL T
  have hsummand : (fun i => (b.repr v) i • T (b i)) =
      fun i => (b.repr u) i • b i := by
    funext i
    rw [hbasis i, smul_smul, hcoeff i]
  rw [hsummand] at hmap
  exact HasSum.unique hmap (b.hasSum_repr u)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

omit [NeZero (Module.finrank ℝ E)] in
theorem resolventEigenvalue_mul_one_add_laplacianEigenvalue
    (g : SmoothRiemannianMetric I M) (i : EigenIdx (I := I) (M := M) g) :
    i.1.val * (1 + EigenIdx.lambda (I := I) (M := M) i) = 1 := by
  unfold EigenIdx.lambda laplacianEigenvalueOf
  have h_pos : 0 < i.1.val := nonzeroResolventEigenvalue_pos i.1
  have h_ne : i.1.val ≠ 0 := h_pos.ne'
  field_simp
  linarith

theorem iteratedResolventL2_apply_basis
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    (i : EigenIdx (I := I) (M := M) g) :
    iteratedResolventL2 (I := I) (M := M) g k
        (resolventHilbertEigenbasisSigma (I := I) (M := M) g i) =
      (i.1.val ^ k) •
        resolventHilbertEigenbasisSigma (I := I) (M := M) g i := by
  induction k with
  | zero =>
    rw [iteratedResolventL2_zero]
    rw [pow_zero, one_smul]
    rfl
  | succ k ih =>
    rw [iteratedResolventL2_succ]
    rw [ContinuousLinearMap.comp_apply]
    rw [ih]
    rw [(resolventL2 (I := I) (M := M) g).map_smul]
    have h_basis :
        resolventL2 (I := I) (M := M) g
          (resolventHilbertEigenbasisSigma (I := I) (M := M) g i) =
        i.1.val •
          resolventHilbertEigenbasisSigma (I := I) (M := M) g i := by
      have h_eq : resolventEigenbasisSigma (I := I) (M := M) g i =
          resolventHilbertEigenbasisSigma (I := I) (M := M) g i :=
        (resolventEigenbasisSigma_eq_resolventEigenbasisVec (I := I) (M := M) g i).trans
          (resolventHilbertEigenbasisSigma_apply (I := I) (M := M) g i).symm
      have h := resolventL2_apply_resolventEigenbasisSigma (I := I) (M := M) g i
      rw [h_eq] at h
      exact h
    rw [h_basis]
    rw [smul_smul]
    rw [show i.1.val ^ k * i.1.val = i.1.val ^ (k + 1) from by ring]

theorem exists_iteratedResolventL2_preimage_of_weighted_coeff_summable
    (g : SmoothRiemannianMetric I M)
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (k : ℕ)
    (hsum : Summable (fun i : EigenIdx (I := I) (M := M) g =>
      (1 + EigenIdx.lambda (I := I) (M := M) i) ^ (2 * k) *
        ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i, u⟫_ℝ ^ 2)) :
    ∃ v : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g),
      iteratedResolventL2 (I := I) (M := M) g k v = u := by
  classical
  set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g
  let c : EigenIdx (I := I) (M := M) g → ℝ := fun i =>
    (1 + EigenIdx.lambda (I := I) (M := M) i) ^ k * (b.repr u) i
  have hc_sq : Summable (fun i => (c i) ^ 2) := by
    have heq : (fun i => (c i) ^ 2) = fun i =>
        (1 + EigenIdx.lambda (I := I) (M := M) i) ^ (2 * k) *
          ⟪b i, u⟫_ℝ ^ 2 := by
      funext i
      simp only [c]
      rw [b.repr_apply_apply, mul_pow]
      rw [← pow_mul]
      congr 2
      omega
    rw [heq]
    exact hsum
  have hc_mem : Memℓp c 2 := by
    apply memℓp_gen
    have hpr : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    have heq : (fun i => ‖c i‖ ^ (2 : ℝ≥0∞).toReal) =
        fun i => (c i) ^ 2 := by
      funext i
      rw [hpr, Real.norm_eq_abs, ← sq_abs]
      norm_num
    rw [heq]
    exact hc_sq
  let v : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
    b.repr.symm ⟨c, hc_mem⟩
  have hv_coeff : ∀ i, (b.repr v) i = c i := by
    intro i
    rw [show b.repr v = ⟨c, hc_mem⟩ from LinearIsometryEquiv.apply_symm_apply _ _]
  refine ⟨v, map_eq_of_hilbertBasis_diagonal b
    (iteratedResolventL2 (I := I) (M := M) g k) (fun i => i.1.val ^ k) u v
    (iteratedResolventL2_apply_basis (I := I) (M := M) g k) ?_⟩
  intro i
  rw [hv_coeff i]
  exact one_add_pow_mul_resolvent_pow_cancel i.1.val
    (EigenIdx.lambda (I := I) (M := M) i) ((b.repr u) i) k
    (resolventEigenvalue_mul_one_add_laplacianEigenvalue (I := I) (M := M) g i)

theorem exists_laplacianDomainPow_succ_lift_of_weighted_coeff_summable
    (g : SmoothRiemannianMetric I M)
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (k : ℕ)
    (hsum : Summable (fun i : EigenIdx (I := I) (M := M) g =>
      (1 + EigenIdx.lambda (I := I) (M := M) i) ^ (2 * (k + 1)) *
        ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i, u⟫_ℝ ^ 2)) :
    ∃ u_h : H1Compl (I := I) (M := M) g,
      u_h ∈ laplacianDomainPow (I := I) (M := M) g (k + 1) ∧
        H1ComplToLp (I := I) (M := M) g u_h = u := by
  obtain ⟨v, hv⟩ := exists_iteratedResolventL2_preimage_of_weighted_coeff_summable
    (I := I) (M := M) g u (k + 1) hsum
  refine ⟨resolvent (I := I) (M := M) g
      (iteratedResolventL2 (I := I) (M := M) g k v), ?_, ?_⟩
  · rw [laplacianDomainPow_succ_mem_iff]
    exact ⟨v, rfl⟩
  · rw [← resolventL2_apply]
    rw [← iteratedResolventL2_succ_apply]
    exact hv

noncomputable def oneMinusLapHeat (g : SmoothRiemannianMetric I M) (k : ℕ)
    (t : ℝ) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  ∑ j ∈ Finset.range (k + 1),
    (k.choose j : ℝ) • heatPower (I := I) (M := M) g j t

lemma oneMinusLapHeat_apply (g : SmoothRiemannianMetric I M) (k : ℕ) (t : ℝ)
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    oneMinusLapHeat (I := I) (M := M) g k t u =
      ∑ j ∈ Finset.range (k + 1),
        (k.choose j : ℝ) • heatPower (I := I) (M := M) g j t u := by
  unfold oneMinusLapHeat
  rw [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [ContinuousLinearMap.smul_apply]

private lemma oneMinusLapHeat_apply_basis
    (g : SmoothRiemannianMetric I M) (k : ℕ) {t : ℝ} (ht : 0 < t)
    (i : EigenIdx (I := I) (M := M) g) :
    oneMinusLapHeat (I := I) (M := M) g k t
        (resolventHilbertEigenbasisSigma (I := I) (M := M) g i) =
      ((1 + EigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) •
        resolventHilbertEigenbasisSigma (I := I) (M := M) g i := by
  set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g
  set lam := EigenIdx.lambda (I := I) (M := M) i with hlam_def
  rw [oneMinusLapHeat_apply]
  have h_term_eq : ∀ j ∈ Finset.range (k + 1),
      (k.choose j : ℝ) • heatPower (I := I) (M := M) g j t (b i) =
      ((k.choose j : ℝ) * lam ^ j * Real.exp (-lam * t)) • b i := by
    intro j _
    have h_basis : heatPower (I := I) (M := M) g j t (b i) =
        (lam ^ j * Real.exp (-lam * t)) • b i :=
      heatPower_apply_basis_pos (I := I) (M := M) g j ht i
    rw [h_basis]
    rw [smul_smul]
    rw [show (k.choose j : ℝ) * (lam ^ j * Real.exp (-lam * t)) =
      (k.choose j : ℝ) * lam ^ j * Real.exp (-lam * t) from by ring]
  rw [Finset.sum_congr rfl h_term_eq]
  rw [← Finset.sum_smul]
  congr 1
  have h_binom : ∑ j ∈ Finset.range (k + 1),
      (k.choose j : ℝ) * lam ^ j * Real.exp (-lam * t) =
      (1 + lam) ^ k * Real.exp (-lam * t) := by
    rw [← Finset.sum_mul]
    congr 1
    have h_pow := add_pow (lam : ℝ) 1 k
    rw [show ((1 : ℝ) + lam) ^ k = (lam + 1) ^ k from by rw [add_comm]]
    rw [h_pow]
    apply Finset.sum_congr rfl
    intro j _
    rw [one_pow, mul_one, mul_comm]
  rw [h_binom]

private lemma iteratedResolventL2_oneMinusLapHeat_basis
    (g : SmoothRiemannianMetric I M) (k : ℕ) {t : ℝ} (ht : 0 < t)
    (i : EigenIdx (I := I) (M := M) g) :
    iteratedResolventL2 (I := I) (M := M) g k
        (oneMinusLapHeat (I := I) (M := M) g k t
          (resolventHilbertEigenbasisSigma (I := I) (M := M) g i)) =
      heatSemigroup (I := I) (M := M) g t
        (resolventHilbertEigenbasisSigma (I := I) (M := M) g i) := by
  set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g
  set lam := EigenIdx.lambda (I := I) (M := M) i
  rw [oneMinusLapHeat_apply_basis (I := I) (M := M) g k ht i]
  rw [(iteratedResolventL2 (I := I) (M := M) g k).map_smul]
  rw [iteratedResolventL2_apply_basis (I := I) (M := M) g k i]
  rw [smul_smul]
  have h_inv : i.1.val * (1 + lam) = 1 :=
    resolventEigenvalue_mul_one_add_laplacianEigenvalue (I := I) (M := M) g i
  have h_pow_inv : i.1.val ^ k * (1 + lam) ^ k = 1 := by
    rw [← mul_pow, h_inv, one_pow]
  have h_pow_inv' : (1 + lam) ^ k * i.1.val ^ k = 1 := by
    rw [mul_comm]; exact h_pow_inv
  have h_scalar :
      (1 + lam) ^ k * Real.exp (-lam * t) * i.1.val ^ k =
      Real.exp (-lam * t) := by
    rw [show (1 + lam) ^ k * Real.exp (-lam * t) * i.1.val ^ k =
        ((1 + lam) ^ k * i.1.val ^ k) * Real.exp (-lam * t) from by ring]
    rw [h_pow_inv', one_mul]
  rw [h_scalar]
  have h_rhs := heatSemigroup_apply_basis (I := I) (M := M) g ht.le i
  have h_eq_basis : resolventEigenbasisSigma (I := I) (M := M) g i = b i := by
    change resolventEigenbasisSigma (I := I) (M := M) g i =
      resolventHilbertEigenbasisSigma (I := I) (M := M) g i
    rw [resolventEigenbasisSigma_eq_resolventEigenbasisVec]
    rw [resolventHilbertEigenbasisSigma_apply]
  rw [h_eq_basis] at h_rhs
  exact h_rhs.symm


private lemma hasSum_repr_smul_mapL {ι : Type*} {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (b : HilbertBasis ι ℝ X) (u : X) (T : X →L[ℝ] Y) :
    HasSum (fun i => b.repr u i • T (b i)) (T u) := by
  have h := (b.hasSum_repr u).mapL T
  have heq : (fun i => T (b.repr u i • b i)) = fun i => b.repr u i • T (b i) := by
    funext i
    exact T.map_smul _ _
  rwa [heq] at h

theorem iteratedResolventL2_oneMinusLapHeat_apply
    (g : SmoothRiemannianMetric I M) (k : ℕ) {t : ℝ} (ht : 0 < t)
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    iteratedResolventL2 (I := I) (M := M) g k
        (oneMinusLapHeat (I := I) (M := M) g k t u) =
      heatSemigroup (I := I) (M := M) g t u := by
  set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g with hb_def
  have h_hsum : HasSum (fun i => b.repr u i • b i) u := b.hasSum_repr u
  let A := iteratedResolventL2 (I := I) (M := M) g k
  let B := oneMinusLapHeat (I := I) (M := M) g k t
  let H := heatSemigroup (I := I) (M := M) g t
  have h_LHS_hsum : HasSum
      (fun i => b.repr u i • A (B (b i)))
      (A (B u)) := hasSum_repr_smul_mapL b u (A.comp B)
  have h_RHS_hsum : HasSum
      (fun i => b.repr u i • H (b i))
      (H u) := hasSum_repr_smul_mapL b u H
  have h_summand_eq :
      (fun i => b.repr u i • A (B (b i))) =
      (fun i => b.repr u i • H (b i)) := by
    funext i
    change b.repr u i • iteratedResolventL2 (I := I) (M := M) g k
        (oneMinusLapHeat (I := I) (M := M) g k t (b i)) =
      b.repr u i • heatSemigroup (I := I) (M := M) g t (b i)
    rw [iteratedResolventL2_oneMinusLapHeat_basis (I := I) (M := M) g k ht i]
  rw [h_summand_eq] at h_LHS_hsum
  change A (B u) = H u
  exact HasSum.unique h_LHS_hsum h_RHS_hsum

theorem heatSemigroup_mem_laplacianDomainPow_all
    (g : SmoothRiemannianMetric I M)
    {t : ℝ} (ht : 0 < t)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ∀ k : ℕ, ∃ u_h : H1Compl (I := I) (M := M) g,
      u_h ∈ laplacianDomainPow (I := I) (M := M) g k ∧
        H1ComplToLp (I := I) (M := M) g u_h =
          heatSemigroup (I := I) (M := M) g t u_0 := by
  intro k
  rcases Nat.eq_zero_or_pos k with hk0 | hk_pos
  · subst hk0
    refine ⟨resolvent (I := I) (M := M) g
      (oneMinusLapHeat (I := I) (M := M) g 1 t u_0), ?_, ?_⟩
    · rw [laplacianDomainPow_zero]
      exact Submodule.mem_top
    · rw [show H1ComplToLp (I := I) (M := M) g
            (resolvent (I := I) (M := M) g
              (oneMinusLapHeat (I := I) (M := M) g 1 t u_0)) =
          resolventL2 (I := I) (M := M) g
            (oneMinusLapHeat (I := I) (M := M) g 1 t u_0) from
        (resolventL2_apply (I := I) (M := M) g _).symm]
      rw [show resolventL2 (I := I) (M := M) g
            (oneMinusLapHeat (I := I) (M := M) g 1 t u_0) =
          iteratedResolventL2 (I := I) (M := M) g 1
            (oneMinusLapHeat (I := I) (M := M) g 1 t u_0) from ?_]
      · exact iteratedResolventL2_oneMinusLapHeat_apply (I := I) (M := M) g 1 ht u_0
      · rw [iteratedResolventL2_one]
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    refine ⟨resolvent (I := I) (M := M) g
      (iteratedResolventL2 (I := I) (M := M) g k'
        (oneMinusLapHeat (I := I) (M := M) g (k' + 1) t u_0)), ?_, ?_⟩
    · rw [laplacianDomainPow_succ_mem_iff]
      exact ⟨oneMinusLapHeat (I := I) (M := M) g (k' + 1) t u_0, rfl⟩
    · have h_step1 : H1ComplToLp (I := I) (M := M) g
            (resolvent (I := I) (M := M) g
              (iteratedResolventL2 (I := I) (M := M) g k'
                (oneMinusLapHeat (I := I) (M := M) g (k' + 1) t u_0))) =
          resolventL2 (I := I) (M := M) g
            (iteratedResolventL2 (I := I) (M := M) g k'
              (oneMinusLapHeat (I := I) (M := M) g (k' + 1) t u_0)) :=
        (resolventL2_apply (I := I) (M := M) g _).symm
      rw [h_step1]
      rw [show resolventL2 (I := I) (M := M) g
            (iteratedResolventL2 (I := I) (M := M) g k'
              (oneMinusLapHeat (I := I) (M := M) g (k' + 1) t u_0)) =
          iteratedResolventL2 (I := I) (M := M) g (k' + 1)
            (oneMinusLapHeat (I := I) (M := M) g (k' + 1) t u_0) from
        (iteratedResolventL2_succ_apply (I := I) (M := M) g k' _).symm]
      exact iteratedResolventL2_oneMinusLapHeat_apply (I := I) (M := M) g (k' + 1) ht u_0

end HeatEquation
end Analysis
end DifferentialGeometry

end
