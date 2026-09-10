import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessTransport
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.CheegerGromovCompactness

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

noncomputable section

universe u uE uH

open Bundle DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology



def scalarComparisonC (n : ℕ) (eps Kb : ℝ) : ℝ :=
  (n : ℝ) ^ 2 * witnessLambda eps * witnessRiemannC eps +
    (n : ℝ) * (witnessLambda eps - 1) * Kb

theorem witnessLambda_sub_one_le {eps : ℝ} (h0 : 0 ≤ eps) (h1 : eps ≤ 1 / 2) :
    witnessLambda eps - 1 ≤ 2 * eps := by
  have hpos : (0 : ℝ) < 1 - eps := by linarith
  have hid : witnessLambda eps * (1 - eps) = 1 := by
    rw [witnessLambda]
    field_simp
  have hle : witnessLambda eps ≤ 2 := by
    rw [witnessLambda, inv_le_comm₀ hpos (by norm_num)]
    linarith
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 - witnessLambda eps) h0]

theorem scalarComparisonC_nonneg {n : ℕ} {eps Kb : ℝ} (h0 : 0 ≤ eps) (h1 : eps < 1)
    (hKb : 0 ≤ Kb) : 0 ≤ scalarComparisonC n eps Kb := by
  have hL1 : (1 : ℝ) ≤ witnessLambda eps := one_le_witnessLambda h0 h1
  have hC0 : 0 ≤ witnessRiemannC eps := witnessRiemannC_nonneg h0 h1
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  unfold scalarComparisonC
  have t1 : 0 ≤ (n : ℝ) ^ 2 * witnessLambda eps * witnessRiemannC eps := by positivity
  have t2 : 0 ≤ (n : ℝ) * (witnessLambda eps - 1) * Kb := by
    have : (0 : ℝ) ≤ witnessLambda eps - 1 := by linarith
    positivity
  linarith

theorem scalarComparisonC_le {n : ℕ} {eps Kb : ℝ} (h0 : 0 ≤ eps) (h1 : eps ≤ 1 / 4)
    (hKb : 0 ≤ Kb) :
    scalarComparisonC n eps Kb ≤ 27 * (n : ℝ) ^ 2 * (eps + eps * Kb) := by
  have hL1 : (1 : ℝ) ≤ witnessLambda eps := one_le_witnessLambda h0 (by linarith)
  have hL : witnessLambda eps ≤ 4 / 3 := witnessLambda_le h1
  have hC0 : 0 ≤ witnessRiemannC eps := witnessRiemannC_nonneg h0 (by linarith)
  have hC : witnessRiemannC eps ≤ 20 * eps := witnessRiemannC_le h0 h1
  have hLm : witnessLambda eps - 1 ≤ 2 * eps := witnessLambda_sub_one_le h0 (by linarith)
  have hprod1 : witnessLambda eps * witnessRiemannC eps ≤ 80 / 3 * eps := by nlinarith
  have hprod2 : (witnessLambda eps - 1) * Kb ≤ 2 * eps * Kb := by nlinarith
  have e1 : (n : ℝ) ^ 2 * witnessLambda eps * witnessRiemannC eps ≤
      (n : ℝ) ^ 2 * (80 / 3 * eps) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hprod1 (sq_nonneg _)
  have e2 : (n : ℝ) * (witnessLambda eps - 1) * Kb ≤ (n : ℝ) * (2 * eps * Kb) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hprod2 (Nat.cast_nonneg n)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · unfold scalarComparisonC
    norm_num
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hsq : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
    have hnn : (0 : ℝ) ≤ eps * Kb := mul_nonneg h0 hKb
    have hcoef : 2 * (n : ℝ) ≤ 27 * (n : ℝ) ^ 2 := by nlinarith
    have g1 : (n : ℝ) ^ 2 * (80 / 3 * eps) ≤ 27 * (n : ℝ) ^ 2 * eps := by nlinarith
    have g2 : (n : ℝ) * (2 * eps * Kb) ≤ 27 * (n : ℝ) ^ 2 * (eps * Kb) := by
      calc (n : ℝ) * (2 * eps * Kb) = 2 * (n : ℝ) * (eps * Kb) := by ring
        _ ≤ 27 * (n : ℝ) ^ 2 * (eps * Kb) := mul_le_mul_of_nonneg_right hcoef hnn
    unfold scalarComparisonC
    linarith [e1, e2, g1, g2]

theorem scalarComparisonC_tendsto (n : ℕ) (Kb : ℝ) :
    Filter.Tendsto (fun e : ℝ => scalarComparisonC n e Kb)
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds 0) := by
  have hcont : ContinuousAt (fun e : ℝ => scalarComparisonC n e Kb) 0 := by
    unfold scalarComparisonC witnessRiemannC riemannDiffC witnessLambda
    fun_prop (disch := norm_num)
  have hval : scalarComparisonC n 0 Kb = 0 := by
    unfold scalarComparisonC witnessRiemannC riemannDiffC witnessLambda
    norm_num
  have hten := hcont.tendsto
  rw [hval] at hten
  exact hten.mono_left nhdsWithin_le_nhds

section General

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M' : Type u} [TopologicalSpace M'] [ChartedSpace H M'] [IsManifold I ∞ M']
variable [T2Space M'] [BoundarylessManifold I M']

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E



private theorem sum_diagonalInvMetric_mul {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (μ : Idx → ℝ) (i : Idx) (F : Idx → ℝ) :
    (∑ k : Idx, diagonalInvMetric μ i k * F k) = μ i * F i := by
  classical
  rw [Finset.sum_eq_single i]
  · rw [diagonalInvMetric_apply_self]
  · intro j _ hj
    rw [diagonalInvMetric_eq_zero_of_ne (fun hh => hj hh.symm), zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem metricScalarAt_eq_sum_ricciTensor
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M') {z : M'}
    (basis : Module.Basis Idx ℝ (TangentSpace I z))
    (gInv : Idx → Idx → ℝ)
    (hinv : MetricInverseInBasis (I := I) g z basis gInv) :
    metricScalarAt (I := I) g z =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * ricciTensor (I := I) g z (basis i) (basis j) := by
  rw [metricScalarAt_def,
    metricTracePair0SAt_eq_sum_basis (I := I) g basis gInv hinv
      (metricRicciAt (I := I) g z)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [metricRicciAt_apply_eq_ricciTensor (I := I) g z (basis i) (basis j)]

theorem metricScalarAt_eq_sum_ricciTensor_diagonal
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M') {z : M'}
    (basis : Module.Basis Idx ℝ (TangentSpace I z)) (μ : Idx → ℝ)
    (hinv : MetricInverseInBasis (I := I) g z basis (diagonalInvMetric μ)) :
    metricScalarAt (I := I) g z =
      ∑ i : Idx, μ i * ricciTensor (I := I) g z (basis i) (basis i) := by
  classical
  rw [metricScalarAt_eq_sum_ricciTensor (I := I) g basis (diagonalInvMetric μ) hinv]
  exact Finset.sum_congr rfl fun i _ =>
    sum_diagonalInvMetric_mul μ i (fun j => ricciTensor (I := I) g z (basis i) (basis j))


theorem metricScalarAt_eq_sum_ricciTensor_orthonormal
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M') {z : M'}
    (basis : Module.Basis Idx ℝ (TangentSpace I z))
    (hON : ∀ i j : Idx, g.inner z (basis i) (basis j) = if i = j then (1 : ℝ) else 0) :
    metricScalarAt (I := I) g z =
      ∑ i : Idx, ricciTensor (I := I) g z (basis i) (basis i) := by
  classical
  have hinv : MetricInverseInBasis (I := I) g z basis
      (diagonalInvMetric (fun _ : Idx => (1 : ℝ))) :=
    metricInverseInBasis_of_orthonormal (I := I) g basis hON
  rw [metricScalarAt_eq_sum_ricciTensor_diagonal (I := I) g basis
    (fun _ : Idx => (1 : ℝ)) hinv]
  exact Finset.sum_congr rfl fun i _ => one_mul _



private theorem sqrt_le_of_sq_bound {A F a b c : ℝ} (hF : 0 ≤ F)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hA : A ≤ F ^ 2 * a * b * c) :
    Real.sqrt A ≤ F * Real.sqrt a * Real.sqrt b * Real.sqrt c := by
  have hprod : F ^ 2 * a * b * c = (F * Real.sqrt a * Real.sqrt b * Real.sqrt c) ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sq_sqrt hc]
  calc Real.sqrt A ≤ Real.sqrt ((F * Real.sqrt a * Real.sqrt b * Real.sqrt c) ^ 2) := by
        rw [← hprod]
        exact Real.sqrt_le_sqrt hA
    _ = F * Real.sqrt a * Real.sqrt b * Real.sqrt c := Real.sqrt_sq (by positivity)

omit [T2Space M'] [BoundarylessManifold I M'] in
private theorem exists_orthoFrame_finrank (g : SmoothRiemannianMetric I M') (z : M') :
    ∃ B : Fin (Module.finrank ℝ E) → TangentSpace I z,
      ∀ i j : Fin (Module.finrank ℝ E),
        g.inner z (B i) (B j) = if i = j then (1 : ℝ) else 0 := by
  classical
  obtain ⟨b0, hb0⟩ := exists_orthonormal_basis (I := I) g z
  have hdim : Module.finrank ℝ E = Module.finrank ℝ (TangentSpace I z) := rfl
  refine ⟨fun i => b0 (Fin.cast hdim i), fun i j => ?_⟩
  by_cases hij : i = j
  · subst hij
    simpa only [if_pos rfl] using hb0 (Fin.cast hdim i) (Fin.cast hdim i)
  · have hcast : Fin.cast hdim i ≠ Fin.cast hdim j := by
      intro hh
      apply hij
      apply Fin.ext
      exact congrArg Fin.val hh
    simpa only [if_neg hij, if_neg hcast] using hb0 (Fin.cast hdim i) (Fin.cast hdim j)

private theorem riemannDiffC_nonneg {Λ Λ' Λ'' : ℝ} (hL : 0 ≤ Λ)
    (hL'' : 0 ≤ Λ'') : 0 ≤ riemannDiffC Λ Λ' Λ'' := by
  have hX : 0 ≤ Λ'' + Λ * Λ' ^ 2 := add_nonneg hL'' (mul_nonneg hL (sq_nonneg Λ'))
  have h4 : (0 : ℝ) ≤ Λ ^ 4 := pow_nonneg hL 4
  unfold riemannDiffC
  nlinarith [sq_nonneg (3 / 2 * Λ ^ 3 * Λ'),
    mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2) h4) hX]

theorem ricciTensor_sub_le_of_jetBounds
    {K : Set M'} (g₂ g₁ : SmoothRiemannianMetric I M') {Λ Λ' Λ'' : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) K g₂ g₁ Λ)
    (hJet1 : MetricCovDerivOrderBoundOn (I := I) K 1 g₁ g₂ Λ')
    (hJet2 : MetricCovDerivOrderBoundOn (I := I) K 2 g₁ g₂ Λ'')
    {z : M'} (hz : z ∈ K) (v w : TangentSpace I z) :
    |ricciTensor (I := I) g₁ z v w - ricciTensor (I := I) g₂ z v w| ≤
      (Module.finrank ℝ E : ℝ) * riemannDiffC Λ Λ' Λ'' *
        Real.sqrt (g₂.inner z v v) * Real.sqrt (g₂.inner z w w) := by
  classical
  have hL1 : (1 : ℝ) ≤ Λ := hEq.1
  have hL0 : (0 : ℝ) ≤ Λ := le_trans zero_le_one hL1
  have hL''0 : (0 : ℝ) ≤ Λ'' := le_trans (Real.sqrt_nonneg _) (hJet2 z hz)
  have hCnn : (0 : ℝ) ≤ riemannDiffC Λ Λ' Λ'' := riemannDiffC_nonneg hL0 hL''0
  obtain ⟨B, hB⟩ := exists_orthoFrame_finrank (I := I) g₂ z
  have hBii : ∀ i, g₂.inner z (B i) (B i) = 1 := by
    intro i
    rw [hB i i, if_pos rfl]
  have hsplit : ricciTensor (I := I) g₁ z v w - ricciTensor (I := I) g₂ z v w =
      ∑ i : Fin (Module.finrank ℝ E),
        g₂.inner z ((ricciEndo (I := I) g₁ z v w - ricciEndo (I := I) g₂ z v w) (B i))
          (B i) := by
    rw [ricciTensor_apply, ricciTensor_apply,
      ← map_sub (LinearMap.trace ℝ (TangentSpace I z)) (ricciEndo (I := I) g₁ z v w)
        (ricciEndo (I := I) g₂ z v w),
      trace_eq_ortho_sum (I := I) g₂ z
        (ricciEndo (I := I) g₁ z v w - ricciEndo (I := I) g₂ z v w) B hB]
  have hterm : ∀ i : Fin (Module.finrank ℝ E),
      |g₂.inner z ((ricciEndo (I := I) g₁ z v w - ricciEndo (I := I) g₂ z v w) (B i))
        (B i)| ≤
        riemannDiffC Λ Λ' Λ'' * Real.sqrt (g₂.inner z v v) *
          Real.sqrt (g₂.inner z w w) := by
    intro i
    have hval : (ricciEndo (I := I) g₁ z v w - ricciEndo (I := I) g₂ z v w) (B i) =
        riemannOp (cov := LeviCivita (I := I) g₁) z (B i) v w -
          riemannOp (cov := LeviCivita (I := I) g₂) z (B i) v w := rfl
    have hsq := riemannDiff_gJet_le (I := I) g₂ g₁ hEq hJet1 hJet2 hz (B i) v w
    have hnorm : Real.sqrt (g₂.inner z
          (riemannOp (cov := LeviCivita (I := I) g₁) z (B i) v w -
            riemannOp (cov := LeviCivita (I := I) g₂) z (B i) v w)
          (riemannOp (cov := LeviCivita (I := I) g₁) z (B i) v w -
            riemannOp (cov := LeviCivita (I := I) g₂) z (B i) v w)) ≤
        riemannDiffC Λ Λ' Λ'' * Real.sqrt (g₂.inner z (B i) (B i)) *
          Real.sqrt (g₂.inner z v v) * Real.sqrt (g₂.inner z w w) :=
      sqrt_le_of_sq_bound hCnn
        (metric_inner_self_nonneg (I := I) (M := M') g₂ z (B i))
        (metric_inner_self_nonneg (I := I) (M := M') g₂ z v)
        (metric_inner_self_nonneg (I := I) (M := M') g₂ z w) hsq
    rw [hBii i, Real.sqrt_one, mul_one] at hnorm
    calc |g₂.inner z ((ricciEndo (I := I) g₁ z v w - ricciEndo (I := I) g₂ z v w) (B i))
            (B i)|
        ≤ Real.sqrt (g₂.inner z
              ((ricciEndo (I := I) g₁ z v w - ricciEndo (I := I) g₂ z v w) (B i))
              ((ricciEndo (I := I) g₁ z v w - ricciEndo (I := I) g₂ z v w) (B i))) *
            Real.sqrt (g₂.inner z (B i) (B i)) :=
          abs_metric_inner_le_sqrt_metric_quadratic (I := I) g₂ z _ _
      _ = Real.sqrt (g₂.inner z
              ((ricciEndo (I := I) g₁ z v w - ricciEndo (I := I) g₂ z v w) (B i))
              ((ricciEndo (I := I) g₁ z v w - ricciEndo (I := I) g₂ z v w) (B i))) := by
          rw [hBii i, Real.sqrt_one, mul_one]
      _ ≤ riemannDiffC Λ Λ' Λ'' * Real.sqrt (g₂.inner z v v) *
            Real.sqrt (g₂.inner z w w) := by
          rw [hval]
          exact hnorm
  rw [hsplit]
  calc |∑ i : Fin (Module.finrank ℝ E),
          g₂.inner z ((ricciEndo (I := I) g₁ z v w - ricciEndo (I := I) g₂ z v w) (B i))
            (B i)|
      ≤ ∑ i : Fin (Module.finrank ℝ E),
          |g₂.inner z ((ricciEndo (I := I) g₁ z v w - ricciEndo (I := I) g₂ z v w) (B i))
            (B i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ E),
          riemannDiffC Λ Λ' Λ'' * Real.sqrt (g₂.inner z v v) *
            Real.sqrt (g₂.inner z w w) := Finset.sum_le_sum (fun i _ => hterm i)
    _ = (Module.finrank ℝ E : ℝ) * riemannDiffC Λ Λ' Λ'' *
          Real.sqrt (g₂.inner z v v) * Real.sqrt (g₂.inner z w w) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

theorem abs_ricciTensor_le_of_riemannOp_le
    (g : SmoothRiemannianMetric I M') {z : M'} {Kr : ℝ}
    (hKr : ∀ a b c : TangentSpace I z,
      Real.sqrt (g.inner z (riemannOp (cov := LeviCivita (I := I) g) z a b c)
          (riemannOp (cov := LeviCivita (I := I) g) z a b c)) ≤
        Kr * Real.sqrt (g.inner z a a) * Real.sqrt (g.inner z b b) *
          Real.sqrt (g.inner z c c))
    (v w : TangentSpace I z) :
    |ricciTensor (I := I) g z v w| ≤
      (Module.finrank ℝ E : ℝ) * Kr * Real.sqrt (g.inner z v v) *
        Real.sqrt (g.inner z w w) := by
  classical
  obtain ⟨B, hB⟩ := exists_orthoFrame_finrank (I := I) g z
  have hBii : ∀ i, g.inner z (B i) (B i) = 1 := by
    intro i
    rw [hB i i, if_pos rfl]
  have hterm : ∀ i : Fin (Module.finrank ℝ E),
      |g.inner z (riemannOp (cov := LeviCivita (I := I) g) z (B i) v w) (B i)| ≤
        Kr * Real.sqrt (g.inner z v v) * Real.sqrt (g.inner z w w) := by
    intro i
    have hbnd := hKr (B i) v w
    rw [hBii i, Real.sqrt_one, mul_one] at hbnd
    calc |g.inner z (riemannOp (cov := LeviCivita (I := I) g) z (B i) v w) (B i)|
        ≤ Real.sqrt (g.inner z (riemannOp (cov := LeviCivita (I := I) g) z (B i) v w)
              (riemannOp (cov := LeviCivita (I := I) g) z (B i) v w)) *
            Real.sqrt (g.inner z (B i) (B i)) :=
          abs_metric_inner_le_sqrt_metric_quadratic (I := I) g z _ _
      _ = Real.sqrt (g.inner z (riemannOp (cov := LeviCivita (I := I) g) z (B i) v w)
              (riemannOp (cov := LeviCivita (I := I) g) z (B i) v w)) := by
          rw [hBii i, Real.sqrt_one, mul_one]
      _ ≤ Kr * Real.sqrt (g.inner z v v) * Real.sqrt (g.inner z w w) := hbnd
  rw [ricciTensor_eq_orthonormal_trace (I := I) g z v w B hB]
  calc |∑ i : Fin (Module.finrank ℝ E),
          g.inner z (riemannOp (LeviCivita (I := I) g) z (B i) v w) (B i)|
      ≤ ∑ i : Fin (Module.finrank ℝ E),
          |g.inner z (riemannOp (LeviCivita (I := I) g) z (B i) v w) (B i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ E),
          Kr * Real.sqrt (g.inner z v v) * Real.sqrt (g.inner z w w) :=
        Finset.sum_le_sum (fun i _ => hterm i)
    _ = (Module.finrank ℝ E : ℝ) * Kr * Real.sqrt (g.inner z v v) *
          Real.sqrt (g.inner z w w) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring



def ScalarCurvatureComparisonOfRicciBound (I : ModelWithCorners ℝ E H)
    (scalarC : ℝ → ℝ → ℝ) : Prop :=
  ∀ (N' : Type u) [TopologicalSpace N'] [ChartedSpace H N'] [IsManifold I ∞ N']
    [T2Space N'] [BoundarylessManifold I N'] (g₁ g₂ : SmoothRiemannianMetric I N')
    (K : Set N') (eps Kb : ℝ), 0 < eps → eps ≤ 1 / 2 → 0 ≤ Kb →
    MetricUniformEquivalentOn (I := I) K g₂ g₁ (witnessLambda eps) →
    MetricCovDerivOrderBoundOn (I := I) K 1 g₁ g₂ eps →
    MetricCovDerivOrderBoundOn (I := I) K 2 g₁ g₂ eps →
    (∀ z ∈ K, ∀ v w : TangentSpace I z,
      |ricciTensor (I := I) g₂ z v w| ≤
        Kb * Real.sqrt (g₂.inner z v v) * Real.sqrt (g₂.inner z w w)) →
    ∀ z ∈ K, |metricScalarAt (I := I) g₁ z - metricScalarAt (I := I) g₂ z| ≤
      scalarC eps Kb

theorem abs_metricScalarAt_sub_le_of_jetBounds
    {K : Set M'} (g₂ g₁ : SmoothRiemannianMetric I M') {Λ Λ' Λ'' Kb : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) K g₂ g₁ Λ)
    (hJet1 : MetricCovDerivOrderBoundOn (I := I) K 1 g₁ g₂ Λ')
    (hJet2 : MetricCovDerivOrderBoundOn (I := I) K 2 g₁ g₂ Λ'')
    {z : M'} (hz : z ∈ K)
    (hKb : ∀ v w : TangentSpace I z,
      |ricciTensor (I := I) g₂ z v w| ≤
        Kb * Real.sqrt (g₂.inner z v v) * Real.sqrt (g₂.inner z w w)) :
    |metricScalarAt (I := I) g₁ z - metricScalarAt (I := I) g₂ z| ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * Λ * riemannDiffC Λ Λ' Λ'' +
        (Module.finrank ℝ E : ℝ) * (Λ - 1) * Kb := by
  classical
  have hL1 : (1 : ℝ) ≤ Λ := hEq.1
  have hL0 : (0 : ℝ) < Λ := lt_of_lt_of_le zero_lt_one hL1
  obtain ⟨μ, basis, hginv, hhinv, hμ0, hμΛ⟩ :=
    exists_diagInv_of_metricUniformEquivalentOn (I := I) (K := K) (g := g₂) (h := g₁)
      (C := Λ) hEq hz
  have hginvGen : MetricInverseInBasis (I := I) g₂ z basis
      (diagonalInvMetric
        (fun _ : Fin (Module.finrank ℝ (TangentSpace I z)) => (1 : ℝ))) := hginv
  have hhinvGen : MetricInverseInBasis (I := I) g₁ z basis
      (diagonalInvMetric μ) := hhinv
  have hON2 : ∀ i j : Fin (Module.finrank ℝ (TangentSpace I z)),
      g₂.inner z (basis i) (basis j) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    have hh := (hginvGen i j).1
    rw [sum_diagonalInvMetric_mul] at hh
    simpa using hh
  have hONd : ∀ i j : Fin (Module.finrank ℝ (TangentSpace I z)),
      μ i * g₁.inner z (basis i) (basis j) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    have hh := (hhinvGen i j).1
    rw [sum_diagonalInvMetric_mul] at hh
    exact hh
  have hBii : ∀ i, g₂.inner z (basis i) (basis i) = 1 := by
    intro i
    rw [hON2 i i, if_pos rfl]
  have hμlow : ∀ i, Λ⁻¹ ≤ μ i := by
    intro i
    have h1 := hONd i i
    rw [if_pos rfl] at h1
    have h2 := (hEq.2 z hz (basis i)).2
    rw [hBii i, mul_one] at h2
    have h3 : 1 ≤ μ i * Λ := by nlinarith [hμ0 i]
    rw [inv_le_iff_one_le_mul₀ hL0]
    linarith
  have hμabs : ∀ i, |μ i - 1| ≤ Λ - 1 := by
    intro i
    have hlow := hμlow i
    have hhigh := hμΛ i
    have hmul : 1 ≤ μ i * Λ := by
      have := mul_le_mul_of_nonneg_right hlow hL0.le
      rw [inv_mul_cancel₀ (ne_of_gt hL0)] at this
      exact this
    rw [abs_le]
    constructor
    · nlinarith [sq_nonneg (Λ - 1)]
    · linarith
  have hs2 : metricScalarAt (I := I) g₂ z =
      ∑ i : Fin (Module.finrank ℝ (TangentSpace I z)),
        ricciTensor (I := I) g₂ z (basis i) (basis i) :=
    metricScalarAt_eq_sum_ricciTensor_orthonormal (I := I) g₂ basis hON2
  have hs1 : metricScalarAt (I := I) g₁ z =
      ∑ i : Fin (Module.finrank ℝ (TangentSpace I z)),
        μ i * ricciTensor (I := I) g₁ z (basis i) (basis i) :=
    metricScalarAt_eq_sum_ricciTensor_diagonal (I := I) g₁ basis μ hhinvGen
  have hdiff : metricScalarAt (I := I) g₁ z - metricScalarAt (I := I) g₂ z =
      ∑ i : Fin (Module.finrank ℝ (TangentSpace I z)),
        (μ i * (ricciTensor (I := I) g₁ z (basis i) (basis i) -
            ricciTensor (I := I) g₂ z (basis i) (basis i)) +
          (μ i - 1) * ricciTensor (I := I) g₂ z (basis i) (basis i)) := by
    rw [hs1, hs2, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hterm : ∀ i : Fin (Module.finrank ℝ (TangentSpace I z)),
      |μ i * (ricciTensor (I := I) g₁ z (basis i) (basis i) -
          ricciTensor (I := I) g₂ z (basis i) (basis i)) +
        (μ i - 1) * ricciTensor (I := I) g₂ z (basis i) (basis i)| ≤
        Λ * ((Module.finrank ℝ E : ℝ) * riemannDiffC Λ Λ' Λ'') + (Λ - 1) * Kb := by
    intro i
    have hRic := ricciTensor_sub_le_of_jetBounds (I := I) g₂ g₁ hEq hJet1 hJet2 hz
      (basis i) (basis i)
    rw [hBii i, Real.sqrt_one, mul_one, mul_one] at hRic
    have hRic2 := hKb (basis i) (basis i)
    rw [hBii i, Real.sqrt_one, mul_one, mul_one] at hRic2
    have hKb0 : 0 ≤ Kb := le_trans (abs_nonneg _) hRic2
    have h1 : |μ i * (ricciTensor (I := I) g₁ z (basis i) (basis i) -
        ricciTensor (I := I) g₂ z (basis i) (basis i))| ≤
        Λ * ((Module.finrank ℝ E : ℝ) * riemannDiffC Λ Λ' Λ'') := by
      rw [abs_mul, abs_of_nonneg (hμ0 i)]
      exact mul_le_mul (hμΛ i) hRic (abs_nonneg _) hL0.le
    have h2 : |(μ i - 1) * ricciTensor (I := I) g₂ z (basis i) (basis i)| ≤
        (Λ - 1) * Kb := by
      rw [abs_mul]
      exact mul_le_mul (hμabs i) hRic2 (abs_nonneg _) (by linarith [hL1])
    exact le_trans (abs_add_le _ _) (add_le_add h1 h2)
  rw [hdiff]
  calc |∑ i : Fin (Module.finrank ℝ (TangentSpace I z)),
          (μ i * (ricciTensor (I := I) g₁ z (basis i) (basis i) -
              ricciTensor (I := I) g₂ z (basis i) (basis i)) +
            (μ i - 1) * ricciTensor (I := I) g₂ z (basis i) (basis i))|
      ≤ ∑ i : Fin (Module.finrank ℝ (TangentSpace I z)),
          |μ i * (ricciTensor (I := I) g₁ z (basis i) (basis i) -
              ricciTensor (I := I) g₂ z (basis i) (basis i)) +
            (μ i - 1) * ricciTensor (I := I) g₂ z (basis i) (basis i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace I z)),
          (Λ * ((Module.finrank ℝ E : ℝ) * riemannDiffC Λ Λ' Λ'') + (Λ - 1) * Kb) :=
        Finset.sum_le_sum (fun i _ => hterm i)
    _ = (Module.finrank ℝ E : ℝ) ^ 2 * Λ * riemannDiffC Λ Λ' Λ'' +
          (Module.finrank ℝ E : ℝ) * (Λ - 1) * Kb := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hn : (Module.finrank ℝ (TangentSpace I z) : ℝ) = (Module.finrank ℝ E : ℝ) := rfl
        rw [hn]
        ring


theorem scalarCurvatureComparison :
    ScalarCurvatureComparisonOfRicciBound.{u, uE, uH} I
      (scalarComparisonC (Module.finrank ℝ E)) := by
  intro N' _ _ _ _ _ g₁ g₂ K eps Kb heps0 heps1 _ hEq hJet1 hJet2 hRic z hz
  have hmain := abs_metricScalarAt_sub_le_of_jetBounds (I := I) (M' := N') g₂ g₁
    hEq hJet1 hJet2 hz (fun v w => hRic z hz v w)
  exact hmain

end General



section Transport

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
variable [T2Space N] [SigmaCompactSpace N] [BoundarylessManifold I N]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
theorem modelComparison_scalar_sub_le_of_ricciBound
    {eps : ℝ} (heps0 : 0 < eps) (heps1 : eps ≤ 1 / 2)
    {h : ℝ → SmoothRiemannianMetric I N} {ghat : ℝ → SmoothRiemannianMetric I M}
    {p : N} {x : M} {F : PartialDiffeomorph I I N M (∞ : WithTop ℕ∞)}
    (C : ModelComparison (I := I) eps h ghat p x F)
    {s : ℝ} (hs : s ∈ Set.Icc (-(modelDepth eps)) (0 : ℝ))
    {y : sourceOpen (I := I) F} (hy : y ∈ witnessWindow (I := I) F eps h p)
    {Kb : ℝ}
    (hKb : ∀ v w : TangentSpace I y,
      |ricciTensor (I := I) (witnessModelMetric (I := I) F h s) y v w| ≤
        Kb * Real.sqrt ((witnessModelMetric (I := I) F h s).inner y v v) *
          Real.sqrt ((witnessModelMetric (I := I) F h s).inner y w w)) :
    |metricScalarAt (I := I) (ghat s) ((F : N → M) (y : N)) -
        metricScalarAt (I := I) (h s) (y : N)| ≤
      scalarComparisonC (Module.finrank ℝ E) eps Kb := by
  let _ : SigmaCompactSpace (sourceOpen (I := I) F) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I (sourceOpen (I := I) F).isOpen)
  have horder := three_le_modelOrder heps0 heps1
  have hEq := modelComparison_metricUniformEquivalentOn (I := I) heps0.le (by linarith) C hs
  have hJet1 := modelComparison_metricCovDerivOrderBoundOn (I := I) C hs
    (a := 1) le_rfl (by omega)
  have hJet2 := modelComparison_metricCovDerivOrderBoundOn (I := I) C hs
    (a := 2) (by omega) (by omega)
  have hmain := abs_metricScalarAt_sub_le_of_jetBounds (I := I)
    (M' := ↥(sourceOpen (I := I) F))
    (witnessModelMetric (I := I) F h s) (witnessPullbackMetric (I := I) F ghat s)
    hEq hJet1 hJet2 hy hKb
  have hsrc : metricScalarAt (I := I) (witnessPullbackMetric (I := I) F ghat s) y =
      metricScalarAt (I := I) (ghat s) ((F : N → M) (y : N)) :=
    openPullbackMetric_scalar (I := I) F (sourceOpen (I := I) F) (sourceOpen_subset F)
      (ghat s) y
  have hmod : metricScalarAt (I := I) (witnessModelMetric (I := I) F h s) y =
      metricScalarAt (I := I) (h s) (y : N) :=
    metricScalarAt_restrictOpen (I := I) (h s) (sourceOpen (I := I) F) y
  rw [hsrc, hmod] at hmain
  exact hmain

omit [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
theorem modelComparison_scalar_sub_le_of_riemannBound
    {eps : ℝ} (heps0 : 0 < eps) (heps1 : eps ≤ 1 / 2)
    {h : ℝ → SmoothRiemannianMetric I N} {ghat : ℝ → SmoothRiemannianMetric I M}
    {p : N} {x : M} {F : PartialDiffeomorph I I N M (∞ : WithTop ℕ∞)}
    (C : ModelComparison (I := I) eps h ghat p x F)
    {s : ℝ} (hs : s ∈ Set.Icc (-(modelDepth eps)) (0 : ℝ))
    {y : sourceOpen (I := I) F} (hy : y ∈ witnessWindow (I := I) F eps h p)
    {Kb : ℝ} (hKb0 : 0 ≤ Kb)
    (hKb : ∀ a b c : TangentSpace I y,
      (witnessModelMetric (I := I) F h s).inner y
          (riemannOp (cov := LeviCivita (I := I) (witnessModelMetric (I := I) F h s))
            y a b c)
          (riemannOp (cov := LeviCivita (I := I) (witnessModelMetric (I := I) F h s))
            y a b c) ≤
        Kb * (witnessModelMetric (I := I) F h s).inner y a a *
          (witnessModelMetric (I := I) F h s).inner y b b *
          (witnessModelMetric (I := I) F h s).inner y c c) :
    |metricScalarAt (I := I) (ghat s) ((F : N → M) (y : N)) -
        metricScalarAt (I := I) (h s) (y : N)| ≤
      scalarComparisonC (Module.finrank ℝ E) eps
        ((Module.finrank ℝ E : ℝ) * Real.sqrt Kb) := by
  refine modelComparison_scalar_sub_le_of_ricciBound (I := I) heps0 heps1 C hs hy ?_
  intro v w
  refine abs_ricciTensor_le_of_riemannOp_le (I := I) (witnessModelMetric (I := I) F h s)
    ?_ v w
  intro a b c
  refine sqrt_le_of_sq_bound (Real.sqrt_nonneg Kb)
    (metric_inner_self_nonneg (I := I) (witnessModelMetric (I := I) F h s) y a)
    (metric_inner_self_nonneg (I := I) (witnessModelMetric (I := I) F h s) y b)
    (metric_inner_self_nonneg (I := I) (witnessModelMetric (I := I) F h s) y c) ?_
  rw [Real.sq_sqrt hKb0]
  exact hKb a b c

end Transport

end

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
