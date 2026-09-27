import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Scalar.EndpointScalarComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.Higher

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Parabolic
open scoped Manifold ContDiff BigOperators
namespace DifferentialGeometry.Analysis

def endpointTowerBound (c K T : ℝ) (A : ℕ → ℝ) : ℕ → ℝ
  | 0 => K ^ 2
  | n + 1 =>
    let L := endpointTowerBound c K T A n
    let a := ((n + 2 : ℕ) : ℝ) * c * (K + L)
    L + Real.exp (a * T) * (A (n + 1) ^ 2 + a * T)

theorem endpointTowerBound_nonneg (c K T : ℝ) (A : ℕ → ℝ)
    (hc : 0 ≤ c) (hK : 0 ≤ K) (hT : 0 ≤ T) (n : ℕ) :
    0 ≤ endpointTowerBound c K T A n := by
  induction n with
  | zero => exact sq_nonneg K
  | succ n ih =>
    simp only [endpointTowerBound]
    positivity

theorem endpoint_tower_reaction_le (w : ℕ → ℝ) (c K L : ℝ) (k : ℕ)
    (hc : 0 ≤ c) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hw : ∀ j ≤ k, 0 ≤ w j) (hzero : w 0 ≤ K ^ 2)
    (hlower : ∀ j < k, w j ≤ L) :
    (∑ j ∈ Finset.range (k + 1),
      c * Real.sqrt (w j) * Real.sqrt (w (k - j)) * Real.sqrt (w k)) ≤
      ((k + 1 : ℕ) : ℝ) * c * (K + L) * (w k + 1) := by
  have hwk := hw k le_rfl
  have hs0 : Real.sqrt (w 0) ≤ K :=
    (Real.sqrt_le_sqrt hzero).trans_eq (Real.sqrt_sq hK)
  have hsq : Real.sqrt (w k) * Real.sqrt (w k) = w k := Real.mul_self_sqrt hwk
  have hboundary : Real.sqrt (w 0) * w k ≤ (K + L) * (w k + 1) := by
    apply (mul_le_mul_of_nonneg_right hs0 hwk).trans
    nlinarith [mul_nonneg hL hwk]
  have htop : Real.sqrt (w k) ≤ w k + 1 := by
    nlinarith [Real.sq_sqrt hwk, sq_nonneg (Real.sqrt (w k) - 1)]
  have hterm (j : ℕ) (hj : j ∈ Finset.range (k + 1)) :
      c * Real.sqrt (w j) * Real.sqrt (w (k - j)) * Real.sqrt (w k) ≤
        c * (K + L) * (w k + 1) := by
    have hjk : j ≤ k := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
    have hraw : Real.sqrt (w j) * Real.sqrt (w (k - j)) * Real.sqrt (w k) ≤
        (K + L) * (w k + 1) := by
      by_cases hj0 : j = 0
      · subst j
        simpa only [Nat.sub_zero, mul_assoc, hsq] using hboundary
      by_cases hjtop : j = k
      · subst j
        calc Real.sqrt (w k) * Real.sqrt (w (k - k)) * Real.sqrt (w k)
            = Real.sqrt (w 0) * (Real.sqrt (w k) * Real.sqrt (w k)) := by
              rw [Nat.sub_self]; ring
          _ ≤ (K + L) * (w k + 1) := by rw [hsq]; exact hboundary
      have hjlt : j < k := lt_of_le_of_ne hjk hjtop
      have hkjlt : k - j < k := by omega
      have hpair : Real.sqrt (w j) * Real.sqrt (w (k - j)) ≤ L := by
        nlinarith [Real.sq_sqrt (hw j hjk), Real.sq_sqrt (hw (k - j) (Nat.sub_le _ _)),
          sq_nonneg (Real.sqrt (w j) - Real.sqrt (w (k - j))),
          hlower j hjlt, hlower (k - j) hkjlt]
      calc Real.sqrt (w j) * Real.sqrt (w (k - j)) * Real.sqrt (w k)
          ≤ L * Real.sqrt (w k) := mul_le_mul_of_nonneg_right hpair (Real.sqrt_nonneg _)
        _ ≤ L * (w k + 1) := mul_le_mul_of_nonneg_left htop hL
        _ ≤ (K + L) * (w k + 1) :=
          mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hraw hc]
  calc (∑ j ∈ Finset.range (k + 1),
      c * Real.sqrt (w j) * Real.sqrt (w (k - j)) * Real.sqrt (w k))
      ≤ ∑ _j ∈ Finset.range (k + 1), c * (K + L) * (w k + 1) := Finset.sum_le_sum hterm
    _ = ((k + 1 : ℕ) : ℝ) * c * (K + L) * (w k + 1) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]

theorem endpoint_tower_bound_compact
    (G : MetricConnectionFamily (I := I) (M := M) ℝ) (T : ℝ) (hT : 0 < T)
    (w : ℕ → ℝ → M → ℝ) (N : ℕ) (c K : ℝ) (A : ℕ → ℝ)
    (hc : 0 ≤ c) (hK : 0 ≤ K)
    (hwnonneg : ∀ k ≤ N + 1, ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ w k t x)
    (hwzero : ∀ t ∈ Icc 0 T, ∀ x, w 0 t x ≤ K ^ 2)
    (hcont : ∀ k ≤ N, ContinuousOn (fun p : ℝ × M => w k p.1 p.2) (Icc 0 T ×ˢ univ))
    (htime : ∀ k ≤ N, ∀ t ∈ Icc 0 T, 0 < t → ∀ x,
      DifferentiableWithinAt ℝ (fun s => w k s x) (Icc 0 T) t)
    (hspace : ∀ k ≤ N, ∀ t ∈ Icc 0 T, 0 < t → ContMDiff I 𝓘(ℝ, ℝ) ∞ (w k t))
    (hinit : ∀ k ≤ N, ∀ x, w k 0 x ≤ A k ^ 2)
    (hheat : ∀ k ≤ N, ∀ t ∈ Icc 0 T, 0 < t → ∀ x,
      parabolicOperatorWithDrift G T (fun _ _ => 0) (w k) t x ≤
        -2 * w (k + 1) t x + towerReactionSum w c k t x) :
    ∀ k ≤ N, ∀ t ∈ Icc 0 T, ∀ x, w k t x ≤ endpointTowerBound c K T A N := by
  have hlevels : ∀ n, n ≤ N → ∀ k ≤ n, ∀ t ∈ Icc 0 T, ∀ x,
      w k t x ≤ endpointTowerBound c K T A n := by
    intro n
    induction n with
    | zero =>
      intro _ k hk t ht x
      have he : k = 0 := by omega
      subst k
      exact hwzero t ht x
    | succ n ih =>
      intro hn
      let L := endpointTowerBound c K T A n
      let a := ((n + 2 : ℕ) : ℝ) * c * (K + L)
      have hL : 0 ≤ L := endpointTowerBound_nonneg c K T A hc hK hT.le n
      have ha : 0 ≤ a := by dsimp only [a]; positivity
      have hlower := ih (by omega : n ≤ N)
      have hlinear : ∀ t ∈ Icc 0 T, 0 < t → ∀ x,
          parabolicOperatorWithDrift G T (fun _ _ => 0) (w (n + 1)) t x ≤
            a * w (n + 1) t x + a := by
        intro t ht hp x
        have hr := endpoint_tower_reaction_le (fun j => w j t x) c K L (n + 1)
          hc hK hL (fun j hj => hwnonneg j (by omega) t ht x)
          (hwzero t ht x) (fun j hj => hlower j (by omega) t ht x)
        have hnext := hwnonneg (n + 1 + 1) (by omega) t ht x
        have he := hheat (n + 1) hn t ht hp x
        change towerReactionSum w c (n + 1) t x ≤ a * (w (n + 1) t x + 1) at hr
        nlinarith
      have hnew := scalar_linear_reaction_bound_compact G T hT (fun _ _ => 0)
        (w (n + 1)) a a (A (n + 1) ^ 2) ha ha (hcont (n + 1) hn)
        (htime (n + 1) hn) (hspace (n + 1) hn) (hinit (n + 1) hn) hlinear
      intro k hk t ht x
      have hlarge : 0 ≤ Real.exp (a * T) * (A (n + 1) ^ 2 + a * T) := by positivity
      change w k t x ≤ L + Real.exp (a * T) * (A (n + 1) ^ 2 + a * T)
      by_cases hkn : k ≤ n
      · exact (hlower k hkn t ht x).trans (le_add_of_nonneg_right hlarge)
      have he : k = n + 1 := by omega
      subst k
      apply (hnew t ht x).trans
      have hat : a * t ≤ a * T := mul_le_mul_of_nonneg_left ht.2 ha
      have hexp : Real.exp (a * t) ≤ Real.exp (a * T) := Real.exp_le_exp.mpr hat
      have hp : 0 ≤ A (n + 1) ^ 2 + a * t := add_nonneg (sq_nonneg _) (mul_nonneg ha ht.1)
      have hb := mul_le_mul hexp (add_le_add le_rfl hat) hp (Real.exp_pos _).le
      exact hb.trans (le_add_of_nonneg_left hL)
  exact hlevels N le_rfl
end DifferentialGeometry.Analysis
