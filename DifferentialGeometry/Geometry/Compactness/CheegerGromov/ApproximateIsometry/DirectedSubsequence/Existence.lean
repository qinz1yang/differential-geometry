import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.PairwiseApproximation.Basic
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.ZeroOrder
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.Monotonicity
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.Congruence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.Identity
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.BallImage
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.Composition.ForwardBounds
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.Composition.ReverseBounds
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.DirectedSubsequence.RadiusBounds
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Metric.Proper
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Addition
import DifferentialGeometry.Analysis.Calculus.Compactness.DiagonalSubsequence
import DifferentialGeometry.Analysis.Estimates.IteratedApproximationError
import DifferentialGeometry.Analysis.Estimates.GeometricTail
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Composition
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open scoped Manifold ContDiff Topology BigOperators ENNReal
open Bundle Manifold Filter
open DifferentialGeometry.Tensor0SBundle

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

section Endpoint

private lemma sepNextC0_nonneg {c0 cov δ : ℝ} (hc0 : 0 ≤ c0) (hδ : 0 ≤ δ)
    (hfeed : 0 ≤ sepEnvelope c0 cov) : 0 ≤ sepNextC0 c0 cov δ := by
  unfold sepNextC0
  have h : 0 ≤ δ * (1 + sepEnvelope c0 cov) := mul_nonneg hδ (by linarith)
  linarith

private lemma sepNextCov_nonneg {c0 cov δ B : ℝ} (hfeed : 0 ≤ sepEnvelope c0 cov)
    (hδ : 0 ≤ δ) (hB : 0 ≤ B) : 0 ≤ sepNextCov c0 cov δ B := by
  unfold sepNextCov
  have h : 0 ≤ δ * B := mul_nonneg hδ hB
  linarith

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private theorem exists_directed_approximations_on_buffered_balls
    (P : ∀ k, ProperMetricOn (I := I) (X.obj k))
    (r R eta : ℕ → ℝ) (ro rm : ℕ → ℕ → ℝ)
    (hr : ∀ j, 0 < r j) (hR : ∀ j, 0 < R j)
    (hro : ∀ j l, r j < ro j l)
    (hrm₁ : ∀ j l, ro j (l + 1) < rm j l)
    (hrm₂ : ∀ j l, rm j l < ro j l)
    (hrmR : ∀ j l, rm j l ≤ R j)
    (heta : ∀ j, 0 < eta j ∧ eta j < 1)
    (hbudget : ∀ j l c0, c0 ≤ 1 / 2 → c0 ≤ 2 * sepTail j l → c0 ≤ eta j)
    (himage : ∀ j l, Real.sqrt (1 + eta j) * rm j l < R (j + l))
    (hstepImage : ∀ j l, Real.sqrt (1 + (1 / 2 : ℝ) ^ (j + 1)) * rm j l < ro (j + 1) l)
    (hB : ∀ j : ℕ,
    ∃ k₀ : Nat, ∀ k ℓ : Nat, k₀ ≤ k → k₀ ≤ ℓ →
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (X.obj k).M := (X.obj k).t2
      letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj k).M := (X.obj k).smooth
      letI : TopologicalSpace (X.obj ℓ).M := (X.obj ℓ).topology
      letI : ChartedSpace H (X.obj ℓ).M := (X.obj ℓ).charted
      letI : IsManifold I ∞ (X.obj ℓ).M := (X.obj ℓ).smooth
      letI : T2Space (X.obj ℓ).M := (X.obj ℓ).t2
      letI : SigmaCompactSpace (X.obj ℓ).M := (X.obj ℓ).sigmaCompact
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj ℓ).M := (X.obj ℓ).smooth
      letI : MetricSpace (X.obj k).M := (P k).ms
      letI : MetricSpace (X.obj ℓ).M := (P ℓ).ms
      ∃ Phi : PartialDiffeomorph I I (X.obj k).M (X.obj ℓ).M (∞ : WithTop ℕ∞),
        Metric.closedBall (X.obj k).basepoint (R j) ⊆ Phi.source ∧
        Phi (X.obj k).basepoint = (X.obj ℓ).basepoint ∧
        Nonempty (PartialDiffeomorphMetricApproximation (I := I)
          (Metric.closedBall (X.obj k).basepoint (R j))
          ((1 / 2 : ℝ) ^ (j + 1)) j Phi (X.obj k).metric (X.obj ℓ).metric)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      (letI : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
       letI : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
       letI : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
       letI : ∀ j, T2Space (X.obj (σ j)).M := fun j => (X.obj (σ j)).t2
       letI : ∀ j, SigmaCompactSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).sigmaCompact
       letI : ∀ j, MetricSpace (X.obj (σ j)).M := fun j => (P (σ j)).ms
       ∃ Ψ : ∀ j, PartialDiffeomorph I I (X.obj (σ j)).M (X.obj (σ (j + 1))).M
          (∞ : WithTop ℕ∞),
        (∀ j, (Ψ j : (X.obj (σ j)).M → (X.obj (σ (j + 1))).M) ((X.obj (σ j)).basepoint)
            = (X.obj (σ (j + 1))).basepoint) ∧
        ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ p : ℕ, ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → ∀ l : ℕ,
          Nonempty (PartialDiffeomorphMetricApproximationBounds (I := I)
            (Metric.closedBall ((X.obj (σ j)).basepoint) (r j)) (min ε (eta j)) ε p
            (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ j l)
            (X.obj (σ j)).metric (X.obj (σ (j + l))).metric)) := by
  classical
  set T : ℕ → ℕ := fun j => (hB j).choose with hT
  obtain ⟨σ, hσmono, hσge⟩ := exists_strictMono_ge T
  refine ⟨σ, hσmono, ?_⟩
  let : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
  let : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
  let : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
  let : ∀ j, T2Space (X.obj (σ j)).M := fun j => (X.obj (σ j)).t2
  let : ∀ j, SigmaCompactSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).sigmaCompact
  let : ∀ j, MetricSpace (X.obj (σ j)).M := fun j => (P (σ j)).ms
  let : ∀ j, IsManifold I 1 (X.obj (σ j)).M := fun j =>
    IsManifold.of_le (I := I) (M := (X.obj (σ j)).M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let : ∀ j, IsManifold I 2 (X.obj (σ j)).M := fun j =>
    IsManifold.of_le (I := I) (M := (X.obj (σ j)).M) (n := (∞ : WithTop ℕ∞))
      (by decide : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let : ∀ j, IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj (σ j)).M := fun j => by
    change IsManifold I ∞ (X.obj (σ j)).M; infer_instance
  let hRB : ∀ j, Bundle.RiemannianBundle (fun x : (X.obj (σ j)).M => TangentSpace I x) :=
    fun j => (X.obj (σ j)).riemBundle
  have hRiem : ∀ j, IsRiemannianManifold I (X.obj (σ j)).M := fun j =>
    (P (σ j)).isRiemannianManifold (X.obj (σ j))
  have hProper : ∀ j, ProperSpace (X.obj (σ j)).M := fun j => (P (σ j)).proper
  have hstep : ∀ j : ℕ, T j ≤ σ j ∧ T j ≤ σ (j + 1) := fun j =>
    ⟨hσge j, le_trans (hσge j) (le_of_lt (hσmono (Nat.lt_succ_self j)))⟩
  have hΨex : ∀ j : ℕ,
      ∃ Φ : PartialDiffeomorph I I (X.obj (σ j)).M (X.obj (σ (j + 1))).M (∞ : WithTop ℕ∞),
        Metric.closedBall ((X.obj (σ j)).basepoint) (R j) ⊆ Φ.source ∧
        (Φ : (X.obj (σ j)).M → (X.obj (σ (j + 1))).M) ((X.obj (σ j)).basepoint)
          = (X.obj (σ (j + 1))).basepoint ∧
        Nonempty (PartialDiffeomorphMetricApproximation (I := I)
          (Metric.closedBall ((X.obj (σ j)).basepoint) (R j))
          ((1 / 2 : ℝ) ^ (j + 1)) j Φ (X.obj (σ j)).metric (X.obj (σ (j + 1))).metric) :=
    fun j => (hB j).choose_spec (σ j) (σ (j + 1)) (hstep j).1 (hstep j).2
  choose Ψ hΨsource hΨbase hΨdata using hΨex
  refine ⟨Ψ, hΨbase, ?_⟩
  intro ε hε hε1 p
  let C : ℝ := (exists_uniform_iterated_covariant_derivative_add_norm_bound.{u, uE, uH} (I := I) p).choose
  have hC0 : 0 ≤ C := (exists_uniform_iterated_covariant_derivative_add_norm_bound.{u, uE, uH} (I := I) p).choose_spec.1
  let B : ℝ := max C 2
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_right C 2)
  obtain ⟨jε, hjε⟩ := sepTailBudget B ε hε
  obtain ⟨jβ, hjβ⟩ := sepTailBudget B (1 / 2) (by norm_num)
  refine ⟨max (max jε jβ) p, fun j hj => ?_⟩
  have hjεj : jε ≤ j := le_trans (Nat.le_trans (Nat.le_max_left jε jβ)
    (Nat.le_max_left (max jε jβ) p)) hj
  have hjβj : jβ ≤ j := le_trans (Nat.le_trans (Nat.le_max_right jε jβ)
    (Nat.le_max_left (max jε jβ) p)) hj
  have hpj : p ≤ j := le_trans (Nat.le_max_right (max jε jβ) p) hj
  suffices hacc : ∀ (l s : ℕ), j ≤ s → ∃ c0 cov : ℝ,
      0 ≤ c0 ∧ 0 ≤ cov ∧ c0 ≤ ε ∧ cov ≤ ε ∧ c0 ≤ 1 / 2 ∧ cov ≤ 1 / 2 ∧
      c0 ≤ 2 * sepTail s l ∧ cov ≤ sepBeta B * sepTail s l ∧
      Nonempty (PartialDiffeomorphMetricApproximationBounds (I := I)
        (Metric.ball ((X.obj (σ s)).basepoint) (ro s l)) c0 cov p
        (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s l)
        (X.obj (σ s)).metric (X.obj (σ (s + l))).metric) ∧
      (∀ m (hm : s + l = m), Nonempty (PartialDiffeomorphMetricApproximationBounds (I := I)
        (Metric.ball ((X.obj (σ s)).basepoint) (ro s l)) c0 cov p
        (chainCompOfAddEq (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ l s m hm)
        (X.obj (σ s)).metric (X.obj (σ m)).metric)) by
    intro l
    obtain ⟨c0, cov, _hc0non, _hcovnon, hc0e, hcove, hc0half, _, hc0budget, _, ⟨⟨D⟩, _⟩⟩ :=
      hacc l j le_rfl
    exact ⟨D.mono (Metric.closedBall_subset_ball (hro j l))
      (le_min hc0e (hbudget j l c0 hc0half hc0budget)) hcove⟩
  intro l
  induction l with
  | zero =>
      intro s _hs
      refine ⟨0, 0, le_rfl, le_rfl, le_of_lt hε, le_of_lt hε, by norm_num, by norm_num,
        ?_, ?_, ?_⟩
      · simp [sepTail]
      · simp [sepTail]
      · exact ⟨
          partial_diffeomorph_metric_approximation_bounds_refl (I := I)
            (Metric.ball ((X.obj (σ s)).basepoint) (ro s 0))
            (X.obj (σ s)).metric p,
          fun m hm => by
            cases hm
            exact partial_diffeomorph_metric_approximation_bounds_refl (I := I)
              (Metric.ball ((X.obj (σ s)).basepoint) (ro s 0))
              (X.obj (σ s)).metric p⟩
  | succ l ih =>
      intro s hs
      obtain ⟨c0F, covF, hc0F0, hcovF0, _hc0Fe, _hcovFe, hc0F2, hcovF2,
        hc0Fbudget, hcovFbudget, ⟨⟨DforAcc⟩, DrevAtSAll⟩⟩ := ih s hs
      obtain ⟨DrevAtS⟩ := DrevAtSAll (s + l) rfl
      obtain ⟨c0R, covR, hc0R0, hcovR0, _hc0Re, _hcovRe, hc0R2, hcovR2,
        hc0Rbudget, hcovRbudget, ⟨⟨DforTail⟩, DrevTailAll⟩⟩ :=
        ih (s + 1) (le_trans hs (Nat.le_succ s))
      have htail_index : s + 1 + l = s + (l + 1) := by omega
      obtain ⟨DrevTail⟩ := DrevTailAll (s + (l + 1)) htail_index
      let δF : ℝ := (1 / 2 : ℝ) ^ (s + l + 1)
      let δR : ℝ := (1 / 2 : ℝ) ^ (s + 1)
      have hδF0 : 0 ≤ δF := by positivity
      have hδR0 : 0 ≤ δR := by positivity
      let c0NF : ℝ := sepNextC0 c0F covF δF
      let covNF : ℝ := sepNextCov c0F covF δF B
      let c0NR : ℝ := sepNextC0 c0R covR δR
      let covNR : ℝ := sepNextCov c0R covR δR B
      let c0Next : ℝ := max c0NF c0NR
      let covNext : ℝ := max covNF covNR
      have hβpos : 0 < sepBeta B := sepBeta_pos B
      have hβ4 : (4 : ℝ) ≤ sepBeta B := sepBeta_four B
      have hTF0 : 0 ≤ sepTail s l := sepTail_nonneg s l
      have hTR0 : 0 ≤ sepTail (s + 1) l := sepTail_nonneg (s + 1) l
      have hTFsmall : sepTail s l ≤ 1 / sepBeta B := by
        have hsmall : sepBeta B * sepTail s l ≤ 1 :=
          le_trans (hjβ s (le_trans hjβj hs) l) (by norm_num)
        rw [le_div_iff₀ hβpos]
        nlinarith
      have hTRsmall : sepTail (s + 1) l ≤ 1 / sepBeta B := by
        have hs1 : j ≤ s + 1 := le_trans hs (Nat.le_succ s)
        have hsmall : sepBeta B * sepTail (s + 1) l ≤ 1 :=
          le_trans (hjβ (s + 1) (le_trans hjβj hs1) l) (by norm_num)
        rw [le_div_iff₀ hβpos]
        nlinarith
      have hc0NFbudget : c0NF ≤ 2 * sepTail s (l + 1) := by
        dsimp [c0NF]
        calc
          sepNextC0 c0F covF δF ≤ 2 * (sepTail s l + δF) :=
            sepNextC0_le hTF0 hδF0 hc0F0 hc0Fbudget hcovFbudget hTFsmall
          _ = 2 * sepTail s (l + 1) := by
            dsimp [δF]
            rw [sepTail_succ]
      have hcovNFbudget : covNF ≤ sepBeta B * sepTail s (l + 1) := by
        dsimp [covNF]
        calc
          sepNextCov c0F covF δF B ≤ sepBeta B * (sepTail s l + δF) :=
            sepNextCov_le hTF0 hδF0 hc0F0 hc0Fbudget hcovFbudget hTFsmall
          _ = sepBeta B * sepTail s (l + 1) := by
            dsimp [δF]
            rw [sepTail_succ]
      have hc0NRbudget : c0NR ≤ 2 * sepTail s (l + 1) := by
        dsimp [c0NR]
        calc
          sepNextC0 c0R covR δR ≤ 2 * (sepTail (s + 1) l + δR) :=
            sepNextC0_le hTR0 hδR0 hc0R0 hc0Rbudget hcovRbudget hTRsmall
          _ = 2 * sepTail s (l + 1) := by
            dsimp [δR]
            rw [sepTail_succ_left]
            ring
      have hcovNRbudget : covNR ≤ sepBeta B * sepTail s (l + 1) := by
        dsimp [covNR]
        calc
          sepNextCov c0R covR δR B ≤ sepBeta B * (sepTail (s + 1) l + δR) :=
            sepNextCov_le hTR0 hδR0 hc0R0 hc0Rbudget hcovRbudget hTRsmall
          _ = sepBeta B * sepTail s (l + 1) := by
            dsimp [δR]
            rw [sepTail_succ_left]
            ring
      have hc0NextBudget : c0Next ≤ 2 * sepTail s (l + 1) := by
        dsimp [c0Next]
        exact max_le hc0NFbudget hc0NRbudget
      have hcovNextBudget : covNext ≤ sepBeta B * sepTail s (l + 1) := by
        dsimp [covNext]
        exact max_le hcovNFbudget hcovNRbudget
      have hfeedF0 : 0 ≤ sepEnvelope c0F covF :=
        sepEnvelope_nonneg hc0F0 (lt_of_le_of_lt hc0F2 (by norm_num))
      have hfeedR0 : 0 ≤ sepEnvelope c0R covR :=
        sepEnvelope_nonneg hc0R0 (lt_of_le_of_lt hc0R2 (by norm_num))
      have hc0NF0 : 0 ≤ c0NF := sepNextC0_nonneg hc0F0 hδF0 hfeedF0
      have hcovNF0 : 0 ≤ covNF := sepNextCov_nonneg hfeedF0 hδF0 hBpos.le
      have hc0NR0 : 0 ≤ c0NR := sepNextC0_nonneg hc0R0 hδR0 hfeedR0
      have hcovNR0 : 0 ≤ covNR := sepNextCov_nonneg hfeedR0 hδR0 hBpos.le
      have hc0Next0 : 0 ≤ c0Next := by
        dsimp [c0Next]
        exact le_max_of_le_left hc0NF0
      have hcovNext0 : 0 ≤ covNext := by
        dsimp [covNext]
        exact le_max_of_le_left hcovNF0
      have htailNext0 : 0 ≤ sepTail s (l + 1) := sepTail_nonneg s (l + 1)
      have htailNextε : sepBeta B * sepTail s (l + 1) ≤ ε :=
        hjε s (le_trans hjεj hs) (l + 1)
      have htailNextHalf : sepBeta B * sepTail s (l + 1) ≤ 1 / 2 :=
        hjβ s (le_trans hjβj hs) (l + 1)
      have htwoTail_le_betaTail :
          2 * sepTail s (l + 1) ≤ sepBeta B * sepTail s (l + 1) := by
        have h2β : (2 : ℝ) ≤ sepBeta B := le_trans (by norm_num) hβ4
        exact mul_le_mul_of_nonneg_right h2β htailNext0
      have hc0Nextε : c0Next ≤ ε := by
        exact le_trans hc0NextBudget (le_trans htwoTail_le_betaTail htailNextε)
      have hcovNextε : covNext ≤ ε := by
        exact le_trans hcovNextBudget htailNextε
      have hc0NextHalf : c0Next ≤ 1 / 2 := by
        exact le_trans hc0NextBudget (le_trans htwoTail_le_betaTail htailNextHalf)
      have hcovNextHalf : covNext ≤ 1 / 2 := by
        exact le_trans hcovNextBudget htailNextHalf
      let Rcur : ℝ := ro s l
      let Rnext : ℝ := ro s (l + 1)
      let Rmid : ℝ := rm s l
      have hRnext_pos : 0 < Rnext := by
        exact (hr s).trans (hro s (l + 1))
      have hRmid_pos : 0 < Rmid := by
        exact ((hr s).trans (hro s (l + 1))).trans (hrm₁ s l)
      have hRnext_lt_Rmid : Rnext < Rmid := by
        simpa [Rnext, Rmid] using hrm₁ s l
      have hRmid_lt_Rcur : Rmid < Rcur := by
        simpa [Rmid, Rcur] using hrm₂ s l
      let U₁ : TopologicalSpace.Opens (X.obj (σ s)).M :=
        ⟨Metric.ball ((X.obj (σ s)).basepoint) Rmid, by
          have hb :
              @IsOpen (X.obj (σ s)).M
                (P (σ s)).ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
                (Metric.ball ((X.obj (σ s)).basepoint) Rmid) := by
            let : MetricSpace (X.obj (σ s)).M := (P (σ s)).ms
            exact Metric.isOpen_ball
          rwa [ProperMetricOn.top_eq (X.obj (σ s)) (P (σ s))] at hb⟩
      let K₂ : TopologicalSpace.Opens (X.obj (σ (s + l))).M :=
        ⟨Metric.ball ((X.obj (σ (s + l))).basepoint) (R (s + l)),
          by
            have hb :
                @IsOpen (X.obj (σ (s + l))).M
                  (P (σ (s + l))).ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
                  (Metric.ball ((X.obj (σ (s + l))).basepoint) (R (s + l))) := by
              let : MetricSpace (X.obj (σ (s + l))).M := (P (σ (s + l))).ms
              exact Metric.isOpen_ball
            rwa [ProperMetricOn.top_eq (X.obj (σ (s + l))) (P (σ (s + l)))] at hb⟩
      have hU₁_nonempty : Nonempty U₁ :=
        ⟨⟨(X.obj (σ s)).basepoint, Metric.mem_ball_self hRmid_pos⟩⟩
      have hK₂_nonempty : Nonempty K₂ :=
        ⟨⟨(X.obj (σ (s + l))).basepoint,
          Metric.mem_ball_self (hR (s + l))⟩⟩
      have hU₁_source : (U₁ : Set (X.obj (σ s)).M) ⊆
          (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s l).source := by
        intro x hx
        exact DforAcc.source_sub (Metric.ball_subset_ball hRmid_lt_Rcur.le hx)
      have hK₂_source : (K₂ : Set (X.obj (σ (s + l))).M) ⊆ (Ψ (s + l)).source := by
        intro y hy
        exact hΨsource (s + l) (Metric.ball_subset_closedBall hy)
      have D₁mid : PartialDiffeomorphMetricApproximationBounds (I := I) (U₁ : Set (X.obj (σ s)).M) c0F covF p
          (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s l)
          (X.obj (σ s)).metric (X.obj (σ (s + l))).metric :=
        DforAcc.mono (Metric.ball_subset_ball hRmid_lt_Rcur.le) le_rfl le_rfl
      obtain ⟨DstepF⟩ := hΨdata (s + l)
      have hp_stepF : p ≤ s + l :=
        le_trans hpj (le_trans hs (Nat.le_add_right s l))
      have D₂openF : PartialDiffeomorphMetricApproximationBounds (I := I) (K₂ : Set (X.obj (σ (s + l))).M)
          δF δF p (Ψ (s + l))
          (X.obj (σ (s + l))).metric (X.obj (σ (s + l + 1))).metric := by
        dsimp [δF]
        exact ((DstepF.monoOrder hp_stepF).mono Metric.ball_subset_closedBall le_rfl
          DstepF.forward.eps_lt_one).toSeparateBounds
      have hclosed_mid_sub :
          Metric.closedEBall ((X.obj (σ s)).basepoint) (ENNReal.ofReal Rmid) ⊆
            Metric.ball ((X.obj (σ s)).basepoint) Rcur := by
        rw [Metric.closedEBall_ofReal hRmid_pos.le]
        exact Metric.closedBall_subset_ball hRmid_lt_Rcur
      have hdata_mid : MapMetricApproximationOn (I := I)
          (Metric.closedEBall ((X.obj (σ s)).basepoint) (ENNReal.ofReal Rmid)) (eta s) 0
          (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s l :
            (X.obj (σ s)).M → (X.obj (σ (s + l))).M)
          (X.obj (σ s)).metric (X.obj (σ (s + l))).metric :=
        (DforAcc.forward.mono hclosed_mid_sub le_rfl le_rfl).toMetricApproximationZero
          (heta s).1 (heta s).2 (hbudget s l c0F hc0F2 hc0Fbudget)
      have hsrc_mid :
          Metric.closedEBall ((X.obj (σ s)).basepoint) (ENNReal.ofReal Rmid) ⊆
            (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s l).source :=
        fun x hx => DforAcc.source_sub (hclosed_mid_sub hx)
      have hcenter :
          (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s l :
              (X.obj (σ s)).M → (X.obj (σ (s + l))).M)
              ((X.obj (σ s)).basepoint)
            = (X.obj (σ (s + l))).basepoint :=
        chainComp_base (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ
          (fun i => (X.obj (σ i)).basepoint) hΨbase s l
      have himg_mid :
          (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s l :
              (X.obj (σ s)).M → (X.obj (σ (s + l))).M) ''
              Metric.ball ((X.obj (σ s)).basepoint) Rmid ⊆
            Metric.ball ((X.obj (σ (s + l))).basepoint) (R (s + l)) := by
        have htmp :
            (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s l :
                (X.obj (σ s)).M → (X.obj (σ (s + l))).M) ''
                Metric.ball ((X.obj (σ s)).basepoint) Rmid ⊆
              Metric.ball
                ((chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s l :
                    (X.obj (σ s)).M → (X.obj (σ (s + l))).M)
                  ((X.obj (σ s)).basepoint))
                (R (s + l)) :=
          MapMetricApproximationOn.image_metric_ball_subset (I := I)
            (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s l)
            (by
              intro x v
              exact (Geometry.Riemannian.isMetricNorm_of_riemannianBundle
                (I := I) (X.obj (σ s)).metric) x v)
            (by
              intro x v
              exact (Geometry.Riemannian.isMetricNorm_of_riemannianBundle
                (I := I) (X.obj (σ (s + l))).metric) x v)
            hRmid_pos le_rfl (heta s).1.le
            (himage s l)
            hdata_mid hsrc_mid
        intro y hy
        simpa [hcenter] using htmp hy
      have hKcompactF : IsCompact
          (Metric.closedBall ((X.obj (σ s)).basepoint) Rnext) := by
        have hcompact :
            @IsCompact (X.obj (σ s)).M
              (P (σ s)).ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
              (Metric.closedBall ((X.obj (σ s)).basepoint) Rnext) := by
          let : MetricSpace (X.obj (σ s)).M := (P (σ s)).ms
          have : ProperSpace (X.obj (σ s)).M := (P (σ s)).proper
          simpa using (isCompact_closedBall ((X.obj (σ s)).basepoint) Rnext)
        rw [ProperMetricOn.top_eq (X.obj (σ s)) (P (σ s))] at hcompact
        exact hcompact
      have hKU₁F : Metric.closedBall ((X.obj (σ s)).basepoint) Rnext ⊆
          (U₁ : Set (X.obj (σ s)).M) :=
        Metric.closedBall_subset_ball hRnext_lt_Rmid
      have hqF1 : sepEnvelope c0F covF ≤ 1 :=
        sepEnvelope_le_one hc0F2 (le_trans hcovF2 (by norm_num : (1 / 2 : ℝ) ≤ 1))
      have hC_le_B : C ≤ B := by
        dsimp [B]
        exact le_max_left C 2
      have hcovF_out : sepEnvelope c0F covF + δF * C ≤ covNext := by
        calc
          sepEnvelope c0F covF + δF * C = δF * C + sepEnvelope c0F covF := by ring
          _ ≤ δF * B + sepEnvelope c0F covF := by
            exact add_le_add_left (mul_le_mul_of_nonneg_left hC_le_B hδF0) _
          _ = sepEnvelope c0F covF + δF * B := by ring
          _ = covNF := by rfl
          _ ≤ covNext := by
            dsimp [covNext]
            exact le_max_left _ _
      have hFclosedSep : MapMetricApproximationBoundsOn (I := I)
          (Metric.closedBall ((X.obj (σ s)).basepoint) Rnext) c0Next covNext p
          (_root_.PartialDiffeomorph.trans (I := I)
            (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s l) (Ψ (s + l)) :
              (X.obj (σ s)).M → (X.obj (σ (s + l + 1))).M)
          (X.obj (σ s)).metric (X.obj (σ (s + l + 1))).metric :=
        PartialDiffeomorphMetricApproximationBounds.transForward (I := I)
          (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s l) (Ψ (s + l))
          hU₁_source hK₂_source himg_mid hKcompactF hKU₁F hc0F2
          hfeedF0 hqF1 (sepEnvelope_c0 c0F covF) (sepEnvelope_cov c0F covF)
          hδF0 le_rfl le_rfl C hC0
          (by
            dsimp [c0Next, c0NF, sepNextC0]
            exact le_max_left _ _)
          hcovF_out
          ((exists_uniform_iterated_covariant_derivative_add_norm_bound.{u, uE, uH} (I := I) p).choose_spec.2)
          (X.obj (σ s)).metric (X.obj (σ (s + l))).metric (X.obj (σ (s + l + 1))).metric
          D₁mid D₂openF
      obtain ⟨DstepR⟩ := hΨdata s
      have hp_stepR : p ≤ s := le_trans hpj hs
      have DstepR_p := DstepR.monoOrder hp_stepR
      have hRmid_le_step : Rmid ≤ R s := hrmR s l
      have hU₁_sub_step :
          (U₁ : Set (X.obj (σ s)).M) ⊆
            Metric.closedBall ((X.obj (σ s)).basepoint) (R s) := by
        intro x hx
        exact Metric.closedBall_subset_closedBall hRmid_le_step (Metric.ball_subset_closedBall hx)
      have DstepRopen : PartialDiffeomorphMetricApproximationBounds (I := I) (U₁ : Set (X.obj (σ s)).M)
          δR δR p (Ψ s)
          (X.obj (σ s)).metric (X.obj (σ (s + 1))).metric := by
        dsimp [δR]
        exact (DstepR_p.mono hU₁_sub_step le_rfl DstepR.forward.eps_lt_one).toSeparateBounds
      let Ktail : TopologicalSpace.Opens (X.obj (σ (s + 1))).M :=
        ⟨Metric.ball ((X.obj (σ (s + 1))).basepoint)
            (ro (s + 1) l),
          (P (σ (s + 1))).isOpen_ball (X.obj (σ (s + 1)))
            ((X.obj (σ (s + 1))).basepoint)
            (ro (s + 1) l)⟩
      have hKtail_nonempty : Nonempty Ktail := by
        dsimp [Ktail]
        exact (P (σ (s + 1))).ball_nonempty (X.obj (σ (s + 1)))
          ((X.obj (σ (s + 1))).basepoint) ((hr (s + 1)).trans (hro (s + 1) l))
      have DtailR_Ktail : PartialDiffeomorphMetricApproximationBounds (I := I) (Ktail : Set (X.obj (σ (s + 1))).M)
          c0R covR p
          (chainCompOfAddEq (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ l (s + 1) (s + (l + 1))
            htail_index)
          (X.obj (σ (s + 1))).metric (X.obj (σ (s + (l + 1)))).metric := by
        exact DrevTail
      have hKtail_source : (Ktail : Set (X.obj (σ (s + 1))).M) ⊆
          (chainCompOfAddEq (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ l (s + 1) (s + (l + 1))
            htail_index).source :=
        DtailR_Ktail.source_sub
      let KmidE : Set (X.obj (σ s)).M :=
        Metric.closedEBall ((X.obj (σ s)).basepoint) (ENNReal.ofReal Rmid)
      have hclosed_mid_step : KmidE ⊆
            Metric.closedBall ((X.obj (σ s)).basepoint) (R s) := by
        dsimp [KmidE]
        rw [Metric.closedEBall_ofReal hRmid_pos.le]
        exact Metric.closedBall_subset_closedBall hRmid_le_step
      have hsrc_step_mid : KmidE ⊆ (Ψ s).source :=
        fun x hx => hΨsource s (hclosed_mid_step hx)
      have hstep_image_radius :
          Real.sqrt (1 + δR) * Rmid < ro (s + 1) l := hstepImage s l
      have himg_step_mid :
          (Ψ s : (X.obj (σ s)).M → (X.obj (σ (s + 1))).M) '' (U₁ : Set (X.obj (σ s)).M) ⊆
            (Ktail : Set (X.obj (σ (s + 1))).M) := by
        have htmp :
            (Ψ s : (X.obj (σ s)).M → (X.obj (σ (s + 1))).M) ''
                Metric.ball ((X.obj (σ s)).basepoint) Rmid ⊆
              Metric.ball ((Ψ s : (X.obj (σ s)).M → (X.obj (σ (s + 1))).M)
                  ((X.obj (σ s)).basepoint))
                (ro (s + 1) l) :=
          MapMetricApproximationOn.image_metric_ball_subset_of_closedEBall_subset (I := I) (Ψ s)
            (by
              intro x v
              exact (Geometry.Riemannian.isMetricNorm_of_riemannianBundle
                (I := I) (X.obj (σ s)).metric) x v)
            (by
              intro x v
              exact (Geometry.Riemannian.isMetricNorm_of_riemannianBundle
                (I := I) (X.obj (σ (s + 1))).metric) x v)
            hRmid_pos le_rfl hδR0 hstep_image_radius hclosed_mid_step DstepR_p.forward
            hsrc_step_mid
        intro y hy
        simpa [Ktail, hΨbase s] using htmp hy
      have hqR1 : sepEnvelope c0R covR ≤ 1 :=
        sepEnvelope_le_one hc0R2 (le_trans hcovR2 (by norm_num : (1 / 2 : ℝ) ≤ 1))
      have hcovR_out : sepEnvelope c0R covR + δR * C ≤ covNext := by
        calc
          sepEnvelope c0R covR + δR * C = δR * C + sepEnvelope c0R covR := by ring
          _ ≤ δR * B + sepEnvelope c0R covR := by
            exact add_le_add_left (mul_le_mul_of_nonneg_left hC_le_B hδR0) _
          _ = sepEnvelope c0R covR + δR * B := by ring
          _ = covNR := by rfl
          _ ≤ covNext := by
            dsimp [covNext]
            exact le_max_right _ _
      have hRclosedSep : MapMetricApproximationBoundsOn (I := I)
          ((_root_.PartialDiffeomorph.trans (I := I) (Ψ s)
              (chainCompOfAddEq (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ l (s + 1) (s + (l + 1))
                htail_index) :
                (X.obj (σ s)).M → (X.obj (σ (s + (l + 1)))).M) ''
            Metric.closedBall ((X.obj (σ s)).basepoint) Rnext) c0Next covNext p
          ((_root_.PartialDiffeomorph.trans (I := I) (Ψ s)
              (chainCompOfAddEq (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ l (s + 1) (s + (l + 1))
                htail_index)).symm :
                (X.obj (σ (s + (l + 1)))).M → (X.obj (σ s)).M)
          (X.obj (σ (s + (l + 1)))).metric (X.obj (σ s)).metric :=
        PartialDiffeomorphMetricApproximationBounds.transReverse (I := I)
          (Ψ s) (chainCompOfAddEq (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ l (s + 1) (s + (l + 1))
            htail_index)
          DstepRopen.source_sub hKtail_source himg_step_mid hKcompactF hKU₁F hc0R2
          hfeedR0 hqR1 (sepEnvelope_c0 c0R covR) (sepEnvelope_cov c0R covR)
          hδR0 le_rfl le_rfl C hC0
          (by
            dsimp [c0Next, c0NR, sepNextC0]
            exact le_max_right _ _)
          hcovR_out
          ((exists_uniform_iterated_covariant_derivative_add_norm_bound.{u, uE, uH} (I := I) p).choose_spec.2)
          (X.obj (σ s)).metric (X.obj (σ (s + 1))).metric (X.obj (σ (s + (l + 1)))).metric
          DstepRopen DtailR_Ktail
      refine ⟨c0Next, covNext, hc0Next0, hcovNext0, hc0Nextε, hcovNextε,
        hc0NextHalf, hcovNextHalf, hc0NextBudget, hcovNextBudget, ?_⟩
      have hfoldF_eq :
          (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s (l + 1) :
              (X.obj (σ s)).M → (X.obj (σ (s + (l + 1)))).M)
            =
          (_root_.PartialDiffeomorph.trans (I := I)
            (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s l) (Ψ (s + l)) :
              (X.obj (σ s)).M → (X.obj (σ (s + l + 1))).M) := by
        funext x
        rw [chainComp_apply_succ]
        rfl
      have hfoldR_eq :
          (chainCompOfAddEq (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ (l + 1) s
              (s + (l + 1)) rfl :
              (X.obj (σ s)).M → (X.obj (σ (s + (l + 1)))).M)
            =
          (_root_.PartialDiffeomorph.trans (I := I) (Ψ s)
            (chainCompOfAddEq (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ l
              (s + 1) (s + (l + 1)) htail_index) :
              (X.obj (σ s)).M → (X.obj (σ (s + (l + 1)))).M) := by
        funext x
        rw [chainCompOfAddEq_apply_succ]
        rfl
      have hsrcFchain : Metric.closedBall ((X.obj (σ s)).basepoint) Rnext ⊆
          (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s (l + 1)).source := by
        intro x hx
        exact ⟨hU₁_source (hKU₁F hx), hK₂_source (himg_mid (Set.mem_image_of_mem _ (hKU₁F hx)))⟩
      have hsrcRchain : Metric.closedBall ((X.obj (σ s)).basepoint) Rnext ⊆
          (chainCompOfAddEq (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ (l + 1) s
            (s + (l + 1)) rfl).source := by
        intro x hx
        exact ⟨DstepRopen.source_sub (hKU₁F hx),
          hKtail_source (himg_step_mid (Set.mem_image_of_mem _ (hKU₁F hx)))⟩
      have hfoldR_symm_eq :
          ((chainCompOfAddEq (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ (l + 1) s
              (s + (l + 1)) rfl).symm :
              (X.obj (σ (s + (l + 1)))).M → (X.obj (σ s)).M)
            =
          ((_root_.PartialDiffeomorph.trans (I := I) (Ψ s)
            (chainCompOfAddEq (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ l
              (s + 1) (s + (l + 1)) htail_index)).symm :
              (X.obj (σ (s + (l + 1)))).M → (X.obj (σ s)).M) := by
        rfl
      have hFclosed : MapMetricApproximationBoundsOn (I := I)
          (Metric.closedBall ((X.obj (σ s)).basepoint) Rnext) c0Next covNext p
          (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s (l + 1) :
            (X.obj (σ s)).M → (X.obj (σ (s + (l + 1)))).M)
          (X.obj (σ s)).metric (X.obj (σ (s + (l + 1)))).metric :=
        hFclosedSep.congrEq hfoldF_eq
      have hRclosed : MapMetricApproximationBoundsOn (I := I)
          ((chainCompOfAddEq (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ (l + 1) s
              (s + (l + 1)) rfl :
              (X.obj (σ s)).M → (X.obj (σ (s + (l + 1)))).M) ''
            Metric.closedBall ((X.obj (σ s)).basepoint) Rnext) c0Next covNext p
          ((chainCompOfAddEq (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ (l + 1) s
            (s + (l + 1)) rfl).symm :
            (X.obj (σ (s + (l + 1)))).M → (X.obj (σ s)).M)
          (X.obj (σ (s + (l + 1)))).metric (X.obj (σ s)).metric := by
        simpa [hfoldR_eq] using
          hRclosedSep.congrEq hfoldR_symm_eq
      have hLR_eq :
          (chainCompOfAddEq (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ (l + 1) s
              (s + (l + 1)) rfl :
              (X.obj (σ s)).M → (X.obj (σ (s + (l + 1)))).M)
            =
          (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s (l + 1) :
              (X.obj (σ s)).M → (X.obj (σ (s + (l + 1)))).M) :=
        (chainComp_eq_right (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ (l + 1) s).symm
      have hRightForward : MapMetricApproximationBoundsOn (I := I)
          (Metric.closedBall ((X.obj (σ s)).basepoint) Rnext) c0Next covNext p
          (chainCompOfAddEq (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ (l + 1) s
            (s + (l + 1)) rfl :
            (X.obj (σ s)).M → (X.obj (σ (s + (l + 1)))).M)
          (X.obj (σ s)).metric (X.obj (σ (s + (l + 1)))).metric :=
        hFclosed.congrEq hLR_eq
      have hRightClosed :
          PartialDiffeomorphMetricApproximationBounds (I := I)
            (Metric.closedBall ((X.obj (σ s)).basepoint) Rnext) c0Next covNext p
            (chainCompOfAddEq (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ (l + 1) s
              (s + (l + 1)) rfl)
            (X.obj (σ s)).metric (X.obj (σ (s + (l + 1)))).metric :=
        PartialDiffeomorphMetricApproximationBounds.ofParts hsrcRchain hRightForward hRclosed
      have hU₁_sourceRchain : (U₁ : Set (X.obj (σ s)).M) ⊆
          (chainCompOfAddEq (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ (l + 1) s
            (s + (l + 1)) rfl).source := by
        intro x hx
        exact ⟨DstepRopen.source_sub hx,
          hKtail_source (himg_step_mid (Set.mem_image_of_mem _ hx))⟩
      have hU₁_sourceFchain : (U₁ : Set (X.obj (σ s)).M) ⊆
          (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s (l + 1)).source := by
        intro x hx
        exact ⟨hU₁_source hx, hK₂_source (himg_mid (Set.mem_image_of_mem _ hx))⟩
      have hNonempty_source_s : Nonempty (X.obj (σ s)).M := ⟨(X.obj (σ s)).basepoint⟩
      have hrev_germ_final :
          ∀ y ∈ (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s (l + 1) :
                (X.obj (σ s)).M → (X.obj (σ (s + (l + 1)))).M) ''
                Metric.closedBall ((X.obj (σ s)).basepoint) Rnext,
            ((chainCompOfAddEq (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ (l + 1) s
                (s + (l + 1)) rfl).symm :
                (X.obj (σ (s + (l + 1)))).M → (X.obj (σ s)).M)
              =ᶠ[nhds y]
            ((chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s (l + 1)).symm :
                (X.obj (σ (s + (l + 1)))).M → (X.obj (σ s)).M) := by
        have hgermU :=
          PartialDiffeomorph.symm_eventuallyEq_on_image_of_eq (I := I)
            (Φ := chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s (l + 1))
            (Ψ := chainCompOfAddEq (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ (l + 1) s
              (s + (l + 1)) rfl)
            hU₁_sourceFchain hU₁_sourceRchain hLR_eq
        intro y hy
        exact hgermU y (Set.image_mono hKU₁F hy)
      have hR_on_left_zone : MapMetricApproximationBoundsOn (I := I)
          ((chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s (l + 1) :
              (X.obj (σ s)).M → (X.obj (σ (s + (l + 1)))).M) ''
            Metric.closedBall ((X.obj (σ s)).basepoint) Rnext) c0Next covNext p
          ((chainCompOfAddEq (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ (l + 1) s
            (s + (l + 1)) rfl).symm :
            (X.obj (σ (s + (l + 1)))).M → (X.obj (σ s)).M)
          (X.obj (σ (s + (l + 1)))).metric (X.obj (σ s)).metric := by
        simpa [hLR_eq] using hRclosed
      have hLeftReverse : MapMetricApproximationBoundsOn (I := I)
          ((chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s (l + 1) :
              (X.obj (σ s)).M → (X.obj (σ (s + (l + 1)))).M) ''
            Metric.closedBall ((X.obj (σ s)).basepoint) Rnext) c0Next covNext p
          ((chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s (l + 1)).symm :
            (X.obj (σ (s + (l + 1)))).M → (X.obj (σ s)).M)
          (X.obj (σ (s + (l + 1)))).metric (X.obj (σ s)).metric :=
        hR_on_left_zone.congr (fun y hy => (hrev_germ_final y hy).symm)
      have hLeftClosed :
          PartialDiffeomorphMetricApproximationBounds (I := I)
            (Metric.closedBall ((X.obj (σ s)).basepoint) Rnext) c0Next covNext p
            (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s (l + 1))
            (X.obj (σ s)).metric (X.obj (σ (s + (l + 1)))).metric :=
        PartialDiffeomorphMetricApproximationBounds.ofParts hsrcFchain hFclosed hLeftReverse
      have hLeftOpen :
          PartialDiffeomorphMetricApproximationBounds (I := I)
            (Metric.ball ((X.obj (σ s)).basepoint) Rnext) c0Next covNext p
            (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s (l + 1))
            (X.obj (σ s)).metric (X.obj (σ (s + (l + 1)))).metric :=
        hLeftClosed.mono Metric.ball_subset_closedBall le_rfl le_rfl
      have hRightOpen :
          PartialDiffeomorphMetricApproximationBounds (I := I)
            (Metric.ball ((X.obj (σ s)).basepoint) Rnext) c0Next covNext p
            (chainCompOfAddEq (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ (l + 1) s
              (s + (l + 1)) rfl)
            (X.obj (σ s)).metric (X.obj (σ (s + (l + 1)))).metric :=
        hRightClosed.mono Metric.ball_subset_closedBall le_rfl le_rfl
      exact ⟨⟨by simpa [Rnext] using hLeftOpen⟩, fun m hm => by
        cases hm
        exact ⟨by simpa [Rnext] using hRightOpen⟩⟩


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem exists_directed_approximate_isometry_subsequence (P : ∀ k, ProperMetricOn (I := I) (X.obj k))
    (B : HasPairwiseApproximateIsometries (X := X) P) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      (letI : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
       letI : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
       letI : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
       letI : ∀ j, T2Space (X.obj (σ j)).M := fun j => (X.obj (σ j)).t2
       letI : ∀ j, SigmaCompactSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).sigmaCompact
       letI : ∀ j, MetricSpace (X.obj (σ j)).M := fun j => (P (σ j)).ms
       ∃ Ψ : ∀ j, PartialDiffeomorph I I (X.obj (σ j)).M (X.obj (σ (j + 1))).M
          (∞ : WithTop ℕ∞),
        (∀ j, (Ψ j : (X.obj (σ j)).M → (X.obj (σ (j + 1))).M) ((X.obj (σ j)).basepoint)
            = (X.obj (σ (j + 1))).basepoint) ∧
        ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ p : ℕ, ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → ∀ l : ℕ,
          Nonempty (PartialDiffeomorphMetricApproximation (I := I)
            (Metric.closedBall ((X.obj (σ j)).basepoint) ((2 : ℝ) ^ j)) ε p
            (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ j l)
            (X.obj (σ j)).metric (X.obj (σ (j + l))).metric)) := by
  obtain ⟨σ, hσ, hout⟩ := exists_directed_approximations_on_buffered_balls P
    (fun j => (2 : ℝ) ^ j) (fun j => (2 : ℝ) ^ (j + 1)) (fun _ => 1 / 2)
    openRadius midRadius (fun _ => by positivity) (fun _ => by positivity)
    two_pow_lt_openRadius openRadius_succ_lt_midRadius midRadius_lt_openRadius
    midRadius_le_two_pow_succ (fun _ => by norm_num)
    (fun _ _ _ h _ => h)
    (fun j l => sqrt_one_add_mul_midRadius_lt_two_pow j l (by norm_num) (by norm_num))
    (fun j l => sqrt_one_add_mul_midRadius_lt_next_openRadius j l (by positivity)
      (half_pow_succ_le_half j)) (fun j =>
      HasPairwiseApproximateIsometries.exists_partial_approximate_isometry P B
        ((2 : ℝ) ^ (j + 1)) (by positivity) ((1 / 2 : ℝ) ^ (j + 1)) (by positivity)
        (pow_lt_one₀ (by norm_num) (by norm_num) (by omega)) j)
  refine ⟨σ, hσ, ?_⟩
  let : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
  let : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
  let : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
  let : ∀ j, T2Space (X.obj (σ j)).M := fun j => (X.obj (σ j)).t2
  let : ∀ j, SigmaCompactSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).sigmaCompact
  let : ∀ j, MetricSpace (X.obj (σ j)).M := fun j => (P (σ j)).ms
  obtain ⟨Ψ, hbase, happrox⟩ := hout
  refine ⟨Ψ, hbase, fun ε hε hε1 p => ?_⟩
  obtain ⟨j₀, hj₀⟩ := happrox ε hε hε1 p
  refine ⟨j₀, fun j hj l => ?_⟩
  obtain ⟨D⟩ := hj₀ j hj l
  exact ⟨D.toMetricApproximation hε hε1 (min_le_left _ _) le_rfl⟩

private def finiteRadius (rho : ℝ) (j : ℕ) : ℝ := rho * Real.exp (-4 * (1 / 2 : ℝ) ^ j)
private def finiteOpenRadius (rho : ℝ) (j l : ℕ) : ℝ :=
  rho * Real.exp ((-4 + (1 / 2 : ℝ) ^ (l + 1)) * (1 / 2 : ℝ) ^ j)
private def finiteMidRadius (rho : ℝ) (j l : ℕ) : ℝ :=
  rho * Real.exp ((-4 + ((1 / 2 : ℝ) ^ (l + 1) + (1 / 2 : ℝ) ^ (l + 2)) / 2) *
    (1 / 2 : ℝ) ^ j)
private def finiteRadiusError (j : ℕ) : ℝ := min (1 / 2) (2 * (1 / 2 : ℝ) ^ j)

private theorem finiteRadius_pos {rho : ℝ} (hrho : 0 < rho) (j : ℕ) : 0 < finiteRadius rho j := by
  unfold finiteRadius
  positivity

private theorem finiteRadius_lt {rho : ℝ} (hrho : 0 < rho) (j : ℕ) : finiteRadius rho j < rho := by
  unfold finiteRadius
  exact mul_lt_of_lt_one_right hrho (Real.exp_lt_one_iff.mpr (by nlinarith [show (0 : ℝ) < (1 / 2 : ℝ) ^ j by positivity]))

private theorem finiteRadius_lt_open {rho : ℝ} (hrho : 0 < rho) (j l : ℕ) :
    finiteRadius rho j < finiteOpenRadius rho j l := by
  apply mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr _) hrho
  have := mul_pos (show (0 : ℝ) < (1 / 2 : ℝ) ^ (l + 1) by positivity)
    (show (0 : ℝ) < (1 / 2 : ℝ) ^ j by positivity)
  nlinarith

private theorem finiteOpenRadius_lt_mid {rho : ℝ} (hrho : 0 < rho) (j l : ℕ) :
    finiteOpenRadius rho j (l + 1) < finiteMidRadius rho j l := by
  apply mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr _) hrho
  have hx : (0 : ℝ) < (1 / 2 : ℝ) ^ j := by positivity
  have hy : (0 : ℝ) < (1 / 2 : ℝ) ^ (l + 1) := by positivity
  simp only [pow_succ] at *
  nlinarith [mul_pos hx hy]

private theorem finiteMidRadius_lt_open {rho : ℝ} (hrho : 0 < rho) (j l : ℕ) :
    finiteMidRadius rho j l < finiteOpenRadius rho j l := by
  apply mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr _) hrho
  have hx : (0 : ℝ) < (1 / 2 : ℝ) ^ j := by positivity
  have hy : (0 : ℝ) < (1 / 2 : ℝ) ^ (l + 1) := by positivity
  simp only [pow_succ] at *
  nlinarith [mul_pos hx hy]

private theorem finiteMidRadius_le_next {rho : ℝ} (hrho : 0 < rho) (j l : ℕ) :
    finiteMidRadius rho j l ≤ finiteRadius rho (j + 1) := by
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) hrho.le
  have hx : (0 : ℝ) < (1 / 2 : ℝ) ^ j := by positivity
  have hy := half_pow_succ_le_half l
  have hp := mul_le_mul_of_nonneg_left hy hx.le
  simp only [pow_succ] at *
  nlinarith

private theorem finiteRadiusError_pos (j : ℕ) : 0 < finiteRadiusError j := by
  unfold finiteRadiusError
  positivity

private theorem finiteRadiusError_lt_one (j : ℕ) : finiteRadiusError j < 1 :=
  (min_le_left _ _).trans_lt (by norm_num)

private theorem finiteRadiusError_budget (j l : ℕ) {c0 : ℝ}
    (hh : c0 ≤ 1 / 2) (ht : c0 ≤ 2 * sepTail j l) : c0 ≤ finiteRadiusError j :=
  le_min hh (ht.trans (mul_le_mul_of_nonneg_left (sepTail_le_half_pow j l) (by norm_num)))

private theorem sqrt_mul_exp_le {rho : ℝ} (hrho : 0 ≤ rho) (a b : ℝ) :
    Real.sqrt (1 + a) * (rho * Real.exp b) ≤ rho * Real.exp (a / 2 + b) := by
  have hs : Real.sqrt (1 + a) ≤ Real.exp (a / 2) := by
    rw [Real.exp_half]
    exact Real.sqrt_le_sqrt (by linarith [Real.add_one_le_exp a])
  calc
    _ ≤ Real.exp (a / 2) * (rho * Real.exp b) := mul_le_mul_of_nonneg_right hs (by positivity)
    _ = rho * Real.exp (a / 2 + b) := by rw [Real.exp_add]; ring

private theorem finiteMidRadius_image {rho : ℝ} (hrho : 0 < rho) (j l : ℕ) :
    Real.sqrt (1 + finiteRadiusError j) * finiteMidRadius rho j l <
      finiteRadius rho (j + l + 1) := by
  refine (sqrt_mul_exp_le hrho.le _ _).trans_lt ?_
  apply mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr _) hrho
  have hx : (0 : ℝ) < (1 / 2 : ℝ) ^ j := by positivity
  have hz : (1 / 2 : ℝ) ^ l ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hp := mul_le_mul_of_nonneg_left hz hx.le
  have he : finiteRadiusError j ≤ 2 * (1 / 2 : ℝ) ^ j := min_le_right _ _
  simp only [pow_add, pow_succ] at *
  nlinarith

private theorem finiteMidRadius_step_image {rho : ℝ} (hrho : 0 < rho) (j l : ℕ) :
    Real.sqrt (1 + (1 / 2 : ℝ) ^ (j + 1)) * finiteMidRadius rho j l <
      finiteOpenRadius rho (j + 1) l := by
  refine (sqrt_mul_exp_le hrho.le _ _).trans_lt ?_
  apply mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr _) hrho
  have hx : (0 : ℝ) < (1 / 2 : ℝ) ^ j := by positivity
  have hy : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (l + 1) := by positivity
  have hy' := half_pow_succ_le_half l
  have hp := mul_le_mul_of_nonneg_left hy' hx.le
  have hp0 := mul_nonneg hy hx.le
  simp only [pow_succ] at *
  nlinarith

private theorem finiteRadius_image {rho : ℝ} (hrho : 0 < rho) (j : ℕ) :
    Real.sqrt (1 + finiteRadiusError j) * finiteRadius rho j < finiteRadius rho (j + 1) := by
  refine (sqrt_mul_exp_le hrho.le _ _).trans_lt ?_
  apply mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr _) hrho
  have hx : (0 : ℝ) < (1 / 2 : ℝ) ^ j := by positivity
  have he : finiteRadiusError j ≤ 2 * (1 / 2 : ℝ) ^ j := min_le_right _ _
  rw [pow_succ]
  linarith

private theorem finiteRadius_tendsto (rho : ℝ) : Tendsto (finiteRadius rho) atTop (nhds rho) := by
  have hp : Tendsto (fun j : ℕ => (1 / 2 : ℝ) ^ j) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  unfold finiteRadius
  simpa only [Function.comp_apply, mul_zero, Real.exp_zero, mul_one] using
    (((Real.continuous_exp.tendsto (-4 * 0)).comp (hp.const_mul (-4))).const_mul rho)

private theorem finiteRadiusError_tendsto : Tendsto finiteRadiusError atTop (nhds 0) := by
  have hp : Tendsto (fun j : ℕ => (1 / 2 : ℝ) ^ j) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  unfold finiteRadiusError
  simpa only [mul_zero, min_eq_right (by norm_num : (0 : ℝ) ≤ 1 / 2)] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (nhds (1 / 2))).min
      (hp.const_mul 2)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem exists_directed_approximate_isometry_subsequence_within_radius
    (P : ∀ k, ProperMetricOn (I := I) (X.obj k)) {rho : ℝ} (hrho : 0 < rho)
    (hB : ∀ r : ℝ, 0 < r → r < rho → ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ p : ℕ,
    ∃ k₀ : Nat, ∀ k ℓ : Nat, k₀ ≤ k → k₀ ≤ ℓ →
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (X.obj k).M := (X.obj k).t2
      letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj k).M := (X.obj k).smooth
      letI : TopologicalSpace (X.obj ℓ).M := (X.obj ℓ).topology
      letI : ChartedSpace H (X.obj ℓ).M := (X.obj ℓ).charted
      letI : IsManifold I ∞ (X.obj ℓ).M := (X.obj ℓ).smooth
      letI : T2Space (X.obj ℓ).M := (X.obj ℓ).t2
      letI : SigmaCompactSpace (X.obj ℓ).M := (X.obj ℓ).sigmaCompact
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj ℓ).M := (X.obj ℓ).smooth
      letI : MetricSpace (X.obj k).M := (P k).ms
      letI : MetricSpace (X.obj ℓ).M := (P ℓ).ms
      ∃ Phi : PartialDiffeomorph I I (X.obj k).M (X.obj ℓ).M (∞ : WithTop ℕ∞),
        Phi (X.obj k).basepoint = (X.obj ℓ).basepoint ∧
        Nonempty (PartialDiffeomorphMetricApproximation (I := I)
          (Metric.closedBall (X.obj k).basepoint r)
          ε p Phi (X.obj k).metric (X.obj ℓ).metric)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ r eta : ℕ → ℝ,
      (∀ j, 0 < r j ∧ r j < rho ∧ 0 < eta j ∧ eta j < 1 ∧
        Real.sqrt (1 + eta j) * r j < r (j + 1)) ∧
      Tendsto r atTop (nhds rho) ∧ Tendsto eta atTop (nhds 0) ∧
      (letI : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
       letI : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
       letI : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
       letI : ∀ j, T2Space (X.obj (σ j)).M := fun j => (X.obj (σ j)).t2
       letI : ∀ j, SigmaCompactSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).sigmaCompact
       letI : ∀ j, MetricSpace (X.obj (σ j)).M := fun j => (P (σ j)).ms
       ∃ Ψ : ∀ j, PartialDiffeomorph I I (X.obj (σ j)).M (X.obj (σ (j + 1))).M
          (∞ : WithTop ℕ∞),
        (∀ j, (Ψ j : (X.obj (σ j)).M → (X.obj (σ (j + 1))).M) ((X.obj (σ j)).basepoint)
            = (X.obj (σ (j + 1))).basepoint) ∧
        ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ p : ℕ, ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → ∀ l : ℕ,
          Nonempty (PartialDiffeomorphMetricApproximationBounds (I := I)
            (Metric.closedBall ((X.obj (σ j)).basepoint) (r j)) (min ε (eta j)) ε p
            (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ j l)
            (X.obj (σ j)).metric (X.obj (σ (j + l))).metric)) := by
  obtain ⟨σ, hσ, hout⟩ := exists_directed_approximations_on_buffered_balls P
    (finiteRadius rho) (fun j => finiteRadius rho (j + 1)) finiteRadiusError
    (finiteOpenRadius rho) (finiteMidRadius rho)
    (finiteRadius_pos hrho) (fun j => finiteRadius_pos hrho (j + 1))
    (finiteRadius_lt_open hrho) (finiteOpenRadius_lt_mid hrho) (finiteMidRadius_lt_open hrho)
    (finiteMidRadius_le_next hrho)
    (fun j => ⟨finiteRadiusError_pos j, finiteRadiusError_lt_one j⟩)
    (fun j l _ hh ht => finiteRadiusError_budget j l hh ht)
    (finiteMidRadius_image hrho) (finiteMidRadius_step_image hrho) (by
      intro j
      obtain ⟨N, hN⟩ := hB (finiteRadius rho (j + 1)) (finiteRadius_pos hrho _)
        (finiteRadius_lt hrho _) ((1 / 2 : ℝ) ^ (j + 1)) (by positivity)
        (pow_lt_one₀ (by norm_num) (by norm_num) (by omega)) j
      refine ⟨N, fun k l hk hl => ?_⟩
      let : TopologicalSpace (X.obj k).M := (X.obj k).topology
      let : ChartedSpace H (X.obj k).M := (X.obj k).charted
      let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      let : T2Space (X.obj k).M := (X.obj k).t2
      let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
      let : MetricSpace (X.obj k).M := (P k).ms
      let : TopologicalSpace (X.obj l).M := (X.obj l).topology
      let : ChartedSpace H (X.obj l).M := (X.obj l).charted
      let : IsManifold I ∞ (X.obj l).M := (X.obj l).smooth
      let : T2Space (X.obj l).M := (X.obj l).t2
      let : SigmaCompactSpace (X.obj l).M := (X.obj l).sigmaCompact
      let : MetricSpace (X.obj l).M := (P l).ms
      obtain ⟨Ψ, hbase, ⟨D⟩⟩ := hN k l hk hl
      exact ⟨Ψ, D.source_sub, hbase, ⟨D⟩⟩)
  exact ⟨σ, hσ, finiteRadius rho, finiteRadiusError,
    fun j => ⟨finiteRadius_pos hrho j, finiteRadius_lt hrho j, finiteRadiusError_pos j,
      finiteRadiusError_lt_one j, finiteRadius_image hrho j⟩,
    finiteRadius_tendsto rho, finiteRadiusError_tendsto, hout⟩

end Endpoint

end CheegerGromovCompactness
end DifferentialGeometry
