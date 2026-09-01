import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.PairwiseApproximateIsometry
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximationMonotonicity
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximationCongruence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximationIdentity
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricBallImage
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.DirectedSubsequenceRadii
import DifferentialGeometry.Analysis.Calculus.DiagonalSubsequence
import DifferentialGeometry.Analysis.Estimates.IteratedApproximationError
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphComposition
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology BigOperators ENNReal
open Bundle Manifold
open DifferentialGeometry.Tensor0SBundle

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

section Endpoint

private lemma sepNextC0_nonneg {c0 cov δ : ℝ} (hc0 : 0 ≤ c0) (hδ : 0 ≤ δ)
    (hfeed : 0 ≤ sepFeed c0 cov) : 0 ≤ sepNextC0 c0 cov δ := by
  unfold sepNextC0
  have h : 0 ≤ δ * (1 + sepFeed c0 cov) := mul_nonneg hδ (by linarith)
  linarith

private lemma sepNextCov_nonneg {c0 cov δ B : ℝ} (hfeed : 0 ≤ sepFeed c0 cov)
    (hδ : 0 ≤ δ) (hB : 0 ≤ B) : 0 ≤ sepNextCov c0 cov δ B := by
  unfold sepNextCov
  have h : 0 ≤ δ * B := mul_nonneg hδ hB
  linarith

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem exists_directed_approximate_isometry_subsequence (P : ∀ k, ProperMetricOn (I := I) (X.obj k))
    (B : PairwiseApproximateIsometryInput (X := X) P) :
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
  classical
  have hrpos : ∀ j : ℕ, (0 : ℝ) < (2 : ℝ) ^ (j + 1) := fun j => by positivity
  have hepos : ∀ j : ℕ, (0 : ℝ) < (1 / 2 : ℝ) ^ (j + 1) := fun j => by positivity
  have helt : ∀ j : ℕ, (1 / 2 : ℝ) ^ (j + 1) < 1 :=
    fun j => pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  set T : ℕ → ℕ := fun j =>
    (PairwiseApproximateIsometryInput.exists_partial_approximate_isometry P B ((2 : ℝ) ^ (j + 1)) (hrpos j) ((1 / 2 : ℝ) ^ (j + 1)) (hepos j)
      (helt j) j).choose with hT
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
    member_isRiemannian (X.obj (σ j)) (P (σ j))
  have hProper : ∀ j, ProperSpace (X.obj (σ j)).M := fun j => (P (σ j)).proper
  have hstep : ∀ j : ℕ, T j ≤ σ j ∧ T j ≤ σ (j + 1) := fun j =>
    ⟨hσge j, le_trans (hσge j) (le_of_lt (hσmono (Nat.lt_succ_self j)))⟩
  have hΨex : ∀ j : ℕ,
      ∃ Φ : PartialDiffeomorph I I (X.obj (σ j)).M (X.obj (σ (j + 1))).M (∞ : WithTop ℕ∞),
        Metric.closedBall ((X.obj (σ j)).basepoint) ((2 : ℝ) ^ (j + 1)) ⊆ Φ.source ∧
        (Φ : (X.obj (σ j)).M → (X.obj (σ (j + 1))).M) ((X.obj (σ j)).basepoint)
          = (X.obj (σ (j + 1))).basepoint ∧
        Nonempty (PartialDiffeomorphMetricApproximation (I := I)
          (Metric.closedBall ((X.obj (σ j)).basepoint) ((2 : ℝ) ^ (j + 1)))
          ((1 / 2 : ℝ) ^ (j + 1)) j Φ (X.obj (σ j)).metric (X.obj (σ (j + 1))).metric) :=
    fun j => (PairwiseApproximateIsometryInput.exists_partial_approximate_isometry P B ((2 : ℝ) ^ (j + 1)) (hrpos j) ((1 / 2 : ℝ) ^ (j + 1)) (hepos j)
      (helt j) j).choose_spec (σ j) (σ (j + 1)) (hstep j).1 (hstep j).2
  choose Ψ hΨsrc hΨbase hΨdata using hΨex
  refine ⟨Ψ, hΨbase, ?_⟩
  intro ε hε hε1 p
  let C : ℝ := (comp_cov_le_unif.{u, uE, uH} (I := I) p).choose
  have hC0 : 0 ≤ C := (comp_cov_le_unif.{u, uE, uH} (I := I) p).choose_spec.1
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
        (Metric.ball ((X.obj (σ s)).basepoint) ((2 : ℝ) ^ s * (1 + (1 / 2 : ℝ) ^ (l + 1)))) c0 cov p
        (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s l)
        (X.obj (σ s)).metric (X.obj (σ (s + l))).metric) ∧
      (∀ m (hm : s + l = m), Nonempty (PartialDiffeomorphMetricApproximationBounds (I := I)
        (Metric.ball ((X.obj (σ s)).basepoint) ((2 : ℝ) ^ s * (1 + (1 / 2 : ℝ) ^ (l + 1)))) c0 cov p
        (chainComp' (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ l s m hm)
        (X.obj (σ s)).metric (X.obj (σ m)).metric)) by
    intro l
    obtain ⟨c0, cov, _hc0non, _hcovnon, hc0e, hcove, _, _, _, _, ⟨⟨D⟩, _⟩⟩ :=
      hacc l j le_rfl
    have hlt : (2 : ℝ) ^ j < (2 : ℝ) ^ j * (1 + (1 / 2 : ℝ) ^ (l + 1)) := by
      have : (0 : ℝ) < (2 : ℝ) ^ j * (1 / 2 : ℝ) ^ (l + 1) := by positivity
      nlinarith [this]
    exact ⟨(D.mono (Metric.closedBall_subset_ball hlt) le_rfl le_rfl).toMetricApproximation hε hε1 hc0e hcove⟩
  intro l
  induction l with
  | zero =>
      intro s _hs
      refine ⟨0, 0, le_rfl, le_rfl, le_of_lt hε, le_of_lt hε, by norm_num, by norm_num,
        ?_, ?_, ?_⟩
      · simp [sepTail]
      · simp [sepTail]
      · exact ⟨
          reflSepData (I := I)
            (Metric.ball ((X.obj (σ s)).basepoint) ((2 : ℝ) ^ s * (1 + (1 / 2 : ℝ) ^ (0 + 1))))
            (X.obj (σ s)).metric p,
          fun m hm => by
            cases hm
            exact reflSepData (I := I)
              (Metric.ball ((X.obj (σ s)).basepoint) ((2 : ℝ) ^ s * (1 + (1 / 2 : ℝ) ^ (0 + 1))))
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
      have hδRpos : 0 < δR := by
        dsimp [δR]
        positivity
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
            rw [sepTail_succ']
            ring
      have hcovNRbudget : covNR ≤ sepBeta B * sepTail s (l + 1) := by
        dsimp [covNR]
        calc
          sepNextCov c0R covR δR B ≤ sepBeta B * (sepTail (s + 1) l + δR) :=
            sepNextCov_le hTR0 hδR0 hc0R0 hc0Rbudget hcovRbudget hTRsmall
          _ = sepBeta B * sepTail s (l + 1) := by
            dsimp [δR]
            rw [sepTail_succ']
            ring
      have hc0NextBudget : c0Next ≤ 2 * sepTail s (l + 1) := by
        dsimp [c0Next]
        exact max_le hc0NFbudget hc0NRbudget
      have hcovNextBudget : covNext ≤ sepBeta B * sepTail s (l + 1) := by
        dsimp [covNext]
        exact max_le hcovNFbudget hcovNRbudget
      have hfeedF0 : 0 ≤ sepFeed c0F covF :=
        sepFeed_nonneg hc0F0 (lt_of_le_of_lt hc0F2 (by norm_num))
      have hfeedR0 : 0 ≤ sepFeed c0R covR :=
        sepFeed_nonneg hc0R0 (lt_of_le_of_lt hc0R2 (by norm_num))
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
      let Rcur : ℝ := (2 : ℝ) ^ s * (1 + (1 / 2 : ℝ) ^ (l + 1))
      let Rnext : ℝ := (2 : ℝ) ^ s * (1 + (1 / 2 : ℝ) ^ (l + 2))
      let Rmid : ℝ := midRad s l
      have hRnext_pos : 0 < Rnext := by
        dsimp [Rnext]
        positivity
      have hRmid_pos : 0 < Rmid := by
        dsimp [Rmid, midRad]
        positivity
      have hRnext_lt_Rmid : Rnext < Rmid := by
        simpa [Rnext, Rmid] using openRad_next_lt_mid s l
      have hRmid_lt_Rcur : Rmid < Rcur := by
        simpa [Rmid, Rcur] using midRad_lt_openRad s l
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
        ⟨Metric.ball ((X.obj (σ (s + l))).basepoint) ((2 : ℝ) ^ (s + l + 1)),
          by
            have hb :
                @IsOpen (X.obj (σ (s + l))).M
                  (P (σ (s + l))).ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
                  (Metric.ball ((X.obj (σ (s + l))).basepoint) ((2 : ℝ) ^ (s + l + 1))) := by
              let : MetricSpace (X.obj (σ (s + l))).M := (P (σ (s + l))).ms
              exact Metric.isOpen_ball
            rwa [ProperMetricOn.top_eq (X.obj (σ (s + l))) (P (σ (s + l)))] at hb⟩
      have hU₁_nonempty : Nonempty U₁ :=
        ⟨⟨(X.obj (σ s)).basepoint, Metric.mem_ball_self hRmid_pos⟩⟩
      have hK₂_nonempty : Nonempty K₂ :=
        ⟨⟨(X.obj (σ (s + l))).basepoint,
          Metric.mem_ball_self (by positivity : (0 : ℝ) < (2 : ℝ) ^ (s + l + 1))⟩⟩
      have hU₁_src : (U₁ : Set (X.obj (σ s)).M) ⊆
          (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s l).source := by
        intro x hx
        exact DforAcc.source_sub (Metric.ball_subset_ball hRmid_lt_Rcur.le hx)
      have hK₂_src : (K₂ : Set (X.obj (σ (s + l))).M) ⊆ (Ψ (s + l)).source := by
        intro y hy
        exact hΨsrc (s + l) (Metric.ball_subset_closedBall hy)
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
        exact ((DstepF.monoP hp_stepF).mono Metric.ball_subset_closedBall le_rfl
          DstepF.forward.eps_lt_one).toSeparateBounds
      have hclosed_mid_sub :
          Metric.closedEBall ((X.obj (σ s)).basepoint) (ENNReal.ofReal Rmid) ⊆
            Metric.ball ((X.obj (σ s)).basepoint) Rcur :=
        closedEBall_ofReal_subset_ball ((X.obj (σ s)).basepoint)
          (le_of_lt hRmid_pos) hRmid_lt_Rcur
      have hdata_mid : MapMetricApproximationOn (I := I)
          (Metric.closedEBall ((X.obj (σ s)).basepoint) (ENNReal.ofReal Rmid)) (1 / 2) p
          (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s l :
            (X.obj (σ s)).M → (X.obj (σ (s + l))).M)
          (X.obj (σ s)).metric (X.obj (σ (s + l))).metric :=
        (DforAcc.forward.mono hclosed_mid_sub le_rfl le_rfl).toMetricApproximation
          (by norm_num) (by norm_num) hc0F2 hcovF2
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
            Metric.ball ((X.obj (σ (s + l))).basepoint) ((2 : ℝ) ^ (s + l + 1)) := by
        have htmp :
            (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s l :
                (X.obj (σ s)).M → (X.obj (σ (s + l))).M) ''
                Metric.ball ((X.obj (σ s)).basepoint) Rmid ⊆
              Metric.ball
                ((chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s l :
                    (X.obj (σ s)).M → (X.obj (σ (s + l))).M)
                  ((X.obj (σ s)).basepoint))
                ((2 : ℝ) ^ (s + l + 1)) :=
          data_image_metric_ball (I := I)
            (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s l)
            (by
              intro x v
              exact (Geometry.Riemannian.isMetricNorm_of_riemannianBundle
                (I := I) (X.obj (σ s)).metric) x v)
            (by
              intro x v
              exact (Geometry.Riemannian.isMetricNorm_of_riemannianBundle
                (I := I) (X.obj (σ (s + l))).metric) x v)
            hRmid_pos le_rfl (by norm_num : (0 : ℝ) ≤ 1 / 2)
            (by
              simpa [Rmid] using
                (imageMid_lt_step (a := (1 / 2 : ℝ)) s l
                  (by norm_num) (by norm_num)))
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
      have hqF1 : sepFeed c0F covF ≤ 1 :=
        sepFeed_le_one hc0F2 (le_trans hcovF2 (by norm_num : (1 / 2 : ℝ) ≤ 1))
      have hC_le_B : C ≤ B := by
        dsimp [B]
        exact le_max_left C 2
      have hcovF_out : sepFeed c0F covF + δF * C ≤ covNext := by
        calc
          sepFeed c0F covF + δF * C = δF * C + sepFeed c0F covF := by ring
          _ ≤ δF * B + sepFeed c0F covF := by
            exact add_le_add_left (mul_le_mul_of_nonneg_left hC_le_B hδF0) _
          _ = sepFeed c0F covF + δF * B := by ring
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
        compSepFwd (I := I)
          (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s l) (Ψ (s + l))
          hU₁_src hK₂_src himg_mid hKcompactF hKU₁F hc0F2
          hfeedF0 hqF1 (sepFeed_c0 c0F covF) (sepFeed_cov c0F covF)
          hδF0 le_rfl le_rfl C hC0
          (by
            dsimp [c0Next, c0NF, sepNextC0]
            exact le_max_left _ _)
          hcovF_out
          ((comp_cov_le_unif.{u, uE, uH} (I := I) p).choose_spec.2)
          (X.obj (σ s)).metric (X.obj (σ (s + l))).metric (X.obj (σ (s + l + 1))).metric
          D₁mid D₂openF
      obtain ⟨DstepR⟩ := hΨdata s
      have hp_stepR : p ≤ s := le_trans hpj hs
      have DstepR_p := DstepR.monoP hp_stepR
      have hstepR_half : δR ≤ 1 / 2 := by
        dsimp [δR]
        exact half_pow_succ_le_half s
      have hRmid_le_step : Rmid ≤ (2 : ℝ) ^ (s + 1) := by
        change midRad s l ≤ (2 : ℝ) ^ (s + 1)
        exact midRad_le_step s l
      have hU₁_sub_step :
          (U₁ : Set (X.obj (σ s)).M) ⊆
            Metric.closedBall ((X.obj (σ s)).basepoint) ((2 : ℝ) ^ (s + 1)) := by
        intro x hx
        exact Metric.closedBall_subset_closedBall hRmid_le_step (Metric.ball_subset_closedBall hx)
      have DstepRopen : PartialDiffeomorphMetricApproximationBounds (I := I) (U₁ : Set (X.obj (σ s)).M)
          δR δR p (Ψ s)
          (X.obj (σ s)).metric (X.obj (σ (s + 1))).metric := by
        dsimp [δR]
        exact (DstepR_p.mono hU₁_sub_step le_rfl DstepR.forward.eps_lt_one).toSeparateBounds
      let Ktail : TopologicalSpace.Opens (X.obj (σ (s + 1))).M :=
        ⟨Metric.ball ((X.obj (σ (s + 1))).basepoint)
            ((2 : ℝ) ^ (s + 1) * (1 + (1 / 2 : ℝ) ^ (l + 1))),
          properMetric_isOpen_ball (I := I) (X.obj (σ (s + 1))) (P (σ (s + 1)))
            ((X.obj (σ (s + 1))).basepoint)
            ((2 : ℝ) ^ (s + 1) * (1 + (1 / 2 : ℝ) ^ (l + 1)))⟩
      have hKtail_nonempty : Nonempty Ktail := by
        dsimp [Ktail]
        exact properMetric_ball_nonempty (I := I) (X.obj (σ (s + 1))) (P (σ (s + 1)))
          ((X.obj (σ (s + 1))).basepoint) (openRad_pos (s + 1) l)
      have DtailR_Ktail : PartialDiffeomorphMetricApproximationBounds (I := I) (Ktail : Set (X.obj (σ (s + 1))).M)
          c0R covR p
          (chainComp' (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ l (s + 1) (s + (l + 1))
            htail_index)
          (X.obj (σ (s + 1))).metric (X.obj (σ (s + (l + 1)))).metric := by
        exact DrevTail
      have hKtail_src : (Ktail : Set (X.obj (σ (s + 1))).M) ⊆
          (chainComp' (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ l (s + 1) (s + (l + 1))
            htail_index).source :=
        DtailR_Ktail.source_sub
      let KmidE : Set (X.obj (σ s)).M :=
        Metric.closedEBall ((X.obj (σ s)).basepoint) (ENNReal.ofReal Rmid)
      have hclosed_mid_step : KmidE ⊆
            Metric.closedBall ((X.obj (σ s)).basepoint) ((2 : ℝ) ^ (s + 1)) := by
        dsimp [KmidE]
        rw [Metric.closedEBall_ofReal hRmid_pos.le]
        exact Metric.closedBall_subset_closedBall hRmid_le_step
      have hsrc_step_mid : KmidE ⊆ (Ψ s).source :=
        fun x hx => hΨsrc s (hclosed_mid_step hx)
      have hRmid_le_mid0 : Rmid ≤ midRad s 0 := by
        change midRad s l ≤ midRad s 0
        exact midRad_le_mid0 s l
      have hstep_image_radius :
          Real.sqrt (1 + δR) * Rmid
            < (2 : ℝ) ^ (s + 1) * (1 + (1 / 2 : ℝ) ^ (l + 1)) := by
        change Real.sqrt (1 + δR) * midRad s l
          < (2 : ℝ) ^ (s + 1) * (1 + (1 / 2 : ℝ) ^ (l + 1))
        exact imageMid_lt_openRad s l hδRpos hstepR_half
      have himg_step_mid :
          (Ψ s : (X.obj (σ s)).M → (X.obj (σ (s + 1))).M) '' (U₁ : Set (X.obj (σ s)).M) ⊆
            (Ktail : Set (X.obj (σ (s + 1))).M) := by
        have htmp :
            (Ψ s : (X.obj (σ s)).M → (X.obj (σ (s + 1))).M) ''
                Metric.ball ((X.obj (σ s)).basepoint) Rmid ⊆
              Metric.ball ((Ψ s : (X.obj (σ s)).M → (X.obj (σ (s + 1))).M)
                  ((X.obj (σ s)).basepoint))
                ((2 : ℝ) ^ (s + 1) * (1 + (1 / 2 : ℝ) ^ (l + 1))) :=
          data_image_metric_ball_of_superset (I := I) (Ψ s)
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
      have hqR1 : sepFeed c0R covR ≤ 1 :=
        sepFeed_le_one hc0R2 (le_trans hcovR2 (by norm_num : (1 / 2 : ℝ) ≤ 1))
      have hcovR_out : sepFeed c0R covR + δR * C ≤ covNext := by
        calc
          sepFeed c0R covR + δR * C = δR * C + sepFeed c0R covR := by ring
          _ ≤ δR * B + sepFeed c0R covR := by
            exact add_le_add_left (mul_le_mul_of_nonneg_left hC_le_B hδR0) _
          _ = sepFeed c0R covR + δR * B := by ring
          _ = covNR := by rfl
          _ ≤ covNext := by
            dsimp [covNext]
            exact le_max_right _ _
      have hRclosedSep : MapMetricApproximationBoundsOn (I := I)
          ((_root_.PartialDiffeomorph.trans (I := I) (Ψ s)
              (chainComp' (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ l (s + 1) (s + (l + 1))
                htail_index) :
                (X.obj (σ s)).M → (X.obj (σ (s + (l + 1)))).M) ''
            Metric.closedBall ((X.obj (σ s)).basepoint) Rnext) c0Next covNext p
          ((_root_.PartialDiffeomorph.trans (I := I) (Ψ s)
              (chainComp' (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ l (s + 1) (s + (l + 1))
                htail_index)).symm :
                (X.obj (σ (s + (l + 1)))).M → (X.obj (σ s)).M)
          (X.obj (σ (s + (l + 1)))).metric (X.obj (σ s)).metric :=
        compSepRev (I := I)
          (Ψ s) (chainComp' (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ l (s + 1) (s + (l + 1))
            htail_index)
          DstepRopen.source_sub hKtail_src himg_step_mid hKcompactF hKU₁F hc0R2
          hfeedR0 hqR1 (sepFeed_c0 c0R covR) (sepFeed_cov c0R covR)
          hδR0 le_rfl le_rfl C hC0
          (by
            dsimp [c0Next, c0NR, sepNextC0]
            exact le_max_right _ _)
          hcovR_out
          ((comp_cov_le_unif.{u, uE, uH} (I := I) p).choose_spec.2)
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
          (chainComp' (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ (l + 1) s
              (s + (l + 1)) rfl :
              (X.obj (σ s)).M → (X.obj (σ (s + (l + 1)))).M)
            =
          (_root_.PartialDiffeomorph.trans (I := I) (Ψ s)
            (chainComp' (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ l
              (s + 1) (s + (l + 1)) htail_index) :
              (X.obj (σ s)).M → (X.obj (σ (s + (l + 1)))).M) := by
        funext x
        rw [chainComp'_apply_succ]
        rfl
      have hsrcFchain : Metric.closedBall ((X.obj (σ s)).basepoint) Rnext ⊆
          (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s (l + 1)).source := by
        intro x hx
        exact ⟨hU₁_src (hKU₁F hx), hK₂_src (himg_mid (Set.mem_image_of_mem _ (hKU₁F hx)))⟩
      have hsrcRchain : Metric.closedBall ((X.obj (σ s)).basepoint) Rnext ⊆
          (chainComp' (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ (l + 1) s
            (s + (l + 1)) rfl).source := by
        intro x hx
        exact ⟨DstepRopen.source_sub (hKU₁F hx),
          hKtail_src (himg_step_mid (Set.mem_image_of_mem _ (hKU₁F hx)))⟩
      have hfoldR_symm_eq :
          ((chainComp' (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ (l + 1) s
              (s + (l + 1)) rfl).symm :
              (X.obj (σ (s + (l + 1)))).M → (X.obj (σ s)).M)
            =
          ((_root_.PartialDiffeomorph.trans (I := I) (Ψ s)
            (chainComp' (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ l
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
          ((chainComp' (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ (l + 1) s
              (s + (l + 1)) rfl :
              (X.obj (σ s)).M → (X.obj (σ (s + (l + 1)))).M) ''
            Metric.closedBall ((X.obj (σ s)).basepoint) Rnext) c0Next covNext p
          ((chainComp' (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ (l + 1) s
            (s + (l + 1)) rfl).symm :
            (X.obj (σ (s + (l + 1)))).M → (X.obj (σ s)).M)
          (X.obj (σ (s + (l + 1)))).metric (X.obj (σ s)).metric := by
        simpa [image_eq_of_fun_eq hfoldR_eq] using
          hRclosedSep.congrEq hfoldR_symm_eq
      have hLR_eq :
          (chainComp' (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ (l + 1) s
              (s + (l + 1)) rfl :
              (X.obj (σ s)).M → (X.obj (σ (s + (l + 1)))).M)
            =
          (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s (l + 1) :
              (X.obj (σ s)).M → (X.obj (σ (s + (l + 1)))).M) :=
        (chainComp_eq_right (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ (l + 1) s).symm
      have hRightForward : MapMetricApproximationBoundsOn (I := I)
          (Metric.closedBall ((X.obj (σ s)).basepoint) Rnext) c0Next covNext p
          (chainComp' (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ (l + 1) s
            (s + (l + 1)) rfl :
            (X.obj (σ s)).M → (X.obj (σ (s + (l + 1)))).M)
          (X.obj (σ s)).metric (X.obj (σ (s + (l + 1)))).metric :=
        hFclosed.congrEq hLR_eq
      have hRightClosed :
          PartialDiffeomorphMetricApproximationBounds (I := I)
            (Metric.closedBall ((X.obj (σ s)).basepoint) Rnext) c0Next covNext p
            (chainComp' (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ (l + 1) s
              (s + (l + 1)) rfl)
            (X.obj (σ s)).metric (X.obj (σ (s + (l + 1)))).metric :=
        PartialDiffeomorphMetricApproximationBounds.ofParts hsrcRchain hRightForward hRclosed
      have hU₁_srcRchain : (U₁ : Set (X.obj (σ s)).M) ⊆
          (chainComp' (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ (l + 1) s
            (s + (l + 1)) rfl).source := by
        intro x hx
        exact ⟨DstepRopen.source_sub hx,
          hKtail_src (himg_step_mid (Set.mem_image_of_mem _ hx))⟩
      have hU₁_srcFchain : (U₁ : Set (X.obj (σ s)).M) ⊆
          (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s (l + 1)).source := by
        intro x hx
        exact ⟨hU₁_src hx, hK₂_src (himg_mid (Set.mem_image_of_mem _ hx))⟩
      have hNonempty_src_s : Nonempty (X.obj (σ s)).M := ⟨(X.obj (σ s)).basepoint⟩
      have hrev_germ_final :
          ∀ y ∈ (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s (l + 1) :
                (X.obj (σ s)).M → (X.obj (σ (s + (l + 1)))).M) ''
                Metric.closedBall ((X.obj (σ s)).basepoint) Rnext,
            ((chainComp' (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ (l + 1) s
                (s + (l + 1)) rfl).symm :
                (X.obj (σ (s + (l + 1)))).M → (X.obj (σ s)).M)
              =ᶠ[nhds y]
            ((chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s (l + 1)).symm :
                (X.obj (σ (s + (l + 1)))).M → (X.obj (σ s)).M) := by
        have hgermU :=
          symm_eventuallyEq_on_image (I := I)
            (Φ := chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s (l + 1))
            (Ψ := chainComp' (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ (l + 1) s
              (s + (l + 1)) rfl)
            hU₁_srcFchain hU₁_srcRchain hLR_eq
        intro y hy
        exact hgermU y (Set.image_mono hKU₁F hy)
      have hR_on_left_zone : MapMetricApproximationBoundsOn (I := I)
          ((chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s (l + 1) :
              (X.obj (σ s)).M → (X.obj (σ (s + (l + 1)))).M) ''
            Metric.closedBall ((X.obj (σ s)).basepoint) Rnext) c0Next covNext p
          ((chainComp' (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ (l + 1) s
            (s + (l + 1)) rfl).symm :
            (X.obj (σ (s + (l + 1)))).M → (X.obj (σ s)).M)
          (X.obj (σ (s + (l + 1)))).metric (X.obj (σ s)).metric := by
        simpa [image_eq_of_fun_eq hLR_eq] using hRclosed
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
            (chainComp' (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ (l + 1) s
              (s + (l + 1)) rfl)
            (X.obj (σ s)).metric (X.obj (σ (s + (l + 1)))).metric :=
        hRightClosed.mono Metric.ball_subset_closedBall le_rfl le_rfl
      exact ⟨⟨by simpa [Rnext] using hLeftOpen⟩, fun m hm => by
        cases hm
        exact ⟨by simpa [Rnext] using hRightOpen⟩⟩

end Endpoint

end HCGCompactness
end DifferentialGeometry
