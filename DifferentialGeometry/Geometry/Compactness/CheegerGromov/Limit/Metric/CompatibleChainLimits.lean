import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.Metric.BallSystem.Images
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.Metric.BallSystem.Estimates
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Composition

open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open scoped Manifold ContDiff
open Set Topology TopologicalSpace

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable [I.Boundaryless]
variable {M : ℕ → Type u} [∀ j, MetricSpace (M j)] [∀ j, ChartedSpace H (M j)]
  [∀ j, IsManifold I ∞ (M j)] [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)]

section ApproxData

open Bundle

variable [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
variable [∀ j, IsRiemannianManifold I (M j)]
variable [NeZero (Module.finrank ℝ E)]


omit [I.Boundaryless] [∀ j, IsRiemannianManifold I (M j)]
  [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [NeZero (Module.finrank ℝ E)] in
omit [∀ (j : ℕ), SigmaCompactSpace (M j)] in
theorem chain_ball_source
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    {j : ℕ}
    (D0 : ∀ k, PartialDiffeomorphMetricApproximation (I := I)
      (Metric.closedBall (b j) ((2 : ℝ) ^ j)) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ j k) (g j) (g (j + k))) :
    ∀ k, (ballOpen b (fun n => (2 : ℝ) ^ n) j : Set (M j)) ⊆
      (chainComp (I := I) (Mf := M) Ψ j k).source := by
  intro k x hx
  apply (D0 k).source_sub
  exact Metric.mem_closedBall.mpr (Metric.mem_ball.mp hx).le

omit [NeZero (Module.finrank ℝ E)] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [I.Boundaryless] in
theorem chain_pullback_bounded
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    {j : ℕ}
    (D0 : ∀ k, PartialDiffeomorphMetricApproximation (I := I)
      (Metric.closedBall (b j) ((2 : ℝ) ^ j)) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ j k) (g j) (g (j + k)))
    (Dhi : ∀ p : ℕ, ∃ a : ℕ, 1 ≤ a ∧ ∀ c : ℕ,
      Nonempty (PartialDiffeomorphMetricApproximation (I := I)
        (Metric.closedBall (b (j + a)) ((2 : ℝ) ^ (j + a))) (1 / 2) p
        (chainComp (I := I) (Mf := M) Ψ (j + a) c)
        (g (j + a)) (g ((j + a) + c)))) :
    let U := ballOpen b (fun n => (2 : ℝ) ^ n) j
    letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
    let hU := chain_ball_source (I := I) b Ψ g D0
    let gSeq := chainPullbackSeq (I := I) Ψ g U hU
    ∃ gRef : ℕ → SmoothRiemannianMetric I U,
      (∀ r q : ℕ, q ≤ r → ∀ K : Set U, IsCompact K → ∃ C : Real,
        ∀ k : ℕ, ∀ z ∈ K,
          metricCovDerivNorm (I := I) q (gSeq k) (gRef r) z ≤ C) ∧
      ∃ c : Real, 0 < c ∧ ∀ (k : ℕ) (x : U) (v : TangentSpace I x),
        c * ((g j).restrictOpen (I := I) U).inner x v v ≤ (gSeq k).inner x v v := by
  classical
  let U := ballOpen b (fun n => (2 : ℝ) ^ n) j
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  let hU := chain_ball_source (I := I) b Ψ g D0
  let gSeq := chainPullbackSeq (I := I) Ψ g U hU
  let a : ℕ → ℕ := fun r => (Dhi r).choose
  have ha : ∀ r, 1 ≤ a r := fun r => (Dhi r).choose_spec.1
  have htail : ∀ r c, PartialDiffeomorphMetricApproximation (I := I)
      (Metric.closedBall (b (j + a r)) ((2 : ℝ) ^ (j + a r))) (1 / 2) r
      (chainComp (I := I) (Mf := M) Ψ (j + a r) c)
      (g (j + a r)) (g ((j + a r) + c)) :=
    fun r c => Classical.choice ((Dhi r).choose_spec.2 c)
  let gRef : ℕ → SmoothRiemannianMetric I U := fun r => gSeq (a r)
  refine ⟨gRef, ?_, ?_⟩
  · intro r q hqr K hK
    apply cov_bdd_of_eventual (I := I) hK q gSeq (gRef r)
    refine ⟨a r, max (2 * Real.sqrt (Module.finrank ℝ E : ℝ)) (1 / 2), ?_⟩
    intro k hk z hz
    let c := k - a r
    have hdecomp : a r + c = k := by
      dsimp only [c]
      omega
    have hpre := hU (a r)
    have himg :
        (chainComp (I := I) (Mf := M) Ψ j (a r) : M j → M (j + a r)) ''
            (U : Set (M j)) ⊆
          Metric.closedBall (b (j + a r)) ((2 : ℝ) ^ (j + a r)) := by
      simpa only [U, ballOpen, Opens.coe_mk] using
        chain_image_ball (I := I) b Ψ hbase g hnorm (ha r) (D0 (a r))
    have hnext :
        (chainComp (I := I) (Mf := M) Ψ j (a r) : M j → M (j + a r)) ''
            (U : Set (M j)) ⊆
          (chainComp (I := I) (Mf := M) Ψ (j + a r) c).source :=
      fun y hy => (htail r c).source_sub (himg hy)
    have hfull : (U : Set (M j)) ⊆
        (chainCompAssoc (I := I) (Mf := M) Ψ j (a r) c).source := by
      rw [chainAssoc_source]
      exact hU (a r + c)
    by_cases hq0 : q = 0
    · subst q
      have hb := chain_prefix_metric_zero_cov_deriv_norm_le (I := I) Ψ U hpre hnext himg hfull
        (g (j + a r)) (g ((j + a r) + c)) (htail r c).forward (by norm_num) z
      rw [chain_pullback_assoc (I := I) Ψ g U hfull (hU (a r + c))] at hb
      rw [hdecomp] at hb
      have hb' : metricCovDerivNorm (I := I) 0 (gSeq k) (gRef r) z ≤
          2 * Real.sqrt (Module.finrank ℝ E : ℝ) := by
        simpa only [gSeq, gRef, chainPullbackSeq,
          SmoothRiemannianMetric.restrictOpen_inner] using hb
      exact hb'.trans (le_max_left _ _)
    · have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq0
      have hb := chain_prefix_metric_cov_deriv_norm_le (I := I) Ψ U hpre hnext himg hfull
        (g (j + a r)) (g ((j + a r) + c)) (htail r c).forward hq1 hqr z
      rw [chain_pullback_assoc (I := I) Ψ g U hfull (hU (a r + c))] at hb
      rw [hdecomp] at hb
      have hb' : metricCovDerivNorm (I := I) q (gSeq k) (gRef r) z ≤ 1 / 2 := by
        simpa only [gSeq, gRef, chainPullbackSeq] using hb
      exact hb'.trans (le_max_right _ _)
  · refine ⟨1 / 2, by norm_num, fun k x v => ?_⟩
    have hUK : (U : Set (M j)) ⊆ Metric.closedBall (b j) ((2 : ℝ) ^ j) :=
      fun y hy => Metric.mem_closedBall.mpr (Metric.mem_ball.mp hy).le
    have hb := pullback_metric_inner_lower (I := I)
      (chainComp (I := I) (Mf := M) Ψ j k) U (hU k) hUK
      (g j) (g (j + k)) (D0 k).forward x v
    norm_num at hb
    change (1 / 2 : ℝ) * (g j).inner (x : M j) v v ≤
      (PartialDiffeomorph.pullbackMetricOn (I := I)
        (chainComp (I := I) (Mf := M) Ψ j k) U (hU k) (g (j + k))).inner x v v
    exact hb

omit [NeZero (Module.finrank ℝ E)] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_chain_pullback_metric_limit
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    {j : ℕ}
    (D0 : ∀ k, PartialDiffeomorphMetricApproximation (I := I)
      (Metric.closedBall (b j) ((2 : ℝ) ^ j)) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ j k) (g j) (g (j + k)))
    (Dhi : ∀ p : ℕ, ∃ a : ℕ, 1 ≤ a ∧ ∀ c : ℕ,
      Nonempty (PartialDiffeomorphMetricApproximation (I := I)
        (Metric.closedBall (b (j + a)) ((2 : ℝ) ^ (j + a))) (1 / 2) p
        (chainComp (I := I) (Mf := M) Ψ (j + a) c)
        (g (j + a)) (g ((j + a) + c)))) :
    let U := ballOpen b (fun n => (2 : ℝ) ^ n) j
    letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
    let hU := chain_ball_source (I := I) b Ψ g D0
    let gSeq := chainPullbackSeq (I := I) Ψ g U hU
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ gInf : SmoothRiemannianMetric I U,
      MetricCInfConvergenceOnCompacts (I := I) (fun k => gSeq (φ k)) gInf
        ((g j).restrictOpen (I := I) U) := by
  classical
  let U := ballOpen b (fun n => (2 : ℝ) ^ n) j
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  let hU := chain_ball_source (I := I) b Ψ g D0
  let gSeq := chainPullbackSeq (I := I) Ψ g U hU
  obtain ⟨gRef, hbdd, hlow⟩ :=
    chain_pullback_bounded (I := I) b Ψ hbase g hnorm D0 Dhi
  exact metricCInf_refs (I := I) (ball_open_nonempty b (fun n => (2 : ℝ) ^ n) j (by positivity))
    ((g j).restrictOpen (I := I) U) gRef gSeq hbdd hlow

omit [I.Boundaryless] [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)] [NeZero (Module.finrank ℝ E)] in
omit [∀ (j : ℕ), SigmaCompactSpace (M j)] in
theorem exists_chain_metric_approximation_data
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hdata : ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ p : ℕ, ∃ j₀ : ℕ,
      ∀ j : ℕ, j₀ ≤ j → ∀ l : ℕ,
        Nonempty (PartialDiffeomorphMetricApproximation (I := I)
          (Metric.closedBall (b j) ((2 : ℝ) ^ j)) δ p
          (chainComp (I := I) (Mf := M) Ψ j l) (g j) (g (j + l)))) :
    ∃ j₀ : ℕ, 1 ≤ j₀ ∧ ∀ j : ℕ, j₀ ≤ j →
      ∃ _D0 : ∀ k, PartialDiffeomorphMetricApproximation (I := I)
          (Metric.closedBall (b j) ((2 : ℝ) ^ j)) (1 / 2) 0
          (chainComp (I := I) (Mf := M) Ψ j k) (g j) (g (j + k)),
        ∀ p : ℕ, ∃ a : ℕ, 1 ≤ a ∧ ∀ c : ℕ,
          Nonempty (PartialDiffeomorphMetricApproximation (I := I)
            (Metric.closedBall (b (j + a)) ((2 : ℝ) ^ (j + a))) (1 / 2) p
            (chainComp (I := I) (Mf := M) Ψ (j + a) c)
            (g (j + a)) (g ((j + a) + c))) := by
  classical
  let hzero := hdata (1 / 2) (by norm_num) (by norm_num) 0
  let jbase := Classical.choose hzero
  have hjbase := Classical.choose_spec hzero
  let j₀ := max 1 jbase
  refine ⟨j₀, le_max_left _ _, fun j hj => ?_⟩
  let D0 : ∀ k, PartialDiffeomorphMetricApproximation (I := I)
      (Metric.closedBall (b j) ((2 : ℝ) ^ j)) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ j k) (g j) (g (j + k)) :=
    fun k => Classical.choice (hjbase j (le_trans (le_max_right 1 jbase) hj) k)
  refine ⟨D0, fun p => ?_⟩
  let hp := hdata (1 / 2) (by norm_num) (by norm_num) p
  let jp := Classical.choose hp
  have hjp := Classical.choose_spec hp
  let a := max 1 (jp - j)
  refine ⟨a, le_max_left _ _, fun c => ?_⟩
  apply hjp (j + a) (by
    dsimp only [a]
    omega) c

omit [NeZero (Module.finrank ℝ E)] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_chain_pullback_metric_limits
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    (hdata : ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ p : ℕ, ∃ j₀ : ℕ,
      ∀ j : ℕ, j₀ ≤ j → ∀ l : ℕ,
        Nonempty (PartialDiffeomorphMetricApproximation (I := I)
          (Metric.closedBall (b j) ((2 : ℝ) ^ j)) δ p
          (chainComp (I := I) (Mf := M) Ψ j l) (g j) (g (j + l)))) :
    ∃ j₀ : ℕ, 1 ≤ j₀ ∧
      let U : ∀ n, Opens (M (j₀ + n)) :=
        fun n => ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)
      ∃ _D₀ : ∀ n k, PartialDiffeomorphMetricApproximation (I := I)
          (Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n))) (1 / 2) 0
          (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k)
          (g (j₀ + n)) (g ((j₀ + n) + k)),
        ∃ hU : ∀ n k, (U n : Set (M (j₀ + n))) ⊆
          (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k).source,
        (∀ n,
            (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1 :
              M (j₀ + n) → M (j₀ + (n + 1))) '' (U n : Set (M (j₀ + n))) ⊆
              (U (n + 1) : Set (M (j₀ + (n + 1)))) ) ∧
          ∃ φ : ℕ → ℕ, StrictMono φ ∧
          ∃ gInf : ∀ n, SmoothRiemannianMetric I (U n),
            ∀ n,
              letI : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
                (Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
              MetricCInfConvergenceOnCompacts (I := I)
                (fun k => chainPullbackSeq (I := I) Ψ g (U n) (hU n)
                  (φ k - (j₀ + n)))
                (gInf n) ((g (j₀ + n)).restrictOpen (I := I) (U n)) := by
  classical
  obtain ⟨j₀, hj₀, hpacks⟩ :=
    exists_chain_metric_approximation_data (I := I) b Ψ g hdata
  let U : ∀ n, Opens (M (j₀ + n)) :=
    fun n => ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)
  have hpacks' : ∀ n,
      ∃ D0 : ∀ k, PartialDiffeomorphMetricApproximation (I := I)
          (Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n))) (1 / 2) 0
          (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k)
          (g (j₀ + n)) (g ((j₀ + n) + k)),
        ∀ p : ℕ, ∃ a : ℕ, 1 ≤ a ∧ ∀ c : ℕ,
          Nonempty (PartialDiffeomorphMetricApproximation (I := I)
            (Metric.closedBall (b ((j₀ + n) + a)) ((2 : ℝ) ^ ((j₀ + n) + a))) (1 / 2) p
            (chainComp (I := I) (Mf := M) Ψ ((j₀ + n) + a) c)
            (g ((j₀ + n) + a)) (g (((j₀ + n) + a) + c))) :=
    fun n => hpacks (j₀ + n) (Nat.le_add_right j₀ n)
  choose D0 Dhi using hpacks'
  let hU : ∀ n k, (U n : Set (M (j₀ + n))) ⊆
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k).source :=
    fun n => chain_ball_source (I := I) b Ψ g (D0 n)
  let hmap : ∀ n,
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1 :
        M (j₀ + n) → M (j₀ + (n + 1))) '' (U n : Set (M (j₀ + n))) ⊆
        (U (n + 1) : Set (M (j₀ + (n + 1))) ) := fun n => by
    intro y hy
    change y ∈ Metric.ball (b ((j₀ + n) + 1)) ((2 : ℝ) ^ ((j₀ + n) + 1))
    exact chain_image_open (I := I) b Ψ hbase g hnorm (j := j₀ + n) (a := 1)
      (by omega) (D0 n 1) hy
  let gSeq : ∀ n, ℕ → SmoothRiemannianMetric I (U n) :=
    fun n => chainPullbackSeq (I := I) Ψ g (U n) (hU n)
  let P : ℕ → (ℕ → ℕ) → Prop := fun n ξ =>
    letI : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
    ∃ gInf : SmoothRiemannianMetric I (U n),
      MetricCInfConvergenceOnCompacts (I := I)
        (fun k => gSeq n (ξ k - (j₀ + n))) gInf
        ((g (j₀ + n)).restrictOpen (I := I) (U n))
  have metric_subseq : ∀ {N : Type u} [TopologicalSpace N] [ChartedSpace H N]
      [T2Space N] [IsManifold I ∞ N] [SigmaCompactSpace N]
      {gS : ℕ → SmoothRiemannianMetric I N} {gLim gBase : SmoothRiemannianMetric I N},
      MetricCInfConvergenceOnCompacts (I := I) gS gLim gBase →
      ∀ {ρ : ℕ → ℕ}, StrictMono ρ →
        MetricCInfConvergenceOnCompacts (I := I) (fun k => gS (ρ k)) gLim gBase := by
    intro N _ _ _ _ _ gS gLim gBase hconv ρ hρ K hK p ε hε
    obtain ⟨k₀, hk₀⟩ := hconv K hK p ε hε
    exact ⟨k₀, fun k hk => hk₀ (ρ k) (le_trans hk hρ.le_apply)⟩
  have metric_of_tail : ∀ {N : Type u} [TopologicalSpace N] [ChartedSpace H N]
      [T2Space N] [IsManifold I ∞ N] [SigmaCompactSpace N]
      {gS : ℕ → SmoothRiemannianMetric I N} {gLim gBase : SmoothRiemannianMetric I N},
      ∀ m : ℕ,
        MetricCInfConvergenceOnCompacts (I := I) (fun k => gS (k + m)) gLim gBase →
        MetricCInfConvergenceOnCompacts (I := I) gS gLim gBase := by
    intro N _ _ _ _ _ gS gLim gBase m hconv K hK p ε hε
    obtain ⟨k₀, hk₀⟩ := hconv K hK p ε hε
    refine ⟨k₀ + m, fun k hk => ?_⟩
    have hval := hk₀ (k - m) (by omega)
    simpa only [Nat.sub_add_cancel (show m ≤ k by omega)] using hval
  obtain ⟨φ, hφ, hPφ⟩ := exists_diag_subseq P
    (fun n ξ _ => by
      let _ : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
      obtain ⟨gRef, hbdd, hlow⟩ :=
        chain_pullback_bounded (I := I) b Ψ hbase g hnorm (D0 n) (Dhi n)
      have hbdd' : ∀ r q : ℕ, q ≤ r → ∀ K : Set (U n), IsCompact K → ∃ C : Real,
          ∀ k : ℕ, ∀ z ∈ K,
            metricCovDerivNorm (I := I) q
              (gSeq n (ξ k - (j₀ + n))) (gRef r) z ≤ C := by
        intro r q hqr K hK
        obtain ⟨C, hC⟩ := hbdd r q hqr K hK
        exact ⟨C, fun k z hz => hC (ξ k - (j₀ + n)) z hz⟩
      obtain ⟨c, hc, hclow⟩ := hlow
      have hlow' : ∃ c : Real, 0 < c ∧ ∀ (k : ℕ) (x : U n) (v : TangentSpace I x),
          c * ((g (j₀ + n)).restrictOpen (I := I) (U n)).inner x v v ≤
            (gSeq n (ξ k - (j₀ + n))).inner x v v :=
        ⟨c, hc, fun k => hclow (ξ k - (j₀ + n))⟩
      obtain ⟨ψ, hψ, gInf, hconv⟩ := metricCInf_refs (I := I)
        (ball_open_nonempty b (fun s => (2 : ℝ) ^ s) (j₀ + n) (by positivity))
        ((g (j₀ + n)).restrictOpen (I := I) (U n)) gRef
        (fun k => gSeq n (ξ k - (j₀ + n))) hbdd' hlow'
      exact ⟨ψ, hψ, gInf, by simpa only [Function.comp_apply] using hconv⟩)
    (fun n ξ ρ hρ hP => by
      let _ : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
      obtain ⟨gInf, hconv⟩ := hP
      exact ⟨gInf, metric_subseq hconv hρ⟩)
    (fun n ξ m hP => by
      let _ : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
      obtain ⟨gInf, hconv⟩ := hP
      exact ⟨gInf, metric_of_tail m hconv⟩)
  let gInf : ∀ n, SmoothRiemannianMetric I (U n) := fun n =>
    letI : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
    (hPφ n).choose
  refine ⟨j₀, hj₀, D0, hU, hmap, φ, hφ, gInf, fun n => ?_⟩
  let _ : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
  exact (hPφ n).choose_spec

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_compatible_chain_pullback_metric_limits
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    (hdata : ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ p : ℕ, ∃ j₀ : ℕ,
      ∀ j : ℕ, j₀ ≤ j → ∀ l : ℕ,
        Nonempty (PartialDiffeomorphMetricApproximation (I := I)
          (Metric.closedBall (b j) ((2 : ℝ) ^ j)) δ p
          (chainComp (I := I) (Mf := M) Ψ j l) (g j) (g (j + l)))) :
    ∃ j₀ : ℕ, 1 ≤ j₀ ∧
      let U : ∀ n, Opens (M (j₀ + n)) :=
        fun n => ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)
      ∃ _D₀ : ∀ n k, PartialDiffeomorphMetricApproximation (I := I)
          (Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n))) (1 / 2) 0
          (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k)
          (g (j₀ + n)) (g ((j₀ + n) + k)),
        ∃ hU : ∀ n k, (U n : Set (M (j₀ + n))) ⊆
          (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k).source,
        ∃ hmap : ∀ n,
            (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1 :
              M (j₀ + n) → M (j₀ + (n + 1))) '' (U n : Set (M (j₀ + n))) ⊆
              (U (n + 1) : Set (M (j₀ + (n + 1)))),
          ∃ φ : ℕ → ℕ, StrictMono φ ∧
          ∃ gInf : ∀ n, SmoothRiemannianMetric I (U n),
            (∀ n,
              letI : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
                (Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
              MetricCInfConvergenceOnCompacts (I := I)
                (fun k => chainPullbackSeq (I := I) Ψ g (U n) (hU n)
                  (φ k - (j₀ + n)))
                (gInf n) ((g (j₀ + n)).restrictOpen (I := I) (U n))) ∧
            (∀ ε : ℝ, 0 < ε → ∀ p : ℕ, ∃ n₀ : ℕ,
              ∀ n : ℕ, n₀ ≤ n →
                letI : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
                  (Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
                ∀ l q : ℕ, q ≤ p → ∀ x : U n,
                  metricDerivNorm (I := I) q
                    (chainPullbackSeq (I := I) Ψ g (U n) (hU n) l)
                    (gInf n) (gInf n) x ≤ ε) ∧
            ∀ n,
              let F : U n → U (n + 1) := PartialDiffeomorph.opensMap
                (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1) (hmap n)
              ∀ (x : U n) (v w : TangentSpace I x),
                (gInf n).inner x v w =
                  (gInf (n + 1)).inner (F x)
                    (mfderiv I I F x v) (mfderiv I I F x w) := by
  classical
  obtain ⟨j₀, hj₀, D₀, hU, hmap, φ, hφ, gInf, hconv⟩ :=
    exists_chain_pullback_metric_limits (I := I) b Ψ hbase g hnorm hdata
  let U : ∀ n, Opens (M (j₀ + n)) :=
    fun n => ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)
  refine ⟨j₀, hj₀, ?_⟩
  dsimp only
  refine ⟨D₀, hU, hmap, φ, hφ, gInf, hconv, ?_, ?_⟩
  · intro ε hε p
    obtain ⟨δ, hδ0, hδ1, hδdim, hδbudget⟩ :=
      exists_metric_reference_change_delta (E := E) p hε
    obtain ⟨jδ, hjδ⟩ := hdata δ hδ0 hδ1 p
    refine ⟨jδ, fun n hn => ?_⟩
    let _ : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
    intro l q hqp x
    have hstage : jδ ≤ j₀ + n := by omega
    let D : ∀ m, PartialDiffeomorphMetricApproximation (I := I)
        (Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n))) δ p
        (chainComp (I := I) (Mf := M) Ψ (j₀ + n) m)
        (g (j₀ + n)) (g ((j₀ + n) + m)) :=
      fun m => Classical.choice (hjδ (j₀ + n) hstage m)
    have hUK : (U n : Set (M (j₀ + n))) ⊆
        Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n)) := by
      simpa only [U, ballOpen, Opens.coe_mk] using
        (Metric.ball_subset_closedBall :
          Metric.ball (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n)) ⊆
            Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n)))
    have htail (m a : ℕ) (hap : a ≤ p) (y : U n) :
        metricDerivNorm (I := I) a
          (chainPullbackSeq (I := I) Ψ g (U n) (hU n) m)
          ((g (j₀ + n)).restrictOpen (I := I) (U n))
          ((g (j₀ + n)).restrictOpen (I := I) (U n)) y ≤ δ := by
      simpa only [chainPullbackSeq] using
        pullback_metric_deriv_norm_le (I := I)
          (chainComp (I := I) (Mf := M) Ψ (j₀ + n) m) (U n) (hU n m) hUK
          (g (j₀ + n)) (g ((j₀ + n) + m)) (D m).forward hap y
    have hInfBase : ∀ y ∈ (Set.univ : Set (U n)), ∀ a, a ≤ p →
        metricDerivNorm (I := I) a (gInf n)
          ((g (j₀ + n)).restrictOpen (I := I) (U n))
          ((g (j₀ + n)).restrictOpen (I := I) (U n)) y ≤ δ := by
      intro y _ a hap
      exact MetricCInfConvergenceOnCompacts.metric_deriv_norm_le (I := I)
        (fun k => chainPullbackSeq (I := I) Ψ g (U n) (hU n)
          (φ k - (j₀ + n)))
        (gInf n) ((g (j₀ + n)).restrictOpen (I := I) (U n))
        ((g (j₀ + n)).restrictOpen (I := I) (U n)) (hconv n)
        (fun k => htail (φ k - (j₀ + n)) a hap y)
    exact metric_deriv_norm_reference_change_le (I := I) isOpen_univ
      (chainPullbackSeq (I := I) Ψ g (U n) (hU n) l) (gInf n)
      ((g (j₀ + n)).restrictOpen (I := I) (U n)) p hδ0.le hδ1.le hδdim hδbudget
      (fun y _ a hap => htail l a hap y) hInfBase x (Set.mem_univ x) q hqp
  · intro n
    let _ : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
    let _ : SigmaCompactSpace (U (n + 1)) := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I (U (n + 1)).isOpen)
    let F : U n → U (n + 1) := PartialDiffeomorph.opensMap
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1) (hmap n)
    intro x v w
    have hleft := metricCInf_inner (I := I)
      (fun k => chainPullbackSeq (I := I) Ψ g (U n) (hU n) (φ k - (j₀ + n)))
      (gInf n) ((g (j₀ + n)).restrictOpen (I := I) (U n)) (hconv n) x v w
    have hright := metricCInf_inner (I := I)
      (fun k => chainPullbackSeq (I := I) Ψ g (U (n + 1)) (hU (n + 1))
        (φ k - (j₀ + (n + 1))))
      (gInf (n + 1)) ((g (j₀ + (n + 1))).restrictOpen (I := I) (U (n + 1)))
      (hconv (n + 1)) (F x) (mfderiv I I F x v) (mfderiv I I F x w)
    have hevent :
        (fun k => (chainPullbackSeq (I := I) Ψ g (U n) (hU n)
          (φ k - (j₀ + n))).inner x v w) =ᶠ[Filter.atTop]
        (fun k => (chainPullbackSeq (I := I) Ψ g (U (n + 1)) (hU (n + 1))
          (φ k - (j₀ + (n + 1)))).inner (F x)
            (mfderiv I I F x v) (mfderiv I I F x w)) := by
      filter_upwards [Filter.eventually_ge_atTop (j₀ + n + 1)] with k hk
      have hφk : j₀ + n + 1 ≤ φ k := le_trans hk (hφ.id_le k)
      have hlen : φ k - (j₀ + n) = 1 + (φ k - (j₀ + (n + 1))) := by omega
      rw [hlen]
      simpa only [F] using chain_pullback_step (I := I) Ψ g (U n) (U (n + 1))
        (hU n) (hU (n + 1)) (hmap n) (φ k - (j₀ + (n + 1))) x v w
    have hleft' := Filter.Tendsto.congr' hevent hleft
    exact tendsto_nhds_unique hleft' hright

end ApproxData

end CheegerGromovCompactness
end DifferentialGeometry
