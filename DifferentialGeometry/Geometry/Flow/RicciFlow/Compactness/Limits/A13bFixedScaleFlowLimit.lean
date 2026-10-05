import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.A13bSeedVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.LocalPointedFlowLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.HalfWindowTerminalBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.HalfWindowTerminalBallApplications
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimitData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionCompatibleFlows

/-!
# A13b — the fixed-scale local flow limit (chapters 9–10, REAL WORK L)

Design: `docs/geometrization/chapter13/design-a13b-fixed-scale-flow-limit-20261004.md` (§0, §5, errata
§10 E1–E11).  The statement is the frozen text of `build-logs/scratch/CH910-C5/A13bStatement.lean`,
verbatim.

`FILL910.A13b_fixed_scale_local_flow_limit` wraps `exists_pointed_local_flow_limits_of_local_solutions`
(`RF/Compactness/Limits/LocalPointedFlowLimit.lean:221`) for the pointed sequence
`(stage at t n, y n, lam n · g_n(t n))` with `c k = τ k / 2`.  The only condition on the scale is
`lam n > 0`.  The inputs of `:221` are proved:

* `hcompact`: the stages are compact;
* `hvol`: L3 `FILL910.hvol_of_traced_seed` (physical seed volume, A13 + L2);
* `W, h, hball, hsol, hzero` and the output (i): the scaled survivor data of each traced region
  (`ObservedHistory.exists_isScaledSurvivorData_of_isTracedRegion`, private, opened here; erratum E9);
* `hjets`: L1′ through `FILL910.exists_half_window_curvDerivNorm_bound_on_ball` (recentring with radius
  1 at every point of `B̄(y n, k + 1)`, the intrinsic terminal ball of `W k n`; erratum E5);
* `hcompat`: on the whole common window `[-min (τ k) (τ l), 0]`, from the public
  `ObservedHistory.backwardMaps_comp_inclusion_eq` and `localPullMetric_restrictOpenOfSubset_eq_of_comp_eq`.

No `hRlim`, no pinching, no metric comparison hypothesis, no curvature sign, no `0 ≤ K k`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology ENNReal

namespace FILL910

universe u

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.CheegerGromovCompactness

open private ObservedHistory.isScaledSurvivorData
  ObservedHistory.exists_isScaledSurvivorData_of_isTracedRegion
  from DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimitData

open private ObservedHistory.scaleMetric_restrictOpenOfSubset ObservedHistory.mem_Icc_of_mem_window
  ObservedHistory.riemannianBallOf_scaleMetric_eq
  from DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimit

/-- Needed by `LocalPointedFlowLimit.lean:221` (the existing copies are private). -/
instance instNeZeroFinrankThreeSpace_CH910C5 : NeZero (Module.finrank ℝ ThreeSpace) :=
  ⟨by simp⟩

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

/-- **A13b (chapter 10, REAL WORK L): fixed-scale local flow limit.**

Inputs (all physical, i.e. in the unscaled history): a positive scaling factor `lam n` (no bound,
`lam n → 0` allowed), per-radius depths `τ k > 0` and curvature bounds `K k` uniform in `n`, the
traced regions `isTracedRegion (t n) (y n) ((k+3)/√lam n) (τ k / lam n) (K k · lam n)` for every `k`,
eventually in `n`, and the physical seed volume `Vol B(y n, r₀/√lam n) ≥ w (r₀/√lam n)³`, eventually.

Proved inside (not assumed): `hcompact` (stages are compact), `hvol` (L3 = A13 + L2), `hsol`,
`hzero`, the window identities and `|Rm| ≤ K k` (scaled survivor data, A12 rescaled by `lam n`),
`hcompat` (`ObservedHistory.backwardMaps_comp_inclusion_eq`), `hjets` on `[-(τ k/2), 0]` (L1').

Output: the local data `W, h` with their link to the history, the jets, the compatibility, and the
whole conclusion of `exists_pointed_local_flow_limits_of_local_solutions` with `c k = τ k / 2`:
complete connected pointed limit `P`, strictly monotone `f`, maps `F`, local diffeomorphisms `φ`
into `W k (f j)`, compatible local flows `Gloc k` on `[-(τ k/2), 0]`, and a second subsequence `ψ`
with smooth local convergence of the pulled-back `h k (f (ψ i))`.  No curvature-sign output. -/
theorem A13b_fixed_scale_local_flow_limit
    (H : ℕ → ObservedHistory.{u}) (t : ∀ n, Icc (0 : ℝ) (H n).horizon)
    (y : ∀ n, ((H n).stageAt (t n)).Carrier) (lam : ℕ → ℝ) (hlam : ∀ n, 0 < lam n)
    (τ K : ℕ → ℝ) (hτ : ∀ k, 0 < τ k)
    (htraced : ∀ k : ℕ, ∀ᶠ n in atTop,
      (H n).isTracedRegion (t n) (y n) (((k + 3 : ℕ) : ℝ) / Real.sqrt (lam n)) (τ k / lam n)
        (K k * lam n))
    {r₀ w : ℝ} (hr₀ : 0 < r₀) (hw : 0 < w)
    (hseed : ∀ᶠ n in atTop,
      ENNReal.ofReal (w * (r₀ / Real.sqrt (lam n)) ^ 3) ≤
        Integral.Measure.riemannianVolumeMeasure ThreeModel ((H n).stageAt (t n)).Carrier
          ((H n).stageMetric ((H n).activeStage (t n)) (t n))
          (riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
            (r₀ / Real.sqrt (lam n)))) :
    let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
      { obj := fun n =>
          { M := ((H n).stageAt (t n)).Carrier
            basepoint := y n
            metric := scaleMetric (lam n) (hlam n)
              ((H n).stageMetric ((H n).activeStage (t n)) (t n)) } }
    ∃ (W : ∀ (_ : ℕ) (n : ℕ), Opens (X.obj n).M)
      (h : ∀ k n, ℝ → SmoothRiemannianMetric ThreeModel (W k n)),
      -- (i) the local data and its link to the history
      (∀ k : ℕ, ∀ᶠ n in atTop,
        (W k n : Set (X.obj n).M) =
          riemannianBallOf (X.obj n).metric (X.obj n).basepoint ((k + 3 : ℕ) : ℝ) ∧
        IsSolutionOn ({ base.metric := h k n } : SolutionOn (I := ThreeModel) (M := W k n)
          (RealTimeInterval.closed (-τ k) 0 (neg_nonpos.mpr (hτ k).le))) ∧
        h k n 0 = (X.obj n).metric.restrictOpen (W k n) ∧
        (∀ s ∈ Icc (-τ k) 0, ∀ x : W k n, curvDerivNormSq 0 (h k n s) x ≤ K k ^ 2) ∧
        (∀ s ∈ Icc (-τ k) 0,
          (t n : ℝ) + s / lam n ∈ (H n).stageDomain ((H n).activeStage (t n)) →
          h k n s = scaleMetric (lam n) (hlam n)
            (((H n).stageMetric ((H n).activeStage (t n)) ((t n : ℝ) + s / lam n)).restrictOpen
              (W k n))) ∧
        (∃ (a : Icc (0 : ℝ) (H n).horizon) (hat : a ≤ t n),
          (a : ℝ) = t n - τ k / lam n ∧
          ∃ f : (j : (H n).StageInterval ((H n).activeStage a) ((H n).activeStage (t n))) →
              W k n → ((H n).stage j.val).Carrier,
            ∃ hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j),
              (∀ j, Function.Injective (f j)) ∧
              (∀ (i : Fin (H n).eventCount) (hi : (H n).activeStage a ≤ i.castSucc)
                  (hl : i.succ ≤ (H n).activeStage (t n)), ∀ x : W k n,
                ((H n).event i).RegularCrossing
                  (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
                  (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x)) ∧
              (∀ x : W k n,
                f ⟨(H n).activeStage (t n), (H n).activeStage_mono hat, le_rfl⟩ x = x.val) ∧
              ∀ s ∈ Icc (-τ k) 0,
                ∀ j : (H n).StageInterval ((H n).activeStage a) ((H n).activeStage (t n)),
                  (t n : ℝ) + s / lam n ∈ (H n).stageDomain j.val →
                    h k n s = scaleMetric (lam n) (hlam n)
                      (localPullMetric ((H n).stageMetric j.val ((t n : ℝ) + s / lam n)) (f j)
                        (hf j)))) ∧
      -- (ii) jets on the half window (L1')
      (∀ k m : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop,
        ∀ s ∈ Icc (-(τ k / 2)) 0, ∀ x : W k n,
          (x : (X.obj n).M) ∈
            riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 1 : ℕ) : ℝ) →
          curvDerivNorm m (h k n s) x ≤ B) ∧
      -- (iii) compatibility on the common window
      (∀ k l : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-τ k) 0, s ∈ Icc (-τ l) 0 →
        (h k n s).restrictOpenOfSubset (inf_le_left : W k n ⊓ W l n ≤ W k n) =
          (h l n s).restrictOpenOfSubset (inf_le_right : W k n ⊓ W l n ≤ W l n)) ∧
      -- (iv) the conclusion of `LocalPointedFlowLimit.lean:221` with `c k = τ k / 2`
      ∃ (f : ℕ → ℕ), StrictMono f ∧
        ∃ (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
          (F : PointedRiemannianConvergenceMaps X P f),
          (∃ C : MetricConvergenceData F,
            ∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData F n) ∧
          MetricComplete P ∧ ConnectedSpace P.M ∧
          (∀ R : ℝ, 0 < R → ∀ᶠ n in atTop,
            riemannianClosedBallOf (X.obj (f n)).metric (X.obj (f n)).basepoint R ⊆
              F.target n) ∧
          ∃ (V : ℕ → Opens P.M) (N : ℕ → ℕ),
            (∀ k, (V k : Set P.M) =
              riemannianBallOf P.metric P.basepoint (((k + 1 : ℕ) : ℝ) / 2)) ∧
            (∀ k j, N k ≤ j → (V k : Set P.M) ⊆ F.source j) ∧
            ∃ (φ : ∀ k j, N k ≤ j → V k → W k (f j))
              (hφ : ∀ k j (hj : N k ≤ j), IsLocalDiffeomorph ThreeModel ThreeModel ∞ (φ k j hj)),
              (∀ k j (hj : N k ≤ j) (z : V k), ((φ k j hj z : W k (f j)) : (X.obj (f j)).M) =
                F.map j z) ∧
              ∃ Gloc : ∀ k : ℕ, ℝ → SmoothRiemannianMetric ThreeModel (V k),
                (∀ k, Gloc k 0 = P.metric.restrictOpen (V k)) ∧
                (∀ k, IsSolutionOn ({ base.metric := Gloc k } :
                  SolutionOn (I := ThreeModel) (M := V k)
                    (RealTimeInterval.closed (-(τ k / 2)) 0
                      (neg_nonpos.mpr (half_pos (hτ k)).le)))) ∧
                (∀ k l, ∀ s ∈ Icc (-(τ k / 2)) 0, s ∈ Icc (-(τ l / 2)) 0 →
                  (Gloc k s).restrictOpenOfSubset (inf_le_left : V k ⊓ V l ≤ V k) =
                    (Gloc l s).restrictOpenOfSubset (inf_le_right : V k ⊓ V l ≤ V l)) ∧
                ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
                  ∀ k (Kc : Set (V k)), IsCompact Kc → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
                    ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i, ∀ s ∈ Icc (-(τ k / 2)) 0,
                      metricDerivNormSupOn Kc p
                        (localPullMetric (h k (f (ψ i)) s) (φ k (ψ i) hi) (hφ k (ψ i) hi))
                        (Gloc k s) (P.metric.restrictOpen (V k)) < η := by
  intro X
  have hc (k : ℕ) : 0 < τ k / 2 := half_pos (hτ k)
  have hcτ (k : ℕ) : τ k / 2 < τ k := half_lt_self (hτ k)
  -- the scaled survivor data, chosen for every `(k, n)`
  have hex : ∀ k n, ∃ (Wk : Opens (X.obj n).M) (g : ℝ → SmoothRiemannianMetric ThreeModel Wk),
      (H n).isTracedRegion (t n) (y n) (((k + 3 : ℕ) : ℝ) / Real.sqrt (lam n)) (τ k / lam n)
          (K k * lam n) →
        ObservedHistory.isScaledSurvivorData (H n) (t n) (y n) (lam n)
          (((k + 3 : ℕ) : ℝ) / Real.sqrt (lam n)) (τ k) (K k) (hlam n) Wk g := by
    intro k n
    by_cases htr : (H n).isTracedRegion (t n) (y n) (((k + 3 : ℕ) : ℝ) / Real.sqrt (lam n))
        (τ k / lam n) (K k * lam n)
    · obtain ⟨Wk, g, hg⟩ :=
        ObservedHistory.exists_isScaledSurvivorData_of_isTracedRegion (H n) (t n) (y n) (hlam n)
          (hτ k) htr
      exact ⟨Wk, g, fun _ => hg⟩
    · exact ⟨⊤, fun _ => (X.obj n).metric.restrictOpen ⊤, fun hh => absurd hh htr⟩
  choose W h hWh using hex
  have hsurv (k : ℕ) : ∀ᶠ n in atTop,
      ObservedHistory.isScaledSurvivorData (H n) (t n) (y n) (lam n)
        (((k + 3 : ℕ) : ℝ) / Real.sqrt (lam n)) (τ k) (K k) (hlam n) (W k n) (h k n) :=
    (htraced k).mono fun n hn => hWh k n hn
  have hWset (k n : ℕ) (hn : ObservedHistory.isScaledSurvivorData (H n) (t n) (y n) (lam n)
      (((k + 3 : ℕ) : ℝ) / Real.sqrt (lam n)) (τ k) (K k) (hlam n) (W k n) (h k n)) :
      (W k n : Set (X.obj n).M) =
        riemannianBallOf (X.obj n).metric (X.obj n).basepoint ((k + 3 : ℕ) : ℝ) := by
    rw [hn.1]
    exact (ObservedHistory.riemannianBallOf_scaleMetric_eq _ (hlam n) _ _).symm
  have hsubW (k n : ℕ) (hn : ObservedHistory.isScaledSurvivorData (H n) (t n) (y n) (lam n)
      (((k + 3 : ℕ) : ℝ) / Real.sqrt (lam n)) (τ k) (K k) (hlam n) (W k n) (h k n)) {r : ℝ}
      (hr : r < ((k + 3 : ℕ) : ℝ)) :
      riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint r ⊆ W k n := by
    intro z hz
    rw [hWset k n hn]
    exact lt_of_le_of_lt hz ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hr)
  -- `hcompact`: the stages are compact
  have hcompact : ∀ r : ℝ, 0 < r → ∀ᶠ n in atTop,
      IsCompact (riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint r) :=
    fun r _ => Eventually.of_forall fun n =>
      (Geometry.Metric.isClosed_riemannianClosedBallOf (X.obj n).metric _ r).isCompact
  -- `hvol`: L3
  have hvolX : ∀ r R : ℝ, 0 < r → r < R → ∀ C : ℝ, 0 ≤ C →
      ∃ a κ : ℝ, 0 < a ∧ 0 < κ ∧ r + a ≤ R ∧ a ^ 4 * C ^ 2 ≤ 1 ∧
      ∀ᶠ n in atTop, ∀ x ∈ riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint r,
        ENNReal.ofReal (κ * a ^ Module.finrank ℝ ThreeSpace) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel (X.obj n).M (X.obj n).metric
            (riemannianBallOf (X.obj n).metric x a) :=
    hvol_of_traced_seed H t y lam hlam τ K htraced hr₀ hw hseed
  have hball : ∀ k : ℕ, ∀ᶠ n in atTop,
      riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 1 : ℕ) : ℝ) ⊆
        W k n := by
    intro k
    filter_upwards [hsurv k] with n hn
    exact hsubW k n hn (by push_cast; linarith)
  have hsolτ : ∀ k : ℕ, ∀ᶠ n in atTop, IsSolutionOn ({ base.metric := h k n } :
      SolutionOn (I := ThreeModel) (M := W k n)
        (RealTimeInterval.closed (-τ k) 0 (neg_nonpos.mpr (hτ k).le))) := by
    intro k
    filter_upwards [hsurv k] with n hn
    exact hn.2.1 (τ k) (hτ k).le le_rfl
  have hzero : ∀ k : ℕ, ∀ᶠ n in atTop, h k n 0 = (X.obj n).metric.restrictOpen (W k n) := by
    intro k
    filter_upwards [hsurv k] with n hn
    exact hn.2.2.1
  -- `hjets`: L1′ at every centre of `B̄(y n, k + 1)`, radius `1`
  have hjets : ∀ k m : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop,
      ∀ s ∈ Icc (-(τ k / 2)) 0, ∀ x : W k n,
        (x : (X.obj n).M) ∈
          riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 1 : ℕ) : ℝ) →
        curvDerivNorm m (h k n s) x ≤ B := by
    intro k m
    obtain ⟨B, hB0, hB⟩ := exists_half_window_curvDerivNorm_bound_on_ball.{u} (K := K k) (hτ k)
      (Nat.cast_nonneg (k + 1))
    refine ⟨B m, hB0 m, ?_⟩
    filter_upwards [hsurv k] with n hn s hs x hx
    exact hB (X.obj n).metric (W k n) (h k n) (X.obj n).basepoint (hn.2.1 (τ k) (hτ k).le le_rfl)
      hn.2.2.1 hn.2.2.2.1 (hsubW k n hn (by push_cast; linarith)) m s hs x hx
  -- compatibility on the whole common window
  have hcompatτ : ∀ k l : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-τ k) 0, s ∈ Icc (-τ l) 0 →
      (h k n s).restrictOpenOfSubset (inf_le_left : W k n ⊓ W l n ≤ W k n) =
        (h l n s).restrictOpenOfSubset (inf_le_right : W k n ⊓ W l n ≤ W l n) := by
    intro k l
    filter_upwards [hsurv k, hsurv l] with n hk hl s hsk hsl
    obtain ⟨a₁, hat₁, ha₁, f₁, hf₁, -, hc₁, hl₁, hp₁⟩ := hk.2.2.2.2.2
    obtain ⟨a₂, hat₂, ha₂, f₂, hf₂, -, hc₂, hl₂, hp₂⟩ := hl.2.2.2.2.2
    have hv₁ := ObservedHistory.mem_Icc_of_mem_window (hlam n) ha₁ hsk
    have hv₂ := ObservedHistory.mem_Icc_of_mem_window (hlam n) ha₂ hsl
    let v : Icc (0 : ℝ) (H n).horizon :=
      ⟨(t n : ℝ) + s / lam n, a₁.2.1.trans hv₁.1, hv₁.2.trans (t n).2.2⟩
    have hja₁ : (H n).activeStage a₁ ≤ (H n).activeStage v :=
      (H n).activeStage_mono (show a₁ ≤ v from hv₁.1)
    have hja₂ : (H n).activeStage a₂ ≤ (H n).activeStage v :=
      (H n).activeStage_mono (show a₂ ≤ v from hv₂.1)
    have hjt : (H n).activeStage v ≤ (H n).activeStage (t n) :=
      (H n).activeStage_mono (show v ≤ t n from hv₁.2)
    have hdom := (H n).activeStage_mem v
    rw [hp₁ s hsk ⟨_, hja₁, hjt⟩ hdom, hp₂ s hsl ⟨_, hja₂, hjt⟩ hdom,
      ObservedHistory.scaleMetric_restrictOpenOfSubset,
      ObservedHistory.scaleMetric_restrictOpenOfSubset]
    congr 1
    exact localPullMetric_restrictOpenOfSubset_eq_of_comp_eq _ _ _ _ _ _ _
      (ObservedHistory.backwardMaps_comp_inclusion_eq (H n) hat₁ hat₂ f₁ hc₁ hl₁ f₂ hc₂ hl₂ _
        hja₁ hja₂ hjt)
  have hcompat : ∀ k l : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-(τ k / 2)) 0, s ∈ Icc (-(τ l / 2)) 0 →
      (h k n s).restrictOpenOfSubset (inf_le_left : W k n ⊓ W l n ≤ W k n) =
        (h l n s).restrictOpenOfSubset (inf_le_right : W k n ⊓ W l n ≤ W l n) := by
    intro k l
    filter_upwards [hcompatτ k l] with n hn s hsk hsl
    exact hn s ⟨(neg_le_neg (hcτ k).le).trans hsk.1, hsk.2⟩
      ⟨(neg_le_neg (hcτ l).le).trans hsl.1, hsl.2⟩
  refine ⟨W, h, fun k => ?_, hjets, hcompatτ,
    exists_pointed_local_flow_limits_of_local_solutions X hcompact hvolX τ (fun k => τ k / 2) hc
      hcτ W h hball hsolτ hzero hjets hcompat⟩
  filter_upwards [hsurv k] with n hn
  exact ⟨hWset k n hn, hn.2.1 (τ k) (hτ k).le le_rfl, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2.1,
    hn.2.2.2.2.2⟩

end FILL910
