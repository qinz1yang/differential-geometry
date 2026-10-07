import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.TerminalCurvatureEscape_P6L

/-!
# P6WIN-B G1：`TerminalCurvatureEscape:193` 的时间窗形（`_P6WB`）

P6CON G2b 窗口 spine 的 B 段（hgradient 链）：`TCE:193_P6L` 的 `hgradient` 在证明里只经
`TerminalScalarBall:27_P6L`（`…_on_time_window`，已是窗口形）于 `t ∈ 𝓝[<] s n`、`c n ≤ t` 求值 ⇒
把 `hgradient` 收窄为窗口形（序列层窗口数据 `c : ℕ → ℝ`、`hc : ∀ n, c n < s n` 紧跟 `U` 之后，
F6）：`∀ t ∈ Ioo (a n) (s n), c n ≤ t → …`。`hU`（移动球）、`hx`、`hfail`、结论逐字。
私有引理（`TCE:12,44,63`）复制为 `_P6WB`。consumer：`TCE:193_P6L`（全 slab 形）⇐ 窗口形取
`c n = a n`（`a n < s n` 由 `(G n).lt` 给）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private theorem exists_radius_of_not_eventually_bounded_P6WB
    {M : ℕ → Type*} (d : ∀ n, M n → ℝ≥0∞) (f : ∀ n, M n → ℝ)
    {r₀ : ℝ}
    (hsmall : ∃ C : ℝ, ∀ᶠ n in atTop, ∀ y, d n y < ENNReal.ofReal r₀ → f n y ≤ C)
    (hfail : ∃ r : ℝ, 0 < r ∧ ¬ ∃ C : ℝ,
      ∀ᶠ n in atTop, ∀ y, d n y < ENNReal.ofReal r → f n y ≤ C) :
    ∃ R : ℝ, r₀ ≤ R ∧
      (∀ r : ℝ, r < R → ∃ C : ℝ,
        ∀ᶠ n in atTop, ∀ y, d n y < ENNReal.ofReal r → f n y ≤ C) ∧
      (∀ r : ℝ, R < r → ∀ C : ℝ, ∀ N : ℕ,
        ∃ n, N ≤ n ∧ ∃ y, d n y < ENNReal.ofReal r ∧ C < f n y) := by
  let S : Set ℝ := {r | ∃ C : ℝ,
    ∀ᶠ n in atTop, ∀ y, d n y < ENNReal.ofReal r → f n y ≤ C}
  have hSne : S.Nonempty := ⟨r₀, hsmall⟩
  obtain ⟨rBad, _, hbad⟩ := hfail
  have hSbdd : BddAbove S := by
    refine ⟨rBad, fun r hr => le_of_not_gt fun hlt => ?_⟩
    apply hbad
    obtain ⟨C, hC⟩ := hr
    refine ⟨C, hC.mono fun n hn y hy => hn y ?_⟩
    exact hy.trans_le (ENNReal.ofReal_le_ofReal hlt.le)
  refine ⟨sSup S, le_csSup hSbdd hsmall, ?_, ?_⟩
  · intro r hr
    obtain ⟨s, hs, hrs⟩ := (lt_csSup_iff hSbdd hSne).mp hr
    obtain ⟨C, hC⟩ := hs
    exact ⟨C, hC.mono fun n hn y hy => hn y
      (hy.trans_le (ENNReal.ofReal_le_ofReal hrs.le))⟩
  · intro r hr C N
    by_contra! h
    have hrS : r ∈ S := ⟨C, eventually_atTop.mpr ⟨N, h⟩⟩
    exact (not_le_of_gt hr) (le_csSup hSbdd hrS)

private theorem abs_sub_lt_div_of_escape_radii_P6WB {R d : ℝ} {k : ℕ} (hR : 0 < R)
    (hlo : R * (((k : ℝ) + 1) / ((k : ℝ) + 2)) ≤ d)
    (hhi : d < R * (((k : ℝ) + 2) / ((k : ℝ) + 1))) :
    |d - R| < R / ((k : ℝ) + 1) := by
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hk2 : ((k : ℝ) + 2) ≠ 0 := by positivity
  have hkey1 : R - R * (((k : ℝ) + 1) / ((k : ℝ) + 2)) = R / ((k : ℝ) + 2) := by
    field_simp [hk2]
    ring
  have hkey2 : R * (((k : ℝ) + 2) / ((k : ℝ) + 1)) - R = R / ((k : ℝ) + 1) := by
    field_simp
    ring
  have h1 : R - d ≤ R / ((k : ℝ) + 2) := by linarith
  have h2 : d - R < R / ((k : ℝ) + 1) := by linarith
  have h3 : R / ((k : ℝ) + 2) < R / ((k : ℝ) + 1) :=
    div_lt_div_of_pos_left hR (by positivity) (by linarith)
  rw [abs_lt]
  constructor <;> linarith

private theorem exists_subsequence_radius_escape_P6WB
    {M : ℕ → Type*} (d : ∀ n, M n → ℝ≥0∞) (f : ∀ n, M n → ℝ)
    {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hsmall : ∃ C : ℝ, ∀ᶠ n in atTop, ∀ y, d n y < ENNReal.ofReal r₀ → f n y ≤ C)
    (hfail : ∃ r : ℝ, 0 < r ∧ ¬ ∃ C : ℝ,
      ∀ᶠ n in atTop, ∀ y, d n y < ENNReal.ofReal r → f n y ≤ C) :
    ∃ (R : ℝ) (ind : ℕ → ℕ), r₀ ≤ R ∧ StrictMono ind ∧
      (∀ r : ℝ, r < R → ∃ C : ℝ,
        ∀ᶠ n in atTop, ∀ y, d n y < ENNReal.ofReal r → f n y ≤ C) ∧
      ∃ y : ∀ n, M (ind n),
        (∀ n, d (ind n) (y n) ≠ ⊤) ∧
        Tendsto (fun n => (d (ind n) (y n)).toReal) atTop (𝓝 R) ∧
        Tendsto (fun n => f (ind n) (y n)) atTop atTop := by
  classical
  obtain ⟨R, hR₀, hinner, houter⟩ := exists_radius_of_not_eventually_bounded_P6WB d f hsmall hfail
  have hR : 0 < R := hr₀.trans_le hR₀
  let rIn (k : ℕ) := R * (((k : ℝ) + 1) / ((k : ℝ) + 2))
  let rOut (k : ℕ) := R * (((k : ℝ) + 2) / ((k : ℝ) + 1))
  have hIn (k : ℕ) : 0 < rIn k ∧ rIn k < R := by
    have hk : ((k : ℝ) + 1) / ((k : ℝ) + 2) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    exact ⟨by dsimp [rIn]; positivity, by dsimp [rIn]; nlinarith⟩
  have hOut (k : ℕ) : R < rOut k := by
    have hk : 1 < ((k : ℝ) + 2) / ((k : ℝ) + 1) := by
      rw [lt_div_iff₀ (by positivity)]
      linarith
    dsimp [rOut]
    nlinarith
  choose C hC using fun k => hinner (rIn k) (hIn k).2
  choose start hstart using fun k => eventually_atTop.mp (hC k)
  have hgood (k N : ℕ) : ∃ n, N ≤ n ∧ ∃ y,
      ENNReal.ofReal (rIn k) ≤ d n y ∧ d n y < ENNReal.ofReal (rOut k) ∧
      (k : ℝ) < f n y := by
    obtain ⟨n, hn, y, hyd, hyf⟩ := houter (rOut k) (hOut k) (max (C k) k) (max N (start k))
    refine ⟨n, (le_max_left _ _).trans hn, y, ?_, hyd, (le_max_right _ _).trans_lt hyf⟩
    by_contra hlo
    have hs := hstart k n ((le_max_right _ _).trans hn) y (lt_of_not_ge hlo)
    exact (not_lt_of_ge hs) ((le_max_left _ _).trans_lt hyf)
  let base : ℕ := Classical.choose (hgood 0 0)
  let step : ℕ → ℕ → ℕ := fun k prev => Classical.choose (hgood (k + 1) (prev + 1))
  let ind : ℕ → ℕ := fun k => Nat.rec base step k
  have hind (k : ℕ) : ind k < ind (k + 1) :=
    Nat.lt_of_succ_le (Classical.choose_spec (hgood (k + 1) (ind k + 1))).1
  have hpoint (k : ℕ) : ∃ y : M (ind k),
      ENNReal.ofReal (rIn k) ≤ d (ind k) y ∧
      d (ind k) y < ENNReal.ofReal (rOut k) ∧ (k : ℝ) < f (ind k) y := by
    cases k with
    | zero => exact (Classical.choose_spec (hgood 0 0)).2
    | succ k => exact (Classical.choose_spec (hgood (k + 1) (ind k + 1))).2
  choose y hy using hpoint
  have hfinite (k) : d (ind k) (y k) ≠ ⊤ := ne_top_of_lt (hy k).2.1
  have habs (k) : |(d (ind k) (y k)).toReal - R| < R / ((k : ℝ) + 1) := by
    apply abs_sub_lt_div_of_escape_radii_P6WB hR
    · exact (ENNReal.ofReal_le_iff_le_toReal (hfinite k)).mp (hy k).1
    · exact ENNReal.toReal_lt_of_lt_ofReal (hy k).2.1
  have hlim : Tendsto (fun k : ℕ => R / ((k : ℝ) + 1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, one_div, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul R
  have habslim := squeeze_zero (fun k => abs_nonneg _) (fun k => (habs k).le) hlim
  refine ⟨R, ind, hR₀, strictMono_nat_of_lt_succ hind, hinner, y, hfinite, ?_, ?_⟩
  · apply Metric.tendsto_nhds.mpr
    intro eps heps
    filter_upwards [habslim.eventually (eventually_lt_nhds heps)] with k hk
    rwa [Real.dist_eq]
  · apply tendsto_atTop_mono (fun n => (hy n).2.2.le)
    exact tendsto_natCast_atTop_atTop (R := ℝ)

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn (CanonicalWitness)
open scoped _root_.Manifold ContDiff NNReal

universe u

/-- **`_P6WB`（`TCE:193` 窗口形）**：`TCE:193_P6L` 的 `hgradient` 只在窗口 `[c n, s n)` 内要
（guard `c n ≤ t`，窗口起点 `c n < s n` 在 `U` 之后给出）；叶子换
`scalar_le_on_small_ball_of_gradient_bound_on_time_window_P6L`（`TSB:27`，已是窗口形）。
`hU`、`hx`、`hfail`、结论与证明体其余逐字。 -/
theorem exists_terminal_scalar_escape_radius_of_derivative_bounds_window_P6WB
    (P : ℕ → OrientedThreeStage.{u}) (a s : ℕ → ℝ)
    (G : ∀ n, (P n).IncomingSlab (a n) (s n))
    (L : ∀ n, (G n).TerminalLimitMetric)
    (x : ∀ n, (G n).terminalRegularOpen)
    (Q : ℕ → ℝ) (hQ : ∀ n, 0 < Q n)
    (C : ℝ≥0) (q : ℕ → ℝ) (hqQ : ∀ n, q n ≤ Q n)
    (U : ∀ n, Set (P n).Carrier) (c : ℕ → ℝ) (hc : ∀ n, c n < s n)
    (hgradient : ∀ n, ∀ y ∈ U n, ∀ t ∈ Ioo (a n) (s n), c n ≤ t →
      q n < (G n).flow.scalar t y → ∀ v : TangentSpace ThreeModel y,
        |scalarDifferential (G n).flow t y v| ≤ C * (G n).flow.scalar t y *
          Real.sqrt ((G n).flow.scalar t y) *
            Real.sqrt (((G n).flow.base.metric t).inner y v v))
    (hU : ∀ n, ∀ᶠ t in 𝓝[<] s n, riemannianBallOf ((G n).flow.base.metric t) (x n).val
      (2 * (localPropagationRadius C / Real.sqrt (2 * Q n))) ⊆ U n)
    (hx : ∀ n, metricScalarAt (L n).metric (x n) ≤ Q n)
    (hfail : ∃ r : ℝ, 0 < r ∧ ¬ ∃ A : ℝ,
      ∀ᶠ n in atTop, ∀ y : (G n).terminalRegularOpen,
        riemannianEDistOf (scaleMetric (Q n) (hQ n) (L n).metric) (x n) y < ENNReal.ofReal r →
          metricScalarAt (L n).metric y / Q n ≤ A) :
    ∃ (R : ℝ) (ind : ℕ → ℕ), 0 < R ∧ StrictMono ind ∧
      (∀ r : ℝ, 0 < r → r < R → ∃ A : ℝ,
        ∀ᶠ n in atTop,
          IsCompact (riemannianClosedBallOf
            (scaleMetric (Q n) (hQ n) (L n).metric) (x n) r) ∧
          ∀ y : (G n).terminalRegularOpen,
            y ∈ riemannianClosedBallOf
              (scaleMetric (Q n) (hQ n) (L n).metric) (x n) r →
              metricScalarAt (L n).metric y / Q n ≤ A) ∧
      ∃ y : ∀ n, (G (ind n)).terminalRegularOpen,
        (∀ n, riemannianEDistOf
          (scaleMetric (Q (ind n)) (hQ (ind n)) (L (ind n)).metric) (x (ind n)) (y n) ≠ ⊤) ∧
        Tendsto (fun n => (riemannianEDistOf
          (scaleMetric (Q (ind n)) (hQ (ind n)) (L (ind n)).metric) (x (ind n)) (y n)).toReal)
          atTop (𝓝 R) ∧
        Tendsto (fun n => metricScalarAt (L (ind n)).metric (y n) / Q (ind n)) atTop atTop := by
  let d := fun n (y : (G n).terminalRegularOpen) =>
    riemannianEDistOf (scaleMetric (Q n) (hQ n) (L n).metric) (x n) y
  let f := fun n (y : (G n).terminalRegularOpen) => metricScalarAt (L n).metric y / Q n
  let r₀ := localPropagationRadius C / (2 * Real.sqrt 2)
  have hr₀ : 0 < r₀ := div_pos (localPropagationRadius_pos C.coe_nonneg) (by positivity)
  have hsmall : ∃ A : ℝ, ∀ᶠ n in atTop, ∀ y, d n y < ENNReal.ofReal r₀ → f n y ≤ A := by
    refine ⟨6, Eventually.of_forall fun n y hy => ?_⟩
    have hball : y ∈ riemannianClosedBallOf (L n).metric (x n)
        (localPropagationRadius C / (2 * Real.sqrt (2 * Q n))) := by
      have heq : r₀ = Real.sqrt (Q n) *
          (localPropagationRadius C / (2 * Real.sqrt (2 * Q n))) := by
        dsimp [r₀]
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
        field_simp [ne_of_gt (Real.sqrt_pos.mpr (hQ n))]
      have hclosed : y ∈ riemannianClosedBallOf
          (scaleMetric (Q n) (hQ n) (L n).metric) (x n) r₀ := hy.le
      rw [heq, DifferentialGeometry.riemannianClosedBallOf_scaleMetric] at hclosed
      exact hclosed
    exact (div_le_iff₀ (hQ n)).mpr
      ((L n).scalar_le_on_small_ball_of_gradient_bound_on_time_window_P6L C (hQ n) (hqQ n)
        (hc n) (U n) (hgradient n) (x n) (hU n) (hx n) y hball)
  obtain ⟨R, ind, hR, hind, hinner, y, hfinite, hdist, hscalar⟩ :=
    exists_subsequence_radius_escape_P6WB d f hr₀ hsmall hfail
  refine ⟨R, ind, hr₀.trans_le hR, hind, ?_, y, hfinite, hdist, hscalar⟩
  intro r hr hrR
  obtain ⟨A, hA⟩ := hinner ((r + R) / 2) (by linarith)
  refine ⟨A, hA.mono fun n hn => ?_⟩
  have hbound : ∀ y : (G n).terminalRegularOpen,
      y ∈ riemannianClosedBallOf (scaleMetric (Q n) (hQ n) (L n).metric) (x n) r →
        metricScalarAt (L n).metric y / Q n ≤ A := by
    intro y hy
    exact hn y (hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)))
  refine ⟨?_, hbound⟩
  apply ((L n).isCompact_scalar_sublevel (A * Q n)).of_isClosed_subset
  · exact isClosed_le (by
      unfold riemannianEDistOf
      exact DifferentialGeometry.Geometry.Riemannian.continuous_riemannianEDist _ (x n))
      continuous_const
  · intro y hy
    exact (div_le_iff₀ (hQ n)).mp (hbound y hy)

/-- consumer：`TCE:193_P6L`（全 slab `hgradient`）由窗口形（`c n = a n`）推出。 -/
example (P : ℕ → OrientedThreeStage.{u}) (a s : ℕ → ℝ)
    (G : ∀ n, (P n).IncomingSlab (a n) (s n))
    (L : ∀ n, (G n).TerminalLimitMetric)
    (x : ∀ n, (G n).terminalRegularOpen)
    (Q : ℕ → ℝ) (hQ : ∀ n, 0 < Q n)
    (C : ℝ≥0) (q : ℕ → ℝ) (hqQ : ∀ n, q n ≤ Q n)
    (U : ∀ n, Set (P n).Carrier)
    (hgradient : ∀ n, ∀ y ∈ U n, ∀ t ∈ Ioo (a n) (s n),
      q n < (G n).flow.scalar t y → ∀ v : TangentSpace ThreeModel y,
        |scalarDifferential (G n).flow t y v| ≤ C * (G n).flow.scalar t y *
          Real.sqrt ((G n).flow.scalar t y) *
            Real.sqrt (((G n).flow.base.metric t).inner y v v))
    (hU : ∀ n, ∀ᶠ t in 𝓝[<] s n, riemannianBallOf ((G n).flow.base.metric t) (x n).val
      (2 * (localPropagationRadius C / Real.sqrt (2 * Q n))) ⊆ U n)
    (hx : ∀ n, metricScalarAt (L n).metric (x n) ≤ Q n)
    (hfail : ∃ r : ℝ, 0 < r ∧ ¬ ∃ A : ℝ,
      ∀ᶠ n in atTop, ∀ y : (G n).terminalRegularOpen,
        riemannianEDistOf (scaleMetric (Q n) (hQ n) (L n).metric) (x n) y < ENNReal.ofReal r →
          metricScalarAt (L n).metric y / Q n ≤ A) :
    ∃ (R : ℝ) (ind : ℕ → ℕ), 0 < R ∧ StrictMono ind ∧
      (∀ r : ℝ, 0 < r → r < R → ∃ A : ℝ,
        ∀ᶠ n in atTop,
          IsCompact (riemannianClosedBallOf
            (scaleMetric (Q n) (hQ n) (L n).metric) (x n) r) ∧
          ∀ y : (G n).terminalRegularOpen,
            y ∈ riemannianClosedBallOf
              (scaleMetric (Q n) (hQ n) (L n).metric) (x n) r →
              metricScalarAt (L n).metric y / Q n ≤ A) ∧
      ∃ y : ∀ n, (G (ind n)).terminalRegularOpen,
        (∀ n, riemannianEDistOf
          (scaleMetric (Q (ind n)) (hQ (ind n)) (L (ind n)).metric) (x (ind n)) (y n) ≠ ⊤) ∧
        Tendsto (fun n => (riemannianEDistOf
          (scaleMetric (Q (ind n)) (hQ (ind n)) (L (ind n)).metric) (x (ind n)) (y n)).toReal)
          atTop (𝓝 R) ∧
        Tendsto (fun n => metricScalarAt (L (ind n)).metric (y n) / Q (ind n)) atTop atTop :=
  exists_terminal_scalar_escape_radius_of_derivative_bounds_window_P6WB P a s G L x Q hQ C q hqQ U
    a (fun n => (G n).lt) (fun n y hy t ht _ => hgradient n y hy t ht) hU hx hfail

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
