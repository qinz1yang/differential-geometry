import DifferentialGeometry.Geometry.Metric.Distance.SublevelMinimizer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarSublevel
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.TerminalScalarBall_P6L
import DifferentialGeometry.Geometry.Metric.Distance.Ball

/-!
# L6-A 第 3 层：`TerminalCurvatureEscape` 的局部化（`_P6L`，合同表 §3 行 5–6）

局部化合同 `docs/geometrization/chapter8/design-C11-P6-localization-contract-20261006.md`
§1.4 与 §2 (G)：
* `exists_terminal_scalar_escape_radius_of_derivative_bounds`（`ST/TerminalCurvatureEscape:166`）：
  `hgradient` 只经 `TerminalScalarBall:110` 在 `x n` 的 r₀-小球上用 ⇒ 限于 `U n`，加移动球包含
  `hU n : ∀ᶠ t in 𝓝[<] s n, B_t(x n, 2·localPropagationRadius C/√(2 Q n)) ⊆ U n`
  （与 G6 `TerminalScalarBall_P6L` 同形，叶子换 `_P6L`）。
  `D` / `htime`（final-slab 导数界）只为闭球紧致（原 l.241）⇒ **删去**，紧致改由无前提的
  `TerminalLimitMetric.isCompact_scalar_sublevel`（`ST/TerminalScalarSublevel:28`）给。
* private `terminal_level_sublevel_isCompact`（`:292`）删 `D`/`htime` 后即
  `isCompact_scalar_sublevel`，不再单独复制；private `exists_terminal_scalar_level_minimizers`
  （`:303`）与 `exists_terminal_minimizing_segments_at_scalar_escape_radius`（`:358`）删 `D`/`htime`。
* 无前提的 private 引理 `:12,:44,:63,:139` 原样复制为 private `_P6L`（合同 §1.2，不 `open private`）。
证明体照抄；结论逐字。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private theorem exists_radius_of_not_eventually_bounded_P6L
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

private theorem abs_sub_lt_div_of_escape_radii_P6L {R d : ℝ} {k : ℕ} (hR : 0 < R)
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

private theorem exists_subsequence_radius_escape_P6L
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
  obtain ⟨R, hR₀, hinner, houter⟩ := exists_radius_of_not_eventually_bounded_P6L d f hsmall hfail
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
    apply abs_sub_lt_div_of_escape_radii_P6L hR
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

private theorem tendsto_radius_of_inner_bounds_of_escape_P6L
    {M : ℕ → Type*} (d : ∀ n, M n → ℝ≥0∞) (f : ∀ n, M n → ℝ)
    {R : ℝ} (hR : 0 < R)
    (hinner : ∀ r : ℝ, 0 < r → r < R → ∃ C : ℝ,
      ∀ᶠ n in atTop, ∀ y, d n y < ENNReal.ofReal r → f n y ≤ C)
    (z y : ∀ n, M n) (hfinite : ∀ n, d n (z n) ≠ ⊤)
    (hupper : ∀ n, d n (y n) ≤ d n (z n))
    (hdist : Tendsto (fun n => (d n (z n)).toReal) atTop (𝓝 R))
    (hscalar : Tendsto (fun n => f n (y n)) atTop atTop) :
    (∀ n, d n (y n) ≠ ⊤) ∧ Tendsto (fun n => (d n (y n)).toReal) atTop (𝓝 R) := by
  have hfin (n) : d n (y n) ≠ ⊤ := ne_top_of_le_ne_top (hfinite n) (hupper n)
  refine ⟨hfin, tendsto_order.mpr ⟨?_, ?_⟩⟩
  · intro a ha
    obtain ⟨r, hrlo, hrhi⟩ := exists_between (max_lt (by linarith : (0 : ℝ) < R) ha)
    have hr : 0 < r := (le_max_left _ _).trans_lt hrlo
    have har : a < r := (le_max_right _ _).trans_lt hrlo
    obtain ⟨C, hC⟩ := hinner r hr hrhi
    filter_upwards [hC, hscalar.eventually_gt_atTop C] with n hn hhigh
    have hnot : ¬ d n (y n) < ENNReal.ofReal r := fun h => (not_lt_of_ge (hn _ h)) hhigh
    have hlow : r ≤ (d n (y n)).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal (hfin n)).mp (le_of_not_gt hnot)
    exact har.trans_le hlow
  · intro b hb
    filter_upwards [hdist.eventually_lt_const hb] with n hn
    exact (ENNReal.toReal_mono (hfinite n) (hupper n)).trans_lt hn



/-- **`_P6L`（合同 §3 行 5）**：原 `exists_terminal_scalar_escape_radius_of_derivative_bounds`
（`ST/TerminalCurvatureEscape:166`）。改动：`hgradient` 限于 `U n`；加 `hU`（移动球包含，
成员关系来源：`TerminalScalarBall:110_P6L` 在 `x n` 处 r₀ = rad_C/(2√2) 小球的路径点距 `x n`
< 2·rad_C/√(2Q n)）；删 `D`/`htime`（原 l.241 只为闭球紧致，改用无前提的
`TerminalLimitMetric.isCompact_scalar_sublevel`）。结论逐字。 -/
theorem exists_terminal_scalar_escape_radius_of_derivative_bounds_P6L
    (P : ℕ → OrientedThreeStage.{u}) (a s : ℕ → ℝ)
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
      ((L n).scalar_le_on_small_ball_of_gradient_bound_P6L C (hQ n) (hqQ n) (U n)
        (hgradient n) (x n) (hU n) (hx n) y hball)
  obtain ⟨R, ind, hR, hind, hinner, y, hfinite, hdist, hscalar⟩ :=
    exists_subsequence_radius_escape_P6L d f hr₀ hsmall hfail
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


private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

/-- **`_P6L`（合同 §3 行 6）**：原 private `exists_terminal_scalar_level_minimizers`（`TCE:303`）。
改动：删 `D`/`htime`（只经 `:292` 为 sublevel 紧致，改 `isCompact_scalar_sublevel`）。 -/
private theorem exists_terminal_scalar_level_minimizers_P6L
    (P : ℕ → OrientedThreeStage.{u}) (a s : ℕ → ℝ)
    (G : ∀ n, (P n).IncomingSlab (a n) (s n))
    (L : ∀ n, (G n).TerminalLimitMetric)
    (p z : ∀ n, (G n).terminalRegularOpen)
    (Q : ℕ → ℝ) (hQ : ∀ n, 0 < Q n)
    (hp : ∀ n, metricScalarAt (L n).metric (p n) ≤ Q n)
    (hhigh : ∀ n, 2 ≤ metricScalarAt (L n).metric (z n) / Q n)
    (hfinite : ∀ n, riemannianEDistOf (L n).metric (p n) (z n) ≠ ⊤) :
    ∃ (A : ℕ → ℝ) (y : ∀ n, (G n).terminalRegularOpen)
      (gamma : ∀ n, ℝ → (G n).terminalRegularOpen),
      (∀ n, A n = min ((n : ℝ) + 2) (metricScalarAt (L n).metric (z n) / Q n)) ∧
      (∀ n, metricScalarAt (L n).metric (y n) / Q n = A n) ∧
      (∀ n, riemannianEDistOf (scaleMetric (Q n) (hQ n) (L n).metric) (p n) (y n) ≠ ⊤) ∧
      (∀ n, riemannianEDistOf (scaleMetric (Q n) (hQ n) (L n).metric) (p n) (y n) ≤
        riemannianEDistOf (scaleMetric (Q n) (hQ n) (L n).metric) (p n) (z n)) ∧
      ∀ n,
        let ell := (riemannianEDistOf (scaleMetric (Q n) (hQ n) (L n).metric) (p n) (y n)).toReal
        gamma n 0 = p n ∧ gamma n ell = y n ∧
        ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel ∞ (gamma n) (Icc 0 ell) ∧
        (∀ t ∈ Ico 0 ell, metricScalarAt (L n).metric (gamma n t) / Q n < A n) ∧
        (∀ t ∈ Icc 0 ell, metricScalarAt (L n).metric (gamma n t) / Q n ≤ A n) ∧
        ∀ t ∈ Icc 0 ell, ∀ u ∈ Icc 0 ell,
          riemannianEDistOf (scaleMetric (Q n) (hQ n) (L n).metric) (gamma n t) (gamma n u) =
            ENNReal.ofReal |t - u| := by
  classical
  let A : ℕ → ℝ := fun n => min ((n : ℝ) + 2) (metricScalarAt (L n).metric (z n) / Q n)
  have hA (n) : 2 ≤ A n := le_min (by linarith [Nat.cast_nonneg (α := ℝ) n]) (hhigh n)
  let g := fun n => scaleMetric (Q n) (hQ n) (L n).metric
  let f := fun n (x : (G n).terminalRegularOpen) => metricScalarAt (L n).metric x / Q n
  have hf (n) : Continuous (f n) := (metricScalar_smooth (L n).metric).continuous.div_const _
  have hK (n) : IsCompact {x : (G n).terminalRegularOpen | f n x ≤ A n} := by
    have heq : {x : (G n).terminalRegularOpen | f n x ≤ A n} =
        {x : (G n).terminalRegularOpen | metricScalarAt (L n).metric x ≤ A n * Q n} := by
      ext x
      exact div_le_iff₀ (hQ n)
    rw [heq]
    exact (L n).isCompact_scalar_sublevel (A n * Q n)
  have hpA (n) : f n (p n) < A n := by
    have hbase : f n (p n) ≤ 1 := (div_le_one (hQ n)).mpr (hp n)
    linarith [hA n]
  have hzA (n) : A n ≤ f n (z n) := min_le_right _ _
  have hfin (n) : riemannianEDistOf (g n) (p n) (z n) ≠ ⊤ := by
    rw [DifferentialGeometry.edistOf_scale]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfinite n)
  choose y gamma hlevel hfiniteY hle hzero hend hsmooth hbelow hbound hdist using
    fun n => Geometry.exists_minimizing_segment_to_level_of_isCompact_sublevel
      (g n) (f n) (hf n) (hK n) (p n) (z n) (hpA n) (hzA n) (hfin n)
  exact ⟨A, y, gamma, fun _ => rfl, hlevel, hfiniteY, hle,
    fun n => ⟨hzero n, hend n, hsmooth n, hbelow n, hbound n, hdist n⟩⟩


/-- **`_P6L`（合同 §3 行 6）**：原 `exists_terminal_minimizing_segments_at_scalar_escape_radius`
（`TCE:358`）。改动：删 `D`/`htime`（只经 `:303 → :292` 为 sublevel 紧致）。其余前提本就只涉及
终端极限度量（无 carrier 全局前提）；结论逐字。 -/
theorem exists_terminal_minimizing_segments_at_scalar_escape_radius_P6L
    (P : ℕ → OrientedThreeStage.{u}) (a s : ℕ → ℝ)
    (G : ∀ n, (P n).IncomingSlab (a n) (s n))
    (L : ∀ n, (G n).TerminalLimitMetric)
    (p z : ∀ n, (G n).terminalRegularOpen)
    (Q : ℕ → ℝ) (hQ : ∀ n, 0 < Q n)
    (hp : ∀ n, metricScalarAt (L n).metric (p n) ≤ Q n)
    (hfinite : ∀ n, riemannianEDistOf (scaleMetric (Q n) (hQ n) (L n).metric) (p n) (z n) ≠ ⊤)
    {R : ℝ} (hR : 0 < R)
    (hdist : Tendsto (fun n => (riemannianEDistOf
      (scaleMetric (Q n) (hQ n) (L n).metric) (p n) (z n)).toReal) atTop (𝓝 R))
    (hhigh : Tendsto (fun n => metricScalarAt (L n).metric (z n) / Q n) atTop atTop)
    (hinner : ∀ r : ℝ, 0 < r → r < R → ∃ C : ℝ,
      ∀ᶠ n in atTop, ∀ y : (G n).terminalRegularOpen,
        riemannianEDistOf (scaleMetric (Q n) (hQ n) (L n).metric) (p n) y < ENNReal.ofReal r →
          metricScalarAt (L n).metric y / Q n ≤ C) :
    ∃ (ind : ℕ → ℕ), StrictMono ind ∧
      ∃ (A ell : ℕ → ℝ) (y : ∀ n, (G (ind n)).terminalRegularOpen)
        (gamma : ∀ n, ℝ → (G (ind n)).terminalRegularOpen),
        (∀ n, A n = min ((n : ℝ) + 2) (metricScalarAt (L (ind n)).metric (z (ind n)) / Q (ind n))) ∧
        Tendsto A atTop atTop ∧ Tendsto ell atTop (𝓝 R) ∧
        (∀ n, 0 < ell n) ∧
        (∀ n, metricScalarAt (L (ind n)).metric (y n) / Q (ind n) = A n) ∧
        (∀ n, riemannianEDistOf (scaleMetric (Q (ind n)) (hQ (ind n)) (L (ind n)).metric)
          (p (ind n)) (y n) = ENNReal.ofReal (ell n)) ∧
        (∀ n, ENNReal.ofReal (ell n) ≤ riemannianEDistOf
          (scaleMetric (Q (ind n)) (hQ (ind n)) (L (ind n)).metric) (p (ind n)) (z (ind n))) ∧
        (∀ n, gamma n 0 = p (ind n) ∧ gamma n (ell n) = y n) ∧
        (∀ n, ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel ∞ (gamma n) (Icc 0 (ell n))) ∧
        (∀ n, ∀ t ∈ Ico 0 (ell n),
          metricScalarAt (L (ind n)).metric (gamma n t) / Q (ind n) < A n) ∧
        (∀ n, ∀ t ∈ Icc 0 (ell n),
          metricScalarAt (L (ind n)).metric (gamma n t) / Q (ind n) ≤ A n) ∧
        ∀ n, ∀ t ∈ Icc 0 (ell n), ∀ u ∈ Icc 0 (ell n),
          riemannianEDistOf (scaleMetric (Q (ind n)) (hQ (ind n)) (L (ind n)).metric)
            (gamma n t) (gamma n u) = ENNReal.ofReal |t - u| := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hhigh.eventually_ge_atTop 2)
  let ind : ℕ → ℕ := fun n => n + N
  have hind : StrictMono ind := fun _ _ h => Nat.add_lt_add_right h N
  have hfinOriginal (n) : riemannianEDistOf (L (ind n)).metric (p (ind n)) (z (ind n)) ≠ ⊤ := by
    have hh := hfinite (ind n)
    rw [DifferentialGeometry.edistOf_scale] at hh
    intro htop
    rw [htop, ENNReal.mul_top
      (ENNReal.ofReal_ne_zero_iff.mpr (Real.sqrt_pos.mpr (hQ (ind n))))] at hh
    exact hh rfl
  obtain ⟨A, y, gamma, hA, hlevel, hfiny, hle, hsegments⟩ :=
    exists_terminal_scalar_level_minimizers_P6L (P ∘ ind) (a ∘ ind) (s ∘ ind)
      (fun n => G (ind n)) (fun n => L (ind n)) (fun n => p (ind n)) (fun n => z (ind n))
      (Q ∘ ind) (fun n => hQ (ind n))
      (fun n => hp (ind n)) (fun n => hN (ind n) (Nat.le_add_left N n)) hfinOriginal
  simp only [Function.comp_apply] at hA hlevel hfiny hle hsegments
  let ell := fun n => (riemannianEDistOf
    (scaleMetric (Q (ind n)) (hQ (ind n)) (L (ind n)).metric) (p (ind n)) (y n)).toReal
  have hAhigh : Tendsto A atTop atTop := by
    apply tendsto_atTop.mpr
    intro B
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop B,
      (hhigh.comp hind.tendsto_atTop).eventually_ge_atTop B] with n hn hzn
    rw [hA n]
    exact le_min (by linarith) hzn
  have hinner' : ∀ r : ℝ, 0 < r → r < R → ∃ C : ℝ,
      ∀ᶠ n in atTop, ∀ x : (G (ind n)).terminalRegularOpen,
        riemannianEDistOf (scaleMetric (Q (ind n)) (hQ (ind n)) (L (ind n)).metric) (p (ind n)) x <
          ENNReal.ofReal r → metricScalarAt (L (ind n)).metric x / Q (ind n) ≤ C := by
    intro r hr hrR
    obtain ⟨C, hC⟩ := hinner r hr hrR
    exact ⟨C, hind.tendsto_atTop.eventually hC⟩
  have hYhigh :
      Tendsto (fun n => metricScalarAt (L (ind n)).metric (y n) / Q (ind n)) atTop atTop := by
    simpa only [hlevel] using hAhigh
  have hell := (tendsto_radius_of_inner_bounds_of_escape_P6L
    (fun n x => riemannianEDistOf (scaleMetric (Q (ind n)) (hQ (ind n)) (L (ind n)).metric)
      (p (ind n)) x)
    (fun n x => metricScalarAt (L (ind n)).metric x / Q (ind n)) hR hinner'
    (fun n => z (ind n)) y (fun n => hfinite (ind n)) hle
    (hdist.comp hind.tendsto_atTop) hYhigh).2
  have hellpos (n) : 0 < ell n := by
    have hA2 : 2 ≤ A n := by
      rw [hA n]
      exact le_min (by linarith [Nat.cast_nonneg (α := ℝ) n]) (hN (ind n) (Nat.le_add_left N n))
    have hne : (p (ind n)) ≠ y n := by
      intro h
      have hbase := (div_le_one (hQ (ind n))).mpr (hp (ind n))
      rw [h, hlevel n] at hbase
      linarith
    have hdne : riemannianEDistOf
        (scaleMetric (Q (ind n)) (hQ (ind n)) (L (ind n)).metric) (p (ind n)) (y n) ≠ 0 := by
      intro hzero
      have hseg := (hsegments n).1
      have hend := (hsegments n).2.1
      rw [hzero, ENNReal.toReal_zero, hseg] at hend
      exact hne hend
    exact ENNReal.toReal_pos hdne (hfiny n)
  have heqd (n) : riemannianEDistOf
      (scaleMetric (Q (ind n)) (hQ (ind n)) (L (ind n)).metric) (p (ind n)) (y n) =
        ENNReal.ofReal (ell n) :=
    (ENNReal.ofReal_toReal (hfiny n)).symm
  refine ⟨ind, hind, A, ell, y, gamma, hA, hAhigh, hell, hellpos, hlevel, heqd,
    (fun n => (heqd n).symm ▸ hle n), ?_, ?_, ?_, ?_, ?_⟩
  · exact fun n => ⟨(hsegments n).1, (hsegments n).2.1⟩
  · exact fun n => (hsegments n).2.2.1
  · exact fun n => (hsegments n).2.2.2.1
  · exact fun n => (hsegments n).2.2.2.2.1
  · exact fun n => (hsegments n).2.2.2.2.2

/-- consumer：原 `TCE:166` 的全局形（carrier 全局 `hgradient`；不需要 `D`/`htime`）由 `_P6L` 版
（`U n = univ`）推出：escape 半径 + 逃逸点序列的数据可用。 -/
example (P : ℕ → OrientedThreeStage.{u}) (a s : ℕ → ℝ)
    (G : ∀ n, (P n).IncomingSlab (a n) (s n))
    (L : ∀ n, (G n).TerminalLimitMetric)
    (x : ∀ n, (G n).terminalRegularOpen)
    (Q : ℕ → ℝ) (hQ : ∀ n, 0 < Q n)
    (C : ℝ≥0) (q : ℕ → ℝ) (hqQ : ∀ n, q n ≤ Q n)
    (hgradient : ∀ n, ∀ y : (P n).Carrier, ∀ t ∈ Ioo (a n) (s n),
      q n < (G n).flow.scalar t y → ∀ v : TangentSpace ThreeModel y,
        |scalarDifferential (G n).flow t y v| ≤ C * (G n).flow.scalar t y *
          Real.sqrt ((G n).flow.scalar t y) *
            Real.sqrt (((G n).flow.base.metric t).inner y v v))
    (hx : ∀ n, metricScalarAt (L n).metric (x n) ≤ Q n)
    (hfail : ∃ r : ℝ, 0 < r ∧ ¬ ∃ A : ℝ,
      ∀ᶠ n in atTop, ∀ y : (G n).terminalRegularOpen,
        riemannianEDistOf (scaleMetric (Q n) (hQ n) (L n).metric) (x n) y < ENNReal.ofReal r →
          metricScalarAt (L n).metric y / Q n ≤ A) :
    ∃ (R : ℝ) (ind : ℕ → ℕ), 0 < R ∧ StrictMono ind ∧
      ∃ y : ∀ n, (G (ind n)).terminalRegularOpen,
        Tendsto (fun n => metricScalarAt (L (ind n)).metric (y n) / Q (ind n)) atTop atTop := by
  obtain ⟨R, ind, hR, hind, -, y, -, -, hscalar⟩ :=
    exists_terminal_scalar_escape_radius_of_derivative_bounds_P6L P a s G L x Q hQ C q hqQ
      (fun _ => univ) (fun n y _ => hgradient n y)
      (fun _ => Eventually.of_forall fun _ => subset_univ _) hx hfail
  exact ⟨R, ind, hR, hind, y, hscalar⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
