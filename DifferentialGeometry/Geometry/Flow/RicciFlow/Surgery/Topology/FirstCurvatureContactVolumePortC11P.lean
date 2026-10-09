import DifferentialGeometry.Geometry.Metric.Distance.SublevelMinimizer
import DifferentialGeometry.Geometry.Metric.Distance.Boundary
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitnessBallVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SpatialBoundedCurvatureAtDistance
import DifferentialGeometry.Geometry.Comparison.Volume.Bishop.LocalBallRatio

/-!
# S-CH11-FIX5 port of astra `FirstCurvatureContactVolume`（`PortC11P`）

来源：donor `FirstCurvatureContactVolume.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树有 6 处 elaboration error；本 port 只做下面 6 处 elaboration 层面修补
（no statement / definition / proof idea altered）：
* `exists_first_rm_contact_or_large_ball_control`：`(fun y hy => hy.le)` 改为
  `(fun y hy => le_of_lt (show f y < 1 from hy))`（`hy : y ∈ {y | f y < 1}` 的 dot-notation
  `.le` 在本树找不到 `LT.lt.le` 的目标，先 `show` 成 `<` 形）。
* 两处 `add_le_add_right hzw _` / `add_le_add_right hwz _`（`hseedInside`、`hdomain` 的 calc）
  改为 `add_le_add hzw le_rfl` / `add_le_add hwz le_rfl`（Mathlib 里 `add_le_add_right` 的
  左右加法约定与 donor 相反）。
* `hK`：`norm_num` 之后的 `nlinarith only [hh']` 改为两个 `ring` 等式（`h81`、`h162`）把目标
  两侧改写成 `hh'` 的两侧再 `linarith only`（同 `WholeCanonicalComponentSeedVolume`：`norm_num` 之后
  `9 * (9 * C2 / r ^ 2)` 与 `hh'` 里的 `81 * C2 / r ^ 2` 被 `linarith` 当作不同原子）。
* `hv`（第二次 `volume_lower_of_scaled_rm_bound`）：`hball y hy.le` 改为
  `hball y (show riemannianEDistOf g x y < ENNReal.ofReal D from hy).le`。
* `round` 分支：`rw [hAlt]; trivial` 改为 `trivial`（`cases hAlt : V.alternative` 已把目标里的
  `V.alternative` 换成 `round …`，`rw [hAlt]` 找不到模式）。

原路径 `FirstCurvatureContactVolume` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

private local instance firstContactThreeSpaceNeZero :
    NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp⟩

open private exists_closest_level_in_complete_extension nearest_level_edist_le from
  DifferentialGeometry.Geometry.Metric.Distance.SublevelMinimizer

/-- The nearest curvature level controls the entire original-metric closed ball. -/
private theorem exists_first_rm_contact_or_large_ball_control
    {P : OrientedThreeStage.{u}} (g : P.Metric) (x : P.Carrier)
    (A r : ℝ) (hA : 0 < A) (hr : 0 < r)
    (hnear : ∀ y ∈ riemannianClosedBallOf g x r,
      r ^ 4 * normSq0S g y 4 (metricRm04At g y) ≤ (1 : ℝ) / 4) :
    (∀ y ∈ riemannianBallOf g x ((A + 1) * r),
      r ^ 4 * normSq0S g y 4 (metricRm04At g y) ≤ 1) ∨
    ∃ (D : ℝ) (w : P.Carrier), r ≤ D ∧ D < (A + 1) * r ∧
      riemannianEDistOf g x w = ENNReal.ofReal D ∧
      r ^ 4 * normSq0S g w 4 (metricRm04At g w) = 1 ∧
      ∀ y ∈ riemannianClosedBallOf g x D,
        r ^ 4 * normSq0S g y 4 (metricRm04At g y) ≤ 1 := by
  classical
  let f : P.Carrier → ℝ := fun y => r ^ 4 * normSq0S g y 4 (metricRm04At g y)
  have hf : Continuous f := continuous_const.mul
    (DifferentialGeometry.Tensor.RSTensor.normSq0S_smooth g (metricRm04 g)).continuous
  have hfx : f x < 1 := by
    have hh := hnear x (by
      change riemannianEDistOf g x x ≤ ENNReal.ofReal r
      rw [riemannianEDistOf_self]
      exact bot_le)
    change f x ≤ 1 / 4 at hh
    linarith
  by_cases hlarge : ∀ y ∈ riemannianBallOf g x ((A + 1) * r), f y ≤ 1
  · exact Or.inl hlarge
  push_neg at hlarge
  obtain ⟨z, hz, hfz⟩ := hlarge
  have hR : 0 < (A + 1) * r := by positivity
  have hfinite : riemannianEDistOf g x z ≠ ⊤ := ne_top_of_lt hz
  obtain ⟨g', U, w, _hcomplete, _hU, hKU, heq, _hmono, hw, hfw, hdist, hnearz,
    hnearest⟩ := exists_closest_level_in_complete_extension g f hf
      (isClosed_le hf continuous_const).isCompact x z hfx hfz.le hfinite
  have hfinitew : riemannianEDistOf g x w ≠ ⊤ := by rw [hdist]; exact hfw
  let D := (riemannianEDistOf g x w).toReal
  have hD : riemannianEDistOf g x w = ENNReal.ofReal D :=
    (ENNReal.ofReal_toReal hfinitew).symm
  have hrD : r ≤ D := by
    by_contra hnot
    have hmem : w ∈ riemannianClosedBallOf g x r := by
      change riemannianEDistOf g x w ≤ ENNReal.ofReal r
      rw [hD]
      exact ENNReal.ofReal_le_ofReal (le_of_lt (lt_of_not_ge hnot))
    have hh := hnear w hmem
    change f w ≤ 1 / 4 at hh
    rw [hw] at hh
    norm_num at hh
  have hDR : D < (A + 1) * r := by
    have hh : ENNReal.ofReal D < ENNReal.ofReal ((A + 1) * r) := by
      rw [← hD]
      exact hnearz.trans_lt hz
    exact (ENNReal.ofReal_lt_ofReal_iff hR).mp hh
  have hfront : ∀ v ∈ frontier {y | f y ≤ 1},
      ENNReal.ofReal D ≤ riemannianEDistOf g x v := by
    intro v hv
    have hlevel : f v = 1 := frontier_le_subset_eq hf continuous_const hv
    rw [← hD, hdist]
    exact nearest_level_edist_le g g' f hf hfx hlevel.ge
      (fun y hy => heq y (hKU hy)) hnearest
  have hxint : x ∈ interior {y | f y ≤ 1} := by
    apply mem_interior_iff_mem_nhds.mpr
    exact Filter.mem_of_superset ((isOpen_lt hf continuous_const).mem_nhds hfx)
      (fun y hy => le_of_lt (show f y < 1 from hy))
  have hball := Geometry.Metric.riemannianEDistOf_closedBall_subset_of_le_frontier_distance
    g (isClosed_le hf continuous_const) hxint ENNReal.ofReal_ne_top hfront
  exact Or.inr ⟨D, w, hrD, hDR, hD, hw, fun y hy => hball hy⟩

/-- Square-root form of the actual curvature normalization. -/
private theorem sqrt_rm_le_of_scaled_bound {P : OrientedThreeStage.{u}}
    (g : P.Metric) (y : P.Carrier) {r : ℝ} (hr : 0 < r)
    (h : r ^ 4 * normSq0S g y 4 (metricRm04At g y) ≤ 1) :
    Real.sqrt (normSq0S g y 4 (metricRm04At g y)) ≤ 1 / r ^ 2 := by
  have hN := normSq0S_nonneg g y 4 (metricRm04At g y)
  have hsq : (r ^ 2 * Real.sqrt (normSq0S g y 4 (metricRm04At g y))) ^ 2 ≤ 1 := by
    rw [mul_pow, ← pow_mul, Real.sq_sqrt hN]
    exact h
  have hprod : r ^ 2 * Real.sqrt (normSq0S g y 4 (metricRm04At g y)) ≤ 1 := by
    nlinarith [sq_nonneg (r ^ 2 * Real.sqrt (normSq0S g y 4 (metricRm04At g y)) - 1)]
  apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
  simpa only [mul_comm] using hprod

/-- General Bishop transfer on the original metric, with an upper radius bound. -/
private theorem volume_lower_of_rm_bound {P : OrientedThreeStage.{u}}
    (g : P.Metric) (x : P.Carrier) {q K D R ρ v : ℝ}
    (hq : 0 ≤ q) (hρ : 0 < ρ) (hρD : ρ ≤ D) (hDR : D ≤ R)
    (hK : 9 * K ≤ 2 * q ^ 2)
    (hRm : ∀ y ∈ riemannianBallOf g x D,
      Real.sqrt (normSq0S g y 4 (metricRm04At g y)) ≤ K)
    (hvol : ENNReal.ofReal v ≤
      riemannianVolumeMeasure ThreeModel P.Carrier g (riemannianBallOf g x D)) :
    ENNReal.ofReal (Real.exp (-(2 * q * R)) * (ρ / (2 * R)) ^ 3 * v) ≤
      riemannianVolumeMeasure ThreeModel P.Carrier g (riemannianBallOf g x ρ) := by
  have hD : 0 < D := hρ.trans_le hρD
  have hR : 0 < R := hD.trans_le hDR
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp
  have hRic : ∀ y ∈ riemannianBallOf g x D, ∀ a : TangentSpace ThreeModel y,
      -(((Module.finrank ℝ ThreeSpace - 1 : ℕ) : ℝ) * q ^ 2) * g.inner y a a ≤
        ricciTensor (I := ThreeModel) g y a a := by
    intro y hy a
    have hh := Geometry.Riemannian.BonnetMyers.ricciLowerAt_of_rm
      (I := ThreeModel) g (hRm y hy) a
    have hinner : 0 ≤ g.inner y a a := by
      rcases eq_or_ne a 0 with ha | ha
      · subst a; simp
      · exact (g.pos y a ha).le
    rw [hdim] at hh ⊢
    have hc : -(((3 - 1 : ℕ) : ℝ) * q ^ 2) ≤ -(((3 : ℕ) : ℝ) ^ 2 * K) := by
      norm_num
      linarith
    exact (mul_le_mul_of_nonneg_right hc hinner).trans hh
  have hmain := Geometry.Riemannian.VolumeComparison.riemannianBallOf_volume_ratio_ge_of_ricci_lower
    g (RiemannianMetricComplete.of_compact g) x hq hρ hρD hRic
  rw [hdim] at hmain
  have hexp : Real.exp (-(2 * q * R)) ≤
      Real.exp (-(q * ((3 - 1 : ℕ) : ℝ) * D)) := by
    apply Real.exp_le_exp.mpr
    norm_num
    nlinarith [mul_nonneg hq (sub_nonneg.mpr hDR)]
  have hratio : ρ / (2 * R) ≤ ρ / (2 * D) :=
    div_le_div_of_nonneg_left hρ.le (by positivity) (by linarith)
  have hc : Real.exp (-(2 * q * R)) * (ρ / (2 * R)) ^ 3 ≤
      Real.exp (-(q * ((3 - 1 : ℕ) : ℝ) * D)) * (ρ / (2 * D)) ^ 3 :=
    mul_le_mul hexp (pow_le_pow_left₀ (by positivity) hratio 3)
      (by positivity) (Real.exp_pos _).le
  rw [ENNReal.ofReal_mul (by positivity)]
  exact (mul_le_mul' (ENNReal.ofReal_le_ofReal hc) hvol).trans hmain

/-- Scale cancellation for the preceding original-metric comparison. -/
private theorem volume_lower_of_scaled_rm_bound {P : OrientedThreeStage.{u}}
    (g : P.Metric) (x : P.Carrier) {c k α r ρ D v : ℝ}
    (hc : 0 ≤ c) (hα : 0 < α) (hr : 0 < r) (hρ : 0 < ρ)
    (hρD : ρ ≤ D) (hD : D ≤ α * r) (hk : 9 * k ≤ 2 * c ^ 2)
    (hRm : ∀ y ∈ riemannianBallOf g x D,
      Real.sqrt (normSq0S g y 4 (metricRm04At g y)) ≤ k / r ^ 2)
    (hvol : ENNReal.ofReal (v * r ^ 3) ≤
      riemannianVolumeMeasure ThreeModel P.Carrier g (riemannianBallOf g x D)) :
    ENNReal.ofReal (v * Real.exp (-(2 * c * α)) / (8 * α ^ 3) * ρ ^ 3) ≤
      riemannianVolumeMeasure ThreeModel P.Carrier g (riemannianBallOf g x ρ) := by
  have hk' : 9 * (k / r ^ 2) ≤ 2 * (c / r) ^ 2 := by
    rw [div_pow]
    simpa only [mul_div_assoc] using
      div_le_div_of_nonneg_right hk (sq_nonneg r)
  have hh := volume_lower_of_rm_bound g x (div_nonneg hc hr.le) hρ hρD hD hk' hRm hvol
  have he : 2 * (c / r) * (α * r) = 2 * c * α := by
    field_simp [hr.ne'] <;> ring
  rw [he] at hh
  have ha : Real.exp (-(2 * c * α)) * (ρ / (2 * (α * r))) ^ 3 * (v * r ^ 3) =
      v * Real.exp (-(2 * c * α)) / (8 * α ^ 3) * ρ ^ 3 := by
    field_simp [hr.ne', hα.ne'] <;> ring
  rwa [ha] at hh

/-- Actual seed volume survives the first spatial curvature contact, using its
canonical domain and an inward ball in the same original metric. -/
theorem exists_ball_volume_lower_of_seed_and_canonical_first_contacts
    (ε C1 C2 A : ℝ) (hA : 0 < A) :
    ∃ κ : ℝ, 0 < κ ∧
    ∀ {P : OrientedThreeStage.{u}} (g : P.Metric) (p x : P.Carrier)
      (r ρ : ℝ), 0 < r → 0 < ρ → ρ ≤ r →
      x ∈ riemannianBallOf g p (A * r) →
      metricScalarAt g p ≤ 3 / r ^ 2 →
      ENNReal.ofReal (A⁻¹ * r ^ 3) ≤
        riemannianVolumeMeasure ThreeModel P.Carrier g (riemannianBallOf g p r) →
      (∀ y ∈ riemannianClosedBallOf g x r,
        r ^ 4 * normSq0S g y 4 (metricRm04At g y) ≤ (1 : ℝ) / 4) →
      (∀ w : P.Carrier,
        r ^ 4 * normSq0S g w 4 (metricRm04At g w) = 1 →
        ∃ V : SpatialCanonicalWitness g ε C1 C2 w, V.capTubeHasNeckChart ε) →
      ENNReal.ofReal (κ * ρ ^ 3) ≤
        riemannianVolumeMeasure ThreeModel P.Carrier g (riemannianBallOf g x ρ) := by
  classical
  obtain ⟨κcan, hκcan, hcanonicalVolume⟩ :=
    exists_ball_volume_of_spatialCanonicalWitness.{u} ε C1 C2
  let B : ℝ := max C2 1
  have hB : 0 < B := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hA1 : 0 < A + 1 := by linarith
  let κlarge : ℝ := Real.exp (-(6 * (A + 1))) / (8 * A * (A + 1) ^ 3)
  let κin : ℝ := κcan * Real.exp (-(36 * Real.sqrt B / 100)) / (512 * 100 ^ 3)
  let κcontact : ℝ := κin * Real.exp (-(6 * (A + 1))) / (8 * (A + 1) ^ 3)
  let κwhole : ℝ := Real.exp (-(12 * (C2 + 1) * (A + 1))) / (8 * A * (A + 1) ^ 3)
  let κ : ℝ := min κlarge (min κcontact κwhole)
  have hκlarge : 0 < κlarge := by dsimp [κlarge]; positivity
  have hκin : 0 < κin := by dsimp [κin]; positivity
  have hκcontact : 0 < κcontact := by dsimp [κcontact]; positivity
  have hκwhole : 0 < κwhole := by dsimp [κwhole]; positivity
  refine ⟨κ, lt_min hκlarge (lt_min hκcontact hκwhole), ?_⟩
  intro P g p x r ρ hr hρ hρr hx hseedScalar hseedVolume hnear hcan
  let R : ℝ := (A + 1) * r
  have hrR : r < R := by dsimp [R]; nlinarith [mul_pos hA hr]
  have hxp : riemannianEDistOf g x p < ENNReal.ofReal (A * r) := by
    rw [riemannianEDistOf_comm]
    exact hx
  have hsubset : riemannianBallOf g p r ⊆ riemannianBallOf g x R := by
    intro y hy
    change riemannianEDistOf g x y < ENNReal.ofReal R
    calc
      riemannianEDistOf g x y ≤ riemannianEDistOf g x p + riemannianEDistOf g p y :=
        riemannianEDistOf_triangle g x p y
      _ < ENNReal.ofReal (A * r) + ENNReal.ofReal r := ENNReal.add_lt_add hxp hy
      _ = ENNReal.ofReal R := by
        rw [← ENNReal.ofReal_add (mul_nonneg hA.le hr.le) hr.le]
        congr 1
        dsimp [R]
        ring
  have hlargeVolume : ENNReal.ofReal (A⁻¹ * r ^ 3) ≤
      riemannianVolumeMeasure ThreeModel P.Carrier g (riemannianBallOf g x R) :=
    hseedVolume.trans (measure_mono hsubset)
  have hfinal {k : ℝ} (hk : κ ≤ k)
      (hv : ENNReal.ofReal (k * ρ ^ 3) ≤
        riemannianVolumeMeasure ThreeModel P.Carrier g (riemannianBallOf g x ρ)) :
      ENNReal.ofReal (κ * ρ ^ 3) ≤
        riemannianVolumeMeasure ThreeModel P.Carrier g (riemannianBallOf g x ρ) :=
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hk (by positivity))).trans hv
  rcases exists_first_rm_contact_or_large_ball_control g x A r hA hr hnear with
    hlarge | ⟨D, w, hrD, hDR, hdist, hcontact, hball⟩
  · have hv := volume_lower_of_scaled_rm_bound g x (c := 3) (k := 1)
      (by norm_num) hA1 hr hρ (hρr.trans hrR.le) (le_refl R) (by norm_num)
      (fun y hy => sqrt_rm_le_of_scaled_bound g y hr (hlarge y hy)) hlargeVolume
    apply hfinal (min_le_left _ _)
    have he : A⁻¹ * Real.exp (-(2 * 3 * (A + 1))) / (8 * (A + 1) ^ 3) = κlarge := by
      dsimp [κlarge]
      norm_num
      field_simp [hA.ne', hA1.ne'] <;> ring
    simpa only [he] using hv
  obtain ⟨V, hchart⟩ := hcan w hcontact
  have hC2 : 1 ≤ C2 := V.one_le_comparison_constant
  have hC2pos : 0 < C2 := zero_lt_one.trans_le hC2
  by_cases hreq : V.alternative.requiresVolume
  · let s : ℝ := r / 100
    have hs : 0 < s := by dsimp [s]; positivity
    have hsr : s ≤ r := by dsimp [s]; linarith
    have hsD : s ≤ D := hsr.trans hrD
    have hcompact : IsCompact (riemannianClosedBallOf g x (D + 1)) :=
      (RiemannianMetricComplete.of_compact g).closedEBall_isCompact x (D + 1)
    obtain ⟨γ, d, _hzero, _hend, _hsmooth, _hmetric, _hd, _hdD, _hld, hzw, hinside⟩ :=
      Geometry.Riemannian.exists_inward_point_and_minimizer_of_isCompact_closedBall
        g x w hs hsD hdist.le (lt_add_one D) hcompact
    let z := γ d
    have hWvolume : ENNReal.ofReal (κcan * s ^ 3) ≤
        riemannianVolumeMeasure ThreeModel P.Carrier g (riemannianBallOf g w s) := by
      apply hcanonicalVolume V hchart hreq s hs
      exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs.le hsr 4)
        (normSq0S_nonneg g w 4 (metricRm04At g w))).trans hcontact.le
    have hseedInside : riemannianBallOf g w s ⊆ riemannianBallOf g z (2 * s) := by
      intro y hy
      change riemannianEDistOf g z y < ENNReal.ofReal (2 * s)
      calc
        riemannianEDistOf g z y ≤ riemannianEDistOf g z w + riemannianEDistOf g w y :=
          riemannianEDistOf_triangle g z w y
        _ ≤ ENNReal.ofReal s + riemannianEDistOf g w y := add_le_add hzw le_rfl
        _ < ENNReal.ofReal s + ENNReal.ofReal s :=
          ENNReal.add_lt_add_left ENNReal.ofReal_ne_top hy
        _ = ENNReal.ofReal (2 * s) := by rw [← ENNReal.ofReal_add hs.le hs.le]; congr 1; ring
    have hinnerSeed : ENNReal.ofReal (κcan * s ^ 3) ≤
        riemannianVolumeMeasure ThreeModel P.Carrier g (riemannianBallOf g z (2 * s)) :=
      hWvolume.trans (measure_mono hseedInside)
    have hthree := sqrt_scalarAt_mul_le_three_of_rm_le g w hcontact.le
    have hscalar : metricScalarAt g w ≤ 9 / r ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
      have hh := (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) hr.le) (by norm_num : (0 : ℝ) ≤ 3)).mpr hthree
      rwa [mul_pow, Real.sq_sqrt V.Q_pos.le, show (3 : ℝ) ^ 2 = 9 by norm_num] at hh
    have hsmall : 3 * s ≤ (Real.sqrt (metricScalarAt g w))⁻¹ := by
      rw [inv_eq_one_div]
      apply (le_div_iff₀ (Real.sqrt_pos.mpr V.Q_pos)).mpr
      dsimp [s]
      nlinarith only [hthree]
    have hdomain : riemannianBallOf g z (2 * s) ⊆ V.domain.carrier := by
      intro y hy
      apply V.ball_inside
      apply riemannianBallOf_mono g w (hsmall.trans V.radius_lower)
      change riemannianEDistOf g w y < ENNReal.ofReal (3 * s)
      have hwz : riemannianEDistOf g w z ≤ ENNReal.ofReal s := by
        rw [riemannianEDistOf_comm]
        exact hzw
      calc
        riemannianEDistOf g w y ≤ riemannianEDistOf g w z + riemannianEDistOf g z y :=
          riemannianEDistOf_triangle g w z y
        _ ≤ ENNReal.ofReal s + riemannianEDistOf g z y := add_le_add hwz le_rfl
        _ < ENNReal.ofReal s + ENNReal.ofReal (2 * s) :=
          ENNReal.add_lt_add_left ENNReal.ofReal_ne_top hy
        _ = ENNReal.ofReal (3 * s) := by
          rw [← ENNReal.ofReal_add hs.le (by positivity)]
          congr 1
          ring
    have hRm : ∀ y ∈ riemannianBallOf g z (2 * s),
        Real.sqrt (normSq0S g y 4 (metricRm04At g y)) ≤ 9 * C2 / r ^ 2 := by
      intro y hy
      calc
        Real.sqrt (normSq0S g y 4 (metricRm04At g y)) ≤ C2 * metricScalarAt g w :=
          V.rm_bound y (hdomain hy)
        _ ≤ C2 * (9 / r ^ 2) := mul_le_mul_of_nonneg_left hscalar hC2pos.le
        _ = 9 * C2 / r ^ 2 := by ring
    have hK : 9 * (9 * C2 / r ^ 2) ≤ 2 * (9 * Real.sqrt B / r) ^ 2 := by
      rw [div_pow, mul_pow, Real.sq_sqrt hB.le]
      have hCB : C2 ≤ B := le_max_left _ _
      have hh : 81 * C2 ≤ 162 * B := by linarith [hB.le]
      have hh' := div_le_div_of_nonneg_right hh (sq_nonneg r)
      norm_num
      have h81 : 9 * (9 * C2 / r ^ 2) = 81 * C2 / r ^ 2 := by ring
      have h162 : 2 * (81 * B / r ^ 2) = 162 * B / r ^ 2 := by ring
      linarith only [hh', h81, h162]
    have hinner := volume_lower_of_rm_bound g z (q := 9 * Real.sqrt B / r)
      (by positivity) (show 0 < s / 2 by positivity) (show s / 2 ≤ 2 * s by linarith)
      (le_refl (2 * s)) hK hRm hinnerSeed
    have hexponent : 2 * (9 * Real.sqrt B / r) * (2 * s) = 36 * Real.sqrt B / 100 := by
      dsimp [s]
      field_simp [hr.ne'] <;> ring
    have hcoefficient : Real.exp (-(2 * (9 * Real.sqrt B / r) * (2 * s))) *
        ((s / 2) / (2 * (2 * s))) ^ 3 * (κcan * s ^ 3) = κin * r ^ 3 := by
      rw [hexponent]
      dsimp [κin, s]
      field_simp [hr.ne'] <;> ring
    rw [hcoefficient] at hinner
    have hvolumeD : ENNReal.ofReal (κin * r ^ 3) ≤
        riemannianVolumeMeasure ThreeModel P.Carrier g (riemannianBallOf g x D) := by
      apply hinner.trans
      apply measure_mono
      intro y hy
      apply hinside
      exact (show riemannianEDistOf g z y < ENNReal.ofReal (s / 2) from hy).le
    have hv := volume_lower_of_scaled_rm_bound g x (c := 3) (k := 1)
      (by norm_num) hA1 hr hρ (hρr.trans hrD) hDR.le (by norm_num)
      (fun y hy => sqrt_rm_le_of_scaled_bound g y hr
        (hball y (show riemannianEDistOf g x y < ENNReal.ofReal D from hy).le)) hvolumeD
    apply hfinal ((min_le_right _ _).trans (min_le_left _ _))
    simpa only [show (2 : ℝ) * 3 = 6 by norm_num] using hv
  · have hwhole : V.alternative.isWholeComponent := by
      cases hAlt : V.alternative with
      | neck _data => exact (hreq (by rw [hAlt]; trivial)).elim
      | cap _data _deep => exact (hreq (by rw [hAlt]; trivial)).elim
      | positive _whole _data _sec => exact (hreq (by rw [hAlt]; trivial)).elim
      | round _whole _data => trivial
    have hwx : riemannianEDistOf g w x < ⊤ := by
      rw [riemannianEDistOf_comm, hdist]
      exact ENNReal.ofReal_lt_top
    have hwp : riemannianEDistOf g w p < ⊤ :=
      (riemannianEDistOf_triangle g w x p).trans_lt
        (ENNReal.add_lt_top.mpr ⟨hwx, hxp.trans ENNReal.ofReal_lt_top⟩)
    have hscalarLower : C2⁻¹ * metricScalarAt g w ≤ 3 / r ^ 2 :=
      (V.scalar_bounds_of_isWholeComponent hwhole hwp).1.trans hseedScalar
    have hscalar : metricScalarAt g w ≤ 3 * C2 / r ^ 2 := by
      calc
        metricScalarAt g w = C2 * (C2⁻¹ * metricScalarAt g w) := by
          rw [← mul_assoc, mul_inv_cancel₀ hC2pos.ne', one_mul]
        _ ≤ C2 * (3 / r ^ 2) := mul_le_mul_of_nonneg_left hscalarLower hC2pos.le
        _ = 3 * C2 / r ^ 2 := by ring
    have hRm : ∀ y ∈ riemannianBallOf g x R,
        Real.sqrt (normSq0S g y 4 (metricRm04At g y)) ≤ 3 * C2 ^ 2 / r ^ 2 := by
      intro y hy
      have hwy : riemannianEDistOf g w y < ⊤ :=
        (riemannianEDistOf_triangle g w x y).trans_lt
          (ENNReal.add_lt_top.mpr ⟨hwx,
            (show riemannianEDistOf g x y < ENNReal.ofReal R from hy).trans ENNReal.ofReal_lt_top⟩)
      have hyDomain : y ∈ V.domain.carrier := by
        rw [V.alternative.eq_connectedComponent_of_isWholeComponent hwhole]
        exact mem_connectedComponent_of_riemannianEDistOf_lt_top g hwy
      calc
        Real.sqrt (normSq0S g y 4 (metricRm04At g y)) ≤ C2 * metricScalarAt g w :=
          V.rm_bound y hyDomain
        _ ≤ C2 * (3 * C2 / r ^ 2) := mul_le_mul_of_nonneg_left hscalar hC2pos.le
        _ = 3 * C2 ^ 2 / r ^ 2 := by ring
    have hv := volume_lower_of_scaled_rm_bound g x (c := 6 * (C2 + 1)) (k := 3 * C2 ^ 2)
      (by positivity) hA1 hr hρ (hρr.trans hrR.le) (le_refl R)
      (by nlinarith only [sq_nonneg C2, hC2pos.le]) hRm hlargeVolume
    apply hfinal ((min_le_right _ _).trans (min_le_right _ _))
    have he : A⁻¹ * Real.exp (-(2 * (6 * (C2 + 1)) * (A + 1))) /
        (8 * (A + 1) ^ 3) = κwhole := by
      rw [show 2 * (6 * (C2 + 1)) * (A + 1) = 12 * (C2 + 1) * (A + 1) by ring]
      dsimp [κwhole]
      field_simp [hA.ne', hA1.ne'] <;> ring
    simpa only [he] using hv

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
