import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceSlice
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BoundedCurvatureAtDistanceChainBuffers_P6L

/-!
# L6-A spine 第 1 件：rebase chain 的局部化（`_P6L`，合同表 §3 行 15 之 `Slice:246`）

局部化合同 `docs/geometrization/chapter8/design-C11-P6-localization-contract-20261006.md` §2 (G)、
rev1a-centers C2.2（链形层：点成员前提）：原 `OrientedThreeStage.ClosedSlab.exists_rebase_chain`
（`ST/BoundedCurvatureAtDistanceSlice.lean:246`）的 `hgradient : ∀ y, …`（carrier 全局）只在链点
`pc k`（`y → x` 的 minimizing segment 上的等分点）经 `CB:18` 求值。这里 `hgradient` 限于 `U`，
加链点成员前提的**生成形**：`hU : ∀ w, d_T(y, w) < r → B_T(w, 4·rad_C/√(2m)) ⊆ U`（`m = max q R(y)`）；
链点 `d_T(y, pc k) = min(kℓ/N, ℓ) ≤ ℓ < r`（segment 等距），`CB:18` 换 P6C 的静态版
`ClosedSlab.scalar_le_six_mul_on_ball_of_gradient_bound_static_P6L`。私有 `:229,:237` 无前提，原样复制。
证明体照抄；结论逐字。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
private theorem ceil_mul_le_P6L {ℓ r₀ : ℝ} (hℓ : 0 ≤ ℓ) (hr₀ : 0 < r₀) :
    ((⌈ℓ / (r₀ / 2)⌉₊ + 1 : ℕ) : ℝ) * r₀ ≤ 2 * ℓ + 2 * r₀ := by
  have h1 : ((⌈ℓ / (r₀ / 2)⌉₊ : ℕ) : ℝ) < ℓ / (r₀ / 2) + 1 :=
    Nat.ceil_lt_add_one (div_nonneg hℓ (by positivity))
  have h2 : ℓ / (r₀ / 2) * r₀ = 2 * ℓ := by field_simp
  push_cast
  nlinarith

private theorem div_ceil_lt_P6L {ℓ r₀ : ℝ} (hr₀ : 0 < r₀) :
    ℓ / ((⌈ℓ / (r₀ / 2)⌉₊ + 1 : ℕ) : ℝ) < r₀ := by
  have hN : (0 : ℝ) < ((⌈ℓ / (r₀ / 2)⌉₊ + 1 : ℕ) : ℝ) := by positivity
  rw [div_lt_iff₀ hN]
  have h1 : ℓ / (r₀ / 2) ≤ ((⌈ℓ / (r₀ / 2)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have h2 : ℓ = ℓ / (r₀ / 2) * (r₀ / 2) := by field_simp
  push_cast
  nlinarith

/-- **`_P6L`**：原 `OrientedThreeStage.ClosedSlab.exists_rebase_chain`（`Slice:246`）。
`hgradient` 限于 `U`；加链点生成形成员前提 `hU`。结论逐字。 -/
theorem OrientedThreeStage.ClosedSlab.exists_rebase_chain_P6L {P : OrientedThreeStage.{u}}
    {a T : ℝ} (A : P.ClosedSlab a T) (Cgrad : ℝ≥0) {q : ℝ} (hq : 0 < q)
    (U : Set P.Carrier)
    (hgradient : ∀ y ∈ U, ∀ t ∈ Ioo a T, q < A.flow.scalar t y →
      ∀ v : TangentSpace ThreeModel y,
        |scalarDifferential (A.restrictIncoming le_rfl A.lt le_rfl).flow t y v| ≤
          Cgrad * A.flow.scalar t y * Real.sqrt (A.flow.scalar t y) *
            Real.sqrt ((A.flow.base.metric t).inner y v v))
    (y z : P.Carrier) {r : ℝ}
    (hyz : riemannianEDistOf (A.flow.base.metric T) y z < ENNReal.ofReal r)
    (hz : max q (A.flow.scalar T y) ≤ A.flow.scalar T z)
    (hU : ∀ w, riemannianEDistOf (A.flow.base.metric T) y w < ENNReal.ofReal r →
      riemannianBallOf (A.flow.base.metric T) w
        (2 * (2 * (localPropagationRadius Cgrad /
          Real.sqrt (2 * max q (A.flow.scalar T y))))) ⊆ U) :
    ∃ (x : P.Carrier) (Nc : ℕ) (pc : ℕ → P.Carrier),
      A.flow.scalar T x = max q (A.flow.scalar T y) ∧
      riemannianEDistOf (A.flow.base.metric T) y x < ENNReal.ofReal r ∧
      pc 0 = y ∧ pc Nc = x ∧
      (∀ k < Nc, pc (k + 1) ∈ riemannianBallOf (A.flow.base.metric T) (pc k)
        (localPropagationRadius Cgrad / (2 * Real.sqrt (2 * max q (A.flow.scalar T y))))) ∧
      (∀ k < Nc, ∀ w ∈ riemannianBallOf (A.flow.base.metric T) (pc k)
        (localPropagationRadius Cgrad / (2 * Real.sqrt (2 * max q (A.flow.scalar T y)))),
        A.flow.scalar T w ≤ 6 * max q (A.flow.scalar T y)) ∧
      (Nc : ℝ) *
          (localPropagationRadius Cgrad / (2 * Real.sqrt (2 * max q (A.flow.scalar T y)))) ≤
        2 * r + 2 * (localPropagationRadius Cgrad /
          (2 * Real.sqrt (2 * max q (A.flow.scalar T y)))) := by
  set m := max q (A.flow.scalar T y) with hmdef
  have hm : 0 < m := lt_of_lt_of_le hq (le_max_left _ _)
  set r₀ := localPropagationRadius Cgrad / (2 * Real.sqrt (2 * m)) with hr₀def
  have hr₀ : 0 < r₀ := div_pos (localPropagationRadius_pos Cgrad.coe_nonneg) (by positivity)
  have hr : 0 < r := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hyz)
  by_cases hyq : q ≤ A.flow.scalar T y
  · refine ⟨y, 0, fun _ => y, by rw [hmdef, max_eq_right hyq], ?_, rfl, rfl,
      fun k hk => absurd hk (Nat.not_lt_zero k), fun k hk => absurd hk (Nat.not_lt_zero k), ?_⟩
    · rw [riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr hr
    · push_cast
      linarith
  · push Not at hyq
    have hmq : m = q := max_eq_left hyq.le
    have hcont : Continuous (A.flow.scalar T) :=
      (metricScalar_smooth (A.flow.base.metric T)).continuous
    have hK : IsCompact {w | A.flow.scalar T w ≤ q} :=
      (isClosed_le hcont continuous_const).isCompact
    obtain ⟨x, gamma, hxq, hfin, hxz, hg0, hgl, -, -, hbelow, hiso⟩ :=
      Geometry.exists_minimizing_segment_to_level_of_isCompact_sublevel
        (A.flow.base.metric T) (A.flow.scalar T) hcont hK y z hyq (by rw [← hmq]; exact hz)
        (ne_top_of_lt hyz)
    set ℓ := (riemannianEDistOf (A.flow.base.metric T) y x).toReal with hℓdef
    have hℓ : 0 ≤ ℓ := ENNReal.toReal_nonneg
    set Nc := ⌈ℓ / (r₀ / 2)⌉₊ + 1 with hNcdef
    have hNc : (0 : ℝ) < Nc := by positivity
    let pc : ℕ → P.Carrier := fun k => gamma (min (k * ℓ / Nc) ℓ)
    have hmem (k : ℕ) : min (k * ℓ / Nc) ℓ ∈ Icc 0 ℓ :=
      ⟨le_min (by positivity) hℓ, min_le_right _ _⟩
    have hxz' : ℓ < r := by
      have h := hxz.trans_lt hyz
      exact (ENNReal.toReal_lt_toReal hfin ENNReal.ofReal_ne_top).mpr h |>.trans_le
        (le_of_eq (ENNReal.toReal_ofReal hr.le))
    refine ⟨x, Nc, pc, by rw [hxq, hmq], hxz.trans_lt hyz, ?_, ?_, fun k hk => ?_,
      fun k _ w hw => ?_, ?_⟩
    · change gamma (min ((0 : ℕ) * ℓ / Nc) ℓ) = y
      rw [Nat.cast_zero, zero_mul, zero_div, min_eq_left hℓ, hg0]
    · change gamma (min ((Nc : ℕ) * ℓ / Nc) ℓ) = x
      rw [mul_div_cancel_left₀ _ hNc.ne', min_self, hgl]
    · change riemannianEDistOf _ (gamma (min (k * ℓ / Nc) ℓ))
        (gamma (min (((k + 1 : ℕ) : ℝ) * ℓ / Nc) ℓ)) < _
      rw [hiso _ (hmem k) _ (hmem (k + 1))]
      have h1 : (k : ℝ) * ℓ / Nc ≤ ℓ := by
        rw [div_le_iff₀ hNc]
        have : (k : ℝ) ≤ Nc := by exact_mod_cast hk.le
        nlinarith
      have h2 : ((k + 1 : ℕ) : ℝ) * ℓ / Nc ≤ ℓ := by
        rw [div_le_iff₀ hNc]
        have : ((k + 1 : ℕ) : ℝ) ≤ Nc := by exact_mod_cast hk
        nlinarith
      rw [min_eq_left h1, min_eq_left h2]
      have heq : (k : ℝ) * ℓ / Nc - ((k + 1 : ℕ) : ℝ) * ℓ / Nc = -(ℓ / Nc) := by
        push_cast
        ring
      rw [heq, abs_neg, abs_of_nonneg (by positivity)]
      exact (ENNReal.ofReal_lt_ofReal_iff hr₀).mpr (div_ceil_lt_P6L hr₀)
    · have hpk : A.flow.scalar T (pc k) ≤ m := by
        rw [hmq]
        exact hbelow _ (hmem k)
      have hdk : riemannianEDistOf (A.flow.base.metric T) y (pc k) < ENNReal.ofReal r := by
        change riemannianEDistOf _ y (gamma (min (k * ℓ / Nc) ℓ)) < _
        rw [← hg0, hiso 0 ⟨le_rfl, hℓ⟩ _ (hmem k), zero_sub, abs_neg,
          abs_of_nonneg (hmem k).1]
        exact (ENNReal.ofReal_lt_ofReal_iff hr).mpr ((hmem k).2.trans_lt hxz')
      exact A.scalar_le_six_mul_on_ball_of_gradient_bound_static_P6L Cgrad hm
        (le_max_left _ _) U hgradient (pc k) (hU (pc k) hdk) hpk w hw
    · have h := ceil_mul_le_P6L hℓ hr₀
      rw [← hNcdef] at h
      linarith

/-- consumer：原 `Slice:246` 全局形由 `_P6L` 版（`U = univ`）推出。 -/
example {P : OrientedThreeStage.{u}}
    {a T : ℝ} (A : P.ClosedSlab a T) (Cgrad : ℝ≥0) {q : ℝ} (hq : 0 < q)
    (hgradient : ∀ y, ∀ t ∈ Ioo a T, q < A.flow.scalar t y →
      ∀ v : TangentSpace ThreeModel y,
        |scalarDifferential (A.restrictIncoming le_rfl A.lt le_rfl).flow t y v| ≤
          Cgrad * A.flow.scalar t y * Real.sqrt (A.flow.scalar t y) *
            Real.sqrt ((A.flow.base.metric t).inner y v v))
    (y z : P.Carrier) {r : ℝ}
    (hyz : riemannianEDistOf (A.flow.base.metric T) y z < ENNReal.ofReal r)
    (hz : max q (A.flow.scalar T y) ≤ A.flow.scalar T z) :
    ∃ (x : P.Carrier) (Nc : ℕ) (pc : ℕ → P.Carrier),
      A.flow.scalar T x = max q (A.flow.scalar T y) ∧
      riemannianEDistOf (A.flow.base.metric T) y x < ENNReal.ofReal r ∧
      pc 0 = y ∧ pc Nc = x ∧
      (∀ k < Nc, pc (k + 1) ∈ riemannianBallOf (A.flow.base.metric T) (pc k)
        (localPropagationRadius Cgrad / (2 * Real.sqrt (2 * max q (A.flow.scalar T y))))) ∧
      (∀ k < Nc, ∀ w ∈ riemannianBallOf (A.flow.base.metric T) (pc k)
        (localPropagationRadius Cgrad / (2 * Real.sqrt (2 * max q (A.flow.scalar T y)))),
        A.flow.scalar T w ≤ 6 * max q (A.flow.scalar T y)) ∧
      (Nc : ℝ) *
          (localPropagationRadius Cgrad / (2 * Real.sqrt (2 * max q (A.flow.scalar T y)))) ≤
        2 * r + 2 * (localPropagationRadius Cgrad /
          (2 * Real.sqrt (2 * max q (A.flow.scalar T y)))) :=
  A.exists_rebase_chain_P6L Cgrad hq univ (fun y _ => hgradient y) y z hyz hz
    (fun _ _ => subset_univ _)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
