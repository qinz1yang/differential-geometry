import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BoundedCurvatureAtDistanceSliceRebase_P6L
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BoundedCurvatureAtDistanceChainBuffersWindow_P6WB

/-!
# P6WIN-B G2：`Slice:246`（rebase chain）的时间窗形（`_P6WB`）

P6CON G2b 窗口 spine 的 B 段补件：`SLT:45/249_P6L` 的 `hgrad` 只经 `exists_rebase_chain_P6L`（再经
`CB:84` 静态版、`TSB:27`）求值 ⇒ 要让 SLT 窗口版的 `hgrad` 也是窗口形，rebase chain 需窗口版：
`U` 后加 `(c : ℝ) (hc : c < T)`，`hgradient` 加 guard `c ≤ t →`，叶子换
`ClosedSlab.scalar_le_six_mul_on_ball_of_gradient_bound_static_window_P6WB`
（`ChainBuffersWindow_P6WB`）。
`hU`（生成形成员前提）与结论逐字；私有引理（`Slice:229,237`）复制为 `_P6WB`。
注：`c < T` 是唯一要求——`hgradient` 只在 `t → T⁻` 求值（`TSB:27` 的 `∀ᶠ t in 𝓝[<] T`），
所以窗口可取任意靠近 `T` 的 `c`。
consumer：`exists_rebase_chain_P6L`（全 slab 形）⇐ 窗口形取 `c = a`。
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

private theorem ceil_mul_le_P6WB {ℓ r₀ : ℝ} (hℓ : 0 ≤ ℓ) (hr₀ : 0 < r₀) :
    ((⌈ℓ / (r₀ / 2)⌉₊ + 1 : ℕ) : ℝ) * r₀ ≤ 2 * ℓ + 2 * r₀ := by
  have h1 : ((⌈ℓ / (r₀ / 2)⌉₊ : ℕ) : ℝ) < ℓ / (r₀ / 2) + 1 :=
    Nat.ceil_lt_add_one (div_nonneg hℓ (by positivity))
  have h2 : ℓ / (r₀ / 2) * r₀ = 2 * ℓ := by field_simp
  push_cast
  nlinarith

private theorem div_ceil_lt_P6WB {ℓ r₀ : ℝ} (hr₀ : 0 < r₀) :
    ℓ / ((⌈ℓ / (r₀ / 2)⌉₊ + 1 : ℕ) : ℝ) < r₀ := by
  have hN : (0 : ℝ) < ((⌈ℓ / (r₀ / 2)⌉₊ + 1 : ℕ) : ℝ) := by positivity
  rw [div_lt_iff₀ hN]
  have h1 : ℓ / (r₀ / 2) ≤ ((⌈ℓ / (r₀ / 2)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have h2 : ℓ = ℓ / (r₀ / 2) * (r₀ / 2) := by field_simp
  push_cast
  nlinarith

/-- **`_P6WB`（`Slice:246` rebase chain 窗口形）**：`hgradient` 只在窗口 `[c, T)` 内要（guard
`c ≤ t`，窗口起点 `c < T` 在 `U` 之后给出；只传给 `CB:84` 静态窗口形）。其余前提、结论、证明体逐字。 -/
theorem OrientedThreeStage.ClosedSlab.exists_rebase_chain_window_P6WB {P : OrientedThreeStage.{u}}
    {a T : ℝ} (A : P.ClosedSlab a T) (Cgrad : ℝ≥0) {q : ℝ} (hq : 0 < q)
    (U : Set P.Carrier) (c : ℝ) (hc : c < T)
    (hgradient : ∀ y ∈ U, ∀ t ∈ Ioo a T, c ≤ t → q < A.flow.scalar t y →
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
      exact (ENNReal.ofReal_lt_ofReal_iff hr₀).mpr (div_ceil_lt_P6WB hr₀)
    · have hpk : A.flow.scalar T (pc k) ≤ m := by
        rw [hmq]
        exact hbelow _ (hmem k)
      have hdk : riemannianEDistOf (A.flow.base.metric T) y (pc k) < ENNReal.ofReal r := by
        change riemannianEDistOf _ y (gamma (min (k * ℓ / Nc) ℓ)) < _
        rw [← hg0, hiso 0 ⟨le_rfl, hℓ⟩ _ (hmem k), zero_sub, abs_neg,
          abs_of_nonneg (hmem k).1]
        exact (ENNReal.ofReal_lt_ofReal_iff hr).mpr ((hmem k).2.trans_lt hxz')
      exact A.scalar_le_six_mul_on_ball_of_gradient_bound_static_window_P6WB Cgrad hm
        (le_max_left _ _) U c hc hgradient (pc k) (hU (pc k) hdk) hpk w hw
    · have h := ceil_mul_le_P6WB hℓ hr₀
      rw [← hNcdef] at h
      linarith

/-- consumer：`exists_rebase_chain_P6L`（全 slab `hgradient`）⇐ 窗口形（`c = a`）。 -/
example : type_of% @OrientedThreeStage.ClosedSlab.exists_rebase_chain_P6L.{0} := by
  intro P a T A Cgrad q hq U hgradient
  exact A.exists_rebase_chain_window_P6WB Cgrad hq U a A.lt
    (fun y hy t ht _ => hgradient y hy t ht)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
