import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4Staged
import DifferentialGeometry.Geometry.Metric.Approximation.EdgeBorderAdapters

/-!
# Register V4: LFR29.1's `W(Δ, τ)`, its numeric conditions at every register, and LFR32's
geometric output on the final family (lane FC39-V4C(b); review 57, §6.1, dispositions item 6)

**The numeric function** (BP-A LFR29.1, A:27523–27530; B:10168):
`W(Δ, τ) = min {τΔ/10⁹, (10⁶Δ)⁻¹, 10⁻⁴}` (`lfr29WV4C`), and the whole group of conditions
`Lfr29NumericV4C Δ τ b' s' s Λ b`:
`0 < b', s' < W`; `0 < s < 10⁻⁵ min {b', s'}`; `0 < Λ < min {(10⁶Δ)⁻¹, s'/(10⁸Δ²)}`;
`0 < b < 10⁻⁵ min {s, b', s'}`.

**The register.** `b', s'` sit below the slot `lfr29W` (and `10⁻⁸`), `s < 10⁻⁵ min {b', s'}` is a
display, `100ΔΛ < 10⁻⁸` and `Λ < s'/(10⁸Δ²)` are displays (RegScale, `lfr29_Λ`), `b` sits below the
slot `splitUp`. The cap `ClosedThresholdsV4.withLfr29_V4C U` puts `W(Δ, τ)` into `lfr29W` and
`s/10⁵` into `splitUp`; at EVERY register of a strategy below the cap the four lines hold
(`ClosedRegisterV4.lfr29_numeric_of_below_V4C`). The slot `lfr29W` stays (it may carry further
requests); it is now bounded by the native `W`.

**The geometric output** (LFR30–LFR32, A:27579–27768): the numeric conditions are used on the ACTUAL
strong edge maps. `Lfr32OutV4C hC ρ hρ F G Δ τ b' s'` is the full conclusion of LFR32 in physical
units
(`coarse_border_of_physical_lipschitz_scale`) for the actual composite `Q_p = (u, G v) =
F.stripMap G`: the closed set `A = closure E'` of the weak edge points (each at its own scale
`d/ρ(x)`, qualities `b', s'`) is closed and contains `p`, `Q_p(p) = 0`, `Q_p₂ ≥ 0`, distortion
`≤ τΔ` on `B_{d_p}(p, 200Δ)`, actual coverage of `[-100Δ, 100Δ] × [0, 100Δ]` within `τΔ`,
`b_p(a) ≤ τΔ` on `A ∩ B(p, 190Δ)` (LFR32.1), and every `(t, 0)` with `|t| ≤ 100Δ` has a witness in
the ACTUAL `E' ∩ B(p, 190Δ)` of image error `< τΔ`.

* `ClosedRegisterV4.lfr32_of_below_V4C`: at every register below the cap, for EVERY Λ-Lipschitz
  scale and every actual pair of strong maps `F` (quality `b`), `G` (quality `s`, `C ≥ 200Δ`) at
  the register's values, `Lfr32OutV4C` holds;
* `ClosedFamilyInstanceV4.lfr32_V4C` (and the C14D version): on every instance of the final family
  at such a register, at every edge centre `j`, the family's own strong maps (`edge.strong j`,
  `C > 200Δ`) exist and EVERY such pair satisfies `Lfr32OutV4C` with the family's `ρ`.
* Consumer `exists_closed_realization_lfr29_V4C`: the C14D realization of any strategy with the cap.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-! ### The numeric function and conditions -/

/-- LFR29.1's `W(Δ, τ) = min {τΔ/10⁹, (10⁶Δ)⁻¹, 10⁻⁴}` (A:27524). -/
def lfr29WV4C (Δ τ : ℝ) : ℝ :=
  min (min (τ * Δ / 10 ^ 9) (1 / (10 ^ 6 * Δ))) (1 / 10 ^ 4)

theorem lfr29WV4C_pos {Δ τ : ℝ} (hΔ : 0 < Δ) (hτ : 0 < τ) : 0 < lfr29WV4C Δ τ := by
  unfold lfr29WV4C
  exact lt_min (lt_min (by positivity) (by positivity)) (by norm_num)

/-- **LFR29.1** (A:27525–27530), the whole group of numeric conditions. -/
def Lfr29NumericV4C (Δ τ b' s' s Λ b : ℝ) : Prop :=
  (0 < b' ∧ b' < lfr29WV4C Δ τ ∧ 0 < s' ∧ s' < lfr29WV4C Δ τ) ∧
    (0 < s ∧ s < 1 / 10 ^ 5 * min b' s') ∧
    (0 < Λ ∧ Λ < min (1 / (10 ^ 6 * Δ)) (s' / (10 ^ 8 * Δ ^ 2))) ∧
    (0 < b ∧ b < 1 / 10 ^ 5 * min s (min b' s'))

/-! ### The cap and the conditions at every register -/

/-- **LFR29.1 as a strategy cap**: `lfr29W ≤ W(Δ, τ)` (read at `Δ, τ`, before `b', s'`) and
`splitUp ≤ s/10⁵` (read at `s`, before `b`). -/
def ClosedThresholdsV4.withLfr29_V4C {D : ClosedEarlyData} (U : ClosedThresholdsV4 D) :
    ClosedThresholdsV4 D :=
  { U with
    lfr29W := fun st ci ex co bd => min (U.lfr29W st ci ex co bd) (posOr_VAL3 (lfr29WV4C ex.Δ bd.τ))
    lfr29W_pos := fun st ci ex co bd => lt_min (U.lfr29W_pos st ci ex co bd) (posOr_pos_VAL3 _)
    splitUp := fun st ci ex er sc => min (U.splitUp st ci ex er sc) (posOr_VAL3 (er.s / 10 ^ 5))
    splitUp_pos := fun st ci ex er sc => lt_min (U.splitUp_pos st ci ex er sc) (posOr_pos_VAL3 _) }

/-- The LFR29.1 cap only lowers two upper slots. -/
theorem ClosedThresholdsV4.withLfr29_below_V4C {D : ClosedEarlyData} (U : ClosedThresholdsV4 D) :
    ClosedStrategyBelowV4 U.withLfr29_V4C U where
  lc18_le := le_rfl
  circleUp_le := fun _ _ _ _ _ => le_rfl
  β₂Up_le := fun _ _ _ => le_rfl
  ΔLow_ge := fun _ _ _ _ => le_rfl
  errorsUp_le := fun _ _ _ => le_rfl
  sectionUp_le := fun _ _ _ _ => le_rfl
  lfr29W_le := fun _ _ _ _ _ => min_le_left _ _
  endpointUp_le := fun _ _ _ _ _ _ => le_rfl
  σcolUp_le := fun _ _ _ _ _ _ _ => le_rfl
  scaleUp_le := fun _ _ _ _ => le_rfl
  wUp_le := fun _ _ _ _ _ => le_rfl
  splitUp_le := fun _ _ _ _ _ => min_le_left _ _
  β₁Up_le := fun _ _ _ _ _ _ => le_rfl
  T₀Low_ge := fun _ _ _ _ _ _ _ => le_rfl
  LmaxLow_ge := fun _ _ _ _ _ _ => le_rfl
  tailLow_ge := fun _ _ _ _ _ _ _ => le_rfl

/-- **LFR29.1 at every register of a strategy below the cap**, at the register's
`Δ, τ, b', s', s, Λ, b`. -/
theorem ClosedRegisterV4.lfr29_numeric_of_below_V4C {D : ClosedEarlyData}
    {T U : ClosedThresholdsV4 D} (h : ClosedStrategyBelowV4 T U.withLfr29_V4C)
    (R : ClosedRegisterV4 D T) :
    Lfr29NumericV4C R.later.excl.Δ R.later.err.bd.τ R.later.err.wk.b' R.later.err.wk.s'
      R.later.err.s R.later.scale.Λ R.later.split.b := by
  have hΔ := R.later.Δ_pos_VAL6
  have hτ := R.later.τ_pos
  have hs := R.later.s_pos
  have hb' := R.later.b'_pos
  have hs' := R.later.s'_pos
  have hΛ := R.later.Λ_pos
  have hW : T.lfr29W R.stage R.later.circle R.later.excl R.later.err.co R.later.err.bd ≤
      lfr29WV4C R.later.excl.Δ R.later.err.bd.τ := by
    refine (h.lfr29W_le _ _ _ _ _).trans ?_
    change min _ (posOr_VAL3 (lfr29WV4C R.later.excl.Δ R.later.err.bd.τ)) ≤ _
    rw [posOr_eq_VAL3 (lfr29WV4C_pos hΔ hτ)]
    exact min_le_right _ _
  have hsl : R.later.err.s < 1 / 10 ^ 5 * min R.later.err.wk.b' R.later.err.wk.s' :=
    R.later.s_lt.trans_le (min_le_left _ _)
  have hsplit : T.splitUp R.stage R.later.circle R.later.excl R.later.err R.later.scale ≤
      R.later.err.s / 10 ^ 5 := by
    refine (h.splitUp_le _ _ _ _ _).trans ?_
    change min _ (posOr_VAL3 (R.later.err.s / 10 ^ 5)) ≤ _
    rw [posOr_eq_VAL3 (by positivity)]
    exact min_le_right _ _
  have hmin : min R.later.err.s (min R.later.err.wk.b' R.later.err.wk.s') = R.later.err.s := by
    apply min_eq_left
    have := lt_min hb' hs'
    nlinarith
  have h100 := R.later.regScale_100
  refine ⟨⟨hb', (R.later.b'_lt.trans_le (min_le_left _ _)).trans_le hW, hs',
    (R.later.s'_lt.trans_le (min_le_left _ _)).trans_le hW⟩, ⟨hs, hsl⟩,
    ⟨hΛ, lt_min ?_ R.later.lfr29_Λ⟩, ⟨R.later.b_pos, ?_⟩⟩
  · rw [lt_div_iff₀ (by positivity)]
    nlinarith
  · rw [hmin]
    have := (R.later.b_lt.trans_le (min_le_left _ _)).trans_le hsplit
    linarith

/-! ### LFR32's output for the actual composite -/

section Out

variable {X : Type} [mX : MetricSpace X] {Y : Type} [MetricSpace Y]

/-- **LFR32's conclusion** (A:27695–27716) in physical units, for the actual composite
`Q_p = F.stripMap G = (u, G v)` of a strong point `p` (maps in `d_p = d/ρ(p)`) and the closure of
the weak edge set `E'` (each point at its own scale `d/ρ(x)`, qualities `b', s'`). -/
def Lfr32OutV4C {p : X} {q : Y} {C b s : ℝ} (hC : 0 ≤ C) (ρ : X → ℝ) (hρpos : ∀ x, 0 < ρ x)
    (F : @KleinerLottApprox X (WithLp 2 (ℝ × Y)) (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) _
      p (WithLp.toLp 2 ((0 : ℝ), q)) b)
    (G : KleinerLottApprox q (⟨0, le_rfl, hC⟩ : Icc (0 : ℝ) C) s) (Δ τ b' s' : ℝ) : Prop :=
  let E : Set X := {x | @isEdgePoint.{0, 0} X
    (mX.rescale (ρ x)⁻¹ (inv_pos.mpr (hρpos x))) x Δ b' s'}
  letI := mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
  IsClosed (closure E) ∧ p ∈ closure E ∧ F.stripMap G p = 0 ∧
    (∀ x, 0 ≤ (F.stripMap G x).snd) ∧
    (∀ x ∈ ball p (200 * Δ), ∀ y ∈ ball p (200 * Δ),
      |dist (F.stripMap G x) (F.stripMap G y) - dist x y| ≤ τ * Δ) ∧
    (∀ y : WithLp 2 (ℝ × ℝ), |y.fst| ≤ 100 * Δ → y.snd ∈ Icc 0 (100 * Δ) →
      ∃ x ∈ ball p (200 * Δ), dist (F.stripMap G x) y < τ * Δ) ∧
    (∀ a ∈ closure E ∩ ball p (190 * Δ), (F.stripMap G a).snd ≤ τ * Δ) ∧
    ∀ t : ℝ, |t| ≤ 100 * Δ → ∃ a ∈ E ∩ ball p (190 * Δ),
      dist (F.stripMap G a) (WithLp.toLp 2 (t, (0 : ℝ))) < τ * Δ

/-- **LFR32 from LFR29.1** (kernel binding): the numeric conditions, `Δ ≥ 1`, `0 < τ < 10⁻⁴` and
`C ≥ 200Δ` give `Lfr32OutV4C` for every `Λ`-Lipschitz scale and every actual strong pair. -/
theorem lfr32Out_of_numeric_V4C {p : X} {q : Y} {C : ℝ} {hC : 0 ≤ C}
    {Δ τ b' s' s Λ b : ℝ} (hnum : Lfr29NumericV4C Δ τ b' s' s Λ b) (hΔ : 1 ≤ Δ) (hτ : 0 < τ)
    (hτs : τ < 1 / 10 ^ 4) {ρ : X → ℝ} (hρ : LipschitzWith (Real.toNNReal Λ) ρ)
    (hρpos : ∀ x, 0 < ρ x)
    (F : @KleinerLottApprox X (WithLp 2 (ℝ × Y)) (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) _
      p (WithLp.toLp 2 ((0 : ℝ), q)) b)
    (G : KleinerLottApprox q (⟨0, le_rfl, hC⟩ : Icc (0 : ℝ) C) s) (hlength : 200 * Δ ≤ C) :
    Lfr32OutV4C hC ρ hρpos F G Δ τ b' s' := by
  obtain ⟨⟨hb', hb'W, hs', hs'W⟩, ⟨hs, hsl⟩, ⟨hΛ, hΛl⟩, ⟨hb, hbl⟩⟩ := hnum
  have hΔ0 : 0 < Δ := by linarith
  have hΛc : ((Real.toNNReal Λ : NNReal) : ℝ) = Λ := Real.coe_toNNReal _ hΛ.le
  unfold lfr29WV4C at hb'W hs'W
  simp only [lt_min_iff] at hb'W hs'W hΛl
  have hmin : min s (min b' s') = s := by
    apply min_eq_left
    have := lt_min hb' hs'
    nlinarith
  rw [hmin] at hbl
  have hbs : b < s / 100000 := by linarith
  have hsb' : s < b' / 100000 := by
    have := min_le_left b' s'
    nlinarith
  have hss' : s < s' / 100000 := by
    have := min_le_right b' s'
    nlinarith
  have h1 : (1 : ℝ) / (1000000 * Δ) = 1 / (10 ^ 6 * Δ) := by norm_num
  have h2 : s' / (100000000 * Δ ^ 2) = s' / (10 ^ 8 * Δ ^ 2) := by norm_num
  have h3 : τ * Δ / 1000000000 = τ * Δ / 10 ^ 9 := by norm_num
  exact coarse_border_of_physical_lipschitz_scale (hC := hC) hρ hρpos F G hΔ hτ
    (by norm_num at hτs ⊢; linarith) (by rw [hΛc, h1]; exact hΛl.1) (by rw [hΛc, h2]; exact hΛl.2)
    (by rw [h1]; exact hb'W.1.2) (by rw [h1]; exact hs'W.1.2) (by rw [h3]; exact hb'W.1.1)
    (by rw [h3]; exact hs'W.1.1) hsb' hss' hbs hlength

end Out

/-- **LFR32 at every register below the cap**: for EVERY scale that is `Λ`-Lipschitz for the
register's `Λ` and every actual strong pair at the register's qualities `b, s` with `C ≥ 200Δ`, the
actual composite and the weak set at the register's `b', s'` satisfy LFR32 with the register's
`Δ, τ`. -/
theorem ClosedRegisterV4.lfr32_of_below_V4C {D : ClosedEarlyData} {T U : ClosedThresholdsV4 D}
    (h : ClosedStrategyBelowV4 T U.withLfr29_V4C) (R : ClosedRegisterV4 D T) {X : Type}
    [mX : MetricSpace X] {Y : Type} [MetricSpace Y] {p : X} {q : Y} {C : ℝ} {hC : 0 ≤ C}
    {ρ : X → ℝ} (hρ : LipschitzWith (Real.toNNReal R.later.scale.Λ) ρ) (hρpos : ∀ x, 0 < ρ x)
    (F : @KleinerLottApprox X (WithLp 2 (ℝ × Y)) (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) _
      p (WithLp.toLp 2 ((0 : ℝ), q)) R.later.split.b)
    (G : KleinerLottApprox q (⟨0, le_rfl, hC⟩ : Icc (0 : ℝ) C) R.later.err.s)
    (hlength : 200 * R.later.excl.Δ ≤ C) :
    Lfr32OutV4C hC ρ hρpos F G R.later.excl.Δ R.later.err.bd.τ R.later.err.wk.b'
      R.later.err.wk.s' :=
  lfr32Out_of_numeric_V4C (R.lfr29_numeric_of_below_V4C h)
    (by have := R.later.Δ_gt; have := le_max_left (10 ^ 6 : ℝ)
          (max (100 / R.later.excl.β₂) (T.ΔLow R.stage R.later.circle R.later.excl.β₃
            R.later.excl.β₂)); norm_num at *; linarith)
    R.later.τ_pos (R.later.τ_lt.trans_le (min_le_left _ _) |>.trans (by norm_num)) hρ hρpos F G
    hlength

/-- **LFR32 on every instance of the final family** at a register below the cap: at every edge
centre `j` the family's own strong maps exist (`edge.strong j`: target `ℝ × Y`, endpoint length
`C > 200Δ`, qualities `b, s`), and EVERY such actual pair satisfies `Lfr32OutV4C` with the family's
scale `ρ` and the register's `Δ, τ, b', s'`. -/
theorem ClosedFamilyInstanceV4.lfr32_V4C {K : ℕ} {D : ClosedEarlyData}
    {T U : ClosedThresholdsV4 D} (h : ClosedStrategyBelowV4 T U.withLfr29_V4C)
    {R : ClosedRegisterV4 D T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (F : ClosedFamilyInstanceV4 K R M δ εr Λz) (j : M.X) (hj : j ∈ F.family.edge.centres) :
    ∃ (Y : Type) (mY : MetricSpace Y) (q : Y) (C : ℝ) (hC : 0 ≤ C),
      200 * R.later.excl.Δ < C ∧
      Nonempty (@KleinerLottApprox M.X (WithLp 2 (ℝ × Y))
        (M.mX.rescale (F.ρ j)⁻¹ (inv_pos.mpr (F.ρ_pos j))) _ j (WithLp.toLp 2 ((0 : ℝ), q))
        R.later.split.b) ∧
      Nonempty (@KleinerLottApprox Y (Icc (0 : ℝ) C) mY _ q ⟨0, le_rfl, hC⟩ R.later.err.s) ∧
      ∀ (Fj : @KleinerLottApprox M.X (WithLp 2 (ℝ × Y))
          (M.mX.rescale (F.ρ j)⁻¹ (inv_pos.mpr (F.ρ_pos j))) _ j (WithLp.toLp 2 ((0 : ℝ), q))
          R.later.split.b)
        (Gj : @KleinerLottApprox Y (Icc (0 : ℝ) C) mY _ q ⟨0, le_rfl, hC⟩ R.later.err.s),
        Lfr32OutV4C hC F.ρ F.ρ_pos Fj Gj R.later.excl.Δ R.later.err.bd.τ R.later.err.wk.b'
          R.later.err.wk.s' := by
  obtain ⟨Y, mY, q, C, hC, hCl, hF, hG⟩ := F.family.edge.strong j hj
  exact ⟨Y, mY, q, C, hC, hCl, hF, hG, fun Fj Gj =>
    R.lfr32_of_below_V4C h F.family.lipschitz_scale F.ρ_pos Fj Gj hCl.le⟩

/-- The same on every C14D instance. -/
theorem ClosedFamilyInstanceC14DV4.lfr32_V4C {K : ℕ} {D : ClosedEarlyData}
    {T U : ClosedThresholdsV4 D} (h : ClosedStrategyBelowV4 T U.withLfr29_V4C)
    {R : ClosedRegisterV4 D T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (F : ClosedFamilyInstanceC14DV4 K R M δ εr Λz) (j : M.X) (hj : j ∈ F.family.edge.centres) :
    ∃ (Y : Type) (mY : MetricSpace Y) (q : Y) (C : ℝ) (hC : 0 ≤ C),
      200 * R.later.excl.Δ < C ∧
      Nonempty (@KleinerLottApprox M.X (WithLp 2 (ℝ × Y))
        (M.mX.rescale (F.ρ j)⁻¹ (inv_pos.mpr (F.ρ_pos j))) _ j (WithLp.toLp 2 ((0 : ℝ), q))
        R.later.split.b) ∧
      Nonempty (@KleinerLottApprox Y (Icc (0 : ℝ) C) mY _ q ⟨0, le_rfl, hC⟩ R.later.err.s) ∧
      ∀ (Fj : @KleinerLottApprox M.X (WithLp 2 (ℝ × Y))
          (M.mX.rescale (F.ρ j)⁻¹ (inv_pos.mpr (F.ρ_pos j))) _ j (WithLp.toLp 2 ((0 : ℝ), q))
          R.later.split.b)
        (Gj : @KleinerLottApprox Y (Icc (0 : ℝ) C) mY _ q ⟨0, le_rfl, hC⟩ R.later.err.s),
        Lfr32OutV4C hC F.ρ F.ρ_pos Fj Gj R.later.excl.Δ R.later.err.bd.τ R.later.err.wk.b'
          R.later.err.wk.s' :=
  F.toC14_VAL6.lfr32_V4C h j hj

/-- **Consumer: LFR29.1 and LFR32 realized.** For every threshold strategy `U`, the complete C14D
realization of `U` with the LFR29.1 cap gives a common strategy `T` at which every register meets
LFR29.1 at its own values, and on every member of the tail the final family's edge centres carry
LFR32's output for their actual strong maps. -/
theorem exists_closed_realization_lfr29_V4C (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2)))
    {D : ClosedEarlyData} (U : ClosedThresholdsV4 D) :
    ∃ T : ClosedThresholdsV4 D, ClosedStrategyRefinesV4 T U.withLfr29_V4C ∧
      ClosedStrategyBelowV4 T U ∧ ClosedFamilyAtC14DV4 K Wseq gseq T ∧
      ∀ R : ClosedRegisterV4 D T,
        Lfr29NumericV4C R.later.excl.Δ R.later.err.bd.τ R.later.err.wk.b' R.later.err.wk.s'
          R.later.err.s R.later.scale.Λ R.later.split.b ∧
        ∃ εr δ' Λz : ℝ, ∃ δ : ℝ, δ < δ' ∧ ∀ m, R.later.tail ≤ m →
          ∃ M : ClosedModel (Wseq m) (gseq m), ∃ F : ClosedFamilyInstanceC14DV4 K R M δ εr Λz,
            ∀ j ∈ F.family.edge.centres,
              ∃ (Y : Type) (mY : MetricSpace Y) (q : Y) (C : ℝ) (hC : 0 ≤ C),
                200 * R.later.excl.Δ < C ∧
                ∃ (Fj : @KleinerLottApprox M.X (WithLp 2 (ℝ × Y))
                    (M.mX.rescale (F.ρ j)⁻¹ (inv_pos.mpr (F.ρ_pos j))) _ j
                    (WithLp.toLp 2 ((0 : ℝ), q)) R.later.split.b)
                  (Gj : @KleinerLottApprox Y (Icc (0 : ℝ) C) mY _ q ⟨0, le_rfl, hC⟩
                    R.later.err.s),
                  Lfr32OutV4C hC F.ρ F.ρ_pos Fj Gj R.later.excl.Δ R.later.err.bd.τ
                    R.later.err.wk.b' R.later.err.wk.s' := by
  obtain ⟨T, hTU, -, -, hfam⟩ :=
    exists_closed_realization_C14D_VAL6 K hK A hA Wseq gseq hf hg U.withLfr29_V4C
  have hb : ClosedStrategyBelowV4 T U.withLfr29_V4C := hTU.below_VAL6
  refine ⟨T, hTU, hb.trans_VAL6 U.withLfr29_below_V4C, hfam,
    fun R => ⟨R.lfr29_numeric_of_below_V4C hb, ?_⟩⟩
  obtain ⟨εrF, δ'F, ΛzF, hF⟩ := hfam
  obtain ⟨-, -, -, -, -, -, δc, -, hδc, ht⟩ := hF R
  refine ⟨εrF R.stage R.later.circle R.later.excl R.later.err R.later.scale R.later.split.b
    R.later.split.β₁, δ'F R.stage R.later.circle R.later.excl R.later.err R.later.scale
    R.later.split.b R.later.split.β₁, ΛzF R.stage R.later.circle R.later.excl R.later.err
    R.later.scale R.later.split.b R.later.split.β₁, δc, hδc, fun m hm => ?_⟩
  obtain ⟨M, ⟨F⟩, -, -⟩ := ht m hm
  refine ⟨M, F, fun j hj => ?_⟩
  obtain ⟨Y, mY, q, C, hC, hCl, ⟨Fj⟩, ⟨Gj⟩, hout⟩ := F.lfr32_V4C hb j hj
  exact ⟨Y, mY, q, C, hC, hCl, Fj, Gj, hout Fj Gj⟩

end DifferentialGeometry.Geometry.Collapse
