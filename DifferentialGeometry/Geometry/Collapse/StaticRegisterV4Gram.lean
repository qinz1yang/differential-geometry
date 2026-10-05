import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4Staged

/-!
# Register V4: TCP01's Gram bound from the circle construction, and its downstream budgets
(lane FC39-V4C(b); review 57, §4.2, dispositions item 4)

Review 57 §4.2: `Tcp01GramOutV2` (`‖Dη w‖ ≤ 1 + γ` on normalized-unit `w`; every unit `ξ` has a unit
`w` with `⟨Dη w, ξ⟩ > 1 − (γ + β₂)`) does NOT give the displayed `‖Dη(Dη)^* − I‖ < γ/4` at the SAME
`γ` (counterexample `A = (1 − γ/2)π`). The circle construction of the tree (the packet's
`(1 + γ)`-Lipschitz bound and its long derivative tests, `tcp01_gram`, Fibration/ActualCircleGram)
records no sharper estimate than this two-sided singular-value bound; the Gram bound it gives is
`2(γ + β₂) + γ²`. This file exports that bound in Gram form and re-proves the downstream budgets.

**Gram form.** For a linear map `A` from the tangent space with its normalized metric `ρ(j)⁻² g` to
`ℝ²`, `⟨A A^* ξ, ξ⟩ = ‖A^* ξ‖² = (sup_{|w| = 1} ⟨A w, ξ⟩)²` (dual norm; the tangent space carries no
inner-product instance here, so the adjoint is expressed through this supremum). Hence
`Tcp01GramQuadOutV4C P κ` — at every circle centre `j`, every `x ∈ B(j, 200ρ(j))` and every unit
`ξ`: every normalized-unit `w` has `⟨Dη w, ξ⟩² ≤ 1 + κ`, and some normalized-unit `w` has
`0 < ⟨Dη w, ξ⟩` and `1 − κ ≤ ⟨Dη w, ξ⟩²` — says exactly that the symmetric matrix `Dη(Dη)^*` has its
quadratic form in `[1 − κ, 1 + κ]` on unit vectors, i.e. `‖Dη(Dη)^* − I‖ ≤ κ`.

* `gram_quad_of_singular_V4C` (kernel): `‖A w‖ ≤ 1 + γ` and the lower witnesses at `γ + β` with
  `β ≤ γ/2`, `γ ≤ 1/10` give the Gram form at `κ = 3γ`.
* `tcp01_gram_quad_V4C`: on every family with `β₂ ≤ γ/2`, `β₂ ≤ 10⁻⁷`, `γ ≤ 1/10`:
  `Tcp01GramQuadOutV4C P (3γ)`; so TCP01's display `‖Dη(Dη)^* − I‖ < γ_T/4` holds at
  `γ_T = 16γ` (`3γ < 16γ/4`), and since the register caps `γ` below any prescribed value (slot
  `circleUp`), every prescribed `γ_T` is met by `γ < γ_T/16` — a choice before `Δ`, as in TCP01.
* Downstream budgets (B:5637, B:6121): `Tcp01GramQuadOutV4C.singular_norm_V4C`: `κ ≤ 1/10` gives
  least singular value `> 9/10` (every unit `ξ` has a unit `w` with `⟨Dη w, ξ⟩ > 9/10`) and operator
  norm `< 2` (`‖Dη w‖ < 2` on unit `w`).
* Register: the cap `ClosedThresholdsV4.withGram_V4C` (`β₂Up ≤ min (γ/2) 10⁻⁷`, read at the circle
  prefix BEFORE `β_c`; `circleUp ≤ 1/100`); at every register below it, every family instance
  satisfies the Gram form at `3γ` and the two budgets; consumer
  `exists_closed_realization_gram_V4C`.
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
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-! ### The kernel -/

/-- **Gram form from the singular-value bounds** (kernel): if every `w ∈ S` has `‖A w‖ ≤ 1 + γ` and
every unit `ξ` has a `w ∈ S` with `⟨A w, ξ⟩ > 1 − (γ + β)`, where `0 ≤ β ≤ γ/2` and `γ ≤ 1/10`, then
for every unit `ξ` all `⟨A w, ξ⟩²` (`w ∈ S`) are at most `1 + 3γ` and some `w ∈ S` has
`0 < ⟨A w, ξ⟩` and `1 − 3γ ≤ ⟨A w, ξ⟩²`. -/
theorem gram_quad_of_singular_V4C {V : Type*} (S : Set V) (A : V → ℝ²) {γ β : ℝ}
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1 / 10) (hβ : 0 ≤ β) (hβγ : β ≤ γ / 2)
    (hup : ∀ w ∈ S, ‖A w‖ ≤ 1 + γ)
    (hlow : ∀ ξ : ℝ², ‖ξ‖ = 1 → ∃ w ∈ S, 1 - (γ + β) < inner ℝ (A w) ξ) :
    ∀ ξ : ℝ², ‖ξ‖ = 1 → (∀ w ∈ S, inner ℝ (A w) ξ ^ 2 ≤ 1 + 3 * γ) ∧
      ∃ w ∈ S, 0 < inner ℝ (A w) ξ ∧ 1 - 3 * γ ≤ inner ℝ (A w) ξ ^ 2 := by
  intro ξ hξ
  refine ⟨fun w hw => ?_, ?_⟩
  · have h1 : |inner ℝ (A w) ξ| ≤ 1 + γ := by
      have := abs_real_inner_le_norm (A w) ξ
      rw [hξ, mul_one] at this
      exact this.trans (hup w hw)
    have h2 : inner ℝ (A w) ξ ^ 2 ≤ (1 + γ) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    nlinarith
  · obtain ⟨w, hw, hlt⟩ := hlow ξ hξ
    have hpos : 0 < 1 - (γ + β) := by linarith
    refine ⟨w, hw, hpos.trans hlt, ?_⟩
    have h2 : (1 - (γ + β)) ^ 2 ≤ inner ℝ (A w) ξ ^ 2 :=
      pow_le_pow_left₀ hpos.le hlt.le 2
    nlinarith

/-! ### The native `Out` -/

section Out

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- **TCP01's Gram clause in Gram form at tolerance `κ`** (B:5265–5268): at every circle centre `j`,
every `x ∈ B(j, 200ρ(j))` and every unit `ξ ∈ ℝ²`, the quadratic form `⟨Dη(Dη)^* ξ, ξ⟩ =
(sup_{|w| = 1} ⟨Dη w, ξ⟩)²` of the normalized metric `ρ(j)⁻² g` lies in `[1 − κ, 1 + κ]`: every
normalized-unit `w` has `⟨Dη w, ξ⟩² ≤ 1 + κ` and some normalized-unit `w` has `0 < ⟨Dη w, ξ⟩`,
`1 − κ ≤ ⟨Dη w, ξ⟩²`. Equivalently `‖Dη(Dη)^* − I‖ ≤ κ`. -/
def Tcp01GramQuadOutV4C
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (κ : ℝ) : Prop :=
  ∀ j (hj : j ∈ P.circle.centres) x, x ∈ ball j (200 * ρ j) → ∀ ξ : ℝ², ‖ξ‖ = 1 →
    (∀ w : TangentSpace 𝓘(ℝ, E3) x, (ρ j)⁻¹ ^ 2 * g.inner x w w = 1 →
      inner ℝ (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x w) ξ ^ 2 ≤
        1 + κ) ∧
    ∃ w : TangentSpace 𝓘(ℝ, E3) x, (ρ j)⁻¹ ^ 2 * g.inner x w w = 1 ∧
      0 < inner ℝ (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x w) ξ ∧
      1 - κ ≤ inner ℝ (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x w) ξ ^ 2

/-- **TCP01's Gram bound from the circle construction**: with `β₂ ≤ γ/2`, `β₂ ≤ 10⁻⁷` and
`0 ≤ γ ≤ 1/10`, the family's circle coordinates satisfy the Gram form at `κ = 3γ` (from
`tcp01_gram`: Lipschitz bound and long derivative tests of the SAME packet). -/
theorem tcp01_gram_quad_V4C
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1 / 10) (hβ0 : 0 ≤ β 2) (hβγ : β 2 ≤ γ / 2)
    (hβ : β 2 ≤ 1 / 10000000) : Tcp01GramQuadOutV4C P (3 * γ) := by
  intro j hj x hx
  have h := tcp01_gram P hγ hβ hj hx
  exact gram_quad_of_singular_V4C {w | (ρ j)⁻¹ ^ 2 * g.inner x w w = 1}
    (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x) hγ hγ1 hβ0 hβγ h.1
    (fun ξ hξ => (h.2 ξ hξ).imp fun _ hw => ⟨hw.1, hw.2.2⟩)

/-- **TCP01's display at `γ_T = 16γ`**: `3γ < (16γ)/4` for `γ > 0`. -/
theorem tcp01_gram_display_V4C {γ' : ℝ} (hγ : 0 < γ') : 3 * γ' < 16 * γ' / 4 := by
  linarith

/-- **The downstream budgets** (B:5637, B:6121): a Gram form with `κ ≤ 1/10` gives least singular
value `> 9/10` (every unit `ξ` has a normalized-unit `w` with `⟨Dη w, ξ⟩ > 9/10`) and operator norm
`< 2` (`‖Dη w‖ < 2` for normalized-unit `w`). -/
theorem Tcp01GramQuadOutV4C.singular_norm_V4C
    {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V}
    {κ : ℝ} (hG : Tcp01GramQuadOutV4C P κ) (hκ : κ ≤ 1 / 10) {j : X} (hj : j ∈ P.circle.centres)
    {x : X} (hx : x ∈ ball j (200 * ρ j)) :
    (∀ ξ : ℝ², ‖ξ‖ = 1 → ∃ w : TangentSpace 𝓘(ℝ, E3) x, (ρ j)⁻¹ ^ 2 * g.inner x w w = 1 ∧
      9 / 10 < inner ℝ (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x w) ξ) ∧
    ∀ w : TangentSpace 𝓘(ℝ, E3) x, (ρ j)⁻¹ ^ 2 * g.inner x w w = 1 →
      ‖mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x w‖ < 2 := by
  refine ⟨fun ξ hξ => ?_, fun w hw => ?_⟩
  · obtain ⟨w, hw, hpos, hlow⟩ := (hG j hj x hx ξ hξ).2
    refine ⟨w, hw, ?_⟩
    nlinarith
  · set v := mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x w with hv
    rcases eq_or_ne v 0 with h0 | h0
    · rw [h0, norm_zero]
      norm_num
    · have hn : 0 < ‖v‖ := norm_pos_iff.mpr h0
      have hξ : ‖‖v‖⁻¹ • v‖ = 1 := by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
      have h := (hG j hj x hx (‖v‖⁻¹ • v) hξ).1 w hw
      rw [← hv, real_inner_smul_right, real_inner_self_eq_norm_sq] at h
      have he : ‖v‖⁻¹ * ‖v‖ ^ 2 = ‖v‖ := by
        field_simp
      rw [he] at h
      nlinarith

end Out

/-! ### The register -/

/-- **TCP01's Gram request as a strategy cap**: `β₂ ≤ min (γ/2) 10⁻⁷` (read at the circle prefix,
before `β_c`) and `γ ≤ 1/100` (through `circleUp`). -/
def ClosedThresholdsV4.withGram_V4C {D : ClosedEarlyData} (U : ClosedThresholdsV4 D) :
    ClosedThresholdsV4 D :=
  { U with
    circleUp := fun st β₃ θs θe θ₂ => min (U.circleUp st β₃ θs θe θ₂) (1 / 100)
    circleUp_pos := fun st β₃ θs θe θ₂ => lt_min (U.circleUp_pos st β₃ θs θe θ₂) (by norm_num)
    β₂Up := fun st cp β₃ => min (U.β₂Up st cp β₃) (min (posOr_VAL3 (cp.γ / 2)) (1 / 10 ^ 7))
    β₂Up_pos := fun st cp β₃ => lt_min (U.β₂Up_pos st cp β₃) (lt_min (posOr_pos_VAL3 _)
      (by norm_num)) }

/-- The Gram cap only lowers two upper slots. -/
theorem ClosedThresholdsV4.withGram_below_V4C {D : ClosedEarlyData} (U : ClosedThresholdsV4 D) :
    ClosedStrategyBelowV4 U.withGram_V4C U where
  lc18_le := le_rfl
  circleUp_le := fun _ _ _ _ _ => min_le_left _ _
  β₂Up_le := fun _ _ _ => min_le_left _ _
  ΔLow_ge := fun _ _ _ _ => le_rfl
  errorsUp_le := fun _ _ _ => le_rfl
  sectionUp_le := fun _ _ _ _ => le_rfl
  lfr29W_le := fun _ _ _ _ _ => le_rfl
  endpointUp_le := fun _ _ _ _ _ _ => le_rfl
  σcolUp_le := fun _ _ _ _ _ _ _ => le_rfl
  scaleUp_le := fun _ _ _ _ => le_rfl
  wUp_le := fun _ _ _ _ _ => le_rfl
  splitUp_le := fun _ _ _ _ _ => le_rfl
  β₁Up_le := fun _ _ _ _ _ _ => le_rfl
  T₀Low_ge := fun _ _ _ _ _ _ _ => le_rfl
  LmaxLow_ge := fun _ _ _ _ _ _ => le_rfl
  tailLow_ge := fun _ _ _ _ _ _ _ => le_rfl

/-- **The Gram request at every register below the cap**: `0 < γ < 1/100`, `β₂ ≤ γ/2`,
`β₂ ≤ 10⁻⁷`. -/
theorem ClosedRegisterV4.gram_request_of_below_V4C {D : ClosedEarlyData}
    {T U : ClosedThresholdsV4 D} (h : ClosedStrategyBelowV4 T U.withGram_V4C)
    (R : ClosedRegisterV4 D T) :
    0 < R.later.circle.γ ∧ R.later.circle.γ < 1 / 100 ∧ R.β 2 ≤ R.later.circle.γ / 2 ∧
      R.β 2 ≤ 1 / 10 ^ 7 := by
  have hγ := R.later.γ_pos
  have hγu : R.later.circle.γ < 1 / 100 := by
    have h1 := (R.later.γ_lt.trans_le (min_le_right _ _)).trans_le (h.circleUp_le _ _ _ _ _)
    exact h1.trans_le (min_le_right _ _)
  have h2 := (R.later.β₂_lt.trans_le (min_le_left _ _)).trans_le (h.β₂Up_le _ _ _)
  have h3 : U.withGram_V4C.β₂Up R.stage R.later.circle.toPrefixV4 R.later.excl.β₃ ≤
      min (R.later.circle.γ / 2) (1 / 10 ^ 7) := by
    change min _ (min (posOr_VAL3 (R.later.circle.γ / 2)) (1 / 10 ^ 7)) ≤ _
    rw [posOr_eq_VAL3 (by positivity)]
    exact min_le_right _ _
  have h4 := h2.trans_le h3
  rw [R.β_two_VAL6]
  exact ⟨hγ, hγu, (h4.trans_le (min_le_left _ _)).le, (h4.trans_le (min_le_right _ _)).le⟩

/-- **TCP01's Gram bound and its budgets on every C14 instance** at a register below the cap: the
Gram form at `3γ` (so `‖Dη(Dη)^* − I‖ < (16γ)/4`), least singular value `> 9/10` and operator norm
`< 2` at every circle centre and every point of `B(j, 200ρ(j))`. -/
theorem ClosedFamilyInstanceV4.gram_V4C {K : ℕ} {D : ClosedEarlyData}
    {T U : ClosedThresholdsV4 D} (h : ClosedStrategyBelowV4 T U.withGram_V4C)
    {R : ClosedRegisterV4 D T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (F : ClosedFamilyInstanceV4 K R M δ εr Λz) :
    Tcp01GramQuadOutV4C F.family.toLocalChartPackets (3 * R.later.circle.γ) ∧
      3 * R.later.circle.γ < 16 * R.later.circle.γ / 4 ∧
      ∀ j (hj : j ∈ F.family.circle.centres) x, x ∈ ball j (200 * F.ρ j) →
        (∀ ξ : ℝ², ‖ξ‖ = 1 → ∃ w : TangentSpace 𝓘(ℝ, E3) x,
          (F.ρ j)⁻¹ ^ 2 * M.gX.inner x w w = 1 ∧ 9 / 10 < inner ℝ (mvfderiv 𝓘(ℝ, E3)
            (cgpCircleCoord F.family.toLocalChartFamily j hj) x w) ξ) ∧
        ∀ w : TangentSpace 𝓘(ℝ, E3) x, (F.ρ j)⁻¹ ^ 2 * M.gX.inner x w w = 1 →
          ‖mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord F.family.toLocalChartFamily j hj) x w‖ < 2 := by
  obtain ⟨hγ, hγu, hβγ, hβ⟩ := R.gram_request_of_below_V4C h
  have hβ0 : 0 ≤ R.β 2 := by
    rw [R.β_two_VAL6]
    exact R.later.β₂_pos.le
  have hG := tcp01_gram_quad_V4C F.family.toLocalChartPackets hγ.le (by linarith) hβ0 hβγ
    (by norm_num at hβ ⊢; linarith)
  exact ⟨hG, tcp01_gram_display_V4C hγ, fun j hj x hx =>
    hG.singular_norm_V4C (by linarith) hj hx⟩

/-- The same on every C14D instance. -/
theorem ClosedFamilyInstanceC14DV4.gram_V4C {K : ℕ} {D : ClosedEarlyData}
    {T U : ClosedThresholdsV4 D} (h : ClosedStrategyBelowV4 T U.withGram_V4C)
    {R : ClosedRegisterV4 D T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (F : ClosedFamilyInstanceC14DV4 K R M δ εr Λz) :
    Tcp01GramQuadOutV4C F.family.toLocalChartPackets (3 * R.later.circle.γ) ∧
      3 * R.later.circle.γ < 16 * R.later.circle.γ / 4 ∧
      ∀ j (hj : j ∈ F.family.circle.centres) x, x ∈ ball j (200 * F.ρ j) →
        (∀ ξ : ℝ², ‖ξ‖ = 1 → ∃ w : TangentSpace 𝓘(ℝ, E3) x,
          (F.ρ j)⁻¹ ^ 2 * M.gX.inner x w w = 1 ∧ 9 / 10 < inner ℝ (mvfderiv 𝓘(ℝ, E3)
            (cgpCircleCoord F.family.toLocalChartFamily j hj) x w) ξ) ∧
        ∀ w : TangentSpace 𝓘(ℝ, E3) x, (F.ρ j)⁻¹ ^ 2 * M.gX.inner x w w = 1 →
          ‖mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord F.family.toLocalChartFamily j hj) x w‖ < 2 :=
  F.toC14_VAL6.gram_V4C h

/-- **Consumer: TCP01's Gram bound realized.** For every threshold strategy `U`, the complete C14D
realization of `U` with the Gram cap gives a common strategy `T` such that at every register, on
every member of the tail, the final family's circle coordinates satisfy the Gram form at `3γ` and
the two downstream budgets. -/
theorem exists_closed_realization_gram_V4C (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2)))
    {D : ClosedEarlyData} (U : ClosedThresholdsV4 D) :
    ∃ T : ClosedThresholdsV4 D, ClosedStrategyRefinesV4 T U.withGram_V4C ∧
      ClosedStrategyBelowV4 T U ∧ ClosedFamilyAtC14DV4 K Wseq gseq T ∧
      ∀ R : ClosedRegisterV4 D T, ∃ εr δ' Λz : ℝ, ∃ δ : ℝ, δ < δ' ∧ ∀ m, R.later.tail ≤ m →
        ∃ M : ClosedModel (Wseq m) (gseq m), ∃ F : ClosedFamilyInstanceC14DV4 K R M δ εr Λz,
          Tcp01GramQuadOutV4C F.family.toLocalChartPackets (3 * R.later.circle.γ) := by
  obtain ⟨T, hTU, -, -, hfam⟩ :=
    exists_closed_realization_C14D_VAL6 K hK A hA Wseq gseq hf hg U.withGram_V4C
  have hb : ClosedStrategyBelowV4 T U.withGram_V4C := hTU.below_VAL6
  refine ⟨T, hTU, hb.trans_VAL6 U.withGram_below_V4C, hfam, fun R => ?_⟩
  obtain ⟨εrF, δ'F, ΛzF, hF⟩ := hfam
  obtain ⟨-, -, -, -, -, -, δc, -, hδc, ht⟩ := hF R
  refine ⟨εrF R.stage R.later.circle R.later.excl R.later.err R.later.scale R.later.split.b
    R.later.split.β₁, δ'F R.stage R.later.circle R.later.excl R.later.err R.later.scale
    R.later.split.b R.later.split.β₁, ΛzF R.stage R.later.circle R.later.excl R.later.err
    R.later.scale R.later.split.b R.later.split.β₁, δc, hδc, fun m hm => ?_⟩
  obtain ⟨M, ⟨F⟩, -, -⟩ := ht m hm
  exact ⟨M, F, (F.gram_V4C hb).1⟩

end DifferentialGeometry.Geometry.Collapse
