import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4Lfr29

/-!
# Register V4: the endpoint model and end buffer as a projection theorem — LFR31's own-scale
recentering with `L = max {λC, 200Δ + s'/100}` (lane FC39-V4C(b); review 57, §6.2)

Review 57 asks for the endpoint slot's NATIVE content (B:10169–10170, BP-A LFR29–LFR31): the actual
pointed maps `F_p = (u, v) : (M, d_p, p) → ℝ × (Y, y₀)`, `G_p : (Y, y₀) → ([0, C], 0)`, the strong
and weak qualities, and LFR31 as a real output: if `d_p(p, a) ≤ 101Δ` and `d_Y(v(a), y₀) < 2b`, then
in `a`'s OWN normalization there are actual weak maps of qualities `b', s'` whose endpoint interval
has length `L = max {λC, 200Δ + s'/100} > 200Δ` (`λ = ρ(p)/ρ(a)`), the endpoint map being the
whole-space map with the basepoint repair `G_a(v(a)) = 0`, `G_a(z) = λ G(z)` (`z ≠ v(a)`).

* `Lfr31OutV4C hC F G a c hc Δ b' s'` (`c = λ`): the recentered rank-one map
  `F_a(x) = (c (u(x) − u(a)), v(x))` is a KL `b'`-approximation at `a` (source and residual factor
  rescaled by `c`), and there is `L = max {cC, 200Δ + s'/100} > 200Δ` with a KL `s'`-approximation
  `G_a : (Y, v(a)) → [0, L]` with `G_a(v(a)) = 0` and `G_a(z) = c G(z)` for `z ≠ v(a)` (LFR31.1).
* `lfr31Out_of_numeric_V4C`: LFR31 in normalized units (`ρ(p) = 1`), from LFR29.1
  (`Lfr29NumericV4C`), `C ≥ 200Δ`, `d(a, p) ≤ 101Δ`, `d(v(a), y₀) < 2b`; route of
  `isEdgePoint_of_lipschitz_scale`
  (`edge_recenter_rescale_budgets`, `recenterRescaleRealProduct`,
  `exists_recenterRescaleInterval_strict`) with the maps kept explicit. No continuity of the
  residual map and no upper bound on `C` are used.
* `lfr31Out_physical_V4C`: the same in physical units (maps in `d_p = d/ρ(p)`, `λ = ρ(p)/ρ(a)`);
  the new source metric `(d/ρ(p))·λ` IS `a`'s own normalization `d/ρ(a)` (`rescale_inv_ratio`).
* `ClosedFamilyInstanceV4.endpoint_V4C` / `ClosedFamilyInstanceC14DV4.endpoint_V4C` (projection
  from the final family's fields): at every register below the LFR29.1 cap, at every edge centre
  `j`, the family's strong maps (`edge.strong j`, `C > 200Δ`) exist, and for EVERY such pair and
  every `a` with `d(a, j) ≤ 101Δρ(j)`, `d(v(a), y₀) < 2b` the explicit LFR31 output holds at
  `λ = ρ(j)/ρ(a)` with the register's `Δ, b', s'`.
* Consumer `exists_closed_realization_endpoint_V4C`.

The slot `endpointUp` keeps its role as a free upper slot for `s`; its NATIVE consumers (LFR31's end
buffer `Δ²Λ ≪ s'`, i.e. `Λ < s'/(10⁸Δ²)`, and `s < 10⁻⁵ min {b', s'}`) are the register displays
used here, so no endpoint statement depends on `endpointUp > 0`.
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

/-- LFR29.1 in the numeral forms of the edge-recentering kernels. -/
theorem lfr29_kernel_forms_V4C {Δ τ b' s' s Λ b : ℝ} (hnum : Lfr29NumericV4C Δ τ b' s' s Λ b) :
    0 < b' ∧ 0 < s' ∧ b' < 1 / 10000 ∧ s' < 1 / 10000 ∧ Λ < 1 / (1000000 * Δ) ∧
      Λ < s' / (100000000 * Δ ^ 2) ∧ b' < 1 / (1000000 * Δ) ∧ s < b' / 100000 ∧
      s < s' / 100000 ∧ b < s / 100000 ∧ b < b' / 100000 ∧ 0 < s ∧ 0 < b ∧ 0 < Λ := by
  obtain ⟨⟨hb', hb'W, hs', hs'W⟩, ⟨hs, hsl⟩, ⟨hΛ, hΛl⟩, ⟨hb, hbl⟩⟩ := hnum
  unfold lfr29WV4C at hb'W hs'W
  simp only [lt_min_iff] at hb'W hs'W hΛl
  have hmin : min s (min b' s') = s := by
    apply min_eq_left
    have := lt_min hb' hs'
    nlinarith
  rw [hmin] at hbl
  have hsb' : s < b' / 100000 := by
    have := min_le_left b' s'
    nlinarith
  have hss' : s < s' / 100000 := by
    have := min_le_right b' s'
    nlinarith
  have h1 : (1 : ℝ) / (1000000 * Δ) = 1 / (10 ^ 6 * Δ) := by norm_num
  have h2 : s' / (100000000 * Δ ^ 2) = s' / (10 ^ 8 * Δ ^ 2) := by norm_num
  refine ⟨hb', hs', by norm_num at hb'W ⊢; linarith [hb'W.2],
    by norm_num at hs'W ⊢; linarith [hs'W.2],
    by rw [h1]; exact hΛl.1, by rw [h2]; exact hΛl.2, by rw [h1]; exact hb'W.1.2, hsb', hss',
    by linarith, by linarith, hs, hb, hΛ⟩

section Out

variable {X : Type} [mX : MetricSpace X] {Y : Type} [mY : MetricSpace Y]

/-- **LFR31's explicit output** (A:27627–27688) at the rescaling factor `c = λ`: the recentered
rank-one map is a KL `b'`-approximation at `a` (source and residual factor rescaled by `c`), and the
repaired endpoint map is a KL `s'`-approximation onto `[0, L]`,
`L = max {cC, 200Δ + s'/100} > 200Δ`, with `G_a(v(a)) = 0` and `G_a(z) = c G(z)` off `v(a)`
(LFR31.1). -/
def Lfr31OutV4C {p : X} {q : Y} {C β σ : ℝ} (hC : 0 ≤ C)
    (F : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), q)) β)
    (G : KleinerLottApprox q (⟨0, le_rfl, hC⟩ : Icc (0 : ℝ) C) σ) (a : X) (c : ℝ) (hc : 0 < c)
    (Δ β' σ' : ℝ) : Prop :=
  ∃ Fa : @KleinerLottApprox X (WithLp 2 (ℝ × Y)) (mX.rescale c hc)
      (MetricSpace.scaledProduct inferInstance mY c hc) a
      (WithLp.toLp 2 ((0 : ℝ), (F.toFun a).snd)) β',
    (∀ x, @KleinerLottApprox.toFun X (WithLp 2 (ℝ × Y)) (mX.rescale c hc)
        (MetricSpace.scaledProduct inferInstance mY c hc) a _ β' Fa x =
      WithLp.toLp 2 (c * ((F.toFun x).fst - (F.toFun a).fst), (F.toFun x).snd)) ∧
    ∃ (L : ℝ) (hL : 0 ≤ L), 200 * Δ < L ∧ L = max (c * C) (200 * Δ + σ' / 100) ∧
      ∃ Ga : @KleinerLottApprox Y (Icc (0 : ℝ) L) (mY.rescale c hc) _ (F.toFun a).snd
          ⟨0, le_rfl, hL⟩ σ',
        @KleinerLottApprox.toFun Y (Icc (0 : ℝ) L) (mY.rescale c hc) _ _ _ σ' Ga
            (F.toFun a).snd = ⟨0, le_rfl, hL⟩ ∧
          ∀ z, z ≠ (F.toFun a).snd →
            (@KleinerLottApprox.toFun Y (Icc (0 : ℝ) L) (mY.rescale c hc) _ _ _ σ' Ga z).val =
              c * (G.toFun z).val

/-- **LFR31 in normalized units** (`ρ(p) = 1`, `λ = ρ(a)⁻¹`): from LFR29.1, `C ≥ 200Δ`,
`d(a, p) ≤ 101Δ` and `d(v(a), y₀) < 2b`, the explicit own-scale weak maps of `Lfr31OutV4C`. -/
theorem lfr31Out_of_numeric_V4C {p a : X} {q : Y} {Δ τ C b s b' s' Λ : ℝ} {ρ : X → ℝ}
    (hnum : Lfr29NumericV4C Δ τ b' s' s Λ b) (hρ : LipschitzWith (Real.toNNReal Λ) ρ)
    (hρp : ρ p = 1) (hρa : 0 < ρ a) (hΔ : 1 ≤ Δ) (hC : 0 ≤ C)
    (F : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), q)) b)
    (G : KleinerLottApprox q (⟨0, le_rfl, hC⟩ : Icc (0 : ℝ) C) s)
    (hlength : 200 * Δ ≤ C) (ha : dist a p ≤ 101 * Δ) (hqa : dist (F.toFun a).snd q < 2 * b) :
    Lfr31OutV4C hC F G a (ρ a)⁻¹ (inv_pos.mpr hρa) Δ b' s' := by
  obtain ⟨hb', hs', hsb', hss', hscale, hend, hbΔ, hσβ, hσσ, hβσ, hββ, -, -, hΛ⟩ :=
    lfr29_kernel_forms_V4C hnum
  have hΛc : ((Real.toNNReal Λ : NNReal) : ℝ) = Λ := Real.coe_toNNReal _ hΛ.le
  have hclose : |ρ a - 1| ≤ 101 * Δ * Λ := by
    have hh := abs_scale_ratio_sub_one_le hρ (p := p) (a := a) (by rw [hρp]; norm_num)
    rw [hρp, div_one, div_one, hΛc] at hh
    exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left ha hΛ.le])
  obtain ⟨-, -, hFerror, hFdomain, hcontraction, hGdomain, hGerror⟩ :=
    edge_recenter_rescale_budgets hΔ hΛ.le hρa F.error_pos G.error_pos
      hb' hs' hsb' hss' hscale hend hbΔ hσβ hσσ hβσ hββ hclose
      dist_nonneg ha dist_nonneg hqa
  have hG := G.exists_recenterRescaleInterval_strict hC (F.toFun a).snd (inv_pos.mpr hρa) hs'
    (by linarith) hlength hcontraction hGdomain hGerror
  obtain ⟨L, hL, hstrict, hLeq, Ga, hGa0, hGav⟩ := hG
  exact ⟨F.recenterRescaleRealProduct a (inv_pos.mpr hρa) hFerror (by linarith) hFdomain,
    fun x => rfl, L, hL, hstrict, hLeq, Ga, hGa0, hGav⟩

/-- **LFR31 in physical units**: strong maps in `d_p = d/ρ(p)`, `λ = (ρ(a)/ρ(p))⁻¹ = ρ(p)/ρ(a)`;
the explicit own-scale output of `Lfr31OutV4C` at `λ`, and the new source metric `(d/ρ(p))·λ` is
`a`'s own normalization `d/ρ(a)`. -/
theorem lfr31Out_physical_V4C {p a : X} {q : Y} {Δ τ C b s b' s' Λ : ℝ} {ρ : X → ℝ}
    (hnum : Lfr29NumericV4C Δ τ b' s' s Λ b) (hρ : LipschitzWith (Real.toNNReal Λ) ρ)
    (hρpos : ∀ x, 0 < ρ x) (hΔ : 1 ≤ Δ) (hC : 0 ≤ C)
    (F : @KleinerLottApprox X (WithLp 2 (ℝ × Y)) (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) _
      p (WithLp.toLp 2 ((0 : ℝ), q)) b)
    (G : KleinerLottApprox q (⟨0, le_rfl, hC⟩ : Icc (0 : ℝ) C) s)
    (hlength : 200 * Δ ≤ C) (ha : dist a p ≤ 101 * Δ * ρ p)
    (hqa : dist (@KleinerLottApprox.toFun X (WithLp 2 (ℝ × Y))
      (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) _ p _ b F a).snd q < 2 * b) :
    @Lfr31OutV4C X (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) Y mY p q C b s hC F G a
        (ρ a / ρ p)⁻¹ (inv_pos.mpr (div_pos (hρpos a) (hρpos p))) Δ b' s' ∧
      (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))).rescale (ρ a / ρ p)⁻¹
          (inv_pos.mpr (div_pos (hρpos a) (hρpos p))) =
        mX.rescale (ρ a)⁻¹ (inv_pos.mpr (hρpos a)) := by
  have hr := @lipschitzWith_normalized_scale X mX ρ (Real.toNNReal Λ) hρ p (hρpos p)
  have hra : @dist X (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))).toDist a p ≤ 101 * Δ := by
    rw [MetricSpace.rescale_dist, ← div_eq_inv_mul, div_le_iff₀ (hρpos p)]
    exact ha
  exact ⟨@lfr31Out_of_numeric_V4C X (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) Y mY p a q Δ τ C
    b s b' s' Λ (fun x => ρ x / ρ p) hnum hr (div_self (hρpos p).ne')
    (div_pos (hρpos a) (hρpos p)) hΔ hC F G hlength hra hqa,
    mX.rescale_inv_ratio (hρpos p) (hρpos a)⟩

end Out

/-- **The endpoint model on every instance of the final family** (projection theorem, review 57
§6.2): at every register of a strategy below the LFR29.1 cap, at every edge centre `j`, the family's
own strong maps exist (`edge.strong j`: target `ℝ × Y`, `C > 200Δ`, qualities `b, s`), and for EVERY
such pair `(F_j, G_j)` and every `a` with `d(a, j) ≤ 101Δρ(j)` and `d(v(a), y₀) < 2b`, LFR31's
explicit output holds at `λ = ρ(j)/ρ(a)` with the register's `Δ, b', s'`, in `a`'s own
normalization. -/
theorem ClosedFamilyInstanceV4.endpoint_V4C {K : ℕ} {D : ClosedEarlyData}
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
        (Gj : @KleinerLottApprox Y (Icc (0 : ℝ) C) mY _ q ⟨0, le_rfl, hC⟩ R.later.err.s)
        (a : M.X), dist a j ≤ 101 * R.later.excl.Δ * F.ρ j →
        dist (@KleinerLottApprox.toFun M.X (WithLp 2 (ℝ × Y))
          (M.mX.rescale (F.ρ j)⁻¹ (inv_pos.mpr (F.ρ_pos j))) _ j _ R.later.split.b Fj a).snd q <
            2 * R.later.split.b →
        @Lfr31OutV4C M.X (M.mX.rescale (F.ρ j)⁻¹ (inv_pos.mpr (F.ρ_pos j))) Y mY j q C
          R.later.split.b R.later.err.s hC Fj Gj a (F.ρ a / F.ρ j)⁻¹
          (inv_pos.mpr (div_pos (F.ρ_pos a) (F.ρ_pos j))) R.later.excl.Δ R.later.err.wk.b'
          R.later.err.wk.s' := by
  obtain ⟨Y, mY, q, C, hC, hCl, hF, hG⟩ := F.family.edge.strong j hj
  have hΔ : 1 ≤ R.later.excl.Δ := by
    have := R.later.Δ_gt
    have := le_max_left (10 ^ 6 : ℝ)
      (max (100 / R.later.excl.β₂) (T.ΔLow R.stage R.later.circle R.later.excl.β₃ R.later.excl.β₂))
    norm_num at *
    linarith
  exact ⟨Y, mY, q, C, hC, hCl, hF, hG, fun Fj Gj a ha hqa =>
    (@lfr31Out_physical_V4C M.X M.mX Y mY j a q _ _ _ _ _ _ _ _ F.ρ (R.lfr29_numeric_of_below_V4C h)
      F.family.lipschitz_scale F.ρ_pos hΔ hC Fj Gj hCl.le ha hqa).1⟩

/-- The same on every C14D instance. -/
theorem ClosedFamilyInstanceC14DV4.endpoint_V4C {K : ℕ} {D : ClosedEarlyData}
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
        (Gj : @KleinerLottApprox Y (Icc (0 : ℝ) C) mY _ q ⟨0, le_rfl, hC⟩ R.later.err.s)
        (a : M.X), dist a j ≤ 101 * R.later.excl.Δ * F.ρ j →
        dist (@KleinerLottApprox.toFun M.X (WithLp 2 (ℝ × Y))
          (M.mX.rescale (F.ρ j)⁻¹ (inv_pos.mpr (F.ρ_pos j))) _ j _ R.later.split.b Fj a).snd q <
            2 * R.later.split.b →
        @Lfr31OutV4C M.X (M.mX.rescale (F.ρ j)⁻¹ (inv_pos.mpr (F.ρ_pos j))) Y mY j q C
          R.later.split.b R.later.err.s hC Fj Gj a (F.ρ a / F.ρ j)⁻¹
          (inv_pos.mpr (div_pos (F.ρ_pos a) (F.ρ_pos j))) R.later.excl.Δ R.later.err.wk.b'
          R.later.err.wk.s' :=
  F.toC14_VAL6.endpoint_V4C h j hj

/-- **Consumer: the endpoint model realized.** For every threshold strategy `U`, the complete C14D
realization of `U` with the LFR29.1 cap gives a common strategy `T` such that at every register, on
every member of the tail, every edge centre of the final family carries actual strong maps for
which LFR31's explicit own-scale recentering holds at every admissible point `a`. -/
theorem exists_closed_realization_endpoint_V4C (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2)))
    {D : ClosedEarlyData} (U : ClosedThresholdsV4 D) :
    ∃ T : ClosedThresholdsV4 D, ClosedStrategyRefinesV4 T U.withLfr29_V4C ∧
      ClosedStrategyBelowV4 T U ∧ ClosedFamilyAtC14DV4 K Wseq gseq T ∧
      ∀ R : ClosedRegisterV4 D T, ∃ εr δ' Λz : ℝ, ∃ δ : ℝ, δ < δ' ∧ ∀ m, R.later.tail ≤ m →
        ∃ M : ClosedModel (Wseq m) (gseq m), ∃ F : ClosedFamilyInstanceC14DV4 K R M δ εr Λz,
          ∀ j ∈ F.family.edge.centres,
            ∃ (Y : Type) (mY : MetricSpace Y) (q : Y) (C : ℝ) (hC : 0 ≤ C),
              200 * R.later.excl.Δ < C ∧
              ∃ (Fj : @KleinerLottApprox M.X (WithLp 2 (ℝ × Y))
                  (M.mX.rescale (F.ρ j)⁻¹ (inv_pos.mpr (F.ρ_pos j))) _ j
                  (WithLp.toLp 2 ((0 : ℝ), q)) R.later.split.b)
                (Gj : @KleinerLottApprox Y (Icc (0 : ℝ) C) mY _ q ⟨0, le_rfl, hC⟩
                  R.later.err.s),
                ∀ a : M.X, dist a j ≤ 101 * R.later.excl.Δ * F.ρ j →
                  dist (@KleinerLottApprox.toFun M.X (WithLp 2 (ℝ × Y))
                    (M.mX.rescale (F.ρ j)⁻¹ (inv_pos.mpr (F.ρ_pos j))) _ j _ R.later.split.b
                    Fj a).snd q < 2 * R.later.split.b →
                  @Lfr31OutV4C M.X (M.mX.rescale (F.ρ j)⁻¹ (inv_pos.mpr (F.ρ_pos j))) Y mY j q
                    C R.later.split.b R.later.err.s hC Fj Gj a (F.ρ a / F.ρ j)⁻¹
                    (inv_pos.mpr (div_pos (F.ρ_pos a) (F.ρ_pos j))) R.later.excl.Δ
                    R.later.err.wk.b' R.later.err.wk.s' := by
  obtain ⟨T, hTU, -, -, hfam⟩ :=
    exists_closed_realization_C14D_VAL6 K hK A hA Wseq gseq hf hg U.withLfr29_V4C
  have hb : ClosedStrategyBelowV4 T U.withLfr29_V4C := hTU.below_VAL6
  refine ⟨T, hTU, hb.trans_VAL6 U.withLfr29_below_V4C, hfam, fun R => ?_⟩
  obtain ⟨εrF, δ'F, ΛzF, hF⟩ := hfam
  obtain ⟨-, -, -, -, -, -, δc, -, hδc, ht⟩ := hF R
  refine ⟨εrF R.stage R.later.circle R.later.excl R.later.err R.later.scale R.later.split.b
    R.later.split.β₁, δ'F R.stage R.later.circle R.later.excl R.later.err R.later.scale
    R.later.split.b R.later.split.β₁, ΛzF R.stage R.later.circle R.later.excl R.later.err
    R.later.scale R.later.split.b R.later.split.β₁, δc, hδc, fun m hm => ?_⟩
  obtain ⟨M, ⟨F⟩, -, -⟩ := ht m hm
  refine ⟨M, F, fun j hj => ?_⟩
  obtain ⟨Y, mY, q, C, hC, hCl, ⟨Fj⟩, ⟨Gj⟩, hout⟩ := F.endpoint_V4C hb j hj
  exact ⟨Y, mY, q, C, hC, hCl, Fj, Gj, hout Fj Gj⟩

end DifferentialGeometry.Geometry.Collapse
