import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.Finite.Assembly

/-!
# LFR02: localized distance smoothing in the finite category

Blueprint 207A, LFR02 (`thm:collapse-finite-distance-smoothing`, A:24862–24955): LC28 on a smooth
carrier with a complete metric of finite order, with the threshold `θ(ε) = min{1, ε}/100`, the
difference `F - d_Y` compactly supported in `U`, and the gradient estimate `‖∇_g F(x) + v‖_g < ε`
for every `v ∈ V_x(Y)` on the smooth neighbourhood of `C`.

* `exists_localized_distance_smoothing_finite`: LC28 (θ = ε/4) for a complete metric
  `g ∈ C^{r+1}`, `2 ≤ r` (re-run of LC28's proof; the chart/assembly tiers are in
  `Finite/LocalApproximation`, `Finite/Assembly`).
* `abs_mfderiv_add_inner_le_of_lipschitz_finite`: at a point where `F` is differentiable and
  `F - d_Y` is `L`-Lipschitz, `|dF_x(w) + g_x(v, w)| ≤ L |w|_g` for EVERY `v ∈ V_x(Y)` (only the
  upper first variation is used, in the directions `w` and `-w`).
* `exists_localized_distance_smoothing_lfr02`: LFR02 with the row's threshold.

Deviation (recorded in sheet-CM-D.md, D4): the metric is `C^{r+1}` with `2 ≤ r` (C³), not C²; every
consumer of LFR02 has order ≥ 4.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Metric
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian Bundle.ContMDiffRiemannianMetric

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]

/-- **LC28 for a complete metric of finite order** (localized distance smoothing), with
`θ(ε) = ε / 4`. -/
theorem exists_localized_distance_smoothing_finite [CompleteSpace M] {r : ℕ∞}
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {ε : ℝ} (hε : 0 < ε) {Y U C : Set M} (hY : IsClosed Y)
    (hYne : Y.Nonempty) (hU : IsOpen U) (hUY : U ⊆ Yᶜ)
    (hdiam : ∀ q ∈ U, ∀ v ∈ finiteMinimizingDirectionsTo g Y q,
      ∀ v' ∈ finiteMinimizingDirectionsTo g Y q, Real.sqrt (g.inner q (v - v') (v - v')) < ε / 4)
    (hC : IsCompact C) (hCU : C ⊆ U) {e : ℝ} (he : 0 < e) :
    ∃ F : M → ℝ, ∃ O : Set M, IsOpen O ∧ C ⊆ O ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O ∧
      (∀ x, |F x - Metric.infDist x Y| < e) ∧ (∀ x, x ∉ U → F x = Metric.infDist x Y) ∧
      (∀ x y, |(F x - Metric.infDist x Y) - (F y - Metric.infDist y Y)| ≤ ε * dist x y) ∧
      LipschitzWith (Real.toNNReal (1 + ε)) F := by
  have hdisj : Disjoint U Y := Set.subset_compl_iff_disjoint_right.mp hUY
  have hloc : ∀ b ∈ U, ∃ W : Set M, IsOpen W ∧ b ∈ W ∧ W ⊆ U ∧ IsCompact (closure W) ∧
      ∀ η > 0, ∃ f' : M → ℝ, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f' W ∧
        (∀ x ∈ W, |f' x - Metric.infDist x Y| ≤ η) ∧
        (∀ x ∈ W, ∀ x' ∈ W, |(f' x - Metric.infDist x Y) - (f' x' - Metric.infDist x' Y)| ≤
          3 * ε / 4 * dist x x') ∧
        (∀ x ∈ W, ∀ x' ∈ W, |f' x - f' x'| ≤ (3 * ε / 4 + 1) * dist x x') := by
    intro b hb
    obtain ⟨W, hWo, hbW, hWU, hWc, happ⟩ := exists_local_distance_approximation_finite g hr hnorm hY hYne
      hU hdisj (θ := ε / 4) (L := 3 * ε / 4) (by linarith) hdiam hb
    refine ⟨W, hWo, hbW, hWU, hWc, fun η hη => ?_⟩
    obtain ⟨f', hsm, hcl, hd⟩ := happ η hη
    refine ⟨f', hsm, hcl, hd, fun x hx x' hx' => ?_⟩
    have h1 := hd x hx x' hx'
    have h2 : |Metric.infDist x Y - Metric.infDist x' Y| ≤ 1 * dist x x' := by
      rw [← Real.dist_eq]; exact (Metric.lipschitz_infDist_pt Y).dist_le_mul x x'
    calc |f' x - f' x'| = |((f' x - Metric.infDist x Y) - (f' x' - Metric.infDist x' Y)) +
          (Metric.infDist x Y - Metric.infDist x' Y)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ 3 * ε / 4 * dist x x' + 1 * dist x x' := add_le_add h1 h2
      _ = (3 * ε / 4 + 1) * dist x x' := by ring
  obtain ⟨F, O, hO, hCO, hFO, hclose, hout, hdiff, hlipF⟩ :=
    exists_smoothing_of_local_approximations_finite g hr hnorm (Metric.lipschitz_infDist_pt Y) hU hC hCU
      (by positivity) hloc he (ε' := ε / 4) (by positivity)
  refine ⟨F, O, hO, hCO, hFO, hclose, hout, fun x y => ?_, ?_⟩
  · have := hdiff x y
    calc _ ≤ (3 * ε / 4 + ε / 4) * dist x y := this
      _ = ε * dist x y := by ring
  · refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
    have hmax : max ((1 : ℝ≥0) : ℝ) (3 * ε / 4 + 1) = 3 * ε / 4 + 1 :=
      max_eq_right (by simp only [NNReal.coe_one, le_add_iff_nonneg_left]; positivity)
    have := hlipF x y
    rw [hmax] at this
    calc _ ≤ (3 * ε / 4 + 1 + ε / 4) * dist x y := this
      _ = (1 + ε) * dist x y := by ring


omit [NeZero (Module.finrank ℝ E)] in
/-- One-sided form of the gradient estimate: `dF_x(w) ≤ -g_x(v, w) + L N_x(w)`. -/
theorem mfderiv_le_neg_inner_add_finite [CompleteSpace M] {r : ℕ∞}
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {Y : Set M} (hY : IsClosed Y) (hYne : Y.Nonempty) {F : M → ℝ} {x : M} (hx : x ∉ Y)
    (hF : MDifferentiableAt I 𝓘(ℝ, ℝ) F x) {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ y, |(F y - Metric.infDist y Y) - (F x - Metric.infDist x Y)| ≤ L * dist y x)
    {v : TangentSpace I x} (hv : v ∈ finiteMinimizingDirectionsTo g Y x) (w : E) :
    mvfderiv (I := I) F x w ≤ -g.inner x v w + L * finiteMetricSeminormAt g x w := by
  set φ := extChartAt I x with hφ
  set N := finiteMetricSeminormAt g x with hN
  set D := mvfderiv (I := I) F x w with hD
  set γ : ℝ → M := fun t => φ.symm (φ x + t • w) with hγ
  have hxs : x ∈ φ.source := by rw [hφ, extChartAt_source]; exact mem_chart_source H x
  have hγ0 : γ 0 = x := by simp only [hγ, zero_smul, add_zero]; exact φ.left_inv hxs
  have hvel := hasMFDerivAt_extChartAt_symm_line (I := I) x (mem_chart_source H x) w
  rw [trivializationAt_symmL_self] at hvel
  have hF' : HasMFDerivAt I 𝓘(ℝ, ℝ) F (γ 0) (mfderiv I 𝓘(ℝ, ℝ) F x) := by
    rw [hγ0]; exact hF.hasMFDerivAt
  have hcomp : HasFDerivAt (fun t => F (γ t))
      (show ℝ →L[ℝ] ℝ from (mfderiv I 𝓘(ℝ, ℝ) F x).comp ((1 : ℝ →L[ℝ] ℝ).smulRight w)) 0 :=
    hasMFDerivAt_iff_hasFDerivAt.mp (hF'.comp 0 hvel)
  have hderiv : HasDerivAt (fun t => F (γ t)) D 0 := by
    refine hcomp.hasDerivAt.congr_deriv ?_
    change (mfderiv I 𝓘(ℝ, ℝ) F x) (((1 : ℝ →L[ℝ] ℝ).smulRight w) 1) =
      mfderiv I 𝓘(ℝ, ℝ) F x w
    rw [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul]
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  set κ : ℝ := 1 + ε / (4 * (L * N w + 1)) with hκ
  have hNw0 : 0 ≤ N w := apply_nonneg _ _
  have hκ1 : 1 < κ := by
    rw [hκ]
    have : 0 < ε / (4 * (L * N w + 1)) := by positivity
    linarith
  have hκL : L * (κ * N w) ≤ L * N w + ε / 4 := by
    have e : L * (κ * N w) = L * N w + L * N w * (ε / (4 * (L * N w + 1))) := by rw [hκ]; ring
    have h1 : L * N w * (ε / (4 * (L * N w + 1))) ≤ ε / 4 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [mul_nonneg hL hNw0]
    linarith
  obtain ⟨ρ, hρ, hρt, hK1⟩ := exists_ball_dist_chart_symm_le_finite g hnorm x hκ1
  have hup := eventually_infDist_sub_le_finite_of_eq g hr hnorm hY hYne hγ0 hvel hx hv
    (c := -g.inner x v w + ε / 4) (by linarith)
  have hlo := (hasDerivAt_iff_isLittleO.mp hderiv).def (show 0 < ε / 4 by positivity)
  have hball : ∀ᶠ t in 𝓝 (0 : ℝ), φ x + t • w ∈ Metric.ball (φ x) ρ := by
    have hc : Continuous (fun t : ℝ => φ x + t • w) := continuous_const.add
      (continuous_id.smul continuous_const)
    have := hc.tendsto 0
    simp only [zero_smul, add_zero] at this
    exact this.eventually (Metric.ball_mem_nhds _ hρ)
  have hlo' : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖F (γ t) - F (γ 0) - (t - 0) • D‖ ≤ ε / 4 * ‖t - 0‖ :=
    nhdsWithin_le_nhds hlo
  have hball' : ∀ᶠ t in 𝓝[>] (0 : ℝ), φ x + t • w ∈ Metric.ball (φ x) ρ :=
    nhdsWithin_le_nhds hball
  have hpos' : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioi (0 : ℝ) := self_mem_nhdsWithin
  obtain ⟨t, ⟨hupt, hlot, hballt⟩, htpos⟩ := ((hup.and (hlo'.and hball')).and hpos').exists
  have htp : 0 < t := htpos
  have hdist : dist (γ t) x ≤ κ * (t * N w) := by
    have h := hK1 _ hballt _ (Metric.mem_ball_self hρ)
    rw [φ.left_inv hxs, add_sub_cancel_left, map_smul_eq_mul, Real.norm_eq_abs,
      abs_of_pos htp] at h
    exact h
  have h1 := (abs_le.mp (hlip (γ t))).2
  rw [hγ0] at hlot
  simp only [sub_zero, Real.norm_eq_abs, abs_of_pos htp, smul_eq_mul] at hlot
  have h2 := (abs_le.mp hlot).1
  have h3 : L * dist (γ t) x ≤ t * (L * N w + ε / 4) := by
    have := mul_le_mul_of_nonneg_left hdist hL
    have e : L * (κ * (t * N w)) = t * (L * (κ * N w)) := by ring
    rw [e] at this
    have := mul_le_mul_of_nonneg_left hκL htp.le
    linarith
  have h4 : t * D ≤ t * (-g.inner x v w + L * N w + 3 * ε / 4) := by nlinarith
  have h5 := le_of_mul_le_mul_left h4 htp
  linarith

omit [NeZero (Module.finrank ℝ E)] in
/-- **Gradient estimate at smooth points**: if `F` is differentiable at `x ∉ Y` and `F - d_Y` is
`L`-Lipschitz at `x`, then `|dF_x(w) + g_x(v, w)| ≤ L |w|_g` for EVERY minimizing direction `v`,
i.e. `‖∇_g F(x) + v‖_g ≤ L`. Only the upper first variation (CM3.c, upper half) is used. -/
theorem abs_mfderiv_add_inner_le_of_lipschitz_finite [CompleteSpace M] {r : ℕ∞}
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {Y : Set M} (hY : IsClosed Y) (hYne : Y.Nonempty) {F : M → ℝ} {x : M} (hx : x ∉ Y)
    (hF : MDifferentiableAt I 𝓘(ℝ, ℝ) F x) {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ y, |(F y - Metric.infDist y Y) - (F x - Metric.infDist x Y)| ≤ L * dist y x)
    {v : TangentSpace I x} (hv : v ∈ finiteMinimizingDirectionsTo g Y x) (w : TangentSpace I x) :
    |mvfderiv (I := I) F x w + g.inner x v w| ≤ L * Real.sqrt (g.inner x w w) := by
  have h1 := mfderiv_le_neg_inner_add_finite g hr hnorm hY hYne hx hF hL hlip hv w
  have h2 := mfderiv_le_neg_inner_add_finite g hr hnorm hY hYne hx hF hL hlip hv (-w)
  have e1 : mvfderiv (I := I) F x (-w) = -mvfderiv (I := I) F x w := map_neg _ w
  have e2 : g.inner x v (-w) = -g.inner x v w := map_neg _ w
  have e3 : finiteMetricSeminormAt g x (-w) = finiteMetricSeminormAt g x w := map_neg_eq_map _ w
  rw [e1, e2, e3] at h2
  rw [abs_le]
  have e4 : finiteMetricSeminormAt g x w = Real.sqrt (g.inner x w w) := rfl
  rw [← e4]
  constructor <;> linarith

/-- **LFR02** (localized distance smoothing in the finite category), with the row's threshold
`θ(ε) = min{1, ε}/100`: for a complete metric `g ∈ C^{r+1}` (`2 ≤ r`) whose distance is the distance
of `M`, every closed nonempty `Y`, open `U ⊆ Yᶜ` on which the minimizing directions `V_q(Y)` have
chordal diameter `< min{1, ε}/100`, compact `C ⊆ U` and `e > 0`, there are `F` and an open `O ⊇ C`
with: `F` smooth on `O`; `|F - d_Y| < e`; `F = d_Y` off `U`; `F - d_Y` `ε`-Lipschitz; `F`
`(1 + ε)`-Lipschitz; `F - d_Y` compactly supported in `U`; and on `O`, for every `v ∈ V_x(Y)`,
`|dF_x(w) + g_x(v, w)| ≤ (ε/25) |w|_g` (`dF = mvfderiv F`), i.e. `‖∇_g F(x) + v‖_g ≤ ε/25 < ε`. -/
theorem exists_localized_distance_smoothing_lfr02 [CompleteSpace M] {r : ℕ∞}
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {ε : ℝ} (hε : 0 < ε) {Y U C : Set M} (hY : IsClosed Y) (hYne : Y.Nonempty) (hU : IsOpen U)
    (hUY : U ⊆ Yᶜ)
    (hdiam : ∀ q ∈ U, ∀ v ∈ finiteMinimizingDirectionsTo g Y q,
      ∀ v' ∈ finiteMinimizingDirectionsTo g Y q,
        Real.sqrt (g.inner q (v - v') (v - v')) < min 1 ε / 100)
    (hC : IsCompact C) (hCU : C ⊆ U) {e : ℝ} (he : 0 < e) :
    ∃ F : M → ℝ, ∃ O : Set M, IsOpen O ∧ C ⊆ O ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O ∧
      (∀ x, |F x - Metric.infDist x Y| < e) ∧ (∀ x, x ∉ U → F x = Metric.infDist x Y) ∧
      (∀ x y, |(F x - Metric.infDist x Y) - (F y - Metric.infDist y Y)| ≤ ε * dist x y) ∧
      LipschitzWith (Real.toNNReal (1 + ε)) F ∧
      HasCompactSupport (fun x => F x - Metric.infDist x Y) ∧
      tsupport (fun x => F x - Metric.infDist x Y) ⊆ U ∧
      ∀ x ∈ O, ∀ v ∈ finiteMinimizingDirectionsTo g Y x, ∀ w : TangentSpace I x,
        |mvfderiv (I := I) F x w + g.inner x v w| ≤ ε / 25 * Real.sqrt (g.inner x w w) := by
  have : ProperSpace M := Manifold.properSpace_of_isRiemannianManifold I
  set ε'' : ℝ := min 1 ε / 25 with hε''
  have hmin : 0 < min 1 ε := lt_min one_pos hε
  have hε''pos : 0 < ε'' := by positivity
  have hε''le : ε'' ≤ ε / 25 := by
    rw [hε'']; exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hε''ε : ε'' ≤ ε := by linarith
  obtain ⟨U', hU'o, hCU', hU'U, hU'c⟩ := exists_open_between_and_isCompact_closure hC hU hCU
  have hU'Y : U' ⊆ Yᶜ := subset_closure.trans (hU'U.trans hUY)
  obtain ⟨F, O, hO, hCO, hFO, hclose, hout, hdiff, hlipF⟩ :=
    exists_localized_distance_smoothing_finite g hr hnorm hε''pos hY hYne hU'o hU'Y
      (fun q hq v hv v' hv' => by
        have := hdiam q (hU'U (subset_closure hq)) v hv v' hv'
        rw [hε'']; linarith) hC hCU' he
  have hzero : ∀ x, x ∉ U' → F x - Metric.infDist x Y = 0 := fun x hx => by
    rw [hout x hx, sub_self]
  have hsupp : tsupport (fun x => F x - Metric.infDist x Y) ⊆ closure U' := by
    refine closure_minimal (fun x hx => ?_) isClosed_closure
    by_contra hxU
    exact hx (hzero x (fun h => hxU (subset_closure h)))
  refine ⟨F, O ∩ U', hO.inter hU'o, subset_inter hCO hCU', hFO.mono inter_subset_left, hclose,
    fun x hx => hout x (fun h => hx (hU'U (subset_closure h))), fun x y => ?_, ?_,
    hU'c.of_isClosed_subset (isClosed_tsupport _) hsupp, hsupp.trans hU'U, ?_⟩
  · exact (hdiff x y).trans (mul_le_mul_of_nonneg_right hε''ε dist_nonneg)
  · refine hlipF.weaken ?_
    exact Real.toNNReal_le_toNNReal (by linarith)
  · intro x hx v hv w
    have hxY : x ∉ Y := hU'Y hx.2
    have hFx : MDifferentiableAt I 𝓘(ℝ, ℝ) F x :=
      ((hFO.mono inter_subset_left).contMDiffAt ((hO.inter hU'o).mem_nhds hx)).mdifferentiableAt
        (by simp)
    have h := abs_mfderiv_add_inner_le_of_lipschitz_finite g hr hnorm hY hYne hxY hFx
      hε''pos.le (fun y => hdiff y x) hv w
    exact h.trans (mul_le_mul_of_nonneg_right hε''le (Real.sqrt_nonneg _))

end DifferentialGeometry.Geometry.Collapse
