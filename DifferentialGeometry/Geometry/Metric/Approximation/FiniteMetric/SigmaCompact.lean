import DifferentialGeometry.Geometry.Metric.Approximation.FiniteMetric.SmoothingConvergence
import DifferentialGeometry.Geometry.Metric.Approximation.FiniteMetric.LocallyFiniteGluing
import DifferentialGeometry.Geometry.Metric.Approximation.FiniteMetric.CurvatureLevel

/-!
# Smooth approximants of a finite-regularity metric on a σ-compact manifold (CM5.a)

Lane CM-A, package CM5.a of the D-FOUND design (`docs/geometrization/chapter13/
design-finite-surface-foundations-20261004.md` §C1, §D1): the non-compact form of B7's A1–A3
(`exists_smooth_metric_approximation`, `exists_smooth_approximants_of_sectional_nonneg`).

Construction. Every point `p` has a chart ball `U p` whose closure in the chart is compact; a
smooth partition of unity `ρ` subordinate to these balls is locally finite, and each
`K i = φ_i (tsupport ρ_i)` is compact. In each chart B7's mollified coefficients converge in `C²`
on `K i`; they are reindexed chart by chart so that the `k`-th one is uniformly
`1/(k+2)`-close to the limit RELATIVE to the chart coercivity constant. The `finsum` gluing
(`exists_smoothMetric_glued_finsum`) then gives smooth metrics with

* `(1 - 1/(k+2))² g ≤ gSeq k ≤ (1 + 1/(k+2))² g` everywhere (convex combination of relative
  errors);
* `C²` convergence of the chart coefficients on every compact subset of every chart target (on a
  compact set only finitely many partition functions are nonzero);
* hence, by `eventually_sectionalBoundedBelowAt_of_chartCoeff_tendsto`, `sec(gSeq k) ≥ κ - ε`
  eventually on every compact set on which `sec_g ≥ κ`.

## Main declarations
* `exists_smooth_approximants_sigmaCompact_chart`: bilipschitz bounds and chart `C²` convergence.
* `exists_smooth_approximants_sigmaCompact`: the frozen CM5.a statement.
-/

set_option autoImplicit false

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Geometry.MetricSmoothing

open DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

/-- **CM5.a, chart form.** On a σ-compact manifold with a boundaryless model, a `C^n` metric `g`,
`2 ≤ n`, is the limit of smooth metrics `gSeq k` that are `(1 ± 1/(k+2))`-bilipschitz to `g`
everywhere and whose chart coefficients converge in `C²` to those of `g` on every compact subset
of every chart target. -/
theorem exists_smooth_approximants_sigmaCompact_chart {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (hn : (2 : ℕ∞ω) ≤ n) :
    ∃ gSeq : ℕ → SmoothRiemannianMetric I M,
      (∀ (k : ℕ) (x : M) (w : TangentSpace I x),
        (1 - 1 / ((k : ℝ) + 2)) ^ 2 * g.inner x w w ≤ (gSeq k).inner x w w ∧
          (gSeq k).inner x w w ≤ (1 + 1 / ((k : ℝ) + 2)) ^ 2 * g.inner x w w) ∧
      ∀ (q : M) (L : Set E), IsCompact L → L ⊆ (extChartAt I q).target →
        MapCPConvergenceOn L 2 (fun k => chartCoeff (gSeq k) q) (chartCoeff g q) := by
  classical
  -- chart balls with compact closure in the chart
  have hr : ∀ x : M, ∃ r : ℝ, 0 < r ∧
      Metric.closedBall (extChartAt I x x) r ⊆ (extChartAt I x).target := by
    intro x
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (isOpen_extChartAt_target (I := I) x) _
      (mem_extChartAt_target (I := I) x)
    exact ⟨r / 2, half_pos hr, (Metric.closedBall_subset_ball (half_lt_self hr)).trans hball⟩
  choose r hr0 hrt using hr
  let U : M → Set M := fun x =>
    (extChartAt I x).source ∩ extChartAt I x ⁻¹' Metric.ball (extChartAt I x x) (r x)
  have hUo : ∀ x, IsOpen (U x) := fun x => isOpen_extChartAt_preimage' x Metric.isOpen_ball
  obtain ⟨ρ, hρU⟩ := SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ U hUo
    (fun x _ => mem_iUnion.2 ⟨x, mem_extChartAt_source x, Metric.mem_ball_self (hr0 x)⟩)
  have hρs : ∀ i, tsupport (ρ i) ⊆ (extChartAt I i).source :=
    fun i => (hρU i).trans inter_subset_left
  have hρsub : ρ.IsSubordinate fun i => (extChartAt I ((fun j : M => j) i)).source := hρs
  let K : M → Set E := fun i => extChartAt I i '' tsupport (ρ i)
  have htsc : ∀ i, IsCompact (tsupport (ρ i)) := by
    intro i
    have hS : IsCompact ((extChartAt I i).symm '' Metric.closedBall (extChartAt I i i) (r i)) :=
      (isCompact_closedBall _ _).image_of_continuousOn
        ((continuousOn_extChartAt_symm i).mono (hrt i))
    refine hS.of_isClosed_subset (isClosed_tsupport _) fun z hz => ?_
    have hzU := hρU i hz
    exact ⟨extChartAt I i z, Metric.ball_subset_closedBall hzU.2, (extChartAt I i).left_inv hzU.1⟩
  have hK : ∀ i, IsCompact (K i) := fun i =>
    (htsc i).image_of_continuousOn ((continuousOn_extChartAt i).mono (hρs i))
  have hKt : ∀ i, K i ⊆ (extChartAt I i).target := by
    rintro i _ ⟨x, hx, rfl⟩
    exact (extChartAt I i).map_source (hρs i hx)
  have hb : ∀ i, ContDiffOn ℝ 2 (chartCoeff g i) (extChartAt I i).target :=
    fun i => contDiffOn_chartCoeff g hn i
  have hb2 : ∀ i, ContDiffOn ℝ ((2 : ℕ) : ℕ∞) (chartCoeff g i) (extChartAt I i).target :=
    fun i => (hb i).of_le (by norm_num)
  -- chart coercivity constants
  have hbounds : ∀ i, ∃ C : ℝ, 1 ≤ C ∧ ∃ W : Set E, IsOpen W ∧ K i ⊆ W ∧
      closure W ⊆ (extChartAt I i).target ∧ ∀ z ∈ closure W,
        ∀ v : E, C⁻¹ * ‖v‖ ^ 2 ≤ chartCoeff g i z v v ∧
          chartCoeff g i z v v ≤ C * ‖v‖ ^ 2 := fun i => by
    obtain ⟨C, hC, W, hWo, hKW, hWt, -, hCW⟩ :=
      (hb i).continuousOn.exists_uniform_bilin_quadratic_bounds_nhds
        (isOpen_extChartAt_target _) (hK i) (hKt i)
        (fun z hz v hv => chartCoeff_pos g i hz hv)
    exact ⟨C, hC, W, hWo, hKW, hWt, hCW⟩
  choose C hC W hWo hKW hWt hCW using hbounds
  have hCpos : ∀ i, 0 < C i := fun i => zero_lt_one.trans_le (hC i)
  -- chartwise mollification (B7)
  have happrox : ∀ i, ∃ G : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ,
      (∀ k, ContDiff ℝ ∞ (G k)) ∧ (∀ k y v w, G k y v w = G k y w v) ∧
      (∀ k y v, (C i)⁻¹ * ‖v‖ ^ 2 ≤ G k y v v ∧ G k y v v ≤ C i * ‖v‖ ^ 2) ∧
      ∀ j, j ≤ 2 → TendstoUniformlyOn (fun k => iteratedFDeriv ℝ j (G k))
        (iteratedFDeriv ℝ j (chartCoeff g i)) atTop (K i) := fun i =>
    DifferentialGeometry.Analysis.exists_smooth_bilinear_approx_on_compact (hK i) (hWo i)
      (hKW i) 2 (((hb i).mono (subset_closure.trans (hWt i))).of_le (by norm_num))
      (fun z _ v w => chartCoeff_symm g i z v w) (C i)⁻¹ (C i)
      ((inv_le_one_of_one_le₀ (hC i)).trans (hC i))
      (fun z hz v => hCW i z (subset_closure hz) v)
  choose G₀ hG₀s hG₀symm hG₀b hG₀conv using happrox
  have hG₀conv' : ∀ i, MapCPConvergenceOn (K i) 2 (G₀ i) (chartCoeff g i) := fun i =>
    mapCPConvergenceOn_of_tendstoUniformlyOn (isOpen_extChartAt_target _) (hKt i)
      (fun k => (hG₀s i k).contDiffOn.of_le (by exact_mod_cast le_top)) (hb2 i)
      (fun j hj => hG₀conv i j hj)
  -- chartwise reindexing to a relative `C⁰` precision `1/(k+2)`
  have hidx : ∀ i (k : ℕ), ∃ m : ℕ, k ≤ m ∧ ∀ y ∈ K i,
      dist (chartCoeff g i y) (G₀ i m y) < 1 / ((k : ℝ) + 2) / C i := by
    intro i k
    have hu := Metric.tendstoUniformlyOn_iff.mp
      (tendstoUniformlyOn_of_cPConvergence ((hG₀conv' i).mono_order (Nat.zero_le 2)))
      (1 / ((k : ℝ) + 2) / C i) (by have := hCpos i; positivity)
    obtain ⟨m, hm1, hm2⟩ := ((eventually_ge_atTop k).and hu).exists
    exact ⟨m, hm1, hm2⟩
  choose N hNk hN using hidx
  let G : M → ℕ → E → E →L[ℝ] E →L[ℝ] ℝ := fun i k => G₀ i (N i k)
  have hGconv : ∀ i, MapCPConvergenceOn (K i) 2 (G i) (chartCoeff g i) := fun i =>
    (hG₀conv' i).comp_tendsto_atTop (tendsto_atTop_mono (hNk i) tendsto_id)
  -- gluing
  have hglue : ∀ k : ℕ, ∃ h : SmoothRiemannianMetric I M, ∀ x (v w : TangentSpace I x),
      h.inner x v w = ∑ᶠ i, ρ i x * G i k (extChartAt I i x)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I i) x v)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I i) x w) := fun k =>
    exists_smoothMetric_glued_finsum (fun j : M => j) ρ hρsub (fun i => G i k)
      (fun i => hG₀s i (N i k)) (fun i => hG₀symm i (N i k))
      (fun i y v hv => lt_of_lt_of_le
        (mul_pos (inv_pos.2 (hCpos i)) (pow_pos (norm_pos_iff.2 hv) 2)) (hG₀b i (N i k) y v).1)
  choose gSeq hgSeq using hglue
  have hfin : ∀ x : M, (support fun i => ρ i x).Finite := fun x =>
    (ρ.locallyFinite.point_finite x).subset fun i hi => hi
  refine ⟨gSeq, ?_, ?_⟩
  · -- bilipschitz bounds
    intro k x w
    set η : ℝ := 1 / ((k : ℝ) + 2) with hη
    have hη0 : 0 < η := by positivity
    have hη1 : η ≤ 1 := by
      rw [hη, div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    let s : Finset M := (hfin x).toFinset
    let D : M → E →L[ℝ] E := fun i => mfderiv I 𝓘(ℝ, E) (extChartAt I i) x
    have hsupp : ∀ (F : M → ℝ), (∀ i, ρ i x = 0 → F i = 0) → support F ⊆ s := by
      intro F hF i hi
      rw [Finite.coe_toFinset]
      intro h0
      exact hi (hF i h0)
    have hgk : (gSeq k).inner x w w = ∑ i ∈ s, ρ i x * G i k (extChartAt I i x) (D i w) (D i w) := by
      rw [hgSeq k x w w]
      exact finsum_eq_sum_of_support_subset _ (hsupp _ fun i h0 => by rw [h0, zero_mul])
    have hg : g.inner x w w =
        ∑ i ∈ s, ρ i x * chartCoeff g i (extChartAt I i x) (D i w) (D i w) := by
      have h1 : g.inner x w w = ∑ i ∈ s, ρ i x * g.inner x w w := by
        rw [← Finset.sum_mul, ← finsum_eq_sum_of_support_subset _ (hsupp _ fun i h0 => h0),
          ρ.sum_eq_one (mem_univ x), one_mul]
      rw [h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : ρ i x = 0
      · rw [hi, zero_mul, zero_mul]
      · exact congrArg (ρ i x * ·)
          (chartCoeff_mfderiv g i (hρs i (subset_tsupport _ (mem_support.mpr hi))) w w).symm
    have hterm : ∀ i, |ρ i x * G i k (extChartAt I i x) (D i w) (D i w) -
        ρ i x * chartCoeff g i (extChartAt I i x) (D i w) (D i w)| ≤
        η * (ρ i x * chartCoeff g i (extChartAt I i x) (D i w) (D i w)) := by
      intro i
      by_cases hi : ρ i x = 0
      · simp [hi]
      have hxt : x ∈ tsupport (ρ i) := subset_tsupport _ (mem_support.mpr hi)
      have hyK : extChartAt I i x ∈ K i := ⟨x, hxt, rfl⟩
      set y := extChartAt I i x
      set v := D i w
      have hd := hN i k y hyK
      rw [dist_comm, dist_eq_norm] at hd
      have hlowc := (hCW i y (subset_closure (hKW i hyK)) v).1
      have hop : |G i k y v v - chartCoeff g i y v v| ≤ η / C i * ‖v‖ ^ 2 := by
        have h1 : G i k y v v - chartCoeff g i y v v = (G i k y - chartCoeff g i y) v v := by
          simp only [_root_.sub_apply]
        rw [h1, ← Real.norm_eq_abs]
        calc ‖(G i k y - chartCoeff g i y) v v‖
            ≤ ‖G i k y - chartCoeff g i y‖ * ‖v‖ * ‖v‖ := (G i k y - chartCoeff g i y).le_opNorm₂ v v
          _ = ‖G i k y - chartCoeff g i y‖ * ‖v‖ ^ 2 := by ring
          _ ≤ η / C i * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right hd.le (sq_nonneg _)
      have hrel : η / C i * ‖v‖ ^ 2 ≤ η * chartCoeff g i y v v := by
        have hCi := hCpos i
        have : ‖v‖ ^ 2 ≤ C i * chartCoeff g i y v v := by
          have h2 := mul_le_mul_of_nonneg_left hlowc hCi.le
          rwa [← mul_assoc, mul_inv_cancel₀ hCi.ne', one_mul] at h2
        calc η / C i * ‖v‖ ^ 2 ≤ η / C i * (C i * chartCoeff g i y v v) :=
              mul_le_mul_of_nonneg_left this (by positivity)
          _ = η * chartCoeff g i y v v := by field_simp
      rw [← mul_sub, abs_mul, abs_of_nonneg (ρ.nonneg i x), mul_left_comm]
      exact mul_le_mul_of_nonneg_left (hop.trans hrel) (ρ.nonneg i x)
    have hlow : (1 - η) * g.inner x w w ≤ (gSeq k).inner x w w := by
      rw [hgk, hg, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have := hterm i
      have := neg_abs_le (ρ i x * G i k (extChartAt I i x) (D i w) (D i w) -
        ρ i x * chartCoeff g i (extChartAt I i x) (D i w) (D i w))
      linarith
    have hup : (gSeq k).inner x w w ≤ (1 + η) * g.inner x w w := by
      rw [hgk, hg, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have := hterm i
      have := le_abs_self (ρ i x * G i k (extChartAt I i x) (D i w) (D i w) -
        ρ i x * chartCoeff g i (extChartAt I i x) (D i w) (D i w))
      linarith
    have hgnn : 0 ≤ g.inner x w w := by
      by_cases hw : w = 0
      · simp [hw]
      · exact (g.pos x w hw).le
    constructor
    · refine le_trans (mul_le_mul_of_nonneg_right ?_ hgnn) hlow
      nlinarith
    · refine hup.trans (mul_le_mul_of_nonneg_right ?_ hgnn)
      nlinarith
  · -- chart `C²` convergence on compact subsets of chart targets
    intro q L hL hLt
    obtain ⟨L', hL'c, hLL', hL't⟩ := exists_compact_between hL (isOpen_extChartAt_target q) hLt
    have hS : IsCompact ((extChartAt I q).symm '' L') :=
      hL'c.image_of_continuousOn ((continuousOn_extChartAt_symm q).mono hL't)
    let F : Finset M := (ρ.locallyFinite.finite_nonempty_inter_compact hS).toFinset
    set V : Set E := interior L' with hVdef
    have hVo : IsOpen V := isOpen_interior
    have hVt : V ⊆ (extChartAt I q).target := interior_subset.trans hL't
    have hzero : ∀ y ∈ V, ∀ i, i ∉ F → ρ i ((extChartAt I q).symm y) = 0 := by
      intro y hy i hi
      by_contra hne
      apply hi
      rw [Finite.mem_toFinset]
      exact ⟨(extChartAt I q).symm y, mem_support.mpr hne, y, interior_subset hy, rfl⟩
    have hsum : ∀ y ∈ V, ∑ i ∈ F, ρ i ((extChartAt I q).symm y) = 1 := by
      intro y hy
      rw [← finsum_eq_sum_of_support_subset _ (fun i hi => by
        by_contra hiF
        exact (mem_support.mp hi) (hzero y hy i hiF)), ρ.sum_eq_one (mem_univ _)]
    have hglued : ∀ (k : ℕ), EqOn (chartCoeff (gSeq k) q)
        (fun y => ∑ i ∈ F, ρ i ((extChartAt I q).symm y) •
          pullbackForm (G i k (chartTransition (I := I) i q y),
            fderiv ℝ (chartTransition (I := I) i q) y)) V := by
      intro k y hy
      refine chartCoeff_eq_finset_sum_of_inner F (fun j : M => j) (fun i => ρ i) hρs
        (fun i => G i k) (gSeq k) q (hVt hy) fun v w => ?_
      rw [hgSeq k]
      exact finsum_eq_sum_of_support_subset _ fun i hi => by
        by_contra hiF
        exact (mem_support.mp hi) (by rw [hzero y hy i hiF, zero_mul])
    have hlimit : EqOn (chartCoeff g q)
        (fun y => ∑ i ∈ F, ρ i ((extChartAt I q).symm y) •
          pullbackForm (chartCoeff g i (chartTransition (I := I) i q y),
            fderiv ℝ (chartTransition (I := I) i q) y)) V := fun y hy =>
      chartCoeff_eq_finset_sum_transition g F (fun j : M => j) (fun i => ρ i) hρs q (hVt hy)
        (hsum y hy)
    refine (MapCPConvergenceOn.sum_of_contDiffOn F hVo (hLL'.trans subset_rfl)
      (Φ := fun i k y => ρ i ((extChartAt I q).symm y) •
        pullbackForm (G i k (chartTransition (I := I) i q y),
          fderiv ℝ (chartTransition (I := I) i q) y))
      (Φinf := fun i y => ρ i ((extChartAt I q).symm y) •
        pullbackForm (chartCoeff g i (chartTransition (I := I) i q y),
          fderiv ℝ (chartTransition (I := I) i q) y))
      (fun i _ => mapCPConvergenceOn_transitionTerm i q (ρ i).contMDiff (hρs i) hL hLt
        (fun k => (hG₀s i (N i k)).contDiffOn.of_le (by exact_mod_cast le_top)) (hb2 i)
        (hGconv i))
      (fun i _ k => (contDiffOn_transitionTerm i q (ρ i).contMDiff (hρs i)
        ((hG₀s i (N i k)).contDiffOn.of_le (by exact_mod_cast le_top))).mono hVt)
      (fun i _ => (contDiffOn_transitionTerm i q (ρ i).contMDiff (hρs i) (hb2 i)).mono hVt)).congr
      hVo hLL' hglued hlimit

/-- **CM5.a (frozen form).** On a σ-compact manifold with a boundaryless model, a `C^n` metric
`g`, `2 ≤ n`, is approximated by smooth metrics that are `(1 ± 1/(k+2))`-bilipschitz to `g`
everywhere and whose sectional curvature is eventually `≥ κ - ε` on every compact set `C` on which
the finite-order sectional curvature of `g` is `≥ κ`. -/
theorem exists_smooth_approximants_sigmaCompact {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (hn : (2 : ℕ∞ω) ≤ n) :
    ∃ gSeq : ℕ → SmoothRiemannianMetric I M,
      (∀ (k : ℕ) (x : M) (w : TangentSpace I x),
        (1 - 1 / ((k : ℝ) + 2)) ^ 2 * g.inner x w w ≤ (gSeq k).inner x w w ∧
          (gSeq k).inner x w w ≤ (1 + 1 / ((k : ℝ) + 2)) ^ 2 * g.inner x w w) ∧
      ∀ (C : Set M), IsCompact C → ∀ (κ ε : ℝ), 0 < ε →
        (∀ x ∈ C, ∀ v w : TangentSpace I x, κ ≤ g.sectionalCurvature x v w) →
        ∀ᶠ k in atTop, ∀ x ∈ C,
          DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelowAt (gSeq k) x (κ - ε) := by
  obtain ⟨gSeq, hbil, hconv⟩ := exists_smooth_approximants_sigmaCompact_chart g hn
  exact ⟨gSeq, hbil, fun C hC κ ε hε hsec =>
    eventually_sectionalBoundedBelowAt_of_chartCoeff_tendsto g hn gSeq hconv hC hε hsec⟩

end DifferentialGeometry.Geometry.MetricSmoothing
