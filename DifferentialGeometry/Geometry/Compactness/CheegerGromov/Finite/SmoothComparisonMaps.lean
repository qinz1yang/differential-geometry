import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.ChartPullbackSequence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.ChartCoefficientTransfer
import DifferentialGeometry.Topology.Manifold.SmoothApproximation.SourceChartConvergence
import DifferentialGeometry.Geometry.Collapse.ComparisonImageContainment
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Basic
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Chart

/-!
# LFR48: smooth buffered comparison maps on the finite limit (binding)

Blueprint LFR48 (master207A.tex:29037–29094). The input is the output of LFR14 (T0,
`exists_finite_cheeger_gromov_limit`) for one subsequence, as explicit data: a proper smooth
carrier `N` with a `C^{K-1}` metric `G`, a base point `q`, and pointed `C^K` partial
diffeomorphisms `j i : N → X i` whose sources exhaust `N`, with `C^{K-1}` convergence of the
pulled-back metric coefficients in every extended chart and pointed distortion `→ 0` on balls.

* `exists_smooth_comparison_maps_of_finite_limit`: there are SMOOTH pointed partial
  diffeomorphisms `jt i` on buffered open sources (compact closure inside the source of `j i`),
  `C⁰`-close to `j i` within `1/(i+1)`, whose sources exhaust `N`, with the SAME `C^{K-1}`
  coefficient convergence to `G` in every extended chart, the same distortion control, and the
  strict-radius coverage `B(pᵢ, a) ⊆ jt i (B(q, b))` for `0 < a < b`.

Route (the blueprint's proof): for each `i`, T1 + T2
(`exists_smooth_partialDiffeomorph_seq_near_isCompact`) near the largest integral ball
`closedBall q (ρ i)` inside the source of `j i`; a countable family of charts `xs a` of `N`
(Lindelöf) and of pieces `closedBall (u l) (2/(r+1))` (a dense sequence `u`); T2b
(`eventually_mapsTo_and_mapCPConvergenceOn_chart_symm_comp`) on each piece; one diagonal index
`nn i` making the source coordinate change `A = φ ∘ j i⁻¹ ∘ jt i ∘ φ⁻¹` `1/(i+1)`-close to the
identity in `C^K` on the first `i` admissible pieces; T3
(`mapCPConvergenceOn_pullbackMetricCoefficients_comp_seq`) on each piece; the chart transfer
`mapCPConvergenceOn_chartCoeff_of_limit_charts` from the countable family to every chart; the
coverage from LFR10 (`eventually_riemannian_ball_subset_image_of_localDiffeomorph`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Metric Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.MetricSmoothing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {X : ℕ → Type*} [∀ i, MetricSpace (X i)] [∀ i, ChartedSpace E (X i)]
  [∀ i, IsManifold 𝓘(ℝ, E) ∞ (X i)] [∀ i, T2Space (TangentBundle 𝓘(ℝ, E) (X i))]
  [∀ i, SigmaCompactSpace (X i)] [∀ i, CompleteSpace (X i)]

/-- **LFR48 (binding on the output of LFR14).** -/
theorem exists_smooth_comparison_maps_of_finite_limit {K : ℕ} (hK : 1 ≤ K)
    (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, E) (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b)) (p : ∀ i, X i)
    {N : Type*} [MetricSpace N] [ProperSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N]
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E) ((K - 1 : ℕ) : ℕ∞ω) E
      (TangentSpace 𝓘(ℝ, E) : N → Type _))
    (q : N) (j : ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) N (X i) K)
    (hpt : ∀ i, q ∈ (j i).source ∧ j i q = p i)
    (hexh : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source)
    (hcoef : ∀ (x : N) (L : Set E), IsCompact L → L ⊆ (extChartAt 𝓘(ℝ, E) x).target →
      MapCPConvergenceOn L (K - 1)
        (fun i => pullbackMetricCoefficients (g i)
          ((j i : N → X i) ∘ (extChartAt 𝓘(ℝ, E) x).symm))
        (chartCoeff G x))
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (j i x) (j i y) - dist x y| < ε) :
    ∃ jt : ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) N (X i) ∞,
      (∀ i, q ∈ (jt i).source ∧ jt i q = p i) ∧
      (∀ i, IsCompact (closure (jt i).source) ∧ closure (jt i).source ⊆ (j i).source) ∧
      (∀ i, ∀ x ∈ (jt i).source, dist (jt i x) (j i x) < 1 / ((i : ℝ) + 1)) ∧
      (∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (jt i).source) ∧
      (∀ (x : N) (L : Set E), IsCompact L → L ⊆ (extChartAt 𝓘(ℝ, E) x).target →
        MapCPConvergenceOn L (K - 1)
          (fun i => pullbackMetricCoefficients (g i)
            ((jt i : N → X i) ∘ (extChartAt 𝓘(ℝ, E) x).symm))
          (chartCoeff G x)) ∧
      (∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
        |dist (jt i x) (jt i y) - dist x y| < ε) ∧
      (∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
        ball (p i) a ⊆ (jt i : N → X i) '' ball q b) := by
  classical
  have hKle : ((K : ℕ) : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hKK : K - 1 + 1 = K := by omega
  have : IsManifold 𝓘(ℝ, E) K N := IsManifold.of_le hKle
  -- Step A: the integral buffers `closedBall q (ρ i)` and the approximations of T1 + T2
  let ρ : ℕ → ℕ := fun i =>
    Nat.findGreatest (fun k : ℕ => closedBall q (k : ℝ) ⊆ (j i).source) i
  have hρsrc : ∀ i, closedBall q (ρ i : ℝ) ⊆ (j i).source := by
    intro i
    refine Nat.findGreatest_spec (P := fun k : ℕ => closedBall q (k : ℝ) ⊆ (j i).source)
      (Nat.zero_le i) ?_
    intro y hy
    have hyq : y = q := by simpa using hy
    rw [hyq]
    exact (hpt i).1
  have hρ : ∀ k : ℕ, ∀ᶠ i in atTop, k ≤ ρ i := by
    intro k
    filter_upwards [hexh _ (isCompact_closedBall q (k : ℝ)), eventually_ge_atTop k] with i hi hki
    exact Nat.le_findGreatest hki hi
  have hball : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ closedBall q (ρ i : ℝ) := by
    intro C hC
    obtain ⟨R, hR⟩ := hC.isBounded.subset_closedBall q
    filter_upwards [hρ ⌈R⌉₊] with i hi
    exact hR.trans (closedBall_subset_closedBall ((Nat.le_ceil R).trans (by exact_mod_cast hi)))
  have hpack := fun i =>
    Topology.Manifold.SmoothApproximation.exists_smooth_partialDiffeomorph_seq_near_isCompact
      (I := 𝓘(ℝ, E)) (J := 𝓘(ℝ, E)) hK (j i) (isCompact_closedBall q (ρ i : ℝ)) (hρsrc i)
      (mem_closedBall_self (Nat.cast_nonneg (ρ i)))
  choose O hO hCO hOc hOj hs hsm hspt hsun hsconv hsev using hpack
  -- Step B: a countable family of charts and a dense sequence of centres
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun x : N => (extChartAt 𝓘(ℝ, E) x).source) (fun x => isOpen_extChartAt_source x)
  have hTmem : ∀ y : N, ∃ x ∈ T, y ∈ (extChartAt 𝓘(ℝ, E) x).source := by
    intro y
    have hy : y ∈ ⋃ x ∈ T, (extChartAt 𝓘(ℝ, E) x).source := by
      rw [hTU]
      exact mem_iUnion.2 ⟨y, mem_extChartAt_source y⟩
    obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 hy
    exact ⟨x, hx, hyx⟩
  have hTne : T.Nonempty := by
    obtain ⟨x, hx, -⟩ := hTmem q
    exact ⟨x, hx⟩
  obtain ⟨xs, hxs⟩ := hTc.exists_eq_range hTne
  have hxcov : ∀ y : N, ∃ a, y ∈ (extChartAt 𝓘(ℝ, E) (xs a)).source := by
    intro y
    obtain ⟨x, hx, hyx⟩ := hTmem y
    rw [hxs] at hx
    obtain ⟨a, rfl⟩ := hx
    exact ⟨a, hyx⟩
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq E
  -- admissible pieces and the closeness condition on them
  let Adm : ℕ → ℕ → E → ℝ → Prop := fun i a c δ =>
    closedBall c (3 * δ) ⊆ (extChartAt 𝓘(ℝ, E) (xs a)).target ∧
      MapsTo (extChartAt 𝓘(ℝ, E) (xs a)).symm (closedBall c (2 * δ)) (O i)
  let Q : ℕ → ℕ → ℕ → E → ℝ → Prop := fun i n a c δ =>
    MapsTo (fun y => hs i n ((extChartAt 𝓘(ℝ, E) (xs a)).symm y)) (closedBall c (2 * δ))
        (j i).target ∧
      MapsTo (fun y => (j i).symm (hs i n ((extChartAt 𝓘(ℝ, E) (xs a)).symm y)))
        (closedBall c (2 * δ)) (extChartAt 𝓘(ℝ, E) (xs a)).source ∧
      ∀ r ≤ K, ∀ y ∈ closedBall c (2 * δ),
        mapDerivNorm r (fun y => extChartAt 𝓘(ℝ, E) (xs a)
          ((j i).symm (hs i n ((extChartAt 𝓘(ℝ, E) (xs a)).symm y)))) id y ≤ 1 / ((i : ℝ) + 1)
  have hQ : ∀ i a c δ, 0 < δ → Adm i a c δ → ∀ᶠ n in atTop, Q i n a c δ := by
    intro i a c δ hδ hadm
    have hL : IsCompact (closedBall c (2 * δ)) := isCompact_closedBall _ _
    have hLO : closedBall c (2 * δ) ⊆ (extChartAt 𝓘(ℝ, E) (xs a)).target ∩
        (extChartAt 𝓘(ℝ, E) (xs a)).symm ⁻¹' O i := fun y hy =>
      ⟨hadm.1 (closedBall_subset_closedBall (by linarith) hy), hadm.2 hy⟩
    obtain ⟨hcap, hcv⟩ :=
      Topology.Manifold.SmoothApproximation.eventually_mapsTo_and_mapCPConvergenceOn_chart_symm_comp
        le_rfl (j i) (hO i) (subset_closure.trans (hOj i)) (fun n => (hsm i n).of_le hKle)
        (fun p' q' K' hK' hKO hKm => hsconv i p' q' K' hK'
          (fun y hy => ⟨(hKO hy).1, subset_closure (hKO hy).2⟩) hKm)
        (xs a) hL hLO
    obtain ⟨k0, hk0⟩ := hcv (1 / ((i : ℝ) + 1)) (by positivity)
    filter_upwards [hcap, eventually_ge_atTop k0] with n hn hnk
    exact ⟨hn.1, hn.2, fun r hr y hy => hk0 n hnk r hr y hy⟩
  let pc : ℕ → ℕ × E × ℝ := fun t => ((Nat.unpair t).1, u (Nat.unpair (Nat.unpair t).2).1,
    1 / (((Nat.unpair (Nat.unpair t).2).2 : ℝ) + 1))
  have hpcpos : ∀ t, 0 < (pc t).2.2 := fun t => by
    simp only [pc]
    positivity
  have hpc : ∀ a l r : ℕ, pc (Nat.pair a (Nat.pair l r)) = (a, u l, 1 / ((r : ℝ) + 1)) := by
    intro a l r
    simp [pc, Nat.unpair_pair]
  -- Step C: the diagonal choice
  have hgood : ∀ i, ∀ᶠ n in atTop,
      (∃ d : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) N (X i) ∞,
        d.source = O i ∧ d.target = hs i n '' O i ∧ (d : N → X i) = hs i n) ∧
      (∀ x ∈ closure (O i), dist (hs i n x) (j i x) < 1 / ((i : ℝ) + 1)) ∧
      (∀ t ∈ Finset.range i, Adm i (pc t).1 (pc t).2.1 (pc t).2.2 →
        Q i n (pc t).1 (pc t).2.1 (pc t).2.2) := by
    intro i
    have h2 : ∀ᶠ n in atTop, ∀ x ∈ closure (O i), dist (hs i n x) (j i x) < 1 / ((i : ℝ) + 1) := by
      filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hsun i) _
        (by positivity : (0 : ℝ) < 1 / ((i : ℝ) + 1))] with n hn x hx
      rw [dist_comm]
      exact hn x hx
    have h3 : ∀ᶠ n in atTop, ∀ t ∈ Finset.range i, Adm i (pc t).1 (pc t).2.1 (pc t).2.2 →
        Q i n (pc t).1 (pc t).2.1 (pc t).2.2 := by
      refine (Filter.eventually_all_finset _).2 fun t _ => ?_
      by_cases ht : Adm i (pc t).1 (pc t).2.1 (pc t).2.2
      · exact (hQ i _ _ _ (hpcpos t) ht).mono fun n hn _ => hn
      · exact Eventually.of_forall fun n h => absurd h ht
    exact (hsev i).and (h2.and h3)
  choose nn hnn using fun i => (hgood i).exists
  choose d hdsrc hdtgt hdcoe using fun i => (hnn i).1
  have hdx : ∀ i x, d i x = hs i (nn i) x := fun i x => by rw [hdcoe i]
  have hdclose : ∀ i, ∀ x ∈ closure (O i), dist (d i x) (j i x) < 1 / ((i : ℝ) + 1) :=
    fun i x hx => by
      rw [hdx]
      exact (hnn i).2.1 x hx
  have hdsub : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (d i).source := fun C hC =>
    (hball C hC).mono fun i hi => by
      rw [hdsrc i]
      exact hi.trans (hCO i)
  have hdpt : ∀ i, q ∈ (d i).source ∧ d i q = p i := fun i =>
    ⟨by
      rw [hdsrc i]
      exact hCO i (mem_closedBall_self (Nat.cast_nonneg _)),
     by
      rw [hdx, hspt i (nn i)]
      exact (hpt i).2⟩
  -- distortion
  have hddist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (d i x) (d i y) - dist x y| < ε := by
    intro R ε hε
    obtain ⟨i0, hi0⟩ := exists_nat_one_div_lt (by positivity : (0 : ℝ) < ε / 4)
    filter_upwards [hdist R (ε / 2) (half_pos hε), hball _ (isCompact_closedBall q R),
      eventually_ge_atTop i0] with i hi hiR hii0 x hx y hy
    have hxC : x ∈ closure (O i) := subset_closure (hCO i (hiR (ball_subset_closedBall hx)))
    have hyC : y ∈ closure (O i) := subset_closure (hCO i (hiR (ball_subset_closedBall hy)))
    have h1 := hdclose i x hxC
    have h2 := hdclose i y hyC
    have hsmall : 1 / ((i : ℝ) + 1) ≤ 1 / ((i0 : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hii0 1)
    have h3 : |dist (d i x) (d i y) - dist (j i x) (j i y)| ≤
        dist (d i x) (j i x) + dist (d i y) (j i y) := by
      have h := dist_dist_dist_le (d i x) (d i y) (j i x) (j i y)
      rwa [Real.dist_eq] at h
    have h4 := hi x hx y hy
    calc |dist (d i x) (d i y) - dist x y|
        ≤ |dist (d i x) (d i y) - dist (j i x) (j i y)| + |dist (j i x) (j i y) - dist x y| :=
          abs_sub_le _ _ _
      _ < ε := by linarith
  -- coverage (LFR10)
  have hdcov : ∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
      ball (p i) a ⊆ (d i : N → X i) '' ball q b := by
    intro a b _ hab
    have hloc : ∀ᶠ i in atTop, IsLocalDiffeomorphOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (d i : N → X i)
        (ball q b) := by
      filter_upwards [hdsub _ (isCompact_closedBall q b)] with i hi
      intro x
      exact (d i).isLocalDiffeomorphAt _ _ _ (hi (ball_subset_closedBall x.2))
    exact Geometry.Metric.eventually_riemannian_ball_subset_image_of_localDiffeomorph g hmetric
      (fun i => (d i : N → X i)) q p (fun i => (hdpt i).2) hloc (fun η hη => hddist b η hη) hab
  -- Step D: coefficient convergence on one piece of one chart of the family
  have hpiece : ∀ a l r : ℕ,
      closedBall (u l) (3 * (1 / ((r : ℝ) + 1))) ⊆ (extChartAt 𝓘(ℝ, E) (xs a)).target →
      ∀ D : Set E, IsCompact D → D ⊆ ball (u l) (1 / ((r : ℝ) + 1)) →
      MapCPConvergenceOn D (K - 1)
        (fun i => pullbackMetricCoefficients (g i)
          ((d i : N → X i) ∘ (extChartAt 𝓘(ℝ, E) (xs a)).symm))
        (chartCoeff G (xs a)) := by
    intro a l r hval D hD hDb
    set c : E := u l with hc
    set δ : ℝ := 1 / ((r : ℝ) + 1) with hδ
    have hδpos : 0 < δ := by positivity
    set ψ := extChartAt 𝓘(ℝ, E) (xs a) with hψ
    have hcomp2 : IsCompact (ψ.symm '' closedBall c (2 * δ)) :=
      (isCompact_closedBall c (2 * δ)).image_of_continuousOn
        ((continuousOn_extChartAt_symm (xs a)).mono
          ((closedBall_subset_closedBall (by linarith)).trans hval))
    have hcomp3 : IsCompact (ψ.symm '' closedBall c (3 * δ)) :=
      (isCompact_closedBall c (3 * δ)).image_of_continuousOn
        ((continuousOn_extChartAt_symm (xs a)).mono hval)
    have hev : ∀ᶠ i in atTop, Adm i a c δ ∧ Q i (nn i) a c δ ∧ 1 / ((i : ℝ) + 1) < δ := by
      obtain ⟨i1, hi1⟩ := exists_nat_one_div_lt hδpos
      filter_upwards [hball _ hcomp2, eventually_gt_atTop (Nat.pair a (Nat.pair l r)),
        eventually_ge_atTop i1] with i hi hti hii1
      have hadm : Adm i a c δ :=
        ⟨hval, fun y hy => hCO i (hi ⟨y, hy, rfl⟩)⟩
      have h := (hnn i).2.2 (Nat.pair a (Nat.pair l r)) (Finset.mem_range.2 hti)
      rw [hpc a l r] at h
      refine ⟨hadm, h hadm, lt_of_le_of_lt ?_ hi1⟩
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hii1 1)
    let A : ℕ → E → E := fun i y => ψ ((j i).symm (hs i (nn i) (ψ.symm y)))
    have hDW : D ⊆ ball c (2 * δ) := hDb.trans (ball_subset_ball (by linarith))
    have hWV : ball c (2 * δ) ⊆ ball c (3 * δ) := ball_subset_ball (by linarith)
    have hf : ∀ᶠ i in atTop, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) (K - 1 + 1 : ℕ)
        ((j i : N → X i) ∘ ψ.symm) (ball c (3 * δ)) := by
      filter_upwards [hexh _ hcomp3] with i hi
      rw [hKK]
      exact (j i).contMDiffOn.comp ((contMDiffOn_extChartAt_symm (xs a)).mono
        (ball_subset_closedBall.trans hval)) fun y hy => hi ⟨y, ball_subset_closedBall hy, rfl⟩
    have hB : ContDiffOn ℝ (K - 1 : ℕ) (chartCoeff G (xs a)) (ball c (3 * δ)) :=
      (Bundle.ContMDiffRiemannianMetric.contDiffOn_pullback_inner G
        (r := ((K - 1 : ℕ) : ℕ∞ω)) (s := ((K : ℕ) : ℕ∞ω)) le_rfl
        (by exact_mod_cast hKK.le) (isOpen_extChartAt_target (xs a))
        (contMDiffOn_extChartAt_symm (xs a))).mono (ball_subset_closedBall.trans hval)
    have hconvV : ∀ S : Set E, IsCompact S → S ⊆ ball c (3 * δ) →
        MapCPConvergenceOn S (K - 1)
          (fun i => pullbackMetricCoefficients (g i) ((j i : N → X i) ∘ ψ.symm))
          (chartCoeff G (xs a)) := fun S hS hSV =>
      hcoef (xs a) S hS (hSV.trans (ball_subset_closedBall.trans hval))
    have hAc : ∀ᶠ i in atTop, ContDiffOn ℝ (K - 1 + 1 : ℕ) (A i) (ball c (2 * δ)) ∧
        MapsTo (A i) (ball c (2 * δ)) (ball c (3 * δ)) := by
      filter_upwards [hev] with i hi
      obtain ⟨hadm, ⟨hQ1, hQ2, hQ4⟩, hsmall⟩ := hi
      refine ⟨?_, ?_⟩
      · rw [hKK]
        have h1 : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) K (fun y => hs i (nn i) (ψ.symm y))
            (ball c (2 * δ)) :=
          ((hsm i (nn i)).of_le hKle).comp ((contMDiffOn_extChartAt_symm (xs a)).mono
            (ball_subset_closedBall.trans
              ((closedBall_subset_closedBall (by linarith)).trans hval)))
            fun y hy => hadm.2 (ball_subset_closedBall hy)
        have h2 : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) K
            (fun y => (j i).symm (hs i (nn i) (ψ.symm y))) (ball c (2 * δ)) :=
          (j i).symm.contMDiffOn.comp h1 fun y hy => hQ1 (ball_subset_closedBall hy)
        refine contMDiffOn_iff_contDiffOn.mp
          ((contMDiffOn_extChartAt (n := K) (x := xs a)).comp h2 ?_)
        intro y hy
        have h := hQ2 (ball_subset_closedBall hy)
        simp only [mem_preimage, extChartAt_source] at h ⊢
        exact h
      · intro y hy
        have h0 := hQ4 0 (Nat.zero_le K) y (ball_subset_closedBall hy)
        rw [mapDerivNorm, norm_iteratedFDeriv_zero] at h0
        rw [mem_ball] at hy ⊢
        have h5 : dist (A i y) y < δ := by
          rw [dist_eq_norm]
          exact lt_of_le_of_lt h0 hsmall
        calc dist (A i y) c ≤ dist (A i y) y + dist y c := dist_triangle _ _ _
          _ < δ + 2 * δ := add_lt_add h5 hy
          _ = 3 * δ := by ring
    have hA : MapCPConvergenceOn D (K - 1 + 1) A id := by
      intro ε hε
      obtain ⟨i1, hi1⟩ := exists_nat_one_div_lt hε
      obtain ⟨i0, hi0⟩ := eventually_atTop.mp (hev.and (eventually_ge_atTop i1))
      refine ⟨i0, fun i hi r' hr' y hy => ?_⟩
      obtain ⟨⟨_, ⟨_, _, hQ4⟩, _⟩, hii1⟩ := hi0 i hi
      refine (hQ4 r' (by omega) y (ball_subset_closedBall (hDW hy))).trans ?_
      refine le_trans ?_ hi1.le
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hii1 1)
    have hT3 := mapCPConvergenceOn_pullbackMetricCoefficients_comp_seq g (m := K - 1)
      (fun i => (j i : N → X i) ∘ ψ.symm) A isOpen_ball isOpen_ball hf (chartCoeff G (xs a))
      hB hconvV hD hDW hWV hAc hA
    refine hT3.congr_eventually isOpen_ball hDW ?_ (Set.eqOn_refl _ _)
    filter_upwards [hev] with i hi y hy
    obtain ⟨_, ⟨hQ1, hQ2, _⟩, _⟩ := hi
    apply pullbackMetricCoefficients_eq_of_eventuallyEq
    filter_upwards [isOpen_ball.mem_nhds hy] with z hz
    have hz1 := hQ1 (ball_subset_closedBall hz)
    have hz2 := hQ2 (ball_subset_closedBall hz)
    change d i (ψ.symm z) = j i (ψ.symm (ψ ((j i).symm (hs i (nn i) (ψ.symm z)))))
    rw [ψ.left_inv hz2,
      show j i ((j i).symm (hs i (nn i) (ψ.symm z))) = hs i (nn i) (ψ.symm z) from
        (j i).toPartialEquiv.right_inv hz1, hdx]
  -- Step E: transfer from the countable family to every chart
  let σ : ℕ → PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E N K := fun a =>
    (DifferentialGeometry.PartialDiffeomorph.extChartAt 𝓘(ℝ, E) K (xs a)).symm
  let jK : ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) N (X i) K := fun i =>
    DifferentialGeometry.PartialDiffeomorph.ofLE (d i) hKle
  have hcover : ∀ y : N, ∃ a, y ∈ (σ a).target := by
    intro y
    obtain ⟨a, ha⟩ := hxcov y
    exact ⟨a, ha⟩
  have hb : ∀ a, ContDiffOn ℝ (K - 1 : ℕ) (chartCoeff G (xs a)) (σ a).source := fun a =>
    Bundle.ContMDiffRiemannianMetric.contDiffOn_pullback_inner G
      (r := ((K - 1 : ℕ) : ℕ∞ω)) (s := ((K : ℕ) : ℕ∞ω)) le_rfl
      (by exact_mod_cast hKK.le) (isOpen_extChartAt_target (xs a))
      (contMDiffOn_extChartAt_symm (xs a))
  have hG : ∀ a, ∀ u' ∈ (σ a).source, ∀ v w : E,
      G.inner (σ a u') (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (σ a) u' v)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (σ a) u' w) = chartCoeff G (xs a) u' v w :=
    fun _ _ _ _ _ => rfl
  have hconvσ : ∀ a (S : Set E), IsCompact S → S ⊆ (σ a).source →
      MapCPConvergenceOn S (K - 1)
        (fun i => pullbackMetricCoefficients (g i) ((jK i : N → X i) ∘ σ a))
        (chartCoeff G (xs a)) := by
    intro a S hS hSt
    refine GC.MetricGeometry.mapCPConvergenceOn_of_isCompact_subset_sUnion
      (S := {V | ∃ l r : ℕ, closedBall (u l) (3 * (1 / ((r : ℝ) + 1))) ⊆
        (extChartAt 𝓘(ℝ, E) (xs a)).target ∧ V = ball (u l) (1 / ((r : ℝ) + 1))}) ?_ ?_ hS ?_
    · rintro _ ⟨l, r, -, rfl⟩
      exact isOpen_ball
    · rintro _ ⟨l, r, hval, rfl⟩ D hD hDV
      exact hpiece a l r hval D hD hDV
    · intro y hy
      have hyt : y ∈ (extChartAt 𝓘(ℝ, E) (xs a)).target := hSt hy
      obtain ⟨ε, hε, hεt⟩ := Metric.isOpen_iff.mp (isOpen_extChartAt_target (xs a)) y hyt
      obtain ⟨r, hr⟩ := exists_nat_one_div_lt (by positivity : (0 : ℝ) < ε / 4)
      obtain ⟨l, hl⟩ := hu.exists_dist_lt y (by positivity : (0 : ℝ) < 1 / ((r : ℝ) + 1))
      refine ⟨ball (u l) (1 / ((r : ℝ) + 1)), ⟨l, r, ?_, rfl⟩, ?_⟩
      · intro z hz
        apply hεt
        rw [mem_ball]
        rw [mem_closedBall] at hz
        calc dist z y ≤ dist z (u l) + dist (u l) y := dist_triangle _ _ _
          _ < ε := by
            rw [dist_comm (u l) y]
            linarith
      · rw [mem_ball]
        exact hl
  refine ⟨d, hdpt, fun i => ⟨by rw [hdsrc i]; exact hOc i, by rw [hdsrc i]; exact hOj i⟩,
    fun i x hx => hdclose i x (subset_closure (by rw [← hdsrc i]; exact hx)), hdsub, ?_,
    hddist, hdcov⟩
  intro x L hL hLt
  exact mapCPConvergenceOn_chartCoeff_of_limit_charts hK G g σ hcover
    (fun a => chartCoeff G (xs a)) hb hG jK hdsub hconvσ x hL hLt

end DifferentialGeometry.CheegerGromovCompactness
