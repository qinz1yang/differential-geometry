import DifferentialGeometry.Geometry.Comparison.FiniteMetric.MinimizingDirections
import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.Finite.ChartMetric
import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.ChartMetric

/-!
# A uniform model collar from strict point-directions for a finite-order metric (LC49′, B6)

Finite-order twin of LC49 (`exists_uniform_collar_of_strict_point_directions_of_radius`,
SublevelCore/UniformCollar.lean), for the limit metric `G` of class `C^{r+1}` (`2 ≤ r`) of LFR14 /
LC50′, with the direction sets `G.finiteMinimizingDirectionsTo {n} q` (CM3). Lane F8-NEW2, task 4.

* `exists_subseq_tendsto_unit_finite`: `G`-unit vectors over a compact set have a subsequence
  converging in `TN` to a `G`-unit vector (one trivialization at the limit base point and the chart
  comparison `eventually_finite_chart_metric_comparison`).
* `exists_uniform_collar_of_strict_point_directions_finite` (**B6 = LC49′**): strict negativity
  of `G(V, v)` on a compact `C₀ ⊆ B(n, R) ∖ {n}` against every limit minimizing direction to `n`
  gives a margin `-2α`, a bound `B` and an open collar `U ⊇ C₀` with compact closure in
  `(B(n, R) ∖ {n}) ∩ O`.
* `exists_uniform_collar_of_frontier_finite`: the LC51 shape (`C₀ = ∂D`,
  `B̄(n, 1/2) ⊆ int D`, `D ⊆ B(n, 2)`, radius `3`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

/-- **Unit compactness for a finite-order metric.** `G`-unit vectors over a compact set of base
points have a subsequence converging in `TN`; the limit lies over the set and is `G`-unit. -/
theorem exists_subseq_tendsto_unit_finite {m : ℕ∞ω}
    (G : ContMDiffRiemannianMetric I m E (TangentSpace I : N → Type _))
    {C : Set N} (hC : IsCompact C) (x : ℕ → N) (hx : ∀ k, x k ∈ C)
    (u : ∀ k, TangentSpace I (x k)) (hu : ∀ k, G.inner (x k) (u k) (u k) = 1) :
    ∃ v : TangentBundle I N, v.proj ∈ C ∧ G.inner v.proj v.snd v.snd = 1 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun k => (⟨x (φ k), u (φ k)⟩ : TangentBundle I N)) atTop (𝓝 v) := by
  obtain ⟨b, hbC, σ₁, hσ₁, hx₁⟩ := hC.tendsto_subseq hx
  set T := trivializationAt E (TangentSpace I) b with hT
  have hev : ∀ᶠ k in atTop, x (σ₁ k) ∈ (chartAt H b).source ∧ ∀ w : E,
      G.inner b w w ≤ 2 * G.inner (x (σ₁ k)) (T.symmL ℝ (x (σ₁ k)) w) (T.symmL ℝ (x (σ₁ k)) w) := by
    filter_upwards [hx₁ (eventually_finite_chart_metric_comparison G b (κ := 2) (by norm_num))]
      with k hk
    exact ⟨hk.1, fun w => (hk.2 w).1⟩
  set w : ℕ → E := fun k => T.continuousLinearMapAt ℝ (x (σ₁ k)) (u (σ₁ k)) with hw
  have hsymm : ∀ k, x (σ₁ k) ∈ (chartAt H b).source →
      T.symmL ℝ (x (σ₁ k)) (w k) = u (σ₁ k) := by
    intro k hk
    have hk' : x (σ₁ k) ∈ T.baseSet := by
      rw [hT, TangentBundle.trivializationAt_baseSet]
      exact hk
    exact T.symmL_continuousLinearMapAt (R := ℝ) hk' (u (σ₁ k))
  obtain ⟨c, hc, hcN⟩ := exists_mul_norm_le_finiteMetricSeminormAt G b
  have hbound : ∀ᶠ k in atTop, w k ∈ closedBall (0 : E) (Real.sqrt 2 / c) := by
    filter_upwards [hev] with k hk
    have h1 := hk.2 (w k)
    rw [hsymm k hk.1, hu] at h1
    have h3 : finiteMetricSeminormAt G b (w k) ≤ Real.sqrt 2 := by
      rw [finiteMetricSeminormAt_apply]
      exact Real.sqrt_le_sqrt (by linarith)
    have h2 := hcN (w k)
    rw [mem_closedBall_zero_iff, le_div_iff₀ hc]
    linarith
  obtain ⟨w₀, -, σ₂, hσ₂, hw₂⟩ :=
    (isCompact_closedBall (0 : E) (Real.sqrt 2 / c)).tendsto_subseq' hbound.frequently
  have hσ₂t := hσ₂.tendsto_atTop
  have hpair : Tendsto (fun k => (x (σ₁ (σ₂ k)), w (σ₂ k))) atTop (𝓝 (b, w₀)) :=
    (hx₁.comp hσ₂t).prodMk_nhds hw₂
  have hcont := (continuousOn_trivializationAt_symm (I := I) b).continuousAt (x := (b, w₀))
    (prod_mem_nhds ((chartAt H b).open_source.mem_nhds (mem_chart_source H b)) univ_mem)
  have hlim := hcont.tendsto.comp hpair
  have hconv : Tendsto (fun k => (⟨x (σ₁ (σ₂ k)), u (σ₁ (σ₂ k))⟩ : TangentBundle I N)) atTop
      (𝓝 (⟨b, T.symmL ℝ b w₀⟩ : TangentBundle I N)) := by
    refine hlim.congr' ?_
    filter_upwards [hσ₂t.eventually hev] with k hk
    exact congrArg (TotalSpace.mk (x (σ₁ (σ₂ k)))) (hsymm (σ₂ k) hk.1)
  refine ⟨⟨b, T.symmL ℝ b w₀⟩, hbC, ?_, σ₁ ∘ σ₂, hσ₁.comp hσ₂, hconv⟩
  have hinner : Continuous (fun q : TangentBundle I N => G.inner q.proj q.snd q.snd) :=
    continuousOn_univ.mp (continuousOn_finiteInner_of_bundle (g := G)
      (b := fun q : TangentBundle I N => q.proj) (v := fun q => q.snd) (w := fun q => q.snd)
      continuousOn_id continuousOn_id)
  exact tendsto_nhds_unique ((hinner.tendsto _).comp hconv)
    (tendsto_const_nhds.congr fun k => (hu _).symm)

variable [I.Boundaryless] [ProperSpace N]
  [RiemannianBundle (fun x : N => TangentSpace I x)] [IsRiemannianManifold I N]

/-- **B6 = LC49′ (finite-order limit metric).** A strict pairing of `V` with every limit minimizing
direction toward `n`, along a compact `C₀ ⊆ B(n, R) ∖ {n}`, gives a uniform margin `-2α`, a norm
bound `B` and an open collar `U` with compact closure inside `(B(n, R) ∖ {n}) ∩ O`. -/
theorem exists_uniform_collar_of_strict_point_directions_finite {r : ℕ∞} (hr : 2 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (hGnorm : ∀ (x : N) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (n : N) {R : ℝ} {C₀ O : Set N} (hC₀ : IsCompact C₀) (hC₀n : C₀ ⊆ ball n R \ {n})
    (hO : IsOpen O) (hC₀O : C₀ ⊆ O) (V : (y : N) → TangentSpace I y)
    (hV : ContinuousOn (fun y => (⟨y, V y⟩ : TangentBundle I N)) O)
    (hneg : ∀ q ∈ C₀, ∀ v ∈ G.finiteMinimizingDirectionsTo {n} q, G.inner q (V q) v < 0) :
    ∃ α B : ℝ, 0 < α ∧ 0 < B ∧ ∃ U : Set N, IsOpen U ∧ C₀ ⊆ U ∧ IsCompact (closure U) ∧
      closure U ⊆ (ball n R \ {n}) ∩ O ∧
      ∀ q ∈ closure U, G.inner q (V q) (V q) ≤ B ^ 2 ∧
        ∀ v ∈ G.finiteMinimizingDirectionsTo {n} q, G.inner q (V q) v ≤ -(2 * α) := by
  classical
  set W : Set N := (ball n R \ {n}) ∩ O with hWdef
  have hWopen : IsOpen W := (isOpen_ball.sdiff isClosed_singleton).inter hO
  have hC₀W : C₀ ⊆ W := fun q hq => ⟨hC₀n hq, hC₀O hq⟩
  obtain ⟨δ, hδ, hδW⟩ := hC₀.exists_cthickening_subset_open hWopen hC₀W
  have hK : IsCompact (cthickening δ C₀) := hC₀.cthickening
  have hKO : cthickening δ C₀ ⊆ O := fun q hq => (hδW hq).2
  have hnormK : ContinuousOn (fun q => G.inner q (V q) (V q)) (cthickening δ C₀) :=
    (continuousOn_finiteInner_of_bundle (g := G) (b := id) hV hV).mono hKO
  obtain ⟨Cb, hCb⟩ := hK.bddAbove_image hnormK
  set B : ℝ := max Cb 0 + 1 with hBdef
  have hB1 : 1 ≤ B := by simp only [hBdef]; linarith [le_max_right Cb 0]
  have hproj := FiberBundle.continuous_proj E (TangentSpace I : N → Type _)
  have hmargin : ∃ α : ℝ, 0 < α ∧ ∃ δ' : ℝ, 0 < δ' ∧ δ' < δ ∧
      ∀ q ∈ cthickening δ' C₀, ∀ v ∈ G.finiteMinimizingDirectionsTo {n} q,
        G.inner q (V q) v ≤ -(2 * α) := by
    by_contra hcon
    push Not at hcon
    have hseq : ∀ k : ℕ, ∃ q ∈ cthickening (δ / ((k : ℝ) + 2)) C₀,
        ∃ v ∈ G.finiteMinimizingDirectionsTo {n} q,
          -(2 * (1 / ((k : ℝ) + 1))) < G.inner q (V q) v := by
      intro k
      have hk2 : (1 : ℝ) < (k : ℝ) + 2 := by
        have := Nat.cast_nonneg (α := ℝ) k
        linarith
      exact hcon (1 / ((k : ℝ) + 1)) (by positivity) (δ / ((k : ℝ) + 2)) (by positivity)
        (div_lt_self hδ hk2)
    choose q hq v hv hlt using hseq
    have hqK : ∀ k, q k ∈ cthickening δ C₀ := fun k =>
      cthickening_mono (div_le_self hδ.le (by have := Nat.cast_nonneg (α := ℝ) k; linarith)) C₀
        (hq k)
    obtain ⟨p, -, -, φ, hφ, hlim⟩ :=
      exists_subseq_tendsto_unit_finite G hK q hqK v (fun k => (hv k).1)
    have hφt := hφ.tendsto_atTop
    have hqlim : Tendsto (fun k => q (φ k)) atTop (𝓝 p.proj) := (hproj.tendsto p).comp hlim
    have hδlim : Tendsto (fun k : ℕ => δ / ((k : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    have hpC₀ : p.proj ∈ C₀ := by
      rw [← hC₀.isClosed.closure_eq, closure_eq_iInter_cthickening]
      refine mem_iInter₂.mpr fun ε hε => ?_
      apply isClosed_cthickening.mem_of_tendsto hqlim
      filter_upwards [(hδlim.comp hφt).eventually (ge_mem_nhds hε)] with k hk
      exact cthickening_mono hk C₀ (hq (φ k))
    have hpdir : p.snd ∈ G.finiteMinimizingDirectionsTo {n} p.proj :=
      Bundle.ContMDiffRiemannianMetric.mem_finiteMinimizingDirectionsTo_of_tendsto G hr hGnorm
        isClosed_singleton (p := fun k => (⟨q (φ k), v (φ k)⟩ : TangentBundle I N))
        (fun k => hv (φ k)) hlim
    have hpairCont : ContinuousOn
        (fun z : TangentBundle I N => G.inner z.proj (V z.proj) z.snd)
        (TotalSpace.proj ⁻¹' O) :=
      continuousOn_finiteInner_of_bundle (g := G) (b := fun z : TangentBundle I N => z.proj)
        (v := fun z => V z.proj) (w := fun z => z.snd)
        (hV.comp hproj.continuousOn fun _ hz => hz) continuousOn_id
    have hpO : p.proj ∈ O := hC₀O hpC₀
    have hlimpair : Tendsto (fun k => G.inner (q (φ k)) (V (q (φ k))) (v (φ k))) atTop
        (𝓝 (G.inner p.proj (V p.proj) p.snd)) :=
      (hpairCont.continuousAt ((hO.preimage hproj).mem_nhds hpO)).tendsto.comp hlim
    have hlow : Tendsto (fun k => -(2 * (1 / ((φ k : ℝ) + 1)))) atTop (𝓝 0) := by
      have h := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2).neg.comp hφt
      rw [mul_zero, neg_zero] at h
      exact h
    have h0 : 0 ≤ G.inner p.proj (V p.proj) p.snd :=
      le_of_tendsto_of_tendsto' hlow hlimpair fun k => (hlt (φ k)).le
    exact absurd (hneg p.proj hpC₀ p.snd hpdir) (not_lt.mpr h0)
  obtain ⟨α, hα, δ', hδ', hδ'δ, hmarg⟩ := hmargin
  have hclU : closure (thickening δ' C₀) ⊆ cthickening δ' C₀ :=
    closure_thickening_subset_cthickening δ' C₀
  have hδ'K : cthickening δ' C₀ ⊆ cthickening δ C₀ := cthickening_mono hδ'δ.le C₀
  refine ⟨α, B, hα, by linarith, thickening δ' C₀, isOpen_thickening,
    self_subset_thickening hδ' C₀, hK.of_isClosed_subset isClosed_closure (hclU.trans hδ'K),
    fun q hq => hδW (hδ'K (hclU hq)), fun q hq => ⟨?_, hmarg q (hclU hq)⟩⟩
  have hle : G.inner q (V q) (V q) ≤ Cb := hCb ⟨q, hδ'K (hclU hq), rfl⟩
  have hCB : Cb < B := by simp only [hBdef]; linarith [le_max_left Cb 0]
  nlinarith

/-- **LC49′ in LC51's shape.** For a compact model core `D` with `B̄(n, 1/2) ⊆ int D` and
`D ⊆ B(n, 2)`, strict negativity on `∂D` gives the collar around `∂D` inside `B(n, 3) ∖ {n}`. -/
theorem exists_uniform_collar_of_frontier_finite {r : ℕ∞} (hr : 2 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (hGnorm : ∀ (x : N) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (n : N) {D : Set N} (hDc : IsCompact D) (hin : closedBall n (1 / 2) ⊆ interior D)
    (hout : D ⊆ ball n 2) {O : Set N} (hO : IsOpen O) (hDO : frontier D ⊆ O)
    (V : (x : N) → TangentSpace I x)
    (hV : ContinuousOn (fun x => (⟨x, V x⟩ : TangentBundle I N)) O)
    (hneg : ∀ x ∈ frontier D, ∀ v ∈ G.finiteMinimizingDirectionsTo {n} x,
      G.inner x (V x) v < 0) :
    ∃ α B : ℝ, 0 < α ∧ 0 < B ∧ ∃ U : Set N, IsOpen U ∧ frontier D ⊆ U ∧
      IsCompact (closure U) ∧ closure U ⊆ (ball n 3 \ {n}) ∩ O ∧
      ∀ q ∈ closure U, G.inner q (V q) (V q) ≤ B ^ 2 ∧
        ∀ v ∈ G.finiteMinimizingDirectionsTo {n} q, G.inner q (V q) v ≤ -(2 * α) := by
  have hfrD : frontier D ⊆ D := hDc.isClosed.frontier_subset
  have hnD : n ∉ frontier D := fun h =>
    h.2 (hin (mem_closedBall_self (by norm_num)))
  have hC₀n : frontier D ⊆ ball n 3 \ {n} := fun x hx =>
    ⟨ball_subset_ball (by norm_num) (hout (hfrD hx)),
      fun h => hnD (by rw [mem_singleton_iff] at h; rwa [← h])⟩
  exact exists_uniform_collar_of_strict_point_directions_finite hr G hGnorm n
    (hDc.of_isClosed_subset isClosed_frontier hfrD) hC₀n hO hDO V hV hneg

end DifferentialGeometry.Geometry.Collapse
