import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimFibreTypeSequence

/-!
# LFR20 item 3 in sequence form (modulo LFR14 data)

Blueprint LFR20 (master207A:26358), item 3, with `L = 10⁶Δ`, `e = Δ/100`, `a = 9L/10`,
`b = 19L/20`, for LFR14's embeddings `j i` and slim charts `c i` (`f_i = η_i ∘ j_i`):
eventually,

1. `|f_i - t| < 2e` on the cylinder `{|t| ≤ b}`;
2. `∂_t f_i = d f_i(V) > 3/4` on the cylinder, and `dt(V) = 1`, so every straight interpolation
   `(1 - u) t + u f_i`, `u ∈ [0, 1]`, has derivative `> 3/4` along `V` (transverse);
3. every point of every source fibre over `[-a, a]` in `B(p i, L)` is `j i` of a point with
   `|t| < 0.93 L < b` (the image contains EVERY source fibre);
4. the inverse images of `[-a, a]` under every interpolation lie in `{|t| < a + 2e}`, inside the
   compact `Q = {|t| ≤ a + 3e} ⊂ {|t| < b}`.

`mvfderiv_splitting_fst_vertical`: `dt(V) = 1` for LFR18's vertical field.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Metric Bundle WithLp
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.MetricSmoothing
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.ExactSplitting
open GC.MetricGeometry

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

section Vertical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [RiemannianBundle (fun x : N => TangentSpace I x)] [IsRiemannianManifold I N]
  [CompleteSpace N] {r : ℕ∞} {W : Type*} [MetricSpace W]

/-- **`dt(V) = 1`.** The splitting coordinate has derivative one along LFR18's vertical field. -/
theorem mvfderiv_splitting_fst_vertical
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : N) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (Φ : N ≃ᵢ WithLp 2 (ℝ × W)) {ℓ : ℝ} (hℓ : 0 < ℓ) (V : ∀ x : N, TangentSpace I x)
    (hVdir : ∀ x, G.finiteMinimizingDirectionsTo
      {Φ.symm (toLp 2 ((Φ x).fst + ℓ, (Φ x).snd))} x = {V x}) (x : N) :
    mvfderiv I (fun y => (Φ y).fst) x (V x) = 1 := by
  obtain ⟨w, hw1, hdw, hline⟩ := exists_unit_line_expMap_forall G hr hnorm Φ x
    (u := (1 : ℝ)) (by simp)
  have hmem : (w : TangentSpace I x) ∈ G.finiteMinimizingDirectionsTo
      {Φ.symm (toLp 2 ((Φ x).fst + ℓ, (Φ x).snd))} x := by
    refine ⟨hw1, ?_⟩
    rw [infDist_singleton, dist_splitting_shift Φ x hℓ.le]
    erw [hline ℓ hℓ.le]
    rw [smul_eq_mul, mul_one]
    exact mem_singleton _
  rw [hVdir x] at hmem
  have hwV : (w : TangentSpace I x) = V x := hmem
  rw [← hwV]
  exact hdw

end Vertical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [ProperSpace N] [RiemannianBundle (fun x : N => TangentSpace I x)] [IsRiemannianManifold I N]
  {M : ℕ → Type*} [∀ i, MetricSpace (M i)] [∀ i, ChartedSpace H (M i)]
  [∀ i, IsManifold I ∞ (M i)] [∀ i, SigmaCompactSpace (M i)]
  [∀ i, RiemannianBundle (fun x : M i => TangentSpace I x)] [∀ i, IsRiemannianManifold I (M i)]
  [∀ i, CompleteSpace (M i)]
  [∀ i, IsContinuousRiemannianBundle E (fun x : M i => TangentSpace I x)]
  {W : Type*} [MetricSpace W]

/-- **LFR20 item 3, sequence form (modulo LFR14 data).** -/
theorem eventually_slimChart_model_embedding [CompactSpace W]
    {r : ℕ∞} (hr : 2 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (hGnorm : ∀ (x : N) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (g : ∀ i, SmoothRiemannianMetric I (M i)) (hEnorm : ∀ i, IsMetricNorm (g i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    {K : ℕ} (hK : 2 ≤ K) (q : N) (j : ∀ i, PartialDiffeomorph I I N (M i) K)
    (hexh : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source)
    (hconv : ∀ (x : N) (L : Set E), IsCompact L → L ⊆ (extChartAt I x).target →
      MapCPConvergenceOn L 1
        (fun i => pullbackMetricCoefficients (g i) ((j i : N → M i) ∘ (extChartAt I x).symm))
        (chartCoeff G x))
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (j i x) (j i y) - dist x y| < ε)
    (hcover : ∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
      ball (j i q) a ⊆ (j i : N → M i) '' ball q b)
    (Φ : N ≃ᵢ WithLp 2 (ℝ × W)) {Δ σ : ℝ} (hΔ : 1 ≤ Δ) (hσ : 0 < σ) (hσ1 : σ ≤ 1 / 100)
    (hD : ∀ a b : W, dist a b ≤ 10 ^ 3 * Δ)
    {Y : ℕ → Type*} [∀ i, MetricSpace (Y i)] {p : ∀ i, M i} {y₀ : ∀ i, Y i} {β : ℕ → ℝ}
    (α : ∀ i, KleinerLottApprox (p i) (WithLp.toLp 2 ((0 : ℝ), y₀ i)) (β i))
    (c : ∀ i, SlimChart (g i) (hEnorm i) Δ σ (α i)) (hpt : ∀ i, j i q = p i)
    (hU : ∀ C' : Set N, IsCompact C' →
      TendstoUniformlyOn (fun i x => ((α i).toFun (j i x)).fst) (fun x => (Φ x).fst) atTop C') :
    ∃ V : ∀ x : N, TangentSpace I x,
      (∀ x, G.finiteMinimizingDirectionsTo
        {Φ.symm (toLp 2 ((Φ x).fst + 2 * (10 ^ 6 * Δ), (Φ x).snd))} x = {V x}) ∧
      (∀ x, mvfderiv I (fun y => (Φ y).fst) x (V x) = 1) ∧
      ∀ᶠ i in atTop,
        (∀ x, |(Φ x).fst| ≤ 95 / 100 * (10 ^ 6 * Δ) →
          j i x ∈ ball (p i) (10 ^ 6 * Δ) ∧ |(c i).coord (j i x) - (Φ x).fst| < 2 * (Δ / 100) ∧
          3 / 4 < mvfderiv I (fun y => (c i).coord (j i y)) x (V x) ∧
          ∀ u ∈ Icc (0 : ℝ) 1,
            3 / 4 < (1 - u) * 1 + u * mvfderiv I (fun y => (c i).coord (j i y)) x (V x) ∧
            (|(1 - u) * (Φ x).fst + u * (c i).coord (j i x)| ≤ 9 / 10 * (10 ^ 6 * Δ) →
              |(Φ x).fst| < 9 / 10 * (10 ^ 6 * Δ) + 2 * (Δ / 100))) ∧
        ∀ y ∈ ball (p i) (10 ^ 6 * Δ), |(c i).coord y| ≤ 9 / 10 * (10 ^ 6 * Δ) →
          ∃ x, |(Φ x).fst| < 93 / 100 * (10 ^ 6 * Δ) ∧ j i x = y := by
  have hΔ0 : 0 < Δ := by linarith
  set L : ℝ := 10 ^ 6 * Δ with hLdef
  have hL : 0 < L := by positivity
  set b : ℝ := 95 / 100 * L with hbdef
  set ℓ : ℝ := 2 * L with hℓdef
  have hℓ : 0 < ℓ := by positivity
  let sh : N → N := fun x => Φ.symm (toLp 2 ((Φ x).fst + ℓ, (Φ x).snd))
  have hshfst : ∀ x, (Φ (sh x)).fst = (Φ x).fst + ℓ := by
    intro x
    change (Φ (Φ.symm (toLp 2 ((Φ x).fst + ℓ, (Φ x).snd)))).fst = _
    rw [Φ.apply_symm_apply]
    rfl
  have hq0 : (Φ q).fst = 0 := by
    have h := (hU {q} isCompact_singleton).tendsto_at (mem_singleton q)
    have h0 : (fun i => ((α i).toFun (j i q)).fst) = fun _ => (0 : ℝ) := by
      funext i
      rw [hpt i, (α i).basepoint]
      rfl
    rw [h0] at h
    exact (tendsto_nhds_unique tendsto_const_nhds h).symm
  set Cyl : Set N := {x | |(Φ x).fst| ≤ b} with hCyldef
  have hCyl : IsCompact Cyl := isCompact_splitting_cylinder Φ b
  have hDb : ∀ x ∈ Cyl, dist x q < 96 / 100 * L := by
    intro x hx
    refine (dist_le_of_splitting hD Φ hq0 hx).trans_lt ?_
    rw [Real.sqrt_lt' (by positivity)]
    nlinarith
  have hDsh : ∀ x ∈ Cyl, dist (sh x) q < 3 * L := by
    intro x hx
    have hx' : |(Φ (sh x)).fst| ≤ b + ℓ := by
      rw [hshfst]
      exact (abs_add_le _ _).trans (by rw [abs_of_pos hℓ]; linarith [show |(Φ x).fst| ≤ b from hx])
    refine (dist_le_of_splitting hD Φ hq0 hx').trans_lt ?_
    rw [Real.sqrt_lt' (by positivity)]
    nlinarith
  have hshd : ∀ x, dist x (sh x) = ℓ := fun x => dist_splitting_shift Φ x hℓ.le
  obtain ⟨V, hVdir, hVcont, -⟩ := exists_vertical_field_eventually_inverse_directions_close hr G
    hGnorm g hmetric hK q j hexh hconv hdist hcover Φ hℓ hCyl
  have hball : ∀ᶠ i in atTop, ∀ x ∈ Cyl, j i x ∈ ball (p i) L ∧ dist (j i (sh x)) (p i) < 4 * L ∧
      L < dist (j i x) (j i (sh x)) := by
    filter_upwards [hdist (3 * L) (L / 100) (by positivity)] with i hi x hx
    have hxq : x ∈ ball q (3 * L) := mem_ball.mpr ((hDb x hx).trans (by linarith))
    have hshq : sh x ∈ ball q (3 * L) := mem_ball.mpr (hDsh x hx)
    have hqq : q ∈ ball q (3 * L) := mem_ball_self (by positivity)
    have h1 := abs_lt.mp (hi x hxq q hqq)
    have h2 := abs_lt.mp (hi (sh x) hshq q hqq)
    have h3 := abs_lt.mp (hi x hxq (sh x) hshq)
    rw [hpt i] at h1 h2
    refine ⟨mem_ball.mpr ?_, ?_, ?_⟩
    · linarith [hDb x hx]
    · linarith [hDsh x hx]
    · rw [hshd x] at h3
      linarith
  have hsmooth : ∀ᶠ i in atTop, ∀ x ∈ Cyl, MDifferentiableAt I 𝓘(ℝ, ℝ) (c i).coord (j i x) := by
    filter_upwards [hball] with i hi x hx
    have hxb := (hi x hx).1
    have hO := (c i).closedBall_subset_domain (ball_subset_closedBall hxb)
    exact (((c i).contMDiffOn_coord _ hO).contMDiffAt
      ((c i).isOpen_domain.mem_nhds hO)).mdifferentiableAt (by simp)
  have h19 : ∀ᶠ i in atTop, ∀ x ∈ Cyl,
      ∀ w ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo (g i)
        {j i (Φ.symm (WithLp.toLp 2 ((Φ x).fst + ℓ, (Φ x).snd)))} (j i x),
        |mvfderiv I (c i).coord (j i x) w -
          (((α i).toFun (j i (Φ.symm (WithLp.toLp 2 ((Φ x).fst + ℓ, (Φ x).snd))))).fst -
            ((α i).toFun (j i x)).fst) /
            dist (j i x) (j i (Φ.symm (WithLp.toLp 2 ((Φ x).fst + ℓ, (Φ x).snd))))| < σ := by
    filter_upwards [hball] with i hi x hx w hw
    obtain ⟨hxb, hshb, hlt⟩ := hi x hx
    obtain ⟨hw1, hwend⟩ := hw
    rw [infDist_singleton, mem_singleton_iff,
      Bundle.ContMDiffRiemannianMetric.expMap_smul_eq_intrinsicGeodesic (g i) (hEnorm i)] at hwend
    refine (c i).test (j i x) hxb (j i (sh x)) (mem_ball.mpr ?_) hlt w hw1 hwend
    rw [lt_div_iff₀ hσ]
    nlinarith
  have hstep2 := eventually_three_quarters_lt_mvfderiv_vertical hr G hGnorm g hmetric hK q j hexh
    hconv hdist hcover Φ hℓ hσ hCyl V hVdir hVcont (fun i => (c i).coord)
    (fun i x => ((α i).toFun x).fst) (fun i => (c i).lipschitz) hsmooth h19 hU hσ1
  have hval : ∀ᶠ i in atTop, ∀ x ∈ Cyl,
      dist ((Φ x).fst) (((α i).toFun (j i x)).fst) < Δ / 100 :=
    Metric.tendstoUniformlyOn_iff.mp (hU Cyl hCyl) (Δ / 100) (by positivity)
  refine ⟨V, hVdir, mvfderiv_splitting_fst_vertical G hr hGnorm Φ hℓ V hVdir, ?_⟩
  filter_upwards [hball, hstep2, hval,
    hcover (92 / 100 * L) (93 / 100 * L) (by positivity) (by linarith)] with
    i hbi hst hvi hcov
  refine ⟨fun x hx => ?_, fun y hy hya => ?_⟩
  · have hfv : |(c i).coord (j i x) - (Φ x).fst| < 2 * (Δ / 100) := by
      have h1 := (c i).value (j i x) (hbi x hx).1
      have h2 := hvi x hx
      rw [Real.dist_eq] at h2
      have := abs_sub_le ((c i).coord (j i x)) (((α i).toFun (j i x)).fst) ((Φ x).fst)
      rw [abs_sub_comm (((α i).toFun (j i x)).fst)] at this
      linarith
    have hd := hst x hx
    refine ⟨(hbi x hx).1, hfv, hd, fun u hu => ⟨three_quarters_lt_interpolation_deriv hd hu, ?_⟩⟩
    have h := (interpolation_enclosure (t := (Φ x).fst) (f := (c i).coord (j i x))
      (c := 2 * (Δ / 100)) (a := 9 / 10 * L) hfv hu).2
    exact h
  · have hyd := (c i).enclosure y hy (by nlinarith)
    have hyb : y ∈ ball (j i q) (92 / 100 * L) := by
      rw [hpt i, mem_ball]
      linarith
    obtain ⟨x, hxq, rfl⟩ := hcov hyb
    refine ⟨x, ?_, rfl⟩
    have h1 : |(Φ x).fst - (Φ q).fst| ≤ dist (Φ x) (Φ q) := abs_fst_sub_le_dist_withLp _ _
    rw [hq0, sub_zero, Φ.dist_eq] at h1
    have := mem_ball.mp hxq
    linarith

end DifferentialGeometry.Geometry.Collapse
