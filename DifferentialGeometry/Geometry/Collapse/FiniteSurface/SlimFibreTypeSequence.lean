import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimFibreType
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.VerticalDerivativeBridgeApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.SlimChart
import DifferentialGeometry.Geometry.Exponential.FiniteMetric.SmoothAgreement

/-!
# LFR20 item 2, the fibre type along a converging sequence (modulo LFR14 data)

Blueprint LFR20 (master207A:26358), steps 1–4 in the sequence form of the compactness argument.
Data: LFR14's output for a sequence `(M i, p i)` (the limit `N`, its `C^{r+1}` metric `G`, the
pointed embeddings `j i` with exhaustion, `C¹` metric convergence, distance comparison and
coverage), an exact splitting `Φ : N ≃ᵢ ℓ²(ℝ × W)` with compact `W`, `diam W ≤ 10³Δ`, and, on every
`M i`, a normalized splitting `α i` with an LC85 slim chart `c i` (LFR19/LFR20's coordinate
`η i`), whose first coordinates converge: `u_i ∘ j_i → t` uniformly on compact sets.

`eventually_nonempty_homeomorph_zeroLevel_slimChart`: eventually the ENTIRE zero fibre
`{y ∈ B(p i, L) | η i y = 0}` is homeomorphic to the zero factor `{t = 0}` of `N`.

The proof: LFR18 (`exists_vertical_field_eventually_inverse_directions_close`) gives `V`; the chart's
(LFR19.1) becomes the lifted estimate of F7-DOWN's bridge, which gives (LFR20.1)
`d(η_i ∘ j_i)(V) > 3/4` on the cylinder `|t| ≤ 19L/20`; the chart's value clause gives
`|η_i ∘ j_i - t| < Δ/50`; (LFR20.2) and LFR14's coverage give the enclosure; then
`nonempty_homeomorph_zeroLevel_of_splitting`.
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
open GC.MetricGeometry

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

section Cylinder

variable {N W : Type*} [MetricSpace N] [MetricSpace W]

/-- The cylinder `{|t| ≤ b}` of an exact splitting with compact factor is compact. -/
theorem isCompact_splitting_cylinder [CompactSpace W] (Φ : N ≃ᵢ WithLp 2 (ℝ × W)) (b : ℝ) :
    IsCompact {x : N | |(Φ x).fst| ≤ b} := by
  have hc : Continuous fun q : ℝ × W => Φ.symm (toLp 2 q) :=
    Φ.symm.continuous.comp (WithLp.prod_continuous_toLp 2 ℝ W)
  have heq : {x : N | |(Φ x).fst| ≤ b} =
      (fun q : ℝ × W => Φ.symm (toLp 2 q)) '' (Icc (-b) b ×ˢ univ) := by
    ext x
    constructor
    · intro hx
      refine ⟨((Φ x).fst, (Φ x).snd), ⟨abs_le.mp hx, mem_univ _⟩, ?_⟩
      apply Φ.injective
      rw [Φ.apply_symm_apply]
      rfl
    · rintro ⟨⟨t, w⟩, ⟨ht, -⟩, rfl⟩
      change |(Φ (Φ.symm (toLp 2 (t, w)))).fst| ≤ b
      rw [Φ.apply_symm_apply]
      exact abs_le.mpr ht
  rw [heq]
  exact (isCompact_Icc.prod isCompact_univ).image hc

/-- The distance from a point of the cylinder to a point of the zero factor. -/
theorem dist_le_of_splitting {D : ℝ} (hD : ∀ a b : W, dist a b ≤ D) (Φ : N ≃ᵢ WithLp 2 (ℝ × W))
    {q x : N} (hq : (Φ q).fst = 0) {c : ℝ} (hx : |(Φ x).fst| ≤ c) :
    dist x q ≤ Real.sqrt (c ^ 2 + D ^ 2) := by
  rw [← Φ.dist_eq]
  apply dist_withLp_le_sqrt _ (hD _ _)
  rw [hq, sub_zero]
  exact hx

end Cylinder

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

/-- **LFR20 item 2, fibre type, sequence form (modulo LFR14 data).** Eventually the entire zero
fibre of the slim chart in `B(p i, L)` is homeomorphic to the zero factor of the limit. -/
theorem eventually_nonempty_homeomorph_zeroLevel_slimChart [CompactSpace W]
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
    ∀ᶠ i in atTop, Nonempty ({y // y ∈ ball (p i) (10 ^ 6 * Δ) ∧ (c i).coord y = 0} ≃ₜ
      {x : N // (Φ x).fst = 0}) := by
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
  -- the basepoint is on the zero factor
  have hq0 : (Φ q).fst = 0 := by
    have h := (hU {q} isCompact_singleton).tendsto_at (mem_singleton q)
    have h0 : (fun i => ((α i).toFun (j i q)).fst) = fun _ => (0 : ℝ) := by
      funext i
      rw [hpt i, (α i).basepoint]
      rfl
    rw [h0] at h
    exact (tendsto_nhds_unique tendsto_const_nhds h).symm
  -- the cylinder and its distances
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
  -- LFR18: the vertical field
  obtain ⟨V, hVdir, hVcont, -⟩ := exists_vertical_field_eventually_inverse_directions_close hr G
    hGnorm g hmetric hK q j hexh hconv hdist hcover Φ hℓ hCyl
  -- eventual facts
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
  filter_upwards [hexh Cyl hCyl, hball, hsmooth, hstep2, hval,
    hcover (92 / 100 * L) (93 / 100 * L) (by positivity) (by linarith)] with
    i hsrc hbi hsmi hst hvi hcov
  have hJ : ContinuousOn (j i : N → M i) Cyl :=
    ((j i).contMDiffOn_toFun.continuousOn).mono hsrc
  have hJinj : InjOn (j i : N → M i) Cyl := (j i).toPartialEquiv.injOn.mono hsrc
  refine nonempty_homeomorph_zeroLevel_of_splitting (r := r) G hr hGnorm Φ hℓ V hVdir
    (j i : N → M i) (b := b) (c := Δ / 50) (by positivity) (by nlinarith) hJ hJinj
    (c i).lipschitz.continuous (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)
    (fun x hx _ => (hbi x hx.le).1) (fun y hy hy0 => ?_)
  · have hjd : MDifferentiableAt I I (j i : N → M i) x :=
      (((j i).contMDiffOn_toFun x (hsrc hx)).contMDiffAt
        ((j i).open_source.mem_nhds (hsrc hx))).mdifferentiableAt (by
          norm_cast; omega)
    exact (hsmi x hx).comp x hjd
  · have := hst x hx
    change 0 < mvfderiv I (fun y => (c i).coord (j i y)) x (V x)
    linarith
  · have h1 := (c i).value (j i x) (hbi x hx).1
    have h2 := hvi x hx
    rw [Real.dist_eq] at h2
    have := abs_sub_le ((c i).coord (j i x)) (((α i).toFun (j i x)).fst) ((Φ x).fst)
    rw [abs_sub_comm (((α i).toFun (j i x)).fst)] at this
    linarith
  · have hyd := (c i).enclosure y hy (by rw [hy0, abs_zero]; positivity)
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
