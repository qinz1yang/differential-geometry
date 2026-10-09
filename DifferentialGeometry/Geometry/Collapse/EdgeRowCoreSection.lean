import DifferentialGeometry.Geometry.Collapse.EdgeRowSequence
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimFibreGraphApplications

/-!
# The core-line section of the edge coordinate (EGP05 / CGP03), sequence form

Blueprint 207B, EGP05 (`lem:fibration-edge-cloud-section`, B:5042–5085) and the edge case of CGP03
(B:4029–4053): along a sequence converging to a nonnegatively curved product limit
`e : N ≃ᵢ ℓ²(ℝ × W)` (LFR14 data), the actual LFR19 coordinates `f_i` have, on a late index, a
continuous section `s_i : (-8.5Δ, 8.5Δ) → M_i` of `f_i` along the image of the core line
`t ↦ e⁻¹(t, w₀)` with `F_i/ρ_i < Δ/100` and `d(s_i(a), p_i) < 10Δ`.

* `exists_continuous_inverse_of_strictMonoOn`: a continuous strictly monotone function on
  `[-L, L]` with `g(-L) < -c`, `c < g(L)` has a continuous inverse on `(-c, c)` with values in
  `(-L, L)` (through the order isomorphism of the two order-connected sets).
* `eventually_edgeSourceSlab_core_section`: the section. Proof (B:5057–5085): LFR18's vertical
  field and the (LFR19.1) tests against `(t + 200Δ, w₀)` give `d(f_i ∘ j_i)(V) > 3/4` on the core
  segment `[-9Δ, 9Δ] × {w₀}` (`eventually_three_quarters_lt_mvfderiv_vertical`), so
  `t ↦ f_i(j_i(e⁻¹(t, w₀)))` is strictly increasing there (`strictMonoOn_comp_splitting_line`);
  its values are within `μΔ + Δ/1000` of `t`; the inverse on `(-8.5Δ, 8.5Δ)` composed with the
  line is the section. On the core line the axis distance is `0`, so (LFR28.2), (LFR25.2) and the
  value error of `F` give `F_i < Δ/200` there, and `ρ_i ≥ 1/2`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Function Filter Metric Manifold WithLp
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.MetricSmoothing
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Exponential
open GC.MetricGeometry

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)

local instance nezero_finrank_euclidean_three_section_LFR28ROW2 : NeZero (Module.finrank ℝ E3) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

/-- A continuous strictly monotone `g` on `[-L, L]` with `g (-L) < -c` and `c < g L` has a
continuous inverse on `(-c, c)` with values in `(-L, L)`. -/
theorem exists_continuous_inverse_of_strictMonoOn {g : ℝ → ℝ} {L c : ℝ} (hL : 0 ≤ L)
    (hg : ContinuousOn g (Icc (-L) L)) (hmono : StrictMonoOn g (Icc (-L) L))
    (hlo : g (-L) < -c) (hhi : c < g L) :
    ∃ h : Ioo (-c) c → ℝ, Continuous h ∧ ∀ a, h a ∈ Ioo (-L) L ∧ g (h a) = a := by
  by_cases hc : c ≤ 0
  · refine ⟨fun _ => 0, continuous_const, fun a => ?_⟩
    exact absurd (a.2.1.trans a.2.2) (by linarith)
  push Not at hc
  have hLL : -L ≤ L := by linarith
  let s : Set ℝ := {t | t ∈ Icc (-L) L ∧ g t ∈ Ioo (-c) c}
  have hs : s.OrdConnected := by
    refine ⟨fun x hx y hy t ht => ⟨⟨hx.1.1.trans ht.1, ht.2.trans hy.1.2⟩, ?_, ?_⟩⟩
    · exact lt_of_lt_of_le hx.2.1
        (hmono.monotoneOn hx.1 ⟨hx.1.1.trans ht.1, ht.2.trans hy.1.2⟩ ht.1)
    · exact lt_of_le_of_lt
        (hmono.monotoneOn ⟨hx.1.1.trans ht.1, ht.2.trans hy.1.2⟩ hy.1 ht.2) hy.2.2
  have _ := hs
  let φ : s → Ioo (-c) c := fun t => ⟨g t, t.2.2⟩
  have hφmono : StrictMono φ := fun a b hab => hmono a.2.1 b.2.1 hab
  have hφsurj : Surjective φ := by
    intro a
    obtain ⟨t, ht, hgt⟩ := intermediate_value_Icc hLL hg
      (show (a : ℝ) ∈ Icc (g (-L)) (g L) from ⟨by linarith [a.2.1], by linarith [a.2.2]⟩)
    refine ⟨⟨t, ht, ?_⟩, Subtype.ext hgt⟩
    rw [hgt]
    exact a.2
  let iso : s ≃o Ioo (-c) c := StrictMono.orderIsoOfSurjective φ hφmono hφsurj
  have hiso : ∀ a, g (iso.symm a : ℝ) = a := fun a =>
    congrArg Subtype.val (iso.apply_symm_apply a)
  refine ⟨fun a => (iso.symm a : ℝ), continuous_subtype_val.comp iso.symm.continuous,
    fun a => ⟨⟨?_, ?_⟩, hiso a⟩⟩
  · rcases (iso.symm a).2.1.1.eq_or_lt with h | h
    · have h' := hiso a
      rw [← h] at h'
      linarith [a.2.1]
    · exact h
  · rcases (iso.symm a).2.1.2.eq_or_lt with h | h
    · have h' := hiso a
      rw [h] at h'
      linarith [a.2.2]
    · exact h

/-- **The core-line section, sequence form.** See the module docstring. -/
theorem eventually_edgeSourceSlab_core_section
    {N : Type} [MetricSpace N] [ChartedSpace E3 N] [IsManifold 𝓘(ℝ, E3) ∞ N] [ProperSpace N]
    [RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x)] [IsRiemannianManifold 𝓘(ℝ, E3) N]
    {M : ℕ → Type} [∀ i, MetricSpace (M i)] [∀ i, ChartedSpace E3 (M i)]
    [∀ i, IsManifold 𝓘(ℝ, E3) ∞ (M i)] [∀ i, SigmaCompactSpace (M i)]
    [∀ i, RiemannianBundle (fun x : M i => TangentSpace 𝓘(ℝ, E3) x)]
    [∀ i, IsRiemannianManifold 𝓘(ℝ, E3) (M i)] [∀ i, CompleteSpace (M i)]
    [∀ i, IsContinuousRiemannianBundle E3 (fun x : M i => TangentSpace 𝓘(ℝ, E3) x)]
    {k : ℕ} (hk : 2 ≤ k)
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) (((k : ℕ∞) : ℕ∞ω) + 1) E3
      (TangentSpace 𝓘(ℝ, E3) : N → Type _))
    (hGnorm : ∀ (x : N) (w : TangentSpace 𝓘(ℝ, E3) x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, E3) (M i)) (hEnorm : ∀ i, IsMetricNorm (g i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (q : N) (j : ∀ i, PartialDiffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) N (M i) ((k + 2 : ℕ) : ℕ∞ω))
    (hexh : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source)
    (hconv : ∀ (x : N) (L : Set E3), IsCompact L → L ⊆ (extChartAt 𝓘(ℝ, E3) x).target →
      MapCPConvergenceOn L 1
        (fun i => pullbackMetricCoefficients (g i)
          ((j i : N → M i) ∘ (extChartAt 𝓘(ℝ, E3) x).symm))
        (chartCoeff G x))
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (j i x) (j i y) - dist x y| < ε)
    (hcover : ∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
      ball (j i q) a ⊆ (j i : N → M i) '' ball q b)
    {W : Type} [MetricSpace W] (e : N ≃ᵢ WithLp 2 (ℝ × W)) {w₀ : W}
    (heq : e q = WithLp.toLp 2 ((0 : ℝ), w₀))
    {Δ σ μ τ : ℝ} {Λ : ℝ≥0} (hΔ : 1 ≤ Δ) (hσ : 0 < σ) (hσ1 : σ ≤ 1 / 100)
    (hμ1 : μ ≤ 1 / 10 ^ 4) (hτ : 0 < τ) (hτ1 : τ ≤ 1 / 10 ^ 8) (hΛ : 100 * Δ * Λ ≤ 1 / 100)
    (Q : ∀ i, M i → WithLp 2 (ℝ × ℝ)) (E : ∀ i, Set (M i)) (U F f ρ : ∀ i, M i → ℝ)
    (hU : ∀ C : Set N, IsCompact C →
      TendstoUniformlyOn (fun i x => U i (j i x)) (fun x => (e x).fst) atTop C)
    (hQU : ∀ i z, (Q i z).fst = U i z)
    (hQp : ∀ i, Q i (j i q) = 0)
    (hQdist : ∀ i, ∀ x ∈ ball (j i q) (200 * Δ), ∀ y ∈ ball (j i q) (200 * Δ),
      |dist (Q i x) (Q i y) - dist x y| ≤ τ * Δ)
    (hheight : ∀ i, ∀ x ∈ ball (j i q) (200 * Δ), 0 ≤ (Q i x).snd)
    (hpE : ∀ i, j i q ∈ E i)
    (hborder : ∀ i, ∀ a ∈ E i ∩ ball (j i q) (190 * Δ), (Q i a).snd ≤ τ * Δ)
    (hbordercover : ∀ i, ∀ t : ℝ, |t| ≤ 100 * Δ →
      ∃ a ∈ E i ∩ ball (j i q) (190 * Δ), dist (Q i a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ)
    (hF : ∀ i x, |F i x - infDist x (E i)| < μ * Δ)
    (hρ : ∀ i, LipschitzWith Λ (ρ i)) (hρp : ∀ i, ρ i (j i q) = 1)
    (Of : ∀ i, Set (M i)) (hOf : ∀ i, IsOpen (Of i))
    (hOfb : ∀ i, closedBall (j i q) (100 * Δ) ⊆ Of i)
    (hfs : ∀ i, ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (f i) (Of i))
    (hflip : ∀ i, LipschitzWith (Real.toNNReal (1 + σ)) (f i))
    (hfval : ∀ i, ∀ x ∈ ball (j i q) (100 * Δ), |f i x - U i x| < μ * Δ)
    (hftest : ∀ i, ∀ x ∈ ball (j i q) (100 * Δ), ∀ x' ∈ ball (j i q) (1000 * Δ),
      100 * Δ < dist x x' → ∀ w : TangentSpace 𝓘(ℝ, E3) x, (g i).inner x w w = 1 →
      intrinsicGeodesic (g i) (hEnorm i) x w (dist x x') = x' →
      |mvfderiv 𝓘(ℝ, E3) (f i) x w - (U i x' - U i x) / dist x x'| < σ) :
    ∀ᶠ i in atTop, ∃ sec : Ioo (-(17 / 2 * Δ)) (17 / 2 * Δ) → M i, Continuous sec ∧
      ∀ a : Ioo (-(17 / 2 * Δ)) (17 / 2 * Δ),
        f i (sec a) = a ∧ F i (sec a) / ρ i (sec a) < Δ / 100 ∧ dist (sec a) (j i q) < 10 * Δ := by
  have hΔ0 : 0 < Δ := by linarith
  have hr2 : (2 : ℕ∞) ≤ (k : ℕ∞) := by exact_mod_cast hk
  have hK2 : 2 ≤ k + 2 := by omega
  have _ : CompleteSpace N := complete_of_proper
  -- the core line and the core segment
  let γ : ℝ → N := fun s => e.symm (toLp 2 (s, w₀))
  have hγc : Continuous γ := e.symm.continuous.comp ((WithLp.prod_continuous_toLp 2 ℝ W).comp
    (continuous_id.prodMk continuous_const))
  have heγ : ∀ s, e (γ s) = toLp 2 (s, w₀) := fun s => e.apply_symm_apply _
  have hγfst : ∀ s, (e (γ s)).fst = s := fun s => by rw [heγ]; rfl
  have hγsnd : ∀ s, (e (γ s)).snd = w₀ := fun s => by rw [heγ]; rfl
  have hγq : ∀ s, dist (γ s) q = |s| := by
    intro s
    rw [← e.dist_eq, heγ, heq, dist_withLp_two_prod]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, dist_self, Real.dist_eq, sub_zero]
    rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero, Real.sqrt_sq_eq_abs, abs_abs]
  set C : Set N := γ '' Icc (-(10 * Δ)) (10 * Δ) with hCdef
  have hC : IsCompact C := isCompact_Icc.image hγc
  have hCq : ∀ x ∈ C, dist x q ≤ 10 * Δ := by
    rintro _ ⟨s, hs, rfl⟩
    rw [hγq]
    exact abs_le.mpr ⟨hs.1, hs.2⟩
  ------------------------------------------------------------------ the vertical field
  set ℓ : ℝ := 200 * Δ with hℓdef
  have hℓ : 0 < ℓ := by positivity
  obtain ⟨V, hVdir, hVcont, -⟩ := exists_vertical_field_eventually_inverse_directions_close hr2 G
    hGnorm g hmetric hK2 q j hexh hconv hdist hcover e hℓ hC
  have hball3 : ∀ᶠ i in atTop, ∀ x ∈ C, j i x ∈ ball (j i q) (100 * Δ) ∧
      j i (e.symm (WithLp.toLp 2 ((e x).fst + ℓ, (e x).snd))) ∈ ball (j i q) (1000 * Δ) ∧
      100 * Δ < dist (j i x) (j i (e.symm (WithLp.toLp 2 ((e x).fst + ℓ, (e x).snd)))) := by
    filter_upwards [hdist (300 * Δ) Δ hΔ0] with i hi x hx
    set y := e.symm (WithLp.toLp 2 ((e x).fst + ℓ, (e x).snd)) with hydef
    have hey : e y = WithLp.toLp 2 ((e x).fst + ℓ, (e x).snd) := e.apply_symm_apply _
    have hxq := hCq x hx
    have hxy : dist x y = ℓ := by
      rw [hydef, dist_vertical_shift e ℓ x, abs_of_pos hℓ]
    have hyq : dist y q ≤ 210 * Δ := by
      have := dist_triangle y x q
      rw [dist_comm y x, hxy] at this
      linarith
    have hx3 : x ∈ ball q (300 * Δ) := mem_ball.mpr (by linarith)
    have hy3 : y ∈ ball q (300 * Δ) := mem_ball.mpr (by linarith)
    have hq3 : q ∈ ball q (300 * Δ) := mem_ball_self (by positivity)
    have h1 := abs_lt.mp (hi x hx3 q hq3)
    have h2 := abs_lt.mp (hi y hy3 q hq3)
    have h3 := abs_lt.mp (hi x hx3 y hy3)
    refine ⟨mem_ball.mpr (by linarith), mem_ball.mpr (by linarith), by linarith⟩
  have hfsm : ∀ᶠ i in atTop, ∀ x ∈ C, MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (f i) (j i x) := by
    filter_upwards [hball3] with i hi x hx
    have hO := hOfb i (ball_subset_closedBall (hi x hx).1)
    exact ((hfs i _ hO).contMDiffAt ((hOf i).mem_nhds hO)).mdifferentiableAt (by simp)
  have h19 : ∀ᶠ i in atTop, ∀ x ∈ C,
      ∀ w ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo (g i)
        {j i (e.symm (WithLp.toLp 2 ((e x).fst + ℓ, (e x).snd)))} (j i x),
        |mvfderiv 𝓘(ℝ, E3) (f i) (j i x) w -
          (U i (j i (e.symm (WithLp.toLp 2 ((e x).fst + ℓ, (e x).snd)))) - U i (j i x)) /
            dist (j i x) (j i (e.symm (WithLp.toLp 2 ((e x).fst + ℓ, (e x).snd))))| < σ := by
    filter_upwards [hball3] with i hi x hx w hw
    obtain ⟨hxb, hshb, hlt⟩ := hi x hx
    obtain ⟨hw1, hwend⟩ := hw
    rw [infDist_singleton, mem_singleton_iff,
      Bundle.ContMDiffRiemannianMetric.expMap_smul_eq_intrinsicGeodesic (g i) (hEnorm i)] at hwend
    exact hftest i (j i x) hxb _ hshb hlt w hw1 hwend
  have hpos := eventually_three_quarters_lt_mvfderiv_vertical hr2 G hGnorm g hmetric hK2 q j hexh
    hconv hdist hcover e hℓ hσ hC V hVdir hVcont f U hflip hfsm h19 hU hσ1
  ------------------------------------------------------------------ values on the segment
  have hcoord : TendstoUniformlyOn (fun i x => (Q i (j i x)).fst) (fun x => (e x).fst) atTop
      (closedBall q (100 * Δ)) := by
    have h := hU _ (isCompact_closedBall q (100 * Δ))
    simp only [← hQU] at h
    exact h
  have hhgt := eventually_abs_height_sub_axisDist_le (fun i => (j i : N → M i)) q hdist e heq
    hΔ0 hτ.le (by linarith) Q hQp hQdist hheight hcoord (21 * Real.sqrt τ)
    (by have := Real.sqrt_pos.mpr hτ; linarith)
  have hsqτ : Real.sqrt τ ≤ 1 / 10 ^ 4 := by
    refine Real.sqrt_le_iff.mpr ⟨by norm_num, ?_⟩
    have h1 : (1 / 10 ^ 4 : ℝ) ^ 2 = 1 / 10 ^ 8 := by norm_num
    rw [h1]
    exact hτ1
  filter_upwards [hexh C hC, hball3, hfsm, hpos, hhgt, hdist (100 * Δ) (Δ / 1000) (by positivity),
    Metric.tendstoUniformlyOn_iff.mp (hU C hC) (Δ / 1000) (by positivity)] with i hsrc hb3 hsm hp
    hh hdi hUi
  -- the function along the core line
  let φ : ℝ → ℝ := fun s => f i (j i (γ s))
  have hγC : ∀ s ∈ Icc (-(10 * Δ)) (10 * Δ), γ s ∈ C := fun s hs => ⟨s, hs, rfl⟩
  have hφc : ContinuousOn φ (Icc (-(9 * Δ)) (9 * Δ)) := by
    refine (hflip i).continuous.comp_continuousOn ?_
    refine ((j i).contMDiffOn_toFun.continuousOn.mono hsrc).comp hγc.continuousOn ?_
    intro s hs
    exact hγC s ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hφmono : StrictMonoOn φ (Icc (-(9 * Δ)) (9 * Δ)) := by
    have hjd : ∀ s ∈ Icc (-(9 * Δ)) (9 * Δ),
        MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun y => f i (j i y)) (γ s) := by
      intro s hs
      have hs' : γ s ∈ C := hγC s ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have hr0 : ((k + 2 : ℕ) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (show k + 2 ≠ 0 by omega)
      exact (hsm _ hs').comp (γ s) ((j i).mdifferentiableAt hr0 (hsrc hs'))
    exact strictMonoOn_comp_splitting_line G hr2 hGnorm e hℓ V hVdir (f := fun y => f i (j i y))
      w₀ hjd (fun s hs => by
        have := hp (γ s) (hγC s ⟨by linarith [hs.1], by linarith [hs.2]⟩)
        linarith)
  have hval : ∀ s ∈ Icc (-(10 * Δ)) (10 * Δ), |φ s - s| < Δ / 100 := by
    intro s hs
    have hx := hγC s hs
    have h1 := hfval i _ (hb3 _ hx).1
    have h2 := hUi _ hx
    rw [Real.dist_eq, hγfst] at h2
    have hμΔ : μ * Δ ≤ Δ / 10000 := by
      have := mul_le_mul_of_nonneg_right hμ1 hΔ0.le
      linarith
    have h3 := abs_sub_lt_iff.mp h2
    have h4 := abs_sub_lt_iff.mp h1
    rw [abs_sub_lt_iff]
    constructor <;> linarith [h3.1, h3.2, h4.1, h4.2]
  have hlo : φ (-(9 * Δ)) < -(17 / 2 * Δ) := by
    have := (abs_sub_lt_iff.mp (hval (-(9 * Δ)) ⟨by linarith, by linarith⟩)).1
    linarith
  have hhi : 17 / 2 * Δ < φ (9 * Δ) := by
    have := (abs_sub_lt_iff.mp (hval (9 * Δ) ⟨by linarith, by linarith⟩)).2
    linarith
  obtain ⟨hinv, hinvc, hinvp⟩ := exists_continuous_inverse_of_strictMonoOn (by positivity) hφc
    hφmono hlo hhi
  have hseg : ∀ a, hinv a ∈ Icc (-(10 * Δ)) (10 * Δ) := fun a =>
    ⟨by linarith [(hinvp a).1.1], by linarith [(hinvp a).1.2]⟩
  refine ⟨fun a => j i (γ (hinv a)), ?_, fun a => ⟨(hinvp a).2, ?_, ?_⟩⟩
  · refine (j i).contMDiffOn_toFun.continuousOn.comp_continuous (hγc.comp hinvc) ?_
    exact fun a => hsrc (hγC _ (hseg a))
  · -- the edge quotient on the core line
    set y := j i (γ (hinv a)) with hydef
    have hx := hγC _ (hseg a)
    have hxq : γ (hinv a) ∈ ball q (100 * Δ) := mem_ball.mpr (by linarith [hCq _ hx])
    have hq100 : q ∈ ball q (100 * Δ) := mem_ball_self (by positivity)
    have hyq : dist y (j i q) < 10 * Δ + Δ / 1000 := by
      have := (abs_lt.mp (hdi _ hxq q hq100)).2
      linarith [hCq _ hx]
    have hy70 : y ∈ ball (j i q) (70 * Δ) := mem_ball.mpr (by linarith)
    have hdb := (abs_le.mp (coarseBorder_abs_infDist_sub_height_le hΔ0 (by linarith) (hQp i)
      (hQdist i) (hheight i) (hpE i) (hborder i) (hbordercover i) hy70)).2
    have hht := (abs_le.mp (hh _ hxq)).2
    rw [hγsnd, dist_self, sub_zero] at hht
    have hFy := (abs_lt.mp (hF i y)).2
    have hρy : 1 / 2 ≤ ρ i y := by
      have h1 := (hρ i).dist_le_mul y (j i q)
      rw [Real.dist_eq, hρp i] at h1
      have h2 : (Λ : ℝ) * dist y (j i q) ≤ Λ * (11 * Δ) :=
        mul_le_mul_of_nonneg_left (by linarith) Λ.coe_nonneg
      have h3 := (abs_le.mp h1).1
      linarith
    have hsq : 21 * Real.sqrt τ * Δ ≤ 21 / 10 ^ 4 * Δ := by
      have := mul_le_mul_of_nonneg_right hsqτ hΔ0.le
      linarith
    have hτΔ : τ * Δ ≤ Δ / 10 ^ 8 := by
      have := mul_le_mul_of_nonneg_right hτ1 hΔ0.le
      linarith
    have hμΔ : μ * Δ ≤ Δ / 10 ^ 4 := by
      have := mul_le_mul_of_nonneg_right hμ1 hΔ0.le
      linarith
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  · have hx := hγC _ (hseg a)
    have hxq : γ (hinv a) ∈ ball q (100 * Δ) := mem_ball.mpr (by linarith [hCq _ hx])
    have hq100 : q ∈ ball q (100 * Δ) := mem_ball_self (by positivity)
    have h1 := (abs_lt.mp (hdi _ hxq q hq100)).2
    rw [hγq] at h1
    have h2 : |hinv a| < 9 * Δ := abs_lt.mpr ⟨(hinvp a).1.1, (hinvp a).1.2⟩
    linarith

end DifferentialGeometry.Geometry.Collapse
