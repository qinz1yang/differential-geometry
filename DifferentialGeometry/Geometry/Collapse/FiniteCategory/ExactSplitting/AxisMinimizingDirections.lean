import DifferentialGeometry.Geometry.Comparison.FiniteMetric.MinimizingDirections
import DifferentialGeometry.Geometry.Exponential.FiniteMetric.Segments
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.VerticalSegment

/-!
# LFR28 R1a, R1: minimizing directions to the axis of a metric product (lane LFR28-R12)

Let `e : N ≃ᵢ ℓ²(ℝ × W)` and let `A = e⁻¹{snd = z₀}` be an axis.

* `expMap_axisDirection_fst_eq` (R1a, the metric step): along `τ ↦ exp_x(τ v)`, `τ ∈ [0, d(x, A)]`,
  for a minimizing direction `v` to `A`, the time coordinate `(e ·).fst` is constant (`ℓ²` strict
  convexity: the time component of the geodesic contributes nothing to its length).
* `axisMinimizingDirection_eq_mfderiv_horizontal` (R1): for an isometric product parametrization
  `Θ : ℝ × S → N` (`e (Θ (t, s)) = (t, ψ s)`), every minimizing direction from `Θ(t, s)` to the axis
  `e⁻¹{snd = ψ s₀}` is the horizontal lift `dΘ_{(t,s)}(0, u)` of a minimizing direction `u` from `s`
  to `s₀` in `(S, κ)`.

Route of R1 (metric, no Christoffel naturality): by R1a the geodesic stays in the slice `{t} × S`,
so its `S`-part `σ` is a unit-speed metric segment of `S` (`Θ(t, ·)` is distance preserving); CM2.a
(`exists_expMap_eq_of_segment`) makes `σ` a `κ`-exponential curve `τ ↦ exp_s(τ u)`; comparing the
right derivatives at `0` (`eq_of_hasMFDerivAt_of_eqOn_Icc`) gives `v = dΘ(0, u)`.

General kernels (new): `dist_snd_le_dist_withLp_two`, `dist_toLp_two_same_fst`,
`dist_expMap_smul_eq_abs_of_mem_finiteMinimizingDirectionsTo` (a minimizing direction gives a
unit-speed segment on `[0, d]`), `eq_of_hasMFDerivAt_of_eqOn_Icc`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Metric Manifold
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-! ## `ℓ²` products -/

/-- The distance of the second components is at most the `ℓ²` distance. -/
theorem dist_snd_le_dist_withLp_two {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    (f g : WithLp 2 (α × β)) : dist f.snd g.snd ≤ dist f g := by
  rw [dist_withLp_two_prod]
  exact (le_abs_self _).trans (Real.abs_le_sqrt (by nlinarith [sq_nonneg (dist f.fst g.fst)]))

/-- Two points of the same time slice of `ℓ²(ℝ × W)` are at the distance of their `W`-parts. -/
theorem dist_toLp_two_same_fst {W : Type*} [PseudoMetricSpace W] (t : ℝ) (a b : W) :
    dist (WithLp.toLp 2 (t, a)) (WithLp.toLp 2 (t, b)) = dist a b := by
  rw [dist_withLp_two_prod]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd, dist_self]
  rw [show (0 : ℝ) ^ 2 = 0 by norm_num, zero_add, Real.sqrt_sq dist_nonneg]

/-- A point of `ℓ²(ℝ × W)` is at distance `d_W(f.snd, w)` from the point `(f.fst, w)` of its time
slice. -/
theorem dist_toLp_two_fst_snd {W : Type*} [PseudoMetricSpace W] (f : WithLp 2 (ℝ × W)) (w : W) :
    dist f (WithLp.toLp 2 (f.fst, w)) = dist f.snd w := by
  rw [dist_withLp_two_prod]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd, dist_self]
  rw [show (0 : ℝ) ^ 2 = 0 by norm_num, zero_add, Real.sqrt_sq dist_nonneg]

/-! ## Minimizing directions give unit-speed segments -/

section Segment

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]

/-- **A minimizing direction gives a unit-speed segment.** For `u` minimizing from `q` to `T`, the
curve `τ ↦ exp_q(τ u)` is a unit-speed metric segment on `[0, d(q, T)]`. -/
theorem dist_expMap_smul_eq_abs_of_mem_finiteMinimizingDirectionsTo [CompleteSpace M] {r : ℕ∞}
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {T : Set M} {q : M} {u : TangentSpace I q} (hu : u ∈ g.finiteMinimizingDirectionsTo T q)
    {a b : ℝ} (ha : a ∈ Icc 0 (infDist q T)) (hb : b ∈ Icc 0 (infDist q T)) :
    dist (g.expMap (⟨q, a • u⟩ : TangentBundle I M)) (g.expMap (⟨q, b • u⟩ : TangentBundle I M)) =
      |a - b| := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  set d := infDist q T with hd
  set γ : ℝ → M := fun τ => g.expMap (⟨q, τ • u⟩ : TangentBundle I M) with hγ
  have hup : ∀ a b : ℝ, dist (γ a) (γ b) ≤ |b - a| := by
    intro a b
    have h := g.dist_expMap_smul_le_of_completeSpace hr1 hnorm u a b
    rwa [hu.1, Real.sqrt_one, one_mul] at h
  have hγ0 : γ 0 = q := by
    simp only [hγ, zero_smul]
    exact g.expMap_zero hr1 q
  have hdT : d ≤ dist q (γ d) := infDist_le_dist_of_mem hu.2
  have key : ∀ a b : ℝ, a ∈ Icc 0 d → b ∈ Icc 0 d → a ≤ b → b - a ≤ dist (γ a) (γ b) := by
    intro a b ha hb hab
    have h1 := hup 0 a
    have h2 := hup b d
    rw [hγ0, sub_zero, abs_of_nonneg ha.1] at h1
    rw [abs_of_nonneg (sub_nonneg.mpr hb.2)] at h2
    have h3 := dist_triangle4 q (γ a) (γ b) (γ d)
    linarith
  change dist (γ a) (γ b) = |a - b|
  rcases le_total a b with hab | hab
  · rw [abs_of_nonpos (sub_nonpos.mpr hab), neg_sub]
    refine le_antisymm ?_ (key a b ha hb hab)
    have h := hup a b
    rwa [abs_of_nonneg (sub_nonneg.mpr hab)] at h
  · rw [abs_of_nonneg (sub_nonneg.mpr hab), dist_comm]
    refine le_antisymm ?_ (key b a hb ha hab)
    have h := hup b a
    rwa [abs_of_nonneg (sub_nonneg.mpr hab)] at h

end Segment

/-! ## Velocities from one-sided agreement -/

/-- Two curves that agree on `[0, d]` (`d > 0`) and are differentiable at `0` have the same velocity
at `0`. -/
theorem eq_of_hasMFDerivAt_of_eqOn_Icc {E' H' N' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N']
    [ChartedSpace H' N'] {f₁ f₂ : ℝ → N'} {d : ℝ} (hd : 0 < d) (heq : EqOn f₁ f₂ (Icc 0 d))
    {v w : E'} (h₁ : HasMFDerivAt 𝓘(ℝ, ℝ) I' f₁ 0 ((1 : ℝ →L[ℝ] ℝ).smulRight v))
    (h₂ : HasMFDerivAt 𝓘(ℝ, ℝ) I' f₂ 0 ((1 : ℝ →L[ℝ] ℝ).smulRight w)) : v = w := by
  have h0 : (0 : ℝ) ∈ Icc 0 d := left_mem_Icc.mpr hd.le
  have hU : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Icc (0 : ℝ) d) 0 :=
    uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.mpr (uniqueDiffOn_Icc hd 0 h0)
  have h2' : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I' f₁ (Icc 0 d) 0 ((1 : ℝ →L[ℝ] ℝ).smulRight w) :=
    h₂.hasMFDerivWithinAt.congr_of_eventuallyEq (eventually_nhdsWithin_of_forall heq) (heq h0)
  have h := congrArg (fun L : ℝ →L[ℝ] E' => L 1) (hU.eq h₁.hasMFDerivWithinAt h2')
  change (1 : ℝ →L[ℝ] ℝ) 1 • v = (1 : ℝ →L[ℝ] ℝ) 1 • w at h
  rwa [one_apply_eq_self, one_smul, one_smul] at h

/-! ## R1a -/

/-- **R1a.** In `N ≃ᵢ ℓ²(ℝ × W)`, the geodesic `τ ↦ exp_x(τv)` of a minimizing direction `v` to the
axis `{snd = z₀}` keeps the time coordinate of `x` for `τ ∈ [0, d(x, axis)]` (ℓ² strict convexity:
the endpoint has the same time, and every intermediate point realizes equality in the triangle
inequality). -/
theorem expMap_axisDirection_fst_eq {N W : Type} [MetricSpace N] [ChartedSpace E3 N]
    [IsManifold 𝓘(ℝ, E3) ∞ N] [CompleteSpace N]
    [RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x)]
    [IsRiemannianManifold 𝓘(ℝ, E3) N] [MetricSpace W] {r : ℕ∞}
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) ((r : ℕ∞ω) + 1) E3
      (TangentSpace 𝓘(ℝ, E3) : N → Type _)) (hr : 2 ≤ r)
    (hGnorm : ∀ (x : N) (w : TangentSpace 𝓘(ℝ, E3) x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (e : N ≃ᵢ WithLp 2 (ℝ × W)) (z₀ : W) (x : N) (v : TangentSpace 𝓘(ℝ, E3) x)
    (hv : v ∈ G.finiteMinimizingDirectionsTo (e ⁻¹' {p | p.snd = z₀}) x) :
    ∀ τ ∈ Icc (0 : ℝ) (infDist x (e ⁻¹' {p | p.snd = z₀})),
      (e (G.expMap (⟨x, τ • v⟩ : TangentBundle 𝓘(ℝ, E3) N))).fst = (e x).fst := by
  intro τ hτ
  have hr1 : 1 ≤ r := one_le_two.trans hr
  set A : Set N := e ⁻¹' {p | p.snd = z₀} with hA
  set d : ℝ := infDist x A with hd
  set y : N := G.expMap (⟨x, d • v⟩ : TangentBundle 𝓘(ℝ, E3) N) with hy
  set z : N := G.expMap (⟨x, τ • v⟩ : TangentBundle 𝓘(ℝ, E3) N) with hz
  have hyA : (e y).snd = z₀ := hv.2
  have hxz : dist x z ≤ τ := (G.infDist_expMap_smul_le_finite hr hGnorm hv hτ).2
  have hzy : dist z y ≤ d - τ := by
    have h := G.dist_expMap_smul_le_of_completeSpace hr1 hGnorm v τ d
    rwa [hv.1, Real.sqrt_one, one_mul, abs_of_nonneg (by linarith [hτ.2])] at h
  have hdW : d ≤ dist (e x).snd z₀ := by
    have hmem : e.symm (WithLp.toLp 2 ((e x).fst, z₀)) ∈ A := by
      change (e (e.symm (WithLp.toLp 2 ((e x).fst, z₀)))).snd = z₀
      rw [e.apply_symm_apply]
      rfl
    calc d ≤ dist x (e.symm (WithLp.toLp 2 ((e x).fst, z₀))) := infDist_le_dist_of_mem hmem
      _ = dist (e x) (WithLp.toLp 2 ((e x).fst, z₀)) := by
          rw [← e.dist_eq, e.apply_symm_apply]
      _ = dist (e x).snd z₀ := dist_toLp_two_fst_snd (e x) z₀
  have hp : dist (e x).snd (e z).snd ≤ dist x z := by
    rw [← e.dist_eq x z]
    exact dist_snd_le_dist_withLp_two _ _
  have hq : dist (e z).snd z₀ ≤ dist z y := by
    rw [← e.dist_eq z y, ← hyA]
    exact dist_snd_le_dist_withLp_two _ _
  have htri := dist_triangle (e x).snd (e z).snd z₀
  have heq : dist x z = dist (e x).snd (e z).snd := le_antisymm (by linarith) hp
  have hsq := dist_withLp_two_prod (e x) (e z)
  rw [e.dist_eq x z, heq] at hsq
  have h2 := Real.sq_sqrt (by positivity :
    0 ≤ dist (e x).fst (e z).fst ^ 2 + dist (e x).snd (e z).snd ^ 2)
  rw [← hsq] at h2
  have hf : dist (e x).fst (e z).fst = 0 := by
    have h3 : dist (e x).fst (e z).fst ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff two_ne_zero |>.mp h3
  exact (dist_eq_zero.mp hf).symm

/-! ## R1 -/

/-- **R1.** Let `Θ : ℝ × S → N` (left inverse `Θinv`, `C²`) satisfy `e (Θ (t, s)) = (t, ψ s)` for an
isometry `ψ : S ≃ᵢ W`. Then at every `x = Θ(t, s)` with `s ≠ s₀`, every `G`-minimizing direction `v`
to the axis `e⁻¹{snd = ψ s₀}` is the horizontal lift `dΘ_{(t,s)}(0, u)` of a `κ`-minimizing
direction `u` from `s` to `s₀`.

Strengthening of the frozen statement: the pull-back identity `hpull` (`Θ^*G = dt² + κ`) and the
smoothness of `Θinv` are not needed (the frozen form is the `example` below); the metric data `he`
and CM2.a already force the geodesic to be the lift of a `κ`-geodesic. -/
theorem axisMinimizingDirection_eq_mfderiv_horizontal {N W S : Type} [MetricSpace N]
    [ChartedSpace E3 N] [IsManifold 𝓘(ℝ, E3) ∞ N] [CompleteSpace N]
    [RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x)]
    [IsRiemannianManifold 𝓘(ℝ, E3) N] [MetricSpace W]
    [MetricSpace S] [ChartedSpace E2 S] [IsManifold (𝓡 2) ∞ S] [CompleteSpace S]
    [RiemannianBundle (fun x : S => TangentSpace (𝓡 2) x)] [IsRiemannianManifold (𝓡 2) S]
    {r r' : ℕ∞}
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) ((r : ℕ∞ω) + 1) E3
      (TangentSpace 𝓘(ℝ, E3) : N → Type _)) (hr : 2 ≤ r)
    (hGnorm : ∀ (x : N) (w : TangentSpace 𝓘(ℝ, E3) x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (κ : ContMDiffRiemannianMetric (𝓡 2) ((r' : ℕ∞ω) + 1) E2
      (TangentSpace (𝓡 2) : S → Type _)) (hr' : 2 ≤ r')
    (hκnorm : ∀ (x : S) (w : TangentSpace (𝓡 2) x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (κ.inner x w w)))
    (e : N ≃ᵢ WithLp 2 (ℝ × W)) (ψ : S ≃ᵢ W)
    (Θ : ℝ × S → N) (Θinv : N → ℝ × S) (hΘl : ∀ p, Θinv (Θ p) = p) (hΘr : ∀ x, Θ (Θinv x) = x)
    (hΘ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) 2 Θ)
    (he : ∀ p : ℝ × S, e (Θ p) = WithLp.toLp 2 (p.1, ψ p.2))
    (s₀ : S) (t : ℝ) (s : S) (hs : s ≠ s₀) :
    ∀ v ∈ G.finiteMinimizingDirectionsTo (e ⁻¹' {p | p.snd = ψ s₀}) (Θ (t, s)),
      ∃ u ∈ κ.finiteMinimizingDirectionsTo ({s₀} : Set S) s,
        v = mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (t, s) ((0 : ℝ), u) := by
  set A : Set N := e ⁻¹' {p | p.snd = ψ s₀} with hA
  set x : N := Θ (t, s) with hx
  set d : ℝ := infDist x A with hd
  intro v hv
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hr1' : 1 ≤ r' := one_le_two.trans hr'
  have neZero_LFR28R12 : NeZero (Module.finrank ℝ E2) :=
    ⟨by rw [finrank_euclideanSpace_fin]; norm_num⟩
  have hdomG : ∀ q, q ∈ G.geodesicFlowDomain := fun q => by
    rw [G.geodesicFlowDomain_eq_univ hr hGnorm]; exact mem_univ q
  have hdomκ : ∀ q, q ∈ κ.geodesicFlowDomain := fun q => by
    rw [κ.geodesicFlowDomain_eq_univ hr' hκnorm]; exact mem_univ q
  set c : ℝ → N := fun τ => G.expMap (⟨x, τ • v⟩ : TangentBundle 𝓘(ℝ, E3) N) with hc
  set σ : ℝ → S := fun τ => (Θinv (c τ)).2 with hσ
  have hd0 : 0 ≤ d := infDist_nonneg
  have hfst := expMap_axisDirection_fst_eq G hr hGnorm e (ψ s₀) x v hv
  have hex : e x = WithLp.toLp 2 (t, ψ s) := he (t, s)
  -- the geodesic stays in the slice `{t} × S`
  have hcΘ : ∀ τ ∈ Icc (0 : ℝ) d, c τ = Θ (t, σ τ) := by
    intro τ hτ
    have h1 : e (c τ) = WithLp.toLp 2 ((Θinv (c τ)).1, ψ (Θinv (c τ)).2) := by
      rw [← he, hΘr]
    have h2 : (Θinv (c τ)).1 = t := by
      have h3 := hfst τ hτ
      change (e (c τ)).fst = (e x).fst at h3
      rw [h1, hex] at h3
      exact h3
    calc c τ = Θ (Θinv (c τ)) := (hΘr _).symm
      _ = Θ (t, σ τ) := by rw [show Θinv (c τ) = (t, σ τ) from Prod.ext h2 rfl]
  -- `Θ(t, ·)` preserves distances
  have hslice : ∀ a b : S, dist (Θ (t, a)) (Θ (t, b)) = dist a b := by
    intro a b
    rw [← e.dist_eq, he, he, dist_toLp_two_same_fst, ψ.dist_eq]
  -- `σ` is a unit-speed segment from `s` of length `d`
  have hσseg : ∀ a ∈ Icc (0 : ℝ) d, ∀ b ∈ Icc (0 : ℝ) d, dist (σ a) (σ b) = |a - b| := by
    intro a ha b hb
    rw [← hslice, ← hcΘ a ha, ← hcΘ b hb]
    exact dist_expMap_smul_eq_abs_of_mem_finiteMinimizingDirectionsTo G hr hGnorm hv ha hb
  have hc0 : c 0 = x := by
    simp only [hc, zero_smul]
    exact G.expMap_zero hr1 x
  have hσ0 : σ 0 = s := by
    simp only [hσ, hc0, hx, hΘl]
  have hdmem : d ∈ Icc (0 : ℝ) d := ⟨hd0, le_rfl⟩
  have hσd : σ d = s₀ := by
    have h1 : (e (c d)).snd = ψ s₀ := hv.2
    rw [hcΘ d hdmem, he] at h1
    exact ψ.injective h1
  have hdist : dist s s₀ = d := by
    rw [← hσ0, ← hσd, hσseg 0 ⟨le_rfl, hd0⟩ d hdmem, zero_sub, abs_neg, abs_of_nonneg hd0]
  have hdpos : 0 < d := by
    rcases eq_or_lt_of_le hd0 with h | h
    · exact absurd (dist_eq_zero.mp (hdist.trans h.symm)) hs
    · exact h
  -- CM2.a: `σ` is a `κ`-exponential curve
  obtain ⟨u, hu1, hσexp⟩ := κ.exists_expMap_eq_of_segment hr' hκnorm hσseg
  rw [hσ0] at hu1 hσexp
  have hσflow : ∀ τ ∈ Icc (0 : ℝ) d, σ τ = (κ.geodesicFlow (⟨s, u⟩ : TangentBundle (𝓡 2) S) τ).proj :=
    fun τ hτ => (hσexp τ hτ).2.trans (κ.expMap_smul_eq_proj_geodesicFlow hr1' s u τ (hdomκ _))
  refine ⟨u, ⟨hu1, ?_⟩, ?_⟩
  · rw [infDist_singleton, hdist]
    exact mem_singleton_iff.mpr (((hσexp d hdmem).2).symm.trans hσd)
  · -- compare the velocities at `0`
    set p : TangentBundle (𝓡 2) S := ⟨s, u⟩ with hp
    have hD1 : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E3) c 0 ((1 : ℝ →L[ℝ] ℝ).smulRight v) := by
      have hcflow : c = fun τ => (G.geodesicFlow (⟨x, v⟩ : TangentBundle 𝓘(ℝ, E3) N) τ).proj :=
        funext fun τ => G.expMap_smul_eq_proj_geodesicFlow hr1 x v τ (hdomG _)
      rw [hcflow]
      exact (G.hasMFDerivAt_geodesicFlow_proj hr1 (hdomG _)).congr_mfderiv
        (by rw [G.geodesicFlow_zero hr1]; rfl)
    have hgeo : HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 2) (fun τ => (κ.geodesicFlow p τ).proj) 0
        ((1 : ℝ →L[ℝ] ℝ).smulRight u) :=
      (κ.hasMFDerivAt_geodesicFlow_proj hr1' (hdomκ _)).congr_mfderiv
        (by rw [κ.geodesicFlow_zero hr1'])
    have hpair : HasMFDerivAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (𝓡 2))
        (fun τ => (t, (κ.geodesicFlow p τ).proj)) 0
        ((0 : ℝ →L[ℝ] ℝ).prod ((1 : ℝ →L[ℝ] ℝ).smulRight u)) :=
      (hasMFDerivAt_const t (0 : ℝ)).prodMk hgeo
    have hpt : (t, (κ.geodesicFlow p 0).proj) = (t, s) := by
      rw [κ.geodesicFlow_zero hr1']
    have hΘd : HasMFDerivAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (t, (κ.geodesicFlow p 0).proj)
        (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (t, s)) := by
      rw [hpt]
      exact (hΘ.mdifferentiableAt two_ne_zero).hasMFDerivAt
    have hD2 : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E3) (fun τ => Θ (t, (κ.geodesicFlow p τ).proj)) 0
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (t, s) ((0 : ℝ), u))) := by
      refine (hΘd.comp 0 hpair).congr_mfderiv ?_
      refine ContinuousLinearMap.ext_ring ?_
      change mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (t, s)
          ((0 : ℝ →L[ℝ] ℝ) 1, (1 : ℝ →L[ℝ] ℝ) 1 • u) =
        (1 : ℝ →L[ℝ] ℝ) 1 • mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (t, s) ((0 : ℝ), u)
      rw [one_apply_eq_self, one_smul, one_smul, zero_apply]
    refine eq_of_hasMFDerivAt_of_eqOn_Icc (E' := E3) (I' := 𝓘(ℝ, E3)) hdpos
      (fun τ hτ => ?_) hD1 hD2
    rw [hcΘ τ hτ, hσflow τ hτ]

/-- The frozen form of R1 (with the unused hypotheses `hΘinv` and `hpull`). -/
example {N W S : Type} [MetricSpace N]
    [ChartedSpace E3 N] [IsManifold 𝓘(ℝ, E3) ∞ N] [CompleteSpace N]
    [RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x)]
    [IsRiemannianManifold 𝓘(ℝ, E3) N] [MetricSpace W]
    [MetricSpace S] [ChartedSpace E2 S] [IsManifold (𝓡 2) ∞ S] [CompleteSpace S]
    [RiemannianBundle (fun x : S => TangentSpace (𝓡 2) x)] [IsRiemannianManifold (𝓡 2) S]
    {r r' : ℕ∞}
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) ((r : ℕ∞ω) + 1) E3
      (TangentSpace 𝓘(ℝ, E3) : N → Type _)) (hr : 2 ≤ r)
    (hGnorm : ∀ (x : N) (w : TangentSpace 𝓘(ℝ, E3) x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (κ : ContMDiffRiemannianMetric (𝓡 2) ((r' : ℕ∞ω) + 1) E2
      (TangentSpace (𝓡 2) : S → Type _)) (hr' : 2 ≤ r')
    (hκnorm : ∀ (x : S) (w : TangentSpace (𝓡 2) x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (κ.inner x w w)))
    (e : N ≃ᵢ WithLp 2 (ℝ × W)) (ψ : S ≃ᵢ W)
    (Θ : ℝ × S → N) (Θinv : N → ℝ × S) (hΘl : ∀ p, Θinv (Θ p) = p) (hΘr : ∀ x, Θ (Θinv x) = x)
    (hΘ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) 2 Θ)
    (_hΘinv : ContMDiff 𝓘(ℝ, E3) (𝓘(ℝ, ℝ).prod (𝓡 2)) 2 Θinv)
    (he : ∀ p : ℝ × S, e (Θ p) = WithLp.toLp 2 (p.1, ψ p.2))
    (_hpull : ∀ (p : ℝ × S) (v w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 2)) p),
      G.inner (Θ p) (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ p v)
        (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ p w) = v.1 * w.1 + κ.inner p.2 v.2 w.2)
    (s₀ : S) (t : ℝ) (s : S) (hs : s ≠ s₀) :
    ∀ v ∈ G.finiteMinimizingDirectionsTo (e ⁻¹' {p | p.snd = ψ s₀}) (Θ (t, s)),
      ∃ u ∈ κ.finiteMinimizingDirectionsTo ({s₀} : Set S) s,
        v = mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (t, s) ((0 : ℝ), u) :=
  axisMinimizingDirection_eq_mfderiv_horizontal G hr hGnorm κ hr' hκnorm e ψ Θ Θinv hΘl hΘr hΘ
    he s₀ t s hs

end DifferentialGeometry.Geometry.Collapse
