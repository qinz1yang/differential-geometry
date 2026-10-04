import DifferentialGeometry.Topology.Manifold.SmoothApproximation.Boundary.Collar.BoundaryPiece
import DifferentialGeometry.Topology.Manifold.SmoothApproximation.Boundary.Collar.Assembly
import DifferentialGeometry.Topology.Manifold.SmoothApproximation.Boundary.Collar.Normal
import DifferentialGeometry.Topology.Manifold.SmoothApproximation.EuclideanValued
import Mathlib.Geometry.Manifold.WhitneyEmbedding

/-!
# A3-c: collar straightening

`exists_diffeomorph_one_smooth_near_boundary`: a `C^k` diffeomorphism `h : A ≃ B` (`2 ≤ k`) of
compact manifolds with boundary (model `𝓡∂ (n + 1)`) can be replaced by a `C¹` diffeomorphism that
is smooth on an open neighbourhood of `∂A` (the input of W3 relative to the boundary, hence of
LFR04).

Route (no approximation up to the boundary, no boundary inverse function theorem): smooth collars
`cA`, `cB` with defining functions `rA`, `rB` and projections `πA`, `πB`; an embedding `e` of `∂B`
with a smooth retraction `ret`. In collar coordinates of `B`, `g = (e ∘ πB ∘ h, rB ∘ h)`; its
boundary data `u = g (·, 0)` (`C^k`, an immersion) and `w = ∂_t g (·, 0)` (`C¹` because `2 ≤ k`,
`contMDiff_collar_derivWithin`; positive normal component) are approximated on the compact
boundaryless `∂A` by smooth maps (W1a). The first-order model `(u_j ∘ πA, 0) + rA • w_j ∘ πA` is
blended with `g` across `{δ_j / 3 ≤ rA ≤ 2 δ_j / 3}` and pushed into `B` by `cB ∘ (ret × projIcc)`.
Local pieces: `eventually_injOn_isInvertible_straighten` at boundary points, `h` itself far from
`∂A`; global: `eventually_exists_diffeomorph_of_collar_pieces`.

* `contMDiff_collar_derivWithin`: the one-sided collar derivative of a `C^k` map (`2 ≤ k`) is `C¹`
  on the boundary;
* `norm_blend_sub_le`, `norm_model_sub_le`, `blend_fst_dist_le`, `blend_snd_mem`: pointwise
  estimates of the blend;
* `exists_eventually_mapsTo_of_collar_coord`: locally uniform convergence of the pushed maps;
* `exists_diffeomorph_one_of_collar_data`: the construction from collar data;
* `exists_diffeomorph_one_smooth_near_boundary`: **A3-c**.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Metric
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.VectorField

namespace DifferentialGeometry.Topology.Manifold.SmoothApproximation

/-- Boundary data of the collar straightening: the one-sided collar derivative of a `C^k` map
`g : A → F` (`2 ≤ k`) along a smooth collar `c` is `C¹` on the boundary. -/
theorem contMDiff_collar_derivWithin {n : ℕ}
    {A : Type*} [TopologicalSpace A] [ChartedSpace (EuclideanHalfSpace (n + 1)) A]
    [IsManifold (𝓡∂ (n + 1)) ∞ A]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a : ℝ} [Fact ((0 : ℝ) < a)]
    {c : BoundaryManifold (𝓡∂ (n + 1)) A × Icc (0 : ℝ) a → A}
    (hc : ContMDiff ((HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))).prod (𝓡∂ 1))
      (𝓡∂ (n + 1)) ∞ c)
    {k : ℕ} (hk : 2 ≤ k) {g : A → F} {O : Set A} (hO : IsOpen O)
    (hg : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, F) k g O)
    (hcO : ∀ p : BoundaryManifold (𝓡∂ (n + 1)) A, c (p, ⟨0, le_rfl, (Fact.out : (0 : ℝ) < a).le⟩) ∈ O) :
    ContMDiff (HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))) 𝓘(ℝ, F) 1
      (fun p => derivWithin (fun t => g (c (p, projIcc 0 a (Fact.out : (0 : ℝ) < a).le t)))
        (Icc 0 a) 0) := by
  set J := HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1)) with hJ
  have ha : (0 : ℝ) < a := Fact.out
  intro p₀
  set φ := extChartAt J p₀ with hφ
  set κ : (EuclideanSpace ℝ (Fin (n + 1 - 1)) × ℝ) → A :=
    fun z => c (φ.symm z.1, projIcc 0 a ha.le z.2) with hκ
  set T₀ : Set (EuclideanSpace ℝ (Fin (n + 1 - 1)) × ℝ) := φ.target ×ˢ Icc 0 a with hT₀
  have hκc : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1 - 1)) × ℝ) (𝓡∂ (n + 1)) ∞ κ T₀ := by
    have h1 : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1 - 1)) × ℝ) J ∞
        (fun z : EuclideanSpace ℝ (Fin (n + 1 - 1)) × ℝ => φ.symm z.1) T₀ :=
      (contMDiffOn_extChartAt_symm p₀).comp contDiff_fst.contMDiff.contMDiffOn
        (fun z hz => hz.1)
    have h2 : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1 - 1)) × ℝ) (𝓡∂ 1) ∞
        (fun z : EuclideanSpace ℝ (Fin (n + 1 - 1)) × ℝ => projIcc 0 a ha.le z.2) T₀ :=
      contMDiffOn_projIcc.comp contDiff_snd.contMDiff.contMDiffOn (fun z hz => hz.2)
    exact hc.comp_contMDiffOn (h1.prodMk h2)
  set y₀ := φ p₀ with hy₀
  have hz₀ : (y₀, (0 : ℝ)) ∈ T₀ := ⟨mem_extChartAt_target (I := J) p₀, left_mem_Icc.2 ha.le⟩
  have hκz₀ : κ (y₀, 0) ∈ O := by
    have : κ (y₀, 0) = c (p₀, ⟨0, le_rfl, ha.le⟩) := by
      simp only [hκ, hy₀, hφ, extChartAt_to_inv, projIcc_left]
    rw [this]
    exact hcO p₀
  -- a product neighbourhood inside `T₀ ∩ κ⁻¹ O`
  obtain ⟨V, hV, hVe⟩ := (continuousOn_iff'.mp hκc.continuousOn) O hO
  have hVz : (y₀, (0 : ℝ)) ∈ V := by
    have : (y₀, (0 : ℝ)) ∈ κ ⁻¹' O ∩ T₀ := ⟨hκz₀, hz₀⟩
    rw [hVe] at this
    exact this.1
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.mp (hV.inter ((isOpen_extChartAt_target (I := J) p₀).prod
    isOpen_univ)) _ ⟨hVz, mem_extChartAt_target (I := J) p₀, mem_univ _⟩
  set r' := min r a with hr'
  have hr'pos : 0 < r' := lt_min hr ha
  set S : Set (EuclideanSpace ℝ (Fin (n + 1 - 1)) × ℝ) := ball y₀ r' ×ˢ Ico 0 r' with hS
  have hSsub : S ⊆ T₀ ∩ κ ⁻¹' O := by
    rintro ⟨y, t⟩ ⟨hy, ht⟩
    have hball : (y, t) ∈ ball (y₀, (0 : ℝ)) r := by
      rw [mem_ball, Prod.dist_eq]
      refine max_lt (lt_of_lt_of_le (mem_ball.mp hy) (min_le_left _ _)) ?_
      rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
      exact lt_of_lt_of_le ht.2 (min_le_left _ _)
    have hmem := hrV hball
    have hT : (y, t) ∈ T₀ := ⟨hmem.2.1, ht.1, (lt_of_lt_of_le ht.2 (min_le_right _ _)).le⟩
    have : (y, t) ∈ V ∩ T₀ := ⟨hmem.1, hT⟩
    rw [← hVe] at this
    exact ⟨hT, this.1⟩
  have hSu : UniqueDiffOn ℝ S := isOpen_ball.uniqueDiffOn.prod (uniqueDiffOn_Ico 0 r')
  set G := fun z => g (κ z) with hG
  have hGS : ContDiffOn ℝ k G S := by
    have h := (hg.comp ((hκc.of_le (by exact_mod_cast le_top)).mono inter_subset_left)
      (fun z hz => hz.2)).mono hSsub
    exact contMDiffOn_iff_contDiffOn.mp h
  have hG'S : ContDiffOn ℝ 1 (fderivWithin ℝ G S) S :=
    hGS.fderivWithin hSu (by exact_mod_cast (show 1 + 1 ≤ k by omega))
  -- the boundary data in the chart
  have hj1 : ∀ y ∈ ball y₀ r',
      derivWithin (fun t => g (c (φ.symm y, projIcc 0 a ha.le t))) (Icc 0 a) 0 =
        fderivWithin ℝ G S (y, 0) (0, 1) := by
    intro y hy
    have hyS : (y, (0 : ℝ)) ∈ S := ⟨hy, left_mem_Ico.2 hr'pos⟩
    have hGd : HasFDerivWithinAt G (fderivWithin ℝ G S (y, 0)) S (y, 0) :=
      ((hGS.differentiableOn (by exact_mod_cast (show k ≠ 0 by omega))) _ hyS).hasFDerivWithinAt
    have hcurve : HasDerivWithinAt (fun t : ℝ => (y, t)) ((0 : EuclideanSpace ℝ (Fin (n + 1 - 1))),
        (1 : ℝ)) (Ico 0 r') 0 :=
      (hasDerivAt_const (0 : ℝ) y).prodMk (hasDerivAt_id (0 : ℝ)) |>.hasDerivWithinAt
    have hcomp := hGd.comp_hasDerivWithinAt (x := (0 : ℝ)) hcurve
      (fun t ht => ⟨hy, ht⟩)
    have hmem : Ico 0 r' ∈ 𝓝[Icc 0 a] (0 : ℝ) := by
      refine Filter.mem_of_superset (inter_mem_nhdsWithin (Icc 0 a) (Iio_mem_nhds hr'pos)) ?_
      rintro t ⟨ht, ht'⟩
      exact ⟨ht.1, ht'⟩
    exact (hcomp.mono_of_mem_nhdsWithin hmem).derivWithin
      (uniqueDiffOn_Icc ha 0 (left_mem_Icc.2 ha.le))
  -- regularity in the chart
  have hreg : ContDiffOn ℝ 1 (fun y => fderivWithin ℝ G S (y, 0) (0, 1)) (ball y₀ r') := by
    have h1 : ContDiffOn ℝ 1 (fun y => fderivWithin ℝ G S (y, 0)) (ball y₀ r') :=
      hG'S.comp (contDiff_id.prodMk contDiff_const).contDiffOn
        (fun y hy => ⟨hy, left_mem_Ico.2 hr'pos⟩)
    exact h1.clm_apply contDiffOn_const
  rw [contMDiffAt_iff_source]
  have hrange : range J = univ := ModelWithCorners.Boundaryless.range_eq_univ
  rw [hrange, contMDiffWithinAt_univ, contMDiffAt_iff_contDiffAt]
  have hev : (fun y => derivWithin (fun t => g (c (φ.symm y, projIcc 0 a ha.le t))) (Icc 0 a) 0)
      =ᶠ[𝓝 y₀] fun y => fderivWithin ℝ G S (y, 0) (0, 1) :=
    Filter.mem_of_superset (isOpen_ball.mem_nhds (mem_ball_self hr'pos)) fun y hy => hj1 y hy
  exact ((hreg.contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hr'pos))).congr_of_eventuallyEq
    hev)

section Blend

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The blend `M + ρ • (G - M)` (`ρ ∈ [0, 1]`) is at least as close to `G` as `M`. -/
theorem norm_blend_sub_le {M G : F × ℝ} {ρ : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1) :
    ‖M + ρ • (G - M) - G‖ ≤ ‖M - G‖ := by
  have h : M + ρ • (G - M) - G = (1 - ρ) • (M - G) := by module
  rw [h, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hρ.2])]
  exact mul_le_of_le_one_left (norm_nonneg _) (by linarith [hρ.1])

/-- Distance of the first-order collar model `(a, 0) + r • w` to a point `G`. -/
theorem norm_model_sub_le (a u₀ : F) (w G : F × ℝ) {r : ℝ} (hr : 0 ≤ r) :
    ‖((a, (0 : ℝ)) + r • w) - G‖ ≤ ‖a - u₀‖ + ‖((u₀, (0 : ℝ)) : F × ℝ) - G‖ + r * ‖w‖ := by
  have h : ((a, (0 : ℝ)) + r • w) - G =
      ((a - u₀, (0 : ℝ)) : F × ℝ) + (((u₀, (0 : ℝ)) : F × ℝ) - G) + r • w := by
    ext <;> simp <;> abel
  rw [h]
  refine norm_add₃_le.trans (add_le_add (add_le_add (le_of_eq (norm_prod_mk_zero _)) le_rfl) ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]

/-- First component of the collar blend: it stays within `η` of `G.1`. -/
theorem blend_fst_dist_le {a u₀ : F} {w G : F × ℝ} {r ρ δ' C η : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1)
    (hr0 : 0 ≤ r) (hr : r < δ') (hw : ‖w‖ ≤ C + 1) (hδC : δ' * (C + 2) ≤ η / 3)
    (ha : ‖a - u₀‖ ≤ η / 3) (hu : ‖u₀ - G.1‖ ≤ η / 3) :
    dist (((a, (0 : ℝ)) + r • w) + ρ • (G - ((a, 0) + r • w))).1 G.1 ≤ η := by
  have hX : (((a, (0 : ℝ)) + r • w) + ρ • (G - ((a, 0) + r • w))).1 - G.1 =
      (1 - ρ) • ((a - u₀) + (u₀ - G.1) + r • w.1) := by
    simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub]
    module
  rw [dist_eq_norm, hX, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hρ.2])]
  have h1 : ‖(a - u₀) + (u₀ - G.1) + r • w.1‖ ≤ η := by
    refine norm_add₃_le.trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0]
    have h2 : r * ‖w.1‖ ≤ δ' * (C + 2) :=
      mul_le_mul hr.le (by linarith [norm_fst_le w]) (norm_nonneg _) (by linarith)
    linarith
  calc (1 - ρ) * ‖(a - u₀) + (u₀ - G.1) + r • w.1‖ ≤ 1 * η :=
        mul_le_mul (by linarith [hρ.1]) h1 (norm_nonneg _) zero_le_one
    _ = η := one_mul η

/-- Second component (height) of the collar blend. -/
theorem blend_snd_mem {a : F} {w G : F × ℝ} {r ρ δ' C aB : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1)
    (hr0 : 0 ≤ r) (hr : r < δ') (hw : ‖w‖ ≤ C + 1) (hw2 : 0 < w.2)
    (hδC : δ' * (C + 2) ≤ aB / 4) (hG0 : 0 ≤ G.2) (hG : G.2 < aB / 2) :
    (((a, (0 : ℝ)) + r • w) + ρ • (G - ((a, 0) + r • w))).2 ∈ Ico 0 aB ∧
      (0 < r → 0 < G.2 → 0 < (((a, (0 : ℝ)) + r • w) + ρ • (G - ((a, 0) + r • w))).2) := by
  have hX : (((a, (0 : ℝ)) + r • w) + ρ • (G - ((a, 0) + r • w))).2 =
      (1 - ρ) * (r * w.2) + ρ * G.2 := by
    simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
    ring
  rw [hX]
  have hw2' : w.2 ≤ C + 1 :=
    (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans ((norm_snd_le _).trans hw))
  have ha₁ : r * w.2 ≤ aB / 4 := by
    have h1 : r * w.2 ≤ δ' * (C + 2) := mul_le_mul hr.le (by linarith) hw2.le (by linarith)
    linarith
  have ha₁0 : 0 ≤ r * w.2 := mul_nonneg hr0 hw2.le
  obtain ⟨hρ0, hρ1⟩ := hρ
  have e1 : (1 - ρ) * (r * w.2) ≤ r * w.2 := mul_le_of_le_one_left ha₁0 (by linarith)
  have e2 : ρ * G.2 ≤ G.2 := mul_le_of_le_one_left hG0 hρ1
  have e3 : 0 ≤ (1 - ρ) * (r * w.2) := mul_nonneg (by linarith) ha₁0
  have e4 : 0 ≤ ρ * G.2 := mul_nonneg hρ0 hG0
  refine ⟨⟨by linarith, by linarith⟩, fun hrpos hGpos => ?_⟩
  rcases lt_or_eq_of_le hρ1 with hlt | heq
  · have h1 : 0 < (1 - ρ) * (r * w.2) := mul_pos (by linarith) (mul_pos hrpos hw2)
    linarith
  · rw [heq, one_mul]
    linarith

omit [NormedSpace ℝ F] in
/-- Locally uniform convergence of pushed collar maps at a point where the collar coordinates
`X j` converge to `g` at a rate `c j + ψ x` with `c j → 0`, `ψ` continuous and `ψ a = 0`. -/
theorem exists_eventually_mapsTo_of_collar_coord {A B Q : Type*} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace Q] {aB : ℝ} [Fact ((0 : ℝ) < aB)]
    {cB : Q × Icc (0 : ℝ) aB → B} (hcB : Continuous cB) {ret : F → Q} {U : Set F}
    (hU : IsOpen U) (hret : ContinuousOn ret U) {g : A → F × ℝ} {h : A → B} {a : A}
    (hga : (g a).1 ∈ U) (hgc : ContinuousAt g a)
    (hΦ : cB (ret (g a).1, projIcc 0 aB (Fact.out : (0 : ℝ) < aB).le (g a).2) = h a)
    {f : ℕ → A → B} {X : ℕ → A → F × ℝ} {Na : Set A} (hNa : Na ∈ 𝓝 a)
    (hfX : ∀ j, ∀ x ∈ Na,
      f j x = cB (ret (X j x).1, projIcc 0 aB (Fact.out : (0 : ℝ) < aB).le (X j x).2))
    {c : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 0)) {ψ : A → ℝ} (hψ : ContinuousAt ψ a)
    (hψa : ψ a = 0) (hXg : ∀ j, ∀ x ∈ Na, ‖X j x - g x‖ ≤ c j + ψ x)
    {V : Set B} (hV : IsOpen V) (haV : h a ∈ V) :
    ∃ N ∈ 𝓝 a, ∀ᶠ j in atTop, MapsTo (f j) N V := by
  set Φ : F × ℝ → B := fun ζ => cB (ret ζ.1, projIcc 0 aB (Fact.out : (0 : ℝ) < aB).le ζ.2)
    with hΦdef
  have hΦc : ContinuousAt Φ (g a) :=
    hcB.continuousAt.comp (((hret.continuousAt (hU.mem_nhds hga)).comp continuousAt_fst).prodMk
      (continuous_projIcc.continuousAt.comp continuousAt_snd))
  have hΦV : Φ (g a) ∈ V := by
    change cB (ret (g a).1, projIcc 0 aB (Fact.out : (0 : ℝ) < aB).le (g a).2) ∈ V
    rw [hΦ]
    exact haV
  obtain ⟨ε, hε, hεV⟩ : ∃ ε > 0, ∀ ζ, dist ζ (g a) < ε → Φ ζ ∈ V := by
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hΦc.preimage_mem_nhds (hV.mem_nhds hΦV))
    exact ⟨ε, hε, fun ζ hζ => hball hζ⟩
  have hε3 : (0 : ℝ) < ε / 3 := by positivity
  have hgn : ∀ᶠ x in 𝓝 a, dist (g x) (g a) < ε / 3 := hgc.eventually (Metric.ball_mem_nhds _ hε3)
  have hψn : ∀ᶠ x in 𝓝 a, ψ x < ε / 3 := hψ.eventually (Iio_mem_nhds (by rw [hψa]; exact hε3))
  refine ⟨{x | dist (g x) (g a) < ε / 3} ∩ {x | ψ x < ε / 3} ∩ Na,
    inter_mem (inter_mem hgn hψn) hNa, ?_⟩
  filter_upwards [hc.eventually (gt_mem_nhds hε3)] with j hj x hx
  rw [hfX j x hx.2]
  apply hεV
  have h1 := hXg j x hx.2
  have h2 : dist (g x) (g a) < ε / 3 := hx.1.1
  have h3 : ψ x < ε / 3 := hx.1.2
  calc dist (X j x) (g a) ≤ dist (X j x) (g x) + dist (g x) (g a) := dist_triangle _ _ _
    _ < ε := by rw [dist_eq_norm]; linarith

end Blend

/-- **Collar straightening from collar data** (the construction of A3-c). Given smooth collars
`cA`, `cB` with defining functions `rA`, `rB` and projections `πA`, `πB`, an embedding `e` of `∂B`
with a smooth retraction `ret`, and the data `g = (e ∘ πB ∘ h, rB ∘ h)`, `u = g (·, 0)` (an
immersion of `∂A`) and `w = ∂_t g (·, 0)` (with positive normal component), the straightened maps
`collarPush cB ret (straightenBlend rA (δ j) (M j) g) h rA δ'` are eventually `C¹`
diffeomorphisms, smooth near `∂A`. -/
theorem exists_diffeomorph_one_of_collar_data {n : ℕ}
    {A : Type*} [TopologicalSpace A] [ChartedSpace (EuclideanHalfSpace (n + 1)) A]
    [IsManifold (𝓡∂ (n + 1)) ∞ A] [CompactSpace A]
    {B : Type*} [TopologicalSpace B] [ChartedSpace (EuclideanHalfSpace (n + 1)) B]
    [IsManifold (𝓡∂ (n + 1)) ∞ B] [T2Space B]
    [CompactSpace (BoundaryManifold (𝓡∂ (n + 1)) A)] [T2Space (BoundaryManifold (𝓡∂ (n + 1)) A)]
    [Nonempty (BoundaryManifold (𝓡∂ (n + 1)) A)] [CompactSpace (BoundaryManifold (𝓡∂ (n + 1)) B)]
    {k : ℕ} (hk : 2 ≤ k) (h : A ≃ₘ^k⟮𝓡∂ (n + 1), 𝓡∂ (n + 1)⟯ B)
    {rA : A → ℝ} (hrA : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) ∞ rA) (hrA0 : ∀ x, 0 ≤ rA x)
    (hrAz : ∀ x, rA x = 0 ↔ (𝓡∂ (n + 1)).IsBoundaryPoint x)
    {aA : ℝ} [Fact ((0 : ℝ) < aA)]
    {cA : BoundaryManifold (𝓡∂ (n + 1)) A × Icc (0 : ℝ) aA → A}
    (hcA : ContMDiff ((HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))).prod (𝓡∂ 1))
      (𝓡∂ (n + 1)) ∞ cA)
    (hcA0 : ∀ p, cA (p, ⟨0, le_rfl, (Fact.out : (0 : ℝ) < aA).le⟩) = p)
    (hrcA : ∀ q, rA (cA q) = q.2.val)
    {πA : A → BoundaryManifold (𝓡∂ (n + 1)) A}
    (hπA : ContMDiffOn (𝓡∂ (n + 1)) (HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))) ∞ πA
      {x | rA x < aA})
    (hπcA : ∀ q : BoundaryManifold (𝓡∂ (n + 1)) A × Icc (0 : ℝ) aA, q.2.val < aA → πA (cA q) = q.1)
    (hcπA : ∀ x (hx : rA x < aA), cA (πA x, ⟨rA x, hrA0 x, hx.le⟩) = x)
    {rB : B → ℝ} (hrB : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) ∞ rB) (hrB0 : ∀ y, 0 ≤ rB y)
    (hrBz : ∀ y, rB y = 0 ↔ (𝓡∂ (n + 1)).IsBoundaryPoint y)
    {aB : ℝ} [Fact ((0 : ℝ) < aB)]
    {cB : BoundaryManifold (𝓡∂ (n + 1)) B × Icc (0 : ℝ) aB → B}
    (hcB : ContMDiff ((HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))).prod (𝓡∂ 1))
      (𝓡∂ (n + 1)) ∞ cB)
    (hcB0 : ∀ q, cB (q, ⟨0, le_rfl, (Fact.out : (0 : ℝ) < aB).le⟩) = q)
    (hrcB : ∀ q, rB (cB q) = q.2.val)
    {πB : B → BoundaryManifold (𝓡∂ (n + 1)) B}
    (hπB : ContMDiffOn (𝓡∂ (n + 1)) (HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))) ∞ πB
      {y | rB y < aB})
    (hπcB : ∀ q : BoundaryManifold (𝓡∂ (n + 1)) B × Icc (0 : ℝ) aB, q.2.val < aB → πB (cB q) = q.1)
    (hcπB : ∀ y (hy : rB y < aB), cB (πB y, ⟨rB y, hrB0 y, hy.le⟩) = y)
    {N : ℕ} {e : BoundaryManifold (𝓡∂ (n + 1)) B → EuclideanSpace ℝ (Fin N)}
    (he : ContMDiff (HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin N))
      ∞ e)
    {ret : EuclideanSpace ℝ (Fin N) → BoundaryManifold (𝓡∂ (n + 1)) B}
    {U : Set (EuclideanSpace ℝ (Fin N))} (hU : IsOpen U) (heU : range e ⊆ U)
    (hret : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin N))
      (HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))) ∞ ret U)
    (hrete : ∀ q, ret (e q) = q)
    {g : A → EuclideanSpace ℝ (Fin N) × ℝ} (hgdef : ∀ x, g x = (e (πB (h x)), rB (h x)))
    (hg : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin N) × ℝ) k g
      (h ⁻¹' {y | rB y < aB}))
    {u : BoundaryManifold (𝓡∂ (n + 1)) A → EuclideanSpace ℝ (Fin N)}
    (hudef : ∀ p, u p = e (πB (h p)))
    (hu : ContMDiff (HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin N))
      k u)
    (hui : ∀ p, Injective (mfderiv (HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) u p))
    {w : BoundaryManifold (𝓡∂ (n + 1)) A → EuclideanSpace ℝ (Fin N) × ℝ}
    (hw : ContMDiff (HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N) × ℝ) 1 w)
    (hwg : ∀ p, w p = derivWithin
      (fun t => g (cA (p, projIcc 0 aA (Fact.out : (0 : ℝ) < aA).le t))) (Icc 0 aA) 0)
    (hlam : ∀ p, 0 < (w p).2) :
    ∃ (h' : A ≃ₘ^1⟮𝓡∂ (n + 1), 𝓡∂ (n + 1)⟯ B) (O' : Set A), IsOpen O' ∧
      (𝓡∂ (n + 1)).boundary A ⊆ O' ∧ ContMDiffOn (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) ∞ h' O' := by
  have hk1 : (1 : ℕ∞ω) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hk0 : (k : ℕ∞ω) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have haA : (0 : ℝ) < aA := Fact.out
  have haB : (0 : ℝ) < aB := Fact.out
  have hπA0 : ∀ p : BoundaryManifold (𝓡∂ (n + 1)) A, πA p = p := fun p => by
    have h1 := hπcA (p, ⟨0, le_rfl, haA.le⟩) haA
    rwa [hcA0] at h1
  have hbdB : ∀ x, (𝓡∂ (n + 1)).IsBoundaryPoint x → rB (h x) = 0 := fun x hx =>
    (hrBz _).mpr ((Diffeomorph.isBoundaryPoint_apply_iff hk1 h).mpr hx)
  have hintB : ∀ x, 0 < rA x → 0 < rB (h x) := by
    intro x hx
    refine lt_of_le_of_ne (hrB0 _) (fun h0 => ?_)
    have hb := (hrBz _).mp h0.symm
    rw [Diffeomorph.isBoundaryPoint_apply_iff hk1 h] at hb
    exact hx.ne' ((hrAz x).mpr hb)
  have hg1 : ∀ x, (g x).1 = e (πB (h x)) := fun x => by rw [hgdef]
  have hg2 : ∀ x, (g x).2 = rB (h x) := fun x => by rw [hgdef]
  -- approximants (W1a) and constants
  obtain ⟨us, hus, husU, husC⟩ := exists_smooth_seq_chart_tendsto_of_contMDiff_normedSpace
    (I := HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))) k hu
  obtain ⟨ws₀, hws₀, hws₀U, hws₀C⟩ := exists_smooth_seq_chart_tendsto_of_contMDiff_normedSpace
    (I := HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))) 1 hw
  obtain ⟨lm, hlm, hlmle⟩ := DifferentialGeometry.Topology.exists_pos_lt_norm_of_isCompact
    (isCompact_univ (X := BoundaryManifold (𝓡∂ (n + 1)) A)) (hw.continuous.snd).continuousOn
    (fun p _ => (hlam p).ne')
  have hlm' : ∀ p, lm < (w p).2 := fun p => by
    have h1 := hlmle p (mem_univ _)
    rwa [Real.norm_eq_abs, abs_of_pos (hlam p)] at h1
  obtain ⟨Cw, hCw⟩ := (isCompact_range hw.continuous).isBounded.exists_norm_le
  have hCw' : ∀ p, ‖w p‖ ≤ Cw := fun p => hCw _ (mem_range_self p)
  have hCw0 : 0 ≤ Cw := (norm_nonneg _).trans (hCw' (Classical.arbitrary _))
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp
    (Metric.tendstoUniformly_iff.mp hws₀U (min 1 (lm / 2)) (lt_min one_pos (half_pos hlm)))
  have hwj : ∀ j p, ‖ws₀ (j + j₀) p - w p‖ ≤ min 1 (lm / 2) := fun j p => by
    rw [← dist_eq_norm, dist_comm]
    exact (hj₀ (j + j₀) (Nat.le_add_left _ _) p).le
  have hwb : ∀ j p, ‖ws₀ (j + j₀) p‖ ≤ Cw + 1 := fun j p => by
    calc ‖ws₀ (j + j₀) p‖ = ‖(ws₀ (j + j₀) p - w p) + w p‖ := by rw [sub_add_cancel]
      _ ≤ ‖ws₀ (j + j₀) p - w p‖ + ‖w p‖ := norm_add_le _ _
      _ ≤ 1 + Cw := add_le_add ((hwj j p).trans (min_le_left _ _)) (hCw' _)
      _ = Cw + 1 := add_comm _ _
  have hwpos : ∀ j p, 0 < (ws₀ (j + j₀) p).2 := fun j p => by
    have h1 : |(ws₀ (j + j₀) p).2 - (w p).2| ≤ lm / 2 := by
      have h2 : |(ws₀ (j + j₀) p - w p).2| ≤ ‖ws₀ (j + j₀) p - w p‖ := by
        rw [← Real.norm_eq_abs]
        exact norm_snd_le _
      rw [Prod.snd_sub] at h2
      exact h2.trans ((hwj j p).trans (min_le_right _ _))
    have h3 := hlm' p
    rw [abs_le] at h1
    linarith
  obtain ⟨ηU, hηU, hηUsub⟩ := (isCompact_range he.continuous).exists_cthickening_subset_open hU heU
  -- the collar width `δ'`
  obtain ⟨δ', hδ', hδ'aA, hδ'C, hδ'B, hδ'u⟩ : ∃ δ' > 0, δ' < aA ∧
      δ' * (Cw + 2) ≤ min (ηU / 3) (aB / 4) ∧ (∀ x, rA x < δ' → rB (h x) < aB / 2) ∧
      (∀ x, rA x < δ' → ‖u (πA x) - e (πB (h x))‖ < ηU / 3) := by
    have hW₀ : IsOpen ({x | rA x < aA} ∩ h ⁻¹' {y | rB y < aB / 2}) :=
      (isOpen_lt hrA.continuous continuous_const).inter
        ((isOpen_lt hrB.continuous continuous_const).preimage h.continuous)
    have hf₀ : ContinuousOn (fun x => ‖u (πA x) - e (πB (h x))‖)
        ({x | rA x < aA} ∩ h ⁻¹' {y | rB y < aB / 2}) := by
      have h1 : ContinuousOn (fun x => u (πA x)) ({x | rA x < aA} ∩ h ⁻¹' {y | rB y < aB / 2}) :=
        hu.continuous.comp_continuousOn (hπA.continuousOn.mono fun x hx => hx.1)
      have h2 : ContinuousOn (fun x => e (πB (h x)))
          ({x | rA x < aA} ∩ h ⁻¹' {y | rB y < aB / 2}) :=
        he.continuous.comp_continuousOn (hπB.continuousOn.comp h.continuous.continuousOn
          (fun x hx => (lt_of_lt_of_le hx.2 (half_le_self haB.le) : rB (h x) < aB)))
      exact (h1.sub h2).norm
    have hO₀ := hf₀.isOpen_inter_preimage hW₀ (isOpen_Iio (a := ηU / 3))
    have hbO₀ : (𝓡∂ (n + 1)).boundary A ⊆ ({x | rA x < aA} ∩ h ⁻¹' {y | rB y < aB / 2}) ∩
        (fun x => ‖u (πA x) - e (πB (h x))‖) ⁻¹' Iio (ηU / 3) := by
      intro x hx
      have hx0 : rA x = 0 := (hrAz x).mpr hx
      have hhx0 : rB (h x) = 0 := hbdB x hx
      refine ⟨⟨by change rA x < aA; rw [hx0]; exact haA, by
        change rB (h x) < aB / 2; rw [hhx0]; exact half_pos haB⟩, ?_⟩
      have hπ : ((πA x : BoundaryManifold (𝓡∂ (n + 1)) A) : A) = x :=
        congrArg Subtype.val (hπA0 ⟨x, hx⟩)
      change ‖u (πA x) - e (πB (h x))‖ < ηU / 3
      rw [hudef, hπ, sub_self, norm_zero]
      exact div_pos hηU three_pos
    obtain ⟨η₀, hη₀, hη₀O⟩ :=
      exists_pos_forall_le_mem_of_boundary_subset hrA.continuous hrAz hO₀ hbO₀
    have hpos : 0 < min η₀ (min (aA / 2) (min (ηU / 3) (aB / 4) / (Cw + 2))) :=
      lt_min hη₀ (lt_min (half_pos haA)
        (div_pos (lt_min (div_pos hηU three_pos) (div_pos haB four_pos)) (by linarith)))
    have hmem : ∀ x, rA x < min η₀ (min (aA / 2) (min (ηU / 3) (aB / 4) / (Cw + 2))) →
        x ∈ ({x | rA x < aA} ∩ h ⁻¹' {y | rB y < aB / 2}) ∩
          (fun x => ‖u (πA x) - e (πB (h x))‖) ⁻¹' Iio (ηU / 3) := fun x hx =>
      hη₀O x (by rw [abs_of_nonneg (hrA0 x)]; exact hx.le.trans (min_le_left _ _))
    refine ⟨_, hpos, lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _))
      (half_lt_self haA), ?_, fun x hx => (hmem x hx).1.2, fun x hx => (hmem x hx).2⟩
    have h1 : min η₀ (min (aA / 2) (min (ηU / 3) (aB / 4) / (Cw + 2))) ≤
        min (ηU / 3) (aB / 4) / (Cw + 2) := (min_le_right _ _).trans (min_le_right _ _)
    rwa [le_div_iff₀ (by linarith)] at h1
  have hδ'η : δ' ≤ ηU / 3 := by
    have h1 : δ' * (Cw + 2) ≤ ηU / 3 := hδ'C.trans (min_le_left _ _)
    nlinarith
  -- the scales and the reindexed boundary approximants
  obtain ⟨δ, hδpos, hδlt, hδlim⟩ : ∃ δ : ℕ → ℝ, (∀ j, 0 < δ j) ∧ (∀ j, δ j < δ') ∧
      Tendsto δ atTop (𝓝 0) := by
    refine ⟨fun j => δ' / (2 * ((j : ℝ) + 2)), fun j => div_pos hδ' (by positivity),
      fun j => ?_, ?_⟩
    · change δ' / (2 * ((j : ℝ) + 2)) < δ'
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    · have h1 : Tendsto (fun j : ℕ => 2 * ((j : ℝ) + 2)) atTop atTop :=
        Tendsto.const_mul_atTop two_pos (tendsto_atTop_add_const_right _ 2
          tendsto_natCast_atTop_atTop)
      have h2 := h1.inv_tendsto_atTop.const_mul δ'
      rw [mul_zero] at h2
      refine h2.congr (fun j => ?_)
      simp only [div_eq_mul_inv, Pi.inv_apply]
  obtain ⟨σ, hσ, hσP⟩ := Filter.extraction_forall_of_eventually
    (P := fun m kk => ∀ p, ‖us kk p - u p‖ ≤ δ m / (m + 1)) (fun m => by
      have h1 := Metric.tendstoUniformly_iff.mp husU (δ m / (m + 1))
        (div_pos (hδpos m) (by positivity))
      filter_upwards [h1] with kk hkk p
      rw [← dist_eq_norm, dist_comm]
      exact (hkk p).le)
  have hσP' : ∀ j p, ‖us (σ j) p - u p‖ ≤ δ j := fun j p =>
    (hσP j p).trans (div_le_self (hδpos j).le (by
      have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
      linarith))
  -- the straightened maps
  obtain ⟨M, hM⟩ : ∃ M : ℕ → A → EuclideanSpace ℝ (Fin N) × ℝ, ∀ j x,
      M j x = (us (σ j) (πA x), 0) + rA x • ws₀ (j + j₀) (πA x) := ⟨_, fun _ _ => rfl⟩
  have hXe : ∀ j x, straightenBlend rA (δ j) (M j) g x =
      ((us (σ j) (πA x), (0 : ℝ)) + rA x • ws₀ (j + j₀) (πA x)) + collarTransition (rA x / δ j) •
        (g x - ((us (σ j) (πA x), 0) + rA x • ws₀ (j + j₀) (πA x))) := fun j x => by
    simp only [straightenBlend, hM]
  have hX1 : ∀ j x, rA x < δ' → (straightenBlend rA (δ j) (M j) g x).1 ∈ U := by
    intro j x hx
    have h1 : dist (straightenBlend rA (δ j) (M j) g x).1 (g x).1 ≤ ηU := by
      rw [hXe]
      exact blend_fst_dist_le (collarTransition_mem_Icc _) (hrA0 x) hx (hwb j _)
        (hδ'C.trans (min_le_left _ _)) ((hσP' j _).trans ((hδlt j).le.trans hδ'η))
        (by rw [hg1]; exact (hδ'u x hx).le)
    exact hηUsub (Metric.mem_cthickening_of_dist_le _ _ _ _ ⟨πB (h x), (hg1 x).symm⟩ h1)
  have hX2 : ∀ j x, rA x < δ' → (straightenBlend rA (δ j) (M j) g x).2 ∈ Ico 0 aB ∧
      (0 < rA x → 0 < (straightenBlend rA (δ j) (M j) g x).2) := by
    intro j x hx
    rw [hXe]
    have h1 := blend_snd_mem (a := us (σ j) (πA x)) (w := ws₀ (j + j₀) (πA x)) (G := g x)
      (collarTransition_mem_Icc (rA x / δ j))
      (hrA0 x) hx (hwb j _) (hwpos j _) (hδ'C.trans (min_le_right _ _))
      (by rw [hg2]; exact hrB0 _) (by rw [hg2]; exact hδ'B x hx)
    exact ⟨h1.1, fun hpos => h1.2 hpos (by rw [hg2]; exact hintB x hpos)⟩
  have hXh : ∀ j x, 2 * δ j / 3 < rA x → rA x < δ' →
      cB (ret (straightenBlend rA (δ j) (M j) g x).1,
        projIcc 0 aB (Fact.out : (0 : ℝ) < aB).le (straightenBlend rA (δ j) (M j) g x).2) =
        h x := by
    intro j x hx1 hx2
    rw [straightenBlend_eq_target (hδpos j) hx1.le, hg1, hg2, hrete]
    have hrBh : rB (h x) < aB := lt_of_lt_of_le (hδ'B x hx2) (half_le_self haB.le)
    rw [projIcc_of_mem _ ⟨hrB0 _, hrBh.le⟩]
    exact hcπB (h x) hrBh
  -- regularity
  have hMs : ∀ j, ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin N) × ℝ) ∞ (M j)
      {x | rA x < aA} := by
    intro j
    rw [show M j = fun x => (us (σ j) (πA x), 0) + rA x • ws₀ (j + j₀) (πA x) from funext (hM j)]
    have h1 : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞
        (fun x => us (σ j) (πA x)) {x | rA x < aA} := (hus (σ j)).comp_contMDiffOn hπA
    have h2 : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin N) × ℝ) ∞
        (fun x => ws₀ (j + j₀) (πA x)) {x | rA x < aA} := (hws₀ (j + j₀)).comp_contMDiffOn hπA
    exact (h1.prodMk_space contMDiffOn_const).add (hrA.contMDiffOn.smul h2)
  have hgδ' : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin N) × ℝ) 1 g
      {x | rA x < δ'} :=
    (hg.of_le (by exact_mod_cast (by omega : 1 ≤ k))).mono fun x hx =>
      (lt_of_lt_of_le (hδ'B x hx) (half_le_self haB.le) : rB (h x) < aB)
  obtain ⟨f, hfdef⟩ : ∃ f : ℕ → A → B,
      ∀ j, f j = collarPush cB ret (straightenBlend rA (δ j) (M j) g) h rA δ' :=
    ⟨_, fun _ => rfl⟩
  have hreg : ∀ j, ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) 1 (f j) ∧
      ContMDiffOn (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) ∞ (f j) {x | rA x < min (δ j / 3) δ'} ∧
      ∀ x, 2 * δ j / 3 < rA x → f j x = h x := by
    intro j
    rw [hfdef]
    refine contMDiff_collarPush hcB hret (h.contMDiff.of_le hk1) hrA.continuous
      (δ₀ := δ j / 3) (δ₁ := 2 * δ j / 3) (by linarith [hδlt j, hδpos j])
      ?_ ?_ (fun x hx => hX1 j x hx) (fun x hx => Ico_subset_Icc_self (hX2 j x hx).1)
      (fun x hx1 hx2 => hXh j x hx1 hx2)
    · exact contMDiffOn_straightenBlend hrA (δ j)
        (((hMs j).of_le (by exact_mod_cast le_top)).mono fun x (hx : rA x < δ') =>
          (lt_trans hx hδ'aA : rA x < aA)) hgδ'
    · refine ((hMs j).mono fun x (hx : rA x < δ j / 3) => ?_).congr
        fun x (hx : rA x < δ j / 3) => straightenBlend_eq_model (hδpos j) hx.le
      exact (lt_trans hx (lt_trans (by linarith [hδpos j]) (lt_trans (hδlt j) hδ'aA)) :
        rA x < aA)
  have hfX : ∀ j x, rA x < δ' → f j x = cB (ret (straightenBlend rA (δ j) (M j) g x).1,
      projIcc 0 aB (Fact.out : (0 : ℝ) < aB).le (straightenBlend rA (δ j) (M j) g x).2) :=
    fun j x hx => by
      rw [hfdef]
      simp only [collarPush, hx, ite_true]
  -- boundary to boundary
  have hjbd : ∀ j x, rA x = 0 → rB (f j x) = 0 := by
    intro j x hx0
    have hX : straightenBlend rA (δ j) (M j) g x = M j x :=
      straightenBlend_eq_model (hδpos j) (by rw [hx0]; linarith [hδpos j])
    have hM2 : (M j x).2 = 0 := by
      rw [hM]
      simp [hx0]
    rw [hfX j x (by rw [hx0]; exact hδ'), hrcB, hX, hM2, projIcc_left]
  -- local pieces at boundary points (the analytic core)
  have hpieceB : ∀ p : BoundaryManifold (𝓡∂ (n + 1)) A, ∃ V ∈ 𝓝 (p : A), ∀ᶠ j in atTop,
      InjOn (f j) V ∧ ∀ x ∈ V, (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (f j) x).IsInvertible :=
    fun p => eventually_injOn_isInvertible_straighten hcA hcA0 hrA.continuous hrA0 hrcA
      hπA.continuousOn hπcA hcπA hrB hrcB hπB hπcB he hU heU hret hrete hδ' hδ'aA hgδ'
      (fun x _ => ⟨πB (h x), (hg1 x).symm⟩) (hu.of_le hk1) hui
      (fun p => by rw [hgdef, hudef, hbdB p p.2]) hw hwg hlam hδpos hδlim
      (us := fun j => us (σ j)) (fun j => hus (σ j)) (fun j p => hσP j p)
      (fun p K hK hKt => ((husC p K hK hKt).comp_subseq hσ).mono_order (by omega))
      (ws := fun j => ws₀ (j + j₀)) (fun j => hws₀ (j + j₀))
      (fun s hs => (tendsto_add_atTop_nat j₀).eventually (hws₀U s hs))
      (fun p K hK hKt => (hws₀C p K hK hKt).comp_subseq (fun a b hab => by omega))
      hM (fun j => (hreg j).1) hfX (fun j x hx => (hX2 j x hx).1) p
  -- locally uniform convergence `f j → h`
  have hfar : ∀ a, 0 < rA a → ∀ᶠ j in atTop, ∀ x, rA a / 2 < rA x → f j x = h x := by
    intro a ha
    filter_upwards [hδlim.eventually (gt_mem_nhds (half_pos ha))] with j hj1 x hx
    exact (hreg j).2.2 x (by linarith [hδpos j])
  have hLU : ∀ (a : A) (V : Set B), IsOpen V → h a ∈ V →
      ∃ N ∈ 𝓝 a, ∀ᶠ j in atTop, MapsTo (f j) N V := by
    intro a V hV haV
    by_cases ha : 0 < rA a
    · refine ⟨{x | rA a / 2 < rA x} ∩ h ⁻¹' V, inter_mem
        ((isOpen_lt continuous_const hrA.continuous).mem_nhds
          (by change rA a / 2 < rA a; linarith))
        ((hV.preimage h.continuous).mem_nhds haV), ?_⟩
      filter_upwards [hfar a ha] with j hj' x hx
      rw [hj' x hx.1]
      exact hx.2
    · have ha0 : rA a = 0 := le_antisymm (not_lt.mp ha) (hrA0 a)
      have hab : (𝓡∂ (n + 1)).IsBoundaryPoint a := (hrAz a).mp ha0
      have hrBa : rB (h a) = 0 := hbdB a hab
      have hOo : IsOpen ({x | rA x < aA} ∩ h ⁻¹' {y | rB y < aB}) :=
        (isOpen_lt hrA.continuous continuous_const).inter
          ((isOpen_lt hrB.continuous continuous_const).preimage h.continuous)
      have haO : a ∈ {x | rA x < aA} ∩ h ⁻¹' {y | rB y < aB} :=
        ⟨by change rA a < aA; rw [ha0]; exact haA, by
          change rB (h a) < aB; rw [hrBa]; exact haB⟩
      have hgc : ContinuousAt g a :=
        (hg.continuousOn.mono inter_subset_right).continuousAt (hOo.mem_nhds haO)
      have hπc : ContinuousAt πA a :=
        (hπA.continuousOn.mono inter_subset_left).continuousAt (hOo.mem_nhds haO)
      refine exists_eventually_mapsTo_of_collar_coord hcB.continuous hU hret.continuousOn
        (g := g) (h := h) (a := a) (heU ⟨πB (h a), (hg1 a).symm⟩) hgc ?_ (f := f)
        (X := fun j => straightenBlend rA (δ j) (M j) g) (Na := {x | rA x < δ'})
        ((isOpen_lt hrA.continuous continuous_const).mem_nhds
          (by change rA a < δ'; rw [ha0]; exact hδ'))
        (fun j x hx => hfX j x hx) hδlim
        (ψ := fun x => ‖((u (πA x), (0 : ℝ)) : EuclideanSpace ℝ (Fin N) × ℝ) - g x‖ +
          rA x * (Cw + 1)) ?_ ?_ ?_ hV haV
      · rw [hg1, hg2, hrete, projIcc_of_mem _ ⟨hrB0 _, by rw [hrBa]; exact haB.le⟩]
        exact hcπB (h a) (by rw [hrBa]; exact haB)
      · exact ((((hu.continuous.continuousAt.comp hπc).prodMk continuousAt_const).sub
          hgc).norm).add (hrA.continuous.continuousAt.mul continuousAt_const)
      · have hπ : ((πA a : BoundaryManifold (𝓡∂ (n + 1)) A) : A) = a :=
          congrArg Subtype.val (hπA0 ⟨a, hab⟩)
        change ‖((u (πA a), (0 : ℝ)) : EuclideanSpace ℝ (Fin N) × ℝ) - g a‖ +
          rA a * (Cw + 1) = 0
        rw [hudef, hπ, hgdef, hrBa, ha0, zero_mul, add_zero, sub_self, norm_zero]
      · intro j x hx
        have hx' : rA x < δ' := hx
        change ‖straightenBlend rA (δ j) (M j) g x - g x‖ ≤
          δ j + (‖((u (πA x), (0 : ℝ)) : EuclideanSpace ℝ (Fin N) × ℝ) - g x‖ + rA x * (Cw + 1))
        rw [hXe]
        refine (norm_blend_sub_le (collarTransition_mem_Icc _)).trans
          ((norm_model_sub_le _ (u (πA x)) _ _ (hrA0 x)).trans ?_)
        have h1 := hσP' j (πA x)
        have h2 : rA x * ‖ws₀ (j + j₀) (πA x)‖ ≤ rA x * (Cw + 1) :=
          mul_le_mul_of_nonneg_left (hwb j _) (hrA0 x)
        linarith
  -- all local pieces
  have hpiece : ∀ a : A, ∃ N : Set A, IsOpen N ∧ a ∈ N ∧ ∀ᶠ j in atTop,
      InjOn (f j) N ∧ ∀ x ∈ N, (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (f j) x).IsInvertible := by
    intro a
    by_cases ha : (𝓡∂ (n + 1)).IsBoundaryPoint a
    · obtain ⟨N, hN, hev⟩ := hpieceB ⟨a, ha⟩
      obtain ⟨t, htN, ht, hat⟩ := mem_nhds_iff.mp hN
      exact ⟨t, ht, hat, hev.mono fun j hj' => ⟨hj'.1.mono htN, fun x hx => hj'.2 x (htN hx)⟩⟩
    · have hpos : 0 < rA a := lt_of_le_of_ne (hrA0 a) (fun h0 => ha ((hrAz a).mp h0.symm))
      have hNo : IsOpen {x | rA a / 2 < rA x} := isOpen_lt continuous_const hrA.continuous
      refine ⟨{x | rA a / 2 < rA x}, hNo, by change rA a / 2 < rA a; linarith, ?_⟩
      filter_upwards [hfar a hpos] with j hj'
      refine ⟨fun x hx y hy hxy => h.injective (by rwa [hj' x hx, hj' y hy] at hxy),
        fun x hx => ?_⟩
      have heq : f j =ᶠ[𝓝 x] h := Filter.mem_of_superset (hNo.mem_nhds hx) fun y hy => hj' y hy
      rw [heq.mfderiv_eq]
      exact h.isInvertible_mfderiv hk0
  -- assembly
  obtain ⟨j, Φ, hΦ⟩ := (eventually_exists_diffeomorph_of_collar_pieces h.toHomeomorph (f := f)
    (fun j => (hreg j).1) hpiece hLU hrA.continuous hrA0 hrAz hrB.continuous hrB0 hrBz
    hcB.continuous hcB0 hrcB hcπB hjbd (δ := fun j => 2 * δ j / 3)
    (fun j x hx => (hreg j).2.2 x hx)
    (fun j x hx => hδ'B x (lt_of_le_of_lt hx (by linarith [hδlt j, hδpos j])))).exists
  refine ⟨Φ, {x | rA x < min (δ j / 3) δ'}, isOpen_lt hrA.continuous continuous_const, ?_, ?_⟩
  · intro x hx
    change rA x < min (δ j / 3) δ'
    rw [(hrAz x).mpr hx]
    exact lt_min (by linarith [hδpos j]) hδ'
  · rw [hΦ]
    exact (hreg j).2.1

/-- **A3-c (collar straightening).** A `C^k` diffeomorphism (`2 ≤ k`) of compact manifolds with
boundary (model `𝓡∂ (n + 1)`) can be replaced by a `C¹` diffeomorphism that is smooth on an open
neighbourhood of the boundary. -/
theorem exists_diffeomorph_one_smooth_near_boundary {n : ℕ}
    {A : Type} [TopologicalSpace A] [ChartedSpace (EuclideanHalfSpace (n + 1)) A]
    [IsManifold (𝓡∂ (n + 1)) ∞ A] [T2Space A] [CompactSpace A]
    {B : Type} [TopologicalSpace B] [ChartedSpace (EuclideanHalfSpace (n + 1)) B]
    [IsManifold (𝓡∂ (n + 1)) ∞ B]
    {k : ℕ} (hk : 2 ≤ k) (h : A ≃ₘ^k⟮𝓡∂ (n + 1), 𝓡∂ (n + 1)⟯ B) :
    ∃ (h' : A ≃ₘ^1⟮𝓡∂ (n + 1), 𝓡∂ (n + 1)⟯ B) (O' : Set A), IsOpen O' ∧
      (𝓡∂ (n + 1)).boundary A ⊆ O' ∧ ContMDiffOn (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) ∞ h' O' := by
  have hk1 : (1 : ℕ∞ω) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hk0 : (k : ℕ∞ω) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have : T2Space B := h.toHomeomorph.symm.isEmbedding.t2Space
  have : CompactSpace B := h.toHomeomorph.compactSpace
  set I := 𝓡∂ (n + 1) with hI
  set J := HasSmoothBoundary.boundaryModel I with hJ
  rcases isEmpty_or_nonempty (BoundaryManifold I A) with hA | hA
  · let h1 : A ≃ₘ^1⟮I, I⟯ B :=
      { toEquiv := h.toEquiv
        contMDiff_toFun := h.contMDiff.of_le hk1
        contMDiff_invFun := h.symm.contMDiff.of_le hk1 }
    refine ⟨h1, ∅, isOpen_empty, ?_, contMDiffOn_empty⟩
    intro x hx
    exact (hA.false ⟨x, hx⟩).elim
  have hB : Nonempty (BoundaryManifold I B) :=
    ⟨⟨h (Classical.arbitrary (BoundaryManifold I A)),
      (Diffeomorph.isBoundaryPoint_apply_iff hk1 h).mpr
        (Classical.arbitrary (BoundaryManifold I A)).2⟩⟩
  -- collars
  obtain ⟨rA', hrA, hrA0, hrAz, aA, haA, hcollA⟩ :=
    DifferentialGeometry.Manifold.Boundary.exists_definingFunction_sublevel_collar (n := n) (M := A)
  have : Fact ((0 : ℝ) < aA) := ⟨haA⟩
  obtain ⟨cA, -, hcA, hcA0, hrcA, -, YA, hYA, dA, hdA⟩ := hcollA
  obtain ⟨rB', hrB, hrB0, hrBz, aB, haB, hcollB⟩ :=
    DifferentialGeometry.Manifold.Boundary.exists_definingFunction_sublevel_collar (n := n) (M := B)
  have : Fact ((0 : ℝ) < aB) := ⟨haB⟩
  obtain ⟨cB, -, hcB, hcB0, hrcB, -, YB, hYB, dB, hdB⟩ := hcollB
  obtain ⟨πA, hπA, hπcA, hcπA⟩ := exists_collar_projection (n := n) (M := A) hrA0 hrcA _ rfl YA hYA dA hdA
  obtain ⟨πB, hπB, hπcB, hcπB⟩ := exists_collar_projection (n := n) (M := B) hrB0 hrcB _ rfl YB hYB dB hdB
  -- compact boundaries, embedding of `∂B` with a retraction
  have : CompactSpace (BoundaryManifold I A) :=
    isCompact_iff_compactSpace.mp (I.isClosed_boundary (n := ∞) (by simp)).isCompact
  have : CompactSpace (BoundaryManifold I B) :=
    isCompact_iff_compactSpace.mp (I.isClosed_boundary (n := ∞) (by simp)).isCompact
  obtain ⟨N, e, he, hemb, hei⟩ := exists_embedding_euclidean_of_compact (I := J)
    (M := BoundaryManifold I B)
  obtain ⟨ret, U, hU, heU, hret, hrete⟩ :=
    DifferentialGeometry.Geometry.exists_smooth_neighborhood_retraction he hemb.isEmbedding hei
  -- boundary points and the collars
  have hbdA : ∀ p : BoundaryManifold I A, rA' p = 0 := fun p => (hrAz p).mpr p.2
  have hbdB : ∀ q : BoundaryManifold I B, rB' q = 0 := fun q => (hrBz q).mpr q.2
  have hcA0' : ∀ p : BoundaryManifold I A, cA (p, ⟨0, le_rfl, haA.le⟩) = p := hcA0
  have hπA0 : ∀ p : BoundaryManifold I A, πA p = p := fun p => by
    have h1 := hπcA (p, ⟨0, le_rfl, haA.le⟩) haA
    rwa [hcA0'] at h1
  have hπB0 : ∀ q : BoundaryManifold I B, πB q = q := fun q => by
    have h1 := hπcB (q, ⟨0, le_rfl, haB.le⟩) haB
    rwa [hcB0] at h1
  have hhbd : ∀ p : BoundaryManifold I A, I.IsBoundaryPoint (h p) := fun p =>
    (Diffeomorph.isBoundaryPoint_apply_iff hk1 h).mpr p.2
  -- the target data `g` and the boundary data `u`, `w`
  set g : A → EuclideanSpace ℝ (Fin N) × ℝ := fun x => (e (πB (h x)), rB' (h x)) with hgdef
  set Og : Set A := h ⁻¹' {y | rB' y < aB} with hOgdef
  have hOg : IsOpen Og := (isOpen_lt rB'.continuous continuous_const).preimage h.continuous
  have hg : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin N) × ℝ) k g Og := by
    have h1 : ContMDiffOn I J k (fun x => πB (h x)) Og :=
      (hπB.of_le (by exact_mod_cast le_top)).comp h.contMDiff.contMDiffOn (fun x hx => hx)
    exact ((he.of_le (by exact_mod_cast le_top)).comp_contMDiffOn h1).prodMk_space
      ((hrB.of_le (by exact_mod_cast le_top)).comp h.contMDiff).contMDiffOn
  set u : BoundaryManifold I A → EuclideanSpace ℝ (Fin N) := fun p => e (πB (h p)) with hudef
  have hu : ContMDiff J 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) k u := by
    have h1 : ContMDiff J I k (fun p : BoundaryManifold I A => h p) :=
      h.contMDiff.comp ((boundaryInclusion_contMDiff (I := I) (M := A)).of_le
        (by exact_mod_cast le_top))
    have h2 : ContMDiff J J k (fun p : BoundaryManifold I A => πB (h p)) :=
      (hπB.of_le (by exact_mod_cast le_top)).comp_contMDiff h1 (fun p => by
        change rB' (h p) < aB
        rw [(hrBz _).mpr (hhbd p)]
        exact haB)
    exact (he.of_le (by exact_mod_cast le_top)).comp h2
  set w : BoundaryManifold I A → EuclideanSpace ℝ (Fin N) × ℝ := fun p =>
    derivWithin (fun t => g (cA (p, projIcc 0 aA haA.le t))) (Icc 0 aA) 0 with hwdef
  have hw : ContMDiff J 𝓘(ℝ, EuclideanSpace ℝ (Fin N) × ℝ) 1 w :=
    contMDiff_collar_derivWithin hcA hk hOg hg (fun p => by
      change rB' (h (cA (p, ⟨0, le_rfl, haA.le⟩))) < aB
      rw [hcA0', (hrBz _).mpr (hhbd p)]
      exact haB)
  -- collar curves
  have hcurveA : ∀ p : BoundaryManifold I A, ContMDiffOn 𝓘(ℝ, ℝ) I ∞
      (fun t => cA (p, projIcc 0 aA haA.le t)) (Icc 0 aA) := fun p =>
    hcA.comp_contMDiffOn (contMDiffOn_const.prodMk contMDiffOn_projIcc)
  have hcurveB : ∀ q : BoundaryManifold I B, ContMDiffOn 𝓘(ℝ, ℝ) I ∞
      (fun t => cB (q, projIcc 0 aB haB.le t)) (Icc 0 aB) := fun q =>
    hcB.comp_contMDiffOn (contMDiffOn_const.prodMk contMDiffOn_projIcc)
  have hrAd : ∀ x, I.IsBoundaryPoint x → mfderiv I 𝓘(ℝ, ℝ) rA' x ≠ 0 := by
    intro x hx
    have h1 := mfderiv_ne_zero_of_collar_curve haA
      (((hcurveA ⟨x, hx⟩) 0 (left_mem_Icc.2 haA.le)).mdifferentiableWithinAt (by simp))
      (r := rA') ((hrA.mdifferentiableAt (by simp)))
      (fun t ht => by simp [hrcA, projIcc_of_mem _ ht])
    have hx0 : cA (⟨x, hx⟩, projIcc 0 aA haA.le 0) = x := by
      rw [projIcc_left]; exact hcA0' ⟨x, hx⟩
    rw [hx0] at h1
    exact h1
  have hrBd : ∀ y, I.IsBoundaryPoint y → mfderiv I 𝓘(ℝ, ℝ) rB' y ≠ 0 := by
    intro y hy
    have h1 := mfderiv_ne_zero_of_collar_curve haB
      (((hcurveB ⟨y, hy⟩) 0 (left_mem_Icc.2 haB.le)).mdifferentiableWithinAt (by simp))
      (r := rB') ((hrB.mdifferentiableAt (by simp)))
      (fun t ht => by simp [hrcB, projIcc_of_mem _ ht])
    have hy0 : cB (⟨y, hy⟩, projIcc 0 aB haB.le 0) = y := by
      rw [projIcc_left]; exact hcB0 ⟨y, hy⟩
    rw [hy0] at h1
    exact h1
  have hlam : ∀ p, 0 < (w p).2 := by
    intro p
    have hγd : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I (fun t => cA (p, projIcc 0 aA haA.le t))
        (Icc 0 aA) 0 :=
      ((hcurveA p) 0 (left_mem_Icc.2 haA.le)).mdifferentiableWithinAt (by simp)
    have hγ0 : cA (p, projIcc 0 aA haA.le 0) = p := by rw [projIcc_left]; exact hcA0' p
    have hgd : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin N) × ℝ) g p := by
      have hpO : (p : A) ∈ Og := by
        change rB' (h p) < aB
        rw [(hrBz _).mpr (hhbd p)]
        exact haB
      exact ((hg.contMDiffAt (hOg.mem_nhds hpO)).mdifferentiableAt
        (by exact_mod_cast (show k ≠ 0 by omega)))
    have hd : DifferentiableWithinAt ℝ (fun t => g (cA (p, projIcc 0 aA haA.le t))) (Icc 0 aA) 0 := by
      have h1 : MDifferentiableWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin N) × ℝ)
          (fun t => g (cA (p, projIcc 0 aA haA.le t))) (Icc 0 aA) 0 := by
        have hgd' : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin N) × ℝ) g
            (cA (p, projIcc 0 aA haA.le 0)) := by rw [hγ0]; exact hgd
        exact hgd'.comp_mdifferentiableWithinAt (0 : ℝ) hγd
      exact mdifferentiableWithinAt_iff_differentiableWithinAt.mp h1
    have hsnd : (w p).2 = derivWithin (fun t => rB' (h (cA (p, projIcc 0 aA haA.le t))))
        (Icc 0 aA) 0 := by
      have h1 := ((ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin N)) ℝ).hasFDerivAt
        (x := g (cA (p, projIcc 0 aA haA.le 0)))).comp_hasDerivWithinAt (0 : ℝ)
          hd.hasDerivWithinAt
      exact (h1.derivWithin (uniqueDiffOn_Icc haA 0 (left_mem_Icc.2 haA.le))).symm
    rw [hsnd]
    have := pos_derivWithin_comp_of_collar_curve hk1 h haA hγd (by rw [hγ0]; exact p.2)
      (hrA.of_le (by exact_mod_cast le_top)) hrA0 (fun x hx => (hrAz x).mpr hx) hrAd
      (fun t ht => by simp [hrcA, projIcc_of_mem _ ht])
      (hrB.of_le (by exact_mod_cast le_top)) hrB0 (fun y hy => (hrBz y).mpr hy) hrBd
    exact this
  -- the immersion `u = e ∘ h|∂`
  have hk' : (k : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  have hub : u = e ∘ Diffeomorph.boundaryRestrict hk1 hk' h := by
    funext p
    change e (πB (h p)) = e (Diffeomorph.boundaryRestrict hk1 hk' h p)
    rw [← hπB0 (Diffeomorph.boundaryRestrict hk1 hk' h p)]
    rfl
  have hui : ∀ p, Injective (mfderiv J 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) u p) := by
    intro p
    have hbdd : MDifferentiableAt J J (Diffeomorph.boundaryRestrict hk1 hk' h) p :=
      ((Diffeomorph.boundaryRestrict hk1 hk' h).contMDiff p).mdifferentiableAt hk0
    have hed : MDifferentiableAt J 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) e
        (Diffeomorph.boundaryRestrict hk1 hk' h p) :=
      (he _).mdifferentiableAt (by simp)
    rw [hub, mfderiv_comp p hed hbdd]
    obtain ⟨e', he'⟩ := (Diffeomorph.boundaryRestrict hk1 hk' h).isInvertible_mfderiv hk0 (x := p)
    rw [ContinuousLinearMap.coe_comp]
    refine (hei _).comp ?_
    rw [← he']
    exact e'.injective
  exact exists_diffeomorph_one_of_collar_data hk h hrA hrA0 hrAz hcA hcA0' hrcA hπA hπcA hcπA
    hrB hrB0 hrBz hcB hcB0 hrcB hπB hπcB hcπB he hU heU hret hrete (g := g) (fun x => rfl) hg
    (u := u) (fun p => rfl) hu hui (w := w) hw (fun p => rfl) hlam

end DifferentialGeometry.Topology.Manifold.SmoothApproximation
