import DifferentialGeometry.Geometry.Fibration.ActualFirstGraphTags

/-!
# TCP05: the own, scale and unlisted blocks of `R_i⁻¹𝓔⁰` near a point of `D_i`

Blueprint `master207B.tex`, TCP05 (B:5537–5594): "Use the own block `(a, 1)`, the constant scale
coordinate `1` ... Unlisted model blocks are zero." and "On the entire original set `|η_i| ≤ 8`
... its own block is exactly `(η_i, 1)`, including its derivative"; "the scale-coordinate error is
at most `10Λ`" (`σ = ρ/R_i`, `|σ − 1| ≤ 10Λ`, `|Dσ| ≤ Λ` on `D_i`).

* `tg_own_tag_KA7`: on `{|η_i| ≤ 8} ∩ B(i, 200R)` the own block of `R⁻¹𝓔⁰` is `(η_i, 1)` and its
  derivative is that of `a ↦ (a, 1)` along `dη_i` (no error: the bump plateau, closed by
  continuity).
* `tg_scale_tag_KA7`: the scale block `(0, ρ)`: value error `|ρ/R − 1| ≤ 10Λ` on `D_i`, derivative
  `R⁻¹|dρ(w)| ≤ Λ|w|` (`|w|` of `R⁻²g`) against the constant model block `(0, 1)`.
* `tg_unlisted_tag_KA7`: a block whose cutoff has `x` outside its closed support vanishes at `x`
  together with its derivative.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis DifferentialGeometry.Analysis.Calculus GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The scalar action on a block `ℓ²(ℝ² × ℝ)` is continuous (given directly: the instance search
for it times out). -/
local instance instContinuousSMulPlaneBlock_KA7S : ContinuousSMul ℝ (WithLp 2 (ℝ² × ℝ)) :=
  IsBoundedSMul.continuousSMul

section Plateau

/-- On the plateau `‖v‖ ≤ 8` the unit-scale circle block `scaledCutoffBlock 1 ψ` is `(v, 1)`. -/
theorem scaledCutoffBlock_one_eq_KA7 {v : ℝ²} (hv : ‖v‖ ≤ 8) :
    scaledCutoffBlock 1 (circleCutoffBump_LC87 : ℝ² → ℝ) v = WithLp.toLp 2 (v, 1) := by
  have h1 : circleCutoffBump_LC87 v = 1 :=
    circleCutoffBump_LC87.one_of_mem_closedBall (mem_closedBall_zero_iff.mpr hv)
  rw [scaledCutoffBlock, inv_one, one_smul, h1, one_smul, mul_one]

/-- On the plateau `‖v‖ ≤ 8` the derivative of `scaledCutoffBlock 1 ψ` is that of `a ↦ (a, 1)`
(equal on the open ball, closed by continuity of both derivatives). -/
theorem fderiv_scaledCutoffBlock_one_eq_KA7 {v : ℝ²} (hv : ‖v‖ ≤ 8) :
    fderiv ℝ (scaledCutoffBlock 1 (circleCutoffBump_LC87 : ℝ² → ℝ)) v =
      fderiv ℝ (fun a : ℝ² => (WithLp.toLp 2 (a, (1 : ℝ)) : WithLp 2 (ℝ² × ℝ))) v := by
  have hc1 : Continuous (fderiv ℝ (scaledCutoffBlock 1 (circleCutoffBump_LC87 : ℝ² → ℝ))) :=
    ((contDiff_scaledCutoffBlock circleCutoffBump_LC87.contDiff 1).of_le
      (by simp : (1 : WithTop ℕ∞) ≤ ∞)).continuous_fderiv (by simp)
  have hc2 : Continuous
      (fderiv ℝ (fun a : ℝ² => (WithLp.toLp 2 (a, (1 : ℝ)) : WithLp 2 (ℝ² × ℝ)))) :=
    (tcp_own_bounds_KA6.1.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).continuous_fderiv (by simp)
  have hclosed : IsClosed {v : ℝ² |
      fderiv ℝ (scaledCutoffBlock 1 (circleCutoffBump_LC87 : ℝ² → ℝ)) v =
        fderiv ℝ (fun a : ℝ² => (WithLp.toLp 2 (a, (1 : ℝ)) : WithLp 2 (ℝ² × ℝ))) v} :=
    isClosed_eq hc1 hc2
  have hball : ball (0 : ℝ²) 8 ⊆ {v : ℝ² |
      fderiv ℝ (scaledCutoffBlock 1 (circleCutoffBump_LC87 : ℝ² → ℝ)) v =
        fderiv ℝ (fun a : ℝ² => (WithLp.toLp 2 (a, (1 : ℝ)) : WithLp 2 (ℝ² × ℝ))) v} := by
    intro y hy
    have hev : scaledCutoffBlock 1 (circleCutoffBump_LC87 : ℝ² → ℝ) =ᶠ[𝓝 y]
        fun a : ℝ² => (WithLp.toLp 2 (a, (1 : ℝ)) : WithLp 2 (ℝ² × ℝ)) := by
      filter_upwards [isOpen_ball.mem_nhds hy] with z hz
      exact scaledCutoffBlock_one_eq_KA7 (mem_closedBall_zero_iff.mp (ball_subset_closedBall hz))
    exact hev.fderiv_eq
  have hcl : closedBall (0 : ℝ²) 8 ⊆ {v : ℝ² |
      fderiv ℝ (scaledCutoffBlock 1 (circleCutoffBump_LC87 : ℝ² → ℝ)) v =
        fderiv ℝ (fun a : ℝ² => (WithLp.toLp 2 (a, (1 : ℝ)) : WithLp 2 (ℝ² × ℝ))) v} := by
    rw [← closure_ball (0 : ℝ²) (by norm_num : (8 : ℝ) ≠ 0)]
    exact closure_minimal hball hclosed
  exact hcl (mem_closedBall_zero_iff.mpr hv)

end Plateau

section Generic

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

/-- **An unlisted block**: if `x` is outside the closed support of the cutoff of the tag `t`, the
block of `𝓔⁰` vanishes at `x` and has zero derivative there. -/
theorem tg_unlisted_tag_KA7
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) {t : CGPTag L Z} {x : X}
    (hx : x ∉ tsupport (cgpCutoff L Z t)) :
    cgpGlobalMap L Z x t = 0 ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x, mvfderiv 𝓘(ℝ, E3) (fun y => cgpGlobalMap L Z y t) x w = 0 := by
  refine ⟨?_, fun w => mvfderiv_block_eq_zero_of_notMem_tsupport hx w⟩
  change blockMap (cgpRadius L Z) (cgpCutoff L Z) (cgpCoord L Z) x t = 0
  rw [blockMap_apply, image_eq_zero_of_notMem_tsupport hx, mul_zero, zero_smul]
  rfl

/-- The scale block of `𝓔⁰` is `(0, ρ)`. -/
theorem cgpGlobalMap_scale_eq_KA7
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (y : X) :
    cgpGlobalMap L Z y (cgpScaleTag L Z) = WithLp.toLp 2 (0, ρ y) := by
  change WithLp.toLp 2 ((ρ y * 1) • (0 : ℝ²), ρ y * 1) = _
  rw [smul_zero, mul_one]

/-- **The scale block at a point of `D_i`** (`ρ` smooth and `Λ`-Lipschitz): value error
`|ρ(x)/R − 1| ≤ 10Λ` against the constant `(0, 1)`, and derivative `R⁻¹|dρ(w)| ≤ Λ|w|` (`|w|` of
`R⁻²g`, `R = ρ(i)`). -/
theorem tg_scale_tag_KA7
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (hΛ : 0 ≤ Λ) {i x : X}
    (hx : x ∈ ball i (10 * ρ i)) :
    ‖(ρ i)⁻¹ • cgpGlobalMap L Z x (cgpScaleTag L Z) - WithLp.toLp 2 (0, 1)‖ ≤ 10 * Λ ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (fun y => cgpGlobalMap L Z y (cgpScaleTag L Z)) x w‖ ≤
          Λ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  have hri := hρ i
  have hlip : ∀ y z : X, |ρ y - ρ z| ≤ Λ * dist y z := by
    intro y z
    have h := L.lipschitz_scale.dist_le_mul y z
    rwa [Real.coe_toNNReal _ hΛ, Real.dist_eq] at h
  have hsm : ∀ (c : ℝ) (t : ℝ),
      c • (WithLp.toLp 2 ((0 : ℝ²), t) : WithLp 2 (ℝ² × ℝ)) = WithLp.toLp 2 (0, c * t) := by
    intro c t
    change WithLp.toLp 2 (c • (0 : ℝ²), c * t) = _
    rw [smul_zero]
  obtain ⟨J, hJ⟩ : ∃ J : ℝ →L[ℝ] WithLp 2 (ℝ² × ℝ), ∀ t, J t = WithLp.toLp 2 (0, t) :=
    ⟨(WithLp.prodContinuousLinearEquiv 2 ℝ ℝ² ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inr ℝ ℝ² ℝ), fun t => rfl⟩
  refine ⟨?_, fun w => ?_⟩
  · rw [cgpGlobalMap_scale_eq_KA7, hsm]
    have he : (WithLp.toLp 2 ((0 : ℝ²), (ρ i)⁻¹ * ρ x) : WithLp 2 (ℝ² × ℝ)) -
        WithLp.toLp 2 (0, 1) = WithLp.toLp 2 (0, (ρ i)⁻¹ * ρ x - 1) := by
      rw [← WithLp.toLp_sub]
      simp
    rw [he, WithLp.norm_toLp_snd, Real.norm_eq_abs]
    have hq : (ρ i)⁻¹ * ρ x - 1 = (ρ x - ρ i) / ρ i := by field_simp
    rw [hq, abs_div, abs_of_pos hri, div_le_iff₀ hri]
    have hd : dist x i < 10 * ρ i := mem_ball.mp hx
    have := hlip x i
    nlinarith
  · have hρd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ρ x :=
      L.contMDiff_scale.mdifferentiableAt (by simp)
    have hfun : (fun y => cgpGlobalMap L Z y (cgpScaleTag L Z)) = fun y => J (ρ y) := by
      funext y
      rw [cgpGlobalMap_scale_eq_KA7, hJ]
    have hd : mvfderiv 𝓘(ℝ, E3) (fun y => J (ρ y)) x w = J (mvfderiv 𝓘(ℝ, E3) ρ x w) :=
      mvfderiv_comp_hasFDerivAt hρd J.hasFDerivAt w
    rw [hfun, hd, hJ, hsm, WithLp.norm_toLp_snd, Real.norm_eq_abs, abs_mul,
      abs_of_pos (inv_pos.mpr hri)]
    have hb := abs_mvfderiv_le_of_lipschitzOn_riem g hmetric isOpen_univ (mem_univ x) hρd
      (fun y _ z _ => hlip y z) w
    have hsq : Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) = (ρ i)⁻¹ * Real.sqrt (g.inner x w w) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_pos.mpr hri).le]
    rw [hsq]
    calc (ρ i)⁻¹ * |mvfderiv 𝓘(ℝ, E3) ρ x w| ≤ (ρ i)⁻¹ * (Λ * Real.sqrt (g.inner x w w)) :=
          mul_le_mul_of_nonneg_left hb (inv_pos.mpr hri).le
      _ = Λ * ((ρ i)⁻¹ * Real.sqrt (g.inner x w w)) := by ring

end Generic

section Own

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_TCP05_KA7
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_TCP05_KA7
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_TCP05_KA7
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **The own block** at a point `x ∈ B(i, 200R)` with `|η_i(x)| ≤ 8`: `R⁻¹𝓔⁰(x)` has own block
exactly `(η_i(x), 1)`, and its derivative along `w` is the derivative of `a ↦ (a, 1)` along
`dη_i(w)` (no error). -/
theorem tg_own_tag_KA7
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    {i : X} (hi : i ∈ P.circle.centres) (j : P.circle.finite_centres.toFinset) (hji : j.1 = i)
    {x : X} (hxi : x ∈ ball i (200 * ρ i))
    (h8 : ‖cgpCircleCoord P.toLocalChartFamily i hi x‖ ≤ 8) :
    (ρ i)⁻¹ • cgpGlobalMap P.toLocalChartFamily P.zero x (.inl j) =
        WithLp.toLp 2 (cgpCircleCoord P.toLocalChartFamily i hi x, 1) ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        (ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3)
            (fun y => cgpGlobalMap P.toLocalChartFamily P.zero y (.inl j)) x w =
          fderiv ℝ (fun a : ℝ² => (WithLp.toLp 2 (a, (1 : ℝ)) : WithLp 2 (ℝ² × ℝ)))
            (cgpCircleCoord P.toLocalChartFamily i hi x)
            (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w) := by
  obtain ⟨j, hjmem⟩ := j
  change j = i at hji
  subst hji
  have hri := hρ j
  set η := cgpCircleCoord P.toLocalChartFamily j hi with hη
  set G := scaledCutoffBlock 1 (circleCutoffBump_LC87 : ℝ² → ℝ) with hG
  have hf : (fun y => cgpGlobalMap P.toLocalChartFamily P.zero y (.inl ⟨j, hjmem⟩)) =ᶠ[𝓝 x]
      fun y => ρ j • G (η y) := by
    filter_upwards [circle_cutoff_eventuallyEq_KA2 P.toLocalChartFamilyE.toLocalChartFamilyQ hi
      hxi] with y hy
    have h := cgpGlobalMap_circle_eq_KA6 P ⟨j, hjmem⟩ hri hy
    rw [h, div_self hri.ne', one_smul]
  have hηd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) η x :=
    ((cgpCircleCoord_contMDiffOn P.toLocalChartFamily hi).contMDiffAt
      (isOpen_ball.mem_nhds hxi)).mdifferentiableAt (by simp)
  have hGd : Differentiable ℝ G :=
    (contDiff_scaledCutoffBlock (n := 1) circleCutoffBump_LC87.contDiff 1).differentiable
      one_ne_zero
  have hφ : HasFDerivAt (fun z => ρ j • G z) (ρ j • fderiv ℝ G (η x)) (η x) :=
    (hGd (η x)).hasFDerivAt.const_smul (ρ j)
  refine ⟨?_, fun w => ?_⟩
  · rw [hf.eq_of_nhds, smul_smul, inv_mul_cancel₀ hri.ne', one_smul, hG]
    exact scaledCutoffBlock_one_eq_KA7 h8
  · rw [mvfderiv_apply_congr_KA2 hf w, mvfderiv_comp_hasFDerivAt hηd hφ w]
    change (ρ j)⁻¹ • (ρ j • fderiv ℝ G (η x) (mvfderiv 𝓘(ℝ, E3) η x w)) = _
    rw [smul_smul, inv_mul_cancel₀ hri.ne', one_smul, hG, fderiv_scaledCutoffBlock_one_eq_KA7 h8]

end Own

end DifferentialGeometry.Geometry.Collapse
