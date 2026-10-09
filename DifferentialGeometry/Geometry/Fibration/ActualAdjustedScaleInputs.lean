import DifferentialGeometry.Geometry.Fibration.ActualStageOneCutoff
import DifferentialGeometry.Geometry.Fibration.ActualFullMarkerContributors
import DifferentialGeometry.Geometry.Fibration.ActualAdjustmentChoiceApplications
import DifferentialGeometry.Geometry.Collapse.EdgeDisk.AdjustedScale
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsResidualApplications

/-!
# EDP01's inputs on the original map `𝓔⁰`: the cutoff `χ = ψ₁ ∘ 𝓔⁰` and the contributor scales

Blueprint `master207B.tex`, EDP01 (`lem:fibration-actual-adjusted-scale-derivative`, B:6666–6746),
the parts of its proof that involve only the original map `F = 𝓔⁰ = cgpGlobalMap` and rows already
in the tree (no stage map, no adjusted map `E`):

* `edp01_cutoff_GAFS`: "Write `χ = ψ₁ ∘ F` … CFS31 gives `‖Dχ‖ ≤ b_cut L₀/ρ`": on the manifold,
  `χ` is smooth, `[0,1]`-valued, one on the circle cores `|η_i| < 6`, its closed support lies in
  the circle charts with `|η_i| ≤ 13/2` ("CFS31 supplies an original circle index `i` with
  `|η_i(p)| ≤ 6.5`") and `|dχ(v)| ≤ (b_cut L₀/ρ) |v|_g` with GAF01's `b_cut = gafCutoffConstant`,
  `L₀ = gafDerivativeBound` (from `gaf02_stageOne_sourceCutoff` and `gaf01_derivative_bound`).
* `edp01_contributor_scale_GAFS`, (SC): at `x = F(p)` with `|η_i(p)| ≤ 7`, EVERY first-cloud point
  `F(q)`, `q ∈ Ã₁`, whose closed `80br` ball meets `B(x, 8br_x)` has `|ρ(q) − R_i| ≤ 10ΛR_i`, and
  `|ρ(p) − R_i| ≤ 10ΛR_i` ("Its original preimage has `|η_i| < 7.2` and therefore lies in
  `B(p_i, 10R_i)` by TCP01 … The point `p` lies in the same ball"): GAF04 (`gaf04_circle`), TCP01's
  enclosure (`LocalChartPacketsR.dist_lt_of_norm_coord_le`) and LC02's Lipschitz scale.
* `edp01_mean_value_GAFS`: a convex combination of contributor scales is within `20ΛR_i ≤
  (80/3)Λρ(p)` of `ρ(p)` (the value half of `|z_ρ − ρ| ≤ (80/3)Λρ`, via (SM)).
* `edp01_mean_deriv_GAFS`, (SW): for weights with CFS12's properties on the reference ball
  (`∑ w_y = 1` near the point, `‖Dw_y‖ ≤ c_w/r_x`, `r_x = Σρ(p)`), the derivative of the weighted
  mean of the contributor scales has norm at most `|J| · (40c_w/(3Σ)) Λ`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricNAS_GAFS
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedNAS_GAFS
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricCAS_GAFS
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- The model metrics of `LocalChartPacketsR`, as a named local instance. -/
local instance instMetricNRAS_GAFS
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsR`, as a named local instance. -/
local instance instChartedNRAS_GAFS
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsR`, as a named local instance. -/
local instance instMetricCRAS_GAFS
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **EDP01's cutoff** `χ = ψ₁ ∘ 𝓔⁰` on the manifold: smooth, `[0,1]`-valued, one on the circle
cores `|η_i| < 6`, closed support in the circle charts with `|η_i| ≤ 13/2`, and
`|dχ(v)| ≤ (b_cut L₀/ρ) |v|_g` (CFS31's `‖Dχ‖ ≤ b_cut L₀/ρ`, `b_cut = gafCutoffConstant`,
`L₀ = gafDerivativeBound`). -/
theorem edp01_cutoff_GAFS
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (hσc : σc ∈ Icc (0 : ℝ) 1) (hγc : γc ∈ Icc (0 : ℝ) 1) (hεr : εr ∈ Icc (0 : ℝ) 1) :
    let χ : X → ℝ := fun p => markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1)
      (gafCircleVector P) (gafCircleMarker P) (cgpGlobalMap P.toLocalChartFamily P.zero p)
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ χ ∧ (∀ p, χ p ∈ Icc (0 : ℝ) 1) ∧
      (∀ p, (∃ j : P.circle.finite_centres.toFinset, p ∈ ball j.1 (200 * ρ j.1) ∧
          ‖cgpCoord P.toLocalChartFamily P.zero (.inl j) p‖ < 6) → χ p = 1) ∧
      (∀ p ∈ tsupport χ, ∃ j : P.circle.finite_centres.toFinset, p ∈ ball j.1 (200 * ρ j.1) ∧
          ‖cgpCoord P.toLocalChartFamily P.zero (.inl j) p‖ ≤ 13 / 2) ∧
      ∀ p (v : TangentSpace 𝓘(ℝ, E3) p),
        |mvfderiv 𝓘(ℝ, E3) χ p v| ≤
          gafCutoffConstant * gafDerivativeBound / ρ p * Real.sqrt (g.inner p v v) := by
  intro χ
  obtain ⟨hψs, hψ01, hψ1, hψsupp, hψd⟩ :=
    gaf02_stageOne_sourceCutoff P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1
  obtain ⟨hF, hFd⟩ := gaf01_derivative_bound P hΛ hΔ hμ hτ hLΛ hLmax he hT
    ⟨hσs, by linarith⟩ hσc hγc hεr
  set F := cgpGlobalMap P.toLocalChartFamily P.zero with hFdef
  set ψ := markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
    (gafCircleMarker P) with hψdef
  have hχ : χ = ψ ∘ F := rfl
  refine ⟨?_, fun p => hψ01 (F p), fun p hp => hψ1 p hp, fun p hp => ?_, fun p v => ?_⟩
  · rw [hχ]
    exact hψs.comp_contMDiff hF
  · rw [hχ] at hp
    exact hψsupp p (tsupport_comp_subset_preimage ψ hF.continuous hp)
  · have hψp : DifferentiableAt ℝ ψ (F p) :=
      (hψs.differentiable (by simp)).differentiableAt
    have hchain : mvfderiv 𝓘(ℝ, E3) χ p v = fderiv ℝ ψ (F p) (mvfderiv 𝓘(ℝ, E3) F p v) := by
      rw [hχ, mvfderiv_comp_apply p hψp.mdifferentiableAt (hF.mdifferentiableAt (by simp)) v,
        mvfderiv_eq_fderiv]
      rfl
    rw [hchain, ← Real.norm_eq_abs]
    have hb : 0 ≤ gafCutoffConstant / ρ p := (norm_nonneg _).trans (hψd p)
    calc ‖fderiv ℝ ψ (F p) (mvfderiv 𝓘(ℝ, E3) F p v)‖
        ≤ ‖fderiv ℝ ψ (F p)‖ * ‖mvfderiv 𝓘(ℝ, E3) F p v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ gafCutoffConstant / ρ p * (gafDerivativeBound * Real.sqrt (g.inner p v v)) :=
          mul_le_mul (hψd p) (hFd p v) (norm_nonneg _) hb
      _ = gafCutoffConstant * gafDerivativeBound / ρ p * Real.sqrt (g.inner p v v) := by ring

/-- LC02's scale is `Λ`-Lipschitz: `|ρ(q) − ρ(i)| ≤ Λ d(q, i)`. -/
theorem abs_scale_sub_le_GAFS
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (q i : X) : |ρ q - ρ i| ≤ Λ * dist q i := by
  have h := P.lipschitz_scale.dist_le_mul q i
  rwa [Real.coe_toNNReal _ hΛ, Real.dist_eq] at h

/-- TCP01's enclosure in the notation of CGP01: `|η_i(q)| ≤ 8` on `B(c_i, 200R_i)` gives
`|ρ(q) − R_i| ≤ 10ΛR_i`. -/
theorem abs_scale_sub_le_of_coord_GAFS
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (i : P.circle.finite_centres.toFinset) {q : X}
    (hq : q ∈ ball i.1 (200 * ρ i.1))
    (hη : ‖cgpCoord P.toLocalChartFamily P.zero (.inl i) q‖ ≤ 8) :
    |ρ q - ρ i.1| ≤ 10 * Λ * ρ i.1 := by
  have hi := (Set.Finite.mem_toFinset _).mp i.2
  have hd : dist q i.1 < 10 * ρ i.1 :=
    LocalChartPacketsR.dist_lt_of_norm_coord_le P hi (mem_ball.mp hq) hη
  calc |ρ q - ρ i.1| ≤ Λ * dist q i.1 := abs_scale_sub_le_GAFS P hΛ q i.1
    _ ≤ Λ * (10 * ρ i.1) := mul_le_mul_of_nonneg_left hd.le hΛ
    _ = 10 * Λ * ρ i.1 := by ring

/-- **EDP01 (SC)** on the first cloud: at `x = 𝓔⁰(p)` with `|η_i(p)| ≤ 7` on `B(c_i, 200R_i)`,
every first-cloud point `𝓔⁰(q)`, `q ∈ Ã₁`, whose closed `80bΣρ(q)` ball meets `B(x, 8bΣρ(p))`
has `|ρ(q) − R_i| ≤ 10ΛR_i`; also `|ρ(p) − R_i| ≤ 10ΛR_i` (`b = εc⁻¹`, `Σ ≤ εc/10000`). -/
theorem edp01_contributor_scale_GAFS
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) {εc σ : ℝ} (hε : 0 < εc)
    (hσ : 0 ≤ σ) (hσε : σ ≤ εc / 10000) (i : P.circle.finite_centres.toFinset) {px pu : X}
    (hpxi : px ∈ ball i.1 (200 * ρ i.1))
    (hηx : ‖cgpCoord P.toLocalChartFamily P.zero (.inl i) px‖ ≤ 7)
    (hpu : pu ∈ fc04Set P.toLocalChartFamily P.zero 8)
    (hmeet : (closedBall (cgpGlobalMap P.toLocalChartFamily P.zero pu) (80 * εc⁻¹ * (σ * ρ pu)) ∩
      ball (cgpGlobalMap P.toLocalChartFamily P.zero px) (8 * εc⁻¹ * (σ * ρ px))).Nonempty) :
    |ρ pu - ρ i.1| ≤ 10 * Λ * ρ i.1 ∧ |ρ px - ρ i.1| ≤ 10 * Λ * ρ i.1 := by
  have hΔ0 : 0 < Δ := by linarith
  obtain ⟨-, hηu, hmu⟩ := gaf04_circle P.toLocalChartFamilyQ P.zero hΔ hΛ hsmall hε hσ hσε i hpxi
    hηx hpu hmeet
  have hcut : P.circle.cutoff i.1 pu ≠ 0 := by
    intro h0
    have h := hmu
    change ρ i.1 * P.circle.cutoff i.1 pu = ρ i.1 at h
    rw [h0, mul_zero] at h
    exact (hρ i.1).ne h
  have hdom := cgpMarkerCutoff_ne_zero P.toLocalChartFamily hΔ0 (.inl i) pu hcut
  exact ⟨abs_scale_sub_le_of_coord_GAFS P hΛ i hdom (by linarith),
    abs_scale_sub_le_of_coord_GAFS P hΛ i hpxi (by linarith)⟩

/-- **EDP01, value half of `|z_ρ − ρ| ≤ (80/3)Λρ`** via (SM): a convex combination of the scales
of first-cloud contributors at `x = 𝓔⁰(p)` (`|η_i(p)| ≤ 7`) is within `(80/3)Λρ(p)` of `ρ(p)`. -/
theorem edp01_mean_value_GAFS
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) {εc σ : ℝ} (hε : 0 < εc)
    (hσ : 0 ≤ σ) (hσε : σ ≤ εc / 10000) (i : P.circle.finite_centres.toFinset) {px : X}
    (hpxi : px ∈ ball i.1 (200 * ρ i.1))
    (hηx : ‖cgpCoord P.toLocalChartFamily P.zero (.inl i) px‖ ≤ 7)
    {ι : Type*} (J : Finset ι) (q : ι → X)
    (hq : ∀ y ∈ J, q y ∈ fc04Set P.toLocalChartFamily P.zero 8 ∧
      (closedBall (cgpGlobalMap P.toLocalChartFamily P.zero (q y)) (80 * εc⁻¹ * (σ * ρ (q y))) ∩
        ball (cgpGlobalMap P.toLocalChartFamily P.zero px) (8 * εc⁻¹ * (σ * ρ px))).Nonempty)
    (w : ι → ℝ) (hw0 : ∀ y ∈ J, 0 ≤ w y) (hw1 : ∑ y ∈ J, w y = 1) :
    |∑ y ∈ J, w y * ρ (q y) - ρ px| ≤ 80 / 3 * Λ * ρ px := by
  have hri := hρ i.1
  have hSC : ∀ y ∈ J, |ρ (q y) - ρ i.1| ≤ 10 * Λ * ρ i.1 := fun y hy =>
    (edp01_contributor_scale_GAFS P hΔ hΛ hsmall hε hσ hσε i hpxi hηx (hq y hy).1
      (hq y hy).2).1
  have hmean := EdgeDisk.abs_weightedMean_sub_le J w (fun y => ρ (q y)) hw0 hw1 hSC
  have hpx : |ρ px - ρ i.1| ≤ 10 * Λ * ρ i.1 :=
    abs_scale_sub_le_of_coord_GAFS P hΛ i hpxi (by linarith)
  have hΛ10 : 10 * Λ ≤ 1 / 4 := by nlinarith
  have hlow : 3 / 4 * ρ i.1 ≤ ρ px := by
    have := (abs_le.mp hpx).1
    nlinarith
  have htri : |∑ y ∈ J, w y * ρ (q y) - ρ px| ≤ 20 * Λ * ρ i.1 := by
    calc |∑ y ∈ J, w y * ρ (q y) - ρ px|
        = |(∑ y ∈ J, w y * ρ (q y) - ρ i.1) - (ρ px - ρ i.1)| := by ring_nf
      _ ≤ |∑ y ∈ J, w y * ρ (q y) - ρ i.1| + |ρ px - ρ i.1| := abs_sub _ _
      _ ≤ 10 * Λ * ρ i.1 + 10 * Λ * ρ i.1 := add_le_add hmean hpx
      _ = 20 * Λ * ρ i.1 := by ring
  calc |∑ y ∈ J, w y * ρ (q y) - ρ px| ≤ 20 * Λ * ρ i.1 := htri
    _ ≤ 20 * Λ * (4 / 3 * ρ px) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
    _ = 80 / 3 * Λ * ρ px := by ring

/-- **EDP01 (SW)** on the first cloud: for weights `w_y` on the ambient space with CFS12's
properties at a point `z` (`∑ w_y = 1` near `z`, `‖Dw_y‖ ≤ c_w/r_x` with `r_x = Σρ(p)`) attached
to first-cloud contributors `q_y` at `x = 𝓔⁰(p)` (`|η_i(p)| ≤ 7`), the weighted mean of their scales
has derivative `∑ ρ(q_y) Dw_y` of norm at most `|J| · (40c_w/(3Σ)) Λ`. -/
theorem edp01_mean_deriv_GAFS
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) {εc σ : ℝ} (hε : 0 < εc)
    (hσ : 0 < σ) (hσε : σ ≤ εc / 10000) (i : P.circle.finite_centres.toFinset) {px : X}
    (hpxi : px ∈ ball i.1 (200 * ρ i.1))
    (hηx : ‖cgpCoord P.toLocalChartFamily P.zero (.inl i) px‖ ≤ 7)
    {ι : Type*} (J : Finset ι) (q : ι → X)
    (hq : ∀ y ∈ J, q y ∈ fc04Set P.toLocalChartFamily P.zero 8 ∧
      (closedBall (cgpGlobalMap P.toLocalChartFamily P.zero (q y)) (80 * εc⁻¹ * (σ * ρ (q y))) ∩
        ball (cgpGlobalMap P.toLocalChartFamily P.zero px) (8 * εc⁻¹ * (σ * ρ px))).Nonempty)
    (w : ι → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → ℝ)
    (w' : ι → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ)
    {z : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hw : ∀ y ∈ J, HasFDerivAt (w y) (w' y) z) (hpart : ∀ᶠ z' in 𝓝 z, ∑ y ∈ J, w y z' = 1)
    {cw : ℝ} (hw' : ∀ y ∈ J, ‖w' y‖ ≤ cw / (σ * ρ px)) :
    HasFDerivAt (fun z' => ∑ y ∈ J, w y z' * ρ (q y)) (∑ y ∈ J, ρ (q y) • w' y) z ∧
      ‖∑ y ∈ J, ρ (q y) • w' y‖ ≤ J.card * (40 * cw / (3 * σ)) * Λ := by
  have hri := hρ i.1
  have hrp := hρ px
  have hSC : ∀ y ∈ J, |ρ (q y) - ρ i.1| ≤ 10 * Λ * ρ i.1 := fun y hy =>
    (edp01_contributor_scale_GAFS P hΔ hΛ hsmall hε hσ.le hσε i hpxi hηx (hq y hy).1
      (hq y hy).2).1
  obtain ⟨hd, hn⟩ := EdgeDisk.weightedMean_hasFDerivAt_norm_le J w w' (fun y => ρ (q y)) hw hpart
    hSC hw'
  refine ⟨hd, hn.trans ?_⟩
  have hpx : |ρ px - ρ i.1| ≤ 10 * Λ * ρ i.1 :=
    abs_scale_sub_le_of_coord_GAFS P hΛ i hpxi (by linarith)
  have hΛ10 : 10 * Λ ≤ 1 / 4 := by nlinarith
  have hlow : 3 / 4 * ρ i.1 ≤ ρ px := by
    have := (abs_le.mp hpx).1
    nlinarith
  rcases J.eq_empty_or_nonempty with hJ | ⟨y₀, hy₀⟩
  · simp [hJ]
  have hcw : 0 ≤ cw := by
    have h := (norm_nonneg _).trans (hw' y₀ hy₀)
    have hpos : 0 < σ * ρ px := mul_pos hσ hrp
    by_contra hneg
    have : cw / (σ * ρ px) < 0 := div_neg_of_neg_of_pos (not_le.mp hneg) hpos
    linarith
  have hkey : 10 * Λ * ρ i.1 * (cw / (σ * ρ px)) ≤ 40 * cw / (3 * σ) * Λ := by
    have hpos : 0 < σ * ρ px := mul_pos hσ hrp
    rw [mul_div_assoc', div_le_iff₀ hpos]
    have h1 : 10 * Λ * ρ i.1 * cw ≤ 10 * Λ * (4 / 3 * ρ px) * cw := by
      apply mul_le_mul_of_nonneg_right _ hcw
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    have h2 : 40 * cw / (3 * σ) * Λ * (σ * ρ px) = 10 * Λ * (4 / 3 * ρ px) * cw := by
      field_simp
      ring
    linarith
  calc (J.card : ℝ) * (10 * Λ * ρ i.1 * (cw / (σ * ρ px)))
      ≤ J.card * (40 * cw / (3 * σ) * Λ) :=
        mul_le_mul_of_nonneg_left hkey (Nat.cast_nonneg _)
    _ = J.card * (40 * cw / (3 * σ)) * Λ := by ring

end DifferentialGeometry.Geometry.Collapse
