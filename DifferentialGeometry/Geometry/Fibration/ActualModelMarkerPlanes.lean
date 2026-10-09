import DifferentialGeometry.Geometry.Fibration.ActualStageOneCutoff
import DifferentialGeometry.Geometry.Fibration.ActualFirstGraphModel
import DifferentialGeometry.Geometry.Fibration.ActualSlimGraphModel
import DifferentialGeometry.Geometry.Fibration.ActualEdgeGraphModel

/-!
# GAF04's plane half at the level of the three producers' model graphs

Blueprint `master207B.tex`, GAF04 (`lem:fibration-actual-full-marker-contributors`, B:5942–5968),
second half of (FM): "If `i = a`, the model marker is identically one. Otherwise … the model `i`
marker is thus the CONSTANT `s_i` on a neighborhood of `a_y` … Therefore its derivative at `a_y`
vanishes. … The physical tangent plane, obtained from this actual model, lies in the scalar marker
kernel." The planes of the stage tests are ranges `im DΦ(a)` of the model graphs of TCP05
(`tcpModelGraph`), EGP06 (`egpModelGraph`) and SGP04 (`sgpFullGraph`); this module proves, for
each of them, that the marker component `v_t = (·)_t.snd` (`blockMarkerCLM t`) of the stage's own
tags annihilates `im DΦ(a)` as soon as the listed block's cutoff argument is in the open plateau
(`< 8` in the block's own units), i.e. `im DΦ(a) ≤ ker v_t`. EDP01's "every first-cloud plane has
zero scale component" is `tcpModelGraph_scale_fderiv_GAFS`.

* Generic: `blockMarkerCLM_fderiv_eq_zero_GAFS` (a locally constant marker component has zero
  derivative), `range_fderiv_le_ker_blockMarkerCLM_GAFS` (the range form),
  `scaledCutoffBlock_snd_eventually_GAFS` (the marker `s φ(s⁻¹u)` of a scaled cutoff block is the
  constant `s` near a point whose argument is in the open plateau of `φ`).
* `tcpModelGraph_marker_fderiv_GAFS` (circle tags), `tcpModelGraph_scale_fderiv_GAFS` (the whole
  scale block), `sgpFullGraph_marker_fderiv_GAFS` (slim tags), `egpModelGraph_marker_fderiv_GAFS`
  (edge tags).
The binding (which model and argument `a_y` the stage test uses at each contributor, and the
plateau inequality from (FV) and the producers' affine comparisons) is the stage tests' part.
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

section Generic

variable {κ : Type*} [Fintype κ] {V : κ → Type*} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, InnerProductSpace ℝ (V i)] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [Fintype κ] in
/-- A marker component that is locally constant near `a` has zero derivative at `a`:
`v_t(DΦ(a)h) = 0`. -/
theorem blockMarkerCLM_fderiv_eq_zero_GAFS [Finite κ] {Φ : E → BlockSpace V} {a : E} (t : κ) {c : ℝ}
    (hΦ : DifferentiableAt ℝ Φ a) (hloc : (fun y => (Φ y t).snd) =ᶠ[𝓝 a] fun _ => c) (h : E) :
    blockMarkerCLM t (fderiv ℝ Φ a h) = 0 := by
  have := Fintype.ofFinite κ
  have h1 : HasFDerivAt (fun y => blockMarkerCLM (V := V) t (Φ y))
      ((blockMarkerCLM (V := V) t).comp (fderiv ℝ Φ a)) a :=
    (blockMarkerCLM (V := V) t).hasFDerivAt.comp a hΦ.hasFDerivAt
  have h2 : HasFDerivAt (fun y => blockMarkerCLM (V := V) t (Φ y)) (0 : E →L[ℝ] ℝ) a :=
    (hasFDerivAt_const c a).congr_of_eventuallyEq hloc
  have h3 := h1.unique h2
  have h4 := congrArg (fun L : E →L[ℝ] ℝ => L h) h3
  simpa using h4

omit [Fintype κ] in
/-- The range form: `im DΦ(a) ≤ ker v_t` for a locally constant marker component. -/
theorem range_fderiv_le_ker_blockMarkerCLM_GAFS [Finite κ] {Φ : E → BlockSpace V} {a : E} (t : κ)
    {c : ℝ} (hΦ : DifferentiableAt ℝ Φ a) (hloc : (fun y => (Φ y t).snd) =ᶠ[𝓝 a] fun _ => c) :
    LinearMap.range (fderiv ℝ Φ a : E →ₗ[ℝ] BlockSpace V) ≤
      LinearMap.ker ((blockMarkerCLM (V := V) t : BlockSpace V →L[ℝ] ℝ) :
        BlockSpace V →ₗ[ℝ] ℝ) := by
  rintro _ ⟨h, rfl⟩
  exact blockMarkerCLM_fderiv_eq_zero_GAFS t hΦ hloc h

omit [Fintype κ] [∀ i, InnerProductSpace ℝ (V i)] [NormedSpace ℝ E] in
/-- The marker `s φ(s⁻¹u)` of a scaled cutoff block along a map `u` continuous at `a` is the
constant `s` near `a` when `‖s⁻¹u(a)‖ < r` and `φ = 1` on the closed `r`-ball. -/
theorem scaledCutoffBlock_snd_eventually_GAFS {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {φ : F → ℝ} {r s : ℝ} (hφ : ∀ z, ‖z‖ ≤ r → φ z = 1) {u : E → F} {a : E}
    (hu : ContinuousAt u a) (ha : ‖s⁻¹ • u a‖ < r) :
    (fun y => (scaledCutoffBlock s φ (u y)).snd) =ᶠ[𝓝 a] fun _ => s := by
  have hcont : ContinuousAt (fun y => ‖s⁻¹ • u y‖) a :=
    (continuous_norm.continuousAt).comp ((continuous_const_smul s⁻¹).continuousAt.comp hu)
  filter_upwards [hcont.eventually (gt_mem_nhds ha)] with y hy
  change s * φ (s⁻¹ • u y) = s
  rw [hφ _ hy.le, mul_one]

end Generic

section Models

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

/-- **GAF04's plane half for TCP05's model** (circle tags): at `a`, the marker of the circle block
`j` of `Φ_i = tcpModelGraph` annihilates `DΦ_i(a)` when `j` is the own tag, unlisted, or listed with
its cutoff argument in the open plateau `‖s_j⁻¹(A_j a + c_j)‖ < 8` (`s_j = ρ(j)/ρ(i)`). -/
theorem tcpModelGraph_marker_fderiv_GAFS
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (i : X)
    (S : Finset (CGPTag L Z)) (Se : Finset L.edge.finite_centres.toFinset)
    (Ac : CGPTag L Z → ℝ² →L[ℝ] ℝ²) (cc : CGPTag L Z → ℝ²) (A1 : CGPTag L Z → ℝ² →L[ℝ] ℝ)
    (c1 : CGPTag L Z → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ) (j : L.circle.finite_centres.toFinset)
    (a : ℝ²)
    (hplat : (.inl j : CGPTag L Z) ∈ S → j.1 ≠ i →
      ‖(ρ j.1 / ρ i)⁻¹ • (Ac (.inl j) a + cc (.inl j))‖ < 8) (h : ℝ²) :
    blockMarkerCLM (.inl j : CGPTag L Z) (fderiv ℝ (tcpModelGraph L Z i S Se Ac cc A1 c1 Bτ cτ) a h)
      = 0 := by
  classical
  have hΦ : DifferentiableAt ℝ (tcpModelGraph L Z i S Se Ac cc A1 c1 Bτ cτ) a :=
    ((contDiff_tcpModelGraph L Z i S Se Ac cc A1 c1 Bτ cτ).differentiable (by simp)) a
  have hval : ∀ y, tcpModelGraph L Z i S Se Ac cc A1 c1 Bτ cτ y (.inl j) =
      tcpModelComponent L Z i S Se Ac cc A1 c1 Bτ cτ (.inl j) y := fun _ => rfl
  by_cases hji : j.1 = i
  · refine blockMarkerCLM_fderiv_eq_zero_GAFS (c := 1) _ hΦ (Eventually.of_forall fun y => ?_) h
    dsimp only
    rw [hval]
    simp only [tcpModelComponent, hji, ite_true]
    rfl
  · by_cases hS : (.inl j : CGPTag L Z) ∈ S
    · refine blockMarkerCLM_fderiv_eq_zero_GAFS (c := ρ j.1 / ρ i) _ hΦ ?_ h
      have hev := scaledCutoffBlock_snd_eventually_GAFS (s := ρ j.1 / ρ i) (r := 8)
        (φ := (circleCutoffBump_LC87 : ℝ² → ℝ))
        (fun z hz => circleCutoffBump_LC87.one_of_mem_closedBall (by
          rw [mem_closedBall, dist_zero_right]; exact hz))
        (u := fun y => Ac (.inl j) y + cc (.inl j))
        ((Ac (.inl j)).continuous.add continuous_const).continuousAt (hplat hS hji)
      filter_upwards [hev] with y hy
      rw [hval]
      simp only [tcpModelComponent, hji, hS, ite_true, ite_false]
      exact hy
    · refine blockMarkerCLM_fderiv_eq_zero_GAFS (c := 0) _ hΦ (Eventually.of_forall fun y => ?_) h
      dsimp only
      rw [hval]
      simp only [tcpModelComponent, hji, hS, ite_false]
      rfl

/-- **EDP01's first-cloud planes have zero scale component**: the scale block of TCP05's model is
the constant `(0, 1)`, so `DΦ_i(a)h` has zero scale block. -/
theorem tcpModelGraph_scale_fderiv_GAFS
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (i : X)
    (S : Finset (CGPTag L Z)) (Se : Finset L.edge.finite_centres.toFinset)
    (Ac : CGPTag L Z → ℝ² →L[ℝ] ℝ²) (cc : CGPTag L Z → ℝ²) (A1 : CGPTag L Z → ℝ² →L[ℝ] ℝ)
    (c1 : CGPTag L Z → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ) (a h : ℝ²) :
    fderiv ℝ (tcpModelGraph L Z i S Se Ac cc A1 c1 Bτ cτ) a h (cgpScaleTag L Z) = 0 := by
  have hd : ∀ t, Differentiable ℝ (tcpModelComponent L Z i S Se Ac cc A1 c1 Bτ cτ t) := fun t =>
    (contDiff_tcpModelComponent L Z i S Se Ac cc A1 c1 Bτ cτ t).differentiable (by simp)
  rw [tcpModelGraph, fderiv_orthogonalBlocks_apply_KA6 hd a h (cgpScaleTag L Z)]
  change fderiv ℝ (fun _ : ℝ² => (WithLp.toLp 2 (0, 1) : WithLp 2 (ℝ² × ℝ))) a h = 0
  rw [fderiv_const_apply]
  rfl

/-- **GAF04's plane half for SGP04's model** (slim tags): at `a`, the marker of the slim block `j`
of `Φ_i = sgpFullGraph` annihilates `DΦ_i(a)` when `j = i`, `j` is unlisted, or listed with
`|s_j⁻¹(sgn_j a + c_j)| < 8·10⁵Δ` (`s_j = ρ(j)/ρ(i)`). -/
theorem sgpFullGraph_marker_fderiv_GAFS
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (hΔ : 0 < Δ)
    (i : L.slim.finite_centres.toFinset) (sgn c zsgn zc : X → ℝ)
    (j : L.slim.finite_centres.toFinset) (a : ℝ)
    (hplat : j ≠ i → j.1 ∈ sgpSlimList L.slim i.1 →
      |(ρ j.1 / ρ i.1)⁻¹ * (sgn j.1 * a + c j.1)| < 8 * (10 ^ 5 * Δ)) (h : ℝ) :
    blockMarkerCLM (.inr (.inl j) : CGPTag L Z) (fderiv ℝ (sgpFullGraph L Z i sgn c zsgn zc) a h)
      = 0 := by
  classical
  have hΦ : DifferentiableAt ℝ (sgpFullGraph L Z i sgn c zsgn zc) a :=
    ((contDiff_sgpFullGraph L Z i sgn c zsgn zc).differentiable (by simp)) a
  have hval : ∀ y, sgpFullGraph L Z i sgn c zsgn zc y (.inr (.inl j)) =
      sgpSlimModelBlock L i sgn c j y := fun _ => rfl
  by_cases hji : j = i
  · refine blockMarkerCLM_fderiv_eq_zero_GAFS (c := 1) _ hΦ (Eventually.of_forall fun y => ?_) h
    dsimp only
    rw [hval]
    simp only [sgpSlimModelBlock, hji, ite_true]
    rfl
  · by_cases hS : j.1 ∈ sgpSlimList L.slim i.1
    · refine blockMarkerCLM_fderiv_eq_zero_GAFS (c := ρ j.1 / ρ i.1) _ hΦ ?_ h
      have hℓ : (0 : ℝ) < 10 ^ 5 * Δ := by positivity
      have hev := scaledCutoffBlock_snd_eventually_GAFS (s := ρ j.1 / ρ i.1)
        (r := 8 * (10 ^ 5 * Δ)) (φ := sgpProfile (10 ^ 5 * Δ))
        (fun z hz => sgpProfile_eq_one hℓ (by rwa [Real.norm_eq_abs] at hz))
        (u := fun y => sgn j.1 * y + c j.1)
        ((continuous_const.mul continuous_id).add continuous_const).continuousAt
        (by rw [smul_eq_mul, Real.norm_eq_abs]; exact hplat hji hS)
      filter_upwards [hev] with y hy
      rw [hval]
      simp only [sgpSlimModelBlock, hji, hS, ite_true, ite_false]
      exact hy
    · refine blockMarkerCLM_fderiv_eq_zero_GAFS (c := 0) _ hΦ (Eventually.of_forall fun y => ?_) h
      dsimp only
      rw [hval]
      simp only [sgpSlimModelBlock, hji, hS, ite_false]
      rfl

/-- **GAF04's plane half for EGP06's model** (edge tags): at `a`, the marker of the edge block `j`
of `Φ_i = egpModelGraph` annihilates `DΦ_i(a)` when `j` is the own tag, unlisted, or listed with
`|s_j⁻¹(sgn_j a + c_j)| < 8Δ` (`s_j = ρ(j)/ρ(i)`). -/
theorem egpModelGraph_marker_fderiv_GAFS
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (hΔ : 0 < Δ) (i : X)
    (sgn c : CGPTag L Z → ℝ) (j : L.edge.finite_centres.toFinset) (a : ℝ)
    (hplat : j.1 ≠ i → j.1 ∈ egpEdgeList L i →
      |(ρ j.1 / ρ i)⁻¹ * (sgn (.inr (.inr (.inl j))) * a + c (.inr (.inr (.inl j))))| < 8 * Δ)
    (h : ℝ) :
    blockMarkerCLM (.inr (.inr (.inl j)) : CGPTag L Z) (fderiv ℝ (egpModelGraph L Z i sgn c) a h)
      = 0 := by
  classical
  have hΦ : DifferentiableAt ℝ (egpModelGraph L Z i sgn c) a :=
    ((contDiff_egpModelGraph L Z i sgn c).differentiable (by simp)) a
  have hval : ∀ y, egpModelGraph L Z i sgn c y (.inr (.inr (.inl j))) =
      egpModelComponent L Z i sgn c (.inr (.inr (.inl j))) y := fun _ => rfl
  by_cases hji : j.1 = i
  · refine blockMarkerCLM_fderiv_eq_zero_GAFS (c := 1) _ hΦ (Eventually.of_forall fun y => ?_) h
    dsimp only
    rw [hval]
    simp only [egpModelComponent, hji, ite_true]
    rfl
  · by_cases hS : j.1 ∈ egpEdgeList L i
    · refine blockMarkerCLM_fderiv_eq_zero_GAFS (c := ρ j.1 / ρ i) _ hΦ ?_ h
      have hev := scaledCutoffBlock_snd_eventually_GAFS (s := ρ j.1 / ρ i) (r := 8 * Δ)
        (φ := scaledEdgeCoordinateProfile Δ)
        (fun z hz => by
          rw [Real.norm_eq_abs] at hz
          have hz' : |z / Δ| ≤ 8 := by
            rw [abs_div, abs_of_pos hΔ, div_le_iff₀ hΔ]
            exact hz
          exact intervalPlateauProfile_one (by norm_num) (by norm_num)
            ⟨by linarith [neg_abs_le (z / Δ)], by linarith [le_abs_self (z / Δ)]⟩)
        (u := fun y => sgn (.inr (.inr (.inl j))) * y + c (.inr (.inr (.inl j))))
        ((continuous_const.mul continuous_id).add continuous_const).continuousAt
        (by rw [smul_eq_mul, Real.norm_eq_abs]; exact hplat hji hS)
      filter_upwards [hev] with y hy
      rw [hval]
      simp only [egpModelComponent, hji, hS, ite_true, ite_false]
      exact hy
    · refine blockMarkerCLM_fderiv_eq_zero_GAFS (c := 0) _ hΦ (Eventually.of_forall fun y => ?_) h
      dsimp only
      rw [hval]
      simp only [egpModelComponent, hji, hS, ite_false]
      rfl

end Models

end DifferentialGeometry.Geometry.Collapse
