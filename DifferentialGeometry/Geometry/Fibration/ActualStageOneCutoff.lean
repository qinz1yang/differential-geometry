import DifferentialGeometry.Geometry.Fibration.ActualAdjustmentChoice
import DifferentialGeometry.Geometry.Fibration.ActualRetainedMarkerCloud
import DifferentialGeometry.Analysis.Calculus.Cutoff.MarkerLocalitySourceCutoff

/-!
# GAF02, stage one: CFS31's source cutoff on the actual `𝓔⁰`

Blueprint `master207B.tex`, GAF02 (`thm:fibration-actual-final-submersions`, B:5797–5858), first
step of its proof: "CFS31 first constructs the source cutoff … its CLOSED support localizes the
original point to the corresponding original core". This module binds CFS31's first paragraph
(`markerLocalitySourceCutoff_row`, B:3783) to CGP01's actual map `𝓔⁰ = cgpGlobalMap` on
`LocalChartPackets`: the stage-one family `𝓘₁ = I₂` is the family of circle centres, with their
blocks `u_i = (·)_i.fst`, `v_i = (·)_i.snd` (`blockVectorCLM`, `blockMarkerCLM`), radii
`R_i = ρ(c_i)`, coordinates `η_i` = the circle chart coordinates and cutoffs `ζ_i` = LC87's circle
cutoffs; the profile is CGP01's `χ_E = lc87EdgeTransition` with the actual profile bound
`P₀ = cgpProfileBound` and the actual multiplicity `N = gafMultiplicity`.

`gaf02_stageOne_sourceCutoff`: `ψ₁` is smooth, `[0,1]`-valued, equal to one at `𝓔⁰(p)` whenever
some circle coordinate has `|η_i(p)| < 6` on its domain `B(c_i, 200ρ(c_i))`, its closed support
only meets `𝓔⁰`-images of points with some `|η_i| ≤ 13/2` on that domain, and
`‖Dψ₁(𝓔⁰p)‖ ≤ b_cut/ρ(p)` with GAF01's `b_cut = gafCutoffConstant`. Hypotheses: parameter ranges
of the producer only.
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

section Blocks

variable {κ : Type*} [Fintype κ] {V : κ → Type*} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, InnerProductSpace ℝ (V i)]

/-- The vector component `y ↦ (y_t).fst` of one block of the block space. -/
def blockVectorCLM (t : κ) : BlockSpace V →L[ℝ] V t :=
  (WithLp.fstL 2 ℝ (V t) ℝ).comp (PiLp.proj 2 (fun i => WithLp 2 (V i × ℝ)) t)

/-- The marker component `y ↦ (y_t).snd` of one block of the block space. -/
def blockMarkerCLM (t : κ) : BlockSpace V →L[ℝ] ℝ :=
  (WithLp.sndL 2 ℝ (V t) ℝ).comp (PiLp.proj 2 (fun i => WithLp 2 (V i × ℝ)) t)

omit [Fintype κ] in
theorem blockVectorCLM_apply (t : κ) (y : BlockSpace V) : blockVectorCLM t y = (y t).fst := rfl

omit [Fintype κ] in
theorem blockMarkerCLM_apply (t : κ) (y : BlockSpace V) : blockMarkerCLM t y = (y t).snd := rfl

theorem norm_blockVectorCLM_le (t : κ) : ‖(blockVectorCLM t : BlockSpace V →L[ℝ] V t)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by
    rw [one_mul, blockVectorCLM_apply]
    exact (WithLp.norm_fst_le (x := y t)).trans (PiLp.norm_apply_le y t)

theorem norm_blockMarkerCLM_le (t : κ) : ‖(blockMarkerCLM t : BlockSpace V →L[ℝ] ℝ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by
    rw [one_mul, blockMarkerCLM_apply]
    exact (WithLp.norm_snd_le (x := y t)).trans (PiLp.norm_apply_le y t)

end Blocks

/-- CGP01's increasing profile `χ_E` has `|χ_E'| ≤ P₀` (from the bound on `χ_{1/2,1}`). -/
theorem abs_deriv_lc87EdgeTransition_le_cgp (y : ℝ) :
    |deriv lc87EdgeTransition y| ≤ cgpProfileBound := by
  have hP := cgpProfileBound_spec.2.2.2.2.2.2.2
  have hχd : DifferentiableAt ℝ lc87EdgeTransition y :=
    (lc87EdgeTransition_contDiff.differentiable (by simp)) y
  have hinner : HasDerivAt (fun s : ℝ => (s - 1 / 2) / (1 - 1 / 2)) (1 / (1 - 1 / 2))
      ((y + 1) / 2) := ((hasDerivAt_id _).sub_const _).div_const _
  have hval : ((y + 1) / 2 - 1 / 2) / (1 - 1 / 2) = y := by ring
  have h1 : HasDerivAt lc87EdgeTransition (deriv lc87EdgeTransition y)
      (((y + 1) / 2 - 1 / 2) / (1 - 1 / 2)) := by
    rw [hval]
    exact hχd.hasDerivAt
  have hcomp : HasDerivAt (cfsRamp lc87EdgeTransition (1 / 2) 1)
      (deriv lc87EdgeTransition y * (1 / (1 - 1 / 2))) ((y + 1) / 2) := h1.comp ((y + 1) / 2) hinner
  have h := hP ((y + 1) / 2)
  rw [hcomp.deriv, abs_mul] at h
  have h2 : |(1 : ℝ) / (1 - 1 / 2)| = 2 := by norm_num
  rw [h2] at h
  have hP1 := cgpProfileBound_spec.1
  linarith [abs_nonneg (deriv lc87EdgeTransition y)]

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricNS_GAF
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedNS_GAF
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricCS_GAF
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- The stage-one vector blocks `u_i` (circle centres) of `𝓔⁰`. -/
def gafCircleVector
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (j : P.circle.finite_centres.toFinset) :
    BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ² :=
  blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl j)

/-- The stage-one markers `v_i` (circle centres) of `𝓔⁰`. -/
def gafCircleMarker
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (j : P.circle.finite_centres.toFinset) :
    BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ :=
  blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl j)

/-- **GAF02, stage one** (CFS31's source cutoff `ψ₁` on the actual `𝓔⁰`): smooth, `[0, 1]`-valued,
exact plateau over `|η_i| < 6`, closed support localizing the original point to some `|η_i| ≤ 13/2`
on `B(c_i, 200ρ(c_i))`, and `‖Dψ₁(𝓔⁰ p)‖ ≤ b_cut / ρ(p)`. -/
theorem gaf02_stageOne_sourceCutoff
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100) :
    let F := cgpGlobalMap P.toLocalChartFamily P.zero
    let ψ := markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
      (gafCircleMarker P)
    ContDiff ℝ ∞ ψ ∧ (∀ z, ψ z ∈ Icc (0 : ℝ) 1) ∧
      (∀ p, (∃ j, p ∈ ball j.1 (200 * ρ j.1) ∧
          ‖cgpCoord P.toLocalChartFamily P.zero (.inl j) p‖ < 6) → ψ (F p) = 1) ∧
      (∀ p, F p ∈ tsupport ψ → ∃ j, p ∈ ball j.1 (200 * ρ j.1) ∧
          ‖cgpCoord P.toLocalChartFamily P.zero (.inl j) p‖ ≤ 13 / 2) ∧
      (∀ p, ‖fderiv ℝ ψ (F p)‖ ≤ gafCutoffConstant / ρ p) := by
  intro F ψ
  have hΔ0 : 0 < Δ := by linarith
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := by nlinarith
  have hAS := (fc26_row P.toLocalChartFamily P.zero hΔ hσs hσs1 hΛ hsmall).1
  -- the block identities of `𝓔⁰`
  have hblock : ∀ (j : P.circle.finite_centres.toFinset) p,
      gafCircleVector P j (F p) = (ρ j.1 * P.circle.cutoff j.1 p) •
        cgpCoord P.toLocalChartFamily P.zero (.inl j) p ∧
      gafCircleMarker P j (F p) = ρ j.1 * P.circle.cutoff j.1 p := fun _ _ => ⟨rfl, rfl⟩
  -- the cutoff vanishes off its domain
  have hζU : ∀ (j : P.circle.finite_centres.toFinset) p, p ∉ ball j.1 (200 * ρ j.1) →
      P.circle.cutoff j.1 p = 0 := by
    intro j p hp
    by_contra h
    exact hp (cgpMarkerCutoff_ne_zero P.toLocalChartFamily hΔ0 (.inl j) p h)
  -- comparability (FC26 (AS))
  have hcomp : ∀ (j : P.circle.finite_centres.toFinset) p, 0 < P.circle.cutoff j.1 p →
      3 / 4 * ρ j.1 ≤ ρ p ∧ ρ p ≤ 5 / 4 * ρ j.1 := by
    intro j p hpos
    have hm : 0 < cgpMarker P.toLocalChartFamily P.zero (.inl j) (F p) := by
      change 0 < ρ j.1 * P.circle.cutoff j.1 p
      exact mul_pos (hρ _) hpos
    obtain ⟨h1, h2⟩ := hAS (.inl j) p hm
    change 3 * ρ j.1 / 4 ≤ ρ p at h1
    change ρ p ≤ 5 * ρ j.1 / 4 at h2
    constructor <;> linarith
  -- the plateau over `|η| < 6`
  have hplateau : ∀ (j : P.circle.finite_centres.toFinset) p, p ∈ ball j.1 (200 * ρ j.1) →
      ‖cgpCoord P.toLocalChartFamily P.zero (.inl j) p‖ < 6 → P.circle.cutoff j.1 p = 1 := by
    intro j p hp hη
    have hj := (Set.Finite.mem_toFinset _).mp j.2
    have h := P.toLocalChartFamilyQ.circle_cutoff_apply hj p
    simp only [mem_ball.mp hp, ↓reduceIte] at h
    rw [h]
    refine circleCutoffBump_LC87.one_of_mem_closedBall ?_
    rw [mem_closedBall, dist_zero_right]
    have h8 : (circleCutoffBump_LC87 : ContDiffBump (0 : ℝ²)).rIn = 8 := rfl
    rw [h8]
    exact le_of_lt (lt_trans hη (by norm_num))
  -- the multiplicity
  have hcount : ∀ p, (Finset.univ.filter fun j : P.circle.finite_centres.toFinset =>
      0 < P.circle.cutoff j.1 p).card ≤ gafMultiplicity := by
    intro p
    have hN := cgp_active_tags_ncard_le_fc07 P hΛ hΔ hμ hτ hLΛ hLmax he hT p
    set A : Set (CGPTag P.toLocalChartFamily P.zero) :=
      {i | i ≠ cgpScaleTag P.toLocalChartFamily P.zero ∧
        i ≠ cgpEdgeTag P.toLocalChartFamily P.zero ∧
        p ∈ tsupport (cgpCutoff P.toLocalChartFamily P.zero i)} with hA
    let S := Finset.univ.filter fun j : P.circle.finite_centres.toFinset =>
      0 < P.circle.cutoff j.1 p
    have hsub : ((S.map ⟨Sum.inl, Sum.inl_injective⟩ :
        Finset (CGPTag P.toLocalChartFamily P.zero)) : Set _) ⊆ A := by
      intro i hi
      simp only [Finset.coe_map, Function.Embedding.coeFn_mk, Set.mem_image,
        Finset.mem_coe] at hi
      obtain ⟨j, hjS, rfl⟩ := hi
      have hpos : 0 < P.circle.cutoff j.1 p := (Finset.mem_filter.mp hjS).2
      refine ⟨by simp [cgpScaleTag], by simp [cgpEdgeTag], subset_tsupport _ ?_⟩
      exact hpos.ne'
    have hcard : (S.card : ℝ) ≤ A.ncard := by
      have := Set.ncard_le_ncard hsub (Set.toFinite A)
      rw [Set.ncard_coe_finset, Finset.card_map] at this
      exact_mod_cast this
    exact Nat.le_floor (hcard.trans hN)
  have hu : ∀ j, ‖gafCircleVector P j‖ ≤ 1 := fun _ => norm_blockVectorCLM_le _
  have hv : ∀ j, ‖gafCircleMarker P j‖ ≤ 1 := fun _ => norm_blockMarkerCLM_le _
  obtain ⟨h1, h2, h3, h4, -, h6⟩ := markerLocalitySourceCutoff_row lc87EdgeTransition_contDiff
    (fun _ ht => lc87EdgeTransition_eq_zero ht) (fun _ ht => lc87EdgeTransition_eq_one ht)
    lc87EdgeTransition_mem_Icc cgpProfileBound_spec.1 abs_deriv_lc87EdgeTransition_le_cgp
    gafMultiplicity (gafCircleVector P) (gafCircleMarker P) hu hv (fun j => ρ j.1)
    (fun _ => hρ _) ρ hρ (fun j => ball j.1 (200 * ρ j.1))
    (fun j => cgpCoord P.toLocalChartFamily P.zero (.inl j)) (fun j => P.circle.cutoff j.1) F
    hζU hblock hcount hcomp hplateau
  exact ⟨h1, h2, h3, h4, h6⟩

end DifferentialGeometry.Geometry.Collapse
