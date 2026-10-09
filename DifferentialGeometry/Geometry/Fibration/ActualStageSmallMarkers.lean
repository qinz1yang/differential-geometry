import DifferentialGeometry.Geometry.Fibration.ActualStageTargets
import DifferentialGeometry.Geometry.Fibration.ActualSlimGraphModel
import DifferentialGeometry.Geometry.Fibration.ActualEdgeGraphModel
import DifferentialGeometry.Geometry.Fibration.ActualSlimRawAlignment
import DifferentialGeometry.Geometry.Fibration.ActualEdgeComparisonList
import DifferentialGeometry.Geometry.Fibration.ActualSegmentLocalization
import DifferentialGeometry.Geometry.Metric.SupportComparisonLists

/-!
# Small markers on the actual stage data: CFS27/CFS28 inputs for CFS31's `hnear`

Blueprint `master207B.tex`, CFS26–CFS28 (B:3575–3730). CFS27 prunes from a reference chart's
model every retained block with `R_i ≤ R_a/2` so that the planes (PP) lie in those blocks' kernels.
The explicit model graphs of SGP04 (`sgpFullGraph`) and EGP06 (`egpModelGraph`) need no pruning:
their blocks of unlisted tags are zero and every listed tag has `ρ(j)/ρ(i) > 99/100` (support
meeting at slow variation), so every retained block with `R < (99/100)ρ(i)` has a CONSTANT marker
in the model and the model planes lie in its kernel.

* `blockMarkerCLM_fderiv_eq_zero_of_const_GAF4`: a globally constant marker component of a map
  into a block space has zero derivative.
* `egpEdgeList_ratio_GAF4`, `egpSlimList_ratio_GAF4`: EGP02's listed centres have
  `ρ(j) > (99/100)ρ(i)`.
* `sgpFullGraph_smallMarker_GAF4`, `egpModelGraph_smallMarker_GAF4`: the marker of every retained
  block with `ρ(c_a) ≤ (99/100)ρ(i)` annihilates `DΦ_i`.
* CFS31's remaining marker inputs on the actual stage data: `blockMarker_retained_GAF4` (retained
  or discarded blocks of `Q_st`), `cgpMarkerCutoff_scale_lip_GAF4` and `gafStage_support_GAF4`
  ((AS) at a positive projected marker, from slow variation only), `gafCloud_preimage_ratio_GAF4`
  (two preimages of a core cloud point: ratio `≥ 3/5`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology InnerProductSpace
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section Generic

variable {κ : Type*} {V : κ → Type*} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, InnerProductSpace ℝ (V i)]

/-- A globally constant marker component has zero derivative: `v_t(DΦ(a)h) = 0`. -/
theorem blockMarkerCLM_fderiv_eq_zero_of_const_GAF4 [Finite κ] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (Φ : E → BlockSpace V) (t : κ) (c : ℝ)
    (hc : ∀ u, (Φ u t).snd = c) (a h : E) : blockMarkerCLM t (fderiv ℝ Φ a h) = 0 := by
  have := Fintype.ofFinite κ
  by_cases hd : DifferentiableAt ℝ Φ a
  · have h1 : HasFDerivAt (fun u => blockMarkerCLM (V := V) t (Φ u))
        ((blockMarkerCLM (V := V) t).comp (fderiv ℝ Φ a)) a :=
      (blockMarkerCLM (V := V) t).hasFDerivAt.comp a hd.hasFDerivAt
    have hfun : (fun u => blockMarkerCLM (V := V) t (Φ u)) = fun _ => c := funext hc
    rw [hfun] at h1
    have h3 := h1.unique (hasFDerivAt_const c a)
    have h4 := congrArg (fun L : E →L[ℝ] ℝ => L h) h3
    simpa using h4
  · rw [fderiv_zero_of_not_differentiableAt hd]
    simp

variable [Fintype κ] [DecidableEq κ] [∀ i, FiniteDimensional ℝ (V i)]

/-- The marker of block `t` is retained by `π_s` (`t ∈ s`: `(ker v_t)ᗮ ≤ range π_s`) or discarded
(`t ∉ s`: `(ker v_t)ᗮ ≤ (range π_s)ᗮ`). -/
theorem blockMarker_retained_GAF4 (s : Finset κ) (t : κ) :
    (LinearMap.ker ((blockMarkerCLM t : BlockSpace V →L[ℝ] ℝ) : BlockSpace V →ₗ[ℝ] ℝ))ᗮ ≤
        (blockRestrict (V := V) s).range ∨
      (LinearMap.ker ((blockMarkerCLM t : BlockSpace V →L[ℝ] ℝ) : BlockSpace V →ₗ[ℝ] ℝ))ᗮ ≤
        ((blockRestrict (V := V) s).range)ᗮ := by
  have hP := blockRestrict_eq_starProjection_GAF3 (V := V) s
  by_cases ht : t ∈ s
  · left
    have hle : ((blockRestrict (V := V) s).range)ᗮ ≤
        LinearMap.ker ((blockMarkerCLM t : BlockSpace V →L[ℝ] ℝ) : BlockSpace V →ₗ[ℝ] ℝ) := by
      intro y hy
      have h0 : ((blockRestrict (V := V) s).range).starProjection y = 0 :=
        (Submodule.starProjection_apply_eq_zero_iff _).mpr hy
      rw [hP] at h0
      have h1 := congrArg (fun z => blockMarkerCLM (V := V) t z) h0
      simp only [blockMarkerCLM_apply, blockRestrict_apply, ht, ite_true, map_zero] at h1
      change blockMarkerCLM (V := V) t y = 0
      rw [blockMarkerCLM_apply]
      simpa using h1
    exact (Submodule.orthogonal_le hle).trans (Submodule.orthogonal_orthogonal _).le
  · right
    refine Submodule.orthogonal_le fun y hy => ?_
    have hy' : blockRestrict (V := V) s y = y := mem_range_blockRestrict_iff_GAF3.mp hy
    change blockMarkerCLM (V := V) t y = 0
    rw [← hy', blockMarkerCLM_apply, blockRestrict_apply, ite_eq_right ht]
    rfl

end Generic

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

variable (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
  (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)

/-- EGP02's listed edge centres have `ρ(j) > (99/100)ρ(i)`. -/
theorem egpEdgeList_ratio_GAF4 (hΔ : 0 < Δ) (hΛ : 0 ≤ Λ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000)
    {i j : X} (hj : j ∈ egpEdgeList L i) : 99 / 100 * ρ i < ρ j := by
  have hc : ((Real.toNNReal Λ : NNReal) : ℝ) = Λ := Real.coe_toNNReal _ hΛ
  obtain ⟨-, y, hy1, hy2⟩ := hj
  have hy1' : y ∈ closedBall j ((100 * Δ) * ρ j) := L.edge.tsupport_cutoff_subset j hy1
  have hy2' : y ∈ ball i ((20 * Δ) * ρ i) := by
    rw [mul_assoc] at hy2 ⊢
    exact hy2
  obtain ⟨h1, -, -, -⟩ := support_meeting_sharp_bounds L.lipschitz_scale (hρ i) (hρ j)
    (a := 20 * Δ) (c := 100 * Δ) (by positivity) (by positivity) (by rw [hc]; nlinarith)
    (by rw [hc]; nlinarith) ⟨y, hy1', hy2'⟩
  have h := (lt_div_iff₀ (hρ i)).mp h1
  linarith

/-- EGP02's listed slim centres have `ρ(j) > (99/100)ρ(i)`. -/
theorem egpSlimList_ratio_GAF4 (hΔ : 0 < Δ) (hΛ : 0 ≤ Λ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000)
    {i j : X} (hj : j ∈ egpSlimList L i) : 99 / 100 * ρ i < ρ j := by
  have hc : ((Real.toNNReal Λ : NNReal) : ℝ) = Λ := Real.coe_toNNReal _ hΛ
  obtain ⟨hjc, y, hy1, hy2⟩ := hj
  have hy1' : y ∈ closedBall j ((910000 * Δ) * ρ j) := (fc18_slim_row L hΔ hjc).1 hy1
  have hy2' : y ∈ ball i ((20 * Δ) * ρ i) := by
    rw [mul_assoc] at hy2 ⊢
    exact hy2
  obtain ⟨h1, -, -, -⟩ := support_meeting_sharp_bounds L.lipschitz_scale (hρ i) (hρ j)
    (a := 20 * Δ) (c := 910000 * Δ) (by positivity) (by positivity) (by rw [hc]; nlinarith)
    (by rw [hc]; nlinarith) ⟨y, hy1', hy2'⟩
  have h := (lt_div_iff₀ (hρ i)).mp h1
  linarith

/-- **Small markers of SGP04's model.** For every retained marker `a` (circle, slim or edge) with
`ρ(c_a) ≤ (99/100)ρ(i)`, the marker of its block annihilates `DΦ_i` (`Φ_i = sgpFullGraph`): that
block of `Φ_i` is zero (circle, edge, unlisted slim tag; a listed slim tag has ratio `> 99/100`). -/
theorem sgpFullGraph_smallMarker_GAF4 (hΔ : 0 < Δ) (hΛ : 0 ≤ Λ)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (i : L.slim.finite_centres.toFinset)
    (sgn c zsgn zc : X → ℝ) (a : CGPMarkerIndex L) (ha : ρ (cgpMarkerCentre L a) ≤ 99 / 100 * ρ i.1)
    (u h : ℝ) :
    blockMarkerCLM (cgpMarkerTag L Z a) (fderiv ℝ (sgpFullGraph L Z i sgn c zsgn zc) u h) = 0 := by
  classical
  have hri := hρ i.1
  rcases a with j | j | j
  · exact blockMarkerCLM_fderiv_eq_zero_of_const_GAF4 _ _ 0 (fun _ => rfl) u h
  · refine blockMarkerCLM_fderiv_eq_zero_of_const_GAF4 _ _ 0 (fun y => ?_) u h
    change (sgpSlimModelBlock L i sgn c j y).snd = 0
    have hji : j ≠ i := by
      rintro rfl
      change ρ j.1 ≤ 99 / 100 * ρ j.1 at ha
      linarith
    have hS : j.1 ∉ sgpSlimList L.slim i.1 := by
      intro hS
      have h1 := (sgpSlimList_bounds L hΔ hΛ hLΛ hS).2.1
      have h2 := (lt_div_iff₀ hri).mp h1
      change ρ j.1 ≤ 99 / 100 * ρ i.1 at ha
      linarith
    unfold sgpSlimModelBlock
    rw [ite_eq_right hji, ite_eq_right hS]
    rfl
  · exact blockMarkerCLM_fderiv_eq_zero_of_const_GAF4 _ _ 0 (fun _ => rfl) u h

/-- **Small markers of EGP06's model.** For every retained marker `a` with
`ρ(c_a) ≤ (99/100)ρ(i)`, the marker of its block annihilates `DΦ_i` (`Φ_i = egpModelGraph`): that
block of `Φ_i` is zero (circle, unlisted slim or edge tag; listed tags have ratio `> 99/100`). -/
theorem egpModelGraph_smallMarker_GAF4 (hΔ : 0 < Δ) (hΛ : 0 ≤ Λ)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (i : X) (sgn c : CGPTag L Z → ℝ) (a : CGPMarkerIndex L)
    (ha : ρ (cgpMarkerCentre L a) ≤ 99 / 100 * ρ i) (u h : ℝ) :
    blockMarkerCLM (cgpMarkerTag L Z a) (fderiv ℝ (egpModelGraph L Z i sgn c) u h) = 0 := by
  classical
  have hri := hρ i
  rcases a with j | j | j
  · exact blockMarkerCLM_fderiv_eq_zero_of_const_GAF4 _ _ 0 (fun _ => rfl) u h
  · refine blockMarkerCLM_fderiv_eq_zero_of_const_GAF4 _ _ 0 (fun y => ?_) u h
    change (egpModelComponent L Z i sgn c (.inr (.inl j)) y).snd = 0
    have hS : j.1 ∉ egpSlimList L i := by
      intro hS
      have h1 := egpSlimList_ratio_GAF4 L hΔ hΛ hLΛ hS
      change ρ j.1 ≤ 99 / 100 * ρ i at ha
      linarith
    simp only [egpModelComponent, hS, ite_false]
    rfl
  · refine blockMarkerCLM_fderiv_eq_zero_of_const_GAF4 _ _ 0 (fun y => ?_) u h
    change (egpModelComponent L Z i sgn c (.inr (.inr (.inl j))) y).snd = 0
    have hji : j.1 ≠ i := by
      intro hji
      change ρ j.1 ≤ 99 / 100 * ρ i at ha
      rw [hji] at ha
      linarith
    have hS : j.1 ∉ egpEdgeList L i := by
      intro hS
      have h1 := egpEdgeList_ratio_GAF4 L hΔ hΛ hLΛ hS
      change ρ j.1 ≤ 99 / 100 * ρ i at ha
      linarith
    simp only [egpModelComponent, hji, hS, ite_false]
    rfl

/-- (AS) at a positive retained cutoff from slow variation alone:
`3ρ(c_a)/4 ≤ ρ(p) ≤ 5ρ(c_a)/4`. -/
theorem cgpMarkerCutoff_scale_lip_GAF4 (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) (a : CGPMarkerIndex L) (p : X)
    (hp : cgpMarkerCutoff L a p ≠ 0) :
    3 * ρ (cgpMarkerCentre L a) / 4 ≤ ρ p ∧ ρ p ≤ 5 * ρ (cgpMarkerCentre L a) / 4 := by
  have hΔ0 : 0 < Δ := by linarith
  have hball := cgpMarkerCutoff_ne_zero L hΔ0 a p hp
  rw [mem_ball] at hball
  have hD : cgpMarkerDomain L a ≤ 1000000 * Δ := by
    rcases a with j | j | j
    · change (200 : ℝ) ≤ 1000000 * Δ
      linarith
    · exact le_rfl
    · change 100 * Δ ≤ 1000000 * Δ
      linarith
  have hc0 := hρ (cgpMarkerCentre L a)
  have hlip := L.lipschitz_scale.dist_le_mul p (cgpMarkerCentre L a)
  rw [Real.coe_toNNReal _ hΛ, Real.dist_eq] at hlip
  have hd : dist p (cgpMarkerCentre L a) ≤ 1000000 * Δ * ρ (cgpMarkerCentre L a) :=
    hball.le.trans (mul_le_mul_of_nonneg_right hD hc0.le)
  have h1 : Λ * dist p (cgpMarkerCentre L a) ≤ Λ * (1000000 * Δ * ρ (cgpMarkerCentre L a)) :=
    mul_le_mul_of_nonneg_left hd hΛ
  have h2 : Λ * (1000000 * Δ * ρ (cgpMarkerCentre L a)) ≤ ρ (cgpMarkerCentre L a) / 4 := by
    have := mul_le_mul_of_nonneg_right hsmall hc0.le
    nlinarith
  have habs := (abs_le.mp (hlip.trans (h1.trans h2)))
  constructor <;> linarith [habs.1, habs.2]

/-- **(AS) for the projected markers of every stage**: a positive marker of `π_{Q_st}𝓔⁰(q)` at a
retained block forces `3ρ(c_a)/4 ≤ ρ(q) ≤ 5ρ(c_a)/4` (CFS31's `hsupport`). -/
theorem gafStage_support_GAF4 (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4)
    (st : Fin 3) (a : CGPMarkerIndex L) (q : X)
    (hq : 0 < blockMarkerCLM (cgpMarkerTag L Z a)
      ((gafStageQ L Z st).starProjection (cgpGlobalMap L Z q))) :
    3 * ρ (cgpMarkerCentre L a) / 4 ≤ ρ q ∧ ρ q ≤ 5 * ρ (cgpMarkerCentre L a) / 4 := by
  classical
  refine cgpMarkerCutoff_scale_lip_GAF4 L hΔ hΛ hsmall a q fun h0 => ?_
  rw [gafStageQ_starProjection, blockMarkerCLM_apply, blockRestrict_apply] at hq
  split_ifs at hq with ht
  · rw [← blockMarkerCLM_apply, (cgpGlobalMap_markerBlock_GAF2 L Z a q).2, h0, mul_zero] at hq
    exact lt_irrefl 0 hq
  · exact lt_irrefl 0 hq

/-- **Two preimages of a core cloud point** (CFS26): for every selection over `S̃_st`, every
preimage `q` of `x ∈ S_st` has `(3/5)ρ(q) ≤ ρ(sel x)` (stage `0`: equality, from FC04's exact
radius; stages `1, 2`: CFS07 at distance zero). -/
theorem gafCloud_preimage_ratio_GAF4 (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) (st : Fin 3)
    (sel : BlockSpace (fun _ : CGPTag L Z => ℝ²) → X)
    (hsel : ∀ x ∈ gafCloudEnlarged L Z st, cgpProjMap L Z (gafStageTags L Z st) (sel x) = x) :
    ∀ x ∈ gafCloud L Z st, ∀ q, (gafStageQ L Z st).starProjection (cgpGlobalMap L Z q) = x →
      3 / 5 * ρ q ≤ ρ (sel x) := by
  have hΔ0 : 0 ≤ Δ := by linarith
  intro x hx q hq
  rw [gafStageQ_starProjection_globalMap] at hq
  have hxe := gafCloud_subset_enlarged L Z hΔ0 st hx
  have hsx := hsel x hxe
  fin_cases st
  · have huniv := cgpProjMap_univ_GAF L Z
    have hq' : cgpGlobalMap L Z q = x := by
      rw [← huniv]
      exact hq
    have hs' : cgpGlobalMap L Z (sel x) = x := by
      rw [← huniv]
      exact hsx
    have hr := (fc04_first_cloud_scale L Z (L' := 0) (sg := 1) zero_le_one (by norm_num)).1
    have h1 := hr q
    have h2 := hr (sel x)
    rw [hq'] at h1
    rw [hs'] at h2
    have heq : ρ q = ρ (sel x) := by linarith
    have := hρ q
    rw [← heq]
    linarith
  · have hx8 : x ∈ cgpProjMap L Z (cgpQ2Tags L Z) '' fc27EdgeSet L 8 := hxe
    have hmc := (fc27_edge_cloud_scale L Z hΔ hΛ hsmall).2.2.2 0 0 le_rfl le_rfl (by norm_num)
      q (sel x) (by rw [show cgpProjMap L Z (cgpQ2Tags L Z) q = x from hq]; exact hx8)
      (by rw [show cgpProjMap L Z (cgpQ2Tags L Z) (sel x) = x from hsx]; exact hx8)
      (by
        rw [show cgpProjMap L Z (cgpQ2Tags L Z) q = x from hq,
          show cgpProjMap L Z (cgpQ2Tags L Z) (sel x) = x from hsx, dist_self]
        simp)
    exact hmc.1
  · have hx8 : x ∈ cgpProjMap L Z (cgpQ3Tags L Z) '' fc27SlimSet L 8 := hxe
    have hmc := (fc27_slim_cloud_scale L Z hΔ hΛ hsmall).2.2.2 0 0 le_rfl le_rfl (by norm_num)
      q (sel x) (by rw [show cgpProjMap L Z (cgpQ3Tags L Z) q = x from hq]; exact hx8)
      (by rw [show cgpProjMap L Z (cgpQ3Tags L Z) (sel x) = x from hsx]; exact hx8)
      (by
        rw [show cgpProjMap L Z (cgpQ3Tags L Z) q = x from hq,
          show cgpProjMap L Z (cgpQ3Tags L Z) (sel x) = x from hsx, dist_self]
        simp)
    exact hmc.1

end DifferentialGeometry.Geometry.Collapse
