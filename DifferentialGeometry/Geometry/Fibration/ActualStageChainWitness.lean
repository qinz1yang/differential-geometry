import DifferentialGeometry.Geometry.Fibration.ActualStageChainPlateau
import DifferentialGeometry.Geometry.Fibration.ActualStageStepApplications
import DifferentialGeometry.Geometry.Metric.Cfs15MarkedWitness

/-!
# GAF02 BASES, second step: CGP04–CGP05 on the WHOLE marked zero set of the chain

Blueprint `master207B.tex`, CGP04 (B:4057–4082), CGP05 (B:4084–4128); external draft 59 §4
"第二步" (D59-5). Indexed by ONE chain `C : Gaf02Chain P …`: the stage-`st` output `O` (the
chain's active slot, or any output with the chain's cloud, radius `Σ_st ρ ∘ sel_st` and planes),
the chain's own planes with their small-marker kernel clause (C.test0–2), CFS07's ratio and the
preimage ratio of the family. No point of `Z_st` is assumed to come from a local section.

For a retained marker `a` (circle, slim or edge centre `c_a`, `R_a = ρ(c_a)`) whose tag survives
`π_st`, with `u_a = κ ∘ (block vector)` for a contraction `κ : ℝ² →L E` (identity on circles, the
axis coordinate `axisCoordCLM_BAS` on edges and slims) and `v_a` the block marker:

* `gafCloudEnlarged_preimage_ratio_BAS`: two preimages of a point of `S̃_st` have comparable
  scales (stage 0: equal; stages 1, 2: CFS07 at distance zero).
* `Gaf02Chain.plane_le_ker_marker_BAS` (the tests' last clause), `markerBlock_projMap_BAS` (FC01's
  block formula through `π_st`), `Gaf02Chain.vanish_of_large_BAS` (no tiny marker at comparable
  cloud points: `25R_a/3 < ρ(sel_st i)` ⇒ `v_a(i) = 0` and `P_i ⊆ ker v_a`).
* **CGP04** `Gaf02Chain.cgp04_BAS`: `R_a < ρ(sel y)/16` for a selected `y` ⇒ `v_a = 0` on
  `Z_st ∩ B(y, 20Ξ⁻¹r_y)`; these balls cover `Z_st`.
* **CGP05** `Gaf02Chain.cgp05_BAS`: EVERY `w ∈ V_a⁰ = {w ∈ Z_st | v_a(w) > .9R_a, ‖u_a(w)‖ < 5.5ℓR_a}`
  has `q ∈ Ã_st` with `ζ_a(q) > .899`, `‖κ η_a(q)‖ < 6.2ℓ` and (MW)
  `‖w − π_st𝓔⁰(q)‖ < (25/12)Ξ_stΣ_stR_a`.
* Full markers (the witness is in the plateau): `cgp05_circle_full_BAS` (`‖η‖ < 6.2`),
  `cgp05_slim_full_BAS` (`|η| < 6.2·10⁵Δ`), `cgp05_edge_full_BAS` (`|η| < 6.2Δ` and `t(q) ≤ 8Δ` from
  `Ã₂`): `ζ_a(q) = 1`.
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

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

/-- The axis coordinate `ℝ² → ℝ`, `(s, t) ↦ s` (left inverse of `planeAxis`). -/
def axisCoordCLM_BAS : ℝ² →L[ℝ] ℝ := EuclideanSpace.proj (0 : Fin 2)

theorem axisCoordCLM_planeAxis_BAS (t : ℝ) : axisCoordCLM_BAS (planeAxis t) = t := by
  simp [axisCoordCLM_BAS, planeAxis_apply]

theorem norm_axisCoordCLM_le_BAS : ‖axisCoordCLM_BAS‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul, axisCoordCLM_BAS]
    exact PiLp.norm_apply_le x 0

section Ratio

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

/-- **Two preimages of a point of `S̃_st`**: for every selection over `S̃_st`, every preimage `q`
of `x ∈ S̃_st` has `3/5 ρ(q) ≤ ρ(sel x) ≤ 5/3 ρ(q)`. -/
theorem gafCloudEnlarged_preimage_ratio_BAS
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) (st : Fin 3)
    (sel : BlockSpace (fun _ : CGPTag L Z => ℝ²) → X)
    (hsel : ∀ x ∈ gafCloudEnlarged L Z st, cgpProjMap L Z (gafStageTags L Z st) (sel x) = x) :
    ∀ x ∈ gafCloudEnlarged L Z st, ∀ q, (gafStageQ L Z st).starProjection (cgpGlobalMap L Z q) = x →
      3 / 5 * ρ q ≤ ρ (sel x) ∧ ρ (sel x) ≤ 5 / 3 * ρ q := by
  intro x hxe q hq
  rw [gafStageQ_starProjection_globalMap] at hq
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
    constructor <;> linarith
  · have hx8 : x ∈ cgpProjMap L Z (cgpQ2Tags L Z) '' fc27EdgeSet L 8 := hxe
    exact (fc27_edge_cloud_scale L Z hΔ hΛ hsmall).2.2.2 0 0 le_rfl le_rfl (by norm_num)
      q (sel x) (by rw [show cgpProjMap L Z (cgpQ2Tags L Z) q = x from hq]; exact hx8)
      (by rw [show cgpProjMap L Z (cgpQ2Tags L Z) (sel x) = x from hsx]; exact hx8)
      (by
        rw [show cgpProjMap L Z (cgpQ2Tags L Z) q = x from hq,
          show cgpProjMap L Z (cgpQ2Tags L Z) (sel x) = x from hsx, dist_self]
        simp)
  · have hx8 : x ∈ cgpProjMap L Z (cgpQ3Tags L Z) '' fc27SlimSet L 8 := hxe
    exact (fc27_slim_cloud_scale L Z hΔ hΛ hsmall).2.2.2 0 0 le_rfl le_rfl (by norm_num)
      q (sel x) (by rw [show cgpProjMap L Z (cgpQ3Tags L Z) q = x from hq]; exact hx8)
      (by rw [show cgpProjMap L Z (cgpQ3Tags L Z) (sel x) = x from hsx]; exact hx8)
      (by
        rw [show cgpProjMap L Z (cgpQ3Tags L Z) q = x from hq,
          show cgpProjMap L Z (cgpQ3Tags L Z) (sel x) = x from hsx, dist_self]
        simp)

/-- FC01's block formula through `π_st`: a retained tag of `π_st𝓔⁰(q)` is the block of `𝓔⁰(q)`,
`(κ u_a, v_a)(π_st𝓔⁰ q) = (R_aζ_a(q) κη_a(q), R_aζ_a(q))`. -/
theorem markerBlock_projMap_BAS
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) {st : Fin 3}
    {a : CGPMarkerIndex L} (ha : cgpMarkerTag L Z a ∈ gafStageTags L Z st) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (κ : ℝ² →L[ℝ] E) (q : X) :
    (κ.comp (blockVectorCLM (V := fun _ : CGPTag L Z => ℝ²) (cgpMarkerTag L Z a)))
        ((gafStageQ L Z st).starProjection (cgpGlobalMap L Z q)) =
      (ρ (cgpMarkerCentre L a) * cgpMarkerCutoff L a q) • κ (cgpCoord L Z (cgpMarkerTag L Z a) q) ∧
    blockMarkerCLM (V := fun _ : CGPTag L Z => ℝ²) (cgpMarkerTag L Z a)
        ((gafStageQ L Z st).starProjection (cgpGlobalMap L Z q)) =
      ρ (cgpMarkerCentre L a) * cgpMarkerCutoff L a q := by
  have hkeep : (gafStageQ L Z st).starProjection (cgpGlobalMap L Z q) (cgpMarkerTag L Z a) =
      cgpGlobalMap L Z q (cgpMarkerTag L Z a) := by
    rw [gafStageQ_starProjection_globalMap]
    exact cgpProjMap_apply_of_mem L Z ha q
  have hb := cgpGlobalMap_markerBlock_GAF2 L Z a q
  refine ⟨?_, ?_⟩
  · rw [ContinuousLinearMap.comp_apply, blockVectorCLM_apply, hkeep, ← blockVectorCLM_apply,
      hb.1, map_smul]
  · rw [blockMarkerCLM_apply, hkeep, ← blockMarkerCLM_apply, hb.2]

end Ratio

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

namespace Gaf02Chain

variable {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- The stage tests' small-marker clause: at a cloud point, for every preimage `q` and every
retained marker with `ρ(c_a) < ρ(q)/5`, the chain's plane lies in `ker v_a`. -/
theorem plane_le_ker_marker_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (st : Fin 3) :
    ∀ x ∈ gafCloud P.toLocalChartFamily P.zero st, ∀ q,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero st) q = x →
      ∀ a : CGPMarkerIndex P.toLocalChartFamily,
        ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
        C.plane st x ≤ LinearMap.ker ((blockMarkerCLM
          (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero a) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ) := by
  fin_cases st
  · exact C.test0.2.2.2.2
  · exact C.test1.2.2.2
  · exact C.test2.2.2.2

/-- The family budget `Λ·10⁶Δ ≤ 1/4` read off the chain. -/
theorem small_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw) : Λ * (1000000 * Δ) ≤ 1 / 4 := by
  obtain ⟨hΛ, hΔ, -, -, hLΛ, -⟩ := C.std
  have h' : Λ * (1000000 * Δ) = 1000000 * Δ * Λ := by ring
  linarith

/-- **No tiny marker at comparable cloud points**: for a retained marker `a` surviving `π_st`, a
cloud point `i` with `25R_a/3 < ρ(sel_st i)` has `v_a(i) = 0` and `P_i ⊆ ker v_a`. -/
theorem vanish_of_large_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw) {st : Fin 3}
    {a : CGPMarkerIndex P.toLocalChartFamily}
    (ha : cgpMarkerTag P.toLocalChartFamily P.zero a ∈ gafStageTags P.toLocalChartFamily P.zero st) :
    ∀ i ∈ gafCloud P.toLocalChartFamily P.zero st,
      25 / 3 * ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ (C.sel st i) →
      blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero a) i = 0 ∧
        C.plane st i ≤ LinearMap.ker ((blockMarkerCLM
          (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero a) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ) := by
  obtain ⟨hΛ, hΔ, -⟩ := C.std
  intro i hi hlarge
  have hi' := hi
  obtain ⟨q₀, -, hq₀⟩ := hi
  have hq₀' : (gafStageQ P.toLocalChartFamily P.zero st).starProjection
      (cgpGlobalMap P.toLocalChartFamily P.zero q₀) = i := by
    rw [gafStageQ_starProjection_globalMap]
    exact hq₀
  have hratio := gafCloud_preimage_ratio_two_GAF5 P.toLocalChartFamily P.zero hΔ hΛ C.small_BAS st
    (C.sel st) (C.hsel st) i hi' q₀ hq₀'
  have hc := hρ (cgpMarkerCentre P.toLocalChartFamily a)
  have hq₀big : ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q₀ / 5 := by linarith [hratio.2]
  refine ⟨?_, C.plane_le_ker_marker_BAS st i hi' q₀ hq₀ a hq₀big⟩
  rw [← hq₀', (markerBlock_projMap_BAS P.toLocalChartFamily P.zero ha
    (ContinuousLinearMap.id ℝ ℝ²) q₀).2]
  by_cases hz : cgpMarkerCutoff P.toLocalChartFamily a q₀ = 0
  · rw [hz, mul_zero]
  · exfalso
    have hs := cgpMarkerCutoff_scale_lip_GAF4 P.toLocalChartFamily hΔ hΛ C.small_BAS a q₀ hz
    linarith [hs.2]

/-- **CGP04 on the chain** (marker form): for a retained marker `a` surviving `π_st`, a selected
centre `y` of the stage output with `R_a < ρ(sel_st y)/16`, `v_a = 0` on
`Z_st ∩ B(y, 20Ξ_st⁻¹ r_y)` (these balls cover `Z_st`). -/
theorem cgp04_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw) {st : Fin 3}
    (O : Cfs15StageOutput (gafStageDim st) Kj (Ξ st) (cw st) (gafCloud P.toLocalChartFamily P.zero st)
      (gafCloudEnlarged P.toLocalChartFamily P.zero st) (fun x => S st * ρ (C.sel st x))
      (C.plane st))
    {a : CGPMarkerIndex P.toLocalChartFamily}
    (ha : cgpMarkerTag P.toLocalChartFamily P.zero a ∈ gafStageTags P.toLocalChartFamily P.zero st)
    {y : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)} (hy : y ∈ O.I)
    (hry : ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ (C.sel st y) / 16)
    {w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)} (hw : w ∈ O.Z)
    (hwy : w ∈ ball y (20 * (Ξ st)⁻¹ * (S st * ρ (C.sel st y)))) :
    blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (cgpMarkerTag P.toLocalChartFamily P.zero a) w = 0 := by
  obtain ⟨hΛ, hΔ, hμ, hτ, hLΛ, -, he, -⟩ := C.std
  obtain ⟨hΞ, hS, hmo, -⟩ := C.numbers.1 st
  have hin := cfs14_stage_inputs_GAF2 P hΛ hΔ hμ hτ (by linarith) hLΛ st (C.sel st) (C.hsel st)
    hΞ hS hmo
  have hc := hρ (cgpMarkerCentre P.toLocalChartFamily a)
  refine cgp04_kernel_BAS O _ hin.1 (fun x hx y hy' h => (hin.2.2.2 x hx y hy' h).2)
    (τ := S st * (25 / 3 * ρ (cgpMarkerCentre P.toLocalChartFamily a)))
    (fun i hi hri => C.vanish_of_large_BAS ha i hi (by
      have : S st * (25 / 3 * ρ (cgpMarkerCentre P.toLocalChartFamily a)) <
          S st * ρ (C.sel st i) := hri
      exact lt_of_mul_lt_mul_left this hS.le)) hy ?_ hw hwy
  have h16 : 125 / 9 * ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ (C.sel st y) := by
    linarith
  change 5 / 3 * (S st * (25 / 3 * ρ (cgpMarkerCentre P.toLocalChartFamily a))) <
    S st * ρ (C.sel st y)
  nlinarith

/-- **CGP05 on the chain**: for a retained marker `a` surviving `π_st`, a contraction `κ` and
`ℓ ≥ 1`, EVERY point `w` of the marked patch `V_a⁰ = {w ∈ Z_st | v_a(w) > .9R_a, ‖κu_a(w)‖ < 5.5ℓR_a}`
of the stage output has an original witness `q ∈ Ã_st` with `ζ_a(q) > .899`, `‖κη_a(q)‖ < 6.2ℓ`
and (MW) `‖w − π_st𝓔⁰(q)‖ < (25/12)Ξ_stΣ_stR_a`. -/
theorem cgp05_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw) {st : Fin 3}
    (O : Cfs15StageOutput (gafStageDim st) Kj (Ξ st) (cw st) (gafCloud P.toLocalChartFamily P.zero st)
      (gafCloudEnlarged P.toLocalChartFamily P.zero st) (fun x => S st * ρ (C.sel st x))
      (C.plane st))
    {a : CGPMarkerIndex P.toLocalChartFamily}
    (ha : cgpMarkerTag P.toLocalChartFamily P.zero a ∈ gafStageTags P.toLocalChartFamily P.zero st)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (κ : ℝ² →L[ℝ] E) (hκ : ‖κ‖ ≤ 1)
    {ℓ : ℝ} (hℓ : 1 ≤ ℓ) :
    ∀ w ∈ markedPatch_BPRE O.Z (κ.comp (blockVectorCLM
        (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero a)))
        (blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero a))
        (ρ (cgpMarkerCentre P.toLocalChartFamily a)) ℓ,
      ∃ q ∈ gafStageEnlargement P.toLocalChartFamily P.zero st,
        899 / 1000 < cgpMarkerCutoff P.toLocalChartFamily a q ∧
        ‖κ (cgpCoord P.toLocalChartFamily P.zero (cgpMarkerTag P.toLocalChartFamily P.zero a) q)‖ <
          31 / 5 * ℓ ∧
        ‖w - (gafStageQ P.toLocalChartFamily P.zero st).starProjection
            (cgpGlobalMap P.toLocalChartFamily P.zero q)‖ <
          25 / 12 * Ξ st * S st * ρ (cgpMarkerCentre P.toLocalChartFamily a) := by
  obtain ⟨hΛ, hΔ, hμ, hτ, hLΛ, -, he, -⟩ := C.std
  obtain ⟨hΞ, hS, hmo, -⟩ := C.numbers.1 st
  have hin := cfs14_stage_inputs_GAF2 P hΛ hΔ hμ hτ (by linarith) hLΛ st (C.sel st) (C.hsel st)
    hΞ hS hmo
  have hSg : S st ≤ Ξ st / 640 := by
    have h1 : 128 * (Ξ st)⁻¹ * S st * Ξ st ≤ 1 / 5 * Ξ st :=
      mul_le_mul_of_nonneg_right hmo hΞ.le
    have h2 : 128 * (Ξ st)⁻¹ * S st * Ξ st = 128 * S st := by
      field_simp
    linarith
  have hb := norm_blockVectorCLM_le (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
    (cgpMarkerTag P.toLocalChartFamily P.zero a)
  have hb0 := norm_nonneg (blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
    (cgpMarkerTag P.toLocalChartFamily P.zero a))
  have hκ0 := norm_nonneg κ
  have hu : ‖κ.comp (blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (cgpMarkerTag P.toLocalChartFamily P.zero a))‖ ≤ 1 :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (by nlinarith)
  exact cgp05_kernel_BAS O (fun q => (gafStageQ P.toLocalChartFamily P.zero st).starProjection
      (cgpGlobalMap P.toLocalChartFamily P.zero q))
    (gafStageEnlargement P.toLocalChartFamily P.zero st) _ hu _
    (norm_blockMarkerCLM_le (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) _)
    (fun q => κ (cgpCoord P.toLocalChartFamily P.zero (cgpMarkerTag P.toLocalChartFamily P.zero a) q))
    (cgpMarkerCutoff P.toLocalChartFamily a) (hρ _) hℓ hS hSg hρ
    (fun q => markerBlock_projMap_BAS P.toLocalChartFamily P.zero ha κ q)
    (fun q hq => by
      have hs := cgpMarkerCutoff_scale_lip_GAF4 P.toLocalChartFamily hΔ hΛ C.small_BAS a q hq
      linarith [hs.2])
    (fun z hz => by
      obtain ⟨q, hq, rfl⟩ := hz
      exact ⟨q, hq, gafStageQ_starProjection_globalMap _ _ st q⟩)
    (fun z hz q _ hqz => (gafCloudEnlarged_preimage_ratio_BAS P.toLocalChartFamily P.zero hΔ hΛ
      C.small_BAS st (C.sel st) (C.hsel st) z hz q hqz).2)
    (fun x hx y hy' h => (hin.2.2.2 x hx y hy' h).2) hin.1 (C.vanish_of_large_BAS ha)

/-- **CGP05, circle stage, full marker**: every point of the circle patch
`V_j⁰ = {w ∈ Z₁ | v_j(w) > .9R_j, ‖u_j(w)‖ < 5.5R_j}` has an original witness `q ∈ Ã₁` in the chart
domain with a FULL marker `ζ_j(q) = 1`, `‖η_j(q)‖ < 6.2`, scale in `[3R_j/4, 5R_j/4]` and (MW)
`‖w − 𝓔⁰(q)‖ < (25/12)Ξ₁Σ₁R_j`; so `u_j(𝓔⁰ q) = R_j η_j(q)`. -/
theorem cgp05_circle_full_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    (O : Cfs15StageOutput (gafStageDim 0) Kj (Ξ 0) (cw 0) (gafCloud P.toLocalChartFamily P.zero 0)
      (gafCloudEnlarged P.toLocalChartFamily P.zero 0) (fun x => S 0 * ρ (C.sel 0 x)) (C.plane 0))
    (j : P.toLocalChartFamily.circle.finite_centres.toFinset) :
    ∀ w ∈ markedPatch_BPRE O.Z (gafCircleVector P j) (gafCircleMarker P j) (ρ j.1) 1,
      ∃ q ∈ gafStageEnlargement P.toLocalChartFamily P.zero 0,
        q ∈ ball j.1 (200 * ρ j.1) ∧ P.circle.cutoff j.1 q = 1 ∧
        ‖cgpCoord P.toLocalChartFamily P.zero (.inl j) q‖ < 31 / 5 ∧
        3 / 4 * ρ j.1 ≤ ρ q ∧ ρ q ≤ 5 / 4 * ρ j.1 ∧
        gafCircleVector P j (cgpGlobalMap P.toLocalChartFamily P.zero q) =
          ρ j.1 • cgpCoord P.toLocalChartFamily P.zero (.inl j) q ∧
        gafCircleMarker P j (cgpGlobalMap P.toLocalChartFamily P.zero q) = ρ j.1 ∧
        ‖w - cgpGlobalMap P.toLocalChartFamily P.zero q‖ < 25 / 12 * Ξ 0 * S 0 * ρ j.1 := by
  obtain ⟨hΛ, hΔ, -⟩ := C.std
  have hΔ0 : 0 < Δ := by linarith
  intro w hw
  have hw' : w ∈ markedPatch_BPRE O.Z ((ContinuousLinearMap.id ℝ ℝ²).comp (blockVectorCLM
      (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (cgpMarkerTag P.toLocalChartFamily P.zero (.inl j))))
      (blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero (.inl j)))
      (ρ (cgpMarkerCentre P.toLocalChartFamily (.inl j))) 1 := by
    rw [ContinuousLinearMap.id_comp]
    exact hw
  obtain ⟨q, hqA, hζ, hη, hmw⟩ := C.cgp05_BAS O (a := .inl j) (Finset.mem_univ _)
    (ContinuousLinearMap.id ℝ ℝ²) ContinuousLinearMap.norm_id_le le_rfl w hw'
  have hne : cgpMarkerCutoff P.toLocalChartFamily (.inl j) q ≠ 0 := by linarith
  have hball := cgpMarkerCutoff_ne_zero P.toLocalChartFamily hΔ0 (.inl j) q hne
  have hj : j.1 ∈ P.circle.centres := (Set.Finite.mem_toFinset _).mp j.2
  have h1 := P.circle.coord_lt_of_cutoff_ne_zero j.1 hj q hne
  have hη' : ‖cgpCoord P.toLocalChartFamily P.zero (.inl j) q‖ < 31 / 5 := by
    have h2 := hη
    simp only [ContinuousLinearMap.id_apply, mul_one] at h2
    exact h2
  have hcut : P.circle.cutoff j.1 q = 1 :=
    P.circle.cutoff_eq_one j.1 hj q h1.1 (hη'.le.trans (by norm_num))
  have hs := cgpMarkerCutoff_scale_lip_GAF4 P.toLocalChartFamily hΔ hΛ C.small_BAS (.inl j) q hne
  have hb := cgpGlobalMap_markerBlock_GAF2 P.toLocalChartFamily P.zero (.inl j) q
  have hcut' : cgpMarkerCutoff P.toLocalChartFamily (.inl j) q = 1 := hcut
  have hF : (gafStageQ P.toLocalChartFamily P.zero 0).starProjection
      (cgpGlobalMap P.toLocalChartFamily P.zero q) = cgpGlobalMap P.toLocalChartFamily P.zero q := by
    rw [gafStageQ_starProjection_globalMap]
    exact congrFun (cgpProjMap_univ_GAF P.toLocalChartFamily P.zero) q
  rw [hF] at hmw
  refine ⟨q, hqA, hball, hcut, hη', ?_, ?_, ?_, ?_, hmw⟩
  · have hs1 : 3 * ρ j.1 / 4 ≤ ρ q := hs.1
    linarith
  · have hs2 : ρ q ≤ 5 * ρ j.1 / 4 := hs.2
    linarith
  · change blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (cgpMarkerTag P.toLocalChartFamily P.zero (.inl j)) (cgpGlobalMap P.toLocalChartFamily P.zero q) = _
    rw [hb.1, hcut', mul_one]
    rfl
  · change blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (cgpMarkerTag P.toLocalChartFamily P.zero (.inl j)) (cgpGlobalMap P.toLocalChartFamily P.zero q) = _
    rw [hb.2, hcut', mul_one]
    rfl

/-- **CGP05, edge stage, full marker**: every point of the edge patch
`V_j⁰ = {w ∈ Z₂ | v_j(w) > .9R_j, |u_j(w)| < 5.5ΔR_j}` (`u_j` the ACTUAL axis coordinate of the
block, one-dimensional) has an original witness `q ∈ Ã₂` (so `t(q) ≤ 8Δ`, the enlarged carrier)
in `B(c_j, 100Δρ_j)` with FULL marker, `|η_j(q)| < 6.2Δ`, scale in `[3R_j/4, 5R_j/4]` and (MW). -/
theorem cgp05_edge_full_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    (O : Cfs15StageOutput (gafStageDim 1) Kj (Ξ 1) (cw 1) (gafCloud P.toLocalChartFamily P.zero 1)
      (gafCloudEnlarged P.toLocalChartFamily P.zero 1) (fun x => S 1 * ρ (C.sel 1 x)) (C.plane 1))
    (j : P.edge.finite_centres.toFinset) :
    ∀ w ∈ markedPatch_BPRE O.Z (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
        (gafEdgeMarker P.toLocalChartFamily P.zero j) (ρ j.1) Δ,
      ∃ q ∈ gafStageEnlargement P.toLocalChartFamily P.zero 1,
        q ∈ ball j.1 (100 * Δ * ρ j.1) ∧ cgpHeight P.toLocalChartFamily q ≤ 8 * Δ ∧
        P.edge.cutoff j.1 q = 1 ∧ |P.edge.coord j.1 q| < 31 / 5 * Δ ∧
        3 / 4 * ρ j.1 ≤ ρ q ∧ ρ q ≤ 5 / 4 * ρ j.1 ∧
        axisCoordCLM_BAS (gafEdgeVector P.toLocalChartFamily P.zero j
            ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection
              (cgpGlobalMap P.toLocalChartFamily P.zero q))) = ρ j.1 * P.edge.coord j.1 q ∧
        gafEdgeMarker P.toLocalChartFamily P.zero j
            ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection
              (cgpGlobalMap P.toLocalChartFamily P.zero q)) = ρ j.1 ∧
        ‖w - (gafStageQ P.toLocalChartFamily P.zero 1).starProjection
            (cgpGlobalMap P.toLocalChartFamily P.zero q)‖ < 25 / 12 * Ξ 1 * S 1 * ρ j.1 := by
  obtain ⟨hΛ, hΔ, -⟩ := C.std
  have hΔ0 : 0 < Δ := by linarith
  have htag : cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inr j)) ∈
      gafStageTags P.toLocalChartFamily P.zero 1 := by
    change cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inr j)) ∈ cgpQ2Tags P.toLocalChartFamily P.zero
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  intro w hw
  obtain ⟨q, hqA, hζ, hη, hmw⟩ := C.cgp05_BAS O (a := .inr (.inr j)) htag axisCoordCLM_BAS
    norm_axisCoordCLM_le_BAS hΔ w hw
  have hη' : |P.edge.coord j.1 q| < 31 / 5 * Δ := by
    have h := hη
    change ‖axisCoordCLM_BAS (planeAxis (P.edge.coord j.1 q))‖ < 31 / 5 * Δ at h
    rwa [axisCoordCLM_planeAxis_BAS, Real.norm_eq_abs] at h
  have hne : cgpMarkerCutoff P.toLocalChartFamily (.inr (.inr j)) q ≠ 0 := by linarith
  have hball := cgpMarkerCutoff_ne_zero P.toLocalChartFamily hΔ0 (.inr (.inr j)) q hne
  have hj : j.1 ∈ P.edge.centres := (Set.Finite.mem_toFinset _).mp j.2
  have ht : cgpHeight P.toLocalChartFamily q ≤ 8 * Δ := by
    obtain ⟨j', -, -, ht'⟩ := hqA
    exact ht'
  have hcut : P.edge.cutoff j.1 q = 1 :=
    P.edge.cutoff_eq_one_of_le hΔ0 hj hball (by linarith) ht
  have hs := cgpMarkerCutoff_scale_lip_GAF4 P.toLocalChartFamily hΔ hΛ C.small_BAS
    (.inr (.inr j)) q hne
  have hb := markerBlock_projMap_BAS P.toLocalChartFamily P.zero htag axisCoordCLM_BAS q
  have hcut' : cgpMarkerCutoff P.toLocalChartFamily (.inr (.inr j)) q = 1 := hcut
  refine ⟨q, hqA, hball, ht, hcut, hη', ?_, ?_, ?_, ?_, hmw⟩
  · have hs1 : 3 * ρ j.1 / 4 ≤ ρ q := hs.1
    linarith
  · have hs2 : ρ q ≤ 5 * ρ j.1 / 4 := hs.2
    linarith
  · have h := hb.1
    rw [hcut', mul_one] at h
    change axisCoordCLM_BAS (blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inr j))) _) = _
    rw [← ContinuousLinearMap.comp_apply, h]
    change ρ j.1 • axisCoordCLM_BAS (planeAxis (P.edge.coord j.1 q)) = _
    rw [axisCoordCLM_planeAxis_BAS, smul_eq_mul]
  · have h := hb.2
    rw [hcut', mul_one] at h
    exact h

/-- **CGP05, slim stage, full marker**: every point of the slim patch
`V_j⁰ = {w ∈ Z₃ | v_j(w) > .9R_j, |u_j(w)| < 5.5·10⁵ΔR_j}` (`u_j` the ACTUAL axis coordinate,
one-dimensional) has an original witness `q ∈ Ã₃` in `B(c_j, 10⁶Δρ_j)` with FULL marker,
`|η_j(q)| < 6.2·10⁵Δ`, scale in `[3R_j/4, 5R_j/4]` and (MW). -/
theorem cgp05_slim_full_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    (O : Cfs15StageOutput (gafStageDim 2) Kj (Ξ 2) (cw 2) (gafCloud P.toLocalChartFamily P.zero 2)
      (gafCloudEnlarged P.toLocalChartFamily P.zero 2) (fun x => S 2 * ρ (C.sel 2 x)) (C.plane 2))
    (j : P.slim.finite_centres.toFinset) :
    ∀ w ∈ markedPatch_BPRE O.Z (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
        (gafSlimMarker P.toLocalChartFamily P.zero j) (ρ j.1) (10 ^ 5 * Δ),
      ∃ q ∈ gafStageEnlargement P.toLocalChartFamily P.zero 2,
        q ∈ ball j.1 (1000000 * Δ * ρ j.1) ∧ P.slim.cutoff j.1 q = 1 ∧
        |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord q| < 31 / 5 * (10 ^ 5 * Δ) ∧
        3 / 4 * ρ j.1 ≤ ρ q ∧ ρ q ≤ 5 / 4 * ρ j.1 ∧
        axisCoordCLM_BAS (gafSlimVector P.toLocalChartFamily P.zero j
            ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection
              (cgpGlobalMap P.toLocalChartFamily P.zero q))) =
          ρ j.1 * (P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord q ∧
        gafSlimMarker P.toLocalChartFamily P.zero j
            ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection
              (cgpGlobalMap P.toLocalChartFamily P.zero q)) = ρ j.1 ∧
        ‖w - (gafStageQ P.toLocalChartFamily P.zero 2).starProjection
            (cgpGlobalMap P.toLocalChartFamily P.zero q)‖ < 25 / 12 * Ξ 2 * S 2 * ρ j.1 := by
  obtain ⟨hΛ, hΔ, -⟩ := C.std
  have hΔ0 : 0 < Δ := by linarith
  have htag : cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inl j)) ∈
      gafStageTags P.toLocalChartFamily P.zero 2 := by
    change cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inl j)) ∈ cgpQ3Tags P.toLocalChartFamily P.zero
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have hℓ : (1 : ℝ) ≤ 10 ^ 5 * Δ := by nlinarith
  intro w hw
  obtain ⟨q, hqA, hζ, hη, hmw⟩ := C.cgp05_BAS O (a := .inr (.inl j)) htag axisCoordCLM_BAS
    norm_axisCoordCLM_le_BAS hℓ w hw
  have hj : j.1 ∈ P.slim.centres := (Set.Finite.mem_toFinset _).mp j.2
  have hη' : |(P.slim.centre j.1 hj).coord q| < 31 / 5 * (10 ^ 5 * Δ) := by
    have h := hη
    change ‖axisCoordCLM_BAS (planeAxis ((P.slim.centre j.1 hj).coord q))‖ < 31 / 5 * (10 ^ 5 * Δ)
      at h
    rwa [axisCoordCLM_planeAxis_BAS, Real.norm_eq_abs] at h
  have hne : cgpMarkerCutoff P.toLocalChartFamily (.inr (.inl j)) q ≠ 0 := by linarith
  have hball := cgpMarkerCutoff_ne_zero P.toLocalChartFamily hΔ0 (.inr (.inl j)) q hne
  have hball' : q ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1) := by
    have h : q ∈ ball j.1 (1000000 * Δ * ρ j.1) := hball
    norm_num
    exact h
  have hcut : P.slim.cutoff j.1 q = 1 := by
    unfold SlimFamily.cutoff
    rw [dite_eq_left hj]
    exact (P.slim.centre j.1 hj).cutoff_eq_one_of_abs_coord_le hball' (by linarith)
  have hs := cgpMarkerCutoff_scale_lip_GAF4 P.toLocalChartFamily hΔ hΛ C.small_BAS
    (.inr (.inl j)) q hne
  have hb := markerBlock_projMap_BAS P.toLocalChartFamily P.zero htag axisCoordCLM_BAS q
  have hcut' : cgpMarkerCutoff P.toLocalChartFamily (.inr (.inl j)) q = 1 := hcut
  refine ⟨q, hqA, hball, hcut, hη', ?_, ?_, ?_, ?_, hmw⟩
  · have hs1 : 3 * ρ j.1 / 4 ≤ ρ q := hs.1
    linarith
  · have hs2 : ρ q ≤ 5 * ρ j.1 / 4 := hs.2
    linarith
  · have h := hb.1
    rw [hcut', mul_one] at h
    change axisCoordCLM_BAS (blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inl j))) _) = _
    rw [← ContinuousLinearMap.comp_apply, h]
    change ρ j.1 • axisCoordCLM_BAS (planeAxis ((P.slim.centre j.1 hj).coord q)) = _
    rw [axisCoordCLM_planeAxis_BAS, smul_eq_mul]
  · have h := hb.2
    rw [hcut', mul_one] at h
    exact h

end Gaf02Chain

end DifferentialGeometry.Geometry.Collapse
