import DifferentialGeometry.Geometry.Fibration.ActualStageChainE
import DifferentialGeometry.Geometry.Fibration.ActualStageChainWitness
import DifferentialGeometry.Geometry.Fibration.ActualStagePlaneZeroBlock
import DifferentialGeometry.Geometry.Fibration.ActualInnerSections

/-!
# CGP04, whole-small-block form, on `Gaf02ChainE`

Blueprint `master207B.tex`, CGP04 (B:4057–4082, (WE)): for a selected centre `y` and a retained
`I_+` block `i` with `R_i < σ_y/16`, `J_i w = 0` for ALL `w ∈ W ∩ B(y, 20b r(y))` (`J_i` = the
projection onto the WHOLE block); these balls cover `W`. Review 71 (D71-4, D71-13): the
whole-small-block form goes through `ChainE`'s enhanced planes (`.small_block_plane` of lane
C14-PLANES) and `plane_eq`; the marker form is `Gaf02Chain.cgp04_BAS` (C14-BASES G1–G2).

Route. CFS24's pointwise spectral calculation (`cgp04_kernel_BAS`) applied to the functional
`⟪J w, J ·⟫` gives the block version `cgp04_block_kernel_BASP`. Its inputs on the chain:

* VALUE: a cloud point `i = π_st𝓔⁰(q₀)` with `ρ(sel i) > (25/3)R_a` has a vanishing cutoff `ζ_a(q₀)`
  (FC01's scale window), so the WHOLE `a` block `(R_aζ_a η_a, R_aζ_a)` of `π_st𝓔⁰(q₀)` vanishes
  (`blockProj_eq_zero_of_large_BASP`, any `Gaf02Chain`);
* PLANE: `ρ(ref i) ≥ (4/5)ρ(pre i) ≥ (12/25)ρ(sel i) > 4R_a` (the reference chart's scale window and
  the two-preimage ratio), so the enhanced plane at `i` kills the whole block
  (`FirstStagePlanes_PLN.small_block_plane`: `ρ(c) ≤ ρ(a)/2`; edge / slim: `ρ(c) ≤ .99ρ(a)`); the
  chain's plane IS the enhanced plane (`plane_eq`).

Main statements (namespace `Gaf02ChainE`):
* `cgp04_block_BASP` (uniform in the stage; any stage output `O` with the chain's cloud, radius and
  planes): `R_a < ρ(sel y)/16` ⇒ `J_a = 0` on `Z ∩ B(y, 20Ξ⁻¹r_y)`.
* `cgp04_block_zeroSet_BASP`: on the slot's native zero set every `w` lies in such a selected ball;
  a nonzero `a` block at `w` forces `ρ(sel y) ≤ 16R_a`.
* Per stage, the stage's own markers: `cgp04_circle_block_BASP` (stage 0),
  `cgp04_edge_block_BASP` (stage 1), `cgp04_slim_block_BASP` (stage 2).
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

/-- **CGP04, whole-block kernel** (CFS24's calculation for a vector-valued block projection): if
every cloud point `i` with `r_i > τ` has `J i = 0` and `P_i ⊆ ker J`, then for every selected `y`
with `r_y > (5/3)τ`, `J = 0` on `Z ∩ B(y, 20ε⁻¹r_y)`. -/
theorem cgp04_block_kernel_BASP {H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [NormedAddCommGroup F] [InnerProductSpace ℝ F] {k K : ℕ} {ε cw : ℝ}
    {S T : Set H} {r : H → ℝ} {P : H → Submodule ℝ H} (O : Cfs15StageOutput k K ε cw S T r P)
    (J : H →L[ℝ] F) (hST : S ⊆ T)
    (hmcb : ∀ x ∈ T, ∀ y ∈ T, dist y x ≤ 128 * ε⁻¹ * max (r y) (r x) → r y ≤ 5 / 3 * r x)
    {τ : ℝ} (hvanish : ∀ i ∈ S, τ < r i → J i = 0 ∧ P i ≤ LinearMap.ker (J : H →ₗ[ℝ] F))
    {y : H} (hy : y ∈ O.I) (hry : 5 / 3 * τ < r y) {w : H} (hw : w ∈ O.Z)
    (hwy : w ∈ ball y (20 * ε⁻¹ * r y)) : J w = 0 := by
  have h := cgp04_kernel_BAS O ((innerSL ℝ (J w)).comp J) hST hmcb (τ := τ) (fun i hi hri => by
    obtain ⟨h0, hP⟩ := hvanish i hi hri
    refine ⟨by simp [h0], fun v hv => ?_⟩
    have hJv : J v = 0 := hP hv
    simp [hJv]) hy hry hw hwy
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply] at h
  exact inner_self_eq_zero.mp h

/-- A point of `WithLp 2 (A × B)` with vanishing components is zero. -/
theorem withLp_prod_eq_zero_BASP {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    {z : WithLp 2 (A × B)} (h1 : z.fst = 0) (h2 : z.snd = 0) : z = 0 := by
  have h : WithLp.ofLp z = 0 := Prod.ext h1 h2
  calc z = WithLp.toLp 2 (WithLp.ofLp z) := (WithLp.toLp_ofLp 2 z).symm
    _ = WithLp.toLp 2 0 := by rw [h]
    _ = 0 := rfl

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

namespace Gaf02Chain

variable {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **The whole block of a large cloud point vanishes** (value half of CGP04's input): for a
retained marker `a` surviving `π_st` and a cloud point `i` with `ρ(sel_st i) > (25/3)R_a`,
`J_a i = 0` (the cutoff `ζ_a` vanishes at the core preimage, so both components of the block are
zero). -/
theorem blockProj_eq_zero_of_large_BASP (C : Gaf02Chain P Kj Ξ Γ S eg c cw) {st : Fin 3}
    {a : CGPMarkerIndex P.toLocalChartFamily}
    (ha : cgpMarkerTag P.toLocalChartFamily P.zero a ∈ gafStageTags P.toLocalChartFamily P.zero st)
    {i : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hi : i ∈ gafCloud P.toLocalChartFamily P.zero st)
    (hlarge : 25 / 3 * ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ (C.sel st i)) :
    blockProjCLM_PLN (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (cgpMarkerTag P.toLocalChartFamily P.zero a) i = 0 := by
  have hΛ : 0 ≤ Λ := C.std.1
  have hΔ : 1 ≤ Δ := C.std.2.1
  have hi' := hi
  obtain ⟨q₀, -, hq₀⟩ := hi
  have hq₀' : (gafStageQ P.toLocalChartFamily P.zero st).starProjection
      (cgpGlobalMap P.toLocalChartFamily P.zero q₀) = i := by
    rw [gafStageQ_starProjection_globalMap]
    exact hq₀
  have hratio := gafCloud_preimage_ratio_two_GAF5 P.toLocalChartFamily P.zero hΔ hΛ C.small_BAS st
    (C.sel st) (C.hsel st) i hi' q₀ hq₀'
  have hc := hρ (cgpMarkerCentre P.toLocalChartFamily a)
  have hz : cgpMarkerCutoff P.toLocalChartFamily a q₀ = 0 := by
    by_contra hz
    have hs := cgpMarkerCutoff_scale_lip_GAF4 P.toLocalChartFamily hΔ hΛ C.small_BAS a q₀ hz
    linarith [hs.2, hratio.2]
  have hb := markerBlock_projMap_BAS P.toLocalChartFamily P.zero ha
    (ContinuousLinearMap.id ℝ ℝ²) q₀
  rw [hz, mul_zero, zero_smul, hq₀'] at hb
  rw [blockProjCLM_apply_PLN]
  exact withLp_prod_eq_zero_BASP hb.1 hb.2

end Gaf02Chain

namespace Gaf02ChainE

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- The preimage scale of a cloud point: a point `q` with `π_st𝓔⁰(q) = i ∈ S_st` has
`ρ(sel_st i) ≤ (5/3)ρ(q)`. -/
theorem sel_le_of_preimage_BASP (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) {st : Fin 3}
    {i : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hi : i ∈ gafCloud P.toLocalChartFamily P.zero st) {q : X}
    (hq : cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero st) q =
      i) :
    ρ (C.toChain.sel st i) ≤ 5 / 3 * ρ q := by
  have hΛ : 0 ≤ Λ := C.toChain.std.1
  have hΔ : 1 ≤ Δ := C.toChain.std.2.1
  have hxe := gafCloud_subset_enlarged P.toLocalChartFamily P.zero (by linarith) st hi
  exact (gafCloudEnlarged_preimage_ratio_BAS P.toLocalChartFamily P.zero hΔ hΛ C.toChain.small_BAS
    st (C.toChain.sel st) (C.toChain.hsel st) i hxe q
    ((gafStageQ_starProjection_globalMap P.toLocalChartFamily P.zero st q).trans hq)).2

/-- **The reference of the first-stage plane is large**: `ρ(ref i) ≥ (12/25)ρ(sel₁ i)`. -/
theorem ref_scale_zero_BASP (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    {i : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hi : i ∈ gafCloud P.toLocalChartFamily P.zero 0) :
    12 / 25 * ρ (C.toChain.sel 0 i) ≤ ρ (C.planes₀.ref ⟨i, hi⟩).1 := by
  have hΛ : 0 ≤ Λ := C.toChain.std.1
  have hΔ : 1 ≤ Δ := C.toChain.std.2.1
  have hsm := C.toChain.small_BAS
  have hps := C.planes₀.pre_spec ⟨i, hi⟩
  have hsc := scale_mem_of_dist_lt_KC P.toLocalChartFamily.lipschitz_scale hΛ
    (hρ (C.planes₀.ref ⟨i, hi⟩).1) hps.1 (by nlinarith)
  have hr := C.sel_le_of_preimage_BASP hi hps.2.2
  linarith [hsc.2]

/-- **The reference of the edge-stage plane is large**: `ρ(ref i) ≥ (12/25)ρ(sel₂ i)`. -/
theorem ref_scale_one_BASP (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    {i : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hi : i ∈ gafCloud P.toLocalChartFamily P.zero 1) :
    12 / 25 * ρ (C.toChain.sel 1 i) ≤ ρ (C.planes₁.ref ⟨i, hi⟩).1 := by
  have hΛ : 0 ≤ Λ := C.toChain.std.1
  have hΔ : 1 ≤ Δ := C.toChain.std.2.1
  have hsm := C.toChain.small_BAS
  have hps := C.planes₁.pre_spec ⟨i, hi⟩
  have hsc := scale_mem_of_dist_lt_KC P.toLocalChartFamily.lipschitz_scale hΛ
    (hρ (C.planes₁.ref ⟨i, hi⟩).1) hps.1 (by nlinarith)
  have hr := C.sel_le_of_preimage_BASP hi hps.2.2.2
  linarith [hsc.2]

/-- **The reference of the slim-stage plane is large**: `ρ(ref i) ≥ (12/25)ρ(sel₃ i)`. -/
theorem ref_scale_two_BASP (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    {i : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hi : i ∈ gafCloud P.toLocalChartFamily P.zero 2) :
    12 / 25 * ρ (C.toChain.sel 2 i) ≤ ρ (C.planes₂.ref ⟨i, hi⟩).1 := by
  have hΛ : 0 ≤ Λ := C.toChain.std.1
  have hΔ : 1 ≤ Δ := C.toChain.std.2.1
  have hsm := C.toChain.small_BAS
  have hps := C.planes₂.pre_spec ⟨i, hi⟩
  have hsc := scale_mem_of_dist_lt_KC P.toLocalChartFamily.lipschitz_scale hΛ
    (hρ (C.planes₂.ref ⟨i, hi⟩).1) hps.1 (by norm_num at hsm ⊢; linarith)
  have hr := C.sel_le_of_preimage_BASP hi hps.2.2
  linarith [hsc.2]

/-- **Whole small block of the chain's first-stage plane** (`plane_eq` + `small_block_plane`):
`ρ(sel₁ i) > (25/3)R_a` ⇒ `L_i ≤ ker J_a`. -/
theorem plane_le_ker_block_zero_BASP (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (a : CGPMarkerIndex P.toLocalChartFamily)
    {i : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hi : i ∈ gafCloud P.toLocalChartFamily P.zero 0)
    (hlarge : 25 / 3 * ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ (C.toChain.sel 0 i)) :
    C.toChain.plane 0 i ≤ LinearMap.ker ((blockProjCLM_PLN (V := fun _ : CGPTag
        P.toLocalChartFamily P.zero => ℝ²) (cgpMarkerTag P.toLocalChartFamily P.zero a) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] WithLp 2 (ℝ² × ℝ)) :
        BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] WithLp 2 (ℝ² × ℝ)) := by
  have href := C.ref_scale_zero_BASP hi
  have hc := hρ (cgpMarkerCentre P.toLocalChartFamily a)
  rw [C.plane_eq.1]
  exact C.planes₀.small_block_plane hi a (by linarith)

/-- **Whole small block of the chain's edge-stage plane**: `ρ(sel₂ i) > (25/3)R_a` ⇒
`L_i ≤ ker J_a`. -/
theorem plane_le_ker_block_one_BASP (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (a : CGPMarkerIndex P.toLocalChartFamily)
    {i : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hi : i ∈ gafCloud P.toLocalChartFamily P.zero 1)
    (hlarge : 25 / 3 * ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ (C.toChain.sel 1 i)) :
    C.toChain.plane 1 i ≤ LinearMap.ker ((blockProjCLM_PLN (V := fun _ : CGPTag
        P.toLocalChartFamily P.zero => ℝ²) (cgpMarkerTag P.toLocalChartFamily P.zero a) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] WithLp 2 (ℝ² × ℝ)) :
        BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] WithLp 2 (ℝ² × ℝ)) := by
  obtain ⟨hΛ, hΔ, -, -, hLΛ, -⟩ := C.toChain.std
  have href := C.ref_scale_one_BASP hi
  have hc := hρ (cgpMarkerCentre P.toLocalChartFamily a)
  rw [C.plane_eq.2.1]
  exact C.planes₁.small_block_plane (by linarith) hΛ hLΛ hi a (by linarith)

/-- **Whole small block of the chain's slim-stage plane**: `ρ(sel₃ i) > (25/3)R_a` ⇒
`L_i ≤ ker J_a`. -/
theorem plane_le_ker_block_two_BASP (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (a : CGPMarkerIndex P.toLocalChartFamily)
    {i : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hi : i ∈ gafCloud P.toLocalChartFamily P.zero 2)
    (hlarge : 25 / 3 * ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ (C.toChain.sel 2 i)) :
    C.toChain.plane 2 i ≤ LinearMap.ker ((blockProjCLM_PLN (V := fun _ : CGPTag
        P.toLocalChartFamily P.zero => ℝ²) (cgpMarkerTag P.toLocalChartFamily P.zero a) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] WithLp 2 (ℝ² × ℝ)) :
        BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] WithLp 2 (ℝ² × ℝ)) := by
  obtain ⟨hΛ, hΔ, -, -, hLΛ, -⟩ := C.toChain.std
  have href := C.ref_scale_two_BASP hi
  have hc := hρ (cgpMarkerCentre P.toLocalChartFamily a)
  rw [C.plane_eq.2.2]
  exact C.planes₂.small_block_plane (by linarith) hΛ hLΛ hi a (by linarith)

/-- **Whole small block of the chain's planes, every stage** (uniform form). -/
theorem plane_le_ker_block_BASP (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) (st : Fin 3)
    (a : CGPMarkerIndex P.toLocalChartFamily)
    {i : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hi : i ∈ gafCloud P.toLocalChartFamily P.zero st)
    (hlarge : 25 / 3 * ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ (C.toChain.sel st i)) :
    C.toChain.plane st i ≤ LinearMap.ker ((blockProjCLM_PLN (V := fun _ : CGPTag
        P.toLocalChartFamily P.zero => ℝ²) (cgpMarkerTag P.toLocalChartFamily P.zero a) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] WithLp 2 (ℝ² × ℝ)) :
        BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] WithLp 2 (ℝ² × ℝ)) := by
  fin_cases st
  · exact C.plane_le_ker_block_zero_BASP a hi hlarge
  · exact C.plane_le_ker_block_one_BASP a hi hlarge
  · exact C.plane_le_ker_block_two_BASP a hi hlarge

/-- **CGP04 on `Gaf02ChainE`, whole-small-block form** (uniform in the stage): for a retained marker
`a` surviving `π_st`, a selected centre `y` of a stage output `O` (the chain's cloud, radius and
planes) with `R_a < ρ(sel_st y)/16`, the WHOLE `a` block vanishes on `Z ∩ B(y, 20Ξ_st⁻¹r_y)`. -/
theorem cgp04_block_BASP (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) {st : Fin 3}
    (O : Cfs15StageOutput (gafStageDim st) Kj (Ξ st) (cw st) (gafCloud P.toLocalChartFamily P.zero st)
      (gafCloudEnlarged P.toLocalChartFamily P.zero st) (fun x => S st * ρ (C.toChain.sel st x))
      (C.toChain.plane st))
    {a : CGPMarkerIndex P.toLocalChartFamily}
    (ha : cgpMarkerTag P.toLocalChartFamily P.zero a ∈ gafStageTags P.toLocalChartFamily P.zero st)
    {y : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)} (hy : y ∈ O.I)
    (hry : ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ (C.toChain.sel st y) / 16)
    {w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)} (hw : w ∈ O.Z)
    (hwy : w ∈ ball y (20 * (Ξ st)⁻¹ * (S st * ρ (C.toChain.sel st y)))) :
    blockProjCLM_PLN (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (cgpMarkerTag P.toLocalChartFamily P.zero a) w = 0 := by
  obtain ⟨hΛ, hΔ, hμ, hτ, hLΛ, -, he, -⟩ := C.toChain.std
  obtain ⟨hΞ, hS, hmo, -⟩ := C.toChain.numbers.1 st
  have hin := cfs14_stage_inputs_GAF2 P.toLocalChartPackets hΛ hΔ hμ hτ (by linarith) hLΛ st
    (C.toChain.sel st) (C.toChain.hsel st) hΞ hS hmo
  have hc := hρ (cgpMarkerCentre P.toLocalChartFamily a)
  refine cgp04_block_kernel_BASP O _ hin.1 (fun x hx y hy' h => (hin.2.2.2 x hx y hy' h).2)
    (τ := S st * (25 / 3 * ρ (cgpMarkerCentre P.toLocalChartFamily a)))
    (fun i hi hri => ?_) hy ?_ hw hwy
  · have hl : 25 / 3 * ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ (C.toChain.sel st i) := by
      have : S st * (25 / 3 * ρ (cgpMarkerCentre P.toLocalChartFamily a)) <
          S st * ρ (C.toChain.sel st i) := hri
      exact lt_of_mul_lt_mul_left this hS.le
    exact ⟨C.toChain.blockProj_eq_zero_of_large_BASP ha hi hl, C.plane_le_ker_block_BASP st a hi hl⟩
  · have h16 : 125 / 9 * ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ (C.toChain.sel st y) := by
      linarith
    change 5 / 3 * (S st * (25 / 3 * ρ (cgpMarkerCentre P.toLocalChartFamily a))) <
      S st * ρ (C.toChain.sel st y)
    nlinarith

/-- **CGP04 on the slot's native zero set** (whole-small-block form, every stage): each
`w ∈ Z_st` lies in a selected ball `B(y, 20Ξ_st⁻¹r_y)`, `y ∈ S_st`, and a nonzero `a` block at `w`
forces `ρ(sel_st y) ≤ 16R_a` ("a positive marker at such a point forces `σ_y ≤ 16R_i`"). -/
theorem cgp04_block_zeroSet_BASP (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) {st : Fin 3}
    {a : CGPMarkerIndex P.toLocalChartFamily}
    (ha : cgpMarkerTag P.toLocalChartFamily P.zero a ∈ gafStageTags P.toLocalChartFamily P.zero st)
    {w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hw : w ∈ (C.toChain.slot st).zeroSet) :
    ∃ y ∈ gafCloud P.toLocalChartFamily P.zero st,
      w ∈ ball y (20 * (Ξ st)⁻¹ * (S st * ρ (C.toChain.sel st y))) ∧
      (blockProjCLM_PLN (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero a) w ≠ 0 →
        ρ (C.toChain.sel st y) ≤ 16 * ρ (cgpMarkerCentre P.toLocalChartFamily a)) := by
  cases hO : C.toChain.slot st with
  | active O =>
    rw [hO, Gaf02StageSlot.zeroSet_active] at hw
    obtain ⟨y, hy, hwy⟩ := exists_selected_mem_ball_BAS O hw
    refine ⟨y, O.I_subset hy, hwy, fun hne => ?_⟩
    by_contra hlt
    exact hne (C.cgp04_block_BASP O ha hy (by linarith [not_le.mp hlt]) hw hwy)
  | inactive h =>
    rw [hO] at hw
    exact absurd hw (Set.notMem_empty w)

/-- **CGP04, circle markers at stage one** (whole-small-block form on `Z₁`). -/
theorem cgp04_circle_block_BASP (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (j : P.toLocalChartFamily.circle.finite_centres.toFinset)
    {w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hw : w ∈ (C.toChain.slot 0).zeroSet) :
    ∃ y ∈ gafCloud P.toLocalChartFamily P.zero 0,
      w ∈ ball y (20 * (Ξ 0)⁻¹ * (S 0 * ρ (C.toChain.sel 0 y))) ∧
      (blockProjCLM_PLN (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero (.inl j)) w ≠ 0 →
        ρ (C.toChain.sel 0 y) ≤ 16 * ρ j.1) :=
  C.cgp04_block_zeroSet_BASP (a := .inl j) (Finset.mem_univ _) hw

/-- **CGP04, edge markers at stage two** (whole-small-block form on `Z₂`). -/
theorem cgp04_edge_block_BASP (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (j : P.toLocalChartFamily.edge.finite_centres.toFinset)
    {w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hw : w ∈ (C.toChain.slot 1).zeroSet) :
    ∃ y ∈ gafCloud P.toLocalChartFamily P.zero 1,
      w ∈ ball y (20 * (Ξ 1)⁻¹ * (S 1 * ρ (C.toChain.sel 1 y))) ∧
      (blockProjCLM_PLN (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inr j))) w ≠ 0 →
        ρ (C.toChain.sel 1 y) ≤ 16 * ρ j.1) :=
  C.cgp04_block_zeroSet_BASP (a := .inr (.inr j)) (by
    change cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inr j)) ∈
      cgpQ2Tags P.toLocalChartFamily P.zero
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩) hw

/-- **CGP04, slim markers at stage three** (whole-small-block form on `Z₃`). -/
theorem cgp04_slim_block_BASP (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (j : P.toLocalChartFamily.slim.finite_centres.toFinset)
    {w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hw : w ∈ (C.toChain.slot 2).zeroSet) :
    ∃ y ∈ gafCloud P.toLocalChartFamily P.zero 2,
      w ∈ ball y (20 * (Ξ 2)⁻¹ * (S 2 * ρ (C.toChain.sel 2 y))) ∧
      (blockProjCLM_PLN (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inl j))) w ≠ 0 →
        ρ (C.toChain.sel 2 y) ≤ 16 * ρ j.1) :=
  C.cgp04_block_zeroSet_BASP (a := .inr (.inl j)) (by
    change cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inl j)) ∈
      cgpQ3Tags P.toLocalChartFamily P.zero
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩) hw

end Gaf02ChainE

end DifferentialGeometry.Geometry.Collapse
