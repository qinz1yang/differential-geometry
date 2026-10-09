import DifferentialGeometry.Geometry.Fibration.ActualStageChainGaf07FibreTypes
import DifferentialGeometry.Geometry.Fibration.ActualStageChainFinalBases

/-!
# GAF05 (slim patches) and GAF07 (whole slim fibres) on `Gaf02ChainE` with BASES' `W₃`

Blueprint `master207B.tex`, GAF05 (B:5971–5977) and GAF07 (B:6049–6165), slim stage (`j = 3`,
`ℓ_i = 10⁵Δ`), on ONE chain on the enhanced planes `C : Gaf02ChainE` with BASES' slim patches
`V_i⁰ = C.toChain.slimPatch_BAS i` (CGP07, `Gaf02Chain.cgp07_slim_BAS`, lane C14-BASES-P) and final
base `W₃ = C.toChain.finalBase_BAS 2 = Θ₃(V₃⁰)`, `Θ₃ = id` (`Gaf02Chain.finalBase_inter_slim_BAS`).

* `Gaf02ChainE.gaf05_slimPatch_marker_GAFC`: `v_i ≡ R_i` on `V_i⁰` (every patch point is `f₃(p)` for
  an original threshold-6 plateau point, GAF05's plateau clause); `gaf05_slimBase_marker_GAFC`: the
  same on `W₃ ∩ {marked i} = V_i⁰`.
* `Gaf02ChainE.gaf07_slim_onto_GAFC`: every point of `W₃` is `π₃E(p)`.
* `Gaf02ChainE.gaf07_slim_whole_fibre_GAFC`: for `w ∈ W₃` in the (full-norm) ratio piece of `i`
  (`v_i > .9R_i`, `‖u_i‖ < 4·10⁵Δ v_i`, GAF47's `gaf07SlimRatio_G47`), `a = proj₀(R_i⁻¹u_i(w))` has
  `|a| < 4·10⁵Δ`; the WHOLE fibre `(π₃E)⁻¹(w)` EQUALS the whole adjusted level
  `{p ∈ Y_i | g_i(p) = a}`, is homeomorphic to the original slim level and connected.
* Consumer `Gaf02ChainEJA.gaf07_slim_whole_fibre_standard_GAFC` (review 70): every such WHOLE fibre
  is the image of a smooth embedding of the standard `ClosureSphere` or `Torus`.

Not here: the AXIS-ratio base `slimBase_BAS` of BASES (`|axis u_i| < 4ℓ v_i`) needs an axis form of
GAF06 (state file: open item); the edge stage.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis
open GC.GraphManifold GC.Endpoint

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

namespace Gaf02ChainE

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- The stage-three map is the final slim image: `f₃ = π₃E` (`Θ₃ = id`). -/
theorem stageMap_two_eq_GAFC (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) (p : X) :
    C.toChain.stageMap_BAS 2 p =
      (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p) := by
  rw [C.toChain.final_factor_BAS 2 p, C.toChain.theta_two_eq_id_BAS]
  rfl

/-- **GAF05, slim patches** (B:5971–5973): `v_i ≡ R_i` on CGP07's slim patch `V_i⁰`. -/
theorem gaf05_slimPatch_marker_GAFC (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (i : P.toLocalChartFamily.slim.finite_centres.toFinset) :
    ∀ w ∈ C.toChain.slimPatch_BAS i, gafSlimMarker P.toLocalChartFamily P.zero i w = ρ i.1 := by
  intro w hw
  obtain ⟨p, ⟨hp, hη⟩, hpw⟩ := (C.toChain.cgp07_slim_BAS C.rough i).2.1 w hw
  rw [← hpw, C.stageMap_two_eq_GAFC]
  have hmk := marker_stageQ_G47 P.toLocalChartFamily P.zero (st := 2) (t := .inr (.inl i))
    (slim_mem_cgpQ3Tags P.toLocalChartFamily P.zero i) (C.toChain.E p)
  change blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl i))
    ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p)) = ρ i.1
  rw [hmk]
  exact C.gaf05_slim_plateau_G47 i hp hη

/-- **GAF05, later slim image** (B:5974–5975): `v_i ≡ R_i` on
`W₃ ∩ {marked i} = Θ₃(V_i⁰) = V_i⁰`. -/
theorem gaf05_slimBase_marker_GAFC (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (i : P.toLocalChartFamily.slim.finite_centres.toFinset) :
    ∀ w ∈ C.toChain.finalBase_BAS 2 ∩ markedCondition_BPRE
        (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i))
        (gafSlimMarker P.toLocalChartFamily P.zero i) (ρ i.1) (10 ^ 5 * Δ),
      gafSlimMarker P.toLocalChartFamily P.zero i w = ρ i.1 := by
  intro w hw
  rw [C.toChain.finalBase_inter_slim_BAS i, C.toChain.theta_two_eq_id_BAS, image_id] at hw
  exact C.gaf05_slimPatch_marker_GAFC i w hw

/-- **GAF07, onto, slim stage** (CGP07–CGP08): every point of `W₃` is `π₃E(p)`. -/
theorem gaf07_slim_onto_GAFC (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hw : w ∈ C.toChain.finalBase_BAS 2) :
    ∃ p, (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p) = w := by
  obtain ⟨w₀, hw₀, rfl⟩ := hw
  obtain ⟨_, ⟨j, rfl⟩, hj⟩ := hw₀
  obtain ⟨p, -, hp⟩ := (C.toChain.cgp07_slim_BAS C.rough j).2.1 w₀ hj
  refine ⟨p, ?_⟩
  rw [← C.stageMap_two_eq_GAFC, hp, C.toChain.theta_two_eq_id_BAS]
  rfl

/-- GAF06 at a point of a whole slim fibre over the ratio piece of `i` (`τ = 1`): `p ∈ Y_i`. -/
theorem gaf07_slim_fibre_mem_Y_GAFC (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000)
    (w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (i : P.toLocalChartFamily.slim.finite_centres.toFinset)
    (hm : 9 / 10 * ρ i.1 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inl i)) w)
    (hr : ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl i))
        w‖ < 4 * (10 ^ 5 * Δ) *
      blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl i)) w)
    (p : X) (hp : (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p) = w) :
    p ∈ gaf07SlimY_GAFC P.toLocalChartPackets i := by
  obtain ⟨-, hΔ1, -⟩ := C.toChain.std
  have ht := slim_mem_cgpQ3Tags P.toLocalChartFamily P.zero i
  have hmk := marker_stageQ_G47 P.toLocalChartFamily P.zero (st := 2) (t := .inr (.inl i)) ht
    (C.toChain.E p)
  have hvk := vector_stageQ_G47 P.toLocalChartFamily P.zero (st := 2) (t := .inr (.inl i)) ht
    (C.toChain.E p)
  rw [hp] at hmk hvk
  have h1 : (1 - (1 : ℝ)) • cgpGlobalMap P.toLocalChartFamily P.zero p +
      (1 : ℝ) • C.toChain.E p = C.toChain.E p := by
    rw [sub_self, zero_smul, zero_add, one_smul]
  obtain ⟨hpi, hη, -⟩ := C.toChain.gaf06_slim_G47 hc i p 1 ⟨zero_le_one, le_rfl⟩
    (by rw [h1, ← hmk]; exact hm) (by rw [h1, ← hmk, ← hvk]; exact hr.le)
  exact ⟨hpi, by nlinarith⟩

/-- The retained slim coordinate of BASES' patch chart is the axis of `R_i⁻¹u_i`. -/
theorem slim_retained_coord_eq_GAFC (i : P.toLocalChartFamily.slim.finite_centres.toFinset)
    (y : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) :
    ((ρ i.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i)) y =
      EuclideanSpace.proj (0 : Fin 2) ((ρ i.1)⁻¹ •
        blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inl i)) y) := by
  simp only [smul_apply, ContinuousLinearMap.comp_apply, map_smul, smul_eq_mul]
  rfl

/-- **GAF07, WHOLE slim fibres** (B:6104–6149): for `w ∈ W₃` in the ratio piece of `i`
(`v_i(w) > .9R_i`, `‖u_i(w)‖ < 4·10⁵Δ v_i(w)`), `a = proj₀(R_i⁻¹u_i(w))` has `|a| < 4·10⁵Δ`; the
WHOLE fibre `(π₃E)⁻¹(w)` EQUALS the whole adjusted level `{p ∈ Y_i | g_i(p) = a}`, is homeomorphic
to the original slim level `{p ∈ Y_i | η_i(p) = a}`, and is connected. -/
theorem gaf07_slim_whole_fibre_GAFC (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000)
    (w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hW : w ∈ C.toChain.finalBase_BAS 2)
    (i : P.toLocalChartFamily.slim.finite_centres.toFinset)
    (hm : 9 / 10 * ρ i.1 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inl i)) w)
    (hr : ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl i))
        w‖ < 4 * (10 ^ 5 * Δ) *
      blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl i)) w) :
    |EuclideanSpace.proj (0 : Fin 2) ((ρ i.1)⁻¹ •
        blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl i)) w)| <
        4 * (10 ^ 5 * Δ) ∧
      (fun p => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p)) ⁻¹' {w} =
        {p | p ∈ gaf07SlimY_GAFC P.toLocalChartPackets i ∧ C.toChain.gaf07SlimCoord_GAFC i p =
          EuclideanSpace.proj (0 : Fin 2) ((ρ i.1)⁻¹ •
            blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
              (.inr (.inl i)) w)} ∧
      Nonempty ((fun p => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection
          (C.toChain.E p)) ⁻¹' {w} ≃ₜ
        {p | p ∈ gaf07SlimY_GAFC P.toLocalChartPackets i ∧
          (P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p =
            EuclideanSpace.proj (0 : Fin 2) ((ρ i.1)⁻¹ •
              blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
                (.inr (.inl i)) w)}) ∧
      IsConnected ((fun p => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection
        (C.toChain.E p)) ⁻¹' {w}) := by
  have hri := hρ i.1
  have hY := C.gaf07_slim_fibre_mem_Y_GAFC hc w i hm hr
  -- a preimage exists; marker exactly `R_i`
  obtain ⟨p₀, hp₀⟩ := C.gaf07_slim_onto_GAFC w hW
  have hY₀ := hY p₀ hp₀
  have hV₀ := C.toChain.slim_mem_patch_of_domain5_BAS i hY₀.1 hY₀.2
  rw [C.stageMap_two_eq_GAFC, hp₀] at hV₀
  have hv : blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inl i)) w = ρ i.1 := C.gaf05_slimPatch_marker_GAFC i w hV₀
  have hpr : ∀ v : ℝ², |EuclideanSpace.proj (0 : Fin 2) v| ≤ ‖v‖ := fun v => by
    simpa using PiLp.norm_apply_le v (0 : Fin 2)
  have ha : |EuclideanSpace.proj (0 : Fin 2) ((ρ i.1)⁻¹ •
      blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl i)) w)| <
      4 * (10 ^ 5 * Δ) := by
    refine (hpr _).trans_lt ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hri), inv_mul_lt_iff₀ hri]
    rw [hv] at hr
    linarith
  have hcoord := slim_retained_coord_eq_GAFC (P := P) i
  have hinj := (C.toChain.cgp07_slim_BAS C.rough i).1.injOn
  have heq : (fun p => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection
      (C.toChain.E p)) ⁻¹' {w} =
      {p | p ∈ gaf07SlimY_GAFC P.toLocalChartPackets i ∧ C.toChain.gaf07SlimCoord_GAFC i p =
        EuclideanSpace.proj (0 : Fin 2) ((ρ i.1)⁻¹ •
          blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
            (.inr (.inl i)) w)} := by
    ext p
    constructor
    · intro hp
      have hp' : (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p) = w := hp
      refine ⟨hY p hp', ?_⟩
      change EuclideanSpace.proj (0 : Fin 2) ((ρ i.1)⁻¹ •
        blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl i))
          ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p))) = _
      rw [hp']
    · rintro ⟨hpY, hpa⟩
      have hVp := C.toChain.slim_mem_patch_of_domain5_BAS i hpY.1 hpY.2
      rw [C.stageMap_two_eq_GAFC] at hVp
      change (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p) = w
      refine hinj hVp hV₀ ?_
      rw [hcoord, hcoord]
      exact hpa
  obtain ⟨⟨φ⟩, hconn, -⟩ := C.toChain.gaf07_slim_level_GAFC hc i ha
  refine ⟨ha, heq, ⟨(Homeomorph.setCongr heq).trans φ.symm⟩, ?_⟩
  rw [heq]
  exact hconn

end Gaf02ChainE

namespace Gaf02ChainEJA

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} {cadj : ℝ}

/-- **Consumer: GAF07 `j = 3` WHOLE fibres, standard smooth type** (review 70): on a chain with (JA)
(`K ≥ 5`, manifold orientation `oM`), for `w ∈ W₃` in the ratio piece of `i`, the WHOLE fibre
`(π₃E)⁻¹(w)` is connected and is the image of a smooth embedding of the standard `ClosureSphere` or
of the standard `Torus`. -/
theorem gaf07_slim_whole_fibre_standard_GAFC (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj)
    (hK : 5 ≤ K) (oM : ManifoldOrientation 𝓘(ℝ, E3) X 3)
    (w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hW : w ∈ C.toChain.finalBase_BAS 2)
    (i : P.toLocalChartFamily.slim.finite_centres.toFinset)
    (hm : 9 / 10 * ρ i.1 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inl i)) w)
    (hr : ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl i))
        w‖ < 4 * (10 ^ 5 * Δ) *
      blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl i)) w) :
    IsConnected ((fun p => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection
        (C.toChain.E p)) ⁻¹' {w}) ∧
      ((∃ f : ClosureSphere.{0} → X, IsSmoothEmbedding (𝓡 2) 𝓘(ℝ, E3) ∞ f ∧
          range f = (fun p => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection
            (C.toChain.E p)) ⁻¹' {w}) ∨
        (∃ f : Torus → X, IsSmoothEmbedding torusModel 𝓘(ℝ, E3) ∞ f ∧
          range f = (fun p => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection
            (C.toChain.E p)) ⁻¹' {w})) := by
  obtain ⟨ha, heq, -, hconn⟩ :=
    C.toGaf02ChainE.gaf07_slim_whole_fibre_GAFC C.c_two_lt w hW i hm hr
  refine ⟨hconn, ?_⟩
  rw [heq]
  exact C.toChain.gaf07_slim_level_standard_GAFC C.c_two_lt hK oM i ha

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
