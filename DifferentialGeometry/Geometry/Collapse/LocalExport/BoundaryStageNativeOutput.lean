import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEnhancedPlaneSpec
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceChain
import DifferentialGeometry.Geometry.Fibration.ActualCfs15StageOutputMean
import DifferentialGeometry.Geometry.Fibration.ActualCloudLargeCover

/-!
# BCG03: the native CFS15 stage output in `H^∂` (lane BAUG-C, G4)

Draft 61 §3.1–§3.2, D61-6: the native output of the boundary chain is the CLOSED
`Cfs15StageOutput` (D59-3) applied in the ambient `H^∂ = BoundaryAmbient_BIF`; the CFS15 kernel is
reused, closed-family theorems with `CompactSpace X` / a global cover are not. The compactness of the
ORIGINAL carrier `W` (with BAUG-A's smoothness of `F_∂`, `boundaryOriginalMap_smooth`) supplies the
total boundedness of the stage clouds and the per-member radius bounds (native selection only);
the scale block `(0, ρ)` kept in every `Q_j^∂` supplies (MCb).

* generic: `blockMarkerCLM_blockRestrict_BAUGC`, `abs_blockMarkerCLM_le_BAUGC`,
  `radius_ratio_of_scale_BAUGC` (the (MCb) arithmetic);
* `scaleMarker_stageProj_BAUGC` (`ℓ_ρ(π_j F_∂(q)) = ρ(q)` when the scale tag is kept),
  `scaleCLM_BAUGC_eq_scaleMarker_BIF` (G2's `v_scale` is BIFACE's `scaleMarker_BIF`);
* `BoundaryAugmentedData.EnhancedPlaneSpec.stage_inputs_BAUGC`: the stage-uniform read-off of a
  stage's plane spec (`S_j ⊆ S̃_j`, scale kept, `π_j F_∂ ∘ q̂ = id` on `S̃_j`, dimension, (CS) at
  radius `D.stageRadius`);
* `boundary_cfs14_stage_inputs_BAUGC`: CFS14's hypotheses on the boundary stage clouds (the analogue
  of `cfs14_stage_inputs_GAF2`, from `W` compact, not from a `CompactSpace` carrier of the family);
* **`boundaryStage_output_BAUGC`** (the analogue of `gafStage_output_GAF8`): at the register's
  modulus, an early `c_w` and, on every supply / slot / augmented data with the stage's plane spec,
  a `Cfs15StageOutput (gafStageDim st) Kj (Ξ Γ) c_w (Φ.stageCloud st) (Φ.stageCloudEnlarged st)
  (D.stageRadius st Σ) (D.stagePlane st)` — exactly the `active` slot type of
  `BoundaryStageSlot_BIF`;
* consumer **`boundaryStage_slot_with_mean_BAUGC`**: the same output as an ACTIVE
  `BoundaryStageSlot_BIF`, with GAF03's locality (three levels), (SM) and (SMV) on that ONE output.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

section Generic

variable {κ : Type*} [Fintype κ] {V : κ → Type*} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, InnerProductSpace ℝ (V i)]

omit [Fintype κ] in
/-- A kept block keeps its marker: `v_t(π_s y) = v_t(y)` for `t ∈ s`. -/
theorem blockMarkerCLM_blockRestrict_BAUGC [DecidableEq κ] (s : Finset κ) {t : κ} (ht : t ∈ s)
    (y : BlockSpace V) : blockMarkerCLM (V := V) t (blockRestrict s y) = blockMarkerCLM t y := by
  simp only [blockMarkerCLM_apply, blockRestrict_apply, ht, ite_true]

/-- A marker is `1`-Lipschitz: `|v_t(y)| ≤ ‖y‖`. -/
theorem abs_blockMarkerCLM_le_BAUGC (t : κ) (y : BlockSpace V) :
    |blockMarkerCLM (V := V) t y| ≤ ‖y‖ := by
  rw [blockMarkerCLM_apply, ← Real.norm_eq_abs]
  exact (WithLp.norm_snd_le (x := y t)).trans (PiLp.norm_apply_le y t)

end Generic

/-- **The (MCb) arithmetic**: for positive scales with `|ρ_x − ρ_y| ≤ L·max(Σρ_y, Σρ_x)` and
`LΣ ≤ 1/5`, the radii `Σρ` are `5/3`-comparable. -/
theorem radius_ratio_of_scale_BAUGC {ρx ρy sg L : ℝ} (hx : 0 < ρx) (hy : 0 < ρy) (hsg : 0 < sg)
    (hLsg : L * sg ≤ 1 / 5) (h : |ρx - ρy| ≤ L * max (sg * ρy) (sg * ρx)) :
    sg * ρx / (5 / 3) ≤ sg * ρy ∧ sg * ρy ≤ 5 / 3 * (sg * ρx) := by
  have hmax : L * max (sg * ρy) (sg * ρx) ≤ 1 / 5 * max ρy ρx := by
    rw [← mul_max_of_nonneg _ _ hsg.le, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hLsg (le_max_of_le_left hy.le)
  have h' := h.trans hmax
  rcases le_total ρy ρx with hyx | hxy
  · rw [max_eq_right hyx] at h'
    have h1 := (abs_le.mp h').2
    constructor
    · rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 5 / 3)]
      nlinarith
    · nlinarith
  · rw [max_eq_left hxy] at h'
    have h1 := (abs_le.mp h').1
    constructor
    · rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 5 / 3)]
      nlinarith
    · nlinarith

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

/-- G2's scale functional is BIFACE's `scaleMarker_BIF`. -/
theorem BoundarySupplyCore.scaleCLM_BAUGC_eq_scaleMarker_BIF
    (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
      W g δn n B oM) : S.scaleCLM_BAUGC = S.scaleMarker_BIF :=
  rfl

section Stage

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S}

/-- **The scale of a stage point**: when the scale tag is kept in `Q_j^∂`,
`ℓ_ρ(π_j F_∂(q)) = ρ(q)`. -/
theorem scaleMarker_stageProj_BAUGC {st : Fin 3} (hsc : S.scaleTag_BAUGA ∈ Φ.stageTags st)
    (q : W.Carrier) :
    S.scaleMarker_BIF (Φ.stageProj st (S.boundaryOriginalMap q)) = S.rho q := by
  have hmem : (Sum.inl S.scaleTag_BAUGA : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count) ∈
      Φ.stageTagsAug st := Finset.inl_mem_disjSum.mpr hsc
  rw [← S.scaleMarker_boundaryOriginalMap_BIF q]
  exact blockMarkerCLM_blockRestrict_BAUGC _ hmem _

/-- **The stage-uniform read-off of a stage's plane spec**: `S_j ⊆ S̃_j`, the scale tag kept, the
radius selection `q̂ = D.stageSel st` is a selection of preimages on `S̃_j`, the dimension, and FC27's
(CS) at quality `Γ_j` and radius `D.stageRadius st Σ_j`. -/
theorem BoundaryAugmentedData.EnhancedPlaneSpec.stage_inputs_BAUGC (D : BoundaryAugmentedData S Φ)
    {Γs sgs egs : Fin 3 → ℝ} {st : Fin 3} (h : D.EnhancedPlaneSpec Γs sgs egs st) :
    Φ.stageCore st ⊆ Φ.stageEnlargement st ∧ S.scaleTag_BAUGA ∈ Φ.stageTags st ∧
    (∀ x ∈ Φ.stageCloudEnlarged st,
      Φ.stageProj st (S.boundaryOriginalMap (D.stageSel st x).val) = x) ∧
    (∀ x ∈ Φ.stageCloud st, Module.finrank ℝ (D.stagePlane st x) = gafStageDim st) ∧
    ∀ x ∈ Φ.stageCloud st,
      hausdorffEDist (Φ.stageCloudEnlarged st ∩ ball x (D.stageRadius st (sgs st) x / Γs st))
        ((AffineSubspace.mk' x (D.stagePlane st x) :
            Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))) ∩
          ball x (D.stageRadius st (sgs st) x / Γs st)) ≤
        ENNReal.ofReal (Γs st * D.stageRadius st (sgs st) x) := by
  fin_cases st
  · have hc : BoundaryEnhancedPlaneSpec D.circle (Γs 0) (sgs 0) (egs 0) := h
    have hsel := D.circle.planes.rsel_spec (Classical.arbitrary _)
      (fun q : W.pieceInterior ⊤ => Φ.stageProj 0 (S.boundaryOriginalMap q.val))
      fun x => D.circle.rpre_spec x
    exact ⟨hc.cloud_subset, hc.scale_kept, hsel, fun x hx => (hc.dimension x hx).1,
      hc.cloudy _ hsel⟩
  · have hc : BoundaryEnhancedPlaneSpec D.edge (Γs 1) (sgs 1) (egs 1) := h
    have hsel := D.edge.planes.rsel_spec (Classical.arbitrary _)
      (fun q : W.pieceInterior ⊤ => Φ.stageProj 1 (S.boundaryOriginalMap q.val))
      fun x => D.edge.rpre_spec x
    exact ⟨hc.cloud_subset, hc.scale_kept, hsel, fun x hx => (hc.dimension x hx).1,
      hc.cloudy _ hsel⟩
  · have hc : BoundaryEnhancedPlaneSpec D.slim (Γs 2) (sgs 2) (egs 2) := h
    have hsel := D.slim.planes.rsel_spec (Classical.arbitrary _)
      (fun q : W.pieceInterior ⊤ => Φ.stageProj 2 (S.boundaryOriginalMap q.val))
      fun x => D.slim.rpre_spec x
    exact ⟨hc.cloud_subset, hc.scale_kept, hsel, fun x hx => (hc.dimension x hx).1,
      hc.cloudy _ hsel⟩

/-- **CFS14's hypotheses on the boundary stage clouds** (all but (CS); the analogue of
`cfs14_stage_inputs_GAF2`): with BAUG-A's smoothness inequalities (`F_∂` smooth on the compact
ORIGINAL carrier `W`) and a stage's plane spec, for `0 < Σ` with CFS15's (MO) `128ε⁻¹Σ ≤ 1/5`:
`S_j ⊆ S̃_j`, `S_j` totally bounded, the radius `D.stageRadius st Σ` bounded above and away from zero
on `S_j`, and (MCb) on `S̃_j` at the buffer `128ε⁻¹` with `B = 5/3`. -/
theorem boundary_cfs14_stage_inputs_BAUGC (D : BoundaryAugmentedData S Φ) {Γs sgs egs : Fin 3 → ℝ}
    {st : Fin 3} (h : D.EnhancedPlaneSpec Γs sgs egs st) (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ)
    (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hV : 0 ≤ V)
    (hβ1 : 0 < β 1) (hb : 0 < b) (he : e ≤ 1 / 10) {εa : ℝ} (hsg : 0 < sgs st)
    (hmo : 128 * εa⁻¹ * sgs st ≤ 1 / 5) :
    Φ.stageCloud st ⊆ Φ.stageCloudEnlarged st ∧ TotallyBounded (Φ.stageCloud st) ∧
    (∃ rmin R : ℝ, 0 < rmin ∧ (∀ x ∈ Φ.stageCloud st, rmin ≤ D.stageRadius st (sgs st) x) ∧
      (∀ x ∈ Φ.stageCloud st, D.stageRadius st (sgs st) x ≤ R)) ∧
    ∀ x ∈ Φ.stageCloudEnlarged st, ∀ y ∈ Φ.stageCloudEnlarged st,
      dist y x ≤ 128 * εa⁻¹ * max (D.stageRadius st (sgs st) y) (D.stageRadius st (sgs st) x) →
      D.stageRadius st (sgs st) x / (5 / 3) ≤ D.stageRadius st (sgs st) y ∧
        D.stageRadius st (sgs st) y ≤ 5 / 3 * D.stageRadius st (sgs st) x := by
  have hsp := h.stage_inputs_BAUGC
  have hsub := hsp.1
  have hsc := hsp.2.1
  have hsel := hsp.2.2.1
  have hcont : Continuous fun q : W.Carrier => Φ.stageProj st (S.boundaryOriginalMap q) :=
    (Φ.stageProj st).continuous.comp
      (S.boundaryOriginalMap_smooth hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he).continuous
  obtain ⟨m, M, hm, hmM⟩ := exists_pos_bounds_KA3 S.rho S.scale_spec.1.continuous S.rho_pos
  refine ⟨Set.image_mono hsub, (isCompact_range hcont).totallyBounded.subset ?_,
    ⟨sgs st * m, sgs st * M, mul_pos hsg hm,
      fun x _ => mul_le_mul_of_nonneg_left (hmM _).1 hsg.le,
      fun x _ => mul_le_mul_of_nonneg_left (hmM _).2 hsg.le⟩, fun x hx y hy hd => ?_⟩
  · rintro _ ⟨p, -, rfl⟩
    exact ⟨p.val, rfl⟩
  · have hρx : S.scaleMarker_BIF x = S.rho (D.stageSel st x) :=
      (congrArg S.scaleMarker_BIF (hsel x hx)).symm.trans
        (scaleMarker_stageProj_BAUGC hsc (D.stageSel st x).val)
    have hρy : S.scaleMarker_BIF y = S.rho (D.stageSel st y) :=
      (congrArg S.scaleMarker_BIF (hsel y hy)).symm.trans
        (scaleMarker_stageProj_BAUGC hsc (D.stageSel st y).val)
    have hdiff : |S.rho (D.stageSel st x) - S.rho (D.stageSel st y)| ≤ dist y x := by
      have h1 : S.rho (D.stageSel st x) - S.rho (D.stageSel st y) = S.scaleMarker_BIF (x - y) := by
        rw [map_sub, hρx, hρy]
      rw [h1, dist_comm, dist_eq_norm]
      exact abs_blockMarkerCLM_le_BAUGC (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
        _ (x - y)
    exact radius_ratio_of_scale_BAUGC (S.rho_pos _) (S.rho_pos _) hsg hmo (hdiff.trans hd)

end Stage

/-- **The native CFS15 stage output in `H^∂`** (D61-6; the analogue of `gafStage_output_GAF8`): for
a stage `st`, `0 < Γ` with CFS15's modulus at `(k_st, Kj, 5/3, Ξ, Γ)` and CFS12's interior condition,
there is an early weight constant `c_w ≥ 0` such that for EVERY supply `S`, slot `Φ` and augmented
data `D` with BAUG-A's smoothness inequalities and the stage's plane spec at quality `Γ` and radius
factor `Σ` (`0 < Σ`, `128Ξ(Γ)⁻¹Σ ≤ 1/5`) there is a `Cfs15StageOutput` on `S_j ⊆ S̃_j` with radius
`D.stageRadius st Σ` and the stage planes `D.stagePlane st` in its plane slot — the type of BIFACE's
`BoundaryStageSlot_BIF.active`. -/
theorem boundaryStage_output_BAUGC {Kj : ℕ} {Ξ : ℝ → ℝ} {Γ : ℝ} (st : Fin 3) (hΓ : 0 < Γ)
    (hat : Cfs15ModulusAtV2 (gafStageDim st) Kj (5 / 3) Ξ Γ)
    (hint : Γ * ((80 * (5 / 3) + 31) * (Ξ Γ)⁻¹ + 2) < 1) :
    ∃ cw : ℝ, 0 ≤ cw ∧
      ∀ {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
        {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
        {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier]
        {g : SmoothRiemannianMetric W.model W.Carrier} {δn : ℝ} {n : ℕ}
        {B : NearlyCuspidalBoundary W g K δn}
        {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
        {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
          Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} (D : BoundaryAugmentedData S Φ),
        0 ≤ Λ → 0 < Δ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 100 * Δ * Λ ≤ 1 / 100 → 0 ≤ V → 0 < β 1 →
        0 < b → e ≤ 1 / 10 →
        ∀ Γs sgs egs : Fin 3 → ℝ, Γs st = Γ → 0 < sgs st → 128 * (Ξ Γ)⁻¹ * sgs st ≤ 1 / 5 →
        D.EnhancedPlaneSpec Γs sgs egs st →
        Nonempty (Cfs15StageOutput (gafStageDim st) Kj (Ξ Γ) cw (Φ.stageCloud st)
          (Φ.stageCloudEnlarged st) (D.stageRadius st (sgs st)) (D.stagePlane st)) := by
  obtain ⟨cw, hcw, hout⟩ := cfs15StageOutput_of_modulusAtV2_C15 hΓ hat hint
  refine ⟨cw, hcw, ?_⟩
  intro K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W _ g δn n B oM S
    Φ D hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he Γs sgs egs hΓs hsg hmo h
  have hin := boundary_cfs14_stage_inputs_BAUGC D h hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he hsg hmo
  have hsp := h.stage_inputs_BAUGC
  obtain ⟨rmin, R, hr, hlo, hhi⟩ := hin.2.2.1
  subst hΓs
  exact hout (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) (Φ.stageCloud st)
    (Φ.stageCloudEnlarged st) hin.1 hin.2.1 (D.stageRadius st (sgs st)) (D.stagePlane st)
    hsp.2.2.2.1 rmin R hr hlo hhi hin.2.2.2 hsp.2.2.2.2

/-- **Consumer: the ACTIVE boundary stage slot with locality, (SM) and (SMV) on ONE output** (draft
61 §3.2 "同一次 native CFS 输出"; the boundary form of `exists_cfs15StageOutput_with_mean`): under the
hypotheses of `boundaryStage_output_BAUGC` there is an output `O` whose active slot
`BoundaryStageSlot_BIF.active O` has smoothing map `O.ambient`, and on THIS `O`: GAF03's locality at
its three levels (section, zero set, ambient nearest map), (SM) on the zero set and (SMV) for
`a = O.ambient`, each with its hypothesis on the whole closed-support contributor list of `S_j`. -/
theorem boundaryStage_slot_with_mean_BAUGC {Kj : ℕ} {Ξ : ℝ → ℝ} {Γ : ℝ} (st : Fin 3)
    (hΓ : 0 < Γ) (hat : Cfs15ModulusAtV2 (gafStageDim st) Kj (5 / 3) Ξ Γ)
    (hint : Γ * ((80 * (5 / 3) + 31) * (Ξ Γ)⁻¹ + 2) < 1) :
    ∃ cw : ℝ, 0 ≤ cw ∧
      ∀ {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
        {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
        {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier]
        {g : SmoothRiemannianMetric W.model W.Carrier} {δn : ℝ} {n : ℕ}
        {B : NearlyCuspidalBoundary W g K δn}
        {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
        {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
          Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} (D : BoundaryAugmentedData S Φ),
        0 ≤ Λ → 0 < Δ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 100 * Δ * Λ ≤ 1 / 100 → 0 ≤ V → 0 < β 1 →
        0 < b → e ≤ 1 / 10 →
        ∀ Γs sgs egs : Fin 3 → ℝ, Γs st = Γ → 0 < sgs st → 128 * (Ξ Γ)⁻¹ * sgs st ≤ 1 / 5 →
        D.EnhancedPlaneSpec Γs sgs egs st →
        ∃ O : Cfs15StageOutput (gafStageDim st) Kj (Ξ Γ) cw (Φ.stageCloud st)
            (Φ.stageCloudEnlarged st) (D.stageRadius st (sgs st)) (D.stagePlane st),
          (BoundaryStageSlot_BIF.active O :
              BoundaryStageSlot_BIF D st Kj (Ξ Γ) (sgs st) cw).map = O.ambient ∧
          (∀ x ∈ Φ.stageCloud st,
            ∀ (Kk : Submodule ℝ (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)))
              (c : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)),
              (∀ i ∈ Φ.stageCloud st,
                (closedBall i (80 * (Ξ Γ)⁻¹ * D.stageRadius st (sgs st) i) ∩
                  ball x (8 * (Ξ Γ)⁻¹ * D.stageRadius st (sgs st) x)).Nonempty →
                Kk.starProjection i = c ∧ D.stagePlane st i ≤ Kkᗮ) →
              (∀ z ∈ ball x (8 * (Ξ Γ)⁻¹ * D.stageRadius st (sgs st) x),
                Kk.starProjection (cfs15Section_C15 (Ξ Γ) (D.stageRadius st (sgs st))
                  (D.stagePlane st) O.hI z) = Kk.starProjection z - c) ∧
              (∀ w ∈ O.Z ∩ ball x (8 * (Ξ Γ)⁻¹ * D.stageRadius st (sgs st) x),
                Kk.starProjection w = c) ∧
              (∀ z ∈ ball x (D.stageRadius st (sgs st) x), Kk.starProjection (O.ambient z) = c)) ∧
          (∀ (x : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
            (ℓ : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ),
              (∀ i ∈ Φ.stageCloud st,
                (closedBall i (80 * (Ξ Γ)⁻¹ * D.stageRadius st (sgs st) i) ∩
                  ball x (8 * (Ξ Γ)⁻¹ * D.stageRadius st (sgs st) x)).Nonempty →
                D.stagePlane st i ≤ LinearMap.ker
                  (ℓ : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ] ℝ)) →
              ∀ w ∈ O.Z ∩ ball x (8 * (Ξ Γ)⁻¹ * D.stageRadius st (sgs st) x),
                ℓ w = ∑ i ∈ O.hI.toFinset,
                  cfs15Weight_C15 (Ξ Γ) (D.stageRadius st (sgs st)) O.hI i w * ℓ i) ∧
          ∀ x ∈ Φ.stageCloud st,
            ∀ ℓ : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ,
              (∀ i ∈ Φ.stageCloud st,
                (closedBall i (80 * (Ξ Γ)⁻¹ * D.stageRadius st (sgs st) i) ∩
                  ball x (8 * (Ξ Γ)⁻¹ * D.stageRadius st (sgs st) x)).Nonempty →
                D.stagePlane st i ≤ LinearMap.ker
                  (ℓ : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ] ℝ)) →
              ∀ R₀ βm : ℝ,
              (∀ i ∈ Φ.stageCloud st,
                (closedBall i (80 * (Ξ Γ)⁻¹ * D.stageRadius st (sgs st) i) ∩
                  ball x (8 * (Ξ Γ)⁻¹ * D.stageRadius st (sgs st) x)).Nonempty →
                |ℓ i - R₀| ≤ βm) →
              ∀ z ∈ ball x (D.stageRadius st (sgs st) x),
                |ℓ (O.ambient z) - R₀| ≤ βm ∧
                  ‖ℓ.comp (fderiv ℝ O.ambient z)‖ ≤ 2 * cw * βm / D.stageRadius st (sgs st) x := by
  have h0 := boundaryStage_output_BAUGC (Kj := Kj) (Ξ := Ξ) (Γ := Γ) st hΓ hat hint
  refine h0.elim fun cw h1 => ⟨cw, h1.1, ?_⟩
  intro K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W _ g δn n B oM S
    Φ D hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he Γs sgs egs hΓs hsg hmo h
  refine (h1.2 D hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he Γs sgs egs hΓs hsg hmo h).elim fun O => ?_
  refine ⟨O, rfl, ?_, ?_, ?_⟩
  · intro x hx Kk c hc
    exact O.locality_of_cloud_C15 hx Kk c hc
  · intro x ℓ hpl
    exact O.mean_of_cloud_C15 (x := x) ℓ hpl
  · intro x hx ℓ hpl R₀ βm hβ
    exact O.smv_of_cloud_C15 hx ℓ hpl R₀ βm hβ

end DifferentialGeometry.Geometry.Collapse
