import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEnhancedPlaneSpecV3
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryStageNativeOutput
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceChain
import DifferentialGeometry.Geometry.Fibration.ActualCfs15StageOutputMean
import DifferentialGeometry.Geometry.Fibration.ActualCloudLargeCover

/-!
# The native CFS15 stage output in `H^∂` on `BoundaryEnhancedPlaneSpecV3` (lane BAUG-C)

New module (the accepted `BoundaryStageNativeOutput`, AGZ 438bccb9a, stays unchanged): the same
results for the spec V3 of lead decision (B), with (MCb) read from the field `radius_mcb` instead of
the scale block of every `Q_j^∂`. Generic lemmas (`blockMarkerCLM_blockRestrict_BAUGC`,
`abs_blockMarkerCLM_le_BAUGC`, `radius_ratio_of_scale_BAUGC`, `scaleMarker_stageProj_BAUGC`) are
imported from the accepted module.

* `BoundaryAugmentedData.EnhancedPlaneSpecV3.stage_inputs_BAUGC` (stage-uniform read-off);
* `boundary_cfs14_stage_inputs_V3_BAUGC` (CFS14's hypotheses on the boundary clouds);
* `boundaryStage_output_V3_BAUGC` (`Cfs15StageOutput` in the type of `BoundaryStageSlot_BIF.active`);
* consumer `boundaryStage_slot_with_mean_V3_BAUGC` (active slot + locality / (SM) / (SMV) on ONE output).
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

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

section Stage

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S}

/-- **The stage-uniform read-off of a stage's plane spec**: `S_j ⊆ S̃_j`, the scale tag kept, the
radius selection `q̂ = D.stageSel st` is a selection of preimages on `S̃_j`, (MCb) for the radius
`D.stageRadius st Σ_j`, the dimension, and FC27's (CS) at quality `Γ_j` and that radius. -/
theorem BoundaryAugmentedData.EnhancedPlaneSpecV3.stage_inputs_BAUGC (D : BoundaryAugmentedData S Φ)
    {Γs sgs egs : Fin 3 → ℝ} {st : Fin 3} (h : D.EnhancedPlaneSpecV3 Γs sgs egs st) :
    Φ.stageCore st ⊆ Φ.stageEnlargement st ∧
    (∀ L' : ℝ, 0 ≤ L' → L' * sgs st ≤ 1 / 5 →
      ∀ x ∈ Φ.stageCloudEnlarged st, ∀ y ∈ Φ.stageCloudEnlarged st,
        dist y x ≤ L' * max (D.stageRadius st (sgs st) y) (D.stageRadius st (sgs st) x) →
        D.stageRadius st (sgs st) x / (5 / 3) ≤ D.stageRadius st (sgs st) y ∧
          D.stageRadius st (sgs st) y ≤ 5 / 3 * D.stageRadius st (sgs st) x) ∧
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
  · have hc : BoundaryEnhancedPlaneSpecV3 D.circle (Γs 0) (sgs 0) (egs 0) := h
    have hsel := D.circle.planes.rsel_spec (Classical.arbitrary _)
      (fun q : W.pieceInterior ⊤ => Φ.stageProj 0 (S.boundaryOriginalMap q.val))
      fun x => D.circle.rpre_spec x
    exact ⟨hc.cloud_subset, hc.radius_mcb _ hsel, hsel, fun x hx => (hc.dimension x hx).1,
      hc.cloudy _ hsel⟩
  · have hc : BoundaryEnhancedPlaneSpecV3 D.edge (Γs 1) (sgs 1) (egs 1) := h
    have hsel := D.edge.planes.rsel_spec (Classical.arbitrary _)
      (fun q : W.pieceInterior ⊤ => Φ.stageProj 1 (S.boundaryOriginalMap q.val))
      fun x => D.edge.rpre_spec x
    exact ⟨hc.cloud_subset, hc.radius_mcb _ hsel, hsel, fun x hx => (hc.dimension x hx).1,
      hc.cloudy _ hsel⟩
  · have hc : BoundaryEnhancedPlaneSpecV3 D.slim (Γs 2) (sgs 2) (egs 2) := h
    have hsel := D.slim.planes.rsel_spec (Classical.arbitrary _)
      (fun q : W.pieceInterior ⊤ => Φ.stageProj 2 (S.boundaryOriginalMap q.val))
      fun x => D.slim.rpre_spec x
    exact ⟨hc.cloud_subset, hc.radius_mcb _ hsel, hsel, fun x hx => (hc.dimension x hx).1,
      hc.cloudy _ hsel⟩

/-- **CFS14's hypotheses on the boundary stage clouds** (all but (CS); the analogue of
`cfs14_stage_inputs_GAF2`): with BAUG-A's smoothness inequalities (`F_∂` smooth on the compact
ORIGINAL carrier `W`) and a stage's plane spec, for `0 < Σ` with CFS15's (MO) `128ε⁻¹Σ ≤ 1/5`:
`S_j ⊆ S̃_j`, `S_j` totally bounded, the radius `D.stageRadius st Σ` bounded above and away from zero
on `S_j`, and (MCb) on `S̃_j` at the buffer `128ε⁻¹` with `B = 5/3` (the spec's `radius_mcb`). -/
theorem boundary_cfs14_stage_inputs_V3_BAUGC (D : BoundaryAugmentedData S Φ) {Γs sgs egs : Fin 3 → ℝ}
    {st : Fin 3} (h : D.EnhancedPlaneSpecV3 Γs sgs egs st) (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ)
    (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hV : 0 ≤ V)
    (hβ1 : 0 < β 1) (hb : 0 < b) (he : e ≤ 1 / 10) {εa : ℝ} (hεa : 0 < εa) (hsg : 0 < sgs st)
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
  have hcont : Continuous fun q : W.Carrier => Φ.stageProj st (S.boundaryOriginalMap q) :=
    (Φ.stageProj st).continuous.comp
      (S.boundaryOriginalMap_smooth hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he).continuous
  obtain ⟨m, M, hm, hmM⟩ := exists_pos_bounds_KA3 S.rho S.scale_spec.1.continuous S.rho_pos
  refine ⟨Set.image_mono hsub, (isCompact_range hcont).totallyBounded.subset ?_,
    ⟨sgs st * m, sgs st * M, mul_pos hsg hm,
      fun x _ => mul_le_mul_of_nonneg_left (hmM _).1 hsg.le,
      fun x _ => mul_le_mul_of_nonneg_left (hmM _).2 hsg.le⟩,
    hsp.2.1 _ (by positivity) hmo⟩
  rintro _ ⟨p, -, rfl⟩
  exact ⟨p.val, rfl⟩

end Stage

/-- **The native CFS15 stage output in `H^∂`** (D61-6; the analogue of `gafStage_output_GAF8`): for
a stage `st`, `0 < Γ` with CFS15's modulus at `(k_st, Kj, 5/3, Ξ, Γ)` and CFS12's interior condition,
there is an early weight constant `c_w ≥ 0` such that for EVERY supply `S`, slot `Φ` and augmented
data `D` with BAUG-A's smoothness inequalities and the stage's plane spec at quality `Γ` and radius
factor `Σ` (`0 < Σ`, `128Ξ(Γ)⁻¹Σ ≤ 1/5`) there is a `Cfs15StageOutput` on `S_j ⊆ S̃_j` with radius
`D.stageRadius st Σ` and the stage planes `D.stagePlane st` in its plane slot — the type of BIFACE's
`BoundaryStageSlot_BIF.active`. -/
theorem boundaryStage_output_V3_BAUGC {Kj : ℕ} {Ξ : ℝ → ℝ} {Γ : ℝ} (st : Fin 3) (hΓ : 0 < Γ)
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
        D.EnhancedPlaneSpecV3 Γs sgs egs st →
        Nonempty (Cfs15StageOutput (gafStageDim st) Kj (Ξ Γ) cw (Φ.stageCloud st)
          (Φ.stageCloudEnlarged st) (D.stageRadius st (sgs st)) (D.stagePlane st)) := by
  obtain ⟨cw, hcw, hout⟩ := cfs15StageOutput_of_modulusAtV2_C15 hΓ hat hint
  refine ⟨cw, hcw, ?_⟩
  intro K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W _ g δn n B oM S
    Φ D hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he Γs sgs egs hΓs hsg hmo h
  have hεa : 0 < Ξ Γ := by
    obtain ⟨⟨m, hm⟩, -⟩ := hat
    rw [hm]
    positivity
  have hin := boundary_cfs14_stage_inputs_V3_BAUGC D h hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he hεa hsg hmo
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
theorem boundaryStage_slot_with_mean_V3_BAUGC {Kj : ℕ} {Ξ : ℝ → ℝ} {Γ : ℝ} (st : Fin 3)
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
        D.EnhancedPlaneSpecV3 Γs sgs egs st →
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
  have h0 := boundaryStage_output_V3_BAUGC (Kj := Kj) (Ξ := Ξ) (Γ := Γ) st hΓ hat hint
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
