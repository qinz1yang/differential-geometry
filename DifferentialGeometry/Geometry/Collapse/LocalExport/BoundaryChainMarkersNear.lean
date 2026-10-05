import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryChainMarkers
import DifferentialGeometry.Geometry.Metric.Cfs15StageOutputLocalityBLOC

/-!
# BCG03: CFS29/CFS30's (PP)-locality input on the boundary chain and ZM / AM0 (BAUG-Dd)

Part (b) of target A2-mk (`TargetsBoundary-A-v3.lean.txt`; review 69 D69-5) and targets A3d / A3e:
the near-marker input `hnear` of `stage_markers_{one,two,three}_GAF7` on the ACTUAL v2 slot, from the
V3 plane spec (`radius_mcb`, `preimage_comparable`, `small_pp`) and BCG45-LOC's linear locality
kernel `Cfs15StageOutput.linear_kernel_of_cloud_BLOC` (never re-proved), then the kernels
instantiated on `W` with `F = F_∂`.

* field read-offs `BoundaryAugmentedDataPV3.radius_mcb_BAUGD`, `small_pp_BAUGD`;
* `contributor_rho_ge_BAUGD`: a contributor `i = π_j F_∂(q_i)` of the whole window at
  `x = π_j F_∂(q)` has `3/5 ρ(q) ≤ ρ(q_i)` (a SPECIAL selection through `q` and `q_i` in (MCb));
* **`stage_marker_near_BAUGD`** (`hnear`, every slot, every stage);
* raw-map kernels `markers_stage_one_BAUGD`, `markers_stage_two_BAUGD`,
  `markers_stage_three_BAUGD` (the stage maps written through their slots, before a chain exists —
  the assembly of A2-mk uses them for BAUG-PSI's (ZM) inputs).
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

namespace BoundaryAugmentedDataPV3

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {Γ Sg eg : Fin 3 → ℝ}

/-- (MCb) on the enlarged cloud, every stage (the V3 field `radius_mcb`). -/
theorem radius_mcb_BAUGD (DP : BoundaryAugmentedDataPV3 S Φ Γ Sg eg) (st : Fin 3) :
    ∀ sel : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → W.pieceInterior ⊤,
    (∀ x ∈ Φ.stageCloudEnlarged st, Φ.stageProj st (S.boundaryOriginalMap (sel x).val) = x) →
    ∀ L' : ℝ, 0 ≤ L' → L' * Sg st ≤ 1 / 5 →
    ∀ x ∈ Φ.stageCloudEnlarged st, ∀ y ∈ Φ.stageCloudEnlarged st,
      dist y x ≤ L' * max (Sg st * S.rho (sel y)) (Sg st * S.rho (sel x)) →
      Sg st * S.rho (sel x) / (5 / 3) ≤ Sg st * S.rho (sel y) ∧
        Sg st * S.rho (sel y) ≤ 5 / 3 * (Sg st * S.rho (sel x)) := by
  fin_cases st
  · exact DP.circle_spec.radius_mcb
  · exact DP.edge_spec.radius_mcb
  · exact DP.slim_spec.radius_mcb

/-- (PP) at every stage (the V3 field `small_pp`), on the stage planes of the data. -/
theorem small_pp_BAUGD (DP : BoundaryAugmentedDataPV3 S Φ Γ Sg eg) (st : Fin 3) :
    ∀ x ∈ Φ.stageCloud st, ∀ q : W.pieceInterior ⊤,
      Φ.stageProj st (S.boundaryOriginalMap q.val) = x →
      ∀ m : S.MarkerIdx_BAUGC, S.rho (S.markerCentre_BAUGC m) < S.rho q / 5 →
        DP.stagePlane st x ≤ LinearMap.ker ((S.markerCLM_BAUGC m :
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ] ℝ)) := by
  fin_cases st
  · exact DP.circle_spec.small_pp
  · exact DP.edge_spec.small_pp
  · exact DP.slim_spec.small_pp

end BoundaryAugmentedDataPV3

section Near

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}

/-- **Contributor scales** (the special-selection argument): if `x = π_j F_∂(q)` and
`i = π_j F_∂(q_i)` are enlarged-cloud points with `dist i x < 80ε⁻¹r_i + 8ε⁻¹r_x` (the whole window of
CFS15 at radius `r = Σρ ∘ q̂`) and `Σ ≤ ε/10⁴`, then `3/5 ρ(q) ≤ ρ(q_i)`. (MCb) is applied to the
selection through `q` at `x` and `q_i` at `i`, at the buffer `440/3 ε⁻¹`. -/
theorem contributor_rho_ge_BAUGD (DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg)
    {st : Fin 3} {ε : ℝ} (hε : 0 < ε) (hsg : 0 < Sg st) (hsgε : Sg st ≤ ε / 10000)
    {q qi : W.pieceInterior ⊤}
    (hxE : (actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val) ∈
      (actualSlotsV2_BAUGD S).stageCloudEnlarged st)
    (hiE : (actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap qi.val) ∈
      (actualSlotsV2_BAUGD S).stageCloudEnlarged st)
    (hd : dist ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap qi.val))
        ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val)) <
      80 * ε⁻¹ * DP.stageRadius st (Sg st)
          ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap qi.val)) +
        8 * ε⁻¹ * DP.stageRadius st (Sg st)
          ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val))) :
    3 / 5 * S.rho q ≤ S.rho qi := by
  set x := (actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val) with hxdef
  set i := (actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap qi.val) with hidef
  have hρq := S.rho_pos q.val
  have hρqi := S.rho_pos qi.val
  by_cases hix : i = x
  · have h := DP.preimage_comparable_BAUGD st x hxE q qi rfl (hix ▸ rfl)
    linarith
  · have hsel := stageSel_spec_BAUGD DP.toBoundaryAugmentedData st
    let sel' : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → W.pieceInterior ⊤ :=
      fun y => if y = x then q else if y = i then qi else DP.stageSel st y
    have hsx : sel' x = q := ite_eq_left rfl
    have hsi : sel' i = qi := by
      change (if i = x then q else if i = i then qi else DP.stageSel st i) = qi
      rw [ite_eq_right hix, ite_eq_left rfl]
    have hsel' : ∀ y ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged st,
        (actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap (sel' y).val) = y := by
      intro y hy
      by_cases h1 : y = x
      · rw [h1, hsx]
      · by_cases h2 : y = i
        · rw [h2, hsi]
        · change (actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap
            (if y = x then q else if y = i then qi else DP.stageSel st y).val) = y
          rw [ite_eq_right h1, ite_eq_right h2]
          exact hsel y hy
    -- radii against the special selection
    have hri : DP.stageRadius st (Sg st) i ≤ 5 / 3 * (Sg st * S.rho qi) := by
      have h := DP.preimage_comparable_BAUGD st i hiE (DP.stageSel st i) qi (hsel i hiE) rfl
      change Sg st * S.rho (DP.stageSel st i) ≤ 5 / 3 * (Sg st * S.rho qi)
      nlinarith
    have hrx : DP.stageRadius st (Sg st) x ≤ 5 / 3 * (Sg st * S.rho q) := by
      have h := DP.preimage_comparable_BAUGD st x hxE (DP.stageSel st x) q (hsel x hxE) rfl
      change Sg st * S.rho (DP.stageSel st x) ≤ 5 / 3 * (Sg st * S.rho q)
      nlinarith
    have hεi : 0 < ε⁻¹ := inv_pos.mpr hε
    have hM1 : Sg st * S.rho qi ≤ max (Sg st * S.rho qi) (Sg st * S.rho q) := le_max_left _ _
    have hM2 : Sg st * S.rho q ≤ max (Sg st * S.rho qi) (Sg st * S.rho q) := le_max_right _ _
    have hdist : dist i x ≤ 440 / 3 * ε⁻¹ * max (Sg st * S.rho (sel' i)) (Sg st * S.rho (sel' x)) := by
      rw [hsx, hsi]
      have h1 : 80 * ε⁻¹ * DP.stageRadius st (Sg st) i ≤
          80 * ε⁻¹ * (5 / 3 * max (Sg st * S.rho qi) (Sg st * S.rho q)) :=
        mul_le_mul_of_nonneg_left (hri.trans (by linarith)) (by positivity)
      have h2 : 8 * ε⁻¹ * DP.stageRadius st (Sg st) x ≤
          8 * ε⁻¹ * (5 / 3 * max (Sg st * S.rho qi) (Sg st * S.rho q)) :=
        mul_le_mul_of_nonneg_left (hrx.trans (by linarith)) (by positivity)
      have h3 : 80 * ε⁻¹ * (5 / 3 * max (Sg st * S.rho qi) (Sg st * S.rho q)) +
          8 * ε⁻¹ * (5 / 3 * max (Sg st * S.rho qi) (Sg st * S.rho q)) =
          440 / 3 * ε⁻¹ * max (Sg st * S.rho qi) (Sg st * S.rho q) := by ring
      linarith
    have hL : 440 / 3 * ε⁻¹ * Sg st ≤ 1 / 5 := by
      have h1 : ε⁻¹ * Sg st ≤ ε⁻¹ * (ε / 10000) := mul_le_mul_of_nonneg_left hsgε hεi.le
      have h2 : ε⁻¹ * (ε / 10000) = 1 / 10000 := by field_simp
      nlinarith
    have h := (DP.radius_mcb_BAUGD st sel' hsel' (440 / 3 * ε⁻¹) (by positivity) hL x hxE i hiE
      hdist).1
    rw [hsx, hsi] at h
    have h' : Sg st * (3 / 5 * S.rho q) ≤ Sg st * S.rho qi := by
      have : Sg st * S.rho q / (5 / 3) = Sg st * (3 / 5 * S.rho q) := by ring
      linarith
    exact le_of_mul_le_mul_left h' hsg

/-- **`hnear` of CFS29/CFS30 on the v2 slot** (every stage, every slot): at a stage-cloud point `x`,
for `z ∈ B(x, r_x)`, every preimage `q` of `x` and every marker chart with `ρ(c_m) < ρ(q)/16`, the
smoothing step `π_{Q_j} a_j(z)` has a vanishing `m`-marker. Active slot: BCG45-LOC's linear kernel
with `J = v_m` — every window contributor `i = π_j F_∂(q_i)` has `3/5 ρ(q) ≤ ρ(q_i)`
(`contributor_rho_ge_BAUGD`), hence `v_m(i) = ρ(c_m)ζ_m(q_i) = 0` (comparability on the marker
support) and `L_i ≤ ker v_m` (V3 `small_pp`, `ρ(c_m) < ρ(q_i)/5`). Inactive slot: the cloud is
empty. -/
theorem stage_marker_near_BAUGD (DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg)
    (hΛ : 0 ≤ Λ) (hΔ1 : 1 ≤ Δ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (hV : 0 ≤ V) (hβ1 : 0 < β 1)
    (hb : 0 < b) {st : Fin 3} {Kj : ℕ} {Ξ cw : ℝ}
    (σ : BoundaryStageSlot_BIF DP.toBoundaryAugmentedData st Kj Ξ (Sg st) cw)
    (hsg : 0 < Sg st) (hsgΞ : Sg st ≤ Ξ / 10000) :
    ∀ x ∈ (actualSlotsV2_BAUGD S).stageCloud st,
      ∀ z ∈ ball x (Sg st * S.rho (DP.stageSel st x).val), ∀ q : W.Carrier,
        ((actualSlotsV2_BAUGD S).stageQ st).starProjection (S.boundaryOriginalMap q) = x →
        ∀ m : S.MarkerIdx_BAUGC, S.rho (S.markerCentre_BAUGC m) < S.rho q / 16 →
          S.markerCLM_BAUGC m
            (((actualSlotsV2_BAUGD S).stageQ st).starProjection (σ.map z)) = 0 := by
  intro x hx z hz q hq m hm
  have hΔ : 0 < Δ := by linarith
  have hqx : ((actualSlotsV2_BAUGD S).stageQ st).starProjection (S.boundaryOriginalMap q) ∈
      (actualSlotsV2_BAUGD S).stageCloud st := by
    rw [hq]; exact hx
  have hint := interior_of_stageCloud_BAUGD hΔ st q hqx
  rcases hint with ⟨q', hq'⟩
  have hm' : S.rho (S.markerCentre_BAUGC m) < S.rho q'.val / 16 := by rw [hq']; exact hm
  have hq2 : (actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q'.val) = x := by
    have h1 : (actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q'.val) =
        (actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q) :=
      congrArg (fun p => (actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap p)) hq'
    exact h1.trans ((DFunLike.congr_fun (stageQ_starProjection_BAUGD
      (Φ := actualSlotsV2_BAUGD S) st) _).symm.trans hq)
  clear hm hq hqx hq'
  cases σ with
  | inactive hcore _ =>
    obtain ⟨q₀, hq₀, -⟩ := hx
    rw [hcore] at hq₀
    exact absurd hq₀ (Set.notMem_empty _)
  | active O =>
    have hε := O.eps_pos
    have hρq := S.rho_pos q'.val
    have hxE : (actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q'.val) ∈
        (actualSlotsV2_BAUGD S).stageCloudEnlarged st := by
      obtain ⟨q₀, hq₀, hx₀⟩ := hx
      rw [hq2]
      exact ⟨q₀, DP.cloud_subset_BAUGD st hq₀, hx₀⟩
    have hcontrib : ∀ i ∈ (actualSlotsV2_BAUGD S).stageCloud st,
        (closedBall i (80 * Ξ⁻¹ * DP.stageRadius st (Sg st) i) ∩
          ball x (8 * Ξ⁻¹ * DP.stageRadius st (Sg st) x)).Nonempty →
        S.markerCLM_BAUGC m i = 0 ∧
          DP.stagePlane st i ≤ LinearMap.ker ((S.markerCLM_BAUGC m :
            BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ] ℝ)) := by
      intro i hi hwin
      obtain ⟨qi, hqi, rfl⟩ := hi
      have hρqi := S.rho_pos qi.val
      obtain ⟨w, hw1, hw2⟩ := hwin
      have hd : dist ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap qi.val))
          ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q'.val)) <
          80 * Ξ⁻¹ * DP.stageRadius st (Sg st)
              ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap qi.val)) +
            8 * Ξ⁻¹ * DP.stageRadius st (Sg st)
              ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q'.val)) := by
        rw [hq2]
        have h1 := mem_closedBall.mp hw1
        have h2 := mem_ball.mp hw2
        calc _ ≤ dist w _ + dist w x := dist_triangle_left _ _ _
          _ < _ := by linarith
      have hcmp := contributor_rho_ge_BAUGD DP hε hsg hsgΞ hxE
        ⟨qi, DP.cloud_subset_BAUGD st hqi, rfl⟩ hd
      have hR := S.rho_pos (S.markerCentre_BAUGC m)
      refine ⟨?_, DP.small_pp_BAUGD st _ ⟨qi, hqi, rfl⟩ qi rfl m (by linarith [hm'])⟩
      rw [markerCLM_stageProj_BAUGD]
      split_ifs with htag
      · rw [S.markerCLM_boundaryOriginalMap_BAUGD]
        have hζ0 := S.markerCutoffW_nonneg_BAUGD hΔ m qi.val
        rcases hζ0.lt_or_eq with hpos | hzero
        · have hc := S.marker_scale_comparable_BAUGD hΛ hΔ1 hΛΔ hV hβ1 hb m qi.val hpos
          linarith [hc.2]
        · rw [← hzero, mul_zero]
      · rfl
    have hker := (O.linear_kernel_of_cloud_BLOC hx (S.markerCLM_BAUGC m) hcontrib).2.2.1 z hz
    change S.markerCLM_BAUGC m (((actualSlotsV2_BAUGD S).stageQ st).starProjection (O.ambient z)) = 0
    rw [stageQ_starProjection_BAUGD, markerCLM_stageProj_BAUGD]
    split_ifs
    · exact hker
    · rfl

/-- (hsel) on the v2 slot: the radius selection `q̂_j` selects preimages on the stage cloud. -/
theorem stage_marker_sel_BAUGD (DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg)
    (st : Fin 3) :
    ∀ x ∈ (actualSlotsV2_BAUGD S).stageCloud st,
      ((actualSlotsV2_BAUGD S).stageQ st).starProjection
        (S.boundaryOriginalMap (DP.stageSel st x).val) = x := by
  intro x hx
  obtain ⟨q₀, hq₀, hx₀⟩ := hx
  have hxE : x ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged st :=
    ⟨q₀, DP.cloud_subset_BAUGD st hq₀, hx₀⟩
  rw [stageQ_starProjection_BAUGD]
  exact stageSel_spec_BAUGD DP.toBoundaryAugmentedData st x hxE

/-- (hloc) from a closed-support localization of the cutoff `ψ_j` at a stage input `y`: a nonzero
cutoff at `y(q)` puts `π_j F_∂(q)` into the stage cloud. -/
theorem stage_marker_loc_BAUGD (st : Fin 3)
    (y : W.Carrier → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
    (hloc : ∀ p : W.Carrier, y p ∈ tsupport ((actualSlotsV2_BAUGD S).cutoff st) →
      ∃ q : W.pieceInterior ⊤, q.val = p ∧ q ∈ (actualSlotsV2_BAUGD S).stageCore st) :
    ∀ q : W.Carrier, (actualSlotsV2_BAUGD S).cutoff st (y q) ≠ 0 →
      ((actualSlotsV2_BAUGD S).stageQ st).starProjection (S.boundaryOriginalMap q) ∈
        (actualSlotsV2_BAUGD S).stageCloud st := by
  intro q hq
  obtain ⟨q', hq', hcore⟩ := hloc q (subset_tsupport _ (Function.mem_support.mpr hq))
  have h1 : (actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q'.val) =
      (actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q) :=
    congrArg (fun p => (actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap p)) hq'
  refine ⟨q', hcore, h1.trans ?_⟩
  exact (DFunLike.congr_fun (stageQ_starProjection_BAUGD (Φ := actualSlotsV2_BAUGD S) st) _).symm

/-- **CFS29/CFS30 at the first stage output** `g₁ = Ψ₀ ∘ F_∂` (raw: the stage map written through
its slot `σ₀`, before a chain exists): markers with `ρ(c_m) < ρ(q)/16` vanish at `g₁ q`, and (AM0)
holds on `[F_∂ p, g₁ p]` off the marker support. -/
theorem markers_stage_one_BAUGD (DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg)
    (hΛ : 0 ≤ Λ) (hΔ1 : 1 ≤ Δ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (hV : 0 ≤ V) (hβ1 : 0 < β 1)
    (hb : 0 < b) {Kj : ℕ} {Ξ₀ cw₀ : ℝ}
    (σ₀ : BoundaryStageSlot_BIF DP.toBoundaryAugmentedData 0 Kj Ξ₀ (Sg 0) cw₀)
    (hsg₀ : 0 < Sg 0) (hsgΞ₀ : Sg 0 ≤ Ξ₀ / 10000)
    (hloc₀ : ∀ p : W.Carrier,
      S.boundaryOriginalMap p ∈ tsupport ((actualSlotsV2_BAUGD S).cutoff 0) →
      ∃ q : W.pieceInterior ⊤, q.val = p ∧ q ∈ (actualSlotsV2_BAUGD S).stageCore 0)
    {E : ℝ} (hE : 0 ≤ E) (hE512 : E ≤ 1 / 512)
    (hcum : ∀ p : W.Carrier, ‖(actualSlotsV2_BAUGD S).adjust 0 σ₀.map (S.boundaryOriginalMap p) -
      S.boundaryOriginalMap p‖ ≤ E * S.rho p) :
    (∀ (q : W.Carrier) (m : S.MarkerIdx_BAUGC), S.rho (S.markerCentre_BAUGC m) < S.rho q / 16 →
      S.markerCLM_BAUGC m ((actualSlotsV2_BAUGD S).adjust 0 σ₀.map (S.boundaryOriginalMap q)) =
        0) ∧
    ∀ (m : S.MarkerIdx_BAUGC) (p : W.Carrier), S.markerCutoffW_BAUGD m p = 0 →
      ∀ z ∈ segment ℝ (S.boundaryOriginalMap p)
          ((actualSlotsV2_BAUGD S).adjust 0 σ₀.map (S.boundaryOriginalMap p)),
        |S.markerCLM_BAUGC m z| ≤ S.rho (S.markerCentre_BAUGC m) / 32 := by
  have hΔ : 0 < Δ := by linarith
  exact stage_markers_one_GAF7 (H := BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
    (fun m => S.markerCLM_BAUGC m) (fun _ => norm_blockMarkerCLM_le _)
    (fun m => S.rho (S.markerCentre_BAUGC m)) (fun m => S.rho_pos _) S.rho
    S.markerCutoffW_BAUGD (S.markerCutoffW_nonneg_BAUGD hΔ) S.boundaryOriginalMap
    S.markerCLM_boundaryOriginalMap_BAUGD (S.marker_scale_comparable_BAUGD hΛ hΔ1 hΛΔ hV hβ1 hb)
    ((actualSlotsV2_BAUGD S).stageQ 0)
    (fun y => ((actualSlotsV2_BAUGD S).stageQ 0).starProjection (σ₀.map y))
    (fun _ => Submodule.coe_mem _) ((actualSlotsV2_BAUGD S).cutoff 0)
    (stage_marker_retained_BAUGD 0) ((actualSlotsV2_BAUGD S).stageCloud 0)
    (fun x => (DP.stageSel 0 x).val)
    (stage_marker_support_BAUGD hΛ hΔ1 hΛΔ hV hβ1 hb 0) (stage_marker_full_BAUGD hΔ 0)
    (stage_marker_sel_BAUGD DP 0) hsg₀
    (stage_marker_loc_BAUGD 0 S.boundaryOriginalMap hloc₀)
    (stage_marker_near_BAUGD DP hΛ hΔ1 hΛΔ hV hβ1 hb σ₀ hsg₀ hsgΞ₀) hE hE512 hcum

/-- **CFS29/CFS30 at the first two stage outputs** `g₁ = Ψ₀ ∘ F_∂`, `g₂ = Ψ₁ ∘ g₁` (raw, through
the slots `σ₀`, `σ₁`): markers with `ρ(c_m) < ρ(q)/16` vanish at `g₁ q` and `g₂ q`, and (AM0) holds
on `[F_∂ p, g₂ p]` off the marker support. -/
theorem markers_stage_two_BAUGD (DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg)
    (hΛ : 0 ≤ Λ) (hΔ1 : 1 ≤ Δ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (hV : 0 ≤ V) (hβ1 : 0 < β 1)
    (hb : 0 < b) {Kj : ℕ} {Ξ₀ cw₀ Ξ₁ cw₁ : ℝ}
    (σ₀ : BoundaryStageSlot_BIF DP.toBoundaryAugmentedData 0 Kj Ξ₀ (Sg 0) cw₀)
    (σ₁ : BoundaryStageSlot_BIF DP.toBoundaryAugmentedData 1 Kj Ξ₁ (Sg 1) cw₁)
    (hsg₀ : 0 < Sg 0) (hsgΞ₀ : Sg 0 ≤ Ξ₀ / 10000) (hsg₁ : 0 < Sg 1) (hsgΞ₁ : Sg 1 ≤ Ξ₁ / 10000)
    (hloc₀ : ∀ p : W.Carrier,
      S.boundaryOriginalMap p ∈ tsupport ((actualSlotsV2_BAUGD S).cutoff 0) →
      ∃ q : W.pieceInterior ⊤, q.val = p ∧ q ∈ (actualSlotsV2_BAUGD S).stageCore 0)
    (hloc₁ : ∀ p : W.Carrier,
      (actualSlotsV2_BAUGD S).adjust 0 σ₀.map (S.boundaryOriginalMap p) ∈
        tsupport ((actualSlotsV2_BAUGD S).cutoff 1) →
      ∃ q : W.pieceInterior ⊤, q.val = p ∧ q ∈ (actualSlotsV2_BAUGD S).stageCore 1)
    {e₁ : ℝ} (he₁ : e₁ ≤ 3 * Sg 1 / 10)
    (herr₁ : ∀ p : W.Carrier, ‖(actualSlotsV2_BAUGD S).adjust 0 σ₀.map (S.boundaryOriginalMap p) -
      S.boundaryOriginalMap p‖ ≤ e₁ * S.rho p)
    {E : ℝ} (hE : 0 ≤ E) (hE512 : E ≤ 1 / 512)
    (hcum : ∀ p : W.Carrier, ‖(actualSlotsV2_BAUGD S).adjust 1 σ₁.map
      ((actualSlotsV2_BAUGD S).adjust 0 σ₀.map (S.boundaryOriginalMap p)) -
        S.boundaryOriginalMap p‖ ≤ E * S.rho p) :
    (∀ (q : W.Carrier) (m : S.MarkerIdx_BAUGC), S.rho (S.markerCentre_BAUGC m) < S.rho q / 16 →
      S.markerCLM_BAUGC m ((actualSlotsV2_BAUGD S).adjust 0 σ₀.map (S.boundaryOriginalMap q)) =
        0) ∧
    (∀ (q : W.Carrier) (m : S.MarkerIdx_BAUGC), S.rho (S.markerCentre_BAUGC m) < S.rho q / 16 →
      S.markerCLM_BAUGC m ((actualSlotsV2_BAUGD S).adjust 1 σ₁.map
        ((actualSlotsV2_BAUGD S).adjust 0 σ₀.map (S.boundaryOriginalMap q))) = 0) ∧
    ∀ (m : S.MarkerIdx_BAUGC) (p : W.Carrier), S.markerCutoffW_BAUGD m p = 0 →
      ∀ z ∈ segment ℝ (S.boundaryOriginalMap p) ((actualSlotsV2_BAUGD S).adjust 1 σ₁.map
          ((actualSlotsV2_BAUGD S).adjust 0 σ₀.map (S.boundaryOriginalMap p))),
        |S.markerCLM_BAUGC m z| ≤ S.rho (S.markerCentre_BAUGC m) / 32 := by
  have hΔ : 0 < Δ := by linarith
  have hl₁ : ∀ q : W.Carrier, (actualSlotsV2_BAUGD S).cutoff 1
      ((actualSlotsV2_BAUGD S).adjust 0 σ₀.map (S.boundaryOriginalMap q)) ≠ 0 →
      ((actualSlotsV2_BAUGD S).stageQ 1).starProjection (S.boundaryOriginalMap q) ∈
        (actualSlotsV2_BAUGD S).stageCloud 1 :=
    stage_marker_loc_BAUGD 1 (fun p => (actualSlotsV2_BAUGD S).adjust 0 σ₀.map
      (S.boundaryOriginalMap p)) hloc₁
  have key := stage_markers_two_GAF7 (H := BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
    (fun m => S.markerCLM_BAUGC m) (fun _ => norm_blockMarkerCLM_le _)
    (fun m => S.rho (S.markerCentre_BAUGC m)) (fun m => S.rho_pos _) S.rho
    S.markerCutoffW_BAUGD (S.markerCutoffW_nonneg_BAUGD hΔ) S.boundaryOriginalMap
    S.markerCLM_boundaryOriginalMap_BAUGD (S.marker_scale_comparable_BAUGD hΛ hΔ1 hΛΔ hV hβ1 hb)
    ((actualSlotsV2_BAUGD S).stageQ 0) ((actualSlotsV2_BAUGD S).stageQ 1)
    (fun y => ((actualSlotsV2_BAUGD S).stageQ 0).starProjection (σ₀.map y))
    (fun y => ((actualSlotsV2_BAUGD S).stageQ 1).starProjection (σ₁.map y))
    (fun _ => Submodule.coe_mem _) (fun _ => Submodule.coe_mem _)
    ((actualSlotsV2_BAUGD S).cutoff 0) ((actualSlotsV2_BAUGD S).cutoff 1)
    (stage_marker_retained_BAUGD 0) (stage_marker_retained_BAUGD 1)
    ((actualSlotsV2_BAUGD S).stageCloud 0) ((actualSlotsV2_BAUGD S).stageCloud 1)
    (fun x => (DP.stageSel 0 x).val) (fun x => (DP.stageSel 1 x).val)
    (stage_marker_support_BAUGD hΛ hΔ1 hΛΔ hV hβ1 hb 0)
    (stage_marker_support_BAUGD hΛ hΔ1 hΛΔ hV hβ1 hb 1)
    (stage_marker_full_BAUGD hΔ 0) (stage_marker_full_BAUGD hΔ 1)
    (stage_marker_sel_BAUGD DP 0) (stage_marker_sel_BAUGD DP 1) hsg₀ hsg₁ he₁
    (stage_marker_loc_BAUGD 0 S.boundaryOriginalMap hloc₀)
    (fun q hq => hl₁ q (by convert hq using 2; rfl)) (fun q => by convert herr₁ q using 1; rfl)
    (stage_marker_near_BAUGD DP hΛ hΔ1 hΛΔ hV hβ1 hb σ₀ hsg₀ hsgΞ₀)
    (stage_marker_near_BAUGD DP hΛ hΔ1 hΛΔ hV hβ1 hb σ₁ hsg₁ hsgΞ₁) hE hE512
    (fun q => by convert hcum q using 1; rfl)
  refine ⟨fun q a ha => ?_, fun q a ha => ?_, fun a p hp z hz => ?_⟩
  · convert key.1 q a ha using 2; rfl
  · convert key.2.1 q a ha using 2; rfl
  · convert key.2.2 a p hp z hz using 2



/-- The three stage adjustments of the v2 slot written as nested `adjustmentMap`s (definitional). -/
theorem adjust_three_eq_BAUGD {Kj : ℕ} {Ξ₀ cw₀ Ξ₁ cw₁ Ξ₂ cw₂ : ℝ}
    {D : BoundaryAugmentedData S (actualSlotsV2_BAUGD S)}
    (σ₀ : BoundaryStageSlot_BIF D 0 Kj Ξ₀ (Sg 0) cw₀)
    (σ₁ : BoundaryStageSlot_BIF D 1 Kj Ξ₁ (Sg 1) cw₁)
    (σ₂ : BoundaryStageSlot_BIF D 2 Kj Ξ₂ (Sg 2) cw₂)
    (y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    (actualSlotsV2_BAUGD S).adjust 2 σ₂.map ((actualSlotsV2_BAUGD S).adjust 1 σ₁.map
        ((actualSlotsV2_BAUGD S).adjust 0 σ₀.map y)) =
      adjustmentMap ((actualSlotsV2_BAUGD S).stageQ 2)
        (fun z => ((actualSlotsV2_BAUGD S).stageQ 2).starProjection (σ₂.map z))
        ((actualSlotsV2_BAUGD S).cutoff 2)
        (adjustmentMap ((actualSlotsV2_BAUGD S).stageQ 1)
          (fun z => ((actualSlotsV2_BAUGD S).stageQ 1).starProjection (σ₁.map z))
          ((actualSlotsV2_BAUGD S).cutoff 1)
          (adjustmentMap ((actualSlotsV2_BAUGD S).stageQ 0)
            (fun z => ((actualSlotsV2_BAUGD S).stageQ 0).starProjection (σ₀.map z))
            ((actualSlotsV2_BAUGD S).cutoff 0) y)) :=
  rfl

/-- **CFS29/CFS30 at the three stage outputs** `g₁`, `g₂`, `g₃` (raw, through the slots): markers
with `ρ(c_m) < ρ(q)/16` vanish at every stage output, and (AM0) holds on `[F_∂ p, g₃ p]` off the
marker support. -/
theorem markers_stage_three_BAUGD (DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg)
    (hΛ : 0 ≤ Λ) (hΔ1 : 1 ≤ Δ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (hV : 0 ≤ V) (hβ1 : 0 < β 1)
    (hb : 0 < b) {Kj : ℕ} {Ξ₀ cw₀ Ξ₁ cw₁ Ξ₂ cw₂ : ℝ}
    (σ₀ : BoundaryStageSlot_BIF DP.toBoundaryAugmentedData 0 Kj Ξ₀ (Sg 0) cw₀)
    (σ₁ : BoundaryStageSlot_BIF DP.toBoundaryAugmentedData 1 Kj Ξ₁ (Sg 1) cw₁)
    (σ₂ : BoundaryStageSlot_BIF DP.toBoundaryAugmentedData 2 Kj Ξ₂ (Sg 2) cw₂)
    (hsg₀ : 0 < Sg 0) (hsgΞ₀ : Sg 0 ≤ Ξ₀ / 10000) (hsg₁ : 0 < Sg 1) (hsgΞ₁ : Sg 1 ≤ Ξ₁ / 10000)
    (hsg₂ : 0 < Sg 2) (hsgΞ₂ : Sg 2 ≤ Ξ₂ / 10000)
    (hloc₀ : ∀ p : W.Carrier,
      S.boundaryOriginalMap p ∈ tsupport ((actualSlotsV2_BAUGD S).cutoff 0) →
      ∃ q : W.pieceInterior ⊤, q.val = p ∧ q ∈ (actualSlotsV2_BAUGD S).stageCore 0)
    (hloc₁ : ∀ p : W.Carrier,
      (actualSlotsV2_BAUGD S).adjust 0 σ₀.map (S.boundaryOriginalMap p) ∈
        tsupport ((actualSlotsV2_BAUGD S).cutoff 1) →
      ∃ q : W.pieceInterior ⊤, q.val = p ∧ q ∈ (actualSlotsV2_BAUGD S).stageCore 1)
    (hloc₂ : ∀ p : W.Carrier,
      (actualSlotsV2_BAUGD S).adjust 1 σ₁.map
          ((actualSlotsV2_BAUGD S).adjust 0 σ₀.map (S.boundaryOriginalMap p)) ∈
        tsupport ((actualSlotsV2_BAUGD S).cutoff 2) →
      ∃ q : W.pieceInterior ⊤, q.val = p ∧ q ∈ (actualSlotsV2_BAUGD S).stageCore 2)
    {e₁ e₂ : ℝ} (he₁ : e₁ ≤ 3 * Sg 1 / 10) (he₂ : e₂ ≤ 3 * Sg 2 / 10)
    (herr₁ : ∀ p : W.Carrier, ‖(actualSlotsV2_BAUGD S).adjust 0 σ₀.map (S.boundaryOriginalMap p) -
      S.boundaryOriginalMap p‖ ≤ e₁ * S.rho p)
    (herr₂ : ∀ p : W.Carrier, ‖(actualSlotsV2_BAUGD S).adjust 1 σ₁.map
      ((actualSlotsV2_BAUGD S).adjust 0 σ₀.map (S.boundaryOriginalMap p)) -
        S.boundaryOriginalMap p‖ ≤ e₂ * S.rho p)
    {E : ℝ} (hE : 0 ≤ E) (hE512 : E ≤ 1 / 512)
    (hcum : ∀ p : W.Carrier, ‖(actualSlotsV2_BAUGD S).adjust 2 σ₂.map
      ((actualSlotsV2_BAUGD S).adjust 1 σ₁.map
        ((actualSlotsV2_BAUGD S).adjust 0 σ₀.map (S.boundaryOriginalMap p))) -
        S.boundaryOriginalMap p‖ ≤ E * S.rho p) :
    (∀ (q : W.Carrier) (m : S.MarkerIdx_BAUGC), S.rho (S.markerCentre_BAUGC m) < S.rho q / 16 →
      S.markerCLM_BAUGC m ((actualSlotsV2_BAUGD S).adjust 0 σ₀.map (S.boundaryOriginalMap q)) =
        0) ∧
    (∀ (q : W.Carrier) (m : S.MarkerIdx_BAUGC), S.rho (S.markerCentre_BAUGC m) < S.rho q / 16 →
      S.markerCLM_BAUGC m ((actualSlotsV2_BAUGD S).adjust 1 σ₁.map
        ((actualSlotsV2_BAUGD S).adjust 0 σ₀.map (S.boundaryOriginalMap q))) = 0) ∧
    (∀ (q : W.Carrier) (m : S.MarkerIdx_BAUGC), S.rho (S.markerCentre_BAUGC m) < S.rho q / 16 →
      S.markerCLM_BAUGC m ((actualSlotsV2_BAUGD S).adjust 2 σ₂.map
        ((actualSlotsV2_BAUGD S).adjust 1 σ₁.map
          ((actualSlotsV2_BAUGD S).adjust 0 σ₀.map (S.boundaryOriginalMap q)))) = 0) ∧
    ∀ (m : S.MarkerIdx_BAUGC) (p : W.Carrier), S.markerCutoffW_BAUGD m p = 0 →
      ∀ z ∈ segment ℝ (S.boundaryOriginalMap p) ((actualSlotsV2_BAUGD S).adjust 2 σ₂.map
          ((actualSlotsV2_BAUGD S).adjust 1 σ₁.map
            ((actualSlotsV2_BAUGD S).adjust 0 σ₀.map (S.boundaryOriginalMap p)))),
        |S.markerCLM_BAUGC m z| ≤ S.rho (S.markerCentre_BAUGC m) / 32 := by
  have hΔ : 0 < Δ := by linarith
  have hl₁ := stage_marker_loc_BAUGD 1 (fun p => (actualSlotsV2_BAUGD S).adjust 0 σ₀.map
    (S.boundaryOriginalMap p)) hloc₁
  have hl₂ := stage_marker_loc_BAUGD 2 (fun p => (actualSlotsV2_BAUGD S).adjust 1 σ₁.map
    ((actualSlotsV2_BAUGD S).adjust 0 σ₀.map (S.boundaryOriginalMap p))) hloc₂
  have key := stage_markers_three_GAF7
    (H := BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
    (fun m => S.markerCLM_BAUGC m) (fun _ => norm_blockMarkerCLM_le _)
    (fun m => S.rho (S.markerCentre_BAUGC m)) (fun m => S.rho_pos _) S.rho
    S.markerCutoffW_BAUGD (S.markerCutoffW_nonneg_BAUGD hΔ) S.boundaryOriginalMap
    S.markerCLM_boundaryOriginalMap_BAUGD (S.marker_scale_comparable_BAUGD hΛ hΔ1 hΛΔ hV hβ1 hb)
    ((actualSlotsV2_BAUGD S).stageQ 0) ((actualSlotsV2_BAUGD S).stageQ 1)
    ((actualSlotsV2_BAUGD S).stageQ 2)
    (fun y => ((actualSlotsV2_BAUGD S).stageQ 0).starProjection (σ₀.map y))
    (fun y => ((actualSlotsV2_BAUGD S).stageQ 1).starProjection (σ₁.map y))
    (fun y => ((actualSlotsV2_BAUGD S).stageQ 2).starProjection (σ₂.map y))
    (fun _ => Submodule.coe_mem _) (fun _ => Submodule.coe_mem _) (fun _ => Submodule.coe_mem _)
    ((actualSlotsV2_BAUGD S).cutoff 0) ((actualSlotsV2_BAUGD S).cutoff 1)
    ((actualSlotsV2_BAUGD S).cutoff 2)
    (stage_marker_retained_BAUGD 0) (stage_marker_retained_BAUGD 1)
    (stage_marker_retained_BAUGD 2)
    ((actualSlotsV2_BAUGD S).stageCloud 0) ((actualSlotsV2_BAUGD S).stageCloud 1)
    ((actualSlotsV2_BAUGD S).stageCloud 2)
    (fun x => (DP.stageSel 0 x).val) (fun x => (DP.stageSel 1 x).val)
    (fun x => (DP.stageSel 2 x).val)
    (stage_marker_support_BAUGD hΛ hΔ1 hΛΔ hV hβ1 hb 0)
    (stage_marker_support_BAUGD hΛ hΔ1 hΛΔ hV hβ1 hb 1)
    (stage_marker_support_BAUGD hΛ hΔ1 hΛΔ hV hβ1 hb 2)
    (stage_marker_full_BAUGD hΔ 0) (stage_marker_full_BAUGD hΔ 1) (stage_marker_full_BAUGD hΔ 2)
    (stage_marker_sel_BAUGD DP 0) (stage_marker_sel_BAUGD DP 1) (stage_marker_sel_BAUGD DP 2)
    hsg₀ hsg₁ hsg₂ he₁ he₂
    (stage_marker_loc_BAUGD 0 S.boundaryOriginalMap hloc₀)
    (fun q hq => hl₁ q (by convert hq using 2; rfl)) (fun q hq => hl₂ q (by convert hq using 2; rfl))
    (fun q => by convert herr₁ q using 1; rfl) (fun q => by convert herr₂ q using 1; rfl)
    (stage_marker_near_BAUGD DP hΛ hΔ1 hΛΔ hV hβ1 hb σ₀ hsg₀ hsgΞ₀)
    (stage_marker_near_BAUGD DP hΛ hΔ1 hΛΔ hV hβ1 hb σ₁ hsg₁ hsgΞ₁)
    (stage_marker_near_BAUGD DP hΛ hΔ1 hΛΔ hV hβ1 hb σ₂ hsg₂ hsgΞ₂) hE hE512
    (fun q => by rw [← adjust_three_eq_BAUGD σ₀ σ₁ σ₂]; exact hcum q)
  refine ⟨fun q a ha => ?_, fun q a ha => ?_, fun q a ha => ?_, fun a p hp z hz => ?_⟩
  · convert key.1 q a ha using 2; rfl
  · convert key.2.1 q a ha using 2; rfl
  · convert key.2.2.1 q a ha using 2; rfl
  · convert key.2.2.2 a p hp z hz using 2

end Near

end DifferentialGeometry.Geometry.Collapse
