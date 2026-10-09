import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryActualSlot
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryStageNativeOutput
import DifferentialGeometry.Geometry.Fibration.ActualStageStepPoint
import DifferentialGeometry.Geometry.Fibration.ActualStageTargets

/-!
# BCG03: smoothness of the boundary chain on the WHOLE original carrier `W` (lane BAUG-D, A3a)

Frozen target A3a (`stage_smooth_BAUGD`, TargetsBoundary.lean.txt §A; D72-3 (1)): on a chain
`C : BoundaryGaf02Chain D …` over augmented data `D` on the ACTUAL slot `actualSlots_BAUGD S`, with
BAUG-A's smoothness inequalities, every stage output `g₀ = F_∂, g₁, g₂, g₃ = C.E` is smooth on ALL
of `W` (manifold with boundary; no restriction to `W°`).

Proof (closed pattern `Gaf02Chain.stage_smooth`, on the chain's own data): `F_∂` is smooth on `W`
(BAUG-A, `boundaryOriginalMap_smooth`). For a stage input `z = g_{j-1}(p)`: off the closed support
of `ψ_j` the adjustment is the identity near `z`; on it, the chain's cutoff binding localizes `p` to a
threshold-`7` set of a stage centre, hence `x = π_j F_∂(p)` lies in the actual stage cloud `S_j`
(`actualSlots_BAUGD`, A0a), the radius there is `Σ_j ρ(p)` (scale block kept), and
`π_j z ∈ B(x, Σ_j ρ(p))` because `‖g_{j-1}(p) − F_∂(p)‖ < c_{j-1}ρ(p) ≤ (3/10)Σ_jρ(p)` (the chain's
numbers); there the native nearest map is smooth (`Cfs15StageOutput.ambient_contDiffAt`), `ψ_j` is
smooth (binding; `ψ₁` on the open set `{ℓ_ρ > 0}` containing `g₁(p)`), so `Ψ_j` is smooth near `z`.

* generic: `adjustmentMap_contDiffAt_BAUGD`, `norm_starProjection_adjust_sub_le_BAUGD`;
* slot level: `stageQ_starProjection_BAUGD`, `stageSel_spec_BAUGD`, `stageRadius_stageProj_BAUGD`,
  `BoundaryStageSlot_BIF.map_value_BAUGD`, `BoundaryStageSlot_BIF.map_contDiffAt_BAUGD`;
* chain level: `stageCloud_of_cutoff_{zero,one,two}_BAUGD` (tube localization),
  `g₁_error_lt_BAUGD`, `g₂_error_lt_BAUGD` (the prefix value errors used for tube membership),
  **`stage_smooth_BAUGD`** (A3a, for every `D` over the actual slot; the frozen form is the
  instance `D = DP.toBoundaryAugmentedData`).
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

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- **One adjustment is smooth near `z`** if `z` is off the closed support of the cutoff, or the
cutoff is smooth at `z` and the smoothing map is smooth at `π_Q z`. -/
theorem adjustmentMap_contDiffAt_BAUGD (Q : Submodule ℝ H) (a : H → H) (ψ : H → ℝ) {z : H}
    (h : z ∉ tsupport ψ ∨ (ContDiffAt ℝ ∞ ψ z ∧ ContDiffAt ℝ ∞ a (Q.starProjection z))) :
    ContDiffAt ℝ ∞ (adjustmentMap Q (fun y => Q.starProjection (a y)) ψ) z := by
  rcases h with h | ⟨hψ, ha⟩
  · exact contDiffAt_id.congr_of_eventuallyEq (adjustmentMap_eventuallyEq_id_GAF5 Q _ h)
  · have hP : ContDiffAt ℝ ∞ (fun y => Q.starProjection y) z :=
      Q.starProjection.contDiff.contDiffAt
    have h1 : ContDiffAt ℝ ∞ (fun y => Q.starProjection (a (Q.starProjection y))) z :=
      Q.starProjection.contDiff.contDiffAt.comp z (ha.comp z hP)
    exact contDiffAt_id.add (hψ.smul (h1.sub hP))

/-- **One projected smoothing step moves a point of `Q` by at most `E + ‖w − x‖`** when the
smoothing map is `E`-close at `w` to the affine plane `x + P`. -/
theorem norm_starProjection_adjust_sub_le_BAUGD (Q P : Submodule ℝ H) (a : H → H) {x w : H}
    (hw : w ∈ Q) {E : ℝ} (ha : ‖a w - (x + P.starProjection (w - x))‖ ≤ E) :
    ‖Q.starProjection (a w) - w‖ ≤ E + ‖w - x‖ := by
  have h1 : Q.starProjection (a w) - w = Q.starProjection (a w - w) := by
    rw [map_sub, Submodule.starProjection_eq_self_iff.mpr hw]
  have h2 : ‖x + P.starProjection (w - x) - w‖ ≤ ‖w - x‖ := by
    have hs := P.starProjection_add_starProjection_orthogonal (w - x)
    have h3 : x + P.starProjection (w - x) - w = -(Pᗮ.starProjection (w - x)) := by
      rw [eq_neg_iff_add_eq_zero]
      calc x + P.starProjection (w - x) - w + Pᗮ.starProjection (w - x)
          = x - w + (P.starProjection (w - x) + Pᗮ.starProjection (w - x)) := by abel
        _ = 0 := by rw [hs]; abel
    rw [h3, norm_neg]
    exact Pᗮ.norm_starProjection_apply_le _
  calc ‖Q.starProjection (a w) - w‖ = ‖Q.starProjection (a w - w)‖ := by rw [h1]
    _ ≤ ‖a w - w‖ := Q.norm_starProjection_apply_le _
    _ = ‖(a w - (x + P.starProjection (w - x))) + (x + P.starProjection (w - x) - w)‖ := by
        congr 1; abel
    _ ≤ E + ‖w - x‖ := (norm_add_le _ _).trans (add_le_add ha h2)

/-- The adjustment increment is the cutoff times the projected smoothing step. -/
theorem norm_adjustmentMap_sub_le_BAUGD (Q : Submodule ℝ H) (a : H → H) (ψ : H → ℝ) (z : H)
    (hψ : ψ z ∈ Icc (0 : ℝ) 1) :
    ‖adjustmentMap Q (fun y => Q.starProjection (a y)) ψ z - z‖ ≤
      ‖Q.starProjection (a (Q.starProjection z)) - Q.starProjection z‖ := by
  rw [adjustmentMap_apply, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hψ.1]
  exact mul_le_of_le_one_left (norm_nonneg _) hψ.2

/-- **One adjustment step** (combined): with `w = π_Q z`, if the smoothing map is `E`-close at `w`
to the affine plane `x + P` and the cutoff takes values in `[0, 1]`, the step moves `z` by at most
`E + ‖w − x‖`. -/
theorem norm_adjustmentMap_sub_le_of_affine_BAUGD (Q P : Submodule ℝ H) (a : H → H) (ψ : H → ℝ)
    {x z w : H} (hw : Q.starProjection z = w) (hψ : ψ z ∈ Icc (0 : ℝ) 1) {E : ℝ}
    (ha : ‖a w - (x + P.starProjection (w - x))‖ ≤ E) :
    ‖adjustmentMap Q (fun y => Q.starProjection (a y)) ψ z - z‖ ≤ E + ‖w - x‖ := by
  subst hw
  exact (norm_adjustmentMap_sub_le_BAUGD Q a ψ z hψ).trans
    (norm_starProjection_adjust_sub_le_BAUGD Q P a (Q.starProjection_apply_mem z) ha)

/-- Off the support of the cutoff the adjustment is the identity at `z`. -/
theorem adjustmentMap_eq_of_notMem_tsupport_BAUGD (Q : Submodule ℝ H) (a : H → H) (ψ : H → ℝ)
    {z : H} (hz : z ∉ tsupport ψ) : adjustmentMap Q (fun y => Q.starProjection (a y)) ψ z = z := by
  rw [adjustmentMap_apply, image_eq_zero_of_notMem_tsupport hz, zero_smul, add_zero]

end Generic

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

section SlotLevel

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S}

/-- The orthogonal projection onto `Q_j^∂` is the stage projection `π_j`. -/
theorem stageQ_starProjection_BAUGD (st : Fin 3) :
    (Φ.stageQ st).starProjection = Φ.stageProj st :=
  blockRestrict_eq_starProjection_GAF3 _

/-- The radius selection `q̂_j = D.stageSel st` is a selection of preimages on `S̃_j`. -/
theorem stageSel_spec_BAUGD (D : BoundaryAugmentedData S Φ) (st : Fin 3) :
    ∀ x ∈ Φ.stageCloudEnlarged st,
      Φ.stageProj st (S.boundaryOriginalMap (D.stageSel st x).val) = x := by
  fin_cases st
  · exact D.circle.planes.rsel_spec (Classical.arbitrary _)
      (fun q : W.pieceInterior ⊤ => Φ.stageProj 0 (S.boundaryOriginalMap q.val))
      fun x => D.circle.rpre_spec x
  · exact D.edge.planes.rsel_spec (Classical.arbitrary _)
      (fun q : W.pieceInterior ⊤ => Φ.stageProj 1 (S.boundaryOriginalMap q.val))
      fun x => D.edge.rpre_spec x
  · exact D.slim.planes.rsel_spec (Classical.arbitrary _)
      (fun q : W.pieceInterior ⊤ => Φ.stageProj 2 (S.boundaryOriginalMap q.val))
      fun x => D.slim.rpre_spec x

/-- **The stage radius at an original point**: with the scale block kept in `Q_j^∂`, at
`x = π_j F_∂(p) ∈ S̃_j` the CFS15 radius is `Σ ρ(p)`. -/
theorem stageRadius_stageProj_BAUGD (D : BoundaryAugmentedData S Φ) {st : Fin 3}
    (hsc : S.scaleTag_BAUGA ∈ Φ.stageTags st) (sg : ℝ) {p : W.Carrier}
    (hx : Φ.stageProj st (S.boundaryOriginalMap p) ∈ Φ.stageCloudEnlarged st) :
    D.stageRadius st sg (Φ.stageProj st (S.boundaryOriginalMap p)) = sg * S.rho p := by
  have h1 := stageSel_spec_BAUGD D st _ hx
  have h2 := scaleMarker_stageProj_BAUGC hsc (D.stageSel st
    (Φ.stageProj st (S.boundaryOriginalMap p))).val
  have h3 := scaleMarker_stageProj_BAUGC hsc p
  rw [h1] at h2
  change sg * S.rho (D.stageSel st (Φ.stageProj st (S.boundaryOriginalMap p))) = sg * S.rho p
  rw [← h2, h3]

namespace BoundaryStageSlot_BIF

variable {D : BoundaryAugmentedData S Φ} {st : Fin 3} {Kj : ℕ} {Ξ sg cw : ℝ}

/-- CFS14 (3)'s value bound for the slot's smoothing map on every `B(x, r_x)`, `x ∈ S_j` (vacuous
for an inactive slot: empty cloud). -/
theorem map_value_BAUGD (σ : BoundaryStageSlot_BIF D st Kj Ξ sg cw) {x : _}
    (hx : x ∈ Φ.stageCloud st) {z : _} (hz : z ∈ ball x (D.stageRadius st sg x)) :
    ‖σ.map z - (x + (D.stagePlane st x).starProjection (z - x))‖ ≤
      Ξ * D.stageRadius st sg x := by
  cases σ with
  | active O => exact (O.ambient_value_deriv hx hz).1
  | inactive hc he =>
    rw [(stageCloud_eq_empty_of_inactive hc he).1] at hx
    exact absurd hx (Set.notMem_empty x)

/-- The slot's smoothing map is smooth on every `B(x, r_x)`, `x ∈ S_j`. -/
theorem map_contDiffAt_BAUGD (σ : BoundaryStageSlot_BIF D st Kj Ξ sg cw) {x : _}
    (hx : x ∈ Φ.stageCloud st) {z : _} (hz : z ∈ ball x (D.stageRadius st sg x)) :
    ContDiffAt ℝ ∞ σ.map z := by
  cases σ with
  | active O => exact O.ambient_contDiffAt (mem_cfs15Omega_of_mem_C15 hx hz)
  | inactive _ _ => exact contDiffAt_id

end BoundaryStageSlot_BIF

/-- `π_j z ∈ Q_j^∂`. -/
theorem stageProj_mem_stageQ_BAUGD (st : Fin 3) (z : BoundaryAmbient_BIF S.IntTag_BAUGA
    (Fin S.packet.cusp.count)) : Φ.stageProj st z ∈ Φ.stageQ st :=
  LinearMap.mem_range_self _ z

/-- `‖π_j z − π_j z'‖ ≤ ‖z − z'‖`. -/
theorem norm_stageProj_sub_le_BAUGD (st : Fin 3) (z z' : BoundaryAmbient_BIF S.IntTag_BAUGA
    (Fin S.packet.cusp.count)) : ‖Φ.stageProj st z - Φ.stageProj st z'‖ ≤ ‖z - z'‖ := by
  rw [← map_sub, ← stageQ_starProjection_BAUGD]
  exact Submodule.norm_starProjection_apply_le _ _

/-- **One stage step, value**: if `x ∈ S_j`, `r_x = r` and `‖π_j z − x‖ < r`, the stage moves `z` by
at most `Ξ r + ‖π_j z − x‖`. -/
theorem adjust_sub_le_BAUGD {D : BoundaryAugmentedData S Φ} {st : Fin 3} {Kj : ℕ} {Ξ sg cw : ℝ}
    (σ : BoundaryStageSlot_BIF D st Kj Ξ sg cw) {x z : BoundaryAmbient_BIF S.IntTag_BAUGA
      (Fin S.packet.cusp.count)} (hx : x ∈ Φ.stageCloud st) {r : ℝ}
    (hr : D.stageRadius st sg x = r) (hz : ‖Φ.stageProj st z - x‖ < r)
    (hψ : Φ.cutoff st z ∈ Icc (0 : ℝ) 1) :
    ‖Φ.adjust st σ.map z - z‖ ≤ Ξ * r + ‖Φ.stageProj st z - x‖ := by
  have hw : (Φ.stageQ st).starProjection z = Φ.stageProj st z := by
    rw [stageQ_starProjection_BAUGD]
  have hball : Φ.stageProj st z ∈ ball x (D.stageRadius st sg x) := by
    rw [hr, mem_ball, dist_eq_norm]; exact hz
  have hval := σ.map_value_BAUGD hx hball
  have hstep := norm_adjustmentMap_sub_le_of_affine_BAUGD
    (H := BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) (Φ.stageQ st)
    (D.stagePlane st x) σ.map (Φ.cutoff st) hw hψ hval
  calc ‖Φ.adjust st σ.map z - z‖
      ≤ Ξ * D.stageRadius st sg x + ‖Φ.stageProj st z - x‖ := hstep
    _ = Ξ * r + ‖Φ.stageProj st z - x‖ := by rw [hr]

/-- **One stage step, smoothness**: under the same tube membership, with the cutoff smooth at `z`,
the stage is smooth at `z`. -/
theorem adjust_contDiffAt_BAUGD {D : BoundaryAugmentedData S Φ} {st : Fin 3} {Kj : ℕ}
    {Ξ sg cw : ℝ} (σ : BoundaryStageSlot_BIF D st Kj Ξ sg cw) {x z : BoundaryAmbient_BIF
      S.IntTag_BAUGA (Fin S.packet.cusp.count)} (hx : x ∈ Φ.stageCloud st) {r : ℝ}
    (hr : D.stageRadius st sg x = r) (hz : ‖Φ.stageProj st z - x‖ < r)
    (hψ : ContDiffAt ℝ ∞ (Φ.cutoff st) z) : ContDiffAt ℝ ∞ (Φ.adjust st σ.map) z := by
  have hball : Φ.stageProj st z ∈ ball x (D.stageRadius st sg x) := by
    rw [hr, mem_ball, dist_eq_norm]; exact hz
  refine adjustmentMap_contDiffAt_BAUGD _ _ _ (Or.inr ⟨hψ, ?_⟩)
  rw [stageQ_starProjection_BAUGD]
  exact σ.map_contDiffAt_BAUGD hx hball

/-- Off the closed support of `ψ_j` the stage is smooth at `z` (the identity nearby). -/
theorem adjust_contDiffAt_of_notMem_BAUGD (st : Fin 3)
    (a : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →
      BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
    {z : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hz : z ∉ tsupport (Φ.cutoff st)) : ContDiffAt ℝ ∞ (Φ.adjust st a) z :=
  adjustmentMap_contDiffAt_BAUGD _ _ _ (Or.inl hz)

/-- Off the closed support of `ψ_j` the stage fixes `z`. -/
theorem adjust_eq_of_notMem_BAUGD (st : Fin 3)
    (a : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →
      BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
    {z : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hz : z ∉ tsupport (Φ.cutoff st)) : Φ.adjust st a z = z :=
  adjustmentMap_eq_of_notMem_tsupport_BAUGD _ _ _ hz

end SlotLevel

namespace BoundaryGaf02Chain

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {D : BoundaryAugmentedData S (actualSlots_BAUGD S)} {Kj : ℕ}
  {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)

/-- `g₁ = Ψ₀ ∘ F_∂` pointwise, with `Ψ₀` the actual slot's adjustment. -/
theorem g₁_apply_BAUGD (p : W.Carrier) :
    C.g₁ p = (actualSlots_BAUGD S).adjust 0 (C.slot 0).map (S.boundaryOriginalMap p) :=
  rfl

/-- `g₂ = Ψ₁ ∘ g₁` pointwise. -/
theorem g₂_apply_BAUGD (p : W.Carrier) :
    C.g₂ p = (actualSlots_BAUGD S).adjust 1 (C.slot 1).map (C.g₁ p) :=
  rfl

/-- `E = Ψ₂ ∘ g₂` pointwise. -/
theorem E_apply_BAUGD (p : W.Carrier) :
    C.E p = (actualSlots_BAUGD S).adjust 2 (C.slot 2).map (C.g₂ p) :=
  rfl

include C in
/-- **Tube localization, stage `0`**: `F_∂ p ∈ tsupport ψ₀ ⟹ π₀ F_∂ p ∈ S₀`. -/
theorem stageCloud_of_cutoff_zero_BAUGD {p : W.Carrier}
    (hp : S.boundaryOriginalMap p ∈ tsupport ((actualSlots_BAUGD S).cutoff 0)) :
    (actualSlots_BAUGD S).stageProj 0 (S.boundaryOriginalMap p) ∈
      (actualSlots_BAUGD S).stageCloud 0 := by
  have hB := C.cutoff_bindings
  obtain ⟨q, hq, j, hj, hd, hη⟩ := hB.1.2.2.2.1 p hp
  subst hq
  exact ⟨q, mem_actualSlots_stageCore_circle_BAUGD S hj hd (hη.trans (by norm_num)), rfl⟩

/-- **Tube localization, stage `1`**: `g₁ p ∈ tsupport ψ₁ ⟹ π₁ F_∂ p ∈ S₁`. -/
theorem stageCloud_of_cutoff_one_BAUGD {p : W.Carrier}
    (hp : C.g₁ p ∈ tsupport ((actualSlots_BAUGD S).cutoff 1)) :
    (actualSlots_BAUGD S).stageProj 1 (S.boundaryOriginalMap p) ∈
      (actualSlots_BAUGD S).stageCloud 1 := by
  have hB := C.cutoff_bindings
  rw [g₁_apply_BAUGD] at hp
  obtain ⟨q, hq, j, hj, hd, hη, ht⟩ := hB.2.1.2.2.2.1 p hp
  subst hq
  exact ⟨q, mem_actualSlots_stageCore_edge_BAUGD S hj hd hη.le ht.le, rfl⟩

/-- **Tube localization, stage `2`**: `g₂ p ∈ tsupport ψ₂ ⟹ π₂ F_∂ p ∈ S₂`. -/
theorem stageCloud_of_cutoff_two_BAUGD {p : W.Carrier}
    (hp : C.g₂ p ∈ tsupport ((actualSlots_BAUGD S).cutoff 2)) :
    (actualSlots_BAUGD S).stageProj 2 (S.boundaryOriginalMap p) ∈
      (actualSlots_BAUGD S).stageCloud 2 := by
  have hB := C.cutoff_bindings
  rw [g₂_apply_BAUGD, g₁_apply_BAUGD] at hp
  obtain ⟨q, hq, j, hj, hd, hη⟩ := hB.2.2.2.2.2.1 p hp
  subst hq
  have hη' : |S.slimEta_BIF j q| ≤ 7 * (100000 * Δ) := by
    rw [show (100000 : ℝ) = 10 ^ 5 by norm_num]
    exact hη.le
  exact ⟨q, mem_actualSlots_stageCore_slim_BAUGD S hj hd hη', rfl⟩

/-- The radius of the stage-`st` cloud point of `p` is `Σ ρ(p)`. -/
theorem stageRadius_of_mem_BAUGD (D : BoundaryAugmentedData S (actualSlots_BAUGD S)) (hΔ : 0 < Δ)
    {st : Fin 3} (sg : ℝ) {p : W.Carrier}
    (hx : (actualSlots_BAUGD S).stageProj st (S.boundaryOriginalMap p) ∈
      (actualSlots_BAUGD S).stageCloud st) :
    D.stageRadius st sg ((actualSlots_BAUGD S).stageProj st (S.boundaryOriginalMap p)) =
      sg * S.rho p :=
  stageRadius_stageProj_BAUGD D (actualSlots_scale_kept_BAUGD S st) sg
    (actualSlots_stageCloud_subset_BAUGD S hΔ.le st hx)

/-- **The stage-one value error** `‖g₁ p − F_∂ p‖ < c₀ρ(p)` (on the chain's own data). -/
theorem g₁_error_lt_BAUGD (hΔ : 0 < Δ) (p : W.Carrier) :
    ‖C.g₁ p - S.boundaryOriginalMap p‖ < c 0 * S.rho p := by
  have hN := C.numbers
  have hΞ := (hN.1 0).1
  have hsg := (hN.1 0).2.1
  have hv : 5 / 3 * Ξ 0 * Sg 0 < c 0 := hN.2.1
  have hρ := S.rho_pos p
  have hpos : 0 < Ξ 0 * Sg 0 := mul_pos hΞ hsg
  have hB := C.cutoff_bindings
  rw [g₁_apply_BAUGD]
  by_cases hz : S.boundaryOriginalMap p ∈ tsupport ((actualSlots_BAUGD S).cutoff 0)
  · have hx := stageCloud_of_cutoff_zero_BAUGD C hz
    have hr := stageRadius_of_mem_BAUGD D hΔ (Sg 0) hx
    have hz' : ‖(actualSlots_BAUGD S).stageProj 0 (S.boundaryOriginalMap p) -
        (actualSlots_BAUGD S).stageProj 0 (S.boundaryOriginalMap p)‖ < Sg 0 * S.rho p := by
      rw [sub_self, norm_zero]; exact mul_pos hsg hρ
    have h := adjust_sub_le_BAUGD (C.slot 0) hx hr hz' (hB.1.2.1 _)
    rw [sub_self, norm_zero, add_zero] at h
    calc _ ≤ Ξ 0 * (Sg 0 * S.rho p) := h
      _ < c 0 * S.rho p := by nlinarith
  · rw [adjust_eq_of_notMem_BAUGD 0 _ hz, sub_self, norm_zero]
    nlinarith

/-- **The stage-two value error** `‖g₂ p − F_∂ p‖ < c₁ρ(p)` (on the chain's own data; tube
membership of `π₁ g₁ p` from the stage-one error and `c₀ ≤ 3Σ₁/10`). -/
theorem g₂_error_lt_BAUGD (hΔ : 0 < Δ) (p : W.Carrier) :
    ‖C.g₂ p - S.boundaryOriginalMap p‖ < c 1 * S.rho p := by
  have hN := C.numbers
  have hΞ1 := (hN.1 1).1
  have hsg1 := (hN.1 1).2.1
  have hv0 : 5 / 3 * Ξ 0 * Sg 0 < c 0 := hN.2.1
  have hc0s : c 0 ≤ 3 * Sg 1 / 10 := hN.2.2.2.2.2.1
  have hv1 : c 0 + (5 / 3 * Ξ 1 * Sg 1 + (1 + Ξ 1) * c 0) < c 1 := hN.2.2.2.2.2.2.1
  have hρ := S.rho_pos p
  have hc0 : 0 < c 0 := lt_trans (mul_pos (mul_pos (by norm_num) (hN.1 0).1) (hN.1 0).2.1) hv0
  have he1 := C.g₁_error_lt_BAUGD hΔ p
  have hB := C.cutoff_bindings
  have hsplit : C.g₂ p - S.boundaryOriginalMap p =
      ((actualSlots_BAUGD S).adjust 1 (C.slot 1).map (C.g₁ p) - C.g₁ p) +
        (C.g₁ p - S.boundaryOriginalMap p) := by
    rw [g₂_apply_BAUGD]; abel
  rw [hsplit]
  by_cases hz : C.g₁ p ∈ tsupport ((actualSlots_BAUGD S).cutoff 1)
  · have hx := C.stageCloud_of_cutoff_one_BAUGD hz
    have hr := stageRadius_of_mem_BAUGD D hΔ (Sg 1) hx
    have hwx := norm_stageProj_sub_le_BAUGD (Φ := actualSlots_BAUGD S) 1 (C.g₁ p)
      (S.boundaryOriginalMap p)
    have hz' : ‖(actualSlots_BAUGD S).stageProj 1 (C.g₁ p) -
        (actualSlots_BAUGD S).stageProj 1 (S.boundaryOriginalMap p)‖ < Sg 1 * S.rho p := by
      have : c 0 * S.rho p ≤ 3 * Sg 1 / 10 * S.rho p :=
        mul_le_mul_of_nonneg_right hc0s hρ.le
      nlinarith
    have h := adjust_sub_le_BAUGD (C.slot 1) hx hr hz' (hB.2.1.2.1 _)
    have hgap : 0 < c 1 - Ξ 1 * Sg 1 - 2 * c 0 := by
      nlinarith [mul_pos hΞ1 hsg1, mul_pos hΞ1 hc0]
    have hprod := mul_pos hgap hρ
    have hexp : (c 1 - Ξ 1 * Sg 1 - 2 * c 0) * S.rho p =
        c 1 * S.rho p - Ξ 1 * (Sg 1 * S.rho p) - 2 * (c 0 * S.rho p) := by ring
    calc _ ≤ ‖(actualSlots_BAUGD S).adjust 1 (C.slot 1).map (C.g₁ p) - C.g₁ p‖ +
          ‖C.g₁ p - S.boundaryOriginalMap p‖ := norm_add_le _ _
      _ ≤ Ξ 1 * (Sg 1 * S.rho p) + 2 * ‖C.g₁ p - S.boundaryOriginalMap p‖ := by linarith
      _ < Ξ 1 * (Sg 1 * S.rho p) + 2 * (c 0 * S.rho p) := by linarith
      _ ≤ c 1 * S.rho p := by linarith
  · rw [adjust_eq_of_notMem_BAUGD 1 _ hz, sub_self, zero_add]
    have hle : c 0 ≤ c 1 := by
      nlinarith [mul_pos hΞ1 hsg1, mul_pos hΞ1 hc0]
    exact he1.trans_le (mul_le_mul_of_nonneg_right hle hρ.le)

/-- **A3a on the chain** (D72-3 (1)): with BAUG-A's smoothness inequalities, `g₀ = F_∂`, `g₁`, `g₂`
and `g₃ = C.E` are smooth on the WHOLE original carrier `W`. -/
theorem stage_smooth_BAUGD (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b) (he : e ≤ 1 / 10) :
    ∀ k : Fin 4, ContMDiff W.model
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ∞ (C.stage k) := by
  have hF : ContMDiff W.model
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ∞ S.boundaryOriginalMap :=
    S.boundaryOriginalMap_smooth hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he
  have hN := C.numbers
  have hB := C.cutoff_bindings
  -- stage one
  have h1 : ContMDiff W.model
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ∞ C.g₁ := by
    intro p
    have hΨ : ContDiffAt ℝ ∞ ((actualSlots_BAUGD S).adjust 0 (C.slot 0).map)
        (S.boundaryOriginalMap p) := by
      by_cases hz : S.boundaryOriginalMap p ∈ tsupport ((actualSlots_BAUGD S).cutoff 0)
      · have hx := stageCloud_of_cutoff_zero_BAUGD C hz
        have hr := stageRadius_of_mem_BAUGD D hΔ (Sg 0) hx
        have hz' : ‖(actualSlots_BAUGD S).stageProj 0 (S.boundaryOriginalMap p) -
            (actualSlots_BAUGD S).stageProj 0 (S.boundaryOriginalMap p)‖ < Sg 0 * S.rho p := by
          rw [sub_self, norm_zero]; exact mul_pos (hN.1 0).2.1 (S.rho_pos p)
        exact adjust_contDiffAt_BAUGD (C.slot 0) hx hr hz' hB.1.1.contDiffAt
      · exact adjust_contDiffAt_of_notMem_BAUGD 0 _ hz
    exact hΨ.contMDiffAt.comp p (hF p)
  -- stage two
  have h2 : ContMDiff W.model
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ∞ C.g₂ := by
    intro p
    have hΨ : ContDiffAt ℝ ∞ ((actualSlots_BAUGD S).adjust 1 (C.slot 1).map) (C.g₁ p) := by
      by_cases hz : C.g₁ p ∈ tsupport ((actualSlots_BAUGD S).cutoff 1)
      · have hx := C.stageCloud_of_cutoff_one_BAUGD hz
        have hr := stageRadius_of_mem_BAUGD D hΔ (Sg 1) hx
        have hρ := S.rho_pos p
        have hc0s : c 0 ≤ 3 * Sg 1 / 10 := hN.2.2.2.2.2.1
        have he1 := C.g₁_error_lt_BAUGD hΔ p
        have hwx := norm_stageProj_sub_le_BAUGD (Φ := actualSlots_BAUGD S) 1 (C.g₁ p)
          (S.boundaryOriginalMap p)
        have hsg1 := (hN.1 1).2.1
        have hz' : ‖(actualSlots_BAUGD S).stageProj 1 (C.g₁ p) -
            (actualSlots_BAUGD S).stageProj 1 (S.boundaryOriginalMap p)‖ < Sg 1 * S.rho p := by
          have : c 0 * S.rho p ≤ 3 * Sg 1 / 10 * S.rho p :=
            mul_le_mul_of_nonneg_right hc0s hρ.le
          nlinarith
        have hscale := (hB.2.1.2.2.2.2 p 1 ⟨zero_le_one, le_rfl⟩).1
        rw [sub_self, zero_smul, zero_add, one_smul] at hscale
        have hopen : IsOpen {z : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) |
            0 < S.scaleMarker_BIF z} :=
          isOpen_lt continuous_const S.scaleMarker_BIF.continuous
        exact adjust_contDiffAt_BAUGD (C.slot 1) hx hr hz'
          (hB.2.1.1.contDiffAt (hopen.mem_nhds hscale))
      · exact adjust_contDiffAt_of_notMem_BAUGD 1 _ hz
    exact hΨ.contMDiffAt.comp p (h1 p)
  -- stage three
  have h3 : ContMDiff W.model
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ∞ C.E := by
    intro p
    have hΨ : ContDiffAt ℝ ∞ ((actualSlots_BAUGD S).adjust 2 (C.slot 2).map) (C.g₂ p) := by
      by_cases hz : C.g₂ p ∈ tsupport ((actualSlots_BAUGD S).cutoff 2)
      · have hx := C.stageCloud_of_cutoff_two_BAUGD hz
        have hr := stageRadius_of_mem_BAUGD D hΔ (Sg 2) hx
        have hρ := S.rho_pos p
        have hc1s : c 1 ≤ 3 * Sg 2 / 10 := hN.2.2.2.2.2.2.2.2.2.2.1
        have he2 := C.g₂_error_lt_BAUGD hΔ p
        have hwx := norm_stageProj_sub_le_BAUGD (Φ := actualSlots_BAUGD S) 2 (C.g₂ p)
          (S.boundaryOriginalMap p)
        have hsg2 := (hN.1 2).2.1
        have hz' : ‖(actualSlots_BAUGD S).stageProj 2 (C.g₂ p) -
            (actualSlots_BAUGD S).stageProj 2 (S.boundaryOriginalMap p)‖ < Sg 2 * S.rho p := by
          have : c 1 * S.rho p ≤ 3 * Sg 2 / 10 * S.rho p :=
            mul_le_mul_of_nonneg_right hc1s hρ.le
          nlinarith
        exact adjust_contDiffAt_BAUGD (C.slot 2) hx hr hz' hB.2.2.1.contDiffAt
      · exact adjust_contDiffAt_of_notMem_BAUGD 2 _ hz
    exact hΨ.contMDiffAt.comp p (h2 p)
  intro k
  fin_cases k
  · exact hF
  · exact h1
  · exact h2
  · exact h3

/-- **Consumer** (BCG6-K's input): the final map `C.E` is smooth on the whole original carrier. -/
theorem contMDiff_E_BAUGD (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b) (he : e ≤ 1 / 10) :
    ContMDiff W.model 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ∞ C.E :=
  C.stage_smooth_BAUGD hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he 3

/-- **Consumer**: the scale `s = ℓ_ρ(E)` is continuous on `W`. -/
theorem continuous_scale_BAUGD (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b) (he : e ≤ 1 / 10) :
    Continuous C.scale :=
  S.scaleMarker_BIF.continuous.comp (C.contMDiff_E_BAUGD hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he).continuous

end BoundaryGaf02Chain

end DifferentialGeometry.Geometry.Collapse
