import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRigidityContributorV3BGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAugmentedDataPV3

/-!
# BCG04 / BCG05 on the boundary chain over slot v2 with spec V3 (lane B-BCG-ROWS)

Blueprint `master207B.tex`, BCG04 (B:9132) and BCG05 (B:9202); frozen targets E1 / E3 of
`docs/geometrization/chapter14/evidence/boundary/TargetsBoundary.lean.txt`, on the chain of text
A-v3 (`TargetsBoundary-A-v3.lean.txt`: `BoundaryGaf02ChainE.toChain` is a
`BoundaryGaf02Chain DP.toBoundaryAugmentedData …` with `DP : BoundaryAugmentedDataPV3 S
(actualSlotsV2_BAUGD S) Γ Sg eg`). Register clause `0 ≤ Λ`, `1 ≤ Δ`, `10⁶ΔΛ < 10⁻⁵` (lead
2026-10-05 13:3x; `R.register_block_BSTD2`, the field `std` of `BoundaryGaf02ChainE`), and
`θ < 1/100` for E3 (`E.theta_BSTD2`).

* `BoundaryAugmentedDataPV3.stageRadius_cmp_V3_BGR`: `3Σρ(q)/5 ≤ r_j(π_jF_∂q) ≤ 5Σρ(q)/3`;
  `…contributor_zero_window_V3_BGR`, `…contributor_marker_window_V3_BGR` on the three tables.
* `BoundaryStageSlot_BIF.stage_step_V3_BGR` (value step `Ξ·(5/3)Σρ(p)` + `J_b`-isolation) and
  `stage_marker_V3_BGR` (`v_b = 1` kept on `Safe_b`).
* `BoundaryGaf02Chain.stagePre_{zero,one,two}_BGR`: the CFS31 localization with the preimage in
  `W°`.
* `BoundaryGaf02Chain.chain_steps_V3_BGR` (A3b with `‖g_j − F_∂‖ < c_jρ`, tube `3Σ_{j+1}ρ/5`
  from the chain's `c_j ≤ 3Σ_{j+1}/10`), **`bcg04_kernel_V3_BGR`** (E1), **`bcg05_kernel_V3_BGR`**
  (E3), `bcg04_block_norm_V3_BGR` (D69-8), `bcg04_BI_V3_BGR` / `bcg05_BFM_V3_BGR` (BCG06's (BI) /
  (BFM) premises at `C.E`).
* **`BoundaryGaf02Chain.bcg04_actualSlotsV2_BGR`**, **`bcg05_actualSlotsV2_BGR`**: E1 / E3 on
  every chain over the ACTUAL slot v2 (A0a v2 `actualSlotsV2_stageCore_BAUGD`) — the whole rows
  BCG04 (BI) and BCG05 (BFM) modulo the chain producer A2 (BAUG-Dc).
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
  (DP : BoundaryAugmentedDataPV3 S Φ Γ Sg eg)

/-- **Comparable stage radius at an anchor** (spec V3 `preimage_comparable`): at a cloud point
`x = π_j F_∂ q`, `3Σρ(q)/5 ≤ r_j(x) ≤ 5Σρ(q)/3`. -/
theorem stageRadius_cmp_V3_BGR (st : Fin 3) (hsg : 0 ≤ Sg st)
    {x : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)} (hx : x ∈ Φ.stageCloud st)
    {q : W.pieceInterior ⊤} (hq : Φ.stageProj st (S.boundaryOriginalMap q.val) = x) :
    3 / 5 * (Sg st * S.rho q) ≤ DP.stageRadius st (Sg st) x ∧
      DP.stageRadius st (Sg st) x ≤ 5 / 3 * (Sg st * S.rho q) := by
  have key : 3 / 5 * S.rho q ≤ S.rho (DP.stageSel st x) ∧
      S.rho (DP.stageSel st x) ≤ 5 / 3 * S.rho q := by
    fin_cases st
    · exact DP.circle.rsel_cmp_BGR DP.circle_spec _ hx hq
    · exact DP.edge.rsel_cmp_BGR DP.edge_spec _ hx hq
    · exact DP.slim.rsel_cmp_BGR DP.slim_spec _ hx hq
  unfold BoundaryAugmentedData.stageRadius
  have h1 := mul_le_mul_of_nonneg_left key.1 hsg
  have h2 := mul_le_mul_of_nonneg_left key.2 hsg
  constructor
  · linarith only [h1]
  · linarith only [h2]

/-- **BCG04's contributor half on the three stored tables, spec V3**: a window contributor `y` of
the anchor `x = π_j F_∂ q` with `ρ(q) > 20r_∂` has `J_b y = 0` and `L_y ≤ ker J_b`. -/
theorem contributor_zero_window_V3_BGR {Ξs : ℝ} (hΞ : 0 < Ξs) (st : Fin 3) (hsg : 0 < Sg st)
    (hsgΞ : Sg st ≤ Ξs / 10000) {rd : ℝ} (hrd : 0 < rd)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000)
    {q : W.pieceInterior ⊤} (hρq : 20 * rd < S.rho q)
    {x y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hx : x ∈ Φ.stageCloud st) (hqx : Φ.stageProj st (S.boundaryOriginalMap q.val) = x)
    (hy : y ∈ Φ.stageCloud st)
    (hwin : (closedBall y (80 * Ξs⁻¹ * DP.stageRadius st (Sg st) y) ∩
      ball x (8 * Ξs⁻¹ * DP.stageRadius st (Sg st) x)).Nonempty)
    (i : Fin S.packet.cusp.count) :
    S.boundaryBlockCLM_BAUGC i y = 0 ∧
      DP.stagePlane st y ≤ LinearMap.ker ((S.boundaryBlockCLM_BAUGC i :
        BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] WithLp 2 (ℝ² × ℝ)) :
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ]
            WithLp 2 (ℝ² × ℝ)) := by
  have hΛC := lambda_mul_stageDomain_le_BGR hΛ hΔ hΛΔ st
  fin_cases st
  · exact DP.circle.contributor_zero_window_V3_BGR DP.circle_spec _ hΞ hsg hsgΞ hrd hprem hΛ hΛC
      hρq hx hqx hy hwin i
  · exact DP.edge.contributor_zero_window_V3_BGR DP.edge_spec _ hΞ hsg hsgΞ hrd hprem hΛ hΛC
      hρq hx hqx hy hwin i
  · exact DP.slim.contributor_zero_window_V3_BGR DP.slim_spec _ hΞ hsg hsgΞ hrd hprem hΛ hΛC
      hρq hx hqx hy hwin i

/-- **BCG05's contributor half on the three stored tables, spec V3**: a window contributor `y` of
a `Safe_b` anchor `x = π_j F_∂ q` (`ρ(q) < r_∂`) has `v_b y = 1` and `L_y ≤ ker v_b` ((BA) from
BAUG-C's row value lemmas). -/
theorem contributor_marker_window_V3_BGR {Ξs : ℝ} (hΞ : 0 < Ξs) (st : Fin 3) (hsg : 0 < Sg st)
    (hsgΞ : Sg st ≤ Ξs / 10000) (hθ : θ < 1 / 100) {rd : ℝ} (hrd : 0 < rd)
    (hrd4 : rd < 1 / 10000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000)
    {i : Fin S.packet.cusp.count} {q : W.pieceInterior ⊤}
    (hp : q.val ∈ S.packet.toBoundaryCollarPacket.safeBand_BAUGA i) (hρq : S.rho q < rd)
    {x y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hx : x ∈ Φ.stageCloud st) (hqx : Φ.stageProj st (S.boundaryOriginalMap q.val) = x)
    (hy : y ∈ Φ.stageCloud st)
    (hwin : (closedBall y (80 * Ξs⁻¹ * DP.stageRadius st (Sg st) y) ∩
      ball x (8 * Ξs⁻¹ * DP.stageRadius st (Sg st) x)).Nonempty) :
    S.boundaryMarkerCLM_BAUGC i y = 1 ∧
      DP.stagePlane st y ≤ LinearMap.ker ((S.boundaryMarkerCLM_BAUGC i :
        BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ) :
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ] ℝ) := by
  have hΛC := lambda_mul_stageDomain_le_BGR hΛ hΔ hΛΔ st
  fin_cases st
  · exact DP.circle.contributor_marker_window_V3_BGR DP.circle_spec
      (fun _ ha _ hi y hy => S.circleRow_BIF_value_BAUGC ha hi y hy) _ hΞ hsg hsgΞ hθ hrd hrd4
      hprem hΛ hΛC hp hρq hx hqx hy hwin
  · exact DP.edge.contributor_marker_window_V3_BGR DP.edge_spec
      (fun _ ha _ hi y hy => (S.edgeRow_BIF_value_deriv_BAUGC ha hi).1 y hy) _ hΞ hsg hsgΞ hθ hrd
      hrd4 hprem hΛ hΛC hp hρq hx hqx hy hwin
  · exact DP.slim.contributor_marker_window_V3_BGR DP.slim_spec
      (fun _ ha _ hi y hy => (S.slimRow_BIF_value_deriv_BAUGC ha hi).1 y hy) _ hΞ hsg hsgΞ hθ hrd
      hrd4 hprem hΛ hΛC hp hρq hx hqx hy hwin

end BoundaryAugmentedDataPV3

namespace BoundaryStageSlot_BIF

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S Φ Γ Sg eg} {Kj : ℕ}

/-- **One stage of the boundary chain, spec V3** (A3b's value step and BCG04's isolation step):
for an input `z` within `3Σ_jρ(p)/5` of `F_∂ p`, whose cutoff support localizes `π_j F_∂ p` into
the stage cloud (with a preimage in `W°`), `‖Ψ_j z − z‖ ≤ ‖z − F_∂ p‖ + Ξ_j(5/3)Σ_jρ(p)`; if
moreover `ρ(p) > 20r_∂` and `J_b z = 0`, then `J_b(Ψ_j z) = 0`. -/
theorem stage_step_V3_BGR {st : Fin 3} {Ξs cws : ℝ}
    (sl : BoundaryStageSlot_BIF DP.toBoundaryAugmentedData st Kj Ξs (Sg st) cws)
    (hΞ : 0 < Ξs) (hsg : 0 < Sg st) (hSgΞ : Sg st ≤ Ξs / 10000)
    (hψ : ∀ z, Φ.cutoff st z ∈ Icc (0 : ℝ) 1) {rd : ℝ} (hrd : 0 < rd)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (i : Fin S.packet.cusp.count)
    (p : W.Carrier) (z : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
    (hloc : z ∈ tsupport (Φ.cutoff st) → ∃ q : W.pieceInterior ⊤, q.val = p ∧
      Φ.stageProj st (S.boundaryOriginalMap p) ∈ Φ.stageCloud st)
    (hz : ‖z - S.boundaryOriginalMap p‖ < 3 / 5 * (Sg st * S.rho p)) :
    ‖Φ.adjust st sl.map z - z‖ ≤
        ‖z - S.boundaryOriginalMap p‖ + Ξs * (5 / 3 * (Sg st * S.rho p)) ∧
      (20 * rd < S.rho p → S.boundaryBlockCLM_BAUGC i z = 0 →
        S.boundaryBlockCLM_BAUGC i (Φ.adjust st sl.map z) = 0) := by
  cases sl with
  | inactive hcore henl =>
    have hid : Φ.adjust st (BoundaryStageSlot_BIF.map (.inactive hcore henl :
        BoundaryStageSlot_BIF DP.toBoundaryAugmentedData st Kj Ξs (Sg st) cws)) = id :=
      Φ.adjust_id st
    rw [hid]
    refine ⟨?_, fun _ hz0 => hz0⟩
    simp only [id, sub_self, norm_zero]
    have h1 : 0 ≤ Ξs * (5 / 3 * (Sg st * S.rho p)) := by
      have := S.rho_pos p
      positivity
    linarith [norm_nonneg (z - S.boundaryOriginalMap p)]
  | active O =>
    have hmap : Φ.adjust st (BoundaryStageSlot_BIF.map (.active O :
        BoundaryStageSlot_BIF DP.toBoundaryAugmentedData st Kj Ξs (Sg st) cws)) =
        adjustmentMap (Φ.stageQ st) (fun y => (Φ.stageQ st).starProjection (O.ambient y))
          (Φ.cutoff st) := rfl
    rw [hmap]
    have hπ := Φ.starProjection_stageQ_BGR st
    have hloc' : z ∈ tsupport (Φ.cutoff st) →
        Φ.stageProj st (S.boundaryOriginalMap p) ∈ Φ.stageCloud st := fun h => by
      obtain ⟨-, -, hx⟩ := hloc h
      exact hx
    have hrx : z ∈ tsupport (Φ.cutoff st) →
        3 / 5 * (Sg st * S.rho p) ≤
            DP.stageRadius st (Sg st) (Φ.stageProj st (S.boundaryOriginalMap p)) ∧
          DP.stageRadius st (Sg st) (Φ.stageProj st (S.boundaryOriginalMap p)) ≤
            5 / 3 * (Sg st * S.rho p) := fun h => by
      obtain ⟨q, hq, hx⟩ := hloc h
      have hc := DP.stageRadius_cmp_V3_BGR st hsg.le hx (q := q) (by rw [hq])
      rw [hq] at hc
      exact hc
    refine ⟨?_, fun hρ hJ => ?_⟩
    · have h := Cfs15StageOutput.stage_step_cmp_generic_BGR
        (H := BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) O (Φ.stageQ st)
        (Φ.stageProj st) (fun v => DFunLike.congr_fun hπ v) (Φ.cutoff st) hψ
        (0 : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ)
        (fun v _ => LinearMap.mem_ker.mpr rfl) (S.boundaryOriginalMap p) z 0 hloc' hrx hz
        (fun _ y _ _ => ⟨rfl, fun v _ => LinearMap.mem_ker.mpr rfl⟩)
      exact h.1
    · have h := Cfs15StageOutput.stage_step_cmp_generic_BGR
        (H := BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) O (Φ.stageQ st)
        (Φ.stageProj st) (fun v => DFunLike.congr_fun hπ v) (Φ.cutoff st) hψ
        (S.boundaryBlockCLM_BAUGC i) (Φ.orthogonal_stageQ_le_ker_BGR st i)
        (S.boundaryOriginalMap p) z 0 hloc' hrx hz
        (fun h0 y hyI hwin => by
          obtain ⟨q, hq, hx⟩ := hloc h0
          have hρq : 20 * rd < S.rho q := by
            have e : S.rho q = S.rho p := by rw [hq]
            rw [e]
            exact hρ
          exact DP.contributor_zero_window_V3_BGR hΞ st hsg hSgΞ hrd hprem hΛ hΔ hΛΔ hρq hx
            (by rw [hq]) (O.I_subset hyI) hwin i)
      exact h.2 hJ

/-- **One stage keeps the boundary marker, spec V3** (BCG05): for `p ∈ Safe_b` and an input `z`
within `3Σ_jρ(p)/5` of `F_∂ p` whose cutoff support localizes `π_j F_∂ p` into the cloud (with a
preimage in `W°`), `v_b z = 1 ⟹ v_b(Ψ_j z) = 1`. -/
theorem stage_marker_V3_BGR (hθ : θ < 1 / 100) {st : Fin 3} {Ξs cws : ℝ}
    (sl : BoundaryStageSlot_BIF DP.toBoundaryAugmentedData st Kj Ξs (Sg st) cws)
    (hΞ : 0 < Ξs) (hsg : 0 < Sg st) (hSgΞ : Sg st ≤ Ξs / 10000)
    (hψ : ∀ z, Φ.cutoff st z ∈ Icc (0 : ℝ) 1) {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) {i : Fin S.packet.cusp.count}
    {p : W.Carrier} (hp : p ∈ S.packet.toBoundaryCollarPacket.safeBand_BAUGA i)
    (z : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
    (hloc : z ∈ tsupport (Φ.cutoff st) → ∃ q : W.pieceInterior ⊤, q.val = p ∧
      Φ.stageProj st (S.boundaryOriginalMap p) ∈ Φ.stageCloud st)
    (hz : ‖z - S.boundaryOriginalMap p‖ < 3 / 5 * (Sg st * S.rho p))
    (hz1 : S.boundaryMarkerCLM_BAUGC i z = 1) :
    S.boundaryMarkerCLM_BAUGC i (Φ.adjust st sl.map z) = 1 := by
  cases sl with
  | inactive hcore henl =>
    have hid : Φ.adjust st (BoundaryStageSlot_BIF.map (.inactive hcore henl :
        BoundaryStageSlot_BIF DP.toBoundaryAugmentedData st Kj Ξs (Sg st) cws)) = id :=
      Φ.adjust_id st
    rw [hid]
    exact hz1
  | active O =>
    have hmap : Φ.adjust st (BoundaryStageSlot_BIF.map (.active O :
        BoundaryStageSlot_BIF DP.toBoundaryAugmentedData st Kj Ξs (Sg st) cws)) =
        adjustmentMap (Φ.stageQ st) (fun y => (Φ.stageQ st).starProjection (O.ambient y))
          (Φ.cutoff st) := rfl
    rw [hmap]
    have hπ := Φ.starProjection_stageQ_BGR st
    have hloc' : z ∈ tsupport (Φ.cutoff st) →
        Φ.stageProj st (S.boundaryOriginalMap p) ∈ Φ.stageCloud st := fun h => by
      obtain ⟨-, -, hx⟩ := hloc h
      exact hx
    have hrx : z ∈ tsupport (Φ.cutoff st) →
        3 / 5 * (Sg st * S.rho p) ≤
            DP.stageRadius st (Sg st) (Φ.stageProj st (S.boundaryOriginalMap p)) ∧
          DP.stageRadius st (Sg st) (Φ.stageProj st (S.boundaryOriginalMap p)) ≤
            5 / 3 * (Sg st * S.rho p) := fun h => by
      obtain ⟨q, hq, hx⟩ := hloc h
      have hc := DP.stageRadius_cmp_V3_BGR st hsg.le hx (q := q) (by rw [hq])
      rw [hq] at hc
      exact hc
    have hne : S.packet.toBoundaryCollarPacket.block i p ≠ 0 := fun h0 => by
      have h1 := S.packet.toBoundaryCollarPacket.block_eq_of_mem_safeBand_BAUGA i hp
      rw [h0] at h1
      exact zero_ne_one (congrArg Prod.snd h1)
    have hρp : S.rho p < rd := S.toBoundarySupplyCore.rho_lt_of_mem_tsupport_block_BGR hrd hprem
      (i := i) (subset_tsupport (S.packet.toBoundaryCollarPacket.block i)
        (Function.mem_support.mpr hne))
    have h := Cfs15StageOutput.stage_step_cmp_generic_BGR
      (H := BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) O (Φ.stageQ st)
      (Φ.stageProj st) (fun v => DFunLike.congr_fun hπ v) (Φ.cutoff st) hψ
      (S.boundaryMarkerCLM_BAUGC i) (Φ.orthogonal_stageQ_le_ker_marker_BGR st i)
      (S.boundaryOriginalMap p) z 1 hloc' hrx hz
      (fun h0 y hyI hwin => by
        obtain ⟨q, hq, hx⟩ := hloc h0
        have hpq : q.val ∈ S.packet.toBoundaryCollarPacket.safeBand_BAUGA i := by
          rw [hq]
          exact hp
        have hρq : S.rho q < rd := by
          have e : S.rho q = S.rho p := by rw [hq]
          rw [e]
          exact hρp
        exact DP.contributor_marker_window_V3_BGR hΞ st hsg hSgΞ hθ hrd hrd4 hprem hΛ hΔ hΛΔ hpq
          hρq hx (by rw [hq]) (O.I_subset hyI) hwin)
    exact h.2 hz1

end BoundaryStageSlot_BIF

namespace BoundaryGaf02Chain

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S Φ Γ Sg eg} {Kj : ℕ} {Ξ c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  (C : BoundaryGaf02Chain DP.toBoundaryAugmentedData Kj Ξ Sg eg c cw bcut bder κ)

include C in
/-- **Stage-`0` localization with the preimage** (CFS31 binding + A0a's `⊇`): `F_∂ p ∈ tsupport ψ₀`
⟹ `p ∈ W°` and `π₀ F_∂ p` is in the circle stage cloud. -/
theorem stagePre_zero_BGR
    (hcore : ∀ st, ⋃ m ∈ {m : S.MarkerIdx_BAUGC | S.markerStage_BAUGC m = st},
      S.markerCore7_BAUGC m ⊆ Φ.stageCore st)
    (p : W.Carrier) (h : S.boundaryOriginalMap p ∈ tsupport (Φ.cutoff 0)) :
    ∃ q : W.pieceInterior ⊤, q.val = p ∧
      Φ.stageProj 0 (S.boundaryOriginalMap p) ∈ Φ.stageCloud 0 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  obtain ⟨q, hq, -⟩ := C.cutoff_bindings.1.2.2.2.1 p h
  exact ⟨q, hq, C.stageCloud_zero_of_tsupport_BGR hcore p h⟩

include C in
/-- **Stage-`1` localization with the preimage**. -/
theorem stagePre_one_BGR
    (hcore : ∀ st, ⋃ m ∈ {m : S.MarkerIdx_BAUGC | S.markerStage_BAUGC m = st},
      S.markerCore7_BAUGC m ⊆ Φ.stageCore st)
    (p : W.Carrier) (h : C.g₁ p ∈ tsupport (Φ.cutoff 1)) :
    ∃ q : W.pieceInterior ⊤, q.val = p ∧
      Φ.stageProj 1 (S.boundaryOriginalMap p) ∈ Φ.stageCloud 1 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  obtain ⟨q, hq, -⟩ := C.cutoff_bindings.2.1.2.2.2.1 p h
  exact ⟨q, hq, C.stageCloud_one_of_tsupport_BGR hcore p h⟩

include C in
/-- **Stage-`2` localization with the preimage**. -/
theorem stagePre_two_BGR
    (hcore : ∀ st, ⋃ m ∈ {m : S.MarkerIdx_BAUGC | S.markerStage_BAUGC m = st},
      S.markerCore7_BAUGC m ⊆ Φ.stageCore st)
    (p : W.Carrier) (h : C.g₂ p ∈ tsupport (Φ.cutoff 2)) :
    ∃ q : W.pieceInterior ⊤, q.val = p ∧
      Φ.stageProj 2 (S.boundaryOriginalMap p) ∈ Φ.stageCloud 2 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  obtain ⟨q, hq, -⟩ := C.cutoff_bindings.2.2.2.2.2.1 p h
  exact ⟨q, hq, C.stageCloud_two_of_tsupport_BGR hcore p h⟩

include C in
/-- The chain's error constants are positive and increasing: `0 < c₀ ≤ c₁ ≤ c₂`. -/
theorem c_pos_mono_V3_BGR : 0 < c 0 ∧ c 0 ≤ c 1 ∧ c 1 ≤ c 2 := by
  obtain ⟨hj, h0, -, -, -, -, h1, -, -, -, -, h2, -, -⟩ := C.numbers
  obtain ⟨hΞ0, hS0, -⟩ := hj 0
  obtain ⟨hΞ1, hS1, -⟩ := hj 1
  obtain ⟨hΞ2, hS2, -⟩ := hj 2
  have hc0 : 0 < c 0 := by
    have := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 5 / 3) hΞ0) hS0
    linarith only [this, h0]
  have hc01 : c 0 ≤ c 1 := by
    have h3 := mul_nonneg hΞ1.le hc0.le
    have h4 := (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 5 / 3) hΞ1) hS1).le
    linarith only [h1, h3, h4, hc0]
  have hc12 : c 1 ≤ c 2 := by
    have h3 := mul_nonneg hΞ2.le (hc0.trans_le hc01).le
    have h4 := (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 5 / 3) hΞ2) hS2).le
    linarith only [h2, h3, h4, hc0, hc01]
  exact ⟨hc0, hc01, hc12⟩

include C in
/-- **A3b with BCG04's isolation along the chain, spec V3** (value errors `‖g_j − F_∂‖ < c_jρ` in
the ORIGINAL metric of `H^∂`, tube membership `3Σ_{j+1}ρ/5` at every stage from the chain's
`c_j ≤ 3Σ_{j+1}/10`, and exact isolation `ρ > 20r_∂ ⟹ J_b g_j = 0`). -/
theorem chain_steps_V3_BGR
    (hcore : ∀ st, ⋃ m ∈ {m : S.MarkerIdx_BAUGC | S.markerStage_BAUGC m = st},
      S.markerCore7_BAUGC m ⊆ Φ.stageCore st) {rd : ℝ} (hrd : 0 < rd)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000)
    (i : Fin S.packet.cusp.count) (p : W.Carrier) :
    ‖C.g₁ p - S.boundaryOriginalMap p‖ < c 0 * S.rho p ∧
      ‖C.g₂ p - S.boundaryOriginalMap p‖ < c 1 * S.rho p ∧
      ‖C.E p - S.boundaryOriginalMap p‖ < c 2 * S.rho p ∧
      (20 * rd < S.rho p → S.boundaryBlockCLM_BAUGC i (C.g₁ p) = 0 ∧
        S.boundaryBlockCLM_BAUGC i (C.g₂ p) = 0 ∧ S.boundaryBlockCLM_BAUGC i (C.E p) = 0) := by
  obtain ⟨hj, h0, -, -, -, hc01, h1, -, -, -, hc12, h2, -, -⟩ := C.numbers
  obtain ⟨hΞ0, hS0, -, -, hSΞ0, -⟩ := hj 0
  obtain ⟨hΞ1, hS1, -, -, hSΞ1, -⟩ := hj 1
  obtain ⟨hΞ2, hS2, -, -, hSΞ2, -⟩ := hj 2
  have hc0 := C.c_pos_mono_V3_BGR.1
  have hψ0 := C.cutoff_bindings.1.2.1
  have hψ1 := C.cutoff_bindings.2.1.2.1
  have hψ2 := C.cutoff_bindings.2.2.2.1
  have hρ := S.rho_pos p
  -- stage 0
  have hz0 : ‖S.boundaryOriginalMap p - S.boundaryOriginalMap p‖ < 3 / 5 * (Sg 0 * S.rho p) := by
    rw [sub_self, norm_zero]; positivity
  have st0 := (C.slot 0).stage_step_V3_BGR hΞ0 hS0 hSΞ0 hψ0 hrd hprem hΛ hΔ hΛΔ i p
    (S.boundaryOriginalMap p) (C.stagePre_zero_BGR hcore p) hz0
  have hg1 : Φ.adjust 0 (C.slot 0).map (S.boundaryOriginalMap p) = C.g₁ p := rfl
  rw [hg1, sub_self, norm_zero, zero_add] at st0
  have he0 : ‖C.g₁ p - S.boundaryOriginalMap p‖ < c 0 * S.rho p := by
    have h3 : 5 / 3 * Ξ 0 * Sg 0 * S.rho p < c 0 * S.rho p := mul_lt_mul_of_pos_right h0 hρ
    have h4 : Ξ 0 * (5 / 3 * (Sg 0 * S.rho p)) = 5 / 3 * Ξ 0 * Sg 0 * S.rho p := by ring
    have st01 := st0.1
    linarith only [st01, h3, h4]
  -- stage 1
  have hz1 : ‖C.g₁ p - S.boundaryOriginalMap p‖ < 3 / 5 * (Sg 1 * S.rho p) := by
    have h3 : c 0 * S.rho p ≤ 3 * Sg 1 / 10 * S.rho p := mul_le_mul_of_nonneg_right hc01 hρ.le
    have h4 : 0 < Sg 1 * S.rho p := mul_pos hS1 hρ
    linarith only [he0, h3, h4]
  have st1 := (C.slot 1).stage_step_V3_BGR hΞ1 hS1 hSΞ1 hψ1 hrd hprem hΛ hΔ hΛΔ i p
    (C.g₁ p) (C.stagePre_one_BGR hcore p) hz1
  have hg2 : Φ.adjust 1 (C.slot 1).map (C.g₁ p) = C.g₂ p := rfl
  rw [hg2] at st1
  have he1 : ‖C.g₂ p - S.boundaryOriginalMap p‖ < c 1 * S.rho p := by
    have htri := norm_sub_le_norm_sub_add_norm_sub (C.g₂ p) (C.g₁ p) (S.boundaryOriginalMap p)
    have hΞc0 : 0 ≤ Ξ 1 * c 0 := mul_nonneg hΞ1.le hc0.le
    have hb : (2 * c 0 + 5 / 3 * Ξ 1 * Sg 1) * S.rho p < c 1 * S.rho p :=
      mul_lt_mul_of_pos_right (by linarith only [h1, hΞc0]) hρ
    have h4 : Ξ 1 * (5 / 3 * (Sg 1 * S.rho p)) = 5 / 3 * Ξ 1 * Sg 1 * S.rho p := by ring
    have st11 := st1.1
    linarith only [htri, st11, he0, hb, h4]
  -- stage 2
  have hc1 : 0 < c 1 := lt_of_lt_of_le hc0 C.c_pos_mono_V3_BGR.2.1
  have hz2 : ‖C.g₂ p - S.boundaryOriginalMap p‖ < 3 / 5 * (Sg 2 * S.rho p) := by
    have h3 : c 1 * S.rho p ≤ 3 * Sg 2 / 10 * S.rho p := mul_le_mul_of_nonneg_right hc12 hρ.le
    have h4 : 0 < Sg 2 * S.rho p := mul_pos hS2 hρ
    linarith only [he1, h3, h4]
  have st2 := (C.slot 2).stage_step_V3_BGR hΞ2 hS2 hSΞ2 hψ2 hrd hprem hΛ hΔ hΛΔ i p
    (C.g₂ p) (C.stagePre_two_BGR hcore p) hz2
  have hg3 : Φ.adjust 2 (C.slot 2).map (C.g₂ p) = C.E p := rfl
  rw [hg3] at st2
  have he2 : ‖C.E p - S.boundaryOriginalMap p‖ < c 2 * S.rho p := by
    have htri := norm_sub_le_norm_sub_add_norm_sub (C.E p) (C.g₂ p) (S.boundaryOriginalMap p)
    have hΞc1 : 0 ≤ Ξ 2 * c 1 := mul_nonneg hΞ2.le hc1.le
    have hb : (2 * c 1 + 5 / 3 * Ξ 2 * Sg 2) * S.rho p < c 2 * S.rho p :=
      mul_lt_mul_of_pos_right (by linarith only [h2, hΞc1]) hρ
    have h4 : Ξ 2 * (5 / 3 * (Sg 2 * S.rho p)) = 5 / 3 * Ξ 2 * Sg 2 * S.rho p := by ring
    have st21 := st2.1
    linarith only [htri, st21, he1, hb, h4]
  refine ⟨he0, he1, he2, fun hρ20 => ?_⟩
  have hJ0 := S.boundaryBlock_original_eq_zero_BGR hrd hprem i (p := p)
    (by linarith only [hρ20, hrd])
  have hJ1 := st0.2 hρ20 hJ0
  have hJ2 := st1.2 hρ20 hJ1
  exact ⟨hJ1, hJ2, st2.2 hρ20 hJ2⟩

include C in
/-- **BCG04 (BI) on the boundary chain, kernel form, spec V3** (frozen target E1 on any slot `Φ`
whose stage cores contain the threshold-`7` marker cores — A0a's `⊇` — and any augmented data
`DP` with BAUG-C's V3 plane spec on the three tables; register clause `0 ≤ Λ`, `1 ≤ Δ`,
`10⁶ΔΛ < 10⁻⁵`): exact isolation `ρ(p) > 20r_∂ ⟹ J_b g_j(p) = J_b F_∂(p) = 0`,
`|J_b(g_j − F_∂)| < 20c₃r_∂` componentwise everywhere (`c₃ = c 2`), and on the segment
`[F_∂ p, E p]`. -/
theorem bcg04_kernel_V3_BGR
    (hcore : ∀ st, ⋃ m ∈ {m : S.MarkerIdx_BAUGC | S.markerStage_BAUGC m = st},
      S.markerCore7_BAUGC m ⊆ Φ.stageCore st) {rd : ℝ} (hrd : 0 < rd)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) :
    (∀ (k : Fin 4) (i : Fin S.packet.cusp.count) (p : W.Carrier), 20 * rd < S.rho p →
      augmentedBoundaryCoord_BC7C i (C.stage k p) = (0, 0) ∧
        S.packet.toBoundaryCollarPacket.block i p = (0, 0)) ∧
    (∀ (k : Fin 4) (i : Fin S.packet.cusp.count) (p : W.Carrier),
      |(augmentedBoundaryCoord_BC7C i (C.stage k p)).1 -
          (S.packet.toBoundaryCollarPacket.block i p).1| < 20 * c 2 * rd ∧
      |(augmentedBoundaryCoord_BC7C i (C.stage k p)).2 -
          (S.packet.toBoundaryCollarPacket.block i p).2| < 20 * c 2 * rd) ∧
    ∀ (i : Fin S.packet.cusp.count) (p : W.Carrier),
      ∀ z ∈ segment ℝ (S.boundaryOriginalMap p) (C.E p),
      |(augmentedBoundaryCoord_BC7C i z).1 - (S.packet.toBoundaryCollarPacket.block i p).1| <
          20 * c 2 * rd ∧
      |(augmentedBoundaryCoord_BC7C i z).2 - (S.packet.toBoundaryCollarPacket.block i p).2| <
          20 * c 2 * rd := by
  obtain ⟨hc0, hc01, hc12⟩ := C.c_pos_mono_V3_BGR
  have hc2 : 0 < c 2 := by linarith only [hc0, hc01, hc12]
  have hsteps := fun i p => C.chain_steps_V3_BGR hcore hrd hprem hΛ hΔ hΛΔ i p
  have hblock : ∀ (i : Fin S.packet.cusp.count) (p : W.Carrier),
      S.packet.toBoundaryCollarPacket.block i p =
        augmentedBoundaryCoord_BC7C i (S.boundaryOriginalMap p) := fun i p =>
    (S.augmentedBoundaryCoord_boundaryOriginalMap_BIF p i).symm
  -- clause 1
  have cl1 : ∀ (k : Fin 4) (i : Fin S.packet.cusp.count) (p : W.Carrier), 20 * rd < S.rho p →
      augmentedBoundaryCoord_BC7C i (C.stage k p) = (0, 0) ∧
        S.packet.toBoundaryCollarPacket.block i p = (0, 0) := by
    intro k i p hρ
    have hρ' : rd ≤ S.rho p := by linarith only [hρ, hrd]
    have hb := S.toBoundarySupplyCore.block_eq_zero_of_le_rho_BGR hrd hprem i hρ'
    have hJ0 := S.boundaryBlock_original_eq_zero_BGR hrd hprem i hρ'
    obtain ⟨hJ1, hJ2, hJ3⟩ := (hsteps i p).2.2.2 hρ
    refine ⟨?_, hb⟩
    fin_cases k
    · exact augmentedBoundaryCoord_eq_zero_BGR hJ0
    · exact augmentedBoundaryCoord_eq_zero_BGR hJ1
    · exact augmentedBoundaryCoord_eq_zero_BGR hJ2
    · exact augmentedBoundaryCoord_eq_zero_BGR hJ3
  -- the stage distances at small scales
  have hdist : ∀ (k : Fin 4) (i : Fin S.packet.cusp.count) (p : W.Carrier), S.rho p ≤ 20 * rd →
      ‖C.stage k p - S.boundaryOriginalMap p‖ < 20 * c 2 * rd := by
    intro k i p hρ
    have hρp := S.rho_pos p
    have hm : c 2 * S.rho p ≤ c 2 * (20 * rd) := mul_le_mul_of_nonneg_left hρ hc2.le
    obtain ⟨he0, he1, he2, -⟩ := hsteps i p
    have hm0 : c 0 * S.rho p ≤ c 2 * S.rho p :=
      mul_le_mul_of_nonneg_right (hc01.trans hc12) hρp.le
    have hm1 : c 1 * S.rho p ≤ c 2 * S.rho p := mul_le_mul_of_nonneg_right hc12 hρp.le
    have hpos : 0 < 20 * c 2 * rd := by positivity
    fin_cases k
    · change ‖S.boundaryOriginalMap p - S.boundaryOriginalMap p‖ < 20 * c 2 * rd
      rw [sub_self, norm_zero]
      exact hpos
    · change ‖C.g₁ p - S.boundaryOriginalMap p‖ < 20 * c 2 * rd
      linarith only [he0, hm0, hm]
    · change ‖C.g₂ p - S.boundaryOriginalMap p‖ < 20 * c 2 * rd
      linarith only [he1, hm1, hm]
    · change ‖C.E p - S.boundaryOriginalMap p‖ < 20 * c 2 * rd
      linarith only [he2, hm]
  -- clause 2
  have cl2 : ∀ (k : Fin 4) (i : Fin S.packet.cusp.count) (p : W.Carrier),
      |(augmentedBoundaryCoord_BC7C i (C.stage k p)).1 -
          (S.packet.toBoundaryCollarPacket.block i p).1| < 20 * c 2 * rd ∧
      |(augmentedBoundaryCoord_BC7C i (C.stage k p)).2 -
          (S.packet.toBoundaryCollarPacket.block i p).2| < 20 * c 2 * rd := by
    intro k i p
    have hpos : 0 < 20 * c 2 * rd := by positivity
    by_cases hρ : 20 * rd < S.rho p
    · obtain ⟨h1', h2'⟩ := cl1 k i p hρ
      rw [h1', h2']
      simp only [sub_self, abs_zero]
      exact ⟨hpos, hpos⟩
    · have hd := hdist k i p (not_lt.mp hρ)
      rw [hblock]
      exact ⟨(abs_augmentedBoundaryCoord_fst_sub_le_BGR _ _ i).trans_lt hd,
        (abs_augmentedBoundaryCoord_snd_sub_le_BGR _ _ i).trans_lt hd⟩
  refine ⟨cl1, cl2, fun i p z hz => ?_⟩
  obtain ⟨a, bb, ha, hbb, hab, rfl⟩ := hz
  have h3 := cl2 3 i p
  change |(augmentedBoundaryCoord_BC7C i (C.E p)).1 -
      (S.packet.toBoundaryCollarPacket.block i p).1| < 20 * c 2 * rd ∧
    |(augmentedBoundaryCoord_BC7C i (C.E p)).2 -
      (S.packet.toBoundaryCollarPacket.block i p).2| < 20 * c 2 * rd at h3
  rw [hblock] at h3 ⊢
  have key : ∀ L : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ,
      L (a • S.boundaryOriginalMap p + bb • C.E p) - L (S.boundaryOriginalMap p) =
        bb * (L (C.E p) - L (S.boundaryOriginalMap p)) := by
    intro L
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, show a = 1 - bb by linarith]
    ring
  have hU := key (chainBoundaryUCLM_BCG6K i)
  have hV := key (blockMarkerCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
    (Sum.inr i))
  have hb1 : bb ≤ 1 := by linarith
  refine ⟨?_, ?_⟩
  · change |chainBoundaryUCLM_BCG6K i (a • S.boundaryOriginalMap p + bb • C.E p) -
      chainBoundaryUCLM_BCG6K i (S.boundaryOriginalMap p)| < 20 * c 2 * rd
    rw [hU, abs_mul, abs_of_nonneg hbb]
    have h31 : |chainBoundaryUCLM_BCG6K i (C.E p) -
        chainBoundaryUCLM_BCG6K i (S.boundaryOriginalMap p)| < 20 * c 2 * rd := h3.1
    calc bb * |chainBoundaryUCLM_BCG6K i (C.E p) -
          chainBoundaryUCLM_BCG6K i (S.boundaryOriginalMap p)| ≤
          1 * |chainBoundaryUCLM_BCG6K i (C.E p) -
            chainBoundaryUCLM_BCG6K i (S.boundaryOriginalMap p)| :=
          mul_le_mul_of_nonneg_right hb1 (abs_nonneg _)
      _ < 20 * c 2 * rd := by rw [one_mul]; exact h31
  · change |blockMarkerCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
        (Sum.inr i) (a • S.boundaryOriginalMap p + bb • C.E p) -
      blockMarkerCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
        (Sum.inr i) (S.boundaryOriginalMap p)| < 20 * c 2 * rd
    rw [hV, abs_mul, abs_of_nonneg hbb]
    have h32 : |blockMarkerCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
        (Sum.inr i) (C.E p) - blockMarkerCLM
          (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²) (Sum.inr i)
          (S.boundaryOriginalMap p)| < 20 * c 2 * rd := h3.2
    calc bb * |blockMarkerCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
          (Sum.inr i) (C.E p) - blockMarkerCLM
            (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²) (Sum.inr i)
            (S.boundaryOriginalMap p)| ≤
          1 * |blockMarkerCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
            (Sum.inr i) (C.E p) - blockMarkerCLM
              (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²) (Sum.inr i)
              (S.boundaryOriginalMap p)| :=
          mul_le_mul_of_nonneg_right hb1 (abs_nonneg _)
      _ < 20 * c 2 * rd := by rw [one_mul]; exact h32

include C in
/-- **BCG06's (BI) premise from E1, spec V3**: `|u_b(E) − (P.block b).1| < ε_∂` and
`|v_b(E) − (P.block b).2| < ε_∂` with `ε_∂ = 20c₃r_∂`. -/
theorem bcg04_BI_V3_BGR
    (hcore : ∀ st, ⋃ m ∈ {m : S.MarkerIdx_BAUGC | S.markerStage_BAUGC m = st},
      S.markerCore7_BAUGC m ⊆ Φ.stageCore st) {rd : ℝ} (hrd : 0 < rd)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000)
    (i : Fin S.packet.cusp.count) (p : W.Carrier) :
    |(augmentedBoundaryCoord_BC7C i (C.E p)).1 -
        (S.packet.toBoundaryCollarPacket.block i p).1| < 20 * c 2 * rd ∧
      |(augmentedBoundaryCoord_BC7C i (C.E p)).2 -
        (S.packet.toBoundaryCollarPacket.block i p).2| < 20 * c 2 * rd :=
  (C.bcg04_kernel_V3_BGR hcore hrd hprem hΛ hΔ hΛΔ).2.1 3 i p

include C in
/-- **E1's whole-block exit, spec V3** (review 69 D69-8): `‖J_b(g_j − F_∂)‖ < ε_∂ = 20c₃r_∂`
for the WHOLE physical block. -/
theorem bcg04_block_norm_V3_BGR
    (hcore : ∀ st, ⋃ m ∈ {m : S.MarkerIdx_BAUGC | S.markerStage_BAUGC m = st},
      S.markerCore7_BAUGC m ⊆ Φ.stageCore st) {rd : ℝ} (hrd : 0 < rd)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) :
    ∀ (k : Fin 4) (i : Fin S.packet.cusp.count) (p : W.Carrier),
      ‖S.boundaryBlockCLM_BAUGC i (C.stage k p - S.boundaryOriginalMap p)‖ < 20 * c 2 * rd := by
  intro k i p
  obtain ⟨hc0, hc01, hc12⟩ := C.c_pos_mono_V3_BGR
  have hc2 : 0 < c 2 := by linarith only [hc0, hc01, hc12]
  have hpos : 0 < 20 * c 2 * rd := by positivity
  have hρp := S.rho_pos p
  obtain ⟨he0, he1, he2, hiso⟩ := C.chain_steps_V3_BGR hcore hrd hprem hΛ hΔ hΛΔ i p
  by_cases hρ : 20 * rd < S.rho p
  · have hJ0 := S.boundaryBlock_original_eq_zero_BGR hrd hprem i (p := p)
      (by linarith only [hρ, hrd])
    obtain ⟨hJ1, hJ2, hJ3⟩ := hiso hρ
    have hk : S.boundaryBlockCLM_BAUGC i (C.stage k p) = 0 := by
      fin_cases k
      · exact hJ0
      · exact hJ1
      · exact hJ2
      · exact hJ3
    rw [map_sub, hk, hJ0, sub_zero, norm_zero]
    exact hpos
  · have hle : S.rho p ≤ 20 * rd := not_lt.mp hρ
    have hm : c 2 * S.rho p ≤ c 2 * (20 * rd) := mul_le_mul_of_nonneg_left hle hc2.le
    have hm0 : c 0 * S.rho p ≤ c 2 * S.rho p :=
      mul_le_mul_of_nonneg_right (hc01.trans hc12) hρp.le
    have hm1 : c 1 * S.rho p ≤ c 2 * S.rho p := mul_le_mul_of_nonneg_right hc12 hρp.le
    have hd : ‖C.stage k p - S.boundaryOriginalMap p‖ < 20 * c 2 * rd := by
      fin_cases k
      · change ‖S.boundaryOriginalMap p - S.boundaryOriginalMap p‖ < 20 * c 2 * rd
        rw [sub_self, norm_zero]
        exact hpos
      · change ‖C.g₁ p - S.boundaryOriginalMap p‖ < 20 * c 2 * rd
        linarith only [he0, hm0, hm]
      · change ‖C.g₂ p - S.boundaryOriginalMap p‖ < 20 * c 2 * rd
        linarith only [he1, hm1, hm]
      · change ‖C.E p - S.boundaryOriginalMap p‖ < 20 * c 2 * rd
        linarith only [he2, hm]
    have hn := PiLp.norm_apply_le (C.stage k p - S.boundaryOriginalMap p) (Sum.inr i)
    exact lt_of_le_of_lt hn hd

include C in
/-- **BCG05 (BFM) on the boundary chain, kernel form, spec V3** (frozen target E3, register clause
and `θ < 1/100`): on `Safe_b` the boundary marker of EVERY stage output is exactly `1` —
`v_b(g_j p) = 1`, `j = 0, …, 3`. -/
theorem bcg05_kernel_V3_BGR
    (hcore : ∀ st, ⋃ m ∈ {m : S.MarkerIdx_BAUGC | S.markerStage_BAUGC m = st},
      S.markerCore7_BAUGC m ⊆ Φ.stageCore st) (hθ : θ < 1 / 100) {rd : ℝ}
    (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) :
    ∀ (k : Fin 4) (i : Fin S.packet.cusp.count),
      ∀ p ∈ S.packet.toBoundaryCollarPacket.safeBand_BAUGA i,
        (augmentedBoundaryCoord_BC7C i (C.stage k p)).2 = 1 := by
  intro k i p hp
  obtain ⟨hj, -, -, -, -, hc01, -, -, -, -, hc12, -, -, -⟩ := C.numbers
  obtain ⟨hΞ0, hS0, -, -, hSΞ0, -⟩ := hj 0
  obtain ⟨hΞ1, hS1, -, -, hSΞ1, -⟩ := hj 1
  obtain ⟨hΞ2, hS2, -, -, hSΞ2, -⟩ := hj 2
  have hψ0 := C.cutoff_bindings.1.2.1
  have hψ1 := C.cutoff_bindings.2.1.2.1
  have hψ2 := C.cutoff_bindings.2.2.2.1
  have hρ := S.rho_pos p
  obtain ⟨he0, he1, -, -⟩ := C.chain_steps_V3_BGR hcore hrd hprem hΛ hΔ hΛΔ i p
  have hz0 : ‖S.boundaryOriginalMap p - S.boundaryOriginalMap p‖ < 3 / 5 * (Sg 0 * S.rho p) := by
    rw [sub_self, norm_zero]; positivity
  have hz1 : ‖C.g₁ p - S.boundaryOriginalMap p‖ < 3 / 5 * (Sg 1 * S.rho p) := by
    have h3 : c 0 * S.rho p ≤ 3 * Sg 1 / 10 * S.rho p := mul_le_mul_of_nonneg_right hc01 hρ.le
    have h4 : 0 < Sg 1 * S.rho p := mul_pos hS1 hρ
    linarith only [he0, h3, h4]
  have hz2 : ‖C.g₂ p - S.boundaryOriginalMap p‖ < 3 / 5 * (Sg 2 * S.rho p) := by
    have h3 : c 1 * S.rho p ≤ 3 * Sg 2 / 10 * S.rho p := mul_le_mul_of_nonneg_right hc12 hρ.le
    have h4 : 0 < Sg 2 * S.rho p := mul_pos hS2 hρ
    linarith only [he1, h3, h4]
  have hv0 : S.boundaryMarkerCLM_BAUGC i (S.boundaryOriginalMap p) = 1 := by
    change (S.boundaryOriginalMap p (Sum.inr i)).snd = 1
    rw [BoundarySupplyCore.boundaryOriginalMap_boundary_block, planeBlockEmbed_snd_BAUGA,
      S.packet.toBoundaryCollarPacket.block_eq_of_mem_safeBand_BAUGA i hp]
  have hv1 : S.boundaryMarkerCLM_BAUGC i (C.g₁ p) = 1 :=
    (C.slot 0).stage_marker_V3_BGR hθ hΞ0 hS0 hSΞ0 hψ0 hrd hrd4 hprem hΛ hΔ hΛΔ hp
      (S.boundaryOriginalMap p) (C.stagePre_zero_BGR hcore p) hz0 hv0
  have hv2 : S.boundaryMarkerCLM_BAUGC i (C.g₂ p) = 1 :=
    (C.slot 1).stage_marker_V3_BGR hθ hΞ1 hS1 hSΞ1 hψ1 hrd hrd4 hprem hΛ hΔ hΛΔ hp
      (C.g₁ p) (C.stagePre_one_BGR hcore p) hz1 hv1
  have hv3 : S.boundaryMarkerCLM_BAUGC i (C.E p) = 1 :=
    (C.slot 2).stage_marker_V3_BGR hθ hΞ2 hS2 hSΞ2 hψ2 hrd hrd4 hprem hΛ hΔ hΛΔ hp
      (C.g₂ p) (C.stagePre_two_BGR hcore p) hz2 hv2
  fin_cases k
  · exact hv0
  · exact hv1
  · exact hv2
  · exact hv3

include C in
/-- **BCG06's (BFM) premise from E3, spec V3**: `v_b(C.E) = 1` on `Safe_b`. -/
theorem bcg05_BFM_V3_BGR
    (hcore : ∀ st, ⋃ m ∈ {m : S.MarkerIdx_BAUGC | S.markerStage_BAUGC m = st},
      S.markerCore7_BAUGC m ⊆ Φ.stageCore st) (hθ : θ < 1 / 100) {rd : ℝ}
    (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (i : Fin S.packet.cusp.count) :
    ∀ p ∈ S.packet.toBoundaryCollarPacket.safeBand_BAUGA i,
      (augmentedBoundaryCoord_BC7C i (C.E p)).2 = 1 :=
  C.bcg05_kernel_V3_BGR hcore hθ hrd hrd4 hprem hΛ hΔ hΛΔ 3 i

end BoundaryGaf02Chain

/-- **BCG04 (BI), whole row on the actual chain** (frozen target E1 on every chain over BAUG-D's
ACTUAL slot v2 `actualSlotsV2_BAUGD S` with BAUG-C's V3 specs — the shape of
`BoundaryGaf02ChainE.toChain`, text A-v3; A0a v2 discharges the stage-core inclusion; register
clause `0 ≤ Λ`, `1 ≤ Δ`, `10⁶ΔΛ < 10⁻⁵` = `BoundaryGaf02ChainE.std`'s clauses 1, 10, 11). -/
theorem BoundaryGaf02Chain.bcg04_actualSlotsV2_BGR
    {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ
      W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
    {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
    {Ξ c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
    (C : BoundaryGaf02Chain DP.toBoundaryAugmentedData Kj Ξ Sg eg c cw bcut bder κ) {rd : ℝ}
    (hrd : 0 < rd)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) :
    (∀ (k : Fin 4) (i : Fin S.packet.cusp.count) (p : W.Carrier), 20 * rd < S.rho p →
      augmentedBoundaryCoord_BC7C i (C.stage k p) = (0, 0) ∧
        S.packet.toBoundaryCollarPacket.block i p = (0, 0)) ∧
    (∀ (k : Fin 4) (i : Fin S.packet.cusp.count) (p : W.Carrier),
      |(augmentedBoundaryCoord_BC7C i (C.stage k p)).1 -
          (S.packet.toBoundaryCollarPacket.block i p).1| < 20 * c 2 * rd ∧
      |(augmentedBoundaryCoord_BC7C i (C.stage k p)).2 -
          (S.packet.toBoundaryCollarPacket.block i p).2| < 20 * c 2 * rd) ∧
    ∀ (i : Fin S.packet.cusp.count) (p : W.Carrier),
      ∀ z ∈ segment ℝ (S.boundaryOriginalMap p) (C.E p),
      |(augmentedBoundaryCoord_BC7C i z).1 - (S.packet.toBoundaryCollarPacket.block i p).1| <
          20 * c 2 * rd ∧
      |(augmentedBoundaryCoord_BC7C i z).2 - (S.packet.toBoundaryCollarPacket.block i p).2| <
          20 * c 2 * rd :=
  C.bcg04_kernel_V3_BGR (fun st => (actualSlotsV2_stageCore_BAUGD S st).superset) hrd hprem hΛ hΔ
    hΛΔ

/-- **BCG05 (BFM), whole row on the actual chain** (frozen target E3 on every chain over the
ACTUAL slot v2 with the V3 specs; register clause as E1 and `θ < 1/100` = `E.theta_BSTD2`). -/
theorem BoundaryGaf02Chain.bcg05_actualSlotsV2_BGR
    {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ
      W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
    {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
    {Ξ c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
    (C : BoundaryGaf02Chain DP.toBoundaryAugmentedData Kj Ξ Sg eg c cw bcut bder κ)
    (hθ : θ < 1 / 100) {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) :
    ∀ (k : Fin 4) (i : Fin S.packet.cusp.count),
      ∀ p ∈ S.packet.toBoundaryCollarPacket.safeBand_BAUGA i,
        (augmentedBoundaryCoord_BC7C i (C.stage k p)).2 = 1 :=
  C.bcg05_kernel_V3_BGR (fun st => (actualSlotsV2_stageCore_BAUGD S st).superset) hθ hrd hrd4
    hprem hΛ hΔ hΛΔ

end DifferentialGeometry.Geometry.Collapse
