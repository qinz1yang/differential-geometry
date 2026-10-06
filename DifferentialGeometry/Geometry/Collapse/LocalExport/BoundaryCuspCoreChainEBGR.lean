import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryChainERowsBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryChainEDerivative
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoreChain

/-!
# BCG04 / BCG05 / BCG06 on the enhanced boundary chain: the E series (lane B-BCG-ROWS)

Targets §E of `TargetsBoundary-v3.1.lean.txt` on the enhanced chain
`C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj` (BAUG-D G7); the register clauses are
`C.std`, the CHOICE validity `C.validity` (with review 76 N76-4's `c 2 < 1/100000`), the derivative
errors are A3c (`stage_derivative_lt_BAUGD`, BAUG-D G9).

* **`bcg04_on_boundary_chain_BGR`** (E1, whole-block exit, D69-8),
  `bcg04_scalar_on_boundary_chain_BGR` (E1');
* **`bcg04_derivative_on_boundary_chain_BGR`** (E2: `|d(u_b − η_b)| ≤ c₂ |v|_g` on the tight band,
  from A3c and `J_b F_∂ = (η_b, 1)` near `Safe_b`);
* **`bcg05_on_boundary_chain_BGR`** (E3 with the vanishing marker differential);
* **`bcg06_on_boundary_chain_BGR`** (E4 with the STRONG component exit, review 76 D76-3: every
  component satisfies BCG6-K's `BoundaryCuspCoreComponent_BCG6K` — whole inner collar by the
  jointly smooth all-level relative flow on `W`, labelled `T² × [0, 1]`, outer-boundary label,
  `frontier C_b = H_b`, `∂C_b = ∂_bW ⊔ H_b` — AND the two-branch geometric output);
  `bcg06_on_boundary_chain_BCG6K` (frozen two-branch projection); **`bcg06_coreSpec_on_chain_BGR`**
  (E4b, the direct separated spec from `DP.separated`);
* **`bcg06_row_BGR`** (BCG06 whole-row candidate: E1 ∧ E2 ∧ E3 ∧ strong E4).
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

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- `|u_b(w)| ≤ ‖w‖`: the first boundary coordinate is a contraction. -/
theorem abs_chainBoundaryUCLM_le_BGR (b : κ) (w : BlockSpace (fun _ : ι ⊕ κ => ℝ²)) :
    |chainBoundaryUCLM_BCG6K (ι := ι) b w| ≤ ‖w‖ := by
  rw [← Real.norm_eq_abs]
  calc ‖chainBoundaryUCLM_BCG6K (ι := ι) b w‖ = ‖(w (Sum.inr b)).fst 0‖ := rfl
    _ ≤ ‖(w (Sum.inr b)).fst‖ := PiLp.norm_apply_le _ 0
    _ ≤ ‖w (Sum.inr b)‖ := WithLp.norm_fst_le (x := w (Sum.inr b))
    _ ≤ ‖w‖ := PiLp.norm_apply_le _ _

/-- **Derivative of `u_b ∘ E − η` against `F`** (generic): if `u_b ∘ F = η` near `x` and `E`, `F`
are differentiable at `x`, then `|d(u_b ∘ E − η) v| ≤ ‖dE v − dF v‖`. -/
theorem abs_mvfderiv_chainBoundaryU_sub_le_BGR {E' H' M : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] {I : ModelWithCorners ℝ E' H'} [TopologicalSpace M]
    [ChartedSpace H' M] {E F : M → BlockSpace (fun _ : ι ⊕ κ => ℝ²)} {η : M → ℝ} {x : M}
    (b : κ) (hE : MDifferentiableAt I 𝓘(ℝ, BlockSpace (fun _ : ι ⊕ κ => ℝ²)) E x)
    (hF : MDifferentiableAt I 𝓘(ℝ, BlockSpace (fun _ : ι ⊕ κ => ℝ²)) F x)
    (hη : ∀ᶠ y in 𝓝 x, (augmentedBoundaryCoord_BC7C b (F y)).1 = η y) (v : TangentSpace I x) :
    |mvfderiv I (fun y => chainBoundaryU_BCG6K E b y - η y) x v| ≤
      ‖mvfderiv I E x v - mvfderiv I F x v‖ := by
  have heq : (fun y => chainBoundaryU_BCG6K E b y - η y) =ᶠ[𝓝 x]
      (chainBoundaryUCLM_BCG6K (ι := ι) b) ∘ fun y => E y - F y := by
    filter_upwards [hη] with y hy
    change (augmentedBoundaryCoord_BC7C b (E y)).1 - η y =
      chainBoundaryUCLM_BCG6K (ι := ι) b (E y - F y)
    rw [map_sub, ← hy]
    rfl
  rw [mvfderiv_congr_BCG6K heq, mvfderiv_comp_apply_of_differentiableAt_GAF3
    (f := fun y => E y - F y) (hE.sub hF) (chainBoundaryUCLM_BCG6K (ι := ι) b).differentiableAt v,
    ContinuousLinearMap.fderiv, mvfderiv_fun_sub hE hF]
  exact abs_chainBoundaryUCLM_le_BGR b _

/-- `ε_∂ = 20c₂r_∂ < 10⁻⁶` from the `r_∂` block `20(c₂ + 1)r_∂ < 10⁻⁶`. -/
theorem epsBoundary_lt_BGR {c₂ rd : ℝ} (hrd : 0 < rd) (hrdc : 20 * (c₂ + 1) * rd < 1 / 1000000) :
    20 * c₂ * rd < 1 / 1000000 := by
  have h : 20 * (c₂ + 1) * rd = 20 * c₂ * rd + 20 * rd := by ring
  linarith only [h, hrdc, hrd]

end Generic

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **E1 BCG04 (BI), whole-block exit** (D69-8): isolation `ρ > 20r_∂ ⟹ J_b g_j = J_b F_∂ = 0`,
the WHOLE physical block `‖J_b(g_j − F_∂)‖ < ε_∂ = 20c₂r_∂`, and on the segment `[F_∂ p, E p]`. -/
theorem bcg04_on_boundary_chain_BGR {rd : ℝ} (hrd : 0 < rd)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2) :
    (∀ (k : Fin 4) (i : Fin S.packet.cusp.count) (p : W.Carrier), 20 * rd < S.rho p →
      augmentedBoundaryCoord_BC7C i (C.toChain.stage k p) = (0, 0) ∧
        S.packet.toBoundaryCollarPacket.block i p = (0, 0)) ∧
    (∀ (k : Fin 4) (i : Fin S.packet.cusp.count) (p : W.Carrier),
      ‖S.boundaryBlockCLM_BAUGC i (C.toChain.stage k p) -
          S.boundaryBlockCLM_BAUGC i (S.boundaryOriginalMap p)‖ < 20 * c 2 * rd) ∧
    ∀ (i : Fin S.packet.cusp.count) (p : W.Carrier),
      ∀ z ∈ segment ℝ (S.boundaryOriginalMap p) (C.toChain.E p),
      ‖S.boundaryBlockCLM_BAUGC i z - S.boundaryBlockCLM_BAUGC i (S.boundaryOriginalMap p)‖ <
        20 * c 2 * rd := by
  obtain ⟨hΛ, -, -, -, -, -, -, -, -, hΔ, hΛΔ, -⟩ := C.std
  have hB := C.toChain.bcg04_block_norm_V3_BGR
    (fun st => (actualSlotsV2_stageCore_BAUGD S st).superset) hrd hprem hΛ hΔ hΛΔ
  refine ⟨(C.bcg04_row_BGR hrd hprem).1, fun k i p => ?_, fun i p z hz => ?_⟩
  · rw [← map_sub]
    exact hB k i p
  · rw [segment_eq_image'] at hz
    obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hz
    have h3 : ‖S.boundaryBlockCLM_BAUGC i (C.toChain.E p - S.boundaryOriginalMap p)‖ <
        20 * c 2 * rd := hB 3 i p
    rw [map_add, add_sub_cancel_left, map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    calc t * ‖S.boundaryBlockCLM_BAUGC i (C.toChain.E p - S.boundaryOriginalMap p)‖ ≤
          1 * ‖S.boundaryBlockCLM_BAUGC i (C.toChain.E p - S.boundaryOriginalMap p)‖ :=
        mul_le_mul_of_nonneg_right ht1 (norm_nonneg _)
      _ < 20 * c 2 * rd := by rw [one_mul]; exact h3

/-- **E1' the scalar corollary**: `|u_b(g_j) − u_b(F_∂)| < ε_∂`, `|v_b(g_j) − v_b(F_∂)| < ε_∂`. -/
theorem bcg04_scalar_on_boundary_chain_BGR {rd : ℝ} (hrd : 0 < rd)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2) :
    ∀ (k : Fin 4) (i : Fin S.packet.cusp.count) (p : W.Carrier),
      |(augmentedBoundaryCoord_BC7C i (C.toChain.stage k p)).1 -
          (S.packet.toBoundaryCollarPacket.block i p).1| < 20 * c 2 * rd ∧
      |(augmentedBoundaryCoord_BC7C i (C.toChain.stage k p)).2 -
          (S.packet.toBoundaryCollarPacket.block i p).2| < 20 * c 2 * rd :=
  (C.bcg04_row_BGR hrd hprem).2.1

/-- **E2 BCG04, derivative half on the tight band** (A3c + `C.deriv_bound`): on
`band ∩ {38 ≤ η_b ≤ 42}`, `|d(u_b ∘ E − η_b) v| ≤ c₂ |v|_g` in the ORIGINAL metric. -/
theorem bcg04_derivative_on_boundary_chain_BGR :
    ∀ (i : Fin S.packet.cusp.count), ∀ x ∈ S.packet.toBoundaryCollarPacket.collarBand_BAUGA i,
      38 ≤ S.packet.toBoundaryCollarPacket.height i x →
      S.packet.toBoundaryCollarPacket.height i x ≤ 42 →
      ∀ v : TangentSpace W.model x,
        |mvfderiv W.model (fun y => chainBoundaryU_BCG6K C.toChain.E i y -
            S.packet.toBoundaryCollarPacket.height i y) x v| ≤ c 2 * Real.sqrt (g.inner x v v) := by
  intro i x hx h38 h42 v
  have hO : IsOpen (S.packet.toBoundaryCollarPacket.collarBand_BAUGA i ∩
      {y | 32 < S.packet.toBoundaryCollarPacket.height i y ∧
        S.packet.toBoundaryCollarPacket.height i y < 78}) :=
    (S.packet.toBoundaryCollarPacket.isOpen_collarBand_BAUGA i).inter
      ((isOpen_lt continuous_const
        (S.packet.toBoundaryCollarPacket.contMDiff_height i).continuous).inter
      (isOpen_lt (S.packet.toBoundaryCollarPacket.contMDiff_height i).continuous
        continuous_const))
  have hη : ∀ᶠ y in 𝓝 x, (augmentedBoundaryCoord_BC7C i (S.boundaryOriginalMap y)).1 =
      S.packet.toBoundaryCollarPacket.height i y := by
    filter_upwards [hO.mem_nhds ⟨hx, by linarith, by linarith⟩] with y hy
    rw [S.toBoundarySupplyCore.augmentedBoundaryCoord_boundaryOriginalMap_BIF y i,
      S.packet.toBoundaryCollarPacket.block_eq_of_mem_safeBand_BAUGA i
        ⟨hy.1, hy.2.1.le, hy.2.2.le⟩]
  obtain ⟨hΛ, hΔ, hμ, hτ, hΔΛ, hV, hβ1, hb0, he, -⟩ := C.std
  have hEd := (C.stage_smooth_BAUGD 3).mdifferentiableAt (x := x) (by simp)
  have hFd := (S.boundaryOriginalMap_smooth hΛ hΔ hμ hτ hΔΛ hV hβ1 hb0 he).mdifferentiableAt
    (x := x) (by simp)
  obtain ⟨Hd, hHd, hder⟩ := C.stage_derivative_lt_BAUGD 2
  exact (abs_mvfderiv_chainBoundaryU_sub_le_BGR i hEd hFd hη v).trans
    ((hder x v).trans (mul_le_mul_of_nonneg_right hHd.le (Real.sqrt_nonneg _)))

/-- **E3 BCG05 (BFM)** with the vanishing marker differential: on `Safe_b` the marker of every
stage output is exactly `1`, and its differential vanishes on the interior of `Safe_b`. -/
theorem bcg05_on_boundary_chain_BGR {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    (∀ (k : Fin 4) (i : Fin S.packet.cusp.count),
      ∀ p ∈ S.packet.toBoundaryCollarPacket.safeBand_BAUGA i,
        (augmentedBoundaryCoord_BC7C i (C.toChain.stage k p)).2 = 1) ∧
    ∀ (k : Fin 4) (i : Fin S.packet.cusp.count),
      ∀ p ∈ interior (S.packet.toBoundaryCollarPacket.safeBand_BAUGA i),
        mvfderiv W.model (fun y => (augmentedBoundaryCoord_BC7C i (C.toChain.stage k y)).2) p =
          0 := by
  have h1 := (C.bcg05_row_BGR hθ hrd hrd4 hprem).1
  refine ⟨h1, fun k i p hp => ?_⟩
  have heq : (fun y => (augmentedBoundaryCoord_BC7C i (C.toChain.stage k y)).2) =ᶠ[𝓝 p]
      fun _ => (1 : ℝ) := by
    filter_upwards [isOpen_interior.mem_nhds hp] with y hy
    exact h1 k i y (interior_subset hy)
  rw [mvfderiv_congr_BCG6K heq, mvfderiv_const]

/-- **E4 BCG06 on the enhanced chain with the STRONG component exit** (review 76 D76-3):
every component satisfies BCG6-K's per-component clauses (whole inner collar by the jointly
smooth all-level relative flow on `W`, labelled smooth `T² × [0, 1]` with the outer-boundary label,
`C_b ∩ ∂W = ∂_bW`, `frontier C_b = H_b`, front in `39.99 < η_b < 40.01` with `v_b = 1` and
`d(u_b − 40) ≠ 0`, strict markers) AND the two-branch geometric output with the original selected
zero balls. `c₃ = c 2 < 10⁻⁵` is `C.validity.c_two_lt_E4` (N76-4). -/
theorem bcg06_on_boundary_chain_BGR {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    (∀ i, S.packet.toBoundaryCollarPacket.BoundaryCuspCoreComponent_BCG6K
        (chainBoundaryU_BCG6K C.toChain.E) (chainBoundaryV_BCG6K C.toChain.E) i) ∧
      BoundaryCollarPacket.BoundaryGeometricOutput_BCG6K S.packet.toBoundaryCollarPacket
        (chainBoundaryU_BCG6K C.toChain.E) (chainBoundaryV_BCG6K C.toChain.E)
        S.toBoundarySupplyCore.zeroBall_BCG6K :=
  C.toChain.bcg06_row_chain_BCG6K
    (fun i => contMDiff_chainBoundaryU_BCG6K (C.stage_smooth_BAUGD 3) i)
    (epsBoundary_lt_BGR hrd hrdc) C.toChain.c_two_pos_BCG6K.le C.validity.c_two_lt_E4
    ((C.bcg04_row_BGR hrd hprem).2.1 3) ((C.bcg05_row_BGR hθ hrd hrd4 hprem).1 3)
    C.bcg04_derivative_on_boundary_chain_BGR

/-- **E4 (frozen two-branch projection)**: the geometric output at `J_b(C.E)` with the original
selected zero balls (the `.2` of the strong exit `bcg06_on_boundary_chain_BGR`). -/
theorem bcg06_on_boundary_chain_BCG6K {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    BoundaryCollarPacket.BoundaryGeometricOutput_BCG6K S.packet.toBoundaryCollarPacket
      (chainBoundaryU_BCG6K C.toChain.E) (chainBoundaryV_BCG6K C.toChain.E)
      S.toBoundarySupplyCore.zeroBall_BCG6K :=
  (C.bcg06_on_boundary_chain_BGR hrd hrd4 hrdc hprem hθ).2

/-- **E4b the DIRECT separated exit** (D69-8): `DP.separated` gives BCG6-K's bare spec at
`J_b(C.E)` with the original selected zero balls (inputs E1 (BI), E2 (BD), E3 (BFM), A3a). -/
theorem bcg06_coreSpec_on_chain_BGR {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    BoundaryCollarPacket.BoundaryCuspCoreSpec_BCG6K S.packet.toBoundaryCollarPacket
      (chainBoundaryU_BCG6K C.toChain.E) (chainBoundaryV_BCG6K C.toChain.E)
      S.toBoundarySupplyCore.zeroBall_BCG6K := by
  have hsep := DP.toBoundaryAugmentedData.separated
  exact S.packet.toBoundaryCollarPacket.boundaryCuspCoreSpec_BCG6K
    (cuspTolerance_le_thousandth_BCUSP1 _ _ _)
    (fun i => contMDiff_chainBoundaryU_BCG6K (C.stage_smooth_BAUGD 3) i)
    (epsBoundary_lt_BGR hrd hrdc) C.toChain.c_two_pos_BCG6K.le C.validity.c_two_lt_E4
    ((C.bcg04_row_BGR hrd hprem).2.1 3) ((C.bcg05_row_BGR hθ hrd hrd4 hprem).1 3)
    C.bcg04_derivative_on_boundary_chain_BGR (fun i j hij => (hsep.1 i j hij).1)
    S.toBoundarySupplyCore.zeroBall_BCG6K (fun z i => hsep.2.1 z.1 z.2 i)

/-- **BCG06, whole-row candidate on the enhanced chain**: E1 (whole-block exit) ∧ E2 (derivative
half) ∧ E3 (BFM with vanishing marker differential) ∧ E4 (STRONG component exit and two-branch
output). Premises: the `r_∂` block and `θ < 1/100` only. -/
theorem bcg06_row_BGR {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    ((∀ (k : Fin 4) (i : Fin S.packet.cusp.count) (p : W.Carrier), 20 * rd < S.rho p →
      augmentedBoundaryCoord_BC7C i (C.toChain.stage k p) = (0, 0) ∧
        S.packet.toBoundaryCollarPacket.block i p = (0, 0)) ∧
    (∀ (k : Fin 4) (i : Fin S.packet.cusp.count) (p : W.Carrier),
      ‖S.boundaryBlockCLM_BAUGC i (C.toChain.stage k p) -
          S.boundaryBlockCLM_BAUGC i (S.boundaryOriginalMap p)‖ < 20 * c 2 * rd) ∧
    ∀ (i : Fin S.packet.cusp.count) (p : W.Carrier),
      ∀ z ∈ segment ℝ (S.boundaryOriginalMap p) (C.toChain.E p),
      ‖S.boundaryBlockCLM_BAUGC i z - S.boundaryBlockCLM_BAUGC i (S.boundaryOriginalMap p)‖ <
        20 * c 2 * rd) ∧
    (∀ (i : Fin S.packet.cusp.count), ∀ x ∈ S.packet.toBoundaryCollarPacket.collarBand_BAUGA i,
      38 ≤ S.packet.toBoundaryCollarPacket.height i x →
      S.packet.toBoundaryCollarPacket.height i x ≤ 42 →
      ∀ v : TangentSpace W.model x,
        |mvfderiv W.model (fun y => chainBoundaryU_BCG6K C.toChain.E i y -
            S.packet.toBoundaryCollarPacket.height i y) x v| ≤
          c 2 * Real.sqrt (g.inner x v v)) ∧
    ((∀ (k : Fin 4) (i : Fin S.packet.cusp.count),
      ∀ p ∈ S.packet.toBoundaryCollarPacket.safeBand_BAUGA i,
        (augmentedBoundaryCoord_BC7C i (C.toChain.stage k p)).2 = 1) ∧
    ∀ (k : Fin 4) (i : Fin S.packet.cusp.count),
      ∀ p ∈ interior (S.packet.toBoundaryCollarPacket.safeBand_BAUGA i),
        mvfderiv W.model (fun y => (augmentedBoundaryCoord_BC7C i (C.toChain.stage k y)).2) p =
          0) ∧
    (∀ i, S.packet.toBoundaryCollarPacket.BoundaryCuspCoreComponent_BCG6K
        (chainBoundaryU_BCG6K C.toChain.E) (chainBoundaryV_BCG6K C.toChain.E) i) ∧
      BoundaryCollarPacket.BoundaryGeometricOutput_BCG6K S.packet.toBoundaryCollarPacket
        (chainBoundaryU_BCG6K C.toChain.E) (chainBoundaryV_BCG6K C.toChain.E)
        S.toBoundarySupplyCore.zeroBall_BCG6K :=
  ⟨C.bcg04_on_boundary_chain_BGR hrd hprem, C.bcg04_derivative_on_boundary_chain_BGR,
    C.bcg05_on_boundary_chain_BGR hrd hrd4 hprem hθ,
    C.bcg06_on_boundary_chain_BGR hrd hrd4 hrdc hprem hθ⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
