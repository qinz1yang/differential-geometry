import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEnhancedPlaneSpec
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceChain
import DifferentialGeometry.Geometry.Metric.Cfs15StageOutputBlendBLOC
import DifferentialGeometry.Geometry.Fibration.ActualStageTargets
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoreChain
import DifferentialGeometry.Geometry.Collapse.BoundaryCloud.SupportListsCollar
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInteriorCompletion

/-!
# BCG04 / BCG05 on the boundary chain, part 1: contributor halves (lane B-BCG-ROWS)

Blueprint `master207B.tex`, BCG04 (B:9132) and BCG01 (B:8727); external draft 61 §3.4, D61-8;
frozen target E1 of `docs/geometrization/chapter14/evidence/boundary/TargetsBoundary.lean.txt`.
Taken over from BAUG-C's G3 (lead 2026-10-05 13:3x): the contributor halves on BIFACE's stage
tables.

* Block algebra on `H^∂ = BlockSpace (ι ⊕ κ ↦ ℝ²)`: `π_{s ⊕ κ}` keeps every boundary slot
  (`blockRestrict_disjSum_inr_BGR`), `H_∂ ≤ range π` (`boundarySubmodule_le_range_BGR`), the
  coordinates `(u_b, v_b)` are `1`-Lipschitz (`abs_augmentedBoundaryCoord_{fst,snd}_sub_le_BGR`).
* One active blend step, abstractly (`Cfs15StageOutput.adjust_value_le_BGR`,
  `Cfs15StageOutput.stage_step_generic_BGR`): the value step of A3b and the isolation step of BCG04
  on CFS15's native output, with the window arithmetic `window_scale_ge_BGR` (`ℓ_y ≥ .99ℓ_x`).
* On the supply: closed supports are physically small (`rho_lt_of_mem_tsupport_block_BGR`, member
  premise at `r_∂`), BCG01's scale bound for a listed reference (`rho_lt_two_of_meets_BGR`,
  `ΛC_a ≤ 1/2`), slow variation on `ĝ`-balls (`rho_le_of_dist_lt_BGR`, `d_g ≤ d_ĝ`).
* **Contributor half of BCG04** on any stage table `R` with BAUG-C's spec
  (`BoundaryStageReferences_BIF.contributor_boundary_zero_BGR`): `ρ(pre y) ≥ 3r_∂ ⟹ J_b y = 0` and
  `L_y ≤ ker J_b` (the component is not in `J_∂(ref y)`; model slot `0`, pruning keeps it); on the
  three stored tables (`BoundaryAugmentedData.contributor_boundary_zero_BGR`, register clause
  `0 ≤ Λ`, `1 ≤ Δ`, `10⁶ΔΛ < 10⁻⁵`, `lambda_mul_stageDomain_le_BGR`).
* Scale facts of the tables: `ρ(pre y) = ℓ_ρ(y)`, `ρ(q̂ y) = ℓ_ρ(y)`, `r_j = Σ_jℓ_ρ` on the cloud.
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

variable {ι κ : Type*} [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Restricting to the blocks `s ⊕ κ` keeps every boundary slot. -/
theorem blockRestrict_disjSum_inr_BGR (s : Finset ι) (v : BlockSpace (fun _ : ι ⊕ κ => ℝ²))
    (b : κ) : blockRestrict (s.disjSum Finset.univ) v (Sum.inr b) = v (Sum.inr b) := by
  simp only [blockRestrict_apply, Finset.inr_mem_disjSum, Finset.mem_univ, ite_true]

/-- Restricting to the blocks `s ⊕ κ` keeps the interior slot of every `t ∈ s`. -/
theorem blockRestrict_disjSum_inl_BGR {s : Finset ι} {t : ι} (ht : t ∈ s)
    (v : BlockSpace (fun _ : ι ⊕ κ => ℝ²)) :
    blockRestrict (s.disjSum (Finset.univ : Finset κ)) v (Sum.inl t) = v (Sum.inl t) := by
  simp only [blockRestrict_apply, Finset.inl_mem_disjSum, ht, ite_true]

omit [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
/-- `H_∂` lies in the range of `π_{s ⊕ κ}`. -/
theorem boundarySubmodule_le_range_BGR [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) :
    augmentedBoundarySubmodule_BC7C (ι := ι) (κ := κ) ≤
      LinearMap.range (blockRestrict (V := fun _ : ι ⊕ κ => ℝ²) (s.disjSum Finset.univ) :
        BlockSpace (fun _ : ι ⊕ κ => ℝ²) →ₗ[ℝ] BlockSpace (fun _ : ι ⊕ κ => ℝ²)) := by
  intro v hv
  refine ⟨v, ?_⟩
  change blockRestrict _ v = v
  ext t : 1
  rcases t with t | t
  · rw [blockRestrict_apply]
    split_ifs
    · rfl
    · exact (hv t).symm
  · exact blockRestrict_disjSum_inr_BGR s v t

end Generic

section GenericCoord

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- `|u_b(x) − u_b(y)| ≤ ‖x − y‖` for BCG7-COLLAR's block coordinates. -/
theorem abs_augmentedBoundaryCoord_fst_sub_le_BGR (u v : BlockSpace (fun _ : ι ⊕ κ => ℝ²)) (b : κ) :
    |(augmentedBoundaryCoord_BC7C b u).1 - (augmentedBoundaryCoord_BC7C b v).1| ≤ ‖u - v‖ := by
  have h1 : (augmentedBoundaryCoord_BC7C b u).1 - (augmentedBoundaryCoord_BC7C b v).1 =
      chainBoundaryUCLM_BCG6K (ι := ι) b (u - v) := by
    rw [map_sub]
    rfl
  rw [h1, ← Real.norm_eq_abs]
  calc ‖chainBoundaryUCLM_BCG6K (ι := ι) b (u - v)‖ =
        ‖((u - v) (Sum.inr b)).fst 0‖ := rfl
    _ ≤ ‖((u - v) (Sum.inr b)).fst‖ := PiLp.norm_apply_le _ 0
    _ ≤ ‖(u - v) (Sum.inr b)‖ := WithLp.norm_fst_le (x := (u - v) (Sum.inr b))
    _ ≤ ‖u - v‖ := PiLp.norm_apply_le _ _

/-- `|v_b(x) − v_b(y)| ≤ ‖x − y‖`. -/
theorem abs_augmentedBoundaryCoord_snd_sub_le_BGR (u v : BlockSpace (fun _ : ι ⊕ κ => ℝ²)) (b : κ) :
    |(augmentedBoundaryCoord_BC7C b u).2 - (augmentedBoundaryCoord_BC7C b v).2| ≤ ‖u - v‖ := by
  have h1 : (augmentedBoundaryCoord_BC7C b u).2 - (augmentedBoundaryCoord_BC7C b v).2 =
      blockMarkerCLM (V := fun _ : ι ⊕ κ => ℝ²) (Sum.inr b) (u - v) := by
    rw [map_sub]
    rfl
  rw [h1, ← Real.norm_eq_abs]
  calc ‖blockMarkerCLM (V := fun _ : ι ⊕ κ => ℝ²) (Sum.inr b) (u - v)‖ =
        ‖((u - v) (Sum.inr b)).snd‖ := rfl
    _ ≤ ‖(u - v) (Sum.inr b)‖ := WithLp.norm_snd_le (x := (u - v) (Sum.inr b))
    _ ≤ ‖u - v‖ := PiLp.norm_apply_le _ _

omit [Fintype ι] [Fintype κ] in
/-- A vanishing whole block has vanishing coordinates `(u_b, v_b) = (0, 0)`. -/
theorem augmentedBoundaryCoord_eq_zero_BGR {u : BlockSpace (fun _ : ι ⊕ κ => ℝ²)} {b : κ}
    (h : u (Sum.inr b) = 0) : augmentedBoundaryCoord_BC7C b u = (0, 0) := by
  simp [augmentedBoundaryCoord_BC7C, h]

/-- The window arithmetic of the scale coordinate: if `‖y − x‖ ≤ 80ε⁻¹σℓ_y + 8ε⁻¹σℓ_x` with
`0 < σ ≤ ε/10⁴` and `|ℓ_y − ℓ_x| ≤ ‖y − x‖`, then `ℓ_y ≥ .99ℓ_x`. -/
theorem window_scale_ge_BGR {d ly lx εs σ : ℝ} (hε : 0 < εs) (hσ : 0 < σ) (hσε : σ ≤ εs / 10000)
    (hlx : 0 ≤ lx) (hly : 0 ≤ ly) (hd : d ≤ 80 * εs⁻¹ * (σ * ly) + 8 * εs⁻¹ * (σ * lx))
    (hl : |ly - lx| ≤ d) : 99 / 100 * lx ≤ ly := by
  have ha : εs⁻¹ * σ ≤ 1 / 10000 := by
    rw [inv_mul_le_iff₀ hε]
    linarith
  have ha0 : 0 ≤ εs⁻¹ * σ := by positivity
  have h1 := (abs_le.mp hl).1
  have h2 : d ≤ 80 * (εs⁻¹ * σ) * ly + 8 * (εs⁻¹ * σ) * lx := by
    have : 80 * εs⁻¹ * (σ * ly) + 8 * εs⁻¹ * (σ * lx) =
        80 * (εs⁻¹ * σ) * ly + 8 * (εs⁻¹ * σ) * lx := by ring
    linarith
  nlinarith

end GenericCoord

section Value

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  {k K : ℕ} {ε cw : ℝ} {S T : Set H} {r : H → ℝ} {P : H → Submodule ℝ H}

/-- **The value step of one active blend** (A3b at one stage): for `x ∈ S` and a projected input
`π_Q z ∈ B(x, r_x)`, `‖Ψ z − z‖ ≤ εr_x + ‖π_Q z − x‖` (`0 ≤ ψ ≤ 1`, CFS14 (3) for `a`). -/
theorem _root_.GC.MetricGeometry.Cfs15StageOutput.adjust_value_le_BGR
    (O : Cfs15StageOutput k K ε cw S T r P)
    (Q : Submodule ℝ H) (ψ : H → ℝ) (hψ : ∀ z, ψ z ∈ Icc (0 : ℝ) 1) {x z : H} (hx : x ∈ S)
    (hw : Q.starProjection z ∈ ball x (r x)) :
    ‖adjustmentMap Q (fun y => Q.starProjection (O.ambient y)) ψ z - z‖ ≤
      ε * r x + dist (Q.starProjection z) x := by
  set w := Q.starProjection z with hwdef
  have hval := (O.ambient_value_deriv hx hw).1
  have hww : Q.starProjection w = w :=
    Submodule.starProjection_eq_self_iff.mpr (Q.starProjection_apply_mem z)
  have h1 : adjustmentMap Q (fun y => Q.starProjection (O.ambient y)) ψ z - z =
      ψ z • Q.starProjection (O.ambient w - w) := by
    rw [adjustmentMap_apply, map_sub, hww, add_sub_cancel_left]
  have h2 : ‖(w - x) - (P x).starProjection (w - x)‖ ≤ ‖w - x‖ := by
    rw [← Submodule.starProjection_orthogonal_val]
    exact Submodule.norm_starProjection_apply_le _ _
  have h3 : ‖O.ambient w - w‖ ≤ ε * r x + ‖w - x‖ := by
    have h4 : O.ambient w - w = (O.ambient w - (x + (P x).starProjection (w - x))) -
        ((w - x) - (P x).starProjection (w - x)) := by abel
    rw [h4]
    exact (norm_sub_le _ _).trans (add_le_add hval h2)
  rw [h1, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hψ z).1, dist_eq_norm]
  calc ψ z * ‖Q.starProjection (O.ambient w - w)‖ ≤ 1 * ‖O.ambient w - w‖ :=
        mul_le_mul (hψ z).2 (Submodule.norm_starProjection_apply_le _ _) (norm_nonneg _)
          zero_le_one
    _ ≤ ε * r x + ‖w - x‖ := by rw [one_mul]; exact h3

/-- **One active blend step, abstractly** (A3b's value step and BCG04's isolation step): the
smoothing `a = O.ambient`, `Q` with `π_Q = π`, a cutoff `0 ≤ ψ ≤ 1`, the radius `r = σℓ` on the
cloud (`ℓ` a `1`-Lipschitz scale functional), an anchor `u` with `ℓ(πu) = l` whose projection is in
the
cloud when `z ∈ tsupport ψ`, and `‖z − u‖ < σl`. Then `‖Ψz − z‖ ≤ ‖z − u‖ + εσl`; and if every cloud
point `y` with `ℓ(y) ≥ 3r_∂` has `J y = 0`, `P y ≤ ker J`, `Qᗮ ≤ ker J`, `l > 20r_∂` and `J z = 0`,
then `J(Ψz) = 0`. -/
theorem _root_.GC.MetricGeometry.Cfs15StageOutput.stage_step_generic_BGR {F' : Type*}
    [NormedAddCommGroup F']
    [NormedSpace ℝ F'] (O : Cfs15StageOutput k K ε cw S T r P) (Q : Submodule ℝ H)
    (pr : H →L[ℝ] H) (hπ : ∀ v, Q.starProjection v = pr v) (ψ : H → ℝ)
    (hψ : ∀ z, ψ z ∈ Icc (0 : ℝ) 1) (J : H →L[ℝ] F')
    (hQJ : Qᗮ ≤ LinearMap.ker (J : H →ₗ[ℝ] F')) (ℓ : H →L[ℝ] ℝ) (hℓ : ‖ℓ‖ ≤ 1) {σ : ℝ}
    (hσε : σ ≤ ε / 10000) (hr : ∀ y ∈ S, r y = σ * ℓ y) (hℓS : ∀ y ∈ S, 0 ≤ ℓ y) {rd : ℝ}
    (hcontrib : ∀ y ∈ S, 3 * rd ≤ ℓ y → J y = 0 ∧ P y ≤ LinearMap.ker (J : H →ₗ[ℝ] F'))
    (u z : H) {l : ℝ} (hℓu : ℓ (pr u) = l) (hloc : z ∈ tsupport ψ → pr u ∈ S)
    (hz : ‖z - u‖ < σ * l) :
    ‖adjustmentMap Q (fun y => Q.starProjection (O.ambient y)) ψ z - z‖ ≤
        ‖z - u‖ + ε * (σ * l) ∧
      (20 * rd < l → J z = 0 →
        J (adjustmentMap Q (fun y => Q.starProjection (O.ambient y)) ψ z) = 0) := by
  have hε := O.eps_pos
  have hσl : 0 < σ * l := lt_of_le_of_lt (norm_nonneg _) hz
  by_cases hz0 : z ∈ tsupport ψ
  · have hx := hloc hz0
    have hrx : r (pr u) = σ * l := by rw [hr _ hx, hℓu]
    have hdist : dist (Q.starProjection z) (pr u) ≤ ‖z - u‖ := by
      rw [dist_eq_norm, ← hπ u, ← map_sub]
      exact Submodule.norm_starProjection_apply_le _ _
    have hw : Q.starProjection z ∈ ball (pr u) (r (pr u)) := by
      rw [mem_ball, hrx]
      exact lt_of_le_of_lt hdist hz
    refine ⟨?_, fun hρ hJ => ?_⟩
    · have h := O.adjust_value_le_BGR Q ψ hψ hx hw
      rw [hrx] at h
      linarith
    · refine O.adjustment_level_BLOC Q J hQJ ψ (x := pr u) hJ fun _ => ⟨hx, hw, ?_⟩
      intro y hyI hwin
      have hy : y ∈ S := O.I_subset hyI
      obtain ⟨v, hv1, hv2⟩ := hwin
      have hdyx : dist y (pr u) ≤ 80 * ε⁻¹ * (σ * ℓ y) + 8 * ε⁻¹ * (σ * l) := by
        have h1 : dist v y ≤ 80 * ε⁻¹ * r y := mem_closedBall.mp hv1
        have h2 : dist v (pr u) < 8 * ε⁻¹ * r (pr u) := mem_ball.mp hv2
        rw [hr y hy] at h1
        rw [hrx] at h2
        linarith [dist_triangle_left y (pr u) v]
      have hlip : |ℓ y - l| ≤ dist y (pr u) := by
        rw [← hℓu, ← map_sub, dist_eq_norm, ← Real.norm_eq_abs]
        exact (ℓ.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hℓ)
      have hl0 : 0 ≤ l := by rw [← hℓu]; exact hℓS _ hx
      have hσ : 0 < σ := by
        by_contra h
        have : σ * l ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) hl0
        linarith
      have hwin := window_scale_ge_BGR hε hσ hσε hl0 (hℓS y hy) hdyx hlip
      exact hcontrib y hy (by linarith)
  · have h0 : ψ z = 0 := image_eq_zero_of_notMem_tsupport hz0
    have hid : adjustmentMap Q (fun y => Q.starProjection (O.ambient y)) ψ z = z := by
      rw [adjustmentMap_apply, h0, zero_smul, add_zero]
    rw [hid]
    refine ⟨?_, fun _ hJ => hJ⟩
    simp only [sub_self, norm_zero]
    have := O.eps_pos
    positivity

end Value

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

namespace BoundarySupplyCore

variable (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
  ζ Λz W g δn n B oM)

/-- **The closed boundary supports are physically small** (`S.cusp_spec`, BCP01 + BSA05): with the
member premise at `r_∂`, every point of `tsupport F_b` has `ρ < r_∂`. -/
theorem rho_lt_of_mem_tsupport_block_BGR {rd : ℝ} (hrd : 0 < rd)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    {i : Fin S.packet.cusp.count} {x : W.Carrier}
    (hx : x ∈ tsupport (S.packet.toBoundaryCollarPacket.block i)) : S.rho x < rd := by
  obtain ⟨q, -, hqx, -, hq90⟩ :=
    S.packet.toBoundaryCollarPacket.exists_of_mem_tsupport_block hx
  have hε := S.packet.toBoundaryCollarPacket.tolerance_le_one
  have h96 : q.2.val 0 ≤ 96 := by linarith
  have h := S.cusp_spec.2.1 rd hrd hprem i q h96
  rw [← hqx]
  exact h

/-- Off the small scales the boundary block vanishes: `r_∂ ≤ ρ(x) ⟹ F_b(x) = 0`. -/
theorem block_eq_zero_of_le_rho_BGR {rd : ℝ} (hrd : 0 < rd)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (i : Fin S.packet.cusp.count) {x : W.Carrier} (hx : rd ≤ S.rho x) :
    S.packet.toBoundaryCollarPacket.block i x = 0 := by
  by_contra h
  exact absurd (S.rho_lt_of_mem_tsupport_block_BGR hrd hprem
    (subset_tsupport _ (Function.mem_support.mpr h))) (not_lt.mpr hx)

/-- **BCG01's scale bound for a listed reference**: if the `i`th closed support meets the `g`-ball
`B(a, Cρ(a))` and `ΛC ≤ 1/2`, then `ρ(a) < 2r_∂`. -/
theorem rho_lt_two_of_meets_BGR {rd : ℝ} (hrd : 0 < rd)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hΛ : 0 ≤ Λ) {C : ℝ} (hΛC : Λ * C ≤ 1 / 2) {a : W.Carrier} {i : Fin S.packet.cusp.count}
    (hmeet : ∃ x ∈ tsupport (S.packet.toBoundaryCollarPacket.block i),
      riemannianEDistOf g a x < ENNReal.ofReal (C * S.rho a)) :
    S.rho a < 2 * rd := by
  obtain ⟨x, hx, hax⟩ := hmeet
  have hρx := S.rho_lt_of_mem_tsupport_block_BGR hrd hprem hx
  have hlip := S.scale_spec.2.1 a x
  have hCpos : 0 < C * S.rho a := by
    by_contra hneg
    rw [ENNReal.ofReal_of_nonpos (not_lt.mp hneg)] at hax
    exact absurd hax (not_lt.mpr bot_le)
  have h1 : ENNReal.ofReal |S.rho a - S.rho x| ≤ ENNReal.ofReal (Λ * (C * S.rho a)) := by
    refine hlip.trans ?_
    rw [ENNReal.ofReal_mul hΛ]
    gcongr
  have h2 : |S.rho a - S.rho x| ≤ Λ * (C * S.rho a) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
  have h3 : Λ * (C * S.rho a) ≤ S.rho a / 2 := by
    have := S.rho_pos a
    nlinarith
  have h4 := (abs_le.mp h2).2
  linarith

/-- **Slow variation on a `ĝ`-ball of `W°`**: `d_ĝ(q, a) < Cρ(a)` and `ΛC ≤ 1/2` give
`ρ(q) ≤ 3ρ(a)/2` (`d_g ≤ d_ĝ`, `riemannianEDistOf_val_le_completion_BDRY1`). -/
theorem rho_le_of_dist_lt_BGR (hΛ : 0 ≤ Λ) {C : ℝ} (hΛC : Λ * C ≤ 1 / 2)
    {q a : W.pieceInterior ⊤}
    (h : letI := inducedMetricSpace S.completion.metric
      dist q a < C * S.rho a) :
    S.rho q ≤ 3 / 2 * S.rho a := by
  let _ := inducedMetricSpace S.completion.metric
  have hlip := S.scale_spec.2.1 q.val a.val
  have hd : riemannianEDistOf g q.val a.val ≤ ENNReal.ofReal (dist q a) := by
    have h1 := riemannianEDistOf_val_le_completion_BDRY1 W g S.completion.metric
      S.completion.inner_le q a
    rwa [inducedMetricSpace_hmetric S.completion.metric q a] at h1
  have h1 : ENNReal.ofReal |S.rho q - S.rho a| ≤ ENNReal.ofReal (Λ * (C * S.rho a)) := by
    refine hlip.trans ?_
    rw [ENNReal.ofReal_mul hΛ]
    gcongr
    exact hd.trans (ENNReal.ofReal_le_ofReal h.le)
  have hCpos : 0 ≤ C * S.rho a := le_trans dist_nonneg h.le
  have h2 : |S.rho q - S.rho a| ≤ Λ * (C * S.rho a) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
  have h3 : Λ * (C * S.rho a) ≤ S.rho a / 2 := by
    have := S.rho_pos a
    nlinarith
  have h4 := (abs_le.mp h2).2
  linarith

end BoundarySupplyCore

namespace BoundaryInteriorSlots_BIF

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} (Φ : BoundaryInteriorSlots_BIF S)

/-- `π_j` keeps every boundary slot. -/
theorem stageProj_inr_BGR (st : Fin 3)
    (v : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
    (i : Fin S.packet.cusp.count) : Φ.stageProj st v (Sum.inr i) = v (Sum.inr i) :=
  blockRestrict_disjSum_inr_BGR _ v i

/-- With the scale tag kept, `ℓ_ρ ∘ π_j = ℓ_ρ`. -/
theorem scaleMarker_stageProj_BGR {st : Fin 3} (h : S.scaleTag_BAUGA ∈ Φ.stageTags st)
    (v : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    S.scaleMarker_BIF (Φ.stageProj st v) = S.scaleMarker_BIF v := by
  change (blockRestrict (Φ.stageTagsAug st) v (Sum.inl S.scaleTag_BAUGA)).snd =
    (v (Sum.inl S.scaleTag_BAUGA)).snd
  rw [stageTagsAug, blockRestrict_disjSum_inl_BGR h]

/-- `π_{Q_j} = π_j` (the stage projection is the orthogonal projection onto `Q_j^∂`). -/
theorem starProjection_stageQ_BGR (st : Fin 3) :
    (Φ.stageQ st).starProjection = Φ.stageProj st :=
  blockRestrict_eq_starProjection_GAF3 _

/-- `H_∂ ≤ Q_j^∂`. -/
theorem boundarySubmodule_le_stageQ_BGR (st : Fin 3) :
    augmentedBoundarySubmodule_BC7C ≤ Φ.stageQ st :=
  boundarySubmodule_le_range_BGR _

/-- `(Q_j^∂)ᗮ ≤ ker J_b`. -/
theorem orthogonal_stageQ_le_ker_BGR (st : Fin 3) (i : Fin S.packet.cusp.count) :
    (Φ.stageQ st)ᗮ ≤ LinearMap.ker ((S.boundaryBlockCLM_BAUGC i :
      BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] WithLp 2 (ℝ² × ℝ)) :
        BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ]
          WithLp 2 (ℝ² × ℝ)) := fun _ hv =>
  slot_eq_zero_of_mem_orthogonal_BC7C
    (Submodule.orthogonal_le (Φ.boundarySubmodule_le_stageQ_BGR st) hv) i

end BoundaryInteriorSlots_BIF

namespace BoundaryStageReferences_BIF

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {st : Fin 3} {E : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] {eta : W.pieceInterior ⊤ → W.pieceInterior ⊤ → E}
  {row : W.pieceInterior ⊤ → Fin S.packet.cusp.count → E →L[ℝ] ℝ}
  (R : BoundaryStageReferences_BIF Φ st E eta row) {Γ sg eg : ℝ}

/-- **An unlisted boundary component annihilates the plane** (BCG04's plane half): if `b` is not
in the whole support list `J_∂(a)` of the reference `a = ref y`, the stored model slot of `b`
vanishes identically and the pruning keeps it, so `L_y ≤ ker J_b`. -/
theorem plane_le_ker_boundaryBlock_of_notMem_BGR (hR : BoundaryEnhancedPlaneSpec R Γ sg eg)
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)} (hy : y ∈ Φ.stageCloud st)
    {i : Fin S.packet.cusp.count} (hi : i ∉ S.boundaryList_BIF st (R.planes.ref ⟨y, hy⟩)) :
    R.planes.plane y ≤ LinearMap.ker ((S.boundaryBlockCLM_BAUGC i :
      BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] WithLp 2 (ℝ² × ℝ)) :
        BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ] WithLp 2 (ℝ² × ℝ)) := by
  have ha := R.ref_mem ⟨y, hy⟩
  have hpl : R.planes.plane y = stagePlane_PLN R.planes.model R.planes.prune R.planes.coord
      (R.planes.ref ⟨y, hy⟩) (R.planes.pre ⟨y, hy⟩) :=
    R.planes.plane_of_mem hy
  have hzero : ∀ u, (⇑(R.planes.prune (R.planes.ref ⟨y, hy⟩)) ∘
      R.planes.model (R.planes.ref ⟨y, hy⟩)) u (Sum.inr i) = 0 := fun u => by
    simp only [Function.comp_apply]
    rw [hR.prune_slot]
    exact R.model_unlisted _ ha i hi u
  rw [hpl]
  by_cases hd : DifferentiableAt ℝ (⇑(R.planes.prune (R.planes.ref ⟨y, hy⟩)) ∘
      R.planes.model (R.planes.ref ⟨y, hy⟩))
      (R.planes.coord (R.planes.ref ⟨y, hy⟩) (R.planes.pre ⟨y, hy⟩))
  · exact stagePlane_le_ker_proj_PLN (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
      R.planes.model R.planes.prune R.planes.coord _ _ (Sum.inr i) hd
      (Filter.Eventually.of_forall hzero)
  · have h0 := fderiv_zero_of_not_differentiableAt hd
    intro v hv
    obtain ⟨u, hu⟩ := hv
    subst hu
    simp only [ContinuousLinearMap.coe_coe, h0, zero_apply, Submodule.zero_mem]

/-- **BCG04's contributor half** at one cloud point `y` of a stage table: if the model preimage
`q = pre y` has `ρ(q) ≥ 3r_∂` (member premise at `r_∂`, `ΛC_a ≤ 1/2`), then the whole boundary block
of `y` vanishes and `L_y ≤ ker J_b` (the component `b` is not in `J_∂(ref y)`). -/
theorem contributor_boundary_zero_BGR (hR : BoundaryEnhancedPlaneSpec R Γ sg eg) {rd : ℝ}
    (hrd : 0 < rd)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hΛ : 0 ≤ Λ) (hΛC : Λ * stageDomain_BIF Δ st ≤ 1 / 2)
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)} (hy : y ∈ Φ.stageCloud st)
    (hρ : 3 * rd ≤ S.rho (R.planes.pre ⟨y, hy⟩).val) (i : Fin S.packet.cusp.count) :
    S.boundaryBlockCLM_BAUGC i y = 0 ∧
      R.planes.plane y ≤ LinearMap.ker ((S.boundaryBlockCLM_BAUGC i :
        BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] WithLp 2 (ℝ² × ℝ)) :
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ]
            WithLp 2 (ℝ² × ℝ)) := by
  have hpre := R.pre_spec ⟨y, hy⟩
  refine ⟨?_, R.plane_le_ker_boundaryBlock_of_notMem_BGR hR hy fun hi => ?_⟩
  · have hy' : y = Φ.stageProj st (S.boundaryOriginalMap (R.planes.pre ⟨y, hy⟩).val) := hpre.1.symm
    have hb := S.toBoundarySupplyCore.block_eq_zero_of_le_rho_BGR hrd hprem i
      (show rd ≤ S.rho (R.planes.pre ⟨y, hy⟩).val by linarith)
    rw [hy']
    change blockRestrict (Φ.stageTagsAug st) (S.boundaryOriginalMap _) (Sum.inr i) = 0
    rw [BoundaryInteriorSlots_BIF.stageTagsAug, blockRestrict_disjSum_inr_BGR,
      BoundarySupplyCore.boundaryOriginalMap_boundary_block, hb, map_zero]
  · have hmeet := (BoundaryCollarPacket.mem_boundarySupportList_iff_edist_BCG8b
      (P := S.packet.toBoundaryCollarPacket)).mp hi
    have h2 := S.toBoundarySupplyCore.rho_lt_two_of_meets_BGR hrd hprem hΛ hΛC hmeet
    have h3 := S.toBoundarySupplyCore.rho_le_of_dist_lt_BGR hΛ hΛC hpre.2
    linarith

/-- `R.pre` is a preimage: `ρ(pre y) = ℓ_ρ(y)` (the scale block is kept). -/
theorem rho_pre_eq_BGR (hR : BoundaryEnhancedPlaneSpec R Γ sg eg)
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)} (hy : y ∈ Φ.stageCloud st) :
    S.rho (R.planes.pre ⟨y, hy⟩).val = S.scaleMarker_BIF y := by
  have h := (R.pre_spec ⟨y, hy⟩).1
  calc S.rho (R.planes.pre ⟨y, hy⟩).val =
        S.scaleMarker_BIF (S.boundaryOriginalMap (R.planes.pre ⟨y, hy⟩).val) :=
        (S.scaleMarker_boundaryOriginalMap_BIF _).symm
    _ = S.scaleMarker_BIF (Φ.stageProj st (S.boundaryOriginalMap (R.planes.pre ⟨y, hy⟩).val)) :=
        (Φ.scaleMarker_stageProj_BGR hR.scale_kept _).symm
    _ = S.scaleMarker_BIF y := congrArg S.scaleMarker_BIF h

/-- The radius selection is a preimage on the cloud: `ρ(q̂ y) = ℓ_ρ(y)`. -/
theorem rho_rsel_eq_BGR (hR : BoundaryEnhancedPlaneSpec R Γ sg eg) (x₀ : W.pieceInterior ⊤)
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)} (hy : y ∈ Φ.stageCloud st) :
    S.rho (R.planes.rsel x₀ y).val = S.scaleMarker_BIF y := by
  have hT : y ∈ Φ.stageCloudEnlarged st := Set.image_mono hR.cloud_subset hy
  have h := R.rpre_spec ⟨y, hT⟩
  rw [R.planes.rsel_of_mem x₀ hT]
  calc S.rho (R.planes.rpre ⟨y, hT⟩).val =
        S.scaleMarker_BIF (S.boundaryOriginalMap (R.planes.rpre ⟨y, hT⟩).val) :=
        (S.scaleMarker_boundaryOriginalMap_BIF _).symm
    _ = S.scaleMarker_BIF (Φ.stageProj st (S.boundaryOriginalMap (R.planes.rpre ⟨y, hT⟩).val)) :=
        (Φ.scaleMarker_stageProj_BGR hR.scale_kept _).symm
    _ = S.scaleMarker_BIF y := congrArg S.scaleMarker_BIF h

end BoundaryStageReferences_BIF

/-- The unified register clause gives `ΛC_a ≤ 1/2` for the three reference domains
(`C_a = 10, 20Δ, 950000Δ`). -/
theorem lambda_mul_stageDomain_le_BGR (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ)
    (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (st : Fin 3) : Λ * stageDomain_BIF Δ st ≤ 1 / 2 := by
  fin_cases st <;> simp [stageDomain_BIF] <;> nlinarith

namespace BoundaryAugmentedData

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} (D : BoundaryAugmentedData S Φ)
  {Γc Γe Γs ec ee es : ℝ} {Sg : Fin 3 → ℝ}

/-- The stage radius on the cloud: `r_j(y) = Σ_j ℓ_ρ(y)`. -/
theorem stageRadius_eq_BGR (hc : BoundaryEnhancedPlaneSpec D.circle Γc (Sg 0) ec)
    (he : BoundaryEnhancedPlaneSpec D.edge Γe (Sg 1) ee)
    (hs : BoundaryEnhancedPlaneSpec D.slim Γs (Sg 2) es)
    (st : Fin 3) (sg : ℝ) {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hy : y ∈ Φ.stageCloud st) : D.stageRadius st sg y = sg * S.scaleMarker_BIF y := by
  unfold stageRadius
  congr 1
  fin_cases st
  · exact D.circle.rho_rsel_eq_BGR hc _ hy
  · exact D.edge.rho_rsel_eq_BGR he _ hy
  · exact D.slim.rho_rsel_eq_BGR hs _ hy

/-- **BCG04's contributor half on the three stored tables**: a cloud point `y` with
`ℓ_ρ(y) ≥ 3r_∂` has zero boundary block and `L_y ≤ ker J_b`. -/
theorem contributor_boundary_zero_BGR (hc : BoundaryEnhancedPlaneSpec D.circle Γc (Sg 0) ec)
    (he : BoundaryEnhancedPlaneSpec D.edge Γe (Sg 1) ee)
    (hs : BoundaryEnhancedPlaneSpec D.slim Γs (Sg 2) es)
    {rd : ℝ} (hrd : 0 < rd)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (st : Fin 3)
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)} (hy : y ∈ Φ.stageCloud st)
    (hρ : 3 * rd ≤ S.scaleMarker_BIF y) (i : Fin S.packet.cusp.count) :
    S.boundaryBlockCLM_BAUGC i y = 0 ∧
      D.stagePlane st y ≤ LinearMap.ker ((S.boundaryBlockCLM_BAUGC i :
        BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] WithLp 2 (ℝ² × ℝ)) :
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ]
            WithLp 2 (ℝ² × ℝ)) := by
  have hΛC := lambda_mul_stageDomain_le_BGR hΛ hΔ hΛΔ st
  fin_cases st
  · exact D.circle.contributor_boundary_zero_BGR hc hrd hprem hΛ hΛC hy
      (by rw [D.circle.rho_pre_eq_BGR hc hy]; exact hρ) i
  · exact D.edge.contributor_boundary_zero_BGR he hrd hprem hΛ hΛC hy
      (by rw [D.edge.rho_pre_eq_BGR he hy]; exact hρ) i
  · exact D.slim.contributor_boundary_zero_BGR hs hrd hprem hΛ hΛC hy
      (by rw [D.slim.rho_pre_eq_BGR hs hy]; exact hρ) i

/-- The scale block is kept at every stage of the stored tables. -/
theorem scale_kept_BGR (hc : BoundaryEnhancedPlaneSpec D.circle Γc (Sg 0) ec)
    (he : BoundaryEnhancedPlaneSpec D.edge Γe (Sg 1) ee)
    (hs : BoundaryEnhancedPlaneSpec D.slim Γs (Sg 2) es)
    (st : Fin 3) : S.scaleTag_BAUGA ∈ Φ.stageTags st := by
  fin_cases st
  · exact hc.scale_kept
  · exact he.scale_kept
  · exact hs.scale_kept

end BoundaryAugmentedData

end DifferentialGeometry.Geometry.Collapse
