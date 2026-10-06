import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryChainBasesSplit
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryChainMarkersChain
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPacketsBF

/-!
# BCG03: A3f' — the EDP01-type early scale exit of the enhanced boundary chain (BAUG-De; G14b)

G14b (S-BAUG-D): the SAME file as G14 (`LE/BoundaryChainEScale.lean`, held by the integrator
because it imported the undelivered B-PORT-A module
`LE/BoundaryPortPacketsResidualApplications`), with that import replaced by the delivered
`LE/BoundaryPacketsBF` and the one lemma used from the undelivered module copied as
`LocalPacketsOnBF.dist_lt_of_norm_coord_le_BAUGD` (dedupe later against `…_BAUGP`). All other
declarations and statements are unchanged; G14b supersedes G14 (the G14 file must not be
registered).

Target A3f' `scale_edp01_BAUGD` of `TargetsBoundary-A-v3.1.lean.txt` (review 69 §1.7, D69-5 (4);
closed twin `Gaf02Chain.edp01_GAF8`): for `C : BoundaryGaf02ChainE DP …`, with
`C_ρ = 100(b_der + 1)(1 + b_cut + c_w(0)/Σ₀) ≥ 100`, the scale `s = ℓ_ρ(E)` is differentiable on
`W`, `|s − ρ| ≤ C_ρΛρ`, `|ds(v)| ≤ C_ρΛ|v|_g` (original metric) and `s > 0`.

Route (BAUG-Dd handover): `s = φ ∘ F_∂` with the blend `φ(z) = ℓ_ρ z + ψ₀ z (ℓ_ρ(a₀ z) − ℓ_ρ z)`
(`π₀ = id`, the later stages keep the scale slot; `ℓ_ρ ∘ F_∂ = ρ`):

* `scaleBlend_hasFDerivAt_BAUGD`, `scaleBlend_deriv_le_BAUGD` (abstract calculus of the blend),
  `scaleMarker_adjust_zero_V2_BAUGD`, `BoundaryGaf02Chain.scale_eq_blend_V2_BAUGD`;
* (SC) the contributor scale at stage `0`, `circle_contributor_scale_BAUGD`: a window contributor
  `i = F_∂(qᵢ)` of a `ψ₀`-localized point `q` (circle chart `j`, `‖η_j(q)‖ ≤ 13/2`) has
  `ζ_j(qᵢ) = 1` (V3 `full_marker`), `‖η_j(qᵢ)‖ ≤ 8` (circle block identity + window size), so both
  points lie in `B(j, 10ρ_j)` (TCP01) and `|ρ(qᵢ) − ρ(q)| ≤ 20Λρ_j ≤ 80/3 Λρ(q)`;
* (SMV) `scale_smv_zero_BAUGD`: CFS15's slow-marker clause `Cfs15StageOutput.smv_of_cloud_C15`
  with `ℓ = ℓ_ρ` (planes in `ker ℓ_ρ`: V3 `scale_zero`), `R₀ = ρ(q)`, `β = 80/3 Λρ(q)`;
* `BoundaryGaf02ChainE.scale_edp01_support_BAUGD` (on `tsupport ψ₀`),
  `BoundaryGaf02ChainE.scale_edp01_off_BAUGD` (off it `s = ρ` nearby; `|dρ| ≤ Λ|v|_g`),
  **`BoundaryGaf02ChainE.scale_edp01_BAUGD`** (A3f').
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

namespace LocalPacketsOnBF

/-- **TCP01, circle clause** (verbatim copy of `dist_lt_of_norm_coord_le_BAUGP` of the undelivered
B-PORT-A module `LE/BoundaryPortPacketsResidualApplications.lean`; dedupe later). At every circle
centre `j`, every point `x` of the chart domain `B(j, 200ρ(j))` with `|η_j(x)| ≤ 8` lies in
`D_j = B(j, 10ρ(j))`. -/
theorem dist_lt_of_norm_coord_le_BAUGD {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompleteSpace X] [SigmaCompactSpace X]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ} {vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}
    (L : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      vs ζ Λz U₁ U₂ Ue₁ Ue₂)
    {j : X} (hj : j ∈ L.circle.centres) {x : X} (hx : dist x j < 200 * ρ j)
    (h8 : let c := L.circle.chart j hj
      letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      ‖c.coord x‖ ≤ 8) :
    dist x j < 10 * ρ j := by
  have hres := L.circle_residual j hj
  have hx' : (ρ j)⁻¹ * dist x j < 200 := inv_mul_dist_lt_of_mem_ball_LC87 (hρ j) hx
  have h10 : (ρ j)⁻¹ * dist x j < 10 := hres x hx' h8
  have h := (inv_mul_lt_iff₀ (hρ j)).mp h10
  linarith

end LocalPacketsOnBF

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

/-- The blend `φ(z) = ℓ z + ψ z (ℓ(a z) − ℓ z)`: differentiable, with its derivative. -/
theorem scaleBlend_hasFDerivAt_BAUGD {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (ℓ : H →L[ℝ] ℝ) (a : H → H) (ψ : H → ℝ) {y : H} (ha : DifferentiableAt ℝ a y)
    (hψ : DifferentiableAt ℝ ψ y) :
    DifferentiableAt ℝ (fun z => ℓ z + ψ z * (ℓ (a z) - ℓ z)) y ∧
      ∀ w, fderiv ℝ (fun z => ℓ z + ψ z * (ℓ (a z) - ℓ z)) y w =
        (1 - ψ y) * ℓ w + ψ y * ℓ (fderiv ℝ a y w) + fderiv ℝ ψ y w * (ℓ (a y) - ℓ y) := by
  have h1 : HasFDerivAt (fun z => ℓ (a z)) (ℓ.comp (fderiv ℝ a y)) y :=
    ℓ.hasFDerivAt.comp y ha.hasFDerivAt
  have h2 : HasFDerivAt (fun z => ℓ (a z) - ℓ z) (ℓ.comp (fderiv ℝ a y) - ℓ) y :=
    h1.sub ℓ.hasFDerivAt
  have h4 : HasFDerivAt (fun z => ℓ z + ψ z * (ℓ (a z) - ℓ z))
      (ℓ + (ψ y • (ℓ.comp (fderiv ℝ a y) - ℓ) + (ℓ (a y) - ℓ y) • fderiv ℝ ψ y)) y :=
    ℓ.hasFDerivAt.add (hψ.hasFDerivAt.mul h2)
  refine ⟨h4.differentiableAt, fun w => ?_⟩
  rw [h4.fderiv]
  simp only [add_apply, smul_apply, sub_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    smul_eq_mul]
  ring

/-- The bound of the blend's derivative. -/
theorem scaleBlend_deriv_le_BAUGD {ψy Lw La Dψ dℓ Aw M N bψ β₀ : ℝ}
    (hψ : ψy ∈ Icc (0 : ℝ) 1) (hLw : |Lw| ≤ Aw) (hLa : |La| ≤ M * N)
    (hDψ : |Dψ| ≤ bψ * N) (hdℓ : |dℓ| ≤ β₀) :
    |(1 - ψy) * Lw + ψy * La + Dψ * dℓ| ≤ Aw + M * N + bψ * N * β₀ := by
  obtain ⟨h0, h1⟩ := hψ
  have hA := (abs_nonneg Lw).trans hLw
  have hM := (abs_nonneg La).trans hLa
  have e1 : |(1 - ψy) * Lw| ≤ Aw := by
    rw [abs_mul, abs_of_nonneg (by linarith)]
    nlinarith [abs_nonneg Lw]
  have e2 : |ψy * La| ≤ M * N := by
    rw [abs_mul, abs_of_nonneg h0]
    nlinarith [abs_nonneg La]
  have e3 : |Dψ * dℓ| ≤ bψ * N * β₀ := by
    rw [abs_mul]
    exact mul_le_mul hDψ hdℓ (abs_nonneg _) ((abs_nonneg _).trans hDψ)
  calc _ ≤ |(1 - ψy) * Lw + ψy * La| + |Dψ * dℓ| := abs_add_le _ _
    _ ≤ |(1 - ψy) * Lw| + |ψy * La| + |Dψ * dℓ| := by gcongr; exact abs_add_le _ _
    _ ≤ _ := by linarith

/-- On the v2 slot, `ℓ_ρ(Ψ₀ z) = ℓ_ρ z + ψ₀ z (ℓ_ρ(a z) − ℓ_ρ z)` (`π₀ = id`). -/
theorem scaleMarker_adjust_zero_V2_BAUGD {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε
    γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g δn n B oM}
    (a : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →
      BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
    (z : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    S.scaleMarker_BIF ((actualSlotsV2_BAUGD S).adjust 0 a z) =
      S.scaleMarker_BIF z + (actualSlotsV2_BAUGD S).cutoff 0 z *
        (S.scaleMarker_BIF (a z) - S.scaleMarker_BIF z) := by
  have hP : ∀ u, ((actualSlotsV2_BAUGD S).stageQ 0).starProjection u = u := fun u =>
    (DFunLike.congr_fun (stageQ_starProjection_BAUGD (Φ := actualSlotsV2_BAUGD S) 0) u).trans
      (stageProj_zero_V2_BAUGD S u)
  simp only [BoundaryInteriorSlots_BIF.adjust, adjustmentMap_apply, hP, map_add, map_smul,
    map_sub, smul_eq_mul]

namespace BoundarySupplyCore

variable (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
  ζ Λz W g δn n B oM)

/-- **`ρ` is `Λ`-Lipschitz in `d_ĝ` on a circle chart ball** (T3B's consumer-ball transport
identifies `d_g` with `d_ĝ` on `B(j, K₀ρ_j)`). -/
theorem rho_sub_le_circle_BAUGD (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ) (hV : 0 ≤ V) (hβ1 : 0 < β 1)
    (hb : 0 < b) (j : S.CircleIdx_BAUGD) (q : W.pieceInterior ⊤)
    (hq : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 200 * S.rho j.1) :
    |S.rho q.val - S.rho j.1.val| ≤
      Λ * (letI := inducedMetricSpace S.completion.metric; dist q j.1) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  have hj1 : ENNReal.ofReal 10 < distanceToBoundary W g j.1 :=
    (S.family.circle.centres_subset hj).1
  have htr := (S.transport_spec.2.1 j.1 hj1).2
  have hK0 := consumerConstant_ge_BAUGA hΔ hV hβ1 hb
  have hrj := S.rho_pos j.1
  have hqK : q ∈ ball j.1 ((2010000 + 2000000 * Δ + 400 * V + (β 1)⁻¹ + b⁻¹) * S.rho j.1) :=
    ball_subset_ball (by nlinarith) (mem_ball.mpr hq)
  have hjK : j.1 ∈ ball j.1 ((2010000 + 2000000 * Δ + 400 * V + (β 1)⁻¹ + b⁻¹) * S.rho j.1) :=
    mem_ball_self (mul_pos (by nlinarith) hrj)
  have hdist : riemannianEDistOf g q.val j.1.val = edist q j.1 := htr q hqK j.1 hjK
  have hlip := S.scale_spec.2.1 q.val j.1.val
  have h1 : ENNReal.ofReal |S.rho q.val - S.rho j.1.val| ≤ ENNReal.ofReal (Λ * dist q j.1) := by
    refine hlip.trans ?_
    rw [hdist, ENNReal.ofReal_mul hΛ, edist_dist]
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hΛ dist_nonneg)).mp h1

/-- **TCP01's circle enclosure on `W`**: a point of the chart ball `B(j, 200ρ_j)` with
`‖η_j‖ ≤ 8` lies in `B(j, 10ρ_j)`. -/
theorem circle_dist_lt_ten_BAUGD (j : S.CircleIdx_BAUGD) (q : W.pieceInterior ⊤)
    (hq : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 200 * S.rho j.1)
    (h8 : ‖S.circleCoordW_BAUGD j q.val‖ ≤ 8) :
    letI := inducedMetricSpace S.completion.metric; dist q j.1 < 10 * S.rho j.1 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  rw [S.circleCoordW_val_BAUGD] at h8
  simp only [CircleFamilyOn.coord_BAUGA, hj, ↓reduceDIte] at h8
  exact S.family.toLocalPacketsOnBFR.toLocalPacketsOnBF.dist_lt_of_norm_coord_le_BAUGD hj hq h8

/-- The circle vector block is norm-nonincreasing. -/
theorem norm_circleVector_le_BAUGD (j : S.CircleIdx_BAUGD)
    (z : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    ‖S.circleVector_BAUGD j z‖ ≤ ‖z‖ := by
  simp only [circleVector_BAUGD, blockVectorCLM_apply]
  exact (WithLp.norm_fst_le (x := z _)).trans (PiLp.norm_apply_le z _)

end BoundarySupplyCore

/-- The contributor window bounds the distance: a point of `B̄(i, 80Ξ⁻¹rᵢ) ∩ B(x, 8Ξ⁻¹rₓ)` gives
`d(i, x) ≤ 80Ξ⁻¹rᵢ + 8Ξ⁻¹rₓ`. -/
theorem dist_le_of_window_BAUGD {H : Type*} [MetricSpace H] {i x : H} {ri rx Ξ₀ : ℝ}
    (hwin : (closedBall i (80 * Ξ₀⁻¹ * ri) ∩ ball x (8 * Ξ₀⁻¹ * rx)).Nonempty) :
    dist i x ≤ 80 * Ξ₀⁻¹ * ri + 8 * Ξ₀⁻¹ * rx := by
  obtain ⟨z, hz1, hz2⟩ := hwin
  have h1 : dist z i ≤ 80 * Ξ₀⁻¹ * ri := hz1
  have h2 : dist z x < 8 * Ξ₀⁻¹ * rx := hz2
  have h3 := dist_triangle i z x
  rw [dist_comm i z] at h3
  linarith

/-- The window arithmetic: `rᵢ ≤ 5/3 Σρ(qᵢ)`, `rₓ ≤ 5/3 Σρ(q)`, `ρ(qᵢ), ρ(q) ≤ 5/4 R`, `Σ ≤ Ξ/10⁴`
give `80Ξ⁻¹rᵢ + 8Ξ⁻¹rₓ ≤ R/50`. -/
theorem window_arith_BAUGD {Ξ₀ sg ri rx ρi ρq R : ℝ} (hΞ : 0 < Ξ₀) (hsg : 0 ≤ sg)
    (hsgΞ : sg ≤ Ξ₀ / 10000) (hri : ri ≤ 5 / 3 * (sg * ρi)) (hrx : rx ≤ 5 / 3 * (sg * ρq))
    (hρi : ρi ≤ 5 / 4 * R) (hρq : ρq ≤ 5 / 4 * R) (hρi0 : 0 ≤ ρi) (hρq0 : 0 ≤ ρq) :
    80 * Ξ₀⁻¹ * ri + 8 * Ξ₀⁻¹ * rx ≤ R / 50 := by
  have ht : Ξ₀⁻¹ * sg ≤ 1 / 10000 := by
    rw [inv_mul_le_iff₀ hΞ]
    linarith
  have ht0 : 0 ≤ Ξ₀⁻¹ * sg := mul_nonneg (inv_nonneg.mpr hΞ.le) hsg
  have hi0 : 0 ≤ Ξ₀⁻¹ := inv_nonneg.mpr hΞ.le
  have e1 : 80 * Ξ₀⁻¹ * ri ≤ 80 * (5 / 3) * (Ξ₀⁻¹ * sg) * ρi := by
    have := mul_le_mul_of_nonneg_left hri (mul_nonneg (by norm_num : (0 : ℝ) ≤ 80) hi0)
    linarith
  have e2 : 8 * Ξ₀⁻¹ * rx ≤ 8 * (5 / 3) * (Ξ₀⁻¹ * sg) * ρq := by
    have := mul_le_mul_of_nonneg_left hrx (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hi0)
    linarith
  have e3 : (Ξ₀⁻¹ * sg) * ρi ≤ 1 / 10000 * (5 / 4 * R) :=
    mul_le_mul ht hρi hρi0 (by norm_num)
  have e4 : (Ξ₀⁻¹ * sg) * ρq ≤ 1 / 10000 * (5 / 4 * R) :=
    mul_le_mul ht hρq hρq0 (by norm_num)
  nlinarith

namespace BoundarySupplyCore

variable (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
  ζ Λz W g δn n B oM)

/-- **Two plateau points of one circle chart**: `ζ_j(q') = ζ_j(q) = 1 ⟹
ρ_j ‖η_j(q') − η_j(q)‖ ≤ ‖F_∂ q' − F_∂ q‖` (the circle vector block of `F_∂` is `ρ_j ζ_j η_j`). -/
theorem circle_coord_close_BAUGD (j : S.CircleIdx_BAUGD) {q' q : W.Carrier}
    (h' : S.circleCutoffW_BAUGD j q' = 1) (h : S.circleCutoffW_BAUGD j q = 1) :
    S.rho j.1 * ‖S.circleCoordW_BAUGD j q' - S.circleCoordW_BAUGD j q‖ ≤
      ‖S.boundaryOriginalMap q' - S.boundaryOriginalMap q‖ := by
  have e' := (S.circleBlock_boundaryOriginalMap_BAUGD j q').1
  have e := (S.circleBlock_boundaryOriginalMap_BAUGD j q).1
  rw [h', mul_one] at e'
  rw [h, mul_one] at e
  have hsub : S.circleVector_BAUGD j (S.boundaryOriginalMap q' - S.boundaryOriginalMap q) =
      S.rho j.1 • (S.circleCoordW_BAUGD j q' - S.circleCoordW_BAUGD j q) := by
    rw [map_sub, e', e, smul_sub]
  have hn := S.norm_circleVector_le_BAUGD j (S.boundaryOriginalMap q' - S.boundaryOriginalMap q)
  rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos (S.rho_pos j.1.val)] at hn
  exact hn

/-- A positive circle cutoff puts the point in the chart ball `B(j, 200ρ_j)`. -/
theorem circle_dist_lt_of_cutoff_pos_BAUGD (j : S.CircleIdx_BAUGD) (q : W.pieceInterior ⊤)
    (hpos : 0 < S.circleCutoffW_BAUGD j q.val) :
    letI := inducedMetricSpace S.completion.metric; dist q j.1 < 200 * S.rho j.1 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  rw [S.circleCutoffW_val_BAUGD] at hpos
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  exact mem_ball.mp (S.family.circle.tsupport_subset_ball j.1 hj (subset_tsupport _ hpos.ne'))

end BoundarySupplyCore

section Contributor

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}

/-- **(FM*) at stage `0`**: a window contributor `i = F_∂(qᵢ)` of the threshold-`7` point `q` of
the circle chart `j` lies in the plateau of `j`: `ζ_j(qᵢ) = 1`. -/
theorem circle_cutoff_one_of_window_BAUGD
    (DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg) {Ξ₀ : ℝ} (hΞ : 0 < Ξ₀)
    (hsg : 0 ≤ Sg 0) (hsgΞ : Sg 0 ≤ Ξ₀ / 10000) (j : S.CircleIdx_BAUGD) (q : W.pieceInterior ⊤)
    (hq7 : q ∈ S.markerCore7_BAUGC (.inl j))
    {i : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hi : i ∈ (actualSlotsV2_BAUGD S).stageCloud 0)
    (hwin : (closedBall i (80 * Ξ₀⁻¹ * DP.stageRadius 0 (Sg 0) i) ∩
      ball ((actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val))
        (8 * Ξ₀⁻¹ * DP.stageRadius 0 (Sg 0)
          ((actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val)))).Nonempty)
    (qi : W.pieceInterior ⊤)
    (hqi : (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap qi.val) = i) :
    S.circleCutoffW_BAUGD j qi.val = 1 := by
  have h := (DP.circle_spec.full_marker Ξ₀ (Sg 0) hΞ hsg hsgΞ (Classical.arbitrary _) (.inl j) rfl
    q hq7 i hi hwin).1
  rw [← hqi, stageProj_zero_V2_BAUGD S, S.markerCLM_boundaryOriginalMap_BAUGD] at h
  have hR := S.rho_pos (S.markerCentre_BAUGC (.inl j))
  have h2 : S.rho (S.markerCentre_BAUGC (.inl j)) * S.markerCutoffW_BAUGD (.inl j) qi.val =
      S.rho (S.markerCentre_BAUGC (.inl j)) * 1 := by rw [h, mul_one]
  exact mul_left_cancel₀ hR.ne' h2

/-- **(SC) the contributor scale at stage `0`**: for a point `q` of the circle chart `j` with
`‖η_j(q)‖ ≤ 13/2` (the `ψ₀` localization) and a window contributor `i ∈ S₀` of `x = π₀F_∂(q)`,
`|ℓ_ρ(i) − ρ(q)| ≤ 80/3 Λρ(q)` (both points in `B(j, 10ρ_j)` by TCP01; `ρ` is `Λ`-Lipschitz). -/
theorem circle_contributor_scale_BAUGD
    (DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg) (hΛ : 0 ≤ Λ)
    (hΔ1 : 1 ≤ Δ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (hV : 0 ≤ V) (hβ1 : 0 < β 1)
    (hb : 0 < b) {Ξ₀ : ℝ} (hΞ : 0 < Ξ₀) (hsg : 0 < Sg 0) (hsgΞ : Sg 0 ≤ Ξ₀ / 10000)
    (j : S.CircleIdx_BAUGD) (q : W.pieceInterior ⊤)
    (hqd : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 200 * S.rho j.1)
    (hqη : ‖S.circleEta_BIF j.1 q‖ ≤ 13 / 2)
    {i : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hi : i ∈ (actualSlotsV2_BAUGD S).stageCloud 0)
    (hwin : (closedBall i (80 * Ξ₀⁻¹ * DP.stageRadius 0 (Sg 0) i) ∩
      ball ((actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val))
        (8 * Ξ₀⁻¹ * DP.stageRadius 0 (Sg 0)
          ((actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val)))).Nonempty) :
    |S.scaleMarker_BIF i - S.rho q.val| ≤ 80 / 3 * Λ * S.rho q.val := by
  let _ := inducedMetricSpace S.completion.metric
  have hΔ : 0 < Δ := by linarith
  have hq7 : q ∈ S.markerCore7_BAUGC (.inl j) := ⟨hqd, hqη.trans (by norm_num)⟩
  have hjc : j.1 ∈ S.stageCentres_BIF 0 := (Set.Finite.mem_toFinset _).mp j.2
  have hqcore : q ∈ (actualSlotsV2_BAUGD S).stageCore 0 :=
    mem_actualSlotsV2_stageCore_circle_BAUGD S hjc hqd (hqη.trans (by norm_num))
  obtain ⟨qi, hqicore, hqi₀⟩ := hi
  have hqi : (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap qi.val) = i := hqi₀
  have hζi := circle_cutoff_one_of_window_BAUGD DP hΞ hsg.le hsgΞ j q hq7 ⟨qi, hqicore, hqi₀⟩
    hwin qi hqi
  have hζq : S.circleCutoffW_BAUGD j q.val = 1 :=
    S.markerCutoffW_eq_one_of_core7_BAUGD hΔ (.inl j) hq7
  have hci := S.circle_scale_comparable_BAUGD hΛ hΔ1 hΛΔ hV hβ1 hb j qi.val (by rw [hζi]; norm_num)
  have hcq := S.circle_scale_comparable_BAUGD hΛ hΔ1 hΛΔ hV hβ1 hb j q.val (by rw [hζq]; norm_num)
  have hri := (stageRadius_bounds_V2_BAUGD DP hsg.le hqicore).2
  rw [hqi] at hri
  have hrx := (stageRadius_bounds_V2_BAUGD DP hsg.le hqcore).2
  have hd := dist_le_of_window_BAUGD hwin
  have hw := window_arith_BAUGD hΞ hsg.le hsgΞ hri hrx hci.2 hcq.2 (S.rho_pos _).le
    (S.rho_pos _).le
  have hd2 := hd.trans hw
  rw [← hqi, stageProj_zero_V2_BAUGD S, stageProj_zero_V2_BAUGD S, dist_eq_norm] at hd2
  have hclose := S.circle_coord_close_BAUGD j hζi hζq
  have hρj := S.rho_pos j.1.val
  have hη : ‖S.circleCoordW_BAUGD j qi.val - S.circleCoordW_BAUGD j q.val‖ ≤ 1 / 50 := by
    have h1 : S.rho j.1 * ‖S.circleCoordW_BAUGD j qi.val - S.circleCoordW_BAUGD j q.val‖ ≤
        S.rho j.1 * (1 / 50) := by linarith
    exact le_of_mul_le_mul_left h1 hρj
  have hηq : ‖S.circleCoordW_BAUGD j q.val‖ ≤ 13 / 2 := by
    rw [← S.circleEta_eq_circleCoordW_BAUGD]; exact hqη
  have hηi : ‖S.circleCoordW_BAUGD j qi.val‖ ≤ 8 := by
    have := norm_le_insert' (S.circleCoordW_BAUGD j qi.val) (S.circleCoordW_BAUGD j q.val)
    linarith
  have hdi := S.circle_dist_lt_ten_BAUGD j qi
    (S.circle_dist_lt_of_cutoff_pos_BAUGD j qi (by rw [hζi]; norm_num)) hηi
  have hdq := S.circle_dist_lt_ten_BAUGD j q hqd (hηq.trans (by norm_num))
  have hli := S.rho_sub_le_circle_BAUGD hΛ hΔ hV hβ1 hb j qi
    (S.circle_dist_lt_of_cutoff_pos_BAUGD j qi (by rw [hζi]; norm_num))
  have hlq := S.rho_sub_le_circle_BAUGD hΛ hΔ hV hβ1 hb j q hqd
  have hℓ : S.scaleMarker_BIF i = S.rho qi.val := by
    rw [← hqi, stageProj_zero_V2_BAUGD S, S.scaleMarker_boundaryOriginalMap_BIF]
  rw [hℓ]
  have e1 : Λ * dist qi j.1 ≤ Λ * (10 * S.rho j.1) := mul_le_mul_of_nonneg_left hdi.le hΛ
  have e2 : Λ * dist q j.1 ≤ Λ * (10 * S.rho j.1) := mul_le_mul_of_nonneg_left hdq.le hΛ
  have e3 : Λ * (20 * S.rho j.1) ≤ 80 / 3 * Λ * S.rho q.val := by nlinarith [hcq.1]
  have h4 : |S.rho qi.val - S.rho q.val| ≤
      |S.rho qi.val - S.rho j.1.val| + |S.rho q.val - S.rho j.1.val| := by
    have := abs_sub_le (S.rho qi.val) (S.rho j.1.val) (S.rho q.val)
    rwa [abs_sub_comm (S.rho j.1.val) (S.rho q.val)] at this
  linarith

/-- `2c_wβ/r ≤ 800/9 (c_w/Σ)Λ` for `β = 80/3 Λρ`, `r ≥ 3/5 Σρ`. -/
theorem smv_const_le_BAUGD {cw₀ sg Λ' ρq r : ℝ} (hcw : 0 ≤ cw₀) (hsg : 0 < sg) (hΛ : 0 ≤ Λ')
    (hρ : 0 < ρq) (hr : 3 / 5 * (sg * ρq) ≤ r) :
    2 * cw₀ * (80 / 3 * Λ' * ρq) / r ≤ 800 / 9 * (cw₀ / sg) * Λ' := by
  have h0 : 0 < 3 / 5 * (sg * ρq) := by positivity
  have h1 : 2 * cw₀ * (80 / 3 * Λ' * ρq) / r ≤
      2 * cw₀ * (80 / 3 * Λ' * ρq) / (3 / 5 * (sg * ρq)) :=
    div_le_div_of_nonneg_left (by positivity) h0 hr
  have h2 : 2 * cw₀ * (80 / 3 * Λ' * ρq) / (3 / 5 * (sg * ρq)) = 800 / 9 * (cw₀ / sg) * Λ' := by
    field_simp
    ring
  linarith

/-- **CFS15's (SMV) at stage `0` on the boundary chain** (the scale marker is slow on the first
stage output): at a point `q` of the circle chart `j` with `‖η_j(q)‖ ≤ 13/2`, the stage-`0` map `a`
of ANY slot is differentiable at `F_∂ q`, `|ℓ_ρ(a(F_∂ q)) − ρ(q)| ≤ 80/3 Λρ(q)` and
`‖ℓ_ρ ∘ Da(F_∂ q)‖ ≤ 800/9 (c_w/Σ₀) Λ` (planes in `ker ℓ_ρ`: V3 `scale_zero`; contributors:
(SC)). -/
theorem scale_smv_zero_BAUGD
    (DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg) (hΛ : 0 ≤ Λ)
    (hΔ1 : 1 ≤ Δ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (hV : 0 ≤ V) (hβ1 : 0 < β 1)
    (hb : 0 < b) {Kj : ℕ} {Ξ₀ cw₀ : ℝ}
    (σ : BoundaryStageSlot_BIF DP.toBoundaryAugmentedData 0 Kj Ξ₀ (Sg 0) cw₀) (hΞ : 0 < Ξ₀)
    (hsg : 0 < Sg 0) (hsgΞ : Sg 0 ≤ Ξ₀ / 10000) (hcw : 0 ≤ cw₀)
    (j : S.CircleIdx_BAUGD) (q : W.pieceInterior ⊤)
    (hqd : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 200 * S.rho j.1)
    (hqη : ‖S.circleEta_BIF j.1 q‖ ≤ 13 / 2) :
    DifferentiableAt ℝ σ.map (S.boundaryOriginalMap q.val) ∧
      |S.scaleMarker_BIF (σ.map (S.boundaryOriginalMap q.val)) - S.rho q.val| ≤
        80 / 3 * Λ * S.rho q.val ∧
      ‖S.scaleMarker_BIF.comp (fderiv ℝ σ.map (S.boundaryOriginalMap q.val))‖ ≤
        800 / 9 * (cw₀ / Sg 0) * Λ := by
  have hjc : j.1 ∈ S.stageCentres_BIF 0 := (Set.Finite.mem_toFinset _).mp j.2
  have hqcore : q ∈ (actualSlotsV2_BAUGD S).stageCore 0 :=
    mem_actualSlotsV2_stageCore_circle_BAUGD S hjc hqd (hqη.trans (by norm_num))
  have hx : (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val) ∈
      (actualSlotsV2_BAUGD S).stageCloud 0 := ⟨q, hqcore, rfl⟩
  have hr := (stageRadius_bounds_V2_BAUGD DP hsg.le hqcore).1
  have hρ := S.rho_pos q.val
  have hrpos : 0 < DP.stageRadius 0 (Sg 0)
      ((actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val)) := by
    have : 0 < 3 / 5 * (Sg 0 * S.rho q.val) := by positivity
    linarith
  have hball := mem_ball_self (x := (actualSlotsV2_BAUGD S).stageProj 0
    (S.boundaryOriginalMap q.val)) hrpos
  have hdiff := (σ.map_contDiffAt_BAUGD hx hball).differentiableAt (by simp)
  rw [stageProj_zero_V2_BAUGD S] at hdiff
  refine ⟨hdiff, ?_⟩
  cases σ with
  | inactive hc _ =>
    exfalso
    rw [hc] at hqcore
    exact hqcore
  | active O =>
    have e := stageProj_zero_V2_BAUGD S (S.boundaryOriginalMap q.val)
    have hz : S.boundaryOriginalMap q.val ∈ ball ((actualSlotsV2_BAUGD S).stageProj 0
        (S.boundaryOriginalMap q.val)) (DP.stageRadius 0 (Sg 0)
          ((actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val))) := by
      rw [mem_ball]
      simpa only [e, dist_self] using hrpos
    have hsmv := O.smv_of_cloud_C15 hx S.scaleMarker_BIF
      (fun i hi _ => DP.circle_spec.scale_zero rfl i hi) (S.rho q.val) (80 / 3 * Λ * S.rho q.val)
      (fun i hi hw => circle_contributor_scale_BAUGD DP hΛ hΔ1 hΛΔ hV hβ1 hb hΞ hsg hsgΞ j q hqd
        hqη hi hw) _ hz
    exact ⟨hsmv.1, hsmv.2.trans (smv_const_le_BAUGD hcw hsg hΛ hρ hr)⟩

end Contributor

/-- The constant of A3f': `100 ≤ C_ρ = 100(b_der + 1)(1 + b_cut + X)` for nonnegative inputs. -/
theorem scaleEdp01Const_ge_BAUGD {bder bcut X : ℝ} (hd : 0 ≤ bder) (hc : 0 ≤ bcut) (hX : 0 ≤ X) :
    100 ≤ 100 * (bder + 1) * (1 + bcut + X) := by
  nlinarith [mul_nonneg hd hc, mul_nonneg hd hX]

/-- The arithmetic of A3f''s derivative bound:
`ΛG + (800/9 XΛ)(b_der G) + (b_cut/ρ)(b_der G)(80/3 Λρ) ≤ C_ρ ΛG`. -/
theorem scaleEdp01_arith_BAUGD {Λ' G bder bcut X ρq : ℝ} (hΛ : 0 ≤ Λ') (hG : 0 ≤ G)
    (hd : 0 ≤ bder) (hc : 0 ≤ bcut) (hX : 0 ≤ X) (hρ : 0 < ρq) :
    Λ' * G + 800 / 9 * X * Λ' * (bder * G) + bcut / ρq * (bder * G) * (80 / 3 * Λ' * ρq) ≤
      100 * (bder + 1) * (1 + bcut + X) * Λ' * G := by
  have e : bcut / ρq * (bder * G) * (80 / 3 * Λ' * ρq) = 80 / 3 * bcut * bder * (Λ' * G) := by
    field_simp
  have key : 1 + 800 / 9 * X * bder + 80 / 3 * bcut * bder ≤
      100 * (bder + 1) * (1 + bcut + X) := by
    nlinarith [mul_nonneg hd hc, mul_nonneg hd hX]
  have hΛG := mul_nonneg hΛ hG
  have h2 := mul_le_mul_of_nonneg_right key hΛG
  rw [e]
  nlinarith

namespace BoundaryGaf02Chain

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  (C : BoundaryGaf02Chain DP.toBoundaryAugmentedData Kj Ξ Sg eg c cw bcut bder κ)

/-- **The scale is the first blend of `ρ`** (EDP01, `π₀ = id`): `s = φ ∘ F_∂` with
`φ(z) = ℓ_ρ z + ψ₀ z (ℓ_ρ(a₀ z) − ℓ_ρ z)`. -/
theorem scale_eq_blend_V2_BAUGD :
    C.scale = (fun z => S.scaleMarker_BIF z + (actualSlotsV2_BAUGD S).cutoff 0 z *
      (S.scaleMarker_BIF ((C.slot 0).map z) - S.scaleMarker_BIF z)) ∘ S.boundaryOriginalMap := by
  funext p
  rw [Function.comp_apply, C.scale_eq_g₁_V2_BAUGD, C.g₁_apply_V2_BAUGD,
    scaleMarker_adjust_zero_V2_BAUGD]

/-- Off `tsupport ψ₀` the blend is `ℓ_ρ` near the point. -/
theorem scaleBlend_eq_of_notMem_BAUGD
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hy : y ∉ tsupport ((actualSlotsV2_BAUGD S).cutoff 0)) :
    (fun z => S.scaleMarker_BIF z + (actualSlotsV2_BAUGD S).cutoff 0 z *
      (S.scaleMarker_BIF ((C.slot 0).map z) - S.scaleMarker_BIF z)) =ᶠ[𝓝 y]
      S.scaleMarker_BIF := by
  filter_upwards [(isClosed_tsupport _).isOpen_compl.mem_nhds hy] with z hz
  rw [image_eq_zero_of_notMem_tsupport hz, zero_mul, add_zero]

end BoundaryGaf02Chain

/-- `ℓ_ρ ∘ DF_∂ = dρ`, hence `|ℓ_ρ(DF_∂ v)| ≤ Λ|v|_g` (`ρ` is `Λ`-Lipschitz for `g`). -/
theorem abs_scaleMarker_mvfderiv_le_BAUGD {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε
    γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g δn n B oM} (hΛ : 0 ≤ Λ) (p : W.Carrier)
    (hF : MDifferentiableAt W.model
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) S.boundaryOriginalMap p)
    (v : TangentSpace W.model p) :
    |S.scaleMarker_BIF (mvfderiv W.model S.boundaryOriginalMap p v)| ≤
      Λ * Real.sqrt (g.inner p v v) := by
  have e : S.rho = S.scaleMarker_BIF ∘ S.boundaryOriginalMap :=
    funext fun p => (S.scaleMarker_boundaryOriginalMap_BIF p).symm
  have h1 := mvfderiv_comp_apply_of_differentiableAt_GAF3 hF
    S.scaleMarker_BIF.differentiableAt v
  rw [← e, ContinuousLinearMap.fderiv] at h1
  rw [← h1]
  exact abs_mvfderiv_le_of_lipschitz_riemannianEDistOf_BDFB g
    ((S.scale_spec.1 p).of_le (by exact_mod_cast le_top)) hΛ Filter.univ_mem
    (fun x _ y _ => S.scale_spec.2.1 x y) v

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

include C in
/-- `F_∂` is differentiable at every point (A3a at `k = 0`). -/
theorem mdifferentiableAt_boundaryOriginalMap_BAUGD (p : W.Carrier) :
    MDifferentiableAt W.model 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
      S.boundaryOriginalMap p :=
  ((C.stage_smooth_BAUGD 0) p).mdifferentiableAt (by simp)

/-- **A3f' on `tsupport ψ₀`** (the SMV branch): the blend is differentiable at `F_∂ p`, the value
error is `≤ 80/3 Λρ` and the derivative is `≤ C_ρΛ|v|_g`. -/
theorem scale_edp01_support_BAUGD {p : W.Carrier}
    (hy : S.boundaryOriginalMap p ∈ tsupport ((actualSlotsV2_BAUGD S).cutoff 0)) :
    DifferentiableAt ℝ (fun z => S.scaleMarker_BIF z + (actualSlotsV2_BAUGD S).cutoff 0 z *
        (S.scaleMarker_BIF ((C.toChain.slot 0).map z) - S.scaleMarker_BIF z))
        (S.boundaryOriginalMap p) ∧
      |C.toChain.scale p - S.rho p| ≤ 80 / 3 * Λ * S.rho p ∧
      ∀ v : TangentSpace W.model p, |mvfderiv W.model C.toChain.scale p v| ≤
        100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Real.sqrt (g.inner p v v) := by
  obtain ⟨hΛ, -, -, -, -, hV, hβ1, hb, -, hΔ1, hΛΔ, -⟩ := C.std
  have hN := C.toChain.numbers
  have hΞ0 : 0 < Ξ 0 := (hN.1 0).1
  have hsg : 0 < Sg 0 := (hN.1 0).2.1
  have hsgΞ : Sg 0 ≤ Ξ 0 / 10000 := (hN.1 0).2.2.2.2.1
  have hcw : 0 ≤ cw 0 := (hN.1 0).2.2.2.2.2
  have hbder := C.bder_nonneg_BAUGD p
  have hbcut := C.bcut_nonneg_BAUGD p
  have hF := C.mdifferentiableAt_boundaryOriginalMap_BAUGD p
  obtain ⟨q, rfl, j, hj, hd, hη⟩ := C.toChain.cutoff_bindings.1.2.2.2.1 p hy
  obtain ⟨hda, hval, hder⟩ := scale_smv_zero_BAUGD DP hΛ hΔ1 hΛΔ hV hβ1 hb (C.toChain.slot 0)
    hΞ0 hsg hsgΞ hcw ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩ q hd hη
  have hψ := C.toChain.cutoff_deriv_zero_V2_BAUGD q.val
  have hψI := C.toChain.cutoff_bindings.1.2.1 (S.boundaryOriginalMap q.val)
  obtain ⟨hφd, hφD⟩ := scaleBlend_hasFDerivAt_BAUGD S.scaleMarker_BIF (C.toChain.slot 0).map
    ((actualSlotsV2_BAUGD S).cutoff 0) hda hψ.1
  have hρ := S.rho_pos q.val
  have hℓ := S.scaleMarker_boundaryOriginalMap_BIF q.val
  have hs := C.toChain.scale_eq_blend_V2_BAUGD
  refine ⟨hφd, ?_, fun v => ?_⟩
  · rw [hs, Function.comp_apply, hℓ, add_sub_cancel_left, abs_mul,
      abs_of_nonneg hψI.1]
    have h1 := mul_le_mul hψI.2 hval (abs_nonneg _) zero_le_one
    linarith
  · rw [hs, mvfderiv_comp_apply_of_differentiableAt_GAF3 hF hφd v, hφD]
    have hG := Real.sqrt_nonneg (g.inner q.val v v)
    have hwN : ‖mvfderiv W.model S.boundaryOriginalMap q.val v‖ ≤
        bder * Real.sqrt (g.inner q.val v v) := C.deriv_bound q.val v
    have hLa : |S.scaleMarker_BIF (fderiv ℝ (C.toChain.slot 0).map (S.boundaryOriginalMap q.val)
          (mvfderiv W.model S.boundaryOriginalMap q.val v))| ≤
        800 / 9 * (cw 0 / Sg 0) * Λ * (bder * Real.sqrt (g.inner q.val v v)) := by
      have h1 : |(S.scaleMarker_BIF.comp (fderiv ℝ (C.toChain.slot 0).map
          (S.boundaryOriginalMap q.val)))
          (mvfderiv W.model S.boundaryOriginalMap q.val v)| ≤
          ‖S.scaleMarker_BIF.comp (fderiv ℝ (C.toChain.slot 0).map
            (S.boundaryOriginalMap q.val))‖ *
            ‖mvfderiv W.model S.boundaryOriginalMap q.val v‖ := by
        rw [← Real.norm_eq_abs]
        exact ContinuousLinearMap.le_opNorm _ _
      exact h1.trans (mul_le_mul hder hwN (norm_nonneg _) (by positivity))
    have hDψ : |fderiv ℝ ((actualSlotsV2_BAUGD S).cutoff 0) (S.boundaryOriginalMap q.val)
        (mvfderiv W.model S.boundaryOriginalMap q.val v)| ≤
        bcut / S.rho q.val * (bder * Real.sqrt (g.inner q.val v v)) := by
      rw [← Real.norm_eq_abs]
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul hψ.2 hwN (norm_nonneg _) (by positivity))
    have hval' : |S.scaleMarker_BIF ((C.toChain.slot 0).map (S.boundaryOriginalMap q.val)) -
        S.scaleMarker_BIF (S.boundaryOriginalMap q.val)| ≤ 80 / 3 * Λ * S.rho q.val :=
      (congrArg (fun t => |S.scaleMarker_BIF ((C.toChain.slot 0).map
        (S.boundaryOriginalMap q.val)) - t|) hℓ).trans_le hval
    have hb := scaleBlend_deriv_le_BAUGD hψI (abs_scaleMarker_mvfderiv_le_BAUGD hΛ q.val hF v)
      hLa hDψ hval'
    exact hb.trans (scaleEdp01_arith_BAUGD hΛ hG hbder hbcut (div_nonneg hcw hsg.le) hρ)

/-- **A3f' off `tsupport ψ₀`**: `s = ρ` near the point. -/
theorem scale_edp01_off_BAUGD {p : W.Carrier}
    (hy : S.boundaryOriginalMap p ∉ tsupport ((actualSlotsV2_BAUGD S).cutoff 0)) :
    DifferentiableAt ℝ (fun z => S.scaleMarker_BIF z + (actualSlotsV2_BAUGD S).cutoff 0 z *
        (S.scaleMarker_BIF ((C.toChain.slot 0).map z) - S.scaleMarker_BIF z))
        (S.boundaryOriginalMap p) ∧
      C.toChain.scale p = S.rho p ∧
      ∀ v : TangentSpace W.model p, |mvfderiv W.model C.toChain.scale p v| ≤
        Λ * Real.sqrt (g.inner p v v) := by
  have hΛ : 0 ≤ Λ := C.std.1
  have hev := C.toChain.scaleBlend_eq_of_notMem_BAUGD hy
  have hφd := S.scaleMarker_BIF.differentiableAt.congr_of_eventuallyEq hev
  have hF := C.mdifferentiableAt_boundaryOriginalMap_BAUGD p
  have hs := C.toChain.scale_eq_blend_V2_BAUGD
  refine ⟨hφd, ?_, fun v => ?_⟩
  · rw [hs, Function.comp_apply, hev.eq_of_nhds, S.scaleMarker_boundaryOriginalMap_BIF]
  · rw [hs, mvfderiv_comp_apply_of_differentiableAt_GAF3 hF hφd v, hev.fderiv_eq,
      ContinuousLinearMap.fderiv]
    exact abs_scaleMarker_mvfderiv_le_BAUGD hΛ p hF v

/-- **A3f' the EDP01-type EARLY scale exit** (review 69 §1.7, D69-5 (4); closed
`Gaf02Chain.edp01_GAF8`), target `scale_edp01_BAUGD` of `TargetsBoundary-A-v3.1`:
`C_ρ = 100(b_der + 1)(1 + b_cut + c_w(0)/Σ₀) ≥ 100`, and at every point `s` is differentiable,
`|s − ρ| ≤ C_ρΛρ`, `|ds(v)| ≤ C_ρΛ|v|_g`, `s > 0`. -/
theorem scale_edp01_BAUGD :
    100 ≤ 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) ∧
    ∀ p : W.Carrier, MDifferentiableAt W.model 𝓘(ℝ, ℝ) C.toChain.scale p ∧
      |C.toChain.scale p - S.rho p| ≤ 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * S.rho p ∧
      (∀ v : TangentSpace W.model p, |mvfderiv W.model C.toChain.scale p v| ≤
        100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Real.sqrt (g.inner p v v)) ∧
      0 < C.toChain.scale p := by
  have hN := C.toChain.numbers
  have hsg : 0 < Sg 0 := (hN.1 0).2.1
  have hcw : 0 ≤ cw 0 := (hN.1 0).2.2.2.2.2
  have hΛ : 0 ≤ Λ := C.std.1
  have p₀ : W.Carrier := Classical.arbitrary _
  have h100 := scaleEdp01Const_ge_BAUGD (C.bder_nonneg_BAUGD p₀) (C.bcut_nonneg_BAUGD p₀)
    (div_nonneg hcw hsg.le)
  refine ⟨h100, fun p => ?_⟩
  have hF := C.mdifferentiableAt_boundaryOriginalMap_BAUGD p
  have hs := C.toChain.scale_eq_blend_V2_BAUGD
  have hρ := S.rho_pos p
  have hΛρ : 0 ≤ Λ * S.rho p := mul_nonneg hΛ hρ.le
  have hpos := (C.scale_pos_BAUGD p).2.2
  by_cases hy : S.boundaryOriginalMap p ∈ tsupport ((actualSlotsV2_BAUGD S).cutoff 0)
  · obtain ⟨hφd, hval, hder⟩ := C.scale_edp01_support_BAUGD hy
    refine ⟨?_, ?_, hder, hpos⟩
    · rw [hs]; exact hφd.comp_mdifferentiableAt hF
    · have : 80 / 3 * Λ * S.rho p ≤ 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * S.rho p := by
        nlinarith
      linarith
  · obtain ⟨hφd, hval, hder⟩ := C.scale_edp01_off_BAUGD hy
    refine ⟨?_, ?_, fun v => ?_, hpos⟩
    · rw [hs]; exact hφd.comp_mdifferentiableAt hF
    · rw [hval, sub_self, abs_zero]
      nlinarith
    · have hG := Real.sqrt_nonneg (g.inner p v v)
      have := mul_nonneg hΛ hG
      have h2 : Λ * Real.sqrt (g.inner p v v) ≤
          100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Real.sqrt (g.inner p v v) := by
        nlinarith
      exact (hder v).trans h2

end BoundaryGaf02ChainE

section Consumer

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

/-- Consumer: the A-v3.1 frozen statement of A3f' VERBATIM (section form of the text). -/
example (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj) :
    100 ≤ 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) ∧
    ∀ p : W.Carrier, MDifferentiableAt W.model 𝓘(ℝ, ℝ) C.toChain.scale p ∧
      |C.toChain.scale p - S.rho p| ≤ 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * S.rho p ∧
      (∀ v : TangentSpace W.model p, |mvfderiv W.model C.toChain.scale p v| ≤
        100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Real.sqrt (g.inner p v v)) ∧
      0 < C.toChain.scale p :=
  C.scale_edp01_BAUGD

/-- Consumer: the slow scale gives the relative error `|s/ρ − 1| ≤ C_ρΛ` at every point. -/
theorem BoundaryGaf02ChainE.abs_scale_div_rho_sub_one_le_BAUGD
    (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj) (p : W.Carrier) :
    |C.toChain.scale p / S.rho p - 1| ≤ 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ := by
  have hρ := S.rho_pos p
  have h := (C.scale_edp01_BAUGD.2 p).2.1
  have e : C.toChain.scale p / S.rho p - 1 = (C.toChain.scale p - S.rho p) / S.rho p := by
    field_simp
  rw [e, abs_div, abs_of_pos hρ, div_le_iff₀ hρ]
  exact h

end Consumer

end DifferentialGeometry.Geometry.Collapse
