import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRigidityContributorBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeCollarExitsBC7C
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPacketsBFApplications

/-!
# BCG01 on the stored boundary supply (lane B-BCG-ROWS)

Blueprint `master207B.tex`, BCG01 (B:8727–8820, "whole boundary support lists and their original
domains"), on ONE `S : BoundarySupplyCore` (the stored T3B supply: packet, scale, completion and
the final family `LocalPacketsOnBFRZ`), in BCP03's nonproduct case (`S.SeparatedCollarZero_BIF`),
with the physical scale `r_∂ = β₁³/1000` of the stored collar smallness `ρ ≤ β₁³/2000`, `L = 10⁶Δ`,
BCG01's request `r_∂ < 1/(1000L)` (`β₁³·10⁶Δ < 1`) and the unified register clause
`10⁶ΔΛ < 10⁻⁵`, `1 ≤ Δ`, `0 < Λ`.

**`BoundarySupplyCore.bcg01_row_BGR`**: for every reference domain `D = B_g(p, Cρ(p))`, `C ≤ .95L`:
(a) at most ONE closed boundary support meets `D`; (b) if the `b`th does, `ρ(p) < 2r_∂` and
`D ⊂ e_b{19 < z < 91} ∩ {19 < η_b < 91}` (the SAME height `η_b`); (c) then no selected zero ball
meets `D`; (d) every boundary block is smooth on the whole carrier; (e) the revised edge selection
gives the four-family cover on `D ≥ 35`; (f) every selected edge packet's radius-`100Δρ_j` domain
lies in `D > 10` and has no `3`-splitting (BCG7-COLLAR exit 1; exits 2–3, the LFR38 circle-collar
cover, are `LocalPacketsOnBFRZ.edgeB_collar_{twoStratum,coveredByCircle}_BC7C` on the SAME
`S.family`). The three stage reference domains (`C_a = 10, 20Δ, 950000Δ`) are instances
(`bcg01_stage_lists_BGR`). The derivative bound `‖DF‖ ≤ 1000(N+2)P²` is lane B-DFB's.
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

namespace BoundarySupplyCore

variable (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
  ζ Λz W g δn n B oM)

/-- The unified register clause gives BCG-8b's `100ΔΛ ≤ 10⁻⁶`. -/
theorem hundred_delta_lambda_le_BGR (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) :
    100 * Δ * Λ ≤ 1 / 1000000 := by
  linarith

/-- **BCG01 (a)–(c) at one reference domain** `D = B_g(p, Cρ(p))`, `C ≤ .95L`, in the nonproduct
case: the whole boundary support list is a subsingleton; a member `b` has `ρ(p) < 2r_∂ = β₁³/500`,
`D ⊂ e_b{19 < z < 91} ∩ {19 < η_b < 91}`, and `D` misses every selected zero ball. -/
theorem bcg01_reference_domain_BGR (hsep : S.SeparatedCollarZero_BIF) (hΛ : 0 < Λ) (hΔ : 1 ≤ Δ)
    (hβ1 : 0 < β 1) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (hreq : β 1 ^ 3 * (1000000 * Δ) < 1)
    (p : W.Carrier) {C : ℝ} (hC : C ≤ 95 / 100 * (1000000 * Δ)) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    letI := S.family.instMetricN
    letI := S.family.instChartedN
    letI := S.family.instMetricC
    (S.packet.toBoundaryCollarPacket.boundarySupportList_BCG8b p (C * S.rho p)).Subsingleton ∧
      ∀ i ∈ S.packet.toBoundaryCollarPacket.boundarySupportList_BCG8b p (C * S.rho p),
        S.rho p < β 1 ^ 3 / 500 ∧
        (∀ y ∈ riemannianBallOf g p (C * S.rho p), ∃ q ∈ cuspDomain,
          (S.packet.toBoundaryCollarPacket.cusp.collar i).toFun q = y ∧ 19 < q.2.val 0 ∧
            q.2.val 0 < 91 ∧ 19 < S.packet.toBoundaryCollarPacket.height i y ∧
            S.packet.toBoundaryCollarPacket.height i y < 91) ∧
        ∀ z (hz : z ∈ S.family.zero.centres),
          Disjoint (riemannianBallOf g p (C * S.rho p))
            (riemannianBallOf g z.val (S.family.zero.zero z hz).radius) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  have hε : cuspTolerance_BCUSP1 (β 1) βd εN ≤ 1 / 4 :=
    (cuspTolerance_le_thousandth_BCUSP1 _ _ _).trans (by norm_num)
  have hΔ0 : 0 < Δ := by linarith
  have hΛΔ' := hundred_delta_lambda_le_BGR (Δ := Δ) (Λ := Λ) hΛΔ
  have hdisj : ∀ i j : Fin S.packet.toBoundaryCollarPacket.cusp.count, i ≠ j →
      Disjoint ((S.packet.toBoundaryCollarPacket.cusp.collar i).toFun ''
          {q : CuspHalfSpace | q.2.val 0 < 92})
        ((S.packet.toBoundaryCollarPacket.cusp.collar j).toFun ''
          {q : CuspHalfSpace | q.2.val 0 < 92}) := fun i j hij => (hsep.1 i j hij).1
  refine ⟨S.packet.toBoundaryCollarPacket.boundarySupportList_subsingleton_BCG8b hε hdisj
      S.rho_pos hΛ hΔ0 hβ1 S.scale_spec.2.1 S.scale_spec.2.2.2.1 hΛΔ' hreq hC p,
    fun i hi => ?_⟩
  have h := S.packet.toBoundaryCollarPacket.bcg03_mem_boundarySupportList_BCG8b hε S.rho_pos hΛ
    hΔ0 hβ1 S.scale_spec.2.1 S.scale_spec.2.2.2.1 hΛΔ' hreq hC
    (fun z : {z // z ∈ S.family.zero.centres} => z.1.val)
    (fun z => (S.family.zero.zero z.1 z.2).radius) (fun z i => hsep.2.1 z.1 z.2 i) hi
  exact ⟨h.1, h.2.1, fun z hz => h.2.2 ⟨z, hz⟩⟩

/-- **BCG01 (a)–(c) at the three stage reference domains** `D_a = B_g(a, C_aρ(a))`,
`C_a = 10, 20Δ, 950000Δ` (BIFACE's `boundaryList_BIF`): `J_∂(a)` is a subsingleton and a member has
`ρ(a) < 2r_∂`. -/
theorem bcg01_stage_lists_BGR (hsep : S.SeparatedCollarZero_BIF) (hΛ : 0 < Λ) (hΔ : 1 ≤ Δ)
    (hβ1 : 0 < β 1) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (hreq : β 1 ^ 3 * (1000000 * Δ) < 1)
    (st : Fin 3) (a : W.Carrier) :
    (S.packet.toBoundaryCollarPacket.boundarySupportList_BCG8b a
        (stageDomain_BIF Δ st * S.rho a)).Subsingleton ∧
      ∀ i ∈ S.packet.toBoundaryCollarPacket.boundarySupportList_BCG8b a
        (stageDomain_BIF Δ st * S.rho a), S.rho a < β 1 ^ 3 / 500 := by
  have hC : stageDomain_BIF Δ st ≤ 95 / 100 * (1000000 * Δ) := by
    fin_cases st <;> simp [stageDomain_BIF] <;> nlinarith
  obtain ⟨h1, h2⟩ := S.bcg01_reference_domain_BGR hsep hΛ hΔ hβ1 hΛΔ hreq a hC
  exact ⟨h1, fun i hi => (h2 i hi).1⟩

/-- **BCG01 on the stored supply** (all clauses except `‖DF‖ ≤ 1000(N+2)P²`, lane B-DFB): (a)–(c)
at every reference domain `B_g(p, Cρ(p))`, `C ≤ .95L`; (d) the boundary blocks are smooth on `W`;
(e) the four-family cover of `{D ≥ 35}` by the revised edge selection; (f) every revised edge
centre is in `{D > 20}` and its whole radius-`100Δρ_j` domain lies in `{D > 10}` without a
`3`-splitting. -/
theorem bcg01_row_BGR (hsep : S.SeparatedCollarZero_BIF) (hΛ : 0 < Λ) (hΔ : 1 ≤ Δ)
    (hβ1 : 0 < β 1) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (hreq : β 1 ^ 3 * (1000000 * Δ) < 1) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    letI := S.family.instMetricN
    letI := S.family.instChartedN
    letI := S.family.instMetricC
    (∀ (p : W.Carrier) (C : ℝ), C ≤ 95 / 100 * (1000000 * Δ) →
      (S.packet.toBoundaryCollarPacket.boundarySupportList_BCG8b p (C * S.rho p)).Subsingleton ∧
      ∀ i ∈ S.packet.toBoundaryCollarPacket.boundarySupportList_BCG8b p (C * S.rho p),
        S.rho p < β 1 ^ 3 / 500 ∧
        (∀ y ∈ riemannianBallOf g p (C * S.rho p), ∃ q ∈ cuspDomain,
          (S.packet.toBoundaryCollarPacket.cusp.collar i).toFun q = y ∧ 19 < q.2.val 0 ∧
            q.2.val 0 < 91 ∧ 19 < S.packet.toBoundaryCollarPacket.height i y ∧
            S.packet.toBoundaryCollarPacket.height i y < 91) ∧
        ∀ z (hz : z ∈ S.family.zero.centres),
          Disjoint (riemannianBallOf g p (C * S.rho p))
            (riemannianBallOf g z.val (S.family.zero.zero z hz).radius)) ∧
    (∀ i, ContMDiff W.model 𝓘(ℝ, ℝ × ℝ) ∞ (S.packet.toBoundaryCollarPacket.block i)) ∧
    (∀ x : W.pieceInterior ⊤, ENNReal.ofReal 35 ≤ distanceToBoundary W g x →
      (∃ c, ∃ hc : c ∈ S.family.zero.centres,
          x ∈ ball c ((S.family.zero.zero c hc).radius / 10)) ∨
        (∃ j ∈ S.family.circle.centres, x ∈ ball j (2 * S.rho j)) ∨
        (∃ j ∈ S.family.slim.centres, x ∈ ball j (2 * (Δ * S.rho j))) ∨
        ∃ j ∈ S.family.edgeB.centres, dist x j < 2 * Δ * S.rho j) ∧
    ∀ j ∈ S.family.edgeB.centres,
      j ∈ {x : W.pieceInterior ⊤ | ENNReal.ofReal 20 < distanceToBoundary W g x} ∧
      ∀ x, dist x j < 100 * Δ * S.rho j →
        x ∈ {x : W.pieceInterior ⊤ | ENNReal.ofReal 10 < distanceToBoundary W g x} ∧
        ¬ @HasEuclideanSplitting.{0, 0} (W.pieceInterior ⊤)
          ((inducedMetricSpace S.completion.metric).rescale (S.rho x)⁻¹
            (inv_pos.mpr (S.rho_pos x))) x 3 (β 3) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  refine ⟨fun p C hC => S.bcg01_reference_domain_BGR hsep hΛ hΔ hβ1 hΛΔ hreq p hC,
    fun i => S.packet.toBoundaryCollarPacket.contMDiff_block i, fun x hx => ?_,
    fun j hj => S.family.edgeB_collar_eligible_BC7C hj⟩
  have hU : {x : W.pieceInterior ⊤ | ENNReal.ofReal 35 ≤ distanceToBoundary W g x} ⊆
      {x : W.pieceInterior ⊤ | ENNReal.ofReal 10 < distanceToBoundary W g x} := fun y hy =>
    lt_of_lt_of_le (ENNReal.ofReal_lt_ofReal_iff (by norm_num) |>.mpr (by norm_num)) hy
  exact S.family.toLocalPacketsOnBFR.toLocalPacketsOnBF.bcg01_cover_BCG3 hU x hx

end BoundarySupplyCore

end DifferentialGeometry.Geometry.Collapse
