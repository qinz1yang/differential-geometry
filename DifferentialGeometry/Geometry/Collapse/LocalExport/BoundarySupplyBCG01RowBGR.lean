import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySupplyBCG01BGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryOriginalDerivativeBDFB

/-!
# BCG01, the whole row on the stored boundary supply (lane B-BCG-ROWS)

Blueprint `master207B.tex`, BCG01 (B:8727–8821): G4's `bcg01_row_BGR` (clauses (a)–(c) at every
reference domain, (d) smooth blocks, (e) the four-family cover of `{D ≥ 35}`, (f) the revised edge
domains in `{D > 10}`) together with the derivative clause of (d), `‖DF_∂ v‖ ≤ bder₀ |v|_g` on ALL
of `W` in the original metric, `bder₀ = boundaryDerivBound_BDFB = 1000(N_TCP + 2)P₀² + 2P_B`
(lane B-DFB's `BoundarySupplyCore.norm_mvfderiv_boundaryOriginalMap_le_BDFB`).

* **`BoundarySupplyCore.bcg01_whole_row_BGR`** (separated branch of T3B as input `hsep`);
* **`BoundarySupply.bcg01_whole_row_BGR`** (the stored supply in its own non-product branch,
  through `geometric_cases_BIF`).

Premises: the register clauses of both halves, minimized (`100ΔΛ ≤ 1/100`, `e ≤ 1/10`, `0 ≤ Λ`,
`0 < Δ` are derived from `10⁶ΔΛ < 10⁻⁵`, `e < 1/40`, `0 < Λ`, `1 ≤ Δ`).
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

/-- **BCG01, the whole row** (blueprint B:8727–8821) on the stored supply in the separated branch:
(a)–(f) of `bcg01_row_BGR` and the derivative clause `‖DF_∂ v‖ ≤ bder₀ |v|_g` at every point of
`W` (boundary included), `bder₀ = boundaryDerivBound_BDFB`. -/
theorem bcg01_whole_row_BGR (hsep : S.SeparatedCollarZero_BIF) (hΛ : 0 < Λ) (hΔ : 1 ≤ Δ)
    (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b)
    (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (hreq : β 1 ^ 3 * (1000000 * Δ) < 1)
    (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax) (he40 : e < 1 / 40)
    (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : σs ∈ Icc (0 : ℝ) 1) (hσc : σc ∈ Icc (0 : ℝ) 1)
    (hγc : γc ∈ Icc (0 : ℝ) 1) (hεr : εr ∈ Icc (0 : ℝ) 1) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    letI := S.family.instMetricN
    letI := S.family.instChartedN
    letI := S.family.instMetricC
    ((∀ (p : W.Carrier) (C : ℝ), C ≤ 95 / 100 * (1000000 * Δ) →
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
            (inv_pos.mpr (S.rho_pos x))) x 3 (β 3)) ∧
    ∀ (p : W.Carrier) (v : TangentSpace W.model p),
      ‖mvfderiv W.model S.boundaryOriginalMap p v‖ ≤
        boundaryDerivBound_BDFB * Real.sqrt (g.inner p v v) := by
  have hΔΛ : 100 * Δ * Λ ≤ 1 / 100 := by nlinarith
  refine ⟨S.bcg01_row_BGR hsep hΛ hΔ hβ1 hΛΔ hreq, fun p v => ?_⟩
  exact S.norm_mvfderiv_boundaryOriginalMap_le_BDFB hΛ.le (by linarith) hμ hτ hΔΛ hV hβ1 hb
    (by linarith) hΔ hΛΔ hLmax he40 hT hσs hσc hγc hεr hsep p v

end BoundarySupplyCore

/-- **BCG01, the whole row on the stored supply** in its own non-product branch
(`geometric_cases_BIF` of T3B gives the separated branch). -/
theorem BoundarySupply.bcg01_whole_row_BGR
    (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ
      W g δn n B oM)
    (hsep : ¬ S.toBoundarySupplyCore.LabelledWholeProduct_BIF) (hΛ : 0 < Λ) (hΔ : 1 ≤ Δ)
    (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b)
    (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (hreq : β 1 ^ 3 * (1000000 * Δ) < 1)
    (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax) (he40 : e < 1 / 40)
    (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : σs ∈ Icc (0 : ℝ) 1) (hσc : σc ∈ Icc (0 : ℝ) 1)
    (hγc : γc ∈ Icc (0 : ℝ) 1) (hεr : εr ∈ Icc (0 : ℝ) 1) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    letI := S.family.instMetricN
    letI := S.family.instChartedN
    letI := S.family.instMetricC
    ((∀ (p : W.Carrier) (C : ℝ), C ≤ 95 / 100 * (1000000 * Δ) →
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
            (inv_pos.mpr (S.rho_pos x))) x 3 (β 3)) ∧
    ∀ (p : W.Carrier) (v : TangentSpace W.model p),
      ‖mvfderiv W.model S.boundaryOriginalMap p v‖ ≤
        boundaryDerivBound_BDFB * Real.sqrt (g.inner p v v) := by
  have hs := S.toBoundarySupplyCore.geometric_cases_BIF.resolve_left hsep
  exact S.toBoundarySupplyCore.bcg01_whole_row_BGR hs hΛ hΔ hμ hτ hV hβ1 hb hΛΔ hreq hLmax he40 hT
    hσs hσc hγc hεr

end DifferentialGeometry.Geometry.Collapse
