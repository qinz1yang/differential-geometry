import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPacketsBFApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeightCircleBinding
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeightEdgeBinding
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeightSlimDifferential

/-!
# BCG02's joint (BA) clauses on GIVEN boundary data (lane BCG2-BIND, G1; review 64 D64-6)

`lc88_boundary_values_differential_BFR_BCG8` proves BCG02's three joint clauses (value AND
differential, ONE unit row / ONE sign per reference and boundary label, whole comparison domain,
`U_b = (η_b − η_b(j))/ρ(j)`, differential in `ρ(j)⁻²ĝ`) only for the family that its own call of
T3B chooses. `bcg02_joint_BA_of_data_BIND` extracts its end assembly as a FUNCTION of the data: for
a GIVEN collar packet `P`, scale `ρ`, completion `ĝ` and family `F : LocalPacketsOnBFR …` with the
certificates below, the three clauses hold for THAT `F` — circle references `F.circle` (radius
`10ρ(j)`), revised edge references `F.edgeB` (`20Δρ(j)`), slim references `F.slim` (`950000Δρ(j)`).
Applied to `F_Z.forgetBFR_BFZD` it gives (BA) on the projection of a fixed final family (G2).

The thresholds are chosen in BCG8's order: `σ_C, η_C` from `θ, ν` (circle); `σ_E, η_E, σ_S, η_S`
from `θ, ν, Δ` and the slim splitting quality `ν_S` (BCG8 uses `ν_S = β₂/3`).

Inputs, exactly those BCG8's three per-carrier calls consume (the redundant ones are derived here):

* certificates of the data (T3B's tail): `1 ≤ K`; `0 ≤ Λ` and `ρ` `Λ`-Lipschitz for `d_g`; the
  collar smallness `ρ ≤ β₁³/2000` on `z ≤ 96`; `ĝ = g°` on `{D ≥ 4}`; BCP04.a at the index `n`; B5's
  physical-scale bound `2ρ(12·10⁶Δ + 1000) < θ²/10⁸` on `z ≤ 96`; completeness of `(W°, d_ĝ)`;
  `U₁ ⊆ {D > 5}`. T3B's B3, B4 (norm, Hessian, Taylor) and late `ρ` certificate are NOT inputs: the
  per-carrier bindings read B4 from the collar packet `P` itself;
* the tail index and the packet tolerances: `32η⁻¹ ≤ n` for the three `η`, `32·10⁶Δ ≤ n`;
  `w₀, ε_B ≤ β₁²/1000` and `≤ θ²/(4·10⁷)`;
* BCG8's parameter requests: `950000ΔΛ ≤ 1/2`; `0 < β₁`, `2β₁ ≤ η_C, η_E, η_S`, `10⁶Δβ₁³ < 1`,
  `3β₁ ≤ σ_S`, `β₁(2(1950002Δ + 1)) ≤ 1`, `β₁ ≤ θ²/10⁷`; `3β₂ ≤ σ_C`, `β₂ ≤ θ²/10⁷`, `3ν_S ≤ β₂`;
  `3ν ≤ β₃ < 1`; `σ⁻¹ ≤ L_max` for the three `σ`; `γ ≤ θ²/10⁷`; `3b ≤ σ_E`, `b(2(421Δ + 1)) ≤ 1`,
  `b ≤ θ²/10⁷`; `s < 10⁻⁶`; `μΔ ≤ θ/4`; `0 ≤ σ_c ≤ θ²/10⁷`; `0 < σ_s ≤ θ²/10⁷`; `v_s ≤ θ/4`.

Derived inside (BCG8 passed them separately): `10Λ, 20ΔΛ ≤ 1/2` (from `950000ΔΛ ≤ 1/2`, `Δ ≥ 1`),
`22Δβ₁³ < 1`, `β₂ < 1` and `b < 10⁻⁶` (from `θ < 1`), `32·130 ≤ n` and `32·106Δ ≤ n`, the edge and
slim length `L_b = 10⁶Δ`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- **BCG02's joint (BA) clauses on GIVEN data** (see the module docstring): for the given collar
packet `P`, scale `ρ`, completion `ĝ` and family `F : LocalPacketsOnBFR …`, the circle, revised
edge and slim joint value/differential clauses of `lc88_boundary_values_differential_BFR_BCG8`. -/
theorem bcg02_joint_BA_of_data_BIND {θ ν : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hν : 0 < ν)
    (hν1 : ν < 1 / 1000000) :
    ∃ σC : ℝ, 0 < σC ∧ ∃ ηC : ℝ, 0 < ηC ∧
    ∀ Δ νS : ℝ, 1 ≤ Δ → 0 < νS → νS < 1 →
    ∃ σE : ℝ, 0 < σE ∧ ∃ ηE : ℝ, 0 < ηE ∧ ∃ σS : ℝ, 0 < σS ∧ ∃ ηS : ℝ, 0 < ηS ∧
    ∀ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
      (g : SmoothRiemannianMetric W.model W.Carrier) {K : ℕ} {A : ℝ → ℝ} {w₀ εB : ℝ}
      (P : BoundaryCollarPacket W g K A w₀ εB) (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p)
      {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {Kf : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz n : ℝ}
      (ĝ : SmoothRiemannianMetric 𝓘(ℝ, E3) (W.pieceInterior ⊤)),
      -- the certificates of the given data
      1 ≤ K → 0 ≤ Λ →
      (∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf g x y) →
      (∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
        ρ ((P.cusp.collar i).toFun q) ≤ β 1 ^ 3 / 2000) →
      (∀ x : W.pieceInterior ⊤, ENNReal.ofReal 4 ≤ distanceToBoundary W g x →
        ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x) →
      (∀ p, 0 < distanceToBoundary W g p →
        n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
          (distanceToBoundary W g p).toReal / ρ p) →
      (∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
        2 * ρ ((P.cusp.collar i).toFun q) * (12 * (1000000 * Δ) + 1000) < θ ^ 2 / 10 ^ 8) →
      -- the tail index and the tolerances of the collar packet
      32 * ηC⁻¹ ≤ n → 32 * ηE⁻¹ ≤ n → 32 * ηS⁻¹ ≤ n → 32 * (1000000 * Δ) ≤ n →
      w₀ ≤ β 1 ^ 2 / 1000 → εB ≤ β 1 ^ 2 / 1000 → εB ≤ θ ^ 2 / 40000000 →
      w₀ ≤ θ ^ 2 / 40000000 →
      -- BCG8's parameter requests
      950000 * Δ * Λ ≤ 1 / 2 → 0 < β 1 → 2 * β 1 ≤ ηC → 2 * β 1 ≤ ηE → 2 * β 1 ≤ ηS →
      1000000 * Δ * β 1 ^ 3 < 1 → 3 * β 1 ≤ σS → β 1 * (2 * (1950002 * Δ + 1)) ≤ 1 →
      β 1 ≤ θ ^ 2 / 10000000 → 3 * β 2 ≤ σC → β 2 ≤ θ ^ 2 / 10000000 → 3 * νS ≤ β 2 →
      3 * ν ≤ β 3 → β 3 < 1 → σC⁻¹ ≤ Lmax → σE⁻¹ ≤ Lmax → σS⁻¹ ≤ Lmax →
      γ ≤ θ ^ 2 / 10000000 → 3 * b ≤ σE → b * (2 * (421 * Δ + 1)) ≤ 1 →
      b ≤ θ ^ 2 / 10000000 → s < 1 / 1000000 → μ * Δ ≤ θ / 4 → 0 ≤ σc →
      σc ≤ θ ^ 2 / 10000000 → 0 < σs → σs ≤ θ ^ 2 / 10000000 → vs ≤ θ / 4 →
      letI := inducedMetricSpace ĝ
      ∀ (_ : CompleteSpace (W.pieceInterior ⊤)) (U₁ U₂ Ue₁ Ue₂ : Set (W.pieceInterior ⊤)),
      (∀ x ∈ U₁, ENNReal.ofReal 5 < distanceToBoundary W g x) →
      ∀ F : LocalPacketsOnBFR (W.pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ)
          (fun x => ρ x) (fun x => hρ x) Λ β Δ σs Kf σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
          vs ζ Λz U₁ U₂ Ue₁ Ue₂,
      -- BCG02 at the circle references: value AND differential with ONE unit row (BCG-7 G6)
      (∀ (j : W.pieceInterior ⊤) (hj : j ∈ F.circle.centres) (bb : Fin P.cusp.count),
        (∃ x ∈ tsupport (P.block bb),
          riemannianEDistOf g j.val x < ENNReal.ofReal (10 * ρ j)) →
        ∃ Ab : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 1),
          Ab.comp (ContinuousLinearMap.adjoint Ab) = ContinuousLinearMap.id ℝ _ ∧
          (∀ y : W.pieceInterior ⊤, dist y j < 10 * ρ j →
            ‖EuclideanSpace.single 0 ((P.height bb y - P.height bb j) / ρ j) -
              Ab ((let c := F.circle.chart j hj;
                  letI := (inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j));
                  c.coord y) -
                (let c := F.circle.chart j hj;
                  letI := (inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j));
                  c.coord j))‖ < θ) ∧
          ∀ x : W.pieceInterior ⊤, dist x j < 10 * ρ j → ∃ θ' < θ,
            ∀ u : TangentSpace 𝓘(ℝ, E3) x,
            |mvfderiv 𝓘(ℝ, E3)
                (fun y : W.pieceInterior ⊤ =>
                  (P.height bb y - P.height bb j) / ρ j) x u -
              Ab (mvfderiv 𝓘(ℝ, E3) (let c := F.circle.chart j hj;
                  letI := (inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j));
                  c.coord) x u) 0| ≤
              θ' * Real.sqrt ((scaleMetric ((ρ j)⁻¹ ^ 2)
                (pow_pos (inv_pos.mpr (hρ j)) 2) ĝ).inner x u u)) ∧
      -- BCG02 at the REVISED (active) edge references `F.edgeB`: value AND differential
      -- with ONE sign (BCG-7/BCG-8 G8)
      (∀ (j : W.pieceInterior ⊤) (hj : j ∈ F.edgeB.centres) (bb : Fin P.cusp.count),
        (∃ x ∈ tsupport (P.block bb),
          riemannianEDistOf g j.val x < ENNReal.ofReal (20 * Δ * ρ j)) →
        ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
          (∀ y : W.pieceInterior ⊤, dist y j < 20 * Δ * ρ j →
            |(P.height bb y - P.height bb j) / ρ j -
              a * (F.edgeB.coord_BCG1 j hj y - F.edgeB.coord_BCG1 j hj j)| < θ) ∧
          ∀ x : W.pieceInterior ⊤, dist x j < 20 * Δ * ρ j → ∃ θ' < θ,
            ∀ u : TangentSpace 𝓘(ℝ, E3) x,
            |mvfderiv 𝓘(ℝ, E3)
                (fun y : W.pieceInterior ⊤ =>
                  (P.height bb y - P.height bb j) / ρ j) x u -
              a * mvfderiv 𝓘(ℝ, E3) (F.edgeB.coord_BCG1 j hj) x u| ≤
              θ' * Real.sqrt ((scaleMetric ((ρ j)⁻¹ ^ 2)
                (pow_pos (inv_pos.mpr (hρ j)) 2) ĝ).inner x u u)) ∧
      -- BCG02 at the slim references: value AND differential with ONE sign (BCG-8 G9)
      ∀ (j : W.pieceInterior ⊤) (hj : j ∈ F.slim.centres) (bb : Fin P.cusp.count),
        (∃ x ∈ tsupport (P.block bb),
          riemannianEDistOf g j.val x < ENNReal.ofReal (950000 * Δ * ρ j)) →
        ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
          (∀ y : W.pieceInterior ⊤, dist y j < 950000 * Δ * ρ j →
            |(P.height bb y - P.height bb j) / ρ j -
              a * ((F.slim.centre j hj).coord_BCG2 y -
                (F.slim.centre j hj).coord_BCG2 j)| < θ) ∧
          ∀ x : W.pieceInterior ⊤, dist x j < 950000 * Δ * ρ j → ∃ θ' < θ,
            ∀ u : TangentSpace 𝓘(ℝ, E3) x,
            |mvfderiv 𝓘(ℝ, E3)
                (fun y : W.pieceInterior ⊤ =>
                  (P.height bb y - P.height bb j) / ρ j) x u -
              a * mvfderiv 𝓘(ℝ, E3) (F.slim.centre j hj).coord_BCG2 x u| ≤
              θ' * Real.sqrt ((scaleMetric ((ρ j)⁻¹ ^ 2)
                (pow_pos (inv_pos.mpr (hρ j)) 2) ĝ).inner x u u) := by
  refine (bcg02_circle_differential_BCG7 hθ hθ1 hν (by linarith)).elim fun σC c1 => ?_
  refine c1.2.2.elim fun ηC c2 => ?_
  refine ⟨σC, c1.1, ηC, c2.1, fun Δ νS hΔ1 hνS hνS1 => ?_⟩
  refine (bcg02_edge_differential_on_BCG7 hθ hθ1 hν hν1 hΔ1).elim fun σE e1 => ?_
  refine e1.2.2.elim fun ηE e2 => ?_
  refine (bcg02_slim_differential_BCG8 hθ hθ1 hνS hνS1 hΔ1).elim fun σS s1 => ?_
  refine s1.2.2.elim fun ηS s2 => ?_
  refine ⟨σE, e1.1, ηE, e2.1, σS, s1.1, ηS, s2.1, ?_⟩
  intro W _ g K A w₀ εB P ρ hρ Λ β σs Kf σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz n ĝ
    hK hΛ hlip hcol heq hbcp hB5 hnC hnE hnS hnL hwβ hεβ hεθ hwθ hΛC hβ1 hβηC hβηE hβηS hβL h3βS
    hβH hβθ hβ2σ hβ2θ hν2 hν3 hβ31 hσCL hσEL hσSL hγθ h3b hbH hbθ hs6 hμθ hσc0 hσcθ hσs0 hσsθ hvs
    hcN U₁ U₂ Ue₁ Ue₂ hU₁ F
  let instM_BIND : MetricSpace (W.pieceInterior ⊤) := inducedMetricSpace ĝ
  -- the inputs that BCG8 passed separately, derived from the ones above
  have hΔ0 : 0 < Δ := by linarith
  have hΛΔ : Λ ≤ Δ * Λ := le_mul_of_one_le_left hΛ hΔ1
  have hΔΛ0 : 0 ≤ Δ * Λ := by positivity
  have hΛ10 : 10 * Λ ≤ 1 / 2 := by linarith
  have hΛ20 : 20 * Δ * Λ ≤ 1 / 2 := by linarith
  have hβΔ : 22 * Δ * β 1 ^ 3 < 1 := by
    have : 0 ≤ Δ * β 1 ^ 3 := by positivity
    linarith
  have hθ2 : θ ^ 2 < 1 := by nlinarith
  have hβ2' : β 2 < 1 := by linarith
  have hb6 : b < 1 / 1000000 := by linarith
  have hn130 : 32 * 130 ≤ n := by linarith
  have hn106 : 32 * (106 * Δ) ≤ n := by linarith
  have hLb0 : (0 : ℝ) ≤ 1000000 * Δ := by positivity
  refine ⟨fun j hj bb hmeet => ?_, fun j hj bb hmeet => ?_, fun j hj bb hmeet => ?_⟩
  · -- circle references (BCG-7 G6)
    exact c2.2.2 W g P ρ hρ ĝ hK hΛ hlip hcol heq hbcp hnC hβ1 hβηC hwβ hεβ hΛ10 hν3 hβ31 hβ2σ
      hσCL hγθ hβ2θ hεθ hwθ hLb0 hB5 hn130 hcN U₁ U₂ hU₁ F.toLocalPacketsOn j hj bb hmeet
  · -- revised edge references `F.edgeB` (BCG-7/BCG-8 G8)
    exact e2.2.2 W g P ρ hρ ĝ hK hΛ hlip hcol heq hbcp hnE hβ1 hβηE hwβ hεβ hΛ20 hβΔ hσEL h3b
      hbH hb6 hs6 hμθ hσc0 hσcθ hbθ hεθ hwθ le_rfl hB5 hn106 hcN U₁ U₂ Ue₁ Ue₂ hU₁
      F.toLocalPacketsOn F.edgeB (F.edgeB_centres_subset_BCG3 hΔ0) j hj bb hmeet
  · -- slim references (BCG-8 G9)
    exact s2.2.2 W g P ρ hρ ĝ hK hΛ hlip hcol heq hbcp hnS hβ1 hβηS hwβ hεβ hΛC hβL hν2 hβ2'
      hσSL h3βS hβH hvs hσs0 hσsθ hβθ hεθ hwθ le_rfl hB5 hnL hcN U₁ U₂ Ue₁ Ue₂ hU₁
      F.toLocalPacketsOnB j hj bb hmeet

end DifferentialGeometry.Geometry.Collapse
