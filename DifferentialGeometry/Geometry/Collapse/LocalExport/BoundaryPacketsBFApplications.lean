import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPacketsBProducerT3
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeightEdgeOn

/-!
# Consumers of the final boundary family (lane BCG-3, review 51)

Consumers of `LocalPacketsOnBF` (the family produced by T3B, `lc88_boundary_packets_BF_BCG3`, on
the regions `U₁ = {D > 10}`, `U₂ = {D ≥ 20}`, `Ue₁ = {D > 20}`, `Ue₂ = {D ≥ 35}`), every edge
statement on the REVISED edge family `F.edgeB` (review 51 P0-A):

* `LocalPacketsOnBF.edgeB_centres_subset_BCG3`: the revised edge centres lie in `U₁` (from
  `edgeB_domain`);
* `LocalPacketsOnBF.bcg01_cover_BCG3`: BCG01's four-family cover of `Ue₂` — every point of `Ue₂`
  lies in a tenth zero ball, a circle ball `B(j, 2ρ_j)`, a slim ball `B(j, 2Δρ_j)` or a revised
  edge ball `B(j, 2Δρ_j)` (`exhaustionB` + the zero family's cover of `U₁ ∩ Z₀`, `Ue₂ ⊆ U₁`);
  `boundary_cover_regions_BCG3`: `{D ≥ 35} ⊆ {D > 10}` (the boundary instance of `Ue₂ ⊆ U₁`);
* `LocalPacketsOnBF.edgeB_collar_eligible_BCG3`: edge-collar ELIGIBILITY (review 51 Q2: eligibility
  only, not the collar cover) — every revised edge centre has `D > 20` and its packet domain
  `B(j, 1000Δρ_j)` lies in `{D > 10}`;
* `bcg02_edge_value_edgeB_BCG3`: BCG02's edge value clause at the revised edge family `F.edgeB` of a
  final boundary family (instantiation of `bcg02_edge_value_on_BCG2`);
* `LocalPacketsOnBF.slim_value_readoff_BCG3`: the slim value read-off `|η_j − u_j| < ϑ/4` on
  `B(j, 10⁶Δρ_j)` for `vs ≤ ϑ/4` (BCG02 slim value clause).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry GC.Endpoint
  DifferentialGeometry.Geometry.Hyperbolic

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Abstract

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- The revised edge centres of a final boundary family lie in `U₁` (their packet domains do). -/
theorem LocalPacketsOnBF.edgeB_centres_subset_BCG3
    (F : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      vs ζ Λz U₁ U₂ Ue₁ Ue₂) (hΔ : 0 < Δ) :
    F.edgeB.centres ⊆ U₁ := fun j hj =>
  F.edgeB_domain j hj (mem_ball_self (by have := hρ j; positivity))

/-- **BCG01's four-family cover of `Ue₂`** on a final boundary family (`Ue₂ ⊆ U₁`): every point of
`Ue₂` lies in a tenth zero ball, a circle ball, a slim ball or a REVISED edge ball. -/
theorem LocalPacketsOnBF.bcg01_cover_BCG3
    (F : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      vs ζ Λz U₁ U₂ Ue₁ Ue₂) (hU : Ue₂ ⊆ U₁) :
    letI := F.instMetricN
    letI := F.instChartedN
    letI := F.instMetricC
    ∀ x ∈ Ue₂, (∃ c, ∃ hc : c ∈ F.zero.centres, x ∈ ball c ((F.zero.zero c hc).radius / 10)) ∨
      (∃ j ∈ F.circle.centres, x ∈ ball j (2 * ρ j)) ∨
      (∃ j ∈ F.slim.centres, x ∈ ball j (2 * (Δ * ρ j))) ∨
      ∃ j ∈ F.edgeB.centres, dist x j < 2 * Δ * ρ j := by
  let _ := F.instMetricN
  let _ := F.instChartedN
  let _ := F.instMetricC
  intro x hx
  rcases F.exhaustionB x hx with h0 | hrest
  · left
    have hmem := F.zero.covers_stratum ⟨hU hx, h0⟩
    obtain ⟨c, hc⟩ := mem_iUnion.mp hmem
    obtain ⟨hc, hxc⟩ := mem_iUnion.mp hc
    exact ⟨c, hc, hxc⟩
  · exact Or.inr hrest

/-- **Edge-collar eligibility** (review 51 Q2; eligibility only): every revised edge centre lies in
`Ue₁` and its packet domain `B(j, 1000Δρ_j)` in `U₁`. -/
theorem LocalPacketsOnBF.edgeB_collar_eligible_BCG3
    (F : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      vs ζ Λz U₁ U₂ Ue₁ Ue₂) :
    ∀ j ∈ F.edgeB.centres, j ∈ Ue₁ ∧ ∀ x ∈ ball j (1000 * Δ * ρ j), x ∈ U₁ := fun j hj =>
  ⟨F.edgeB.centres_subset hj, fun _ hx => F.edgeB_domain j hj hx⟩

/-- **The slim value read-off** (BCG02 slim value clause): for `vs ≤ ϑ/4`, at every slim centre the
slim coordinate and the real coordinate of the stored split differ by `< ϑ/4` on `B(j, 10⁶Δρ_j)`. -/
theorem LocalPacketsOnBF.slim_value_readoff_BCG3
    (F : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      vs ζ Λz U₁ U₂ Ue₁ Ue₂) {ϑ : ℝ} (hvs : vs ≤ ϑ / 4) :
    ∀ j (hj : j ∈ F.slim.centres), ∀ x ∈ ball j (10 ^ 6 * Δ * ρ j),
      |(F.slim.centre j hj).coord_BCG2 x -
        (letI := (F.slim.centre j hj).instZ
         @KleinerLottApprox.toFun X (WithLp 2 (ℝ × (F.slim.centre j hj).Z))
          (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ j _ (β 1) (F.slim.centre j hj).split x).fst|
        < ϑ / 4 := fun j hj x hx =>
  (F.slim_value j hj x hx).trans_le hvs

end Abstract

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- The boundary instance of `Ue₂ ⊆ U₁`: `{D ≥ 35} ⊆ {D > 10}`. -/
theorem boundary_cover_regions_BCG3 {Y : Type} (D : Y → ℝ≥0∞) :
    {x | ENNReal.ofReal 35 ≤ D x} ⊆ {x | ENNReal.ofReal 10 < D x} := fun _ hx =>
  lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)) hx

/-- **BCG02's edge value at the REVISED edge family of a final boundary family** (review 51 P0-A):
`bcg02_edge_value_on_BCG2` at `E = F.edgeB` (centres in `U₁` by `edgeB_domain`). -/
theorem bcg02_edge_value_edgeB_BCG3 {θ ν Δ : ℝ} (hθ : 0 < θ) (hν : 0 < ν)
    (hν1 : ν < 1 / 1000000) (hΔ : 1 ≤ Δ) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 2 ∧
    ∀ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
      (g : SmoothRiemannianMetric W.model W.Carrier) {K : ℕ} {A : ℝ → ℝ} {w₀ εB : ℝ}
      (P : BoundaryCollarPacket W g K A w₀ εB) (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p)
      {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {Kf : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V n vs ζ Λz : ℝ}
      (ĝ : SmoothRiemannianMetric 𝓘(ℝ, E3) (W.pieceInterior ⊤)),
      1 ≤ K → 0 ≤ Λ →
      (∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf g x y) →
      (∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
        ρ ((P.cusp.collar i).toFun q) ≤ β 1 ^ 3 / 2000) →
      (∀ x : W.pieceInterior ⊤, ENNReal.ofReal 4 ≤ distanceToBoundary W g x →
        ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x) →
      (∀ p, 0 < distanceToBoundary W g p →
        n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
          (distanceToBoundary W g p).toReal / ρ p) →
      32 * η⁻¹ ≤ n → 0 < β 1 → 2 * β 1 ≤ η → w₀ ≤ β 1 ^ 2 / 1000 → εB ≤ β 1 ^ 2 / 1000 →
      20 * Δ * Λ ≤ 1 / 2 → 22 * Δ * β 1 ^ 3 < 1 → σ⁻¹ ≤ Lmax → 3 * b ≤ σ →
      b * (2 * (20 * Δ + 1)) ≤ 1 → b < 1 / 1000000 → s < 1 / 1000000 → μ * Δ ≤ θ / 4 →
      letI := inducedMetricSpace ĝ
      ∀ (_ : CompleteSpace (W.pieceInterior ⊤)) (U₁ U₂ Ue₁ Ue₂ : Set (W.pieceInterior ⊤)),
      (∀ x ∈ U₁, ENNReal.ofReal 5 < distanceToBoundary W g x) →
      ∀ (F : LocalPacketsOnBF (W.pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ)
          (fun x => ρ x) (fun x => hρ x) Λ β Δ σs Kf σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
          vs ζ Λz U₁ U₂ Ue₁ Ue₂)
        (j : W.pieceInterior ⊤) (hj : j ∈ F.edgeB.centres) (bb : Fin P.cusp.count),
        (∃ x ∈ tsupport (P.block bb),
          riemannianEDistOf g j.val x < ENNReal.ofReal (20 * Δ * ρ j)) →
      ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
        ∀ y : W.pieceInterior ⊤, dist y j < 20 * Δ * ρ j →
          |(P.height bb y - P.height bb j) / ρ j -
            a * (F.edgeB.coord_BCG1 j hj y - F.edgeB.coord_BCG1 j hj j)| < θ := by
  obtain ⟨σ, hσ, hσ1, η, hη, hη2, h⟩ := bcg02_edge_value_on_BCG2 hθ hν hν1 hΔ
  refine ⟨σ, hσ, hσ1, η, hη, hη2, ?_⟩
  intro W _ g K A w₀ εB P ρ hρ Λ β σs Kf σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V n vs ζ Λz ĝ hK
    hΛ hlip hcol heq hbcp hn hβ1 hβη hwβ hεβ hΛ20 hβΔ hσL h3b hbH hb6 hs6 hμ hcN U₁ U₂ Ue₁ Ue₂ hU₁
    F j hj bb hmeet
  let _ : MetricSpace (W.pieceInterior ⊤) := inducedMetricSpace ĝ
  exact h W g P ρ hρ ĝ hK hΛ hlip hcol heq hbcp hn hβ1 hβη hwβ hεβ hΛ20 hβΔ hσL h3b hbH hb6 hs6 hμ
    hcN U₁ U₂ Ue₁ Ue₂ hU₁ F.toLocalPacketsOn F.edgeB
    (F.edgeB_centres_subset_BCG3 (by linarith)) j hj bb hmeet

end DifferentialGeometry.Geometry.Collapse
