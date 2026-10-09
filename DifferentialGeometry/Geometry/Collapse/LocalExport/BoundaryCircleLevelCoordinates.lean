import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleLevelDeriv

/-!
# G17 circle level (c): GAF07's two coordinate clauses together (S-BAUG-D2)

`circle_final_coordinates_BAUGD` (closed twin `Gaf02ChainEJA.gaf07_coordinates_GAFC`, circle part):
on a chain with `c₂ < 1/1000`, at every point `q` of the circle chart `j`'s original
threshold-`6` plateau (which contains `Y_j`), the adjusted coordinate `g_j = κ_j ∘ f₀` is
`1/800`-close to `η_j` AND `‖Dg_j(u) − Dη_j(u)‖ ≤ H ρ_j⁻¹ |u|_ĝ` with one `0 ≤ H < 1/1000`.
These are the closeness and derivative hypotheses (`hgη`, `hDg`, with `c = H`) of the FC34 kernels
`connected_adjusted_level_of_isotopy_BAUGD` / `exists_embedding_adjusted_level_BAUGD` for the circle
stage; the right inverse and the compact trace are the remaining ones.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open scoped ENNReal

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

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

include C in
/-- **GAF07's coordinate clauses on the boundary chain, circle stage** (consumer of
`circle_final_value_close_BAUGD` and `circle_final_deriv_close_BAUGD`). -/
theorem circle_final_coordinates_BAUGD (hc : c 2 < 1 / 1000) :
    ∃ H : ℝ, 0 ≤ H ∧ H < 1 / 1000 ∧ ∀ (j : S.CircleIdx_BAUGD) {q : W.pieceInterior ⊤},
      (letI := inducedMetricSpace S.completion.metric; dist q j.1 < 200 * S.rho j.1) →
      ‖S.circleEta_BIF j.1 q‖ < 6 →
      ‖S.circleKappa_BBP j (C.toChain.stageMap 0 q.val) - S.circleEta_BIF j.1 q‖ < 1 / 800 ∧
        ∀ u : TangentSpace (𝓡 3) q,
          ‖mvfderiv (𝓡 3) (fun x : W.pieceInterior ⊤ =>
              S.circleKappa_BBP j (C.toChain.stageMap 0 x.val)) q u -
            mvfderiv (𝓡 3) (S.circleEta_BIF j.1) q u‖ ≤
            H * ((S.rho j.1)⁻¹ * Real.sqrt (S.completion.metric.inner q u u)) := by
  obtain ⟨H, h0, h1, hd⟩ := C.circle_final_deriv_close_BAUGD hc
  exact ⟨H, h0, h1, fun j q hq hη =>
    ⟨C.circle_final_value_close_BAUGD hc j hq hη, hd j hq hη⟩⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
