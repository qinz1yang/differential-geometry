import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceAugmented

/-!
# S-SOLIDTORUS2 (suffix `_STR`): one boundary component forces T3B's separated branch

D77-11 premise survey of the producer route (lane S-SOLIDTORUS2). The labelled whole-product branch
of `BoundarySupplyCore.geometric_cases` needs two DISTINCT cusp labels `i ≠ j`; with exactly one
nearly cuspidal boundary component (the solid torus) it is impossible, so the stored supply is on
the separated branch (`separated_of_count_one_STR`). Consequently the register's production theorem
`exists_boundaryChainE_register_stored_RNUM` (whose hypothesis `S.SeparatedCollarZero_BIF` is thus
automatic for every standing sequence whose members have ONE boundary component) discharges ALL
numerical premises of ProducerDP for every standing sequence: the only geometric input of the route
is the `BoundaryStandingSequence_BSTD1` itself. (The corollary restating that theorem without the
separation hypothesis exceeds the heartbeat limit at `obtain`; use the two lemmas below directly.)
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

/-- **One boundary component ⟹ the separated branch** of the stored supply. -/
theorem separated_of_count_one_STR {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
    {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier]
    {g : SmoothRiemannianMetric W.model W.Carrier} {δn : ℝ} {n : ℕ}
    {B : NearlyCuspidalBoundary W g K δn}
    {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
    (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      ζ Λz W g δn n B oM)
    (hc : B.count = 1) : S.SeparatedCollarZero_BIF := by
  rcases S.geometric_cases_BIF with ⟨i, j, hij, -⟩ | h
  · exfalso
    have hcount : S.packet.cusp.count = 1 := by rw [S.cusp_eq]; exact hc
    have hsub : Subsingleton (Fin S.packet.cusp.count) := by
      rw [hcount]
      infer_instance
    exact hij (Subsingleton.elim i j)
  · exact h

/-- The same for the supply `BoundarySupply` (extends the core). -/
theorem separated_of_count_one_supply_STR {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
    {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
    {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier]
    {g : SmoothRiemannianMetric W.model W.Carrier} {δn : ℝ} {n : ℕ}
    {B : NearlyCuspidalBoundary W g K δn}
    {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
    (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      ζ Λz θ W g δn n B oM)
    (hc : B.count = 1) : S.SeparatedCollarZero_BIF :=
  separated_of_count_one_STR S.toBoundarySupplyCore hc

end DifferentialGeometry.Geometry.Collapse
