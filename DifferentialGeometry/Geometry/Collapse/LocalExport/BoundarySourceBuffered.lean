import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryLevelMargins
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesCoreData

/-!
# O-WF G5a: the BASES sources lie in the rank region `{D > 5}` (v2b's `source_buffered`)

The named revision for text v3.2 (`source_buffered`: `D > 5`, lead decision 2026-10-05 20:4x).
A source point `p ∈ X_st = C.baseSource_BBP st` lies in the chart ball `B(j, Rρ_j)` of a centre
`j` of its stage (circle `R = 200`, edge `R = 100Δ`, slim `R = 10⁶Δ`; the whole-preimage
localization of S-BASES-PORT2), every centre has `D(j) > 10` (the region `U₁`, the edge region
`{D > 20}`), and BCP04.a at `j` with `13R ≤ 5n` gives `D(p) > 5`
(`ofReal_lt_of_near_centre_BCG2`, `c₁ = 10`, `c₀ = 5`, `d_g ≤ d_ĝ`).

* `ofReal_five_lt_of_near_centre_OWF` (chain-free): the arithmetic step at one centre;
* **`BoundaryGaf02ChainE.source_buffered_OWF`**: `∀ st, X_st ⊆ {D > 5}`, under the register
  clause `32·10⁶Δ ≤ n` (already a premise of `BoundaryAffineHeightSlimDifferential`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic

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

/-- **One centre**: `D(j) > 10`, `d_ĝ(q, j) < Rρ_j` and `13R ≤ 5n` give `D(q) > 5`. -/
theorem ofReal_five_lt_of_near_centre_OWF (j q : W.pieceInterior ⊤)
    (hj : ENNReal.ofReal 10 < distanceToBoundary W g j) {R : ℝ} (hR : 13 * R ≤ 5 * (n : ℝ))
    (hd : (letI := inducedMetricSpace S.completion.metric; dist q j) < R * S.rho j) :
    ENNReal.ofReal 5 < distanceToBoundary W g q := by
  let _ := inducedMetricSpace S.completion.metric
  have hρ := S.rho_pos j.val
  have hpos : 0 < distanceToBoundary W g j :=
    lt_of_le_of_lt zero_le hj
  have hbcp := S.scale_spec.2.2.2.2 j.val hpos
  have hax : riemannianEDistOf S.completion.metric j q < ENNReal.ofReal (R * S.rho j) := by
    rw [inducedMetricSpace_hmetric S.completion.metric j q, dist_comm]
    exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt dist_nonneg hd)).mpr hd
  exact ofReal_lt_of_near_centre_BCG2 W g S.completion.metric S.completion.inner_le j q hρ
    (by norm_num) (by norm_num) (by linarith) hbcp hj hax

end BoundarySupplyCore

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

include C in
/-- **The BASES sources lie in `{D > 5}`** (v2b's `source_buffered`; see the module docstring). -/
theorem source_buffered_OWF (hn : 32 * (1000000 * Δ) ≤ (n : ℝ)) :
    ∀ st, C.baseSource_BBP st ⊆ {p | ENNReal.ofReal 5 < distanceToBoundary W g p} := by
  obtain ⟨-, hΔ, -, -, -, -, -, -, -, h1Δ, -⟩ := C.std
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  intro st p hp
  fin_cases st
  · obtain ⟨j, q, rfl, hd, -⟩ := C.circle_source_loc_BBP hp
    have hj : j.1 ∈ S.family.circle.centres := (Set.Finite.mem_toFinset _).mp j.2
    have hD := (S.family.circle.centres_subset hj).1
    exact S.ofReal_five_lt_of_near_centre_OWF j.1 q hD (R := 200) (by nlinarith) hd
  · obtain ⟨j, q, rfl, hd, -⟩ := C.edge_source_loc_BBP hp
    have hj : j.1 ∈ S.family.edgeB.centres := (Set.Finite.mem_toFinset _).mp j.2
    have hD20 : ENNReal.ofReal 20 < distanceToBoundary W g j.1 :=
      S.family.edgeB.centres_subset hj
    have hD : ENNReal.ofReal 10 < distanceToBoundary W g j.1 :=
      lt_trans ((ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)) hD20
    exact S.ofReal_five_lt_of_near_centre_OWF j.1 q hD (R := 100 * Δ) (by nlinarith)
      (by convert hd using 1)
  · obtain ⟨j, q, rfl, hd, -⟩ := C.slim_source_loc_BBP hp
    have hj : j.1 ∈ S.family.slim.centres := (Set.Finite.mem_toFinset _).mp j.2
    have hD := (S.family.slim.centres_subset hj).1
    exact S.ofReal_five_lt_of_near_centre_OWF j.1 q hD (R := 1000000 * Δ) (by nlinarith)
      (by convert hd using 1)

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
