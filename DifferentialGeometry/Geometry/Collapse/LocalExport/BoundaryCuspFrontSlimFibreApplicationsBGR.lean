import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspFrontSlimFibreBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimFibreEqualityApplicationsBGR

/-!
# Consumers of F5 without `Z` (S-BCG-ROWS2 G28)

* the FROZEN v3.1 F5 `cuspFront_eq_slimFibre_BAUGF` (premises `rd`-block, `cadj ≤ 10⁻⁵` unused,
  `θ < 1/100`) as an `example`, derived from `cuspFront_eq_slimFibre_direct_BGR`;
* `cuspFront_image_eq_singleton_BGR`: a front meeting `X₃` has exactly one base point (the cusp half
  of the finiteness of `f₃(∂M₁ ∩ X₃)`).
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
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)
  {Bs : BoundaryGaf02BasesV2 C.toChain}

/-- Frozen F5 (v3.1 verbatim premises, `cadj ≤ 10⁻⁵` unused). -/
example (WF : BoundaryWholeFiberSpecV2 C.toChain Bs) : ∀ {rd : ℝ}, 0 < rd → rd < 1 / 10000 →
    20 * (c 2 + 1) * rd < 1 / 1000000 →
    1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2 →
    cadj ≤ 1 / 100000 → θ < 1 / 100 →
    ∀ i : Fin S.packet.cusp.count, (C.toChain.cuspFront_BIF i ∩ Bs.source 2).Nonempty →
      ∃ y ∈ Bs.base 2, C.toChain.cuspFront_BIF i = Bs.fibre 2 y :=
  fun hrd hrd4 hrdc hprem _ hθ => C.cuspFront_eq_slimFibre_direct_BGR WF hrd hrd4 hrdc hprem hθ

/-- **A cusp front meeting `X₃` has ONE base point**: `f₃(H_b ∩ X₃) = {y}` with `y ∈ B₃` (the cusp
half of the finiteness of `f₃(∂M₁ ∩ X₃)`, BCF01 G1a input (a)). -/
theorem cuspFront_image_eq_singleton_BGR (WF : BoundaryWholeFiberSpecV2 C.toChain Bs) {rd : ℝ}
    (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (i : Fin S.packet.cusp.count)
    (hne : (C.toChain.cuspFront_BIF i ∩ Bs.source 2).Nonempty) :
    ∃ y ∈ Bs.base 2,
      C.toChain.stageMap 2 '' (C.toChain.cuspFront_BIF i ∩ Bs.source 2) = {y} := by
  obtain ⟨y, hy, hfib⟩ := C.cuspFront_eq_slimFibre_direct_BGR WF hrd hrd4 hrdc hprem hθ i hne
  refine ⟨y, hy, ?_⟩
  obtain ⟨p, hp, hpX⟩ := hne
  have hpy : C.toChain.stageMap 2 p = y := by
    have hp' : p ∈ Bs.fibre 2 y := hfib ▸ hp
    exact hp'.2
  ext z
  constructor
  · rintro ⟨q, ⟨hq, hqX⟩, rfl⟩
    have hq' : q ∈ Bs.fibre 2 y := hfib ▸ hq
    exact hq'.2
  · intro hz
    rw [mem_singleton_iff] at hz
    exact ⟨p, ⟨hp, hpX⟩, hpy.trans hz.symm⟩

end DifferentialGeometry.Geometry.Collapse
