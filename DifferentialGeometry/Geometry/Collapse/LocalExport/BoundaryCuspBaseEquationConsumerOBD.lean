import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspBaseEquationOBD

/-!
# Consumer of BCG07 07.g3 (lane O-BD2b)

Lane O-BD1 (by O-BD2b, suffix `_OBD`), group G3b consumer: the stage image of a cusp front lies in
the zero level of the base cusp function and is crossed TRANSVERSALLY: at every front point there
is a tangent vector whose stage image has nonzero `φ_b`-derivative (the regularity input of
BCF01 G1a for the cusp frontier points of the slim base domain).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology GC.GraphManifold
  GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

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

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **Consumer of 07.g3**: the stage image of the front lies in `{φ_b = 0}`, and at every front
point some tangent vector has nonzero `φ_b`-derivative of its stage image (transversal crossing
of the base cusp equation). -/
theorem cuspBase_transversal_OBD {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (st : Fin 3) (i : Fin S.packet.cusp.count) :
    C.toChain.stageMap st '' C.toChain.cuspFront_BIF i ⊆ {y | cuspBaseCLM_OBD i y = 0} ∧
      ∀ p ∈ C.toChain.cuspFront_BIF i, ∃ v : TangentSpace W.model p,
        cuspBaseCLM_OBD i
          (mfderiv W.model 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
            (C.toChain.stageMap st) p v) ≠ 0 := by
  refine ⟨?_, fun p hp => ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact C.cuspBase_front_zero_OBD st i hp
  · have h := C.cuspBase_differential_ne_zero_OBD hrd hrd4 hrdc hprem hθ st i hp
    by_contra hall
    push Not at hall
    exact h (ContinuousLinearMap.ext hall)

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
