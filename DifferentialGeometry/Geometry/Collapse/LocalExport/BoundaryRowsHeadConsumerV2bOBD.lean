import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRowsHeadV2bOBD

/-!
# Consumers of the boundary zero rows and of the BD2 head on v2b (lane O-BD2b)

Lane O-BD1 (by O-BD2b, suffix `_OBD`), group G3 consumer.

* `BoundaryActualZeroDomains_BIFc.exists_zeroDomains_union_OBD`: the pieces of the boundary zero
  rows cover exactly the union of the actual zero domains (the zero half of `M₁ = W \ int(Z ∪ C)`,
  the `regionM1` input of the landing), and every face is a regular zero level of the row's ratio;
* `BoundaryGaf02ChainE.boundary_graphPresentation_of_actual_decomposition74b_OBD`: the BD2 head
  composed with BCF04 (frozen G8's conclusion on tori with the packet's labels).
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

section Zero

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ}
  {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}

/-- **Consumer of the boundary zero rows**: the pieces cover exactly the union of the actual zero
domains, and each actual zero face is the regular zero level of the corresponding ratio. -/
theorem BoundaryActualZeroDomains_BIFc.exists_zeroDomains_union_OBD
    {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} {Bs : BoundaryGaf02BasesV2 C}
    (Z : BoundaryActualZeroDomains_BIFc C Bs)
    (Q : ∀ k : S.ZeroIdx_BAUGC,
      SelectedSmoothCore74.{0, 0} {q : W.pieceInterior ⊤ | S.zeroRadial_BIFc k q ≤ 2 / 5}) :
    ∃ zero : ZeroDomains W,
      (⋃ j, range (zero.piece j).map) = ⋃ k, C.actualZeroDomain_BIFc k ∧
      ∀ j, ∃ k, C.actualZeroFace_BIFc k = {x | zero.ratio j x = 0} ∧
        ∀ x ∈ C.actualZeroFace_BIFc k, mfderiv W.model 𝓘(ℝ, ℝ) (zero.ratio j) x ≠ 0 := by
  obtain ⟨zero, σ, hz⟩ := Z.exists_zeroDomains_OBD Q
  refine ⟨zero, ?_, fun j => ⟨σ j, ?_, fun x hx => zero.ratio_regular j x ?_⟩⟩
  · rw [← σ.surjective.iUnion_comp (fun k => C.actualZeroDomain_BIFc k)]
    exact iUnion_congr fun j => (hz j).1
  · rw [← (hz j).2.2.1]
    exact zero.boundary_eq j
  · rw [← (hz j).2.2.1, zero.boundary_eq j] at hx
    exact hx

end Zero

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

/-- **Consumer of the BD2 head** (BCF04): frozen G8's conclusion (certificate with the rim-product
clause) on tori whose ranges are the packet's cusp components. -/
theorem BoundaryGaf02ChainE.boundary_graphPresentation_of_actual_decomposition74b_OBD
    (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)
    (dec : BoundaryActualDecompositionV2b C.toChain)
    (geom : BoundaryGeometricExports74b C.toChain dec)
    (Q : ∀ k : S.ZeroIdx_BAUGC,
      SelectedSmoothCore74.{0, 0} {q : W.pieceInterior ⊤ | S.zeroRadial_BIFc k q ≤ 2 / 5})
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100)
    (hlift : ∀ zc : BoundaryZeroCuspExit74b C.toChain dec,
      ∃ X : BoundaryLandingExits74b C.toChain dec, X.zc = zc) :
    ∃ Et : BoundaryTori W S.packet.cusp.count,
      Nonempty {D : DecompositionCertificate W Et // D.RimProduct} ∧
        ∀ i, range (Et.torusMap i) = S.packet.cusp.component i := by
  obtain ⟨Et, hEt, Rw, -⟩ :=
    C.boundary_rows_of_actual_decomposition74b_OBD dec geom Q hrd hrd4 hrdc hprem hθ hlift
  exact boundary_graphPresentation_of_rows_BCF04 S Rw hEt

end DifferentialGeometry.Geometry.Collapse
