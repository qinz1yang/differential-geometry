import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryGraphPresentationProductBCF
import DifferentialGeometry.Geometry.Collapse.BoundaryEarlyThresholdsBSTD1

/-!
# The product-label bridge for H (lane S-HBRIDGE, suffix `_HB`), group G1

Disposition D80-11 (g): the product branch of the geometric output keeps `LabelledWholeProduct_BIF`
(a statement about the supply, with NO tori and NO certificate inside); a NAMED bridge theorem
turns it into the labelled certificate of H2 on the member's own boundary `B`:

* `count_eq_two_of_product_HB`: the product has exactly two boundary components;
* `labels_exhaust_of_product_HB`: the two labels `i ≠ j` of the product exhaust the labels,
  `∀ k, k = i ∨ k = j` (exhaustion; disjointness is inside `exists_productPortsEquiv`);
* **`labelledCertificate_of_product_HB`**: the labelled certificate on `B` (tori numbered by `B`,
  a certificate with the rim-product clause, torus `i` = component `i`) from the product, with
  the label transport `S.cusp_eq : S.packet.cusp = B`;
* `labelledCertificate_of_product_member_HB`: the same at the member `m` of a standing sequence
  in the exact shape of the conclusion of H2 (`letI := Sq.conn m`, `Sq.B m`).

Everything is assembled from tree modules (BCF04's `boundary_graphPresentation_of_product_BCF04`,
the FC39-P0 whole-product ports); no new premise, structure or named proposition.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology GC.GraphManifold
open GC.GraphManifold.Assembly

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

/-- **The labelled whole product has exactly two boundary components**: its product
diffeomorphism identifies `W` with `annulus × S¹`, whose boundary has two tori. -/
theorem count_eq_two_of_product_HB (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc
    βc Lmax τ γ δ εr e T V vs ζ Λz θ W g δn n B oM)
    (h : S.LabelledWholeProduct_BIF) : S.packet.cusp.count = 2 := by
  obtain ⟨-, -, -, D, -, -⟩ := h
  exact GC.GraphManifold.Assembly.FC39P0.count_eq_two_of_productDiffeomorph S.packet.cusp
    (annulusCircleCarrierDiffeomorphTorusInterval.{0}.trans D)

/-- **Exhaustion of the labels** (D80-11): the two labels `i ≠ j` of the labelled whole product
are ALL the labels of the packet's boundary, `∀ k, k = i ∨ k = j`. -/
theorem labels_exhaust_of_product_HB (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc
    βc Lmax τ γ δ εr e T V vs ζ Λz θ W g δn n B oM)
    (h : S.LabelledWholeProduct_BIF) :
    ∃ i j : Fin S.packet.cusp.count, i ≠ j ∧ (∀ k, k = i ∨ k = j) ∧
      ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) W.model (Torus × Icc (0 : ℝ) 1) W.Carrier ∞,
        (∀ p, D p ∈ S.packet.cusp.component i ↔ p.2.1 = 0) ∧
          ∀ p, D p ∈ S.packet.cusp.component j ↔ p.2.1 = 1 := by
  have hc := count_eq_two_of_product_HB S h
  obtain ⟨i, j, hij, D, hi, hj⟩ := h
  refine ⟨i, j, hij, fun k => ?_, D, hi, hj⟩
  have hk : (k : ℕ) < 2 := hc ▸ k.2
  have hi2 : (i : ℕ) < 2 := hc ▸ i.2
  have hj2 : (j : ℕ) < 2 := hc ▸ j.2
  have hne : (i : ℕ) ≠ j := fun he => hij (Fin.ext he)
  by_contra hcon
  have hcon' := not_or.mp hcon
  have h1 : (k : ℕ) ≠ i := fun he => hcon'.1 (Fin.ext he)
  have h2 : (k : ℕ) ≠ j := fun he => hcon'.2 (Fin.ext he)
  omega

/-- **The labelled certificate at the packet's labels** (BCF04 on the labelled whole product). -/
theorem labelledCertificate_of_product_packet_HB (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s
    b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g δn n B oM)
    (h : S.LabelledWholeProduct_BIF) :
    ∃ Et : BoundaryTori W S.packet.cusp.count,
      Nonempty {D : DecompositionCertificate W Et // D.RimProduct} ∧
        ∀ i, range (Et.torusMap i) = S.packet.cusp.component i :=
  boundary_graphPresentation_of_product_BCF04 S h

/-- **The product-label bridge** (D80-11 (g)): the labelled whole product of the supply gives the
labelled certificate on the member's boundary `B` — tori numbered by `B`, a decomposition
certificate with the rim-product clause, torus `i` = component `i` of `B` — by BCF04 (ports
numbered by the packet's labels, exhaustion by `labels_exhaust_of_product_HB`) and the label
transport `S.cusp_eq : S.packet.cusp = B`. -/
theorem labelledCertificate_of_product_HB (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε
    γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g δn n B oM)
    (h : S.LabelledWholeProduct_BIF) :
    ∃ Et : BoundaryTori W B.count,
      Nonempty {D : DecompositionCertificate W Et // D.RimProduct} ∧
        ∀ i, range (Et.torusMap i) = B.component i := by
  rw [← S.cusp_eq]
  exact labelledCertificate_of_product_packet_HB S h

attribute [local instance] BoundaryStandingSequence_BSTD1.conn

/-- **The bridge at a member of a standing sequence**, in the exact shape of the conclusion of
H2: for the supply `S` of member `m` (any index data, the member's own `Sq.B m`), the labelled
whole product gives tori `Et` on `Sq.W m` numbered by `Sq.B m` with the rim-product certificate. -/
theorem labelledCertificate_of_product_member_HB {δs : ℝ}
    (Sq : BoundaryStandingSequence_BSTD1 K A δs) (m : ℕ)
    (oM' : ManifoldOrientation 𝓘(ℝ, E3) ((Sq.W m).pieceInterior ⊤) 3)
    (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      ζ Λz θ (Sq.W m) (Sq.g m) (boundaryCounterexampleRatio Sq.δ₀ (m + 1)) (m + 1) (Sq.B m) oM')
    (h : S.LabelledWholeProduct_BIF) :
    letI := Sq.conn m
    ∃ Et : BoundaryTori (Sq.W m) (Sq.B m).count,
      Nonempty {D : DecompositionCertificate (Sq.W m) Et // D.RimProduct} ∧
        ∀ i, range (Et.torusMap i) = (Sq.B m).component i :=
  labelledCertificate_of_product_HB S h

end DifferentialGeometry.Geometry.Collapse
