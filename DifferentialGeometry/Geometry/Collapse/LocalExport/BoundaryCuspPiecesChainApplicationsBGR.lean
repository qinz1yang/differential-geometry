import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspPiecesChainBGR

/-!
# Consumer of the BD0 skeleton: the frozen E4c from the same-product exit (S-BCG-ROWS2 G26)

The hypothesis `hE` of `cuspCoresData_of_same_product_BGR` (the labelled product of the core with
its concrete charted structure AND the smooth embedding of `val ∘ D`) implies the FROZEN E4c of
`TargetsBoundary-v3.1` (`bcg06_product_embedding_on_chain`): every component has a smooth embedding
`Φ : T² × [0, 1] → W` onto the core, end `0` onto `∂_bW`, end `1` onto the front. So a delivery of
E4c in the `hE` form (lane O-CROSS) closes the frozen E4c and feeds BD0.

* **`bcg06_product_embedding_of_same_product_BGR`**.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
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

/-- **The frozen E4c (`bcg06_product_embedding_on_chain`) from the same-product exit `hE`.** -/
theorem bcg06_product_embedding_of_same_product_BGR {rd : ℝ} (hrd : 0 < rd)
    (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100)
    (hE : ∀ i : Fin S.packet.cusp.count,
      ∃ cs : ChartedSpace (EuclideanHalfSpace 3) (C.toChain.cuspCore_BIF i),
      letI := cs
      IsManifold (𝓡∂ 3) ∞ (C.toChain.cuspCore_BIF i) ∧
      ContMDiff (𝓡∂ 3) W.model ∞ (fun y : C.toChain.cuspCore_BIF i => (y : W.Carrier)) ∧
      (∀ y : C.toChain.cuspCore_BIF i, (𝓡∂ 3).IsBoundaryPoint y ↔
        ((y : W.Carrier) ∈ S.packet.cusp.component i ∨
          (y : W.Carrier) ∈ C.toChain.cuspFront_BIF i)) ∧
      ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) (𝓡∂ 3) (Torus × Icc (0 : ℝ) 1)
          (C.toChain.cuspCore_BIF i) ∞,
        (∀ p, (D p : W.Carrier) ∈ S.packet.cusp.component i ↔ (p.2 : ℝ) = 0) ∧
        (∀ p, (D p : W.Carrier) ∈ C.toChain.cuspFront_BIF i ↔ (p.2 : ℝ) = 1) ∧
        IsSmoothEmbedding (torusModel.prod (𝓡∂ 1)) W.model ∞ (fun p => (D p : W.Carrier))) :
    ∀ i : Fin S.packet.cusp.count, ∃ Φ : Torus × Icc (0 : ℝ) 1 → W.Carrier,
      IsSmoothEmbedding (torusModel.prod (𝓡∂ 1)) W.model ∞ Φ ∧
        range Φ = C.toChain.cuspCore_BIF i ∧
        (range fun t => Φ (t, iccEnd false)) = S.packet.cusp.component i ∧
        (range fun t => Φ (t, iccEnd true)) = C.toChain.cuspFront_BIF i := by
  intro i
  have hcomp := (C.bcg06_on_boundary_chain_BGR hrd hrd4 hrdc hprem hθ).1 i
  have hX : IsCompact (C.toChain.cuspCore_BIF i) := hcomp.compact_core
  obtain ⟨cs, hman, hval, hbd, D, h0, h1, hemb⟩ := hE i
  let _ := cs
  have hcompSub : S.packet.cusp.component i ⊆ C.toChain.cuspCore_BIF i := by
    intro x hx
    rw [← hcomp.boundary_label] at hx
    exact hx.1
  have hfrontSub : C.toChain.cuspFront_BIF i ⊆ C.toChain.cuspCore_BIF i := by
    have h := hX.isClosed.frontier_subset
    have hf : frontier (C.toChain.cuspCore_BIF i) = C.toChain.cuspFront_BIF i :=
      hcomp.relative_frontier_eq
    rw [hf] at h
    exact h
  refine ⟨fun p => (D p : W.Carrier), hemb, ?_, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact (D p).2
    · intro hx
      obtain ⟨p, hp⟩ := D.surjective ⟨x, hx⟩
      exact ⟨p, congrArg Subtype.val hp⟩
  · exact range_end_of_product_BGR D _ hcompSub (fun p => by rw [h0 p, iccEnd_false_val_BGR])
  · exact range_end_of_product_BGR D _ hfrontSub (fun p => by rw [h1 p, iccEnd_true_val_BGR])

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
