import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoreProductEmbeddingOCX

/-!
# Consumer of E4c (lane O-CROSS, G2): the cusp fields of the boundary geometric exports

`bcg06_cusp_fields_on_chain_OCX`: on the enhanced chain, with E4b's premises, BCG6-K's bare spec
(E4b, `bcg06_coreSpec_on_chain_BGR`) AND, for every component, the concrete E4c (`hE` of BD0) AND
the frozen E4c — the `cusp` / `cuspProduct` fields of the geometric exports. The frozen form is
re-derived from the concrete one (`Φ = val ∘ D`, `frozen_of_concrete_OCX`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis GC.GraphManifold.Assembly

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- **Frozen E4c from the concrete form**: `Φ = val ∘ D` maps onto the core, end `0` onto `Bd`,
end `1` onto `Fr`, when `D` is onto the core and the end labels hold. -/
theorem frozen_of_concrete_OCX {X : Type*} {Cr Bd Fr : Set X} {T : Type*}
    (D : T × Icc (0 : ℝ) 1 ≃ Cr) (hB : Bd ⊆ Cr) (hF : Fr ⊆ Cr)
    (h0 : ∀ p, (D p : X) ∈ Bd ↔ (p.2 : ℝ) = 0) (h1 : ∀ p, (D p : X) ∈ Fr ↔ (p.2 : ℝ) = 1) :
    range (fun p => (D p : X)) = Cr ∧
      (range fun t => (D (t, iccEnd false) : X)) = Bd ∧
      (range fun t => (D (t, iccEnd true) : X)) = Fr := by
  have hr : range (fun p => (D p : X)) = Cr := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact (D p).2
    · intro hx
      exact ⟨D.symm ⟨x, hx⟩, by simp⟩
  refine ⟨hr, range_iccEnd_eq_OCX hr hB false (fun p => ?_),
    range_iccEnd_eq_OCX hr hF true (fun p => ?_)⟩
  · rw [h0 p]
    rfl
  · rw [h1 p]
    rfl

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

/-- **The cusp fields on the chain**: E4b (bare spec) ∧ E4c in the frozen form, the latter read
off the concrete form `val ∘ D` (the same product as BD0's `hE`). -/
theorem bcg06_cusp_fields_on_chain_OCX {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    BoundaryCollarPacket.BoundaryCuspCoreSpec_BCG6K S.packet.toBoundaryCollarPacket
      (chainBoundaryU_BCG6K C.toChain.E) (chainBoundaryV_BCG6K C.toChain.E)
      S.toBoundarySupplyCore.zeroBall_BCG6K ∧
    ∀ i : Fin S.packet.cusp.count, ∃ Φ : Torus × Icc (0 : ℝ) 1 → W.Carrier,
      IsSmoothEmbedding (torusModel.prod (𝓡∂ 1)) W.model ∞ Φ ∧
        range Φ = C.toChain.cuspCore_BIF i ∧
        (range fun t => Φ (t, iccEnd false)) = S.packet.cusp.component i ∧
        (range fun t => Φ (t, iccEnd true)) = C.toChain.cuspFront_BIF i := by
  refine ⟨C.bcg06_coreSpec_on_chain_BGR hrd hrd4 hrdc hprem hθ, fun i => ?_⟩
  obtain ⟨Φ, -, hrange, hB0, hF0⟩ :=
    C.bcg06_product_embedding_on_chain_OCX hrd hrd4 hrdc hprem hθ i
  have hB : S.packet.cusp.component i ⊆ C.toChain.cuspCore_BIF i := by
    rw [← hB0, ← hrange]
    rintro _ ⟨t, rfl⟩
    exact ⟨_, rfl⟩
  have hF : C.toChain.cuspFront_BIF i ⊆ C.toChain.cuspCore_BIF i := by
    rw [← hF0, ← hrange]
    rintro _ ⟨t, rfl⟩
    exact ⟨_, rfl⟩
  obtain ⟨cs, -, -, -, D, h0, h1, hemb⟩ :=
    C.bcg06_labelled_product_embedding_on_chain_OCX hrd hrd4 hrdc hprem hθ i
  obtain ⟨hr, he0, he1⟩ := frozen_of_concrete_OCX D.toEquiv hB hF h0 h1
  exact ⟨fun p => (D p : W.Carrier), hemb, hr, he0, he1⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
