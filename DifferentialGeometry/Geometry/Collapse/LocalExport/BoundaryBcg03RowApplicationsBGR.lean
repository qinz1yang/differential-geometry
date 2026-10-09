import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBcg03RowBGR

/-!
# BCG03 on a non-empty chain with an A4 output: the existential form (S-BCG-ROWS3, G36)

* **`bcg03_row_of_A4_BGR`**: `h` is the conclusion of the production A2 v3 (a chain on `DP` with
  every slot active, i.e. GAF01's ordered construction has produced the actual adjustments), `hA4`
  the conclusion of A4 (v2 bases with the whole-fibre layer v2b on every chain); the conclusion is
  the activity clause and `bcg03_row_BGR` (chain part ∧ A4 part) on ONE chain and ONE A4 output.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology

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
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

/-- **BCG03 on a non-empty chain with an A4 output** (existential form of `bcg03_row_BGR`). -/
theorem bcg03_row_of_A4_BGR
    (h : ∃ C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj,
      ∀ st, ∃ O, C.toChain.slot st = .active O)
    (hA4 : ∀ C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj,
      ∃ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs) :
    ∃ C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj,
      (∀ st, ∃ O, C.toChain.slot st = .active O) ∧
      ∃ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs ∧
    (-- the three stage tables of the augmented data
      (∀ st : Fin 3, DP.toBoundaryAugmentedData.EnhancedPlaneSpecV3 Γ Sg eg st) ∧
      -- GAF02: A3a smoothness, A3b value errors, A3c derivative errors
      ((∀ k : Fin 4, ContMDiff W.model
          𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ∞
          (C.toChain.stage k)) ∧
        (∀ (k : Fin 3) (p : W.Carrier),
          ‖C.toChain.stage k.succ p - S.boundaryOriginalMap p‖ < c k * S.rho p) ∧
        (∀ k : Fin 3, ∃ Hd : ℝ, Hd < c k ∧ ∀ (p : W.Carrier) (v : TangentSpace W.model p),
          ‖mvfderiv W.model (C.toChain.stage k.succ) p v -
              mvfderiv W.model S.boundaryOriginalMap p v‖ ≤ Hd * Real.sqrt (g.inner p v v))) ∧
      -- the original zero-marker bound (A3d: ZM, AM0 at every prefix, AM0 on the segment)
      ((∀ (k : Fin 3) (q : W.pieceInterior ⊤) (m : S.MarkerIdx_BAUGC),
          S.rho (S.markerCentre_BAUGC m) < S.rho q / 16 →
          S.markerCLM_BAUGC m (C.toChain.stage k.succ q.val) = 0) ∧
        (∀ (k : Fin 4) (m : S.MarkerIdx_BAUGC) (p : W.pieceInterior ⊤),
          S.intCutoff_BAUGA (S.markerTag_BAUGC m) p = 0 →
          |blockMarkerCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
              (Sum.inl (S.markerTag_BAUGC m)) (C.toChain.stage k p.val)| ≤
            S.rho (S.markerCentre_BAUGC m) / 32) ∧
        (∀ (m : S.MarkerIdx_BAUGC) (p : W.pieceInterior ⊤),
          S.intCutoff_BAUGA (S.markerTag_BAUGC m) p = 0 →
          ∀ z ∈ segment ℝ (S.boundaryOriginalMap p.val) (C.toChain.E p.val),
          |blockMarkerCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
              (Sum.inl (S.markerTag_BAUGC m)) z| ≤ S.rho (S.markerCentre_BAUGC m) / 32)) ∧
      -- the scale exit (A3f) and EDP01's early scale constant (A3f')
      ((∀ p : W.Carrier, C.toChain.scale p = S.scaleMarker_BIF (C.toChain.g₁ p) ∧
          |C.toChain.scale p - S.rho p| < c 0 * S.rho p ∧ 0 < C.toChain.scale p) ∧
        (100 ≤ 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) ∧
          ∀ p : W.Carrier, MDifferentiableAt W.model 𝓘(ℝ, ℝ) C.toChain.scale p ∧
            |C.toChain.scale p - S.rho p| ≤
              100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * S.rho p ∧
            (∀ v : TangentSpace W.model p, |mvfderiv W.model C.toChain.scale p v| ≤
              100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Real.sqrt (g.inner p v v)) ∧
            0 < C.toChain.scale p)) ∧
      -- the kept blocks: A0 (earlier interior blocks are kept), A3g (kept orthogonal coordinates)
      ((∀ (st : Fin 3) (a : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →
            BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
          (z : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) (t : S.IntTag_BAUGA),
          t ∉ S.stageTagsV2_BAUGD st →
          (actualSlotsV2_BAUGD S).adjust st a z (Sum.inl t) = z (Sum.inl t)) ∧
        (∀ (st : Fin 3) (z : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)),
          C.toChain.Ψ st z - z ∈ (actualSlotsV2_BAUGD S).stageQ st)) ∧
      -- A3i and the early derivative bound of `F_∂`
      (Continuous C.toChain.heightRatio ∧
        ∀ (p : W.Carrier) (v : TangentSpace W.model p),
          ‖mvfderiv W.model S.boundaryOriginalMap p v‖ ≤ bder * Real.sqrt (g.inner p v v)) ) ∧
    (-- GAF02: sources, bases, submersion rank
      ((∀ st : Fin 3, st ≠ 1 → IsOpen (Bs.source st)) ∧
        (∀ st : Fin 3, C.toChain.stageMap st '' Bs.source st = Bs.base st) ∧
        Bs.source 0 = C.toChain.stageMap 0 ⁻¹' Bs.base 0 ∧
        Bs.source 2 = C.toChain.stageMap 2 ⁻¹' Bs.base 2 ∧
        Bs.source 1 = C.toChain.stageMap 1 ⁻¹' Bs.base 1 ∩ {p | C.toChain.heightRatio p ≤ 4 * Δ} ∧
        (∀ st : Fin 3, ∀ p ∈ Bs.source st, Module.finrank ℝ (LinearMap.range
          ((mvfderiv W.model (C.toChain.stageMap st) p :
            TangentSpace W.model p →L[ℝ]
              BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
            TangentSpace W.model p →ₗ[ℝ]
              BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))) = gafStageDim st)) ∧
      -- one-sheet bases and no merging: `f_j = Θ_j ∘ f_j⁰`, `Θ_j` an embedding of the native base
      ((∀ st : Fin 3, Bs.base st = Bs.later st '' Bs.nativeBase st) ∧
        (∀ (st : Fin 3) (p : W.Carrier),
          C.toChain.stageMap st p = Bs.later st (C.toChain.nativeStageMap_BIFc st p)) ∧
        (∀ st : Fin 3, IsEmbedding (fun x : Bs.nativeBase st => Bs.later st x)) ∧
        (∀ st : Fin 3, InjOn (Bs.later st) (Bs.nativeBase st))) ∧
      -- GAF06: whole-preimage localization
      (letI := inducedMetricSpace S.completion.metric;
        (∀ p ∈ Bs.source 0, ∃ q : W.pieceInterior ⊤, q.val = p ∧ ∃ j ∈ S.stageCentres_BIF 0,
          dist q j < 200 * S.rho j ∧ ‖S.circleEta_BIF j q‖ < 401 / 100) ∧
        (∀ p ∈ Bs.source 1, ∃ q : W.pieceInterior ⊤, q.val = p ∧ ∃ j ∈ S.stageCentres_BIF 1,
          dist q j < 100 * Δ * S.rho j ∧ |S.edgeEta_BIF j q| < 401 / 100 * Δ ∧
            S.edgeHeightRaw q < 401 / 100 * Δ) ∧
        (∀ p ∈ Bs.source 2, ∃ q : W.pieceInterior ⊤, q.val = p ∧ ∃ j ∈ S.stageCentres_BIF 2,
          dist q j < 1000000 * Δ * S.rho j ∧ |S.slimEta_BIF j q| < 401 / 100 * (10 ^ 5 * Δ))) ∧
      -- GAF07: the original circle / edge / slim sets lie in the sources
      (letI := inducedMetricSpace S.completion.metric;
        (∀ q : W.pieceInterior ⊤, ∀ j ∈ S.stageCentres_BIF 0, dist q j < 200 * S.rho j →
          ‖S.circleEta_BIF j q‖ ≤ 7 / 2 → q.val ∈ Bs.source 0) ∧
        (∀ q : W.pieceInterior ⊤, ∀ j ∈ S.stageCentres_BIF 1, dist q j < 100 * Δ * S.rho j →
          |S.edgeEta_BIF j q| ≤ 7 / 2 * Δ → S.edgeHeightRaw q ≤ 7 / 2 * Δ →
            q.val ∈ interior (Bs.source 1)) ∧
        (∀ q : W.pieceInterior ⊤, ∀ j ∈ S.stageCentres_BIF 2, dist q j < 1000000 * Δ * S.rho j →
          |S.slimEta_BIF j q| ≤ 350000 * Δ → q.val ∈ Bs.source 2)) ∧
      -- GAF07: proper whole circle, slim and edge-disk fibres
      ((∀ (st : Fin 3) (Kc : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))),
          Kc ⊆ Bs.base st → IsCompact Kc →
            IsCompact (Bs.source st ∩ C.toChain.stageMap st ⁻¹' Kc)) ∧
        (∀ y ∈ Bs.base 0, Nonempty (Bs.fibre 0 y ≃ₜ Circle)) ∧
        (∀ y ∈ Bs.base 2, Nonempty (Bs.fibre 2 y ≃ₜ Metric.sphere (0 : E3) 1) ∨
          Nonempty (Bs.fibre 2 y ≃ₜ Circle × Circle)) ∧
        (∀ y ∈ Bs.base 1, ∃ ed : Bs.fibre 1 y ≃ₜ ClosedCell 2,
          Subtype.val '' (ed ⁻¹' {x : ClosedCell 2 | ‖x.1‖ = 1}) =
            Bs.fibre 1 y ∩ {p | C.toChain.heightRatio p = 4 * Δ})) ∧
      -- all sources, hence all compact fibre traces, lie in `{D > 5} ⊆ int M`
      (∀ st : Fin 3, Bs.source st ⊆ {p | ENNReal.ofReal 5 < distanceToBoundary W g p}) )  := by
  obtain ⟨C, hact⟩ := h
  exact ⟨C, hact, (hA4 C).choose, (hA4 C).choose_spec, C.bcg03_row_BGR (hA4 C).choose_spec⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
