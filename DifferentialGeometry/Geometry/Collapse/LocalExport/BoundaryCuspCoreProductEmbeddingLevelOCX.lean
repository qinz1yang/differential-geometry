import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoreProductEmbeddingOCX

/-!
# BCG06 E4c with the level identity of the product (lane O-CROSS, G2b)

Request of S-BCG-ROWS2 (port half-collar from the SAME product): the concrete E4c of
`BoundaryCuspCoreProductEmbeddingOCX` together with the affine level identity
`G_i (D p) = a + (40 - a) p₂` (`a = levelBase i < 40`) of BCG6-K's modified level `G_i`, for which
`C_i = {G_i ≤ 40}`.

* `BoundaryCollarPacket.cuspCore_labelled_product_embedding_level_BCG6K_OCX` (kernel);
* **`BoundaryGaf02ChainE.bcg06_labelled_product_embedding_level_on_chain_OCX`** (chain, E4b's
  premises).
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

universe u

namespace BoundaryCollarPacket

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ}
  {A : ℝ → ℝ} {w₀ ε : ℝ} {P : BoundaryCollarPacket W g K A w₀ ε} {b : Fin P.cusp.count}

/-- **E4c kernel, concrete form with the level identity**: as
`cuspCore_labelled_product_embedding_BCG6K_OCX`, and the modified level `G` of BCG6-K
(`C_b = {G ≤ 40}`) is affine along the product: `G (D p) = a + (40 - a) p₂` with
`a = levelBase b < 40`. -/
theorem cuspCore_labelled_product_embedding_level_BCG6K_OCX (hε : ε ≤ 1 / 1000)
    {u v : Fin P.cusp.count → W.Carrier → ℝ} (hu : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (u b))
    {εd c₃ : ℝ} (hεd : εd < 1 / 1000000) (hc₃ : 0 ≤ c₃) (hR : 80 * εd + 102 / 100 * c₃ < 1)
    (hBI : ∀ x, |u b x - (P.block b x).1| < εd ∧ |v b x - (P.block b x).2| < εd)
    (hBFM : ∀ x ∈ P.safeBand_BAUGA b, v b x = 1)
    (hBD : ∀ x ∈ P.collarBand_BAUGA b, 38 ≤ P.height b x → P.height b x ≤ 42 →
      ∀ w : TangentSpace W.model x, |mvfderiv W.model (fun y => u b y - P.height b y) x w| ≤
        c₃ * Real.sqrt (g.inner x w w)) :
    ∃ cs : ChartedSpace (EuclideanHalfSpace 3) (P.cuspCore_BCG6K b u v),
      letI := cs
      IsManifold (𝓡∂ 3) ∞ (P.cuspCore_BCG6K b u v) ∧
      ContMDiff (𝓡∂ 3) W.model ∞ (fun y : P.cuspCore_BCG6K b u v => (y : W.Carrier)) ∧
      (∀ y : P.cuspCore_BCG6K b u v, (𝓡∂ 3).IsBoundaryPoint y ↔
        ((y : W.Carrier) ∈ P.cusp.component b ∨ (y : W.Carrier) ∈ P.cuspFront_BCG6K b u v)) ∧
      ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) (𝓡∂ 3) (Torus × Icc (0 : ℝ) 1)
          (P.cuspCore_BCG6K b u v) ∞,
        (∀ p, (D p : W.Carrier) ∈ P.cusp.component b ↔ (p.2 : ℝ) = 0) ∧
        (∀ p, (D p : W.Carrier) ∈ P.cuspFront_BCG6K b u v ↔ (p.2 : ℝ) = 1) ∧
        IsSmoothEmbedding (torusModel.prod (𝓡∂ 1)) W.model ∞ (fun p => (D p : W.Carrier)) ∧
        ∃ a : ℝ, a < 40 ∧
          ∀ p, P.coreLevel_BCG6K b (u b) (D p : W.Carrier) = a + (40 - a) * (p.2 : ℝ) := by
  have ha39 := P.levelBase_lt_thirtyNine_BCG6K b
  have har : P.levelBase b < 40 := by linarith
  have hF := P.contMDiff_coreLevel_BCG6K b hu
  have hreg : ∀ x, P.coreLevel_BCG6K b (u b) x ≤ 40 →
      mfderiv W.model 𝓘(ℝ, ℝ) (P.coreLevel_BCG6K b (u b)) x ≠ 0 := fun x hx =>
    P.mfderiv_coreLevel_ne_zero_BCG6K b hε hu hc₃ hR (fun y _ => (hBI y).1) hBD hx
  have hr := P.exists_coreLevel_eq_forty_BCG6K b hu
  have hXa : ∀ x ∈ P.cusp.component b, P.coreLevel_BCG6K b (u b) x = P.levelBase b :=
    fun x hx => P.coreLevel_eq_levelBase_BCG6K b (u b) hx
  have hbd : ∀ x, W.model.IsBoundaryPoint x → P.coreLevel_BCG6K b (u b) x ≤ 40 →
      x ∈ P.cusp.component b := fun x hx hle =>
    P.mem_component_of_isBoundaryPoint_BCG6K hεd hBI hBFM hx hle
  obtain ⟨cs, hman, hval, hbdy, D, hDF, hDX, hemb⟩ :=
    (P.cusp.collar b).exists_sublevel_diffeomorph_torus_Icc_embedding_OCX har hF hreg hr hXa hbd
  rw [P.cuspCore_eq_BCG6K hεd hBI hBFM, P.cuspFront_eq_BCG6K hεd hBI hBFM]
  have : Fact (P.levelBase b < 40) := ⟨har⟩
  let cs' : ChartedSpace (EuclideanHalfSpace 3) {x | P.coreLevel_BCG6K b (u b) x ≤ 40} := cs
  let := cs'
  refine ⟨cs', hman, hval, hbdy,
    unitCylinderDiffeomorphOfProduct (P.levelBase b) 40 (Diffeomorph.refl torusModel Torus _) D,
    fun p => ?_, fun p => ?_, ?_, P.levelBase b, har, fun p => ?_⟩
  · rw [unitCylinderDiffeomorphOfProduct_apply, hDX, affineIntervalDiffeomorph_apply]
    constructor
    · intro h
      have h1 : (40 - P.levelBase b) * (p.2 : ℝ) = 0 := by linarith
      rcases mul_eq_zero.mp h1 with h2 | h2
      · linarith
      · exact h2
    · intro h
      rw [h]
      ring
  · rw [unitCylinderDiffeomorphOfProduct_apply, Set.mem_ofPred_eq, hDF,
      affineIntervalDiffeomorph_apply]
    constructor
    · intro h
      have h1 : (40 - P.levelBase b) * ((p.2 : ℝ) - 1) = 0 := by linarith
      rcases mul_eq_zero.mp h1 with h2 | h2
      · linarith
      · linarith
    · intro h
      rw [h]
      ring
  · exact hemb.comp_diffeomorph ((Diffeomorph.refl torusModel Torus ∞).prodCongr
      (affineIntervalDiffeomorph (P.levelBase b) 40))
  · rw [unitCylinderDiffeomorphOfProduct_apply, hDF, affineIntervalDiffeomorph_apply]
    ring

end BoundaryCollarPacket

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

/-- **E4c on the enhanced chain, concrete form with the level identity**: as
`bcg06_labelled_product_embedding_on_chain_OCX`, and BCG6-K's level `G_i` (`C_i = {G_i ≤ 40}`) is
affine along the SAME product `D`: `G_i (D p) = a + (40 - a) p₂`, `a < 40` (input of the port
half-collar `Φ(T² × [0, 1/2)) = {G_i < (a + 40)/2}`). Premises of E4b. -/
theorem bcg06_labelled_product_embedding_level_on_chain_OCX {rd : ℝ} (hrd : 0 < rd)
    (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    ∀ i : Fin S.packet.cusp.count,
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
        IsSmoothEmbedding (torusModel.prod (𝓡∂ 1)) W.model ∞ (fun p => (D p : W.Carrier)) ∧
        ∃ a : ℝ, a < 40 ∧ ∀ p,
          S.packet.toBoundaryCollarPacket.coreLevel_BCG6K i (chainBoundaryU_BCG6K C.toChain.E i)
            (D p : W.Carrier) = a + (40 - a) * (p.2 : ℝ) :=
  fun i =>
    S.packet.toBoundaryCollarPacket.cuspCore_labelled_product_embedding_level_BCG6K_OCX (b := i)
      (u := chainBoundaryU_BCG6K C.toChain.E) (v := chainBoundaryV_BCG6K C.toChain.E)
      (cuspTolerance_le_thousandth_BCUSP1 _ _ _)
      (contMDiff_chainBoundaryU_BCG6K (C.stage_smooth_BAUGD 3) i)
      (epsBoundary_lt_BGR hrd hrdc) C.toChain.c_two_pos_BCG6K.le
      (BoundaryCollarPacket.register_R_BCG6K (epsBoundary_lt_BGR hrd hrdc)
        C.validity.c_two_lt_E4)
      ((C.bcg04_row_BGR hrd hprem).2.1 3 i) ((C.bcg05_row_BGR hθ hrd hrd4 hprem).1 3 i)
      (C.bcg04_derivative_on_boundary_chain_BGR i)

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
