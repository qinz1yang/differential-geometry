import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoreChainEBGR
import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.InnerCollarEmbeddingOCX
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificateParts

/-!
# BCG06 E4c: the SAME whole-core product as a smooth embedding into `W` (lane O-CROSS, G2)

Target E4c of `TargetsBoundary-v3.1.lean.txt` (D74-16, draft 74 §3.2): the rows' cusp piece needs
the labelled product `T² × [0, 1] ≅ C_b` as a smooth embedding into `W` (model
`torusModel.prod (𝓡∂ 1)` into `W.model`), end `0` onto the boundary component `∂_b W`, end `1` onto
the front `H_b`. BCG6-K's E6 product (`cuspCore_labelled_product_BCG6K`) is the same kernel
(`CuspEmbedding.exists_sublevel_diffeomorph_torus_Icc` at the modified level `G`, levels
`a = levelBase b < 40 = r`) read through lane SUB-BDY's sublevel structure; the embedding is that
product followed by the sublevel inclusion, which is a smooth embedding `𝓡∂ 3 → 𝓡∂ 3`
(`boundarySublevel_isSmoothEmbedding_val_OCX`: front points by the vector-chart kernel of
`CrossModelHalfSpaceOCX`), and the linear model change `halfCollarLinearEquiv_OCX`.

* `BoundaryCollarPacket.cuspCore_product_embedding_BCG6K_OCX` (kernel, BCG6-K's hypotheses);
* `range_iccEnd_eq_OCX` (end ranges from the end labels);
* **`BoundaryGaf02ChainE.bcg06_product_embedding_on_chain_OCX`** (E4c on the enhanced chain;
  premises of E4b `bcg06_coreSpec_on_chain_BGR`; the frozen premise `cadj ≤ 10⁻⁵` is unused —
  strengthening, verbatim form as an `example`).
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

/-- **End ranges from end labels**: if `Φ` maps onto `C`, `Bd ⊆ C`, and `Φ p ∈ Bd ↔ p₂ = s`, then
`Φ (·, s)` maps onto `Bd`. -/
theorem range_iccEnd_eq_OCX {T X : Type*} {Φ : T × Icc (0 : ℝ) 1 → X} {C Bd : Set X}
    (hrange : range Φ = C) (hBd : Bd ⊆ C) (s : Bool)
    (hlab : ∀ p, Φ p ∈ Bd ↔ (p.2 : ℝ) = (iccEnd s : ℝ)) :
    (range fun t => Φ (t, iccEnd s)) = Bd := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact (hlab _).mpr rfl
  · intro hx
    have hxC : x ∈ range Φ := hrange ▸ hBd hx
    obtain ⟨p, rfl⟩ := hxC
    refine ⟨p.1, ?_⟩
    have hp : p.2 = iccEnd s := Subtype.ext ((hlab p).mp hx)
    change Φ (p.1, iccEnd s) = Φ p
    rw [← hp]

namespace BoundaryCollarPacket

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ}
  {A : ℝ → ℝ} {w₀ ε : ℝ} {P : BoundaryCollarPacket W g K A w₀ ε} {b : Fin P.cusp.count}

/-- **E4c kernel (BCG6-K's hypotheses)**: the labelled whole-core product as a smooth embedding
`T² × [0, 1] → W` onto `C_b`, `∂_b W` at end `0`, the front `H_b` at end `1`. -/
theorem cuspCore_product_embedding_BCG6K_OCX (hε : ε ≤ 1 / 1000)
    {u v : Fin P.cusp.count → W.Carrier → ℝ} (hu : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (u b))
    {εd c₃ : ℝ} (hεd : εd < 1 / 1000000) (hc₃ : 0 ≤ c₃) (hR : 80 * εd + 102 / 100 * c₃ < 1)
    (hBI : ∀ x, |u b x - (P.block b x).1| < εd ∧ |v b x - (P.block b x).2| < εd)
    (hBFM : ∀ x ∈ P.safeBand_BAUGA b, v b x = 1)
    (hBD : ∀ x ∈ P.collarBand_BAUGA b, 38 ≤ P.height b x → P.height b x ≤ 42 →
      ∀ w : TangentSpace W.model x, |mvfderiv W.model (fun y => u b y - P.height b y) x w| ≤
        c₃ * Real.sqrt (g.inner x w w)) :
    ∃ Φ : Torus × Icc (0 : ℝ) 1 → W.Carrier,
      IsSmoothEmbedding (torusModel.prod (𝓡∂ 1)) W.model ∞ Φ ∧
        range Φ = P.cuspCore_BCG6K b u v ∧
        (∀ p, Φ p ∈ P.cusp.component b ↔ (p.2 : ℝ) = 0) ∧
        (∀ p, Φ p ∈ P.cuspFront_BCG6K b u v ↔ (p.2 : ℝ) = 1) ∧
        P.cusp.component b ⊆ P.cuspCore_BCG6K b u v ∧
        P.cuspFront_BCG6K b u v ⊆ P.cuspCore_BCG6K b u v := by
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
  obtain ⟨Φ, hΦ, hrange, hΦF, hΦX⟩ :=
    (P.cusp.collar b).exists_sublevel_embedding_torus_unitIcc_OCX har hF hreg hr hXa hbd
  rw [P.cuspCore_eq_BCG6K hεd hBI hBFM, P.cuspFront_eq_BCG6K hεd hBI hBFM]
  refine ⟨Φ, hΦ, hrange, hΦX, fun p => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · change P.coreLevel_BCG6K b (u b) (Φ p) = 40 ↔ _
    rw [hΦF]
    constructor
    · intro h
      have h1 : (40 - P.levelBase b) * ((p.2 : ℝ) - 1) = 0 := by linarith
      rcases mul_eq_zero.mp h1 with h2 | h2
      · linarith
      · linarith
    · intro h
      rw [h]
      ring
  · change P.coreLevel_BCG6K b (u b) x ≤ 40
    rw [hXa x hx]
    exact har.le
  · exact le_of_eq hx

/-- **E4c kernel, concrete form** (BCG6-K's `cuspCore_labelled_product_BCG6K` on the SAME charted
space and product, plus the smooth embedding `val ∘ D` into `W`). -/
theorem cuspCore_labelled_product_embedding_BCG6K_OCX (hε : ε ≤ 1 / 1000)
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
        IsSmoothEmbedding (torusModel.prod (𝓡∂ 1)) W.model ∞ (fun p => (D p : W.Carrier)) := by
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
    fun p => ?_, fun p => ?_, ?_⟩
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

/-- **E4c the SAME product as a smooth embedding into `W`** (D74-16): for every boundary component
`i`, a smooth embedding `Φ : T² × [0, 1] → W` with `range Φ = C_b`, end `0` onto `∂_b W` and end
`1` onto the front `H_b` (premises of E4b; `cadj ≤ 10⁻⁵` unused). -/
theorem bcg06_product_embedding_on_chain_OCX {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    ∀ i : Fin S.packet.cusp.count, ∃ Φ : Torus × Icc (0 : ℝ) 1 → W.Carrier,
      IsSmoothEmbedding (torusModel.prod (𝓡∂ 1)) W.model ∞ Φ ∧
        range Φ = C.toChain.cuspCore_BIF i ∧
        (range fun t => Φ (t, iccEnd false)) = S.packet.cusp.component i ∧
        (range fun t => Φ (t, iccEnd true)) = C.toChain.cuspFront_BIF i := by
  intro i
  obtain ⟨Φ, hΦ, hrange, h0, h1, hB, hF⟩ :=
    S.packet.toBoundaryCollarPacket.cuspCore_product_embedding_BCG6K_OCX (b := i)
      (u := chainBoundaryU_BCG6K C.toChain.E) (v := chainBoundaryV_BCG6K C.toChain.E)
      (cuspTolerance_le_thousandth_BCUSP1 _ _ _)
      (contMDiff_chainBoundaryU_BCG6K (C.stage_smooth_BAUGD 3) i)
      (epsBoundary_lt_BGR hrd hrdc) C.toChain.c_two_pos_BCG6K.le
      (BoundaryCollarPacket.register_R_BCG6K (epsBoundary_lt_BGR hrd hrdc)
        C.validity.c_two_lt_E4)
      ((C.bcg04_row_BGR hrd hprem).2.1 3 i) ((C.bcg05_row_BGR hθ hrd hrd4 hprem).1 3 i)
      (C.bcg04_derivative_on_boundary_chain_BGR i)
  refine ⟨Φ, hΦ, hrange, range_iccEnd_eq_OCX hrange hB false (fun p => ?_),
    range_iccEnd_eq_OCX hrange hF true (fun p => ?_)⟩
  · rw [h0 p]
    rfl
  · rw [h1 p]
    rfl

/-- The frozen E4c statement verbatim (with the unused premise `cadj ≤ 10⁻⁵`). -/
example : ∀ {rd : ℝ}, 0 < rd → rd < 1 / 10000 → 20 * (c 2 + 1) * rd < 1 / 1000000 →
    1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2 →
    cadj ≤ 1 / 100000 → θ < 1 / 100 →
    ∀ i : Fin S.packet.cusp.count, ∃ Φ : Torus × Icc (0 : ℝ) 1 → W.Carrier,
      IsSmoothEmbedding (torusModel.prod (𝓡∂ 1)) W.model ∞ Φ ∧
        range Φ = C.toChain.cuspCore_BIF i ∧
        (range fun t => Φ (t, iccEnd false)) = S.packet.cusp.component i ∧
        (range fun t => Φ (t, iccEnd true)) = C.toChain.cuspFront_BIF i :=
  fun hrd hrd4 hrdc hprem _ hθ => C.bcg06_product_embedding_on_chain_OCX hrd hrd4 hrdc hprem hθ

/-- **E4c on the enhanced chain, concrete form** (the hypothesis `hE` of BD0's
`cuspCoresData_of_same_product_BGR`): for every component, the SAME charted structure on `C_b`
(manifold, smooth inclusion, boundary `∂_b W ∪ H_b`) and the SAME labelled product `D`, with
`val ∘ D` a smooth embedding into `W`. Premises of E4b. -/
theorem bcg06_labelled_product_embedding_on_chain_OCX {rd : ℝ} (hrd : 0 < rd)
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
        IsSmoothEmbedding (torusModel.prod (𝓡∂ 1)) W.model ∞ (fun p => (D p : W.Carrier)) :=
  fun i =>
    S.packet.toBoundaryCollarPacket.cuspCore_labelled_product_embedding_BCG6K_OCX (b := i)
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
