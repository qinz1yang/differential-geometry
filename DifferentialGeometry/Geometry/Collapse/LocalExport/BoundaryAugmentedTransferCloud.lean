import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAugmentedTransferNormal

/-!
# The transfer layer, field `cloudy` (lane BAUG-C)

The spec field `cloudy` of `BoundaryEnhancedPlaneSpecV3` (FC27's (CS) for every selection of
preimages) for the port table `portTable_BAUGC`, uniform in the stage, from the port clauses (M),
(OWN), (TG value), (SEL), (LOC), (COV), (PRE) of `PortTargets v3.1` called at `(Γ, 5Σ/4, e')`
(dry-run table in `build-logs/resume/state-BAUG-C.md`).

* generic kernels `augmented_cloud_test_empty_BAUGC` (`J_∂(a) = ∅`) and
  `augmented_bm_cloud_test_list_BAUGC` (one statement for every subsingleton list, `C = C_j + 2P_*`,
  `e = e' + 2P_*θ`);
* supply facts `augIntProj_stageProj_boundaryOriginalMap_BAUGC`, `stageProj_boundaryOriginalMap_inr_BAUGC`,
  `rho_ratio_of_dist_lt_BAUGC` (`3ρ(a)/4 ≤ ρ(q) ≤ 5ρ(a)/4` on `D_a`),
  `block_eq_boundaryBlock_of_mem_BAUGC`, `block_eq_zero_of_notMem_BAUGC`;
* `cloud_local_BAUGC` (FC03 localization from (LOC) + (OWN)), `cloudy_at_point_BAUGC` (abstract plane),
  `portTable_plane_eq_model_BAUGC`;
* **`portTable_cloudy_BAUGC`**: the field `cloudy` of the port table;
* consumer `transfer_numbers_BAUGC`: the numeric premises of the transfer (`cloudy`, `normal`) and of
  the port called at `5Σ/4` from ProducerDP v3's numbers (`Σ < Γ/250`, `Σ < Γ³/(125(C_j + 2P_*))`,
  `e < ΓΣ/100`, `16P_*θ ≤ e`).
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
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section Kernel

variable {M ι κ E : Type*} [Fintype ι] [Fintype κ] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **(CS) for the augmented model with an empty list** (`J_∂(a) = ∅`): the closed graph test for
`Φ^∂ = ι_int ∘ Ψ` with the left inverse `Pc ∘ pr_int`, when every boundary slot of the source map
vanishes on the source set. -/
theorem augmented_cloud_test_empty_BAUGC (F : M → BlockSpace (fun _ : ι ⊕ κ => ℝ²))
    (η : M → E) (D : Set M) (Ψ : E → BlockSpace (fun _ : ι => ℝ²)) (Φb : κ → E → ℝ × ℝ)
    (Pc : BlockSpace (fun _ : ι => ℝ²) →L[ℝ] E) (hPc : ∀ z, ‖Pc z‖ ≤ ‖z‖)
    (hgraph : ∀ u, Pc (Ψ u) = u) (T : Set (BlockSpace (fun _ : ι ⊕ κ => ℝ²)))
    {x : BlockSpace (fun _ : ι ⊕ κ => ℝ²)} (hx : x ∈ T) {c r Γ sg Cint eint : ℝ} (hc : 0 < c)
    (hΓ : 0 < Γ) (hΓ1 : Γ < 1) (hsg : 0 < sg) (hsgΓ : sg < Γ / 200) (hCint : 0 < Cint)
    (hsgC : sg < Γ ^ 3 / (100 * Cint)) (heint : 0 ≤ eint) (heΓ : eint < Γ * sg / 100)
    (hrlo : 3 * sg / 4 ≤ r / c) (hrhi : r / c ≤ 5 * sg / 4)
    (hΨreg : ∀ u ∈ closedBall (Pc (augIntProjCLM_BAUGC (c⁻¹ • x))) (r / c / Γ),
      ContDiffAt ℝ 2 Ψ u)
    (hΨ2 : ∀ u ∈ closedBall (Pc (augIntProjCLM_BAUGC (c⁻¹ • x))) (r / c / Γ),
      ‖iteratedFDeriv ℝ 2 Ψ u‖ ≤ Cint)
    (hlocal : ∀ y ∈ (fun z => c⁻¹ • z) '' T ∩ closedBall (c⁻¹ • x) (r / c / Γ),
      ∃ q ∈ D, c⁻¹ • F q = y ∧ Pc (augIntProjCLM_BAUGC y) = η q)
    (hzero : ∀ q ∈ D, ∀ b, F q (Sum.inr b) = 0)
    (hint : ∀ q ∈ D, ‖augIntProjCLM_BAUGC (c⁻¹ • F q) - Ψ (η q)‖ ≤ eint)
    (hcover : ∀ u ∈ closedBall (Pc (augIntProjCLM_BAUGC (c⁻¹ • x))) (r / c / Γ),
      ∃ q ∈ D, η q = u ∧ F q ∈ T) :
    hausdorffEDist (T ∩ ball x (r / Γ))
      ((AffineSubspace.mk' x (fderiv ℝ (augmentedModel_BAUGC Ψ ∅ Φb)
          (Pc (augIntProjCLM_BAUGC (c⁻¹ • x)))).range :
          Set (BlockSpace (fun _ : ι ⊕ κ => ℝ²))) ∩ ball x (r / Γ)) ≤
        ENNReal.ofReal (Γ * r) := by
  classical
  have hmodel : augmentedModel_BAUGC Ψ ∅ Φb = fun u => augIntInclCLM_BAUGC (κ := κ) (Ψ u) :=
    augmentedModel_empty_BAUGC Ψ Φb
  refine cloud_test_of_graph_coverage_BAUGC F η D (augmentedModel_BAUGC Ψ ∅ Φb)
    (Pc.comp augIntProjCLM_BAUGC) (norm_comp_augIntProj_le_BAUGC Pc hPc)
    (comp_augIntProj_augmentedModel_BAUGC Pc hgraph ∅ Φb) T hx hc hΓ hΓ1 hsg hsgΓ hCint hsgC heint
    heΓ hrlo hrhi (fun u hu => ?_) (fun u hu => ?_) hlocal (fun q hq => ?_) hcover
  · rw [hmodel]
    exact (augIntInclCLM_BAUGC (ι := ι) (κ := κ)).contDiff.contDiffAt.comp u (hΨreg u hu)
  · rw [hmodel]
    refine ((augIntInclCLM_BAUGC (ι := ι) (κ := κ)).norm_iteratedFDeriv_comp_left (hΨreg u hu)
      le_rfl).trans ?_
    calc ‖augIntInclCLM_BAUGC (ι := ι) (κ := κ)‖ * ‖iteratedFDeriv ℝ 2 Ψ u‖ ≤
          1 * Cint :=
        mul_le_mul norm_augIntInclCLM_le_BAUGC (hΨ2 u hu) (norm_nonneg _) zero_le_one
      _ = Cint := one_mul _
  · rw [dist_eq_norm, norm_eq_proj_of_slots_zero_BAUGC _ fun b => ?_, map_sub,
      augIntProj_augmentedModel_BAUGC]
    · exact hint q hq
    · rw [PiLp.sub_apply, PiLp.smul_apply, hzero q hq b, smul_zero, augmentedModel_apply_inr_BAUGC,
        augmentedBlocks_of_notMem_BAUGC Φb (Set.notMem_empty b), Pi.zero_apply, map_zero, sub_zero]

/-- **(CS) for the augmented (BM) model on a whole support list** (`J_∂(a)` a subsingleton; one
statement for `J = ∅` and `J = {b₀}`): the interior inputs, the vanishing of unlisted slots, the
listed slot `F_b = slot(𝓑(t_b))` and BCG02's value clause give the test with
`C = C_int + 2P_*`, `e = e_int + 2P_*ϑ` (`R ≤ 1` when `J ≠ ∅`). -/
theorem augmented_bm_cloud_test_list_BAUGC (F : M → BlockSpace (fun _ : ι ⊕ κ => ℝ²))
    (η : M → E) (D : Set M) (Ψ : E → BlockSpace (fun _ : ι => ℝ²)) (J : Set κ)
    (hJ : J.Subsingleton) (cb : κ → ℝ) {R : ℝ} (hR : 0 < R) (hR1 : J.Nonempty → R ≤ 1)
    (Ar : κ → E →L[ℝ] ℝ) (z₀ : E) (hA : ∀ b ∈ J, ‖Ar b‖ ≤ 1)
    (Pc : BlockSpace (fun _ : ι => ℝ²) →L[ℝ] E) (hPc : ∀ z, ‖Pc z‖ ≤ ‖z‖)
    (hgraph : ∀ u, Pc (Ψ u) = u) (T : Set (BlockSpace (fun _ : ι ⊕ κ => ℝ²)))
    {x : BlockSpace (fun _ : ι ⊕ κ => ℝ²)} (hx : x ∈ T) {r Γ sg Cint eint ϑ : ℝ}
    (hΓ : 0 < Γ) (hΓ1 : Γ < 1) (hsg : 0 < sg) (hsgΓ : sg < Γ / 200) (hCint : 0 < Cint)
    (hsgC : sg < Γ ^ 3 / (100 * (Cint + 2 * bmConst_BAUGC))) (heint : 0 ≤ eint) (hϑ : 0 ≤ ϑ)
    (heΓ : eint + 2 * (bmConst_BAUGC * ϑ) < Γ * sg / 100)
    (hrlo : 3 * sg / 4 ≤ r / R) (hrhi : r / R ≤ 5 * sg / 4)
    (hΨreg : ∀ u ∈ closedBall (Pc (augIntProjCLM_BAUGC (R⁻¹ • x))) (r / R / Γ),
      ContDiffAt ℝ 2 Ψ u)
    (hΨ2 : ∀ u ∈ closedBall (Pc (augIntProjCLM_BAUGC (R⁻¹ • x))) (r / R / Γ),
      ‖iteratedFDeriv ℝ 2 Ψ u‖ ≤ Cint)
    (hlocal : ∀ y ∈ (fun z => R⁻¹ • z) '' T ∩ closedBall (R⁻¹ • x) (r / R / Γ),
      ∃ q ∈ D, R⁻¹ • F q = y ∧ Pc (augIntProjCLM_BAUGC y) = η q)
    (hzero : ∀ q ∈ D, ∀ b ∉ J, F q (Sum.inr b) = 0)
    (hint : ∀ q ∈ D, ‖augIntProjCLM_BAUGC (R⁻¹ • F q) - Ψ (η q)‖ ≤ eint)
    (t : κ → M → ℝ)
    (hslotF : ∀ q ∈ D, ∀ b ∈ J, F q (Sum.inr b) = planeBlockEmbed_BAUGA (boundaryBlock (t b q)))
    (hval : ∀ q ∈ D, ∀ b ∈ J, |(t b q - cb b) / R - Ar b (η q - z₀)| < ϑ)
    (hcover : ∀ u ∈ closedBall (Pc (augIntProjCLM_BAUGC (R⁻¹ • x))) (r / R / Γ),
      ∃ q ∈ D, η q = u ∧ F q ∈ T) :
    hausdorffEDist (T ∩ ball x (r / Γ))
      ((AffineSubspace.mk' x (fderiv ℝ (augmentedModel_BAUGC Ψ J (bmBlocks_BAUGC cb R Ar z₀))
          (Pc (augIntProjCLM_BAUGC (R⁻¹ • x)))).range :
          Set (BlockSpace (fun _ : ι ⊕ κ => ℝ²))) ∩ ball x (r / Γ)) ≤
        ENNReal.ofReal (Γ * r) := by
  have hP1 := one_le_bmConst_BAUGC
  by_cases hJn : J.Nonempty
  · obtain ⟨b₀, hb₀⟩ := hJn
    have hR1' := hR1 ⟨b₀, hb₀⟩
    have hJeq : J = {b₀} := hJ.eq_singleton_of_mem hb₀
    subst hJeq
    have hsgC' : sg < Γ ^ 3 / (100 * (Cint + 2 * (R * bmConst_BAUGC))) := by
      refine lt_of_lt_of_le hsgC (div_le_div_of_nonneg_left (by positivity) (by positivity) ?_)
      nlinarith
    exact augmented_bm_cloud_test_BAUGC norm_fderiv_boundaryBlock_le_bmConst_BAUGC
      norm_fderiv_fderiv_boundaryBlock_le_bmConst_BAUGC F η D Ψ cb hR Ar z₀ (hA b₀ rfl) Pc hPc
      hgraph T hx hΓ hΓ1 hsg hsgΓ hCint hsgC' heint hϑ heΓ hrlo hrhi hΨreg hΨ2 hlocal
      (fun q hq b hb => hzero q hq b hb) hint (t b₀) (fun q hq => hslotF q hq b₀ rfl)
      (fun q hq => hval q hq b₀ rfl) hcover
  · rw [Set.not_nonempty_iff_eq_empty] at hJn
    subst hJn
    have hsgC'' : sg < Γ ^ 3 / (100 * Cint) := by
      refine lt_of_lt_of_le hsgC (div_le_div_of_nonneg_left (by positivity) (by positivity) ?_)
      nlinarith
    have heΓ' : eint < Γ * sg / 100 := by nlinarith
    exact augmented_cloud_test_empty_BAUGC F η D Ψ _ Pc hPc hgraph T hx hR hΓ hΓ1 hsg hsgΓ hCint
      hsgC'' heint heΓ' hrlo hrhi hΨreg hΨ2 hlocal
      (fun q hq b => hzero q hq b (Set.notMem_empty b)) hint hcover

end Kernel

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

namespace BoundarySupply

variable (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM)

/-- The interior part of a stage point: `pr_int π_j F_∂(q) = π_{Q_j}(F_int(q))` on `W°`. -/
theorem augIntProj_stageProj_boundaryOriginalMap_BAUGC (Φ : BoundaryInteriorSlots_BIF S)
    (st : Fin 3) (q : W.pieceInterior ⊤) :
    augIntProjCLM_BAUGC (Φ.stageProj st (S.boundaryOriginalMap q.val)) =
      blockRestrict (Φ.stageTags st) (S.interiorMapOn_BAUGA q) := by
  change augIntProjCLM_BAUGC (blockRestrict ((Φ.stageTags st).disjSum Finset.univ)
    (S.boundaryOriginalMap q.val)) = _
  rw [augIntProj_blockRestrict_disjSum_BAUGC, augIntProjCLM_eq_BAUGC,
    S.boundaryOriginalMap_interior_projection, S.interiorMapW_val_BAUGA]

/-- A boundary slot of a stage point is the plane encoding of the collar block. -/
theorem stageProj_boundaryOriginalMap_inr_BAUGC (Φ : BoundaryInteriorSlots_BIF S) (st : Fin 3)
    (p : W.Carrier) (i : Fin S.packet.cusp.count) :
    Φ.stageProj st (S.boundaryOriginalMap p) (Sum.inr i) =
      planeBlockEmbed_BAUGA (S.packet.toBoundaryCollarPacket.block i p) := by
  rw [BoundaryInteriorSlots_BIF.stageProj_inr_BGR]
  rfl

/-- **Slow variation on the reference domains**: `d_ĝ(q, a) < C ρ(a)` with `C ≤ 950000Δ` gives
`3ρ(a)/4 ≤ ρ(q) ≤ 5ρ(a)/4`. -/
theorem rho_ratio_of_dist_lt_BAUGC (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ)
    (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) {q a : W.pieceInterior ⊤} {C : ℝ}
    (hC : C ≤ 950000 * Δ)
    (hq : letI := inducedMetricSpace S.completion.metric; dist q a < C * S.rho a) :
    3 / 4 * S.rho a ≤ S.rho q ∧ S.rho q ≤ 5 / 4 * S.rho a := by
  let _ := inducedMetricSpace S.completion.metric
  obtain ⟨Λ', hΛ'0, -, hΛ'C, hlip'⟩ := S.exists_pos_scale_lipschitz_BAUGC hΛ hΔ hΛΔ
  have hρa := S.rho_pos a
  have hd := S.riemannianEDistOf_le_ofReal_dist_BAUGC q a
  have hCρ : 0 ≤ C * S.rho a := le_trans dist_nonneg hq.le
  have h1 : ENNReal.ofReal |S.rho q - S.rho a| ≤ ENNReal.ofReal (Λ' * (C * S.rho a)) := by
    refine (hlip' q.val a.val).trans ?_
    rw [ENNReal.ofReal_mul hΛ'0.le]
    gcongr
    exact hd.trans (ENNReal.ofReal_le_ofReal hq.le)
  have h2 : |S.rho q - S.rho a| ≤ Λ' * (C * S.rho a) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
  have h3 : Λ' * (C * S.rho a) ≤ S.rho a / 4 := by
    have : Λ' * C ≤ 1 / 4 := le_trans (mul_le_mul_of_nonneg_left hC hΛ'0.le) hΛ'C
    nlinarith
  have h4 := abs_le.mp (h2.trans h3)
  constructor <;> linarith [h4.1, h4.2]

/-- On the reference domain of a listed component the collar block is `𝓑(η_b)`. -/
theorem block_eq_boundaryBlock_of_mem_BAUGC (hsep : S.SeparatedCollarZero_BIF) (hΛ : 0 ≤ Λ)
    (hΔ : 1 ≤ Δ) (hβ1 : 0 < β 1) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000)
    (hreq : β 1 ^ 3 * (1000000 * Δ) < 1) {st : Fin 3} {a q : W.pieceInterior ⊤}
    {i : Fin S.packet.cusp.count} (hi : i ∈ S.boundaryList_BIF st a)
    (hq : letI := inducedMetricSpace S.completion.metric;
      dist q a < stageDomain_BIF Δ st * S.rho a) :
    S.packet.toBoundaryCollarPacket.block i q.val =
      boundaryBlock (S.packet.toBoundaryCollarPacket.height i q.val) := by
  obtain ⟨q', -, hqx, hq2, hq98⟩ :=
    ((S.boundaryList_facts_BAUGC hsep hΛ hΔ hβ1 hΛΔ hreq st a).2 i hi).2 q hq
  have hmem : q.val ∈ (S.packet.toBoundaryCollarPacket.cusp.collar i).toFun ''
      {q : CuspHalfSpace | 2 < q.2.val 0 ∧ q.2.val 0 < 98} := ⟨q', ⟨hq2, hq98⟩, hqx⟩
  exact indicator_of_mem hmem _

/-- Off the list the collar block vanishes on the reference domain. -/
theorem block_eq_zero_of_notMem_BAUGC {st : Fin 3} {a q : W.pieceInterior ⊤}
    {i : Fin S.packet.cusp.count} (hi : i ∉ S.boundaryList_BIF st a)
    (hq : letI := inducedMetricSpace S.completion.metric;
      dist q a < stageDomain_BIF Δ st * S.rho a) :
    S.packet.toBoundaryCollarPacket.block i q.val = 0 :=
  image_eq_zero_of_notMem_tsupport (S.notMem_tsupport_block_of_notMem_BAUGC hi hq)

end BoundarySupply

section CloudParts

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM}

/-- **FC03 localization in the scaled form of the (CS) kernel** from the port clause (LOC) (radius
`ρ_c` in the interior norm) and (OWN) on the core. -/
theorem cloud_local_BAUGC (Φ : BoundaryInteriorSlots_BIF S) (st : Fin 3) {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (eta : W.pieceInterior ⊤ → E) (a : W.pieceInterior ⊤)
    (core : W.pieceInterior ⊤ → Prop) (Pca : BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²) →L[ℝ] E)
    (hOWN : ∀ y, core y →
      Pca ((S.rho a)⁻¹ • blockRestrict (Φ.stageTags st) (S.interiorMapOn_BAUGA y)) = eta y)
    {C ρc r Γ : ℝ} (x : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
    (hLOC : ∀ y ∈ Φ.stageCloudEnlarged st, ‖augIntProjCLM_BAUGC (y - x)‖ ≤ ρc →
      ∃ q : W.pieceInterior ⊤, core q ∧
        (letI := inducedMetricSpace S.completion.metric; dist q a < C * S.rho a) ∧
        Φ.stageProj st (S.boundaryOriginalMap q.val) = y)
    (hr : r / Γ ≤ ρc) :
    ∀ y ∈ (fun z => (S.rho a)⁻¹ • z) '' Φ.stageCloudEnlarged st ∩
        closedBall ((S.rho a)⁻¹ • x) (r / S.rho a / Γ),
      ∃ q ∈ {q : W.pieceInterior ⊤ | core q ∧
          (letI := inducedMetricSpace S.completion.metric; dist q a < C * S.rho a)},
        (S.rho a)⁻¹ • Φ.stageProj st (S.boundaryOriginalMap q.val) = y ∧
          Pca (augIntProjCLM_BAUGC y) = eta q := by
  rintro _ ⟨⟨y', hy', rfl⟩, hyb⟩
  have hρa := S.rho_pos a
  have hd : ‖y' - x‖ ≤ r / Γ := by
    rw [mem_closedBall, dist_eq_norm, ← smul_sub, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hρa.le)] at hyb
    have h1 : ‖y' - x‖ ≤ S.rho a * (r / S.rho a / Γ) := by
      rw [inv_mul_le_iff₀ hρa] at hyb
      exact hyb
    calc ‖y' - x‖ ≤ S.rho a * (r / S.rho a / Γ) := h1
      _ = r / Γ := by field_simp
  obtain ⟨q, hq, hqa, hqy⟩ := hLOC y' hy' ((norm_augIntProj_le_BAUGC _).trans (hd.trans hr))
  refine ⟨q, ⟨hq, hqa⟩, by rw [hqy], ?_⟩
  rw [← hqy, map_smul, S.augIntProj_stageProj_boundaryOriginalMap_BAUGC Φ st q]
  exact hOWN q hq

/-- **The (CS) test of the port table at one cloud point** (abstract plane
`K = im D(Φ^∂[Ψ_a])(z)`, `z = Pc_a(pr_int(ρ(a)⁻¹x))`): from the port's model bounds, (OWN), (TG value)
with error `e'` on the core, (LOC) / (COV) called at `5Σ/4`, a selected preimage `q̂ ∈ D_a` and
BCG02's value clause on `D_a`, at radius `Σρ(q̂)` and quality `Γ`. -/
theorem cloudy_at_point_BAUGC (hΛ : 0 ≤ Λ) (hΔ1 : 1 ≤ Δ) (hβ1 : 0 < β 1)
    (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (hreq : β 1 ^ 3 * (1000000 * Δ) < 1)
    (hsep : S.SeparatedCollarZero_BIF) (hθ : 0 ≤ θ) (Φ : BoundaryInteriorSlots_BIF S)
    (st : Fin 3) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (eta : W.pieceInterior ⊤ → W.pieceInterior ⊤ → E)
    (row : W.pieceInterior ⊤ → Fin S.packet.cusp.count → E →L[ℝ] ℝ)
    (hrow : ∀ a i, ‖row a i‖ ≤ 1) (a : W.pieceInterior ⊤) (core : W.pieceInterior ⊤ → Prop)
    (Pca : BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²) →L[ℝ] E)
    (Ψa : E → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²)) {Cj eg' Γ sg : ℝ} (hCj : 0 < Cj)
    (hΨa : ContDiff ℝ 2 Ψa) (hΨa2 : ∀ u, ‖fderiv ℝ (fderiv ℝ Ψa) u‖ ≤ Cj)
    (hPc : ∀ z, ‖Pca z‖ ≤ ‖z‖) (hgraph : ∀ u, Pca (Ψa u) = u)
    (hOWN : ∀ y, core y →
      Pca ((S.rho a)⁻¹ • blockRestrict (Φ.stageTags st) (S.interiorMapOn_BAUGA y)) = eta a y)
    (hTGv : ∀ y, core y →
      ‖(S.rho a)⁻¹ • blockRestrict (Φ.stageTags st) (S.interiorMapOn_BAUGA y) - Ψa (eta a y)‖ < eg')
    (hBAv : ∀ i ∈ S.boundaryList_BIF st a,
      letI := inducedMetricSpace S.completion.metric
      ∀ y : W.pieceInterior ⊤, dist y a < stageDomain_BIF Δ st * S.rho a →
        |(S.packet.height i y - S.packet.height i a) / S.rho a -
          row a i (eta a y - eta a a)| < θ)
    (x : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
    (hxT : x ∈ Φ.stageCloudEnlarged st) (z : E)
    (hz : Pca (augIntProjCLM_BAUGC ((S.rho a)⁻¹ • x)) = z) (selx : W.pieceInterior ⊤)
    (hsel : letI := inducedMetricSpace S.completion.metric;
      dist selx a < stageDomain_BIF Δ st * S.rho a)
    (hLOC : ∀ y ∈ Φ.stageCloudEnlarged st,
      ‖augIntProjCLM_BAUGC (y - x)‖ ≤ 5 / 4 * sg * S.rho a / Γ →
      ∃ q : W.pieceInterior ⊤, core q ∧
        (letI := inducedMetricSpace S.completion.metric;
          dist q a < stageDomain_BIF Δ st * S.rho a) ∧
        Φ.stageProj st (S.boundaryOriginalMap q.val) = y)
    (hCOV : ∀ u : E, ‖u - z‖ ≤ 2 * (5 / 4 * sg) / Γ →
      ∃ q : W.pieceInterior ⊤, core q ∧
        (letI := inducedMetricSpace S.completion.metric;
          dist q a < stageDomain_BIF Δ st * S.rho a) ∧
        eta a q = u ∧ Φ.stageProj st (S.boundaryOriginalMap q.val) ∈ Φ.stageCloudEnlarged st)
    (hΓ : 0 < Γ) (hΓ1 : Γ < 1) (hsg : 0 < sg) (hsgΓ : sg < Γ / 250)
    (hsgC : sg < Γ ^ 3 / (125 * (Cj + 2 * bmConst_BAUGC))) (heg' : 0 ≤ eg')
    (heΓ : eg' + 2 * (bmConst_BAUGC * θ) < Γ * sg / 100)
    (Kp : Submodule ℝ (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)))
    (hK : Kp = LinearMap.range (fderiv ℝ (augmentedModel_BAUGC Ψa (S.boundaryList_BIF st a)
      (bmBlocks_BAUGC (fun i => S.packet.height i a) (S.rho a) (row a) (eta a a))) z :
        E →ₗ[ℝ] BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))) :
    hausdorffEDist (Φ.stageCloudEnlarged st ∩ ball x (sg * S.rho selx / Γ))
      ((AffineSubspace.mk' x Kp :
          Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))) ∩
        ball x (sg * S.rho selx / Γ)) ≤ ENNReal.ofReal (Γ * (sg * S.rho selx)) := by
  have hρa := S.rho_pos a
  have hρs := S.rho_pos selx
  have hP1 := one_le_bmConst_BAUGC
  have hfacts := S.boundaryList_facts_BAUGC hsep hΛ hΔ1 hβ1 hΛΔ hreq st a
  have hC := (stageDomain_BIF_bounds_BAUGC hΔ1 st).2
  have hrat := S.rho_ratio_of_dist_lt_BAUGC hΛ hΔ1 hΛΔ hC hsel
  have hrlo : 3 * sg / 4 ≤ sg * S.rho selx / S.rho a := by
    rw [le_div_iff₀ hρa]; nlinarith [hrat.1]
  have hrhi : sg * S.rho selx / S.rho a ≤ 5 * sg / 4 := by
    rw [div_le_iff₀ hρa]; nlinarith [hrat.2]
  have hrloc : sg * S.rho selx / Γ ≤ 5 / 4 * sg * S.rho a / Γ := by
    apply div_le_div_of_nonneg_right _ hΓ.le
    nlinarith [hrat.2]
  have hrcov : sg * S.rho selx / S.rho a / Γ ≤ 2 * (5 / 4 * sg) / Γ := by
    apply div_le_div_of_nonneg_right _ hΓ.le
    linarith
  have hsgC' : sg < Γ ^ 3 / (100 * (Cj + 2 * bmConst_BAUGC)) :=
    lt_of_lt_of_le hsgC (div_le_div_of_nonneg_left (by positivity) (by positivity)
      (by nlinarith))
  subst hK
  rw [← hz]
  refine augmented_bm_cloud_test_list_BAUGC
    (fun q : W.pieceInterior ⊤ => Φ.stageProj st (S.boundaryOriginalMap q.val)) (eta a)
    {q : W.pieceInterior ⊤ | core q ∧
      (letI := inducedMetricSpace S.completion.metric; dist q a < stageDomain_BIF Δ st * S.rho a)}
    Ψa _ hfacts.1 (fun i => S.packet.height i a) hρa (fun ⟨i, hi⟩ => (hfacts.2 i hi).1) (row a)
    (eta a a) (fun i _ => hrow a i) Pca hPc hgraph _ hxT hΓ hΓ1 hsg (by linarith) hCj hsgC' heg' hθ
    heΓ hrlo hrhi (fun u _ => hΨa.contDiffAt) (fun u _ => ?_)
    (cloud_local_BAUGC Φ st (eta a) a core Pca hOWN x hLOC hrloc) (fun q hq i hi => ?_)
    (fun q hq => ?_) (fun i q => S.packet.toBoundaryCollarPacket.height i q.val)
    (fun q hq i hi => ?_) (fun q hq i hi => hBAv i hi q hq.2) (fun u hu => ?_)
  · rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]
    exact hΨa2 u
  · rw [S.stageProj_boundaryOriginalMap_inr_BAUGC Φ st, S.block_eq_zero_of_notMem_BAUGC hi hq.2,
      map_zero]
  · rw [map_smul, S.augIntProj_stageProj_boundaryOriginalMap_BAUGC Φ st q]
    exact (hTGv q hq.1).le
  · rw [S.stageProj_boundaryOriginalMap_inr_BAUGC Φ st,
      S.block_eq_boundaryBlock_of_mem_BAUGC hsep hΛ hΔ1 hβ1 hΛΔ hreq hi hq.2]
  · rw [hz] at hu
    obtain ⟨q, hq, hqa, hqu, hqT⟩ := hCOV u ((mem_closedBall.mp hu).trans hrcov |>.trans_eq'
      (dist_eq_norm u z))
    exact ⟨q, ⟨hq, hqa⟩, hqu, hqT⟩

end CloudParts

section Cloud

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} (Φ : BoundaryInteriorSlots_BIF S) (st : Fin 3) {E : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] (eta : W.pieceInterior ⊤ → W.pieceInterior ⊤ → E)
  (row : W.pieceInterior ⊤ → Fin S.packet.cusp.count → E →L[ℝ] ℝ)
  (Ψ : W.pieceInterior ⊤ → E → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))
  (Kint : W.pieceInterior ⊤ → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²) →L[ℝ]
    BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))
  (rpre : Φ.stageCloudEnlarged st → W.pieceInterior ⊤)
  (pre ref : Φ.stageCloud st → W.pieceInterior ⊤)
  (href : ∀ x, ref x ∈ S.stageCentres_BIF st)
  (hrpre : ∀ x, Φ.stageProj st (S.boundaryOriginalMap (rpre x).val) = x.1)
  (hpre : ∀ x, Φ.stageProj st (S.boundaryOriginalMap (pre x).val) = x.1 ∧
    (letI := inducedMetricSpace S.completion.metric
     dist (pre x) (ref x) < stageDomain_BIF Δ st * S.rho (ref x)))

/-- (PDEF) of the port table as the derivative image of the augmented PRUNED model
`Φ^∂[K_int a ∘ Ψ_a]` (`K^∂ ∘ Φ^∂ = Φ^∂[K ∘ Ψ]`). -/
theorem portTable_plane_eq_model_BAUGC
    {x : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)} (hx : x ∈ Φ.stageCloud st) :
    (portTable_BAUGC Φ st eta row Ψ Kint rpre pre ref href hrpre hpre).planes.plane x =
      LinearMap.range (fderiv ℝ (augmentedModel_BAUGC (Kint (ref ⟨x, hx⟩) ∘ Ψ (ref ⟨x, hx⟩))
        (S.boundaryList_BIF st (ref ⟨x, hx⟩))
        (bmBlocks_BAUGC (fun i => S.packet.height i (ref ⟨x, hx⟩)) (S.rho (ref ⟨x, hx⟩))
          (row (ref ⟨x, hx⟩)) (eta (ref ⟨x, hx⟩) (ref ⟨x, hx⟩))))
        (eta (ref ⟨x, hx⟩) (pre ⟨x, hx⟩)) :
          E →ₗ[ℝ] BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) := by
  rw [portTable_plane_BAUGC Φ st eta row Ψ Kint rpre pre ref href hrpre hpre hx]
  simp only [portModel_BAUGC]
  rw [augmentedPrune_comp_model_BAUGC]

/-- **Field `cloudy` of the port table** (FC27's (CS) for every selection of preimages, stage
uniform): from the port's model bounds (M), (OWN), (TG value) with error `e'` on the core, the
model preimage in the core, (LOC) / (COV) called at `5Σ/4`, (PRE) (preimages in `D_a`), `S_j ⊆ S̃_j`
and BCG02's value clause on `D_a`; numbers `Σ < Γ/250`, `Σ < Γ³/(125(C_j + 2P_*))`,
`e' + 2P_*θ < ΓΣ/100`. -/
theorem portTable_cloudy_BAUGC (hΛ : 0 ≤ Λ) (hΔ1 : 1 ≤ Δ) (hβ1 : 0 < β 1)
    (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (hreq : β 1 ^ 3 * (1000000 * Δ) < 1)
    (hsep : S.SeparatedCollarZero_BIF) (hθ : 0 ≤ θ) {Cj eg' Γ sg : ℝ} (hCj : 0 < Cj)
    (hΓ : 0 < Γ) (hΓ1 : Γ < 1) (hsg : 0 < sg) (hsgΓ : sg < Γ / 250)
    (hsgC : sg < Γ ^ 3 / (125 * (Cj + 2 * bmConst_BAUGC))) (heg' : 0 ≤ eg')
    (heΓ : eg' + 2 * (bmConst_BAUGC * θ) < Γ * sg / 100)
    (core : W.pieceInterior ⊤ → W.pieceInterior ⊤ → Prop)
    (Pc : W.pieceInterior ⊤ → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²) →L[ℝ] E)
    (hMc : ∀ a ∈ S.stageCentres_BIF st, ContDiff ℝ 2 (Kint a ∘ Ψ a) ∧
      ∀ u, ‖fderiv ℝ (fderiv ℝ (Kint a ∘ Ψ a)) u‖ ≤ Cj)
    (hOWN : ∀ a ∈ S.stageCentres_BIF st, (∀ z, ‖Pc a z‖ ≤ ‖z‖) ∧
      (∀ u, Pc a ((Kint a ∘ Ψ a) u) = u) ∧ ∀ y, core a y →
        Pc a ((S.rho a)⁻¹ • blockRestrict (Φ.stageTags st) (S.interiorMapOn_BAUGA y)) = eta a y)
    (hTGv : ∀ a ∈ S.stageCentres_BIF st, ∀ y, core a y →
      ‖(S.rho a)⁻¹ • blockRestrict (Φ.stageTags st) (S.interiorMapOn_BAUGA y) -
        (Kint a ∘ Ψ a) (eta a y)‖ < eg')
    (hprecore : ∀ x, core (ref x) (pre x))
    (hLOC : ∀ x (hx : x ∈ Φ.stageCloud st), ∀ y ∈ Φ.stageCloudEnlarged st,
      ‖augIntProjCLM_BAUGC (y - x)‖ ≤ 5 / 4 * sg * S.rho (ref ⟨x, hx⟩) / Γ →
      ∃ q : W.pieceInterior ⊤, core (ref ⟨x, hx⟩) q ∧
        (letI := inducedMetricSpace S.completion.metric;
          dist q (ref ⟨x, hx⟩) < stageDomain_BIF Δ st * S.rho (ref ⟨x, hx⟩)) ∧
        Φ.stageProj st (S.boundaryOriginalMap q.val) = y)
    (hCOV : ∀ x (hx : x ∈ Φ.stageCloud st), ∀ u : E,
      ‖u - eta (ref ⟨x, hx⟩) (pre ⟨x, hx⟩)‖ ≤ 2 * (5 / 4 * sg) / Γ →
      ∃ q : W.pieceInterior ⊤, core (ref ⟨x, hx⟩) q ∧
        (letI := inducedMetricSpace S.completion.metric;
          dist q (ref ⟨x, hx⟩) < stageDomain_BIF Δ st * S.rho (ref ⟨x, hx⟩)) ∧
        eta (ref ⟨x, hx⟩) q = u ∧
        Φ.stageProj st (S.boundaryOriginalMap q.val) ∈ Φ.stageCloudEnlarged st)
    (hPREd : ∀ x (hx : x ∈ Φ.stageCloud st) (q : W.pieceInterior ⊤),
      Φ.stageProj st (S.boundaryOriginalMap q.val) = x →
        (letI := inducedMetricSpace S.completion.metric;
          dist q (ref ⟨x, hx⟩) < stageDomain_BIF Δ st * S.rho (ref ⟨x, hx⟩)))
    (hsub : Φ.stageCloud st ⊆ Φ.stageCloudEnlarged st) (hrow : ∀ a i, ‖row a i‖ ≤ 1)
    (hBAv : ∀ a ∈ S.stageCentres_BIF st, ∀ i ∈ S.boundaryList_BIF st a,
      letI := inducedMetricSpace S.completion.metric
      ∀ y : W.pieceInterior ⊤, dist y a < stageDomain_BIF Δ st * S.rho a →
        |(S.packet.height i y - S.packet.height i a) / S.rho a -
          row a i (eta a y - eta a a)| < θ) :
    ∀ sel : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → W.pieceInterior ⊤,
      (∀ x ∈ Φ.stageCloudEnlarged st, Φ.stageProj st (S.boundaryOriginalMap (sel x).val) = x) →
      ∀ x ∈ Φ.stageCloud st,
        hausdorffEDist (Φ.stageCloudEnlarged st ∩ ball x (sg * S.rho (sel x) / Γ))
          ((AffineSubspace.mk' x
              ((portTable_BAUGC Φ st eta row Ψ Kint rpre pre ref href hrpre hpre).planes.plane x) :
              Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))) ∩
            ball x (sg * S.rho (sel x) / Γ)) ≤ ENNReal.ofReal (Γ * (sg * S.rho (sel x))) := by
  intro sel hsel x hx
  have ha := href ⟨x, hx⟩
  have hO := hOWN _ ha
  have hz : Pc (ref ⟨x, hx⟩) (augIntProjCLM_BAUGC ((S.rho (ref ⟨x, hx⟩))⁻¹ • x)) =
      eta (ref ⟨x, hx⟩) (pre ⟨x, hx⟩) := by
    have h1 : Φ.stageProj st (S.boundaryOriginalMap (pre ⟨x, hx⟩).val) = x := (hpre ⟨x, hx⟩).1
    calc Pc (ref ⟨x, hx⟩) (augIntProjCLM_BAUGC ((S.rho (ref ⟨x, hx⟩))⁻¹ • x)) =
        Pc (ref ⟨x, hx⟩) (augIntProjCLM_BAUGC ((S.rho (ref ⟨x, hx⟩))⁻¹ •
          Φ.stageProj st (S.boundaryOriginalMap (pre ⟨x, hx⟩).val))) := by rw [h1]
      _ = Pc (ref ⟨x, hx⟩) ((S.rho (ref ⟨x, hx⟩))⁻¹ •
          blockRestrict (Φ.stageTags st) (S.interiorMapOn_BAUGA (pre ⟨x, hx⟩))) := by
        rw [map_smul, S.augIntProj_stageProj_boundaryOriginalMap_BAUGC Φ st (pre ⟨x, hx⟩)]
      _ = eta (ref ⟨x, hx⟩) (pre ⟨x, hx⟩) := hO.2.2 _ (hprecore ⟨x, hx⟩)
  exact cloudy_at_point_BAUGC hΛ hΔ1 hβ1 hΛΔ hreq hsep hθ Φ st eta row hrow (ref ⟨x, hx⟩)
    (core (ref ⟨x, hx⟩)) (Pc (ref ⟨x, hx⟩)) (Kint (ref ⟨x, hx⟩) ∘ Ψ (ref ⟨x, hx⟩)) hCj
    (hMc _ ha).1 (hMc _ ha).2 hO.1 hO.2.1 hO.2.2 (hTGv _ ha) (hBAv _ ha) x (hsub hx) _ hz (sel x)
    (hPREd x hx (sel x) (hsel x (hsub hx))) (hLOC x hx) (hCOV x hx) hΓ hΓ1 hsg hsgΓ hsgC heg' heΓ
    _ (portTable_plane_eq_model_BAUGC Φ st eta row Ψ Kint rpre pre ref href hrpre hpre hx)

end Cloud

/-! ### Consumer: the numbers of the transfer -/

/-- **The numeric premises of the transfer from ProducerDP v3's numbers**: with the port called at
`(Γ, Σ' = 5Σ/4, e' = e/2)`, the port's own numbers hold (`Σ' < Γ/200`, `Σ' < Γ³/(100C_j)`,
`e' < ΓΣ'/100`), and the transfer's budgets hold (`cloudy`: `e' + 2P_*θ < ΓΣ/100`; `normal`:
`e' + 6P_*θ ≤ e`). -/
theorem transfer_numbers_BAUGC {Γ sg eg Cj θ : ℝ} (hΓ : 0 < Γ) (hCj : 0 < Cj)
    (hsgΓ : sg < Γ / 250) (hsgC : sg < Γ ^ 3 / (125 * (Cj + 2 * bmConst_BAUGC))) (heg : 0 < eg)
    (hegΓ : eg < Γ * sg / 100) (h16 : 16 * bmConst_BAUGC * θ ≤ eg) :
    5 / 4 * sg < Γ / 200 ∧ 5 / 4 * sg < Γ ^ 3 / (100 * Cj) ∧ eg / 2 < Γ * (5 / 4 * sg) / 100 ∧
      eg / 2 + 2 * (bmConst_BAUGC * θ) < Γ * sg / 100 ∧ eg / 2 + 6 * bmConst_BAUGC * θ ≤ eg ∧
      0 ≤ eg / 2 := by
  have hP := one_le_bmConst_BAUGC
  refine ⟨by linarith, ?_, by nlinarith, by nlinarith, by nlinarith, by positivity⟩
  have h1 : Γ ^ 3 / (125 * (Cj + 2 * bmConst_BAUGC)) * (5 / 4) ≤ Γ ^ 3 / (100 * Cj) := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 < Γ ^ 3 := by positivity
    nlinarith
  nlinarith

end DifferentialGeometry.Geometry.Collapse
