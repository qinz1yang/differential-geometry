import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimIsolationBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryFrontierM1ApplicationsBGR

/-!
# BCG07 F5 / F5z (equalities) on the enhanced chain (lane S-BCG-ROWS)

Given the v2 bases `Bs`, the whole-fibre layer `WF`, the actual zero domains `Z` of the same chain
(G19's premises: E4's `r_∂` block and `θ < 1/100`, as in `frontier_M₁_BGR`):

* `slim_isolation_BGR`: the base value `f₃ p` of a saturated regular level of a smooth function is
  isolated in the image of the level (both slim chart types `S²`, `T²`; generic
  `exists_isOpen_inter_image_zero_eq_singleton_BGR`);
* **`zeroFace_eq_slimFibre_BGR`** (F5z): a zero face meeting `X₃` is ONE whole slim fibre;
* `cuspFront_level_data_BGR`, `isPreconnected_cuspFront_BGR`;
* **`cuspFront_eq_slimFibre_BGR`** (F5): a cusp front meeting `X₃` is ONE whole slim fibre.

Route: the closed chapter's `eq_fiber_of_isPreconnected_of_isolated` with `S` = the face / front
(preconnected: `Z.face_param`, the labelled product of the strong component), `D = f₃(S ∩ X₃)`,
`hSX` = G19's saturation identities, isolation from the slim product chart.
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

/-- slim isolation, chart cases combined. -/
theorem slim_isolation_BGR {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2 C.toChain Bs) {Fd : W.Carrier → ℝ}
    (hFd : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ Fd) {cc : ℝ} {p : W.Carrier} (hpX : p ∈ Bs.source 2)
    (hfib : ∀ q ∈ Bs.source 2, C.toChain.stageMap 2 q = C.toChain.stageMap 2 p → Fd q = cc)
    (hsat : ∀ q ∈ Bs.source 2, ∀ q' ∈ Bs.source 2,
      C.toChain.stageMap 2 q = C.toChain.stageMap 2 q' → Fd q = cc → Fd q' = cc)
    (hreg : mfderiv W.model 𝓘(ℝ, ℝ) Fd p ≠ 0) :
    ∃ O : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)), IsOpen O ∧
      O ∩ C.toChain.stageMap 2 '' ({q | Fd q = cc} ∩ Bs.source 2) = {C.toChain.stageMap 2 p} := by
  have hw : C.toChain.stageMap 2 p ∈ Bs.base 2 := Bs.image_eq 2 ▸ mem_image_of_mem _ hpX
  have hB : C.toChain.stageMap 2 '' Bs.source 2 ⊆ Bs.base 2 := (Bs.image_eq 2).subset
  rcases WF.slim_chart _ hw with h | h
  · exact exists_isOpen_inter_image_zero_eq_singleton_BGR h hB
      (by rw [finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]) hFd hfib hsat hpX rfl hreg
  · exact exists_isOpen_inter_image_zero_eq_singleton_BGR h hB
      (by rw [finrank_euclideanSpace_fin, Module.finrank_prod, finrank_euclideanSpace_fin]) hFd hfib
      hsat hpX rfl hreg

/-- The actual zero face is preconnected (its standard parametrization by `S²` or `T²`). -/
theorem isPreconnected_actualZeroFace_BGR {Bs : BoundaryGaf02BasesV2 C.toChain}
    (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs) (k : S.ZeroIdx_BAUGC) :
    IsPreconnected (C.toChain.actualZeroFace_BIFc k) := by
  rcases Z.face_param k with ⟨e, he, hr⟩ | ⟨e, he, hr⟩
  · rw [← hr]
    exact isPreconnected_range he.isEmbedding.continuous
  · rw [← hr]
    exact isPreconnected_range he.isEmbedding.continuous

/-- **F5z: a zero face meeting `X₃` is ONE whole slim fibre** (frozen v3.1 F5z, with E4's premises
as in G19's F4c). -/
theorem zeroFace_eq_slimFibre_BGR {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2 C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    ∀ k : S.ZeroIdx_BAUGC, (C.toChain.actualZeroFace_BIFc k ∩ Bs.source 2).Nonempty →
      ∃ y ∈ Bs.base 2, C.toChain.actualZeroFace_BIFc k = Bs.fibre 2 y := by
  rintro k ⟨p, hp, hpX⟩
  have hface := Z.face_eq k
  have hF0 : Z.defFn k p = 0 := by
    have h : p ∈ {q | Z.defFn k q = 0} := hface ▸ hp
    exact h
  have hSX := C.zeroFace_inter_source_eq_preimage_BGR WF Z hrd hrd4 hrdc hprem hθ k
  have hfibsub := C.zeroFace_fibre_subset_BGR WF Z hrd hrd4 hrdc hprem hθ k hp hpX
  obtain ⟨O, hO, hOD⟩ := C.slim_isolation_BGR WF (Z.defFn_smooth k) hpX (cc := 0)
    (fun q hq hqp => by
      have h : q ∈ C.toChain.actualZeroFace_BIFc k := hfibsub ⟨hq, hqp⟩
      rw [hface] at h
      exact h)
    (fun q hq q' hq' hqq' hq0 => by
      have hqf : q ∈ C.toChain.actualZeroFace_BIFc k ∩ Bs.source 2 :=
        ⟨by rw [hface]; exact hq0, hq⟩
      have h : q' ∈ C.toChain.actualZeroFace_BIFc k ∩ Bs.source 2 := by
        rw [hSX]
        exact ⟨hq', q, hqf, hqq'⟩
      have h' : q' ∈ C.toChain.actualZeroFace_BIFc k := h.1
      rw [hface] at h'
      exact h')
    (Z.defFn_regular k p hF0)
  rw [← hface] at hOD
  refine ⟨C.toChain.stageMap 2 p, Bs.image_eq 2 ▸ mem_image_of_mem _ hpX, ?_⟩
  exact DifferentialGeometry.Topology.eq_fiber_of_isPreconnected_of_isolated
    (C.toChain.stageMap 2) (Bs.source 2) (C.toChain.actualZeroFace_BIFc k)
    (C.toChain.stageMap 2 '' (C.toChain.actualZeroFace_BIFc k ∩ Bs.source 2))
    (Bs.isOpen_source 2 (by decide)) (Bs.continuousOn_stageMap_BCF 2)
    (C.isPreconnected_actualZeroFace_BGR Z k) hSX ⟨O, hO, hOD⟩
    (Bs.proper 2 {C.toChain.stageMap 2 p}
      (singleton_subset_iff.mpr (Bs.image_eq 2 ▸ mem_image_of_mem _ hpX)) isCompact_singleton)
    ⟨p, hpX, rfl⟩

/-- **The cusp front as a regular level of BCG6-K's core level function** (premises of E4). -/
theorem cuspFront_level_data_BGR {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (i : Fin S.packet.cusp.count) :
    ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (S.packet.toBoundaryCollarPacket.coreLevel_BCG6K i
      (chainBoundaryU_BCG6K C.toChain.E i)) ∧
    C.toChain.cuspFront_BIF i = {x | S.packet.toBoundaryCollarPacket.coreLevel_BCG6K i
      (chainBoundaryU_BCG6K C.toChain.E i) x = 40} ∧
    ∀ x ∈ C.toChain.cuspFront_BIF i, mfderiv W.model 𝓘(ℝ, ℝ)
      (S.packet.toBoundaryCollarPacket.coreLevel_BCG6K i (chainBoundaryU_BCG6K C.toChain.E i)) x
        ≠ 0 := by
  have hεd := epsBoundary_lt_BGR hrd hrdc
  have hBI := (C.bcg04_row_BGR hrd hprem).2.1 3 i
  have hBFM := (C.bcg05_row_BGR hθ hrd hrd4 hprem).1 3 i
  have hc₃ := C.validity.c_two_lt_E4
  have hR := BoundaryCollarPacket.register_R_BCG6K hεd hc₃
  have hu : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (chainBoundaryU_BCG6K C.toChain.E i) :=
    contMDiff_chainBoundaryU_BCG6K (C.stage_smooth_BAUGD 3) i
  have heq : C.toChain.cuspFront_BIF i = {x | S.packet.toBoundaryCollarPacket.coreLevel_BCG6K i
      (chainBoundaryU_BCG6K C.toChain.E i) x = 40} :=
    S.packet.toBoundaryCollarPacket.cuspFront_eq_BCG6K hεd hBI hBFM
  refine ⟨S.packet.toBoundaryCollarPacket.contMDiff_coreLevel_BCG6K i hu, heq, fun x hx => ?_⟩
  have hx40 : S.packet.toBoundaryCollarPacket.coreLevel_BCG6K i
      (chainBoundaryU_BCG6K C.toChain.E i) x = 40 := by
    rw [heq] at hx
    exact hx
  exact S.packet.toBoundaryCollarPacket.mfderiv_coreLevel_ne_zero_BCG6K i
    (cuspTolerance_le_thousandth_BCUSP1 _ _ _) hu C.toChain.c_two_pos_BCG6K.le hR
    (fun y _ => (hBI y).1) (C.bcg04_derivative_on_boundary_chain_BGR i) (le_of_eq hx40)

/-- **A cusp front is preconnected** (the labelled product `T² × [0, 1]` of BCG6-K's strong
component: the front is the image of the end `T² × {1}`; premises of E4). -/
theorem isPreconnected_cuspFront_BGR {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (i : Fin S.packet.cusp.count) :
    IsPreconnected (C.toChain.cuspFront_BIF i) := by
  have hcomp := (C.bcg06_on_boundary_chain_BGR hrd hrd4 hrdc hprem hθ).1 i
  obtain ⟨cs, -, -, -, D, -, hD1⟩ := hcomp.labelled_smooth_product
  have hfr := hcomp.relative_frontier_eq
  have hcl : IsClosed (S.packet.toBoundaryCollarPacket.cuspCore_BCG6K i
      (chainBoundaryU_BCG6K C.toChain.E) (chainBoundaryV_BCG6K C.toChain.E)) :=
    hcomp.compact_core.isClosed
  have hsub := hcl.frontier_subset
  rw [hfr] at hsub
  have hrange : C.toChain.cuspFront_BIF i = range (fun t : Torus =>
      ((D (t, (⟨1, by norm_num, le_rfl⟩ : Icc (0 : ℝ) 1)) :
        S.packet.toBoundaryCollarPacket.cuspCore_BCG6K i (chainBoundaryU_BCG6K C.toChain.E)
          (chainBoundaryV_BCG6K C.toChain.E)) : W.Carrier)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨p, hp⟩ := D.surjective ⟨x, hsub hx⟩
      have hxp : (D p : W.Carrier) = x := congrArg Subtype.val hp
      have hp2 : (p.2 : ℝ) = 1 := (hD1 p).mp (by rw [hxp]; exact hx)
      refine ⟨p.1, ?_⟩
      have : (p.1, (⟨1, by norm_num, le_rfl⟩ : Icc (0 : ℝ) 1)) = p :=
        Prod.ext rfl (Subtype.ext hp2.symm)
      beta_reduce
      rw [this, hxp]
    · rintro ⟨t, rfl⟩
      exact (hD1 _).mpr rfl
  rw [hrange]
  exact isPreconnected_range (continuous_subtype_val.comp
    (D.continuous.comp (Continuous.prodMk continuous_id continuous_const)))

/-- **F5: a cusp front meeting `X₃` is ONE whole slim fibre** (frozen v3.1 F5, with E4's premises
and the zero domains `Z` as in G19's point-set half). -/
theorem cuspFront_eq_slimFibre_BGR {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2 C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    ∀ i : Fin S.packet.cusp.count, (C.toChain.cuspFront_BIF i ∩ Bs.source 2).Nonempty →
      ∃ y ∈ Bs.base 2, C.toChain.cuspFront_BIF i = Bs.fibre 2 y := by
  rintro i ⟨p, hp, hpX⟩
  obtain ⟨hsm, hfeq, hreg⟩ := C.cuspFront_level_data_BGR hrd hrd4 hrdc hprem hθ i
  have hSX := C.cuspFront_inter_source_eq_preimage_BGR WF Z hrd hrd4 hrdc hprem hθ i
  have hfibsub := C.cuspFront_fibre_subset_BGR WF Z hrd hrd4 hrdc hprem hθ i hp hpX
  obtain ⟨O, hO, hOD⟩ := C.slim_isolation_BGR WF hsm hpX (cc := 40)
    (fun q hq hqp => by
      have h : q ∈ C.toChain.cuspFront_BIF i := hfibsub ⟨hq, hqp⟩
      rw [hfeq] at h
      exact h)
    (fun q hq q' hq' hqq' hq0 => by
      have hqf : q ∈ C.toChain.cuspFront_BIF i ∩ Bs.source 2 :=
        ⟨by rw [hfeq]; exact hq0, hq⟩
      have h : q' ∈ C.toChain.cuspFront_BIF i ∩ Bs.source 2 := by
        rw [hSX]
        exact ⟨hq', q, hqf, hqq'⟩
      have h' : q' ∈ C.toChain.cuspFront_BIF i := h.1
      rw [hfeq] at h'
      exact h')
    (hreg p hp)
  rw [← hfeq] at hOD
  refine ⟨C.toChain.stageMap 2 p, Bs.image_eq 2 ▸ mem_image_of_mem _ hpX, ?_⟩
  exact DifferentialGeometry.Topology.eq_fiber_of_isPreconnected_of_isolated
    (C.toChain.stageMap 2) (Bs.source 2) (C.toChain.cuspFront_BIF i)
    (C.toChain.stageMap 2 '' (C.toChain.cuspFront_BIF i ∩ Bs.source 2))
    (Bs.isOpen_source 2 (by decide)) (Bs.continuousOn_stageMap_BCF 2)
    (C.isPreconnected_cuspFront_BGR hrd hrd4 hrdc hprem hθ i) hSX ⟨O, hO, hOD⟩
    (Bs.proper 2 {C.toChain.stageMap 2 p}
      (singleton_subset_iff.mpr (Bs.image_eq 2 ▸ mem_image_of_mem _ hpX)) isCompact_singleton)
    ⟨p, hpX, rfl⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
