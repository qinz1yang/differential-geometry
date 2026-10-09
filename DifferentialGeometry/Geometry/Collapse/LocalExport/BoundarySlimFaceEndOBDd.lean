import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimSubArcsOBDd
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeSlimFunBG4
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimFreeEndOBDd
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCutCoverOBD

/-!
# A face point of `D₃` is an end value of a sub-arc (lane S-BD2d2, suffix `_OBDd`), group G10g

Lane O-BD1 (by S-BD2d2), hlift, `SlimCutPieces74`. For a point `p ∈ ∂M₁ ∩ X₃` with `f₃ p ∈ D₃ =
K₃ ∩ C₃`, the base point `f₃ p` is an END value `γ' i (iccEnd b)` of one of the sub-arcs of
`exists_slimD3SubArcs_OBDd`: if it were an interior point of the sub-arc `arc k [s, e]`, the
`f₃`-preimage `R` of the open sub-arc `arc k (s, e)` would be an open neighbourhood of `p`
(`isOpen_slimArc_preimage_BG4`), hence contain a point `q ∉ M₁`; but `f₃ q ∈ C₃`, so `q ∈ M₁` by the
saturation `X₃ ∩ f₃⁻¹(C₃) = M₁ ∩ X₃` (`bcg07_row_extras_BGR`).

* `BoundaryGaf02ChainE.faceValue_isEnd_OBDd`: the statement.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology GC.GraphManifold
  GC.GraphManifold.Assembly

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

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

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

include C in
/-- **A face point of `D₃` is an end value of a sub-arc.** -/
theorem faceValue_isEnd_OBDd (dec : BoundaryActualDecompositionV2b C.toChain)
    (hεr : εr < 1 / 2) {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) {N : ℕ} (γ' : Fin N → SmoothEmbeddedBaseArc_EFE (dec.bases.base 2))
    (hU : ⋃ i, (γ' i).toFun '' Icc 0 1 = dec.slim.K₃ ∩ dec.bases.slimBaseDomain_BIFc)
    (hsub : ∀ i : Fin N, ∃ (k : Fin dec.slim.arcCount) (s e : ℝ), 0 ≤ s ∧ s < e ∧ e ≤ 1 ∧
      ∀ u, (γ' i).toFun u = dec.slim.arc k (s + (e - s) * u))
    {p : W.Carrier} (hpf : p ∈ frontier C.toChain.M₁_BIFc)
    (hpD : C.toChain.stageMap 2 p ∈ dec.slim.K₃ ∩ dec.bases.slimBaseDomain_BIFc) :
    ∃ (i : Fin N) (b : Bool), (γ' i).toFun (iccEnd b) = C.toChain.stageMap 2 p := by
  obtain ⟨i, t, ht, hti⟩ := mem_iUnion.1 (hU ▸ hpD)
  by_cases h0 : t = 0
  · subst h0
    exact ⟨i, false, hti⟩
  by_cases h1 : t = 1
  · subst h1
    exact ⟨i, true, hti⟩
  exfalso
  obtain ⟨k, s, e, hs, hse, he, hfun⟩ := hsub i
  have ht0 : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm h0)
  have ht1 : t < 1 := lt_of_le_of_ne ht.2 h1
  obtain ⟨hsat, -⟩ := C.bcg07_row_extras_BGR hεr hrd hrd4 hrdc hprem hθ dec.fibres
  have hmem : s + (e - s) * t ∈ Ioo s e := ⟨by nlinarith, by nlinarith⟩
  have hfp : C.toChain.stageMap 2 p ∈ dec.slim.arc k '' Ioo s e :=
    ⟨s + (e - s) * t, hmem, by rw [← hfun, hti]⟩
  have hR : IsOpen {q : W.Carrier | C.toChain.stageMap 2 q ∈ dec.slim.arc k '' Ioo s e} :=
    C.isOpen_slimArc_preimage_BG4 dec.fibres dec.slim k hs he
  have hnot : ¬ {q : W.Carrier | C.toChain.stageMap 2 q ∈ dec.slim.arc k '' Ioo s e} ⊆
      C.toChain.M₁_BIFc := fun hsub' => hpf.2 (interior_maximal hsub' hR hfp)
  obtain ⟨q, ⟨t'', ht'', hq3⟩, hqM⟩ := not_subset.1 hnot
  have hmemI : t'' ∈ Icc (0 : ℝ) 1 := ⟨hs.trans ht''.1.le, ht''.2.le.trans he⟩
  have hqb : C.toChain.stageMap 2 q ∈ dec.bases.base 2 :=
    hq3 ▸ dec.slim.arc_subset_base k ⟨t'', hmemI, rfl⟩
  have hqX : q ∈ dec.bases.source 2 := C.mem_source_of_stageMap_mem_base_OBDd dec hqb
  have hu : (t'' - s) / (e - s) ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (by linarith [ht''.1]) (sub_pos.2 hse).le,
      (div_le_one (sub_pos.2 hse)).2 (by linarith [ht''.2])⟩
  have hqC : C.toChain.stageMap 2 q ∈ dec.slim.K₃ ∩ dec.bases.slimBaseDomain_BIFc := by
    rw [← hU]
    refine mem_iUnion.2 ⟨i, (t'' - s) / (e - s), hu, ?_⟩
    rw [hfun, mul_div_cancel₀ _ (sub_pos.2 hse).ne', ← hq3]
    congr 1
    ring
  exact hqM (hsat.subset ⟨hqX, hqC.2⟩).1

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
