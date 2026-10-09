import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeFibreSatBG4
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeTransverseBG4
import DifferentialGeometry.Topology.Ehresmann.ArcPointDatumBG4

/-!
# BCF02 G4, group G4a: the slim base near a point of an arc of `K₃` (lane S-BCF02-G4)

For an arc `γ = Kc.arc j` of the compact slim choice and a parameter `t₀ ∈ [0, 1]`, the point
`y₀ = γ t₀` of the slim base `B₃`, in ONE smooth product chart of `f₃` at `y₀` (`WF.slim_chart`):

* the classification of the points of `B₃` near `y₀` (`arc_point_classification_BG4` applied to the
  chart parameter): `y₀` itself, arc points on the sides `t < t₀`, `t₀ < t` with the sign of a
  functional `ℓ`, or off-arc points beyond an end of the arc; arc points of the neighbourhood have
  parameter near `t₀`; at an end the arc is not interior in `B₃`;
* the regularity of `κ ℓ(f₃ - y₀)` at every point `p ∈ X₃` over `y₀` (`d ≠ 0`: the chart sends the
  `ℝ`-direction of `ℝ × F` onto the base curve, `mfderiv_ne_zero_of_comp_fst_BG4`).

Also `exists_slim_good_nbhd_BG4`: `B₃` has an open neighbourhood `G` in `H` with
`f₃(W) ∩ G ⊆ B₃` (the complement of the compact `f₃(W ∖ X₃)`).
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

section Rank

variable {EM HM M EF HF F : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  [NormedAddCommGroup EF] [NormedSpace ℝ EF] [TopologicalSpace HF] {IF : ModelWithCorners ℝ EF HF}
  [TopologicalSpace F] [ChartedSpace HF F] {k : ℕ}

/-- **Rank argument, base to total**: if `G ∘ φ = h ∘ pr₁` with `φ : ℝᵏ × F → M` differentiable
at `x₀` and `h` has non-zero derivative at `x₀.1`, then `G` has non-zero differential at `φ x₀`. -/
theorem mfderiv_ne_zero_of_comp_fst_BG4 {φ : EuclideanSpace ℝ (Fin k) × F → M} {G : M → ℝ}
    {h : EuclideanSpace ℝ (Fin k) → ℝ} {x₀ : EuclideanSpace ℝ (Fin k) × F}
    (hφ : MDifferentiableAt ((𝓡 k).prod IF) IM φ x₀)
    (hG : MDifferentiableAt IM 𝓘(ℝ, ℝ) G (φ x₀)) (hcomp : ∀ x, G (φ x) = h x.1)
    (hh : DifferentiableAt ℝ h x₀.1) (hh0 : fderiv ℝ h x₀.1 ≠ 0) :
    mfderiv IM 𝓘(ℝ, ℝ) G (φ x₀) ≠ 0 := by
  intro hG0
  have hd : MDifferentiableAt (𝓡 k) 𝓘(ℝ, ℝ) h x₀.1 := hh.mdifferentiableAt
  have e1 : mfderiv ((𝓡 k).prod IF) 𝓘(ℝ, ℝ) (G ∘ φ) x₀ =
      (mfderiv IM 𝓘(ℝ, ℝ) G (φ x₀)).comp (mfderiv ((𝓡 k).prod IF) IM φ x₀) :=
    mfderiv_comp x₀ hG hφ
  have e2 : mfderiv ((𝓡 k).prod IF) 𝓘(ℝ, ℝ) (h ∘ Prod.fst) x₀ =
      (mfderiv (𝓡 k) 𝓘(ℝ, ℝ) h x₀.1).comp (mfderiv ((𝓡 k).prod IF) (𝓡 k) Prod.fst x₀) :=
    mfderiv_comp x₀ hd mdifferentiableAt_fst
  have e3 : G ∘ φ = h ∘ Prod.fst := funext hcomp
  obtain ⟨v, hv⟩ : ∃ v, fderiv ℝ h x₀.1 v ≠ 0 := by
    by_contra hcon
    exact hh0 (ContinuousLinearMap.ext fun v => not_not.mp fun hv => hcon ⟨v, hv⟩)
  have hfst : mfderiv ((𝓡 k).prod IF) (𝓡 k) Prod.fst x₀ =
      ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin k)) EF := mfderiv_fst
  have hmh : mfderiv (𝓡 k) 𝓘(ℝ, ℝ) h x₀.1 = fderiv ℝ h x₀.1 := mfderiv_eq_fderiv
  have h2 : mfderiv ((𝓡 k).prod IF) 𝓘(ℝ, ℝ) (h ∘ Prod.fst) x₀
      ((v, (0 : EF)) : EuclideanSpace ℝ (Fin k) × EF) = fderiv ℝ h x₀.1 v := by
    rw [e2, hfst, hmh]
    rfl
  have h1 : mfderiv ((𝓡 k).prod IF) 𝓘(ℝ, ℝ) (G ∘ φ) x₀
      ((v, (0 : EF)) : EuclideanSpace ℝ (Fin k) × EF) = 0 := by
    rw [e1, hG0]
    rfl
  rw [e3] at h1
  exact hv (h2.symm.trans h1)

end Rank

namespace BoundaryGaf02ChainE

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **A good neighbourhood of the slim base**: `B₃ ⊆ G` open with `f₃ q ∈ G → f₃ q ∈ B₃`
(`f₃(W ∖ X₃)` is compact, hence closed, and misses `B₃` because `X₃ = f₃⁻¹ B₃`). -/
theorem exists_slim_good_nbhd_BG4 {Bs : BoundaryGaf02BasesV2 C.toChain} :
    ∃ G : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)), IsOpen G ∧
      Bs.base 2 ⊆ G ∧ ∀ q : W.Carrier, C.toChain.stageMap 2 q ∈ G →
        C.toChain.stageMap 2 q ∈ Bs.base 2 := by
  have hf : Continuous (C.toChain.stageMap 2) := (C.stageMap_contMDiff_BAUGD 2).continuous
  have hXc : IsCompact (Bs.source 2)ᶜ := (Bs.isOpen_source 2 (by decide)).isClosed_compl.isCompact
  have hK : IsClosed (C.toChain.stageMap 2 '' (Bs.source 2)ᶜ) :=
    (hXc.image hf).isClosed
  have hmem : ∀ q : W.Carrier, C.toChain.stageMap 2 q ∈ Bs.base 2 → q ∈ Bs.source 2 := by
    intro q hq
    rw [Bs.slim_source_eq]
    exact hq
  refine ⟨(C.toChain.stageMap 2 '' (Bs.source 2)ᶜ)ᶜ, hK.isOpen_compl, ?_, ?_⟩
  · rintro y hy ⟨q, hq, rfl⟩
    exact hq (hmem q hy)
  · intro q hq
    have hqX : q ∈ Bs.source 2 := by
      by_contra hqn
      exact hq ⟨q, hqn, rfl⟩
    exact Bs.image_eq 2 ▸ mem_image_of_mem _ hqX

/-- **Regularity of a base functional along a product chart**: if `φ` is a differentiable chart
with `f₃ ∘ φ = σ ∘ pr₁` and `σ ∘ e` has a derivative `w` along a line `e` with `ℓ w ≠ 0`, then
`q ↦ κ' ℓ(f₃ q - σ 0)` has non-zero differential at `φ x₀` for `x₀.1 = 0`. -/
theorem slim_chart_regular_BG4 {EF HF F : Type*} [NormedAddCommGroup EF]
    [NormedSpace ℝ EF] [TopologicalSpace HF] {IF : ModelWithCorners ℝ EF HF} [TopologicalSpace F]
    [ChartedSpace HF F]
    {σ : EuclideanSpace ℝ (Fin 1) → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hσdiff : Differentiable ℝ σ) (e : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1))
    {w : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hsd : HasDerivAt (σ ∘ e) w 0)
    (ℓ : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ) (hℓw : ℓ w ≠ 0)
    {κ' : ℝ} (hκ' : κ' ≠ 0) {φ : EuclideanSpace ℝ (Fin 1) × F → W.Carrier}
    (hf : ∀ x z, C.toChain.stageMap 2 (φ (x, z)) = σ x)
    {x₀ : EuclideanSpace ℝ (Fin 1) × F}
    (hφd : MDifferentiableAt ((𝓡 1).prod IF) W.model φ x₀) (hx0 : x₀.1 = 0) :
    mfderiv W.model 𝓘(ℝ, ℝ) (fun q => κ' * ℓ (C.toChain.stageMap 2 q - σ 0)) (φ x₀) ≠ 0 := by
  have hR : ContDiff ℝ ∞ fun r : BoundaryAmbient_BIF S.IntTag_BAUGA
      (Fin S.packet.cusp.count) => κ' * ℓ (r - σ 0) :=
    contDiff_const.mul (ℓ.contDiff.comp (contDiff_id.sub contDiff_const))
  have hGd : MDifferentiableAt W.model 𝓘(ℝ, ℝ)
      (fun q => κ' * ℓ (C.toChain.stageMap 2 q - σ 0)) (φ x₀) :=
    ((hR.comp_contMDiff (C.stageMap_contMDiff_BAUGD 2)) (φ x₀)).mdifferentiableAt (by simp)
  have hhd : DifferentiableAt ℝ (fun x => κ' * ℓ (σ x - σ 0)) x₀.1 :=
    ((hR.differentiable (by simp)) (σ x₀.1)).comp x₀.1 (hσdiff x₀.1)
  have hh0 : fderiv ℝ (fun x => κ' * ℓ (σ x - σ 0)) x₀.1 ≠ 0 := by
    intro hz
    rw [hx0] at hz hhd
    have he : HasDerivAt e (e 1) 0 := e.hasDerivAt
    have hhd' : HasFDerivAt (fun x => κ' * ℓ (σ x - σ 0))
        (fderiv ℝ (fun x => κ' * ℓ (σ x - σ 0)) 0) (e 0) := by
      rw [map_zero]
      exact hhd.hasFDerivAt
    have h1 := hhd'.comp_hasDerivAt (0 : ℝ) he
    have h2 : HasDerivAt ((fun x => κ' * ℓ (σ x - σ 0)) ∘ e) (κ' * ℓ w) 0 := by
      have h3 := ℓ.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hsd.sub_const (σ 0))
      exact h3.const_mul κ'
    have h4 := h1.unique h2
    rw [hz] at h4
    exact (mul_ne_zero hκ' hℓw) (by simpa using h4.symm)
  exact mfderiv_ne_zero_of_comp_fst_BG4 (IM := W.model) (IF := IF) (φ := φ)
    (G := fun q => κ' * ℓ (C.toChain.stageMap 2 q - σ 0)) (h := fun x => κ' * ℓ (σ x - σ 0))
    hφd hGd (fun x => by
      have h := hf x.1 x.2
      simp only [Prod.mk.eta] at h
      change κ' * ℓ (C.toChain.stageMap 2 (φ x) - σ 0) = κ' * ℓ (σ x.1 - σ 0)
      rw [h]) hhd hh0

/-- **The slim base near an arc point, in ONE smooth product chart** (see the module docstring). -/
theorem slim_point_datum_of_chart_BG4 {EF HF F : Type*} [NormedAddCommGroup EF]
    [NormedSpace ℝ EF] [TopologicalSpace HF] {IF : ModelWithCorners ℝ EF HF} [TopologicalSpace F]
    [ChartedSpace HF F] {Bs : BoundaryGaf02BasesV2 C.toChain}
    (Kc : BoundaryCompactSlimChoiceV2 Bs) (j : Fin Kc.arcCount) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hch : SmoothProductChartAt_BIFc W.model IF (F := F) 1 (C.toChain.stageMap 2) (Bs.source 2)
      (Bs.base 2) (Kc.arc j t₀)) :
    ∃ (ℓ : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ)
      (V : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))) (δ : ℝ),
      IsOpen V ∧ Kc.arc j t₀ ∈ V ∧ 0 < δ ∧ δ ≤ δ₀ ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Kc.arc j t ∈ V → |t - t₀| < δ) ∧
      (∀ z ∈ Bs.base 2 ∩ V, z = Kc.arc j t₀ ∨
        (∃ t ∈ Icc (0 : ℝ) 1, 0 < |t - t₀| ∧ |t - t₀| < δ ∧ z = Kc.arc j t ∧
          ((t < t₀ ∧ ℓ (z - Kc.arc j t₀) < 0) ∨ (t₀ < t ∧ 0 < ℓ (z - Kc.arc j t₀)))) ∨
        (z ∉ Kc.arc j '' Icc 0 1 ∧ ((t₀ = 0 ∧ ℓ (z - Kc.arc j t₀) < 0) ∨
          (t₀ = 1 ∧ 0 < ℓ (z - Kc.arc j t₀))))) ∧
      ((t₀ = 0 ∨ t₀ = 1) → ∀ N : Set (BoundaryAmbient_BIF S.IntTag_BAUGA
        (Fin S.packet.cusp.count)), IsOpen N → Kc.arc j t₀ ∈ N →
          ∃ z ∈ Bs.base 2 ∩ N, z ∉ Kc.arc j '' Icc 0 1) ∧
      (∀ p ∈ Bs.source 2, C.toChain.stageMap 2 p = Kc.arc j t₀ → ∀ κ' : ℝ, κ' ≠ 0 →
        mfderiv W.model 𝓘(ℝ, ℝ)
          (fun q => κ' * ℓ (C.toChain.stageMap 2 q - Kc.arc j t₀)) p ≠ 0) := by
  obtain ⟨σ, φ, O, h0, hσs, hσe, hσd, hO, hr, hφ, hrφ, hf⟩ := hch
  let e : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
    (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm.trans (EuclideanSpace.equiv (Fin 1) ℝ).symm
  have hs : IsEmbedding (σ ∘ e) := hσe.comp e.toHomeomorph.isEmbedding
  have hsr : range (σ ∘ e) = Bs.base 2 ∩ O := by
    rw [e.surjective.range_comp]
    exact hr
  have hs0 : (σ ∘ e) 0 = Kc.arc j t₀ := by
    simp [h0]
  have hσdiff : Differentiable ℝ σ := hσs.differentiable (by simp)
  have hsd : HasDerivAt (σ ∘ e) (fderiv ℝ σ 0 (e 1)) 0 := by
    have he : HasDerivAt e (e 1) 0 := (e : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)).hasDerivAt
    have hσ' : HasFDerivAt σ (fderiv ℝ σ 0) (e 0) := by
      rw [map_zero]
      exact (hσdiff 0).hasFDerivAt
    exact hσ'.comp_hasDerivAt (0 : ℝ) he
  have hw : fderiv ℝ σ 0 (e 1) ≠ 0 := by
    intro hz
    have : e 1 = 0 := hσd 0 (by rw [hz, map_zero])
    exact one_ne_zero (e.injective (by rw [this, map_zero]))
  obtain ⟨ℓ, V, δ, hℓw, hV, hy, hδ, hδ₀', hiso, hcls, hend⟩ := arc_point_classification_BG4 hs hO
    hsr (Kc.arc_injOn j) (Kc.arc_smooth j).continuousOn (Kc.arc_subset_base j) ht₀ hs0 hsd hw hδ₀
  refine ⟨ℓ, V, δ, hV, hy, hδ, hδ₀', hiso, hcls, hend, ?_⟩
  intro p hpX hpy κ' hκ'
  have hpφ : p ∈ range φ := by
    rw [hrφ]
    exact ⟨hpX, ⟨0, h0.trans hpy.symm⟩⟩
  obtain ⟨x₀, hx₀⟩ := hpφ
  have hx0 : x₀.1 = 0 := by
    apply hσe.injective
    rw [← hf x₀.1 x₀.2, show φ (x₀.1, x₀.2) = p from hx₀, hpy, h0]
  have hφd : MDifferentiableAt ((𝓡 1).prod IF) W.model φ x₀ :=
    hφ.contMDiff.mdifferentiableAt (by simp)
  have := C.slim_chart_regular_BG4 (IF := IF) hσdiff (e : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)) hsd ℓ
    hℓw hκ' hf hφd hx0
  rw [show φ x₀ = p from hx₀, h0] at this
  exact this

/-- **The slim base near an arc point** (`WF.slim_chart`: the `S²` and `T²` branches). -/
theorem slim_point_datum_BG4 {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Kc : BoundaryCompactSlimChoiceV2 Bs)
    (j : Fin Kc.arcCount) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) :
    ∃ (ℓ : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ)
      (V : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))) (δ : ℝ),
      IsOpen V ∧ Kc.arc j t₀ ∈ V ∧ 0 < δ ∧ δ ≤ δ₀ ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Kc.arc j t ∈ V → |t - t₀| < δ) ∧
      (∀ z ∈ Bs.base 2 ∩ V, z = Kc.arc j t₀ ∨
        (∃ t ∈ Icc (0 : ℝ) 1, 0 < |t - t₀| ∧ |t - t₀| < δ ∧ z = Kc.arc j t ∧
          ((t < t₀ ∧ ℓ (z - Kc.arc j t₀) < 0) ∨ (t₀ < t ∧ 0 < ℓ (z - Kc.arc j t₀)))) ∨
        (z ∉ Kc.arc j '' Icc 0 1 ∧ ((t₀ = 0 ∧ ℓ (z - Kc.arc j t₀) < 0) ∨
          (t₀ = 1 ∧ 0 < ℓ (z - Kc.arc j t₀))))) ∧
      ((t₀ = 0 ∨ t₀ = 1) → ∀ N : Set (BoundaryAmbient_BIF S.IntTag_BAUGA
        (Fin S.packet.cusp.count)), IsOpen N → Kc.arc j t₀ ∈ N →
          ∃ z ∈ Bs.base 2 ∩ N, z ∉ Kc.arc j '' Icc 0 1) ∧
      (∀ p ∈ Bs.source 2, C.toChain.stageMap 2 p = Kc.arc j t₀ → ∀ κ' : ℝ, κ' ≠ 0 →
        mfderiv W.model 𝓘(ℝ, ℝ)
          (fun q => κ' * ℓ (C.toChain.stageMap 2 q - Kc.arc j t₀)) p ≠ 0) := by
  have hy₀ : Kc.arc j t₀ ∈ Bs.base 2 := Kc.arc_subset_base j ⟨t₀, ht₀, rfl⟩
  rcases WF.slim_chart _ hy₀ with hch | hch
  · exact C.slim_point_datum_of_chart_BG4 Kc j ht₀ hδ₀ hch
  · exact C.slim_point_datum_of_chart_BG4 Kc j ht₀ hδ₀ hch

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
