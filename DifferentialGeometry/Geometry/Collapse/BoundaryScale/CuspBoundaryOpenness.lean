import DifferentialGeometry.Analysis.Calculus.Inverse.HalfSpaceLocalOnto
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspFinitePatch

/-!
# Openness of a cusp collar up to its boundary (height `0`)

For a cusp embedding `e : CuspEmbedding W g K δ X` (`Geometry/Collapse/CuspBoundary.lean`, with the
repaired field `boundary_preimage`), the image under `e` of every open subset of the cusp domain
is open in the carrier, boundary points included (`CuspEmbedding.isOpen_image`,
`CuspEmbedding.isOpen_image_cuspDomain`).

At height `0`, in the product chart of the cusp and a chart of the carrier, `e` is a
boundary-preserving `C¹` map of half-spaces with invertible derivative (`immersion` and equal
dimension 3), and the finite-order half-space local onto theorem
`DifferentialGeometry.Analysis.image_mem_nhdsWithin_halfSpace` applies. At positive height the
finite interior patch of Codex X87 is used. A closed carrier cannot carry a cusp embedding: the
points of height `0` would be boundary points (`CompactCarrier.range_model_eq_of_isBoundaryPoint`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- Interior points read off in an arbitrary extended chart: `w` is an interior point iff its
coordinate in the chart at `b` lies in the interior of the model range. -/
theorem isInteriorPoint_iff_extChartAt_mem_interior_range {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] {b w : M} (hw : w ∈ (extChartAt I b).source) :
    I.IsInteriorPoint w ↔ extChartAt I b w ∈ interior (range I) := by
  have hw' : w ∈ (chartAt H b).source := by rwa [extChartAt_source] at hw
  rw [ModelWithCorners.isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp) (chart_mem_atlas H b)
    hw']
  constructor
  · exact fun h => interior_mono (extChartAt_target_subset_range b) h
  · exact fun h => (chartAt H b).mem_interior_extend_target ((chartAt H b).map_source hw') h

/-- A carrier with a boundary point is modelled on the closed half-space `{v 0 ≥ 0}`. -/
theorem CompactCarrier.range_model_eq_of_isBoundaryPoint (W : CompactCarrier.{u}) {y : W.Carrier}
    (hy : W.model.IsBoundaryPoint y) :
    range W.model = {v : EuclideanSpace ℝ (Fin 3) | 0 ≤ v 0} := by
  obtain ⟨k⟩ := W
  cases k with
  | closed =>
    exfalso
    rw [ModelWithCorners.isBoundaryPoint_iff] at hy
    change _ ∈ frontier (range (𝓡 3)) at hy
    rw [ModelWithCorners.range_eq_univ, frontier_univ] at hy
    exact hy
  | withBoundary => exact range_modelWithCornersEuclideanHalfSpace 3

/-- The range of the cusp model is the half-space of nonnegative height coordinate. -/
theorem range_halfCollarModel : range halfCollarModel =
    {x : (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1) |
      0 ≤ x.2 0} := by
  rw [ModelWithCorners.range_prod, ModelWithCorners.range_eq_univ,
    range_modelWithCornersEuclideanHalfSpace]
  ext x
  simp

/-- The height coordinate of the product chart of the cusp is the height. -/
theorem extChartAt_halfCollarModel_height (p q : CuspHalfSpace) :
    (extChartAt halfCollarModel p q).2 0 = q.2.val 0 := rfl

/-- **Openness at height `0`.** The image of an open subset of the cusp domain is a
neighbourhood of the image of each of its points of height `0`. -/
theorem CuspEmbedding.image_mem_nhds_of_height_zero {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) {S : Set CuspHalfSpace} (hS : IsOpen S) (hSd : S ⊆ cuspDomain)
    {p : CuspHalfSpace} (hpS : p ∈ S) (hz : p.2.val 0 = 0) :
    e.toFun '' S ∈ 𝓝 (e.toFun p) := by
  have hp : p ∈ cuspDomain := hSd hpS
  have hby : W.model.IsBoundaryPoint (e.toFun p) := (e.boundary_preimage hp).mpr hz
  have hrangeT := CompactCarrier.range_model_eq_of_isBoundaryPoint W hby
  set φ := extChartAt halfCollarModel p with hφ
  set ψ := extChartAt W.model (e.toFun p) with hψ
  set F : (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1) →
    EuclideanSpace ℝ (Fin 3) := ψ ∘ e.toFun ∘ φ.symm with hF
  have hcont : ContinuousOn e.toFun cuspDomain := e.contMDiffOn.continuousOn
  have hD : IsOpen (S ∩ e.toFun ⁻¹' ψ.source) :=
    (hcont.mono hSd).isOpen_inter_preimage hS (isOpen_extChartAt_source (e.toFun p))
  have hpD : p ∈ S ∩ e.toFun ⁻¹' ψ.source := ⟨hpS, mem_extChartAt_source (e.toFun p)⟩
  have hR : φ.target ∩ φ.symm ⁻¹' (S ∩ e.toFun ⁻¹' ψ.source) ∈
      𝓝[range halfCollarModel] (φ p) :=
    inter_mem (extChartAt_target_mem_nhdsWithin p)
      (mem_nhdsWithin_of_mem_nhds (extChartAt_preimage_mem_nhds (hD.mem_nhds hpD)))
  obtain ⟨O, hO, hpO, hOR⟩ := mem_nhdsWithin.mp hR
  let ℓ : (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1) →L[ℝ]
      ℝ := (EuclideanSpace.proj (0 : Fin 1)).comp (ContinuousLinearMap.snd ℝ _ _)
  let n : (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1) :=
    ((0, 0), EuclideanSpace.single 0 1)
  let μ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ := EuclideanSpace.proj 0
  have hn : ℓ n = 1 := by simp [ℓ, n]
  have hμ : μ ≠ 0 := by
    intro h
    have := congrArg (fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ => L (EuclideanSpace.single 0 1)) h
    simp [μ] at this
  have hrangeS : range halfCollarModel = {x | 0 ≤ ℓ x} := range_halfCollarModel
  have hmem : ∀ x ∈ O, 0 ≤ ℓ x →
      x ∈ φ.target ∧ φ.symm x ∈ S ∧ e.toFun (φ.symm x) ∈ ψ.source := by
    intro x hxO hx
    have h := hOR ⟨hxO, by rw [hrangeS]; exact hx⟩
    exact ⟨h.1, h.2.1, h.2.2⟩
  have hsmooth : ∀ x ∈ O, 0 ≤ ℓ x → ContDiffWithinAt ℝ 1 F (range halfCollarModel) x := by
    intro x hxO hx
    obtain ⟨hxt, hxS, hxψ⟩ := hmem x hxO hx
    have hq : ContMDiffAt halfCollarModel W.model 1 e.toFun (φ.symm x) :=
      ((e.contMDiffOn (φ.symm x) (hSd hxS)).contMDiffAt
        (isOpen_cuspDomain.mem_nhds (hSd hxS))).of_le (by exact_mod_cast Nat.le_add_left 1 K)
    have hxs := φ.map_target hxt
    rw [hφ, extChartAt_source] at hxs
    have hys := hxψ
    rw [hψ, extChartAt_source] at hys
    have h2 := ((contMDiffAt_iff_of_mem_source hxs hys).mp hq).2
    rw [← hφ, ← hψ, φ.right_inv hxt] at h2
    exact h2
  have hCD : ContDiffOn ℝ 1 F (range halfCollarModel ∩ O) := fun x hx =>
    (hsmooth x hx.2 (by have h := hx.1; rw [hrangeS] at h; exact h)).mono inter_subset_left
  have hUD : UniqueDiffOn ℝ (range halfCollarModel ∩ O) := halfCollarModel.uniqueDiffOn.inter hO
  set f' := fderivWithin ℝ F (range halfCollarModel ∩ O) with hf'
  have hf : ∀ x ∈ O, 0 ≤ ℓ x → HasFDerivWithinAt F (f' x) {x | 0 ≤ ℓ x} x := by
    intro x hxO hx
    have hxR : x ∈ range halfCollarModel ∩ O := ⟨by rw [hrangeS]; exact hx, hxO⟩
    have h := ((hCD.differentiableOn one_ne_zero) x hxR).hasFDerivWithinAt
    rw [hasFDerivWithinAt_inter (hO.mem_nhds hxO)] at h
    exact h.mono hrangeS.symm.subset
  have hpR : φ p ∈ range halfCollarModel ∩ O := ⟨extChartAt_target_subset_range p
    (mem_extChartAt_target p), hpO⟩
  have hcf' : ContinuousWithinAt f' {x | 0 ≤ ℓ x} (φ p) := by
    have h := (hCD.continuousOn_fderivWithin hUD le_rfl) (φ p) hpR
    rw [continuousWithinAt_inter (hO.mem_nhds hpO)] at h
    exact h.mono hrangeS.symm.subset
  -- the derivative at `φ p` is the manifold derivative, injective hence invertible
  have hmd : MDifferentiableAt halfCollarModel W.model e.toFun p :=
    ((e.contMDiffOn p hp).contMDiffAt (isOpen_cuspDomain.mem_nhds hp)).mdifferentiableAt
      (by simp)
  have hf'p : f' (φ p) = mfderiv halfCollarModel W.model e.toFun p := by
    rw [hmd.mfderiv, hf', fderivWithin_inter (hO.mem_nhds hpO)]
    rfl
  have hinj : Injective (mfderiv halfCollarModel W.model e.toFun p) := e.immersion p hp
  have hdim : Module.finrank ℝ
      ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1)) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    simp [Module.finrank_prod]
  let L : (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1) →L[ℝ]
      EuclideanSpace ℝ (Fin 3) := mfderiv halfCollarModel W.model e.toFun p
  let A := (L.toLinearMap.linearEquivOfInjective hinj hdim).toContinuousLinearEquiv
  have hA : f' (φ p) = (A : _ →L[ℝ] EuclideanSpace ℝ (Fin 3)) := by
    rw [hf'p]
    exact ContinuousLinearMap.ext fun v => rfl
  -- the half-space conditions
  have hpos : ∀ x ∈ O, 0 ≤ ℓ x → 0 ≤ μ (F x) := by
    intro x hxO hx
    obtain ⟨-, -, hxψ⟩ := hmem x hxO hx
    have h := extChartAt_target_subset_range (e.toFun p) (ψ.map_source hxψ)
    rw [hrangeT] at h
    exact h
  have hbdry : ∀ x ∈ O, ℓ x = 0 → μ (F x) = 0 := by
    intro x hxO hx
    obtain ⟨hxt, hxS, hxψ⟩ := hmem x hxO hx.ge
    have hzq : (φ.symm x).2.val 0 = 0 := by
      rw [← extChartAt_halfCollarModel_height p, φ.right_inv hxt]
      exact hx
    have hb := (e.boundary_preimage (hSd hxS)).mpr hzq
    have hni : ¬ W.model.IsInteriorPoint (e.toFun (φ.symm x)) :=
      (W.model.isBoundaryPoint_iff_not_isInteriorPoint _).mp hb
    rw [isInteriorPoint_iff_extChartAt_mem_interior_range hxψ, hrangeT,
      ← range_modelWithCornersEuclideanHalfSpace 3,
      interior_range_modelWithCornersEuclideanHalfSpace] at hni
    have h0 := hpos x hxO hx.ge
    change ¬ 0 < (ψ (e.toFun (φ.symm x))) 0 at hni
    change 0 ≤ (ψ (e.toFun (φ.symm x))) 0 at h0
    change (ψ (e.toFun (φ.symm x))) 0 = 0
    linarith [not_lt.mp hni]
  have himg := DifferentialGeometry.Analysis.image_mem_nhdsWithin_halfSpace hn hμ hO hpO
    (by rw [← hz]; rfl) hf hcf' hA hpos hbdry
  have hFp : F (φ p) = ψ (e.toFun p) := by
    simp only [hF, comp_apply, φ.left_inv (mem_extChartAt_source p)]
  rw [hFp] at himg
  have hT : {y : EuclideanSpace ℝ (Fin 3) | 0 ≤ μ y} = range W.model := hrangeT.symm
  rw [hT, ← map_extChartAt_nhds] at himg
  filter_upwards [himg, (isOpen_extChartAt_source (I := W.model) (e.toFun p)).mem_nhds
    (mem_extChartAt_source (I := W.model) (e.toFun p))] with w hw hwψ
  obtain ⟨x, ⟨hx, hxO⟩, hxw⟩ := hw
  obtain ⟨-, hxS, hxψ⟩ := hmem x hxO hx
  refine ⟨φ.symm x, hxS, ψ.injOn hxψ hwψ ?_⟩
  exact hxw

/-- The image of an open subset of the cusp domain is open, boundary points included. -/
theorem CuspEmbedding.isOpen_image {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) {S : Set CuspHalfSpace} (hS : IsOpen S)
    (hSd : S ⊆ cuspDomain) : IsOpen (e.toFun '' S) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨p, hp, rfl⟩
  rcases (p.2.property : 0 ≤ p.2.val 0).eq_or_lt with h0 | hpos
  · exact e.image_mem_nhds_of_height_zero hS hSd hp h0.symm
  · obtain ⟨Φ, hpΦ, -, heq, -, -⟩ := e.exists_finiteInteriorPatch (hSd hp) hpos
    have hopen : IsOpen (Φ '' (Φ.source ∩ S)) :=
      Φ.toOpenPartialHomeomorph.isOpen_image_source_inter hS
    have hmem : e.toFun p ∈ Φ '' (Φ.source ∩ S) := ⟨p, ⟨hpΦ, hp⟩, (heq hpΦ).symm⟩
    apply Filter.mem_of_superset (hopen.mem_nhds hmem)
    rintro z ⟨q, ⟨hqΦ, hqS⟩, rfl⟩
    exact ⟨q, hqS, heq hqΦ⟩

/-- The whole cusp collar `e(T² × [0, 100))` is open in the carrier. -/
theorem CuspEmbedding.isOpen_image_cuspDomain {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) : IsOpen (e.toFun '' cuspDomain) :=
  e.isOpen_image isOpen_cuspDomain subset_rfl

end DifferentialGeometry.Geometry.Collapse
