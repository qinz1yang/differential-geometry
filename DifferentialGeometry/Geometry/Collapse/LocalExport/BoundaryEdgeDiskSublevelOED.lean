import DifferentialGeometry.Topology.Manifold.RegularLevel.RegularSublevelSlice
import DifferentialGeometry.Topology.Manifold.ImmersionCriterionInteriorTarget
import Mathlib.Geometry.Manifold.SmoothEmbedding

/-!
# Regular sublevels in a boundaryless manifold of ANY model: the inclusion is a smooth embedding
(lane O-EDGEDISK, G1)

The tree proves that the inclusion of a regular sublevel `{Ψ = 0, 0 ≤ B}`
(`regularSublevelChartedSpace`, model `𝓡∂ (d + 1)`) is a smooth embedding only for an ambient
manifold modelled on a normed space itself (`regularSublevel_isSmoothEmbedding_val_EIM`, through
`slice_isImmersionAtOfComplement_val_GARC`). Here the ambient model `I : ModelWithCorners ℝ E H` is
an arbitrary BOUNDARYLESS model: the code chart of `slice_isImmersionAtOfComplement_val_GARC`
(slice chart followed by `q ↦ L (q₁ - c e₀, q₂)`) is followed by the inverse of `I` on the
interior of its range (`modelInverseInterior_GSF`), which is all of `E` because `I` is
boundaryless.

* `sliceChart_mem_maximalAtlas_OED`: every slice chart lies in the maximal atlas (any model `I`);
* `slice_isImmersionAtOfComplement_val_OED`: the slice inclusion is an immersion at a point lying
  in a slice chart with positive first coordinate (boundaryless `I`);
* `regularSublevel_isImmersionAt_of_chart_OED`, `regularSublevel_isSmoothEmbedding_val_OED`: the
  inclusion of a regular sublevel with boundary is a smooth embedding.
-/

set_option autoImplicit false
noncomputable section
open Set Function Filter Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Manifold.RegularLevel

section Immersion

variable {d : ℕ} {E' H' M F : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {I : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M] [ChartedSpace H' M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (P Bd : M → Prop)
  (hP : ∀ x, P x → ∃ p : PartialDiffeomorph I ((𝓡∂ (d + 1)).prod 𝓘(ℝ, F)) M
        (EuclideanHalfSpace (d + 1) × F) ∞ × ℝ,
      0 ≤ p.2 ∧ x ∈ p.1.source ∧
      (∀ y ∈ p.1.source, P y ↔ ((p.1 y).2 = 0 ∧ p.2 ≤ (p.1 y).1.1 0)) ∧
      ((p.1 x).1.1 0 = p.2 ↔ Bd x))

/-- Every slice chart (not only the chosen ones) lies in the maximal atlas of `{x // P x}`. -/
theorem sliceChart_mem_maximalAtlas_OED
    (Φ : PartialDiffeomorph I ((𝓡∂ (d + 1)).prod 𝓘(ℝ, F)) M
      (EuclideanHalfSpace (d + 1) × F) ∞)
    {c : ℝ} (hc : 0 ≤ c) (hΦ : ∀ y ∈ Φ.source, P y ↔ ((Φ y).2 = 0 ∧ c ≤ (Φ y).1.1 0))
    (x₀ : {x // P x}) :
    letI := sliceChartedSpace P Bd hP
    sliceChart P Φ hc hΦ x₀ ∈ IsManifold.maximalAtlas (𝓡∂ (d + 1)) ∞ {x // P x} := by
  let _ := sliceChartedSpace P Bd hP
  have _ := slice_isManifold P Bd hP
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · have hv : ContMDiffOn (𝓡∂ (d + 1)) ((𝓡∂ (d + 1)).prod 𝓘(ℝ, F)) ∞
        (fun y : {x // P x} => Φ y.1) (Subtype.val ⁻¹' Φ.source) :=
      Φ.contMDiffOn.comp (slice_contMDiff_val P Bd hP).contMDiffOn (fun y hy => hy)
    refine (contMDiffOn_sliceUnshift (d := d) c).comp (contMDiff_fst.comp_contMDiffOn hv) ?_
    intro y hy
    exact ((hΦ y.1 hy).mp y.2).2
  · intro w hw
    have hw' : (sliceShift d c w, (0 : F)) ∈ Φ.target := hw
    rw [slice_contMDiffWithinAt_iff hP le_rfl]
    have hk : ContMDiff (𝓡∂ (d + 1)) ((𝓡∂ (d + 1)).prod 𝓘(ℝ, F)) ∞
        (fun w => (sliceShift d c w, (0 : F))) :=
      (contMDiff_sliceShift hc).prodMk contMDiff_const
    have h1 : ContMDiffWithinAt (𝓡∂ (d + 1)) I ∞
        (fun w => Φ.symm (sliceShift d c w, (0 : F)))
        ((sliceChart P Φ hc hΦ x₀).target) w :=
      (Φ.symm.contMDiffOn.comp hk.contMDiffOn (fun w hw => hw)) w hw
    refine h1.congr (fun w' hw' => ?_) ?_
    · exact sliceChartInv_val P Φ hc hΦ x₀ hw'
    · exact sliceChartInv_val P Φ hc hΦ x₀ hw'

variable [I.Boundaryless] [IsManifold I ∞ M]

/-- **The slice inclusion into a boundaryless manifold of any model is an immersion** at a point
lying in a slice chart with positive first coordinate (code chart: the slice chart, then
`q ↦ L (q₁ - c e₀, q₂)`, then `I⁻¹`). -/
theorem slice_isImmersionAtOfComplement_val_OED
    (L : (EuclideanSpace ℝ (Fin (d + 1)) × F) ≃L[ℝ] E') (x : {x // P x})
    (Φ : PartialDiffeomorph I ((𝓡∂ (d + 1)).prod 𝓘(ℝ, F)) M
      (EuclideanHalfSpace (d + 1) × F) ∞)
    {c : ℝ} (hc : 0 ≤ c) (hΦ : ∀ y ∈ Φ.source, P y ↔ ((Φ y).2 = 0 ∧ c ≤ (Φ y).1.1 0))
    (hx : x.1 ∈ Φ.source) (hpos : ∀ y ∈ Φ.source, 0 < (Φ y).1.1 0) :
    letI := sliceChartedSpace P Bd hP
    IsImmersionAtOfComplement F (𝓡∂ (d + 1)) I ∞ (Subtype.val : {x // P x} → M) x := by
  let _ := sliceChartedSpace P Bd hP
  have hint : ∀ v : E', v ∈ interior (range I) := by
    intro v
    rw [I.range_eq_univ, interior_univ]
    exact mem_univ v
  let ψ : PartialDiffeomorph I I M H' ∞ :=
    Φ.trans ((sliceHalfSpaceProd (d := d) F).symm.trans
      ((sliceAffine L (-L (c • EuclideanSpace.single 0 1, 0))).toPartialDiffeomorph.trans
        (DifferentialGeometry.Topology.Manifold.modelInverseInterior_GSF I ∞)))
  have hψ : ∀ y ∈ Φ.source,
      ψ y = I.symm (L ((Φ y).1.1 - c • EuclideanSpace.single 0 1, (Φ y).2)) := by
    intro y _
    change I.symm (L ((Φ y).1.1, (Φ y).2) + -L (c • EuclideanSpace.single 0 1, 0)) = _
    rw [← map_neg, ← map_add]
    congr 2
    ext <;> simp [sub_eq_add_neg]
  have hψsource : ψ.source = Φ.source := by
    apply Subset.antisymm
    · intro y hy
      exact hy.1
    · intro y hy
      exact ⟨hy, hpos y hy, mem_univ _, hint _⟩
  refine IsImmersionAtOfComplement.mk_of_charts L (sliceChart P Φ hc hΦ x)
    ψ.toOpenPartialHomeomorph hx (hψsource ▸ hx)
    (sliceChart_mem_maximalAtlas_OED P Bd hP Φ hc hΦ x) ?_ ?_ ?_
  · apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
    · exact ψ.contMDiffOn
    · exact ψ.symm.contMDiffOn
  · intro y hy
    change y.1 ∈ ψ.source
    rw [hψsource]
    exact hy
  · intro y hy
    obtain ⟨hy2, hy1⟩ := hy
    set w : EuclideanHalfSpace (d + 1) := (𝓡∂ (d + 1)).symm y with hwdef
    have hw : (sliceShift d c w, (0 : F)) ∈ Φ.target := hy1
    have hwy : w.1 = y := (𝓡∂ (d + 1)).right_inv (by rwa [← ModelWithCorners.target_eq])
    have hinv : (((sliceChart P Φ hc hΦ x).extend (𝓡∂ (d + 1))).symm y : M) =
        Φ.symm (sliceShift d c w, 0) := by
      rw [OpenPartialHomeomorph.extend_coe_symm]
      exact sliceChartInv_val P Φ hc hΦ x hw
    have key : ψ (Φ.symm (sliceShift d c w, (0 : F))) = I.symm (L (y, 0)) := by
      refine (hψ _ (Φ.map_target hw)).trans ?_
      have hr : Φ (Φ.symm (sliceShift d c w, (0 : F))) = (sliceShift d c w, 0) :=
        Φ.right_inv hw
      erw [hr]
      congr 2
      refine Prod.ext ?_ rfl
      change (sliceShift d c w).1 - c • EuclideanSpace.single 0 1 = y
      rw [sliceShift_val hc w, hwy, add_sub_cancel_right]
    change I (ψ (((sliceChart P Φ hc hΦ x).extend (𝓡∂ (d + 1))).symm y : M)) = L (y, 0)
    rw [hinv, key]
    exact I.right_inv (interior_subset (hint _))

end Immersion

section Sublevel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] {d : ℕ}

/-- **Immersion at a point from a slice chart with positive first coordinate at the point** (any
boundaryless model): the chart is restricted to the open set where its first coordinate is
positive. -/
theorem regularSublevel_isImmersionAt_of_chart_OED
    (hdim : Module.finrank ℝ E = d + 1 + Module.finrank ℝ G)
    {Ψ : M → G} (hΨ : ContMDiff I 𝓘(ℝ, G) ∞ Ψ)
    {B : M → ℝ} (hB : ContMDiff I 𝓘(ℝ, ℝ) ∞ B)
    (hreg : ∀ x, Ψ x = 0 → 0 ≤ B x → Surjective (mfderiv I 𝓘(ℝ, G) Ψ x))
    (hregb : ∀ x, Ψ x = 0 → B x = 0 →
      Surjective (mfderiv I 𝓘(ℝ, G × ℝ) (fun y => (Ψ y, B y)) x))
    (x : {x : M // Ψ x = 0 ∧ 0 ≤ B x})
    (Φ : PartialDiffeomorph I ((𝓡∂ (d + 1)).prod 𝓘(ℝ, G)) M
      (EuclideanHalfSpace (d + 1) × G) ∞)
    {c : ℝ} (hc : 0 ≤ c)
    (hΦ : ∀ y ∈ Φ.source, (Ψ y = 0 ∧ 0 ≤ B y) ↔ ((Φ y).2 = 0 ∧ c ≤ (Φ y).1.1 0))
    (hx : x.1 ∈ Φ.source) (hxpos : 0 < (Φ x.1).1.1 0) :
    letI := regularSublevelChartedSpace hdim hΨ hB hreg hregb
    IsImmersionAtOfComplement G (𝓡∂ (d + 1)) I ∞
      (Subtype.val : {x : M // Ψ x = 0 ∧ 0 ≤ B x} → M) x := by
  let _ := regularSublevelChartedSpace hdim hΨ hB hreg hregb
  let L : (EuclideanSpace ℝ (Fin (d + 1)) × G) ≃L[ℝ] E :=
    ContinuousLinearEquiv.ofFinrankEq
      (by rw [Module.finrank_prod, finrank_euclideanSpace_fin, hdim])
  have hcoord : Continuous fun q : EuclideanHalfSpace (d + 1) × G => q.1.1 0 := by fun_prop
  have hopen : IsOpen (Φ.source ∩ {y | 0 < (Φ y).1.1 0}) :=
    Φ.contMDiffOn.continuousOn.isOpen_inter_preimage Φ.open_source
      (isOpen_lt continuous_const hcoord)
  let Φ' := DifferentialGeometry.Topology.PartialDiffeomorph.restrict Φ
    (Φ.source ∩ {y | 0 < (Φ y).1.1 0}) hopen
  have hsrc : Φ'.source = Φ.source ∩ (Φ.source ∩ {y | 0 < (Φ y).1.1 0}) := rfl
  exact slice_isImmersionAtOfComplement_val_OED (fun x => Ψ x = 0 ∧ 0 ≤ B x) (fun x => B x = 0)
    (regularSublevel_sliceCharts hdim hΨ hB hreg hregb) L x Φ' hc
    (fun y hy => hΦ y (by rw [hsrc] at hy; exact hy.1))
    (by rw [hsrc]; exact ⟨hx, hx, hxpos⟩)
    (fun y hy => by rw [hsrc] at hy; exact hy.2.2)

/-- **The inclusion of a regular sublevel with boundary into a boundaryless manifold of any model
is a smooth embedding.** -/
theorem regularSublevel_isSmoothEmbedding_val_OED
    (hdim : Module.finrank ℝ E = d + 1 + Module.finrank ℝ G)
    {Ψ : M → G} (hΨ : ContMDiff I 𝓘(ℝ, G) ∞ Ψ)
    {B : M → ℝ} (hB : ContMDiff I 𝓘(ℝ, ℝ) ∞ B)
    (hreg : ∀ x, Ψ x = 0 → 0 ≤ B x → Surjective (mfderiv I 𝓘(ℝ, G) Ψ x))
    (hregb : ∀ x, Ψ x = 0 → B x = 0 →
      Surjective (mfderiv I 𝓘(ℝ, G × ℝ) (fun y => (Ψ y, B y)) x)) :
    letI := regularSublevelChartedSpace hdim hΨ hB hreg hregb
    IsSmoothEmbedding (𝓡∂ (d + 1)) I ∞
      (Subtype.val : {x : M // Ψ x = 0 ∧ 0 ≤ B x} → M) := by
  let _ := regularSublevelChartedSpace hdim hΨ hB hreg hregb
  refine ⟨IsImmersionOfComplement.isImmersion (F := G) (fun x => ?_),
    Topology.IsEmbedding.subtypeVal⟩
  have hint : I.IsInteriorPoint x.1 := BoundarylessManifold.isInteriorPoint
  rcases x.2.2.eq_or_lt with h0 | hpos
  · obtain ⟨Φ, hxΦ, hΦ1, hΦ⟩ := exists_sliceChart_of_zero hdim hΨ hB hint h0.symm
      (hregb x.1 x.2.1 h0.symm)
    exact regularSublevel_isImmersionAt_of_chart_OED hdim hΨ hB hreg hregb x Φ zero_le_one hΦ
      hxΦ (by rw [hΦ1]; exact one_pos)
  · obtain ⟨Φ, hxΦ, hΦpos, hΦ⟩ := exists_sliceChart_of_pos hdim hΨ hB hint hpos
      (hreg x.1 x.2.1 x.2.2)
    exact regularSublevel_isImmersionAt_of_chart_OED hdim hΨ hB hreg hregb x Φ le_rfl hΦ hxΦ
      (hΦpos x.1 hxΦ)

end Sublevel

end DifferentialGeometry.Manifold.RegularLevel
