import DifferentialGeometry.Geometry.Collapse.CuspBoundary
import DifferentialGeometry.Topology.InvarianceOfDomainManifold
import DifferentialGeometry.Topology.Manifold.InteriorChart

/-!
# CH12 C4: the `boundary_preimage` field of a cusp collar from invariance of domain

For a continuous map `toFun` of the cusp half space which is injective on `cuspDomain`, whose
height-zero slice lands in `∂W`, a point of positive height cannot land in `∂W` (invariance of
domain in a chart), so `toFun p ∈ ∂W ↔ height p = 0` on `cuspDomain`.
-/

set_option autoImplicit false

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Manifold
open GC.Endpoint
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u

theorem isOpen_cuspDomain_C4 : IsOpen cuspDomain :=
  isOpen_lt ((EuclideanSpace.proj 0).continuous.comp
    (continuous_subtype_val.comp continuous_snd)) continuous_const

private theorem eq_halfZero_C4 {q : EuclideanHalfSpace 1} (h : q.val 0 = 0) : q = halfZero := by
  apply Subtype.ext
  ext i
  fin_cases i
  exact h

theorem halfCollar_interior_C4 {p : CuspHalfSpace} (hpos : 0 < p.2.val 0) :
    halfCollarModel.IsInteriorPoint p := by
  change p ∈ (torusModel.prod (𝓡∂ 1)).interior (Torus × EuclideanHalfSpace 1)
  rw [ModelWithCorners.interior_prod]
  refine ⟨BoundarylessManifold.isInteriorPoint, ?_⟩
  change (𝓡∂ 1).IsInteriorPoint p.2
  simpa only [ModelWithCorners.IsInteriorPoint, extChartAt_self_apply,
    interior_range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq,
    modelWithCornersEuclideanHalfSpace_apply] using hpos

/-- A point of positive height of a continuous injective cusp collar is an interior point of the
target. -/
theorem interior_of_pos_C4 {W : CompactCarrier.{u}} {toFun : CuspHalfSpace → W.Carrier}
    (hcont : ContinuousOn toFun cuspDomain) (hinj : InjOn toFun cuspDomain)
    {p : CuspHalfSpace} (hp : p ∈ cuspDomain) (hpos : 0 < p.2.val 0) :
    W.model.IsInteriorPoint (toFun p) := by
  let ψ := extChartAt halfCollarModel p
  let φ := extChartAt W.model (toFun p)
  have hψp : ψ p ∈ interior ψ.target :=
    halfCollarModel.isInteriorPoint_iff.mp (halfCollar_interior_C4 hpos)
  have hV : IsOpen (cuspDomain ∩ toFun ⁻¹' φ.source) :=
    hcont.isOpen_inter_preimage isOpen_cuspDomain_C4 (isOpen_extChartAt_source (toFun p))
  have hU : IsOpen (interior ψ.target ∩ ψ.symm ⁻¹' (cuspDomain ∩ toFun ⁻¹' φ.source)) :=
    ((continuousOn_extChartAt_symm p).mono interior_subset).isOpen_inter_preimage
      isOpen_interior hV
  let F0 := φ ∘ toFun ∘ ψ.symm
  have hψsrc : p ∈ ψ.source := mem_extChartAt_source p
  have hmem : ψ p ∈ interior ψ.target ∩ ψ.symm ⁻¹' (cuspDomain ∩ toFun ⁻¹' φ.source) := by
    refine ⟨hψp, ?_⟩
    change ψ.symm (ψ p) ∈ cuspDomain ∩ toFun ⁻¹' φ.source
    rw [ψ.left_inv hψsrc]
    exact ⟨hp, mem_extChartAt_source (toFun p)⟩
  have hcontF : ContinuousOn F0
      (interior ψ.target ∩ ψ.symm ⁻¹' (cuspDomain ∩ toFun ⁻¹' φ.source)) := by
    have h1 : ContinuousOn ψ.symm
        (interior ψ.target ∩ ψ.symm ⁻¹' (cuspDomain ∩ toFun ⁻¹' φ.source)) :=
      (continuousOn_extChartAt_symm p).mono (inter_subset_left.trans interior_subset)
    have h2 : ContinuousOn toFun (cuspDomain ∩ toFun ⁻¹' φ.source) :=
      hcont.mono inter_subset_left
    have h3 : ContinuousOn φ φ.source := continuousOn_extChartAt (toFun p)
    exact h3.comp (h2.comp h1 (fun z hz => hz.2)) (fun z hz => hz.2.2)
  have hinjF : InjOn F0 (interior ψ.target ∩ ψ.symm ⁻¹' (cuspDomain ∩ toFun ⁻¹' φ.source)) := by
    intro x hx y hy hxy
    have hφ := φ.injOn hx.2.2 hy.2.2 hxy
    have h2 := hinj hx.2.1 hy.2.1 hφ
    exact ψ.symm.injOn (by rw [PartialEquiv.symm_source]; exact interior_subset hx.1)
      (by rw [PartialEquiv.symm_source]; exact interior_subset hy.1) h2
  have hdim : Module.finrank ℝ
      ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1)) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    simp [Module.finrank_prod]
  have hopen := DifferentialGeometry.Topology.invariance_of_domain_isOpen_image_of_finrank_eq
    hdim hU hcontF hinjF
  have hsub : F0 '' (interior ψ.target ∩ ψ.symm ⁻¹' (cuspDomain ∩ toFun ⁻¹' φ.source)) ⊆
      Set.range W.model := by
    rintro _ ⟨z, hz, rfl⟩
    have := φ.map_source hz.2.2
    rw [extChartAt_target] at this
    exact this.2
  have hFp : F0 (ψ p) = φ (toFun p) := by
    show φ (toFun (ψ.symm (ψ p))) = _
    rw [ψ.left_inv hψsrc]
  have hint : φ (toFun p) ∈ interior (Set.range W.model) :=
    (hopen.subset_interior_iff.mpr hsub) ⟨ψ p, hmem, hFp⟩
  exact hint

/-- **`boundary_preimage` for a cusp collar.** -/
theorem boundary_preimage_C4 {W : CompactCarrier.{u}} {toFun : CuspHalfSpace → W.Carrier}
    (hcont : ContinuousOn toFun cuspDomain) (hinj : InjOn toFun cuspDomain)
    (hslice : ∀ t : Torus, toFun (t, halfZero) ∈ W.model.boundary W.Carrier) :
    ∀ {p : CuspHalfSpace}, p ∈ cuspDomain →
      (toFun p ∈ W.model.boundary W.Carrier ↔ p.2.val 0 = 0) := by
  intro p hp
  constructor
  · intro hb
    by_contra hne
    have hnn : 0 ≤ p.2.val 0 := p.2.property
    have hpos : 0 < p.2.val 0 := lt_of_le_of_ne hnn (Ne.symm hne)
    have hi := interior_of_pos_C4 hcont hinj hp hpos
    exact ((W.model.isInteriorPoint_iff_not_isBoundaryPoint _).mp hi) hb
  · intro h0
    have : p = (p.1, halfZero) := Prod.ext rfl (eq_halfZero_C4 h0)
    rw [this]
    exact hslice p.1

end GC.LongTime.Ch12
