import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspFirstExit

/-!
# Consumers of the boundary openness, the `C¹` inverse coordinate and the first exit

* `NearlyCuspidalBoundary.isOpen_iUnion_collar`,
  `NearlyCuspidalBoundary.boundary_subset_iUnion_collar`: the open collars of a nearly cuspidal boundary form an open neighbourhood of `∂W`;
* `CuspEmbedding.contMDiffOn_height_invFunOn`: the actual collar height `z ∘ e⁻¹` is `C¹` on the
  open collar, boundary included;
* the interface statements E.1–E.3 of `build-logs/scratch/BDY-FILL/BoundaryInterfaces.lean`,
  verbatim, as `example`s.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- The union of the collars of a nearly cuspidal boundary is open. -/
theorem NearlyCuspidalBoundary.isOpen_iUnion_collar {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ) : IsOpen (⋃ i, (B.collar i).toFun '' cuspDomain) :=
  isOpen_iUnion fun i => (B.collar i).isOpen_image_cuspDomain

/-- The collars of a nearly cuspidal boundary cover the boundary. -/
theorem NearlyCuspidalBoundary.boundary_subset_iUnion_collar {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ) :
    W.model.boundary W.Carrier ⊆ ⋃ i, (B.collar i).toFun '' cuspDomain := by
  intro w hw
  rw [← B.covers] at hw
  obtain ⟨i, hwi⟩ := mem_iUnion.mp hw
  rw [← (B.collar i).boundary_image] at hwi
  obtain ⟨t, rfl⟩ := hwi
  refine mem_iUnion.mpr ⟨i, (t, halfZero), ?_, rfl⟩
  change (halfZero : EuclideanHalfSpace 1).val 0 < cuspDepth
  change (0 : ℝ) < 100
  norm_num

/-- The collar height `z ∘ e⁻¹` is `C¹` on the open collar `e(T² × [0, 100))`. -/
theorem CuspEmbedding.contMDiffOn_height_invFunOn {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) :
    ContMDiffOn W.model 𝓘(ℝ, ℝ) 1 (fun y => (invFunOn e.toFun cuspDomain y).2.val 0)
      (e.toFun '' cuspDomain) := by
  have hz : ContMDiff halfCollarModel 𝓘(ℝ, ℝ) 1
      ((EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ) ∘ (𝓡∂ 1) ∘
        Prod.snd) :=
    (ContinuousLinearMap.contMDiff _).comp ((𝓡∂ 1).contMDiff.comp
      (contMDiff_snd (M := Torus) (N := EuclideanHalfSpace 1)))
  exact hz.comp_contMDiffOn e.contMDiffOn_invFunOn

section Interface

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier}
  {K : ℕ} {δ : ℝ} {X : Set W.Carrier}

/-- Interface E.1, verbatim. -/
example (e : CuspEmbedding W g K δ X) {h : ℝ} (hh : h ≤ cuspDepth) :
    IsOpen (e.toFun '' {p : CuspHalfSpace | p.2.val 0 < h}) :=
  e.isOpen_image_height_lt hh

/-- Interface E.2, verbatim. -/
example (e : CuspEmbedding W g K δ X) {h : ℝ} (hh0 : 0 < h) (hh : h < cuspDepth) :
    frontier (e.toFun '' {p : CuspHalfSpace | p.2.val 0 < h}) =
      e.toFun '' {p : CuspHalfSpace | p.2.val 0 = h} :=
  e.frontier_image_height_lt hh0 hh

/-- Interface E.3, verbatim (the hypothesis `δ < 1` is not needed). -/
example (e : CuspEmbedding W g K δ X) (_hδ : δ < 1) {h : ℝ} (hh : h < cuspDepth)
    {p : CuspHalfSpace} (hph : p.2.val 0 < h) {y : W.Carrier}
    (hy : y ∉ e.toFun '' {q : CuspHalfSpace | q.2.val 0 < h}) :
    ENNReal.ofReal (Real.sqrt (1 - δ) * (h - p.2.val 0)) ≤ riemannianEDistOf g (e.toFun p) y :=
  e.ofReal_le_riemannianEDistOf_of_not_mem_image_height_lt hh hph hy

end Interface

end DifferentialGeometry.Geometry.Collapse
