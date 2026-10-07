import DifferentialGeometry.Geometry.Collapse.CuspBoundary
import DifferentialGeometry.Topology.HalfSpaceInvarianceOfDomain
import DifferentialGeometry.Topology.Manifold.EuclideanHalfSpaceProd
import DifferentialGeometry.Topology.Manifold.HalfLine

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Topology.Manifold GC.Endpoint Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u

private abbrev TorusCoordinates :=
  EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)

private def targetHalfSpaceHomeomorph :
    EuclideanHalfSpace 3 ≃ₜ EuclideanSpace ℝ (Fin 2) × Ici (0 : ℝ) :=
  DifferentialGeometry.Manifold.euclideanHalfSpaceProdHomeomorph.symm.trans
    (Homeomorph.prodCongr (Homeomorph.refl _) halfSpaceOneHomeomorph)

private theorem targetHalfSpaceHomeomorph_height (y : EuclideanHalfSpace 3) :
    (targetHalfSpaceHomeomorph y).2.val = y.val 0 := by
  change (DifferentialGeometry.Manifold.euclideanHalfSpaceProdCoordinates.symm y.val).2 0 =
    y.val 0
  rw [← DifferentialGeometry.Manifold.euclideanHalfSpaceProdCoordinates_apply_zero,
    ContinuousLinearEquiv.apply_symm_apply]

private theorem isOpen_image_cusp_of_boundary_preimage
    {k : CarrierModel} {M : Type u} [TopologicalSpace M] [ChartedSpace k.Space M]
    {f : CuspHalfSpace → M} (hf : ContinuousOn f cuspDomain)
    (hinj : InjOn f cuspDomain)
    (hboundary : ∀ p ∈ cuspDomain,
      f p ∈ k.model.boundary M ↔ p.2.val 0 = 0) :
    IsOpen (f '' cuspDomain) := by
  have hdomain : IsOpen cuspDomain :=
    isOpen_lt ((EuclideanSpace.proj 0).continuous.comp
      (continuous_subtype_val.comp continuous_snd)) continuous_const
  cases k with
  | closed =>
      have hp : (((1, 1) : Torus), halfZero) ∈ cuspDomain := by
        norm_num [cuspDomain, cuspDepth, halfZero, halfPoint]
      have hb := (hboundary _ hp).mpr (by rfl)
      have hempty : (𝓡 3).boundary M = ∅ :=
        ModelWithCorners.Boundaryless.boundary_eq_empty
      change f (((1, 1) : Torus), halfZero) ∈ (𝓡 3).boundary M at hb
      rw [hempty] at hb
      exact hb.elim
  | withBoundary =>
      rw [isOpen_iff_mem_nhds]
      rintro y ⟨p, hp, rfl⟩
      let cT : OpenPartialHomeomorph Torus TorusCoordinates :=
        (chartAt (EuclideanSpace ℝ (Fin 1)) p.1.1).prod
          (chartAt (EuclideanSpace ℝ (Fin 1)) p.1.2)
      let c : OpenPartialHomeomorph CuspHalfSpace (TorusCoordinates × Ici (0 : ℝ)) :=
        cT.prod halfSpaceOneHomeomorph.toOpenPartialHomeomorph
      let d₀ : OpenPartialHomeomorph M (EuclideanHalfSpace 3) :=
        chartAt (EuclideanHalfSpace 3) (f p)
      let d : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2) × Ici (0 : ℝ)) :=
        d₀.trans targetHalfSpaceHomeomorph.toOpenPartialHomeomorph
      have hpc : p ∈ c.source := by
        exact ⟨⟨mem_chart_source (EuclideanSpace ℝ (Fin 1)) p.1.1,
          mem_chart_source (EuclideanSpace ℝ (Fin 1)) p.1.2⟩, mem_univ p.2⟩
      have hpd : f p ∈ d.source := by
        exact ⟨mem_chart_source (EuclideanHalfSpace 3) (f p), mem_univ _⟩
      have hcheight (z : TorusCoordinates × Ici (0 : ℝ)) :
          (c.symm z).2.val 0 = z.2.val := by
        change (halfSpaceOneHomeomorph.symm z.2).val 0 = z.2.val
        exact congrArg Subtype.val (halfSpaceOneHomeomorph.apply_symm_apply z.2)
      have hdheight (q : M) : (d q).2.val = (d₀ q).val 0 :=
        targetHalfSpaceHomeomorph_height (d₀ q)
      have hdboundary (q : M) (hq : q ∈ d.source) :
          (𝓡∂ 3).IsBoundaryPoint q ↔ (d q).2.val = 0 := by
        have hq₀ : q ∈ d₀.source := hq.1
        have h := DifferentialGeometry.Topology.isBoundaryPoint_iff_any_chart_real
          (𝓡∂ 3) (f := d₀) hq₀
        rw [frontier_range_modelWithCornersEuclideanHalfSpace] at h
        change (𝓡∂ 3).IsBoundaryPoint q ↔ 0 = (d₀ q).val 0 at h
        rw [hdheight]
        exact h.trans eq_comm
      let V : Set CuspHalfSpace := cuspDomain ∩ f ⁻¹' d.source
      have hV : IsOpen V := hf.isOpen_inter_preimage hdomain d.open_source
      let U : Set (TorusCoordinates × Ici (0 : ℝ)) := c.target ∩ c.symm ⁻¹' V
      have hU : IsOpen U := c.isOpen_inter_preimage_symm hV
      let F : TorusCoordinates × Ici (0 : ℝ) →
          EuclideanSpace ℝ (Fin 2) × Ici (0 : ℝ) := d ∘ f ∘ c.symm
      have hF : ContinuousOn F U :=
        d.continuousOn.comp
          (hf.comp (c.continuousOn_symm.mono inter_subset_left) (fun _ hz => hz.2.1))
          (fun _ hz => hz.2.2)
      have hFinj : InjOn F U := by
        intro z hz w hw hzw
        apply c.symm.injOn hz.1 hw.1
        apply hinj hz.2.1 hw.2.1
        exact d.injOn hz.2.2 hw.2.2 hzw
      have hFboundary (z : TorusCoordinates × Ici (0 : ℝ)) (hz : z ∈ U) :
          (F z).2.val = 0 ↔ z.2.val = 0 := by
        calc
          (F z).2.val = 0 ↔ (𝓡∂ 3).IsBoundaryPoint (f (c.symm z)) :=
            (hdboundary _ hz.2.2).symm
          _ ↔ (c.symm z).2.val 0 = 0 := hboundary _ hz.2.1
          _ ↔ z.2.val = 0 := by rw [hcheight]
      have hopen : IsOpen (F '' U) :=
        DifferentialGeometry.Topology.isOpen_image_halfSpace_of_continuousOn_injOn_boundary_iff
          (by simp [TorusCoordinates, Module.finrank_prod]) hU hF hFinj hFboundary
      have hcpU : c p ∈ U := by
        refine ⟨c.map_source hpc, ?_⟩
        change c.symm (c p) ∈ V
        rw [c.left_inv hpc]
        exact ⟨hp, hpd⟩
      have hpoint : f p ∈ d.source ∩ d ⁻¹' (F '' U) := by
        refine ⟨hpd, c p, hcpU, ?_⟩
        change d (f (c.symm (c p))) = d (f p)
        rw [c.left_inv hpc]
      apply Filter.mem_of_superset
        ((d.isOpen_inter_preimage hopen).mem_nhds hpoint)
      rintro q ⟨hqd, z, hz, hzq⟩
      refine ⟨c.symm z, hz.2.1, ?_⟩
      exact d.injOn hz.2.2 hqd hzq

/-- The given cusp collar has open image in the original compact carrier.

Renamed from `CuspEmbedding.isOpen_image` (CH12-S47): that name is already taken by the general
statement `CuspEmbedding.isOpen_image` in `BoundaryScale/CuspBoundaryOpenness.lean` (open
subsets of the collar have open image), and the two modules must be importable together. -/
theorem CuspEmbedding.isOpen_image_openness
    {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier}
    {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) :
    IsOpen (e.toFun '' cuspDomain) := by
  apply isOpen_image_cusp_of_boundary_preimage
    (k := W.kind) e.contMDiffOn.continuousOn
  · intro p hp q hq hpq
    exact congrArg Subtype.val (e.isEmbedding.injective
      (show (fun x : cuspDomain => e.toFun x) ⟨p, hp⟩ =
        (fun x : cuspDomain => e.toFun x) ⟨q, hq⟩ from hpq))
  · intro p hp
    exact e.boundary_preimage hp

end DifferentialGeometry.Geometry.Collapse
