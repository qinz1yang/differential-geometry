/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.External.CanonicalTopology.Topology.Homotopy.ConvexPlaneExtension
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.OpenTargetApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.Prism
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphTopology

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem exists_continuous_convex_disk_extension
    {Q : Type*} [TopologicalSpace Q] [SimplyConnectedSpace Q]
    {P : Set (EuclideanSpace ℝ (Fin 2))} (hP : IsCompact P) (hc : Convex ℝ P)
    (hi : (interior P).Nonempty) (f : C(frontier P, Q)) :
    ∃ F : C(P, Q), ∀ z : frontier P, F ⟨z.val, hP.isClosed.frontier_subset z.property⟩ = f z := by
  let e : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] ℂ :=
    ((EuclideanSpace.equiv (Fin 2) ℝ).trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)).trans
      Complex.equivRealProdCLM.symm
  have hfront : e '' frontier P = frontier (e '' P) := e.toHomeomorph.image_frontier P
  have hbd : ∀ z ∈ frontier (e '' P), e.symm z ∈ frontier P := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hfront.symm.subset hz
    simpa only [e.symm_apply_apply] using hw
  let f' : C(frontier (e '' P), Q) :=
    ⟨fun z => f ⟨e.symm z, hbd z z.property⟩,
      f.continuous.comp ((e.symm.continuous.comp continuous_subtype_val).subtype_mk _)⟩
  obtain ⟨F, hF⟩ := exists_convex_plane_boundary_extension
    (hc.linear_image e.toLinearMap) (hP.image e.continuous).isClosed
    (hP.image e.continuous).isBounded
    (e.toHomeomorph.image_interior P ▸ hi.image e) f'
  let G : C(P, Q) := ⟨fun z => F ⟨e z, mem_image_of_mem e z.property⟩,
    F.continuous.comp ((e.continuous.comp continuous_subtype_val).subtype_mk _)⟩
  refine ⟨G, fun z => ?_⟩
  have hz : e z ∈ frontier (e '' P) := hfront.subset (mem_image_of_mem e z.property)
  exact (hF ⟨e z, hz⟩).trans (congrArg f (Subtype.ext (e.symm_apply_apply z)))

private theorem exists_piecewise_affine_convex_disk_extension
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Set (EuclideanSpace ℝ (Fin 2))} (hP : IsPLBall 2 P) (hc : Convex ℝ P)
    {U : Set E} (hU : IsOpen U) [SimplyConnectedSpace U]
    {f : EuclideanSpace ℝ (Fin 2) → E} (hf : IsPiecewiseAffineOn f (frontier P))
    (hmap : MapsTo f (frontier P) U) :
    ∃ g : EuclideanSpace ℝ (Fin 2) → E,
      IsPiecewiseAffineOn g P ∧ EqOn g f (frontier P) ∧ MapsTo g P U := by
  classical
  have hbd : frontier P ⊆ P := hP.isPolyhedron.isClosed.frontier_subset
  let b : C(frontier P, U) :=
    ⟨fun z => ⟨f z, hmap z.property⟩, hf.continuousOn.domRestrict.subtype_mk _⟩
  obtain ⟨F, hF⟩ := exists_continuous_convex_disk_extension
    hP.isPolyhedron.isCompact hc hP.interior_nonempty b
  let v : EuclideanSpace ℝ (Fin 2) → E :=
    fun z => if hz : z ∈ P then (F ⟨z, hz⟩ : E) else 0
  have hv (z : P) : v z = (F z : E) := by simp only [v, dite_eq_left z.property]
  have hvcont : ContinuousOn v P := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_subtype_val.comp F.continuous).congr (fun z => (hv z).symm)
  have hvbd : EqOn v f (frontier P) := fun z hz =>
    (hv ⟨z, hbd hz⟩).trans (congrArg (fun w : U => (w : E)) (hF ⟨z, hz⟩))
  obtain ⟨g, hg, hgv, hgmap⟩ := exists_isPiecewiseAffineOn_mapsTo_eqOn
    hP.isPolyhedron hP.isPLSphere_frontier.isPolyhedron hbd hU hvcont (hf.congr hvbd)
    (fun z hz => by rw [hv ⟨z, hz⟩]; exact (F ⟨z, hz⟩).property)
  exact ⟨g, hg, hgv.trans hvbd, hgmap⟩

theorem IsPLBall.exists_isPiecewiseAffineOn_extension
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Set (EuclideanSpace ℝ (Fin 2))} (hP : IsPLBall 2 P)
    {U : Set E} (hU : IsOpen U) [SimplyConnectedSpace U]
    {f : EuclideanSpace ℝ (Fin 2) → E} (hf : IsPiecewiseAffineOn f (frontier P))
    (hmap : MapsTo f (frontier P) U) :
    ∃ g : EuclideanSpace ℝ (Fin 2) → E,
      IsPiecewiseAffineOn g P ∧ EqOn g f (frontier P) ∧ MapsTo g P U := by
  let e : (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans (EuclideanSpace.equiv (Fin 2) ℝ).symm
  let C := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  have he : IsPLHomeomorphOn e C (e '' C) :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isPLBall_unit_square.isPolyhedron
      ((isPiecewiseAffineOn_of_affine e.toLinearMap.toAffineMap isOpen_univ).mono_of_isPolyhedron
        isPLBall_unit_square.isPolyhedron (subset_univ _)) e.injective.injOn.bijOn_image
  have hQ : IsPLBall 2 (e '' C) := isPLBall_unit_square.of_isPLHomeomorphOn he
  have hQc : Convex ℝ (e '' C) :=
    ((convex_Icc (0 : ℝ) 1).prod (convex_Icc (0 : ℝ) 1)).linear_image e.toLinearMap
  obtain ⟨r, hr⟩ := hP
  obtain ⟨s, hs⟩ := hQ
  let φ := r ∘ Function.invFunOn s (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
  have hφ : IsPLHomeomorphOn φ (e '' C) P := hs.symm.trans hr
  have hP : IsPLBall 2 P := ⟨r, hr⟩
  have hQ : IsPLBall 2 (e '' C) := ⟨s, hs⟩
  have hbdQ := hQ.isPolyhedron.isClosed.frontier_subset
  have hbdP := hP.isPolyhedron.isClosed.frontier_subset
  have hfront := hφ.image_frontier rfl hQ.isPolyhedron.isClosed hP.isPolyhedron.isClosed
  have hfrontmap : MapsTo φ (frontier (e '' C)) (frontier P) :=
    fun z hz => hfront.subset (mem_image_of_mem φ hz)
  have hfφ : IsPiecewiseAffineOn (f ∘ φ) (frontier (e '' C)) := by
    have h := hf.comp (hφ.isPiecewiseAffineOn.mono_of_isPolyhedron
      hQ.isPLSphere_frontier.isPolyhedron hbdQ)
    have hsub : frontier (e '' C) ⊆ φ ⁻¹' frontier P := hfrontmap
    rwa [inter_eq_self_of_subset_left hsub] at h
  obtain ⟨g, hg, hgeq, hgmap⟩ := exists_piecewise_affine_convex_disk_extension hQ hQc hU
    hfφ (hmap.comp hfrontmap)
  let ψ := Function.invFunOn φ (e '' C)
  have hψ : MapsTo ψ P (e '' C) := hφ.symm.bijOn.mapsTo
  have hψfront : MapsTo ψ (frontier P) (frontier (e '' C)) := by
    intro z hz
    exact (hφ.symm.image_frontier rfl hP.isPolyhedron.isClosed hQ.isPolyhedron.isClosed).subset
      (mem_image_of_mem ψ hz)
  refine ⟨g ∘ ψ, ?_, ?_, hgmap.comp hψ⟩
  · have h := hg.comp hφ.symm.isPiecewiseAffineOn
    change IsPiecewiseAffineOn (g ∘ ψ) (P ∩ ψ ⁻¹' (e '' C)) at h
    have hsub : P ⊆ ψ ⁻¹' (e '' C) := hψ
    rwa [inter_eq_self_of_subset_left hsub] at h
  · intro z hz
    change g (ψ z) = f z
    rw [hgeq (hψfront hz)]
    exact congrArg f (hφ.bijOn.invOn_invFunOn.2 (hbdP hz))

end DifferentialGeometry.Topology.PiecewiseLinear
