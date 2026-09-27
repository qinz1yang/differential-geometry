/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ProjectedCellInDouble
import DifferentialGeometry.Topology.PiecewiseLinear.SingularManifoldLocal

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem SingularTwoCell.exists_small_interior_doubleCrossing_in_chart
    {X : Type*} [MetricSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    (D : SingularTwoCell X) {C : Set X}
    (hmap : MapsTo D D.domain C)
    (hproper : D.domain ∩ D ⁻¹' frontier C = frontier D.domain)
    (hloc : IsLocallyInjective (D.domain.domRestrict D))
    (hcard : ∀ z, (D.domain ∩ D ⁻¹' {z}).encard ≤ 2)
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin 3)))
    (he : e ∈ (plGroupoid 3).maximalAtlas X)
    {y : X} (hy : y ∈ doublePointSet D D.domain) (hye : y ∈ e.source)
    (hyC : y ∈ interior C) {V : Set X} (hV : V ∈ 𝓝 y) :
    ∃ W : Set X, IsOpen W ∧ y ∈ W ∧ closure W ⊆ V ∩ interior C ∧ W ⊆ e.source ∧
      ∀ ε : ℝ, 0 < ε → ∃ (A : SingularTwoCell X)
        (G : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))),
        A.domain = D.domain ∧ (∀ x, dist (A x) (D x) < ε) ∧
        EqOn A D (frontier D.domain) ∧
        EqOn A D (D ⁻¹' (V ∩ interior C)ᶜ) ∧ MapsTo A A.domain C ∧
        A.domain ∩ A ⁻¹' frontier C = frontier A.domain ∧
        A '' A.domain ∩ frontier C = range A.boundary ∧
        range A.boundary = range D.boundary ∧
        (∀ z ∉ V ∩ interior C, A ⁻¹' {z} = D ⁻¹' {z}) ∧
        IsLocallyInjective (A.domain.domRestrict A) ∧
        (∀ z, (A.domain ∩ A ⁻¹' {z}).encard ≤ 2) ∧
        G.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 1 G ∧
        (∀ z ∈ W, z ∈ doublePointSet A A.domain ↔ e z ∈ G.space) ∧
        ∀ z ∈ W ∩ doublePointSet A A.domain,
          HasPLDoubleCrossingAt (e ∘ A) (A.domain ∩ A ⁻¹' e.source) (e z) := by
  obtain ⟨K, hKfin, hKP⟩ := D.isPLBall_domain.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hK : IsCombinatorialManifoldWithBoundary 2 K :=
    (hKP.symm ▸ D.isPLBall_domain).isCombinatorialManifoldWithBoundary
  obtain ⟨W, hW, hyW, hWV, hWe, hsmall⟩ :=
    exists_isOpen_forall_exists_small_isPLOn_crossing_in_chart K hK D (hKP.symm ▸ D.isPLOn)
      (hKP.symm ▸ hloc) (hKP.symm ▸ hcard) e he (hKP.symm ▸ hy) hye
      (Filter.inter_mem hV (isOpen_interior.mem_nhds hyC))
  refine ⟨W, hW, hyW, hWV, hWe, fun ε hε => ?_⟩
  obtain ⟨g, G, hg, hclose, hgloc, hgcard, hfiber, hGfin, hGman, hGspace, hcross⟩ := hsmall ε hε
  rw [hKP] at hg hgloc hgcard hGspace hcross
  let A : SingularTwoCell X :=
    { domain := D.domain
      isPLBall_domain := D.isPLBall_domain
      toFun := g
      isPLOn := hg }
  have hfix : EqOn A D (D ⁻¹' (V ∩ interior C)ᶜ) := by
    intro x hx
    have hmem : x ∈ A ⁻¹' {D x} :=
      (hfiber (D x) hx).symm ▸ (show x ∈ D ⁻¹' {D x} from rfl)
    exact hmem
  have hfrontnot (z : X) (hz : z ∈ frontier C) : z ∉ V ∩ interior C := by
    intro hin
    exact hz.2 hin.2
  have hboundary : EqOn A D (frontier D.domain) := by
    intro x hx
    exact hfix (hfrontnot (D x) (hproper.superset hx).2)
  have hmapA : MapsTo A A.domain C := by
    intro x hx
    by_contra hnot
    change g x ∉ C at hnot
    have hv : g x ∉ V ∩ interior C := fun hi => hnot (interior_subset hi.2)
    have heq : D x = g x := (hfiber (g x) hv).subset rfl
    exact hnot (heq ▸ hmap hx)
  have hpreA : A.domain ∩ A ⁻¹' frontier C = frontier A.domain := by
    apply Subset.antisymm
    · rintro x ⟨hx, hfront⟩
      apply hproper.subset
      refine ⟨hx, ?_⟩
      have heq : D x = g x := (hfiber (g x) (hfrontnot _ hfront)).subset rfl
      change D x ∈ frontier C
      rw [heq]
      exact hfront
    · intro x hx
      refine ⟨(hproper.superset hx).1, ?_⟩
      change A x ∈ frontier C
      rw [hboundary hx]
      exact (hproper.superset hx).2
  have hinter : A '' A.domain ∩ frontier C = range A.boundary := by
    rw [← image_inter_preimage, hpreA]
    ext z
    exact ⟨fun ⟨x, hx, hxz⟩ => ⟨⟨x, hx⟩, hxz⟩,
      fun ⟨x, hxz⟩ => ⟨x, x.2, hxz⟩⟩
  have hboundaryRange : range A.boundary = range D.boundary := by
    have heq : (fun x : frontier D.domain => A.boundary x) = D.boundary := by
      funext x
      exact hboundary x.2
    exact congrArg range heq
  exact ⟨A, G, rfl, hclose, hboundary, hfix, hmapA, hpreA, hinter, hboundaryRange,
    hfiber, hgloc, hgcard, hGfin, hGman, hGspace, hcross⟩

end DifferentialGeometry.Topology.PiecewiseLinear
