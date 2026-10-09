/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CircleParametrization
import DifferentialGeometry.Topology.PiecewiseLinear.DiskFilling
import DifferentialGeometry.Topology.PiecewiseLinear.SimplicialApproximation

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLBall.exists_isPiecewiseAffineOn_filling_freeLoop_homotopic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P : Set (EuclideanSpace ℝ (Fin 2))} (hP : IsPLBall 2 P)
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    {U : Set E} (hU : IsOpen U) (hLU : L.space ⊆ U) [SimplyConnectedSpace U]
    (γ : freeLoop L.space) :
    ∃ g : EuclideanSpace ℝ (Fin 2) → E,
      IsPiecewiseAffineOn g P ∧ MapsTo g P U ∧
      ∃ (b : C(frontier P, L.space)) (e : loopCircle ≃ₜ frontier P),
        (∀ z : frontier P, g z = (b z : E)) ∧
        γ.Homotopic (b.comp (e : C(loopCircle, frontier P))) := by
  obtain ⟨J, hJfin, hJspace⟩ := hP.isPLSphere_frontier.isPolyhedron.exists_simplicialComplex
  let _ : Finite J.faces := hJfin.to_subtype
  obtain ⟨e⟩ := nonempty_homeomorph_loopCircle_of_isPLSphere_one hP.isPLSphere_frontier
  let eJ : loopCircle ≃ₜ J.space := e.trans (Homeomorph.setCongr hJspace.symm)
  obtain ⟨f, hf, hfmap, hhom⟩ :=
    exists_isPiecewiseAffineOn_freeLoop_homotopic J L eJ γ zero_lt_one
  have hfbd : IsPiecewiseAffineOn f (frontier P) := hJspace ▸ hf
  have hfbdmap : MapsTo f (frontier P) L.space := hJspace ▸ hfmap
  let b : C(frontier P, L.space) :=
    ⟨fun z => ⟨f z, hfbdmap z.property⟩, hfbd.continuousOn.domRestrict.subtype_mk _⟩
  obtain ⟨g, hg, hgf, hgmap⟩ := hP.exists_isPiecewiseAffineOn_extension hU hfbd
    (fun z hz => hLU (hfbdmap hz))
  refine ⟨g, hg, hgmap, b, e, fun z => hgf z.property, ?_⟩
  exact hhom

end DifferentialGeometry.Topology.PiecewiseLinear
