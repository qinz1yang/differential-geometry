/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CurveInclusion
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.MoiseChainPL
import DifferentialGeometry.Topology.PiecewiseLinear.TorusMeridian

/-!
# A normal system exists

Every statement of the Moise Lemma 2 chain is universally quantified over `NormalSystem`, so it
would be worth nothing if no normal system existed.  This file removes that possibility by
exhibiting one over `EuclideanSpace ℝ (Fin 3)`.

The witness is the meridian disk of an embedded solid torus.  `exists_embedded_solid_torus_meridian`
already produces, unconditionally, a finite combinatorial `3`-manifold with boundary `K` in
`EuclideanSpace ℝ (Fin 3)` together with a piecewise linear circle `J` in its frontier which bounds
in `K` and does not bound in the frontier.  Those are exactly the data that the normal-system
producer `exists_normalSystem_of_isPiecewiseAffineOn` consumes once the circle is filled by a
piecewise affine singular disk, so the whole construction is a matter of routing existing producers.

Main contents.

* `exists_normalSystem_of_component_loop`: a normal system from a free loop in one boundary
  component of a finite combinatorial `3`-manifold with boundary which bounds in the manifold and
  not in the component.  This is the normal-system half of
  `exists_polyhedralDisk_of_normalSystemDisk`, isolated from the embedded disk producer that the
  rest of that argument needs.
* `exists_normalSystem_of_essential_boundary_circle`: the same conclusion from frontier-level data
  about a piecewise linear circle, which is the shape the solid torus producer delivers.
* `exists_normalSystem_euclideanSpace_three` and `nonempty_normalSystem_euclideanSpace_three`: the
  anchor itself.  The normal system produced also satisfies the properness identity and the
  basepoint normalization, that is, two of the three side conditions that `LemmaTwoStatement`
  imposes on its covering system, so those are not vacuous either.

What is **not** established here.  The witness is not shown to be singular, so the branch machinery
is not exercised by it; the trivial normal subgroup is used throughout, and the singular disk comes
from a simplicial filling about which the producer records nothing beyond its boundary values.
Neither an `EmbeddedDisk` for the witness nor a `DoubleCoverReduction` between two witnesses is
produced here.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
/-- A normal system from a free loop in a boundary component.  Given a finite combinatorial
`3`-manifold with boundary `K`, a connected component `c` of its boundary complex and a free loop in
that component which is nullhomotopic in `K` but not in the component, there is a normal system over
the same space.  The normal system produced is also proper, in the sense that only the frontier of
its source disk is carried into the boundary, and its basepoint is the initial point of its boundary
loop. -/
theorem exists_normalSystem_of_component_loop {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (hKfin : K.faces.Finite)
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (c : ConnectedComponents (boundaryComplex 3 K).space)
    (hsub : (connectedComponentComplex (boundaryComplex 3 K) c).space ⊆ K.space)
    (γ : freeLoop (connectedComponentComplex (boundaryComplex 3 K) c).space)
    (hnull : ((⟨Set.inclusion hsub, continuous_inclusion hsub⟩ :
      C((connectedComponentComplex (boundaryComplex 3 K) c).space, K.space)).comp γ).Nullhomotopic)
    (hess : ¬ γ.Nullhomotopic) :
    ∃ S : NormalSystem E,
      S.sourceComplex.space ∩ S.singularMap ⁻¹' S.boundaryComplex.space =
        frontier S.sourceComplex.space ∧
      S.basepoint = S.boundaryLoop 0 := by
  let _ : Finite K.faces := hKfin.to_subtype
  have hVB : (connectedComponentComplex (boundaryComplex 3 K) c).space ⊆
      (boundaryComplex 3 K).space :=
    space_mono_of_faces_subset (restrict_faces_subset (boundaryComplex 3 K) _)
  have hVcomp : ∀ z ∈ (connectedComponentComplex (boundaryComplex 3 K) c).space,
      connectedComponentIn (boundaryComplex 3 K).space z =
        (connectedComponentComplex (boundaryComplex 3 K) c).space := fun z hz =>
    (connectedComponentComplex_space_eq_connectedComponentIn (boundaryComplex 3 K) c hz).symm
  obtain ⟨P, f, a, δ, hP, hf, hfmap, hfbd, hδ, hhom⟩ :=
    exists_isPiecewiseAffineOn_fill_of_nullhomotopic K (boundaryComplex 3 K)
      (boundaryComplex_faces_subset 3 K) hVB hsub hVcomp γ hnull
  have hδess : ¬ δ.Nullhomotopic := fun hd =>
    hess (FreeLoop.nullhomotopic_of_homotopic hhom hd)
  obtain ⟨O, hO, hOV⟩ :=
    exists_isOpen_inter_eq_connectedComponentComplex_space (boundaryComplex 3 K) c
  have hnbhd : (connectedComponentComplex (boundaryComplex 3 K) c).space ∈
      𝓝ˢ[(boundaryComplex 3 K).space] (f '' frontier P) := by
    refine mem_nhdsSetWithin.mpr ⟨O, hO, ?_, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact (hOV.symm.subset (hfbd hz)).1
    · exact hOV.subset
  obtain ⟨S, hsource, -, -, -, hbase, hproper, -, -⟩ :=
    exists_normalSystem_of_isPiecewiseAffineOn K hK hP hf hfmap (hfbd.mono_right hVB) hnbhd a δ hδ
      (⊥ : Subgroup (FundamentalGroup
        (connectedComponentComplex (boundaryComplex 3 K) c).space (δ 0)))
      (fun hmeet => hδess ((conjugacyClassMeets_bot_iff_nullhomotopic δ _).mp hmeet))
  exact ⟨S, hproper.trans (congrArg frontier hsource.symm), hbase⟩

open Classical in
/-- A normal system from an essential piecewise linear circle in the frontier of a finite
combinatorial `3`-manifold with boundary of full dimension.  The circle has to bound in the manifold
and not to bound in the frontier; it is not required to be a subcomplex, and no connectedness
assumption on the frontier is made, since the circle selects its own boundary component. -/
theorem exists_normalSystem_of_essential_boundary_circle {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 3)
    (K : Geometry.SimplicialComplex ℝ E) (hKfin : K.faces.Finite)
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    {J : Set E} (hJ : IsPLSphere 1 J)
    (hJb : J ⊆ frontier K.space) (hJK : J ⊆ K.space)
    (hnull : (⟨Set.inclusion hJK, continuous_inclusion hJK⟩ : C(J, K.space)).Nullhomotopic)
    (hess : ¬ (⟨Set.inclusion hJb, continuous_inclusion hJb⟩ :
      C(J, frontier K.space)).Nullhomotopic) :
    ∃ S : NormalSystem E,
      S.sourceComplex.space ∩ S.singularMap ⁻¹' S.boundaryComplex.space =
        frontier S.sourceComplex.space ∧
      S.basepoint = S.boundaryLoop 0 := by
  let _ : Finite K.faces := hKfin.to_subtype
  obtain ⟨e⟩ := nonempty_homeomorph_loopCircle_of_isPLSphere_one hJ
  have hdim' : Module.finrank ℝ E = 2 + 1 := by rw [hdim]
  have hfr : frontier K.space = (boundaryComplex 3 K).space :=
    frontier_space_eq_boundaryComplex_space_of_finrank hdim' K hK
  have hJB : J ⊆ (boundaryComplex 3 K).space := hJb.trans hfr.subset
  have hx : (e 0 : E) ∈ (boundaryComplex 3 K).space := hJB (e 0).2
  obtain ⟨c, hc⟩ : ∃ c : ConnectedComponents (boundaryComplex 3 K).space,
      c = ConnectedComponents.mk ⟨(e 0 : E), hx⟩ := ⟨_, rfl⟩
  have hxV : (e 0 : E) ∈ (connectedComponentComplex (boundaryComplex 3 K) c).space := by
    rw [hc, connectedComponentComplex_space]
    exact ⟨⟨_, hx⟩, rfl, rfl⟩
  have hJV : J ⊆ (connectedComponentComplex (boundaryComplex 3 K) c).space := by
    rw [connectedComponentComplex_space_eq_connectedComponentIn _ c hxV]
    exact hJ.isConnected_one.isPreconnected.subset_connectedComponentIn (e 0).2 hJB
  have hVB : (connectedComponentComplex (boundaryComplex 3 K) c).space ⊆
      (boundaryComplex 3 K).space :=
    space_mono_of_faces_subset (restrict_faces_subset (boundaryComplex 3 K) _)
  have hsub : (connectedComponentComplex (boundaryComplex 3 K) c).space ⊆ K.space :=
    hVB.trans (space_mono_of_faces_subset (boundaryComplex_faces_subset 3 K))
  have hVfr : (connectedComponentComplex (boundaryComplex 3 K) c).space ⊆ frontier K.space :=
    hVB.trans hfr.symm.subset
  refine exists_normalSystem_of_component_loop K hKfin hK c hsub
    ⟨fun θ => ⟨(e θ : E), hJV (e θ).2⟩,
      (continuous_subtype_val.comp e.continuous).subtype_mk _⟩ ?_ ?_
  · have hcomp : (⟨Set.inclusion hsub, continuous_inclusion hsub⟩ :
        C((connectedComponentComplex (boundaryComplex 3 K) c).space, K.space)).comp
          ⟨fun θ => ⟨(e θ : E), hJV (e θ).2⟩,
            (continuous_subtype_val.comp e.continuous).subtype_mk _⟩ =
        (⟨Set.inclusion hJK, continuous_inclusion hJK⟩ : C(J, K.space)).comp
          (e : C(loopCircle, J)) :=
      ContinuousMap.ext fun _ => rfl
    rw [hcomp]
    exact hnull.comp_left _
  · intro hg
    refine hess ?_
    have h2 := (hg.comp_right (⟨Set.inclusion hVfr, continuous_inclusion hVfr⟩ :
      C((connectedComponentComplex (boundaryComplex 3 K) c).space,
        frontier K.space))).comp_left (e.symm : C(J, loopCircle))
    have h3 : ((⟨Set.inclusion hVfr, continuous_inclusion hVfr⟩ :
        C((connectedComponentComplex (boundaryComplex 3 K) c).space, frontier K.space)).comp
          ⟨fun θ => ⟨(e θ : E), hJV (e θ).2⟩,
            (continuous_subtype_val.comp e.continuous).subtype_mk _⟩).comp
          (e.symm : C(J, loopCircle)) =
        (⟨Set.inclusion hJb, continuous_inclusion hJb⟩ : C(J, frontier K.space)) :=
      ContinuousMap.ext fun y => congrArg (Set.inclusion hJb) (e.apply_symm_apply y)
    rwa [h3] at h2

open Classical in
/-- **A normal system exists.**  The meridian disk of an embedded solid torus in
`EuclideanSpace ℝ (Fin 3)` is a singular disk of the kind a normal system is built from, so the
structure `NormalSystem` is inhabited over `EuclideanSpace ℝ (Fin 3)`.  The system produced is also
proper and basepoint normalized, which are two of the three side conditions that `LemmaTwoStatement`
imposes on the covering system it quantifies over. -/
theorem exists_normalSystem_euclideanSpace_three :
    ∃ S : NormalSystem (EuclideanSpace ℝ (Fin 3)),
      S.sourceComplex.space ∩ S.singularMap ⁻¹' S.boundaryComplex.space =
        frontier S.sourceComplex.space ∧
      S.basepoint = S.boundaryLoop 0 := by
  obtain ⟨K, J, _Ddisk, _rpar, hKfin, hK, -, -, -, hJ, -, -, -, -, -, -, hJb, hJK, hess,
    hnull, -⟩ := exists_embedded_solid_torus_meridian
  exact exists_normalSystem_of_essential_boundary_circle finrank_euclideanSpace_fin K hKfin hK
    hJ hJb hJK hnull hess

/-- The structure `NormalSystem` is inhabited over `EuclideanSpace ℝ (Fin 3)`.  Consequently every
statement of the Lemma 2 chain that quantifies over normal systems is a statement about something,
and the conditional theorems of that chain are not vacuously true. -/
theorem nonempty_normalSystem_euclideanSpace_three :
    Nonempty (NormalSystem (EuclideanSpace ℝ (Fin 3))) := by
  obtain ⟨S, -⟩ := exists_normalSystem_euclideanSpace_three
  exact ⟨S⟩

end DifferentialGeometry.Topology.PiecewiseLinear
