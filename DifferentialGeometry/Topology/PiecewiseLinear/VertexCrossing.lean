/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CrossingNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.HeightSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.LinkPair
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexLink
import DifferentialGeometry.Topology.PiecewiseLinear.StarPair
import DifferentialGeometry.Topology.PiecewiseLinear.TransverseHeight

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem hasPLCrossingAt_fiber_of_geometricLink_section
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [dE : DecidableEq E] (hdimE : Module.finrank ℝ E = 3)
    (K M : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hM : M.faces ⊆ K.faces) {p : E} (hp : {p} ∈ M.faces) (hK : K.space ∈ 𝓝 p)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hpℓ : ℓ p = 0)
    (hside : ∀ s ∈ K.faces, convexHull ℝ (s : Set E) ⊆ {x | ℓ x ≤ 0} ∨
      convexHull ℝ (s : Set E) ⊆ {x | 0 ≤ ℓ x})
    (hlink : IsPLSphere 1 (SimplicialComplex.geometricLink M {p}).space)
    {a b : E} (hab : a ≠ b)
    (hzero : (SimplicialComplex.geometricLink M {p}).space ∩ {x | ℓ x = 0} = {a, b})
    (hpos : ∃ x ∈ (SimplicialComplex.geometricLink M {p}).space, 0 < ℓ x)
    (hneg : ∃ x ∈ (SimplicialComplex.geometricLink M {p}).space, ℓ x < 0) :
    HasPLCrossingAt M.space {x | ℓ x = 0} p := by
  classical
  cases Subsingleton.elim dE (Classical.decEq E)
  let _ : Nontrivial E := Module.nontrivial_of_finrank_pos (by rw [hdimE]; norm_num)
  obtain ⟨q, -, hq, -⟩ := exists_continuousLinearMap_ne_zero_injOn
    (A := (∅ : Set E)) Set.finite_empty (0 : E →L[ℝ] ℝ) (by norm_num : (0 : ℝ) < 1)
  have hq' : q.toLinearMap ≠ 0 := by
    intro h
    apply hq
    ext x
    exact LinearMap.congr_fun h x
  obtain ⟨T, hT, hTcard, h0T, -, hspan⟩ :=
    exists_affineIndependent_openSimplex_superset_of_subset_fiber
      (n := 2) hdimE q.toLinearMap hq' (r := 0) (C := ({0} : Set E))
      isCompact_singleton.isBounded (by
        intro x hx
        rw [mem_singleton_iff] at hx
        subst x
        exact map_zero q.toLinearMap)
  have h0T' : (0 : E) ∈ openSimplex T := h0T rfl
  let P := LinearMap.ker q.toLinearMap
  have hP : Module.finrank ℝ P = 2 := by
    have hker := Module.Dual.finrank_ker_add_one_of_ne_zero hq'
    dsimp only [P]
    omega
  let _ : Nontrivial P := Module.nontrivial_of_finrank_pos (by rw [hP]; norm_num)
  obtain ⟨v, hv⟩ := exists_ne (0 : P)
  have hvE : (v : E) ≠ 0 := fun h => hv (Subtype.ext h)
  obtain ⟨m₀, hm₀⟩ := Module.Projective.exists_dual_ne_zero ℝ hvE
  let m : E →L[ℝ] ℝ := m₀.toContinuousLinearMap
  have hmv : m v ≠ 0 := by simpa only [m, LinearMap.coe_toContinuousLinearMap'] using hm₀
  have hm : m ≠ 0 := by
    intro h
    apply hmv
    simp only [h, zero_apply]
  let M₀ := simplexComplex T hT
  let _ : Finite M₀.faces := (simplexComplex_faces_finite T hT).to_subtype
  have hM₀space : M₀.space = convexHull ℝ (T : Set E) :=
    simplexComplex_space T hT (Finset.card_pos.mp (by omega))
  obtain ⟨M₁, hM₁, hM₁finite, h0M₁⟩ := exists_isSubdivision_singleton_mem M₀ (by
    rw [hM₀space]
    exact openSimplex_subset_convexHull T h0T')
  let _ : Finite M₁.faces := hM₁finite.to_subtype
  obtain ⟨C, hC, -, -, -, hCnhds⟩ :=
    exists_affineIndependent_openSimplex_subset (n := 2) hdimE (0 : E) Filter.univ_mem
  let D := convexHull ℝ (C : Set E)
  have hD : IsPolyhedron D := isPolyhedron_convexHull_of_affineIndependent C hC
  obtain ⟨R, hRfinite, hRspace, hRM₁, -, hRside⟩ :=
    exists_triangulation_union_with_halfSpace_faces M₁ hD m.toLinearMap.toAffineMap 0
  let _ : Finite R.faces := hRfinite.to_subtype
  let N := restrict R M₁.space
  let _ : Finite N.faces := (restrict_faces_finite R M₁.space).to_subtype
  have hNR : N.faces ⊆ R.faces := restrict_faces_subset R M₁.space
  change IsSubdivision N M₁ at hRM₁
  have h0N : ({0} : Finset E) ∈ N.faces := hRM₁.singleton_mem h0M₁
  have hRnhds : R.space ∈ 𝓝 (0 : E) := by
    rw [hRspace]
    exact Filter.mem_of_superset hCnhds subset_union_right
  have hlocal : ∀ᶠ x in 𝓝 (0 : E), x ∈ N.space ↔ x - 0 ∈ P := by
    filter_upwards [eventually_mem_convexHull_iff_sub_mem_vectorSpan hT h0T'] with x hx
    rw [hRM₁.space_eq, hM₁.space_eq, hM₀space]
    simpa only [P, hspan] using hx
  have hNlink : IsPLSphere 1 (SimplicialComplex.geometricLink N {0}).space :=
    isPLSphere_geometricLink_of_isSubdivision_simplexComplex_of_mem_openSimplex hT
      (by omega) (hRM₁.trans hM₁) h0N h0T'
  obtain ⟨⟨a', b', hab', hzero'⟩, hpos', hneg'⟩ :=
    exists_pair_geometricLink_fiber_of_eventually_plane R N hNR h0N hRnhds P hP hlocal
      m.toLinearMap (map_zero m.toLinearMap) v.property hmv
  have hRside' : ∀ s ∈ R.faces, convexHull ℝ (s : Set E) ⊆ {x | m x ≤ 0} ∨
      convexHull ℝ (s : Set E) ⊆ {x | 0 ≤ m x} := by
    intro s hs
    simpa only [LinearMap.coe_toAffineMap, ContinuousLinearMap.coe_coe] using hRside s hs
  have hmodel : HasPLCrossingAt N.space {x | m x = 0} 0 := by
    have hc := hasPLCrossingAt_affineSubspace_fiber P hP hdimE m.toLinearMap v.property hmv (0 : E)
    exact hc.congr (hlocal.mono fun _ hx => hx.symm)
      (Filter.Eventually.of_forall fun x => by
        change (m x = m 0) ↔ m x = 0
        rw [map_zero])
  have hlinkMK : (SimplicialComplex.geometricLink M {p}).space ⊆
      (SimplicialComplex.geometricLink K {p}).space := by
    apply space_mono_of_faces_subset
    intro s hs
    obtain ⟨hne, hp', hs'⟩ := (SimplicialComplex.mem_geometricLink_singleton M p s).mp hs
    exact (SimplicialComplex.mem_geometricLink_singleton K p s).mpr ⟨hne, hp', hM hs'⟩
  have hlinkNR : (SimplicialComplex.geometricLink N {0}).space ⊆
      (SimplicialComplex.geometricLink R {0}).space := by
    apply space_mono_of_faces_subset
    intro s hs
    obtain ⟨hne, hp', hs'⟩ := (SimplicialComplex.mem_geometricLink_singleton N 0 s).mp hs
    exact (SimplicialComplex.mem_geometricLink_singleton R 0 s).mpr ⟨hne, hp', hNR hs'⟩
  obtain ⟨f, hf, hfM, hfzero, -, -, -, -⟩ :=
    exists_isPLHomeomorphOn_geometricLink_pair hdimE hdimE K R (hM hp) (hNR h0N) hK hRnhds
      ℓ m hℓ hm hpℓ (map_zero m) hside hRside' hlink hNlink hlinkMK hlinkNR
      hab hab' hzero hzero' hpos hneg hpos' hneg'
  obtain ⟨g, hg, hgp, hgM, hgzero⟩ := exists_isPLHomeomorphOn_closedStar_pair K R M N
    hM hNR hp h0N hf hfM ℓ.toLinearMap m.toLinearMap hpℓ (map_zero m.toLinearMap) hfzero
  exact HasPLCrossingAt.of_closedStar_pair K R M N hM hNR hK hg hgp hgM hgzero hmodel

end DifferentialGeometry.Topology.PiecewiseLinear
