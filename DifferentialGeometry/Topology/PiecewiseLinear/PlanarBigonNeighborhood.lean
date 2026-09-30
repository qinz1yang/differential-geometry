/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarChartArcNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.CurveCrossingRestriction
import DifferentialGeometry.Topology.PiecewiseLinear.CurveCrossingGeneralPosition

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

theorem IsPLBall.exists_isPLBall_neighborhood_with_two_crossings
    {D U A C : Set Plane} {p q : Plane} (hD : IsPLBall 2 D)
    (hU : IsOpen U) (hDU : D ⊆ U)
    {r s : (Fin 2 → ℝ) → Plane}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) A)
    (hs : IsPLHomeomorphOn s (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) C)
    (hDA : IsPLBall 1 (D ∩ A)) (hDC : IsPLBall 1 (D ∩ C))
    (hrends : Disjoint D (r '' stdSimplexBoundary 1))
    (hsends : Disjoint D (s '' stdSimplexBoundary 1))
    (hfinite : (A ∩ C).Finite) (hpair : D ∩ (A ∩ C) = {p, q})
    (hp : HasPLCurveCrossingOnAt univ A C p)
    (hq : HasPLCurveCrossingOnAt univ A C q) :
    ∃ (Q : Set Plane) (α β : ℝ → Plane),
      IsPLBall 2 Q ∧ D ⊆ interior Q ∧ Q ⊆ U ∧
      IsPLHomeomorphOn α (Icc 0 1) (A ∩ Q) ∧
      IsPLHomeomorphOn β (Icc 0 1) (C ∩ Q) ∧
      Schoenflies.IsCrosscut (frontier Q) (A ∩ Q) (α 0) (α 1) ∧
      Schoenflies.IsCrosscut (frontier Q) (C ∩ Q) (β 0) (β 1) ∧
      (A ∩ Q) ∩ (C ∩ Q) = {p, q} ∧ p ∈ interior Q ∧ q ∈ interior Q ∧
      HasPLCurveCrossingOnAt univ (A ∩ Q) (C ∩ Q) p ∧
      HasPLCurveCrossingOnAt univ (A ∩ Q) (C ∩ Q) q := by
  classical
  let V := U \ ((A ∩ C) \ {p, q})
  have hV : IsOpen V := hU.sdiff (hfinite.subset sdiff_subset).isClosed
  have hDV : D ⊆ V := by
    intro x hx
    exact ⟨hDU hx, fun hxc => hxc.2 (hpair ▸ ⟨hx, hxc.1⟩)⟩
  let T : Fin 2 → Set Plane := ![A, C]
  let t : Fin 2 → (Fin 2 → ℝ) → Plane := ![r, s]
  have ht (i : Fin 2) : IsPLHomeomorphOn (t i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) (T i) := by
    fin_cases i
    · exact hr
    · exact hs
  have hDT (i : Fin 2) : IsPLBall 1 (D ∩ T i) := by
    fin_cases i
    · exact hDA
    · exact hDC
  have hte (i : Fin 2) : Disjoint D (t i '' stdSimplexBoundary 1) := by
    fin_cases i
    · exact hrends
    · exact hsends
  obtain ⟨Q, γ, hQ, hDQ, hQV, hγ⟩ :=
    hD.exists_isPLBall_neighborhood_with_crosscut_traces hV hDV T t ht hDT hte
  have hpD : p ∈ D := (hpair.symm ▸ (mem_insert p {q})).1
  have hqD : q ∈ D := (hpair.symm ▸ (mem_insert_of_mem p (mem_singleton q))).1
  have hpQ := hDQ hpD
  have hqQ := hDQ hqD
  refine ⟨Q, γ 0, γ 1, hQ, hDQ, hQV.trans sdiff_subset,
    (hγ 0).1, (hγ 1).1, (hγ 0).2, (hγ 1).2, ?_, hpQ, hqQ, ?_, ?_⟩
  · apply subset_antisymm
    · intro x hx
      by_contra hxp
      exact (hQV hx.1.2).2 ⟨⟨hx.1.1, hx.2.1⟩, hxp⟩
    · intro x hx
      have hxp := hpair.symm ▸ hx
      exact ⟨⟨hxp.2.1, interior_subset (hDQ hxp.1)⟩,
        hxp.2.2, interior_subset (hDQ hxp.1)⟩
  · refine hp.congr (Filter.Eventually.of_forall fun _ => Iff.rfl) ?_ ?_
    · filter_upwards [isOpen_interior.mem_nhds hpQ] with x hx
      exact ⟨fun h => ⟨h, interior_subset hx⟩, And.left⟩
    · filter_upwards [isOpen_interior.mem_nhds hpQ] with x hx
      exact ⟨fun h => ⟨h, interior_subset hx⟩, And.left⟩
  · refine hq.congr (Filter.Eventually.of_forall fun _ => Iff.rfl) ?_ ?_
    · filter_upwards [isOpen_interior.mem_nhds hqQ] with x hx
      exact ⟨fun h => ⟨h, interior_subset hx⟩, And.left⟩
    · filter_upwards [isOpen_interior.mem_nhds hqQ] with x hx
      exact ⟨fun h => ⟨h, interior_subset hx⟩, And.left⟩

theorem HasPLCurveCrossingOnAt.fst_openPartialHomeomorph
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 3) {S A C : Set E} {x : E}
    (e : OpenPartialHomeomorph E (Plane × ℝ))
    (hei : IsPiecewiseAffineOn e.symm e.target) (hx : x ∈ e.source)
    (hxz : (e x).2 = 0) (hcross : HasPLCurveCrossingOnAt S A C x)
    (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    (hAs : A ⊆ e.source) (hCs : C ⊆ e.source)
    (hAz : ∀ y ∈ A, (e y).2 = 0) (hCz : ∀ y ∈ C, (e y).2 = 0) :
    HasPLCurveCrossingOnAt univ ((fun y => (e y).1) '' A)
      ((fun y => (e y).1) '' C) (e x).1 := by
  let S' := e '' (S ∩ e.source)
  have hmem (T : Set E) : ∀ᶠ z in 𝓝 (e x),
      z ∈ e '' (T ∩ e.source) ↔ e.symm z ∈ T := by
    filter_upwards [e.open_target.mem_nhds (e.map_source hx)] with z hz
    constructor
    · rintro ⟨y, ⟨hy, hys⟩, rfl⟩
      rwa [e.left_inv hys]
    · intro hzt
      exact ⟨e.symm z, ⟨hzt, e.map_target hz⟩, e.right_inv hz⟩
  have hdim' : Module.finrank ℝ E = Module.finrank ℝ (Plane × ℝ) := by
    simpa using hdim
  have hcross' : HasPLCurveCrossingOnAt S' (e '' A) (e '' C) (e x) := by
    refine HasPLCurveCrossingOnAt.of_openPartialHomeomorph_of_finrank_eq hdim'
      e.symm hei (e.map_source hx) (e.left_inv hx ▸ hcross) (hmem S) ?_ ?_
    · simpa only [inter_eq_left.mpr hAs] using hmem A
    · simpa only [inter_eq_left.mpr hCs] using hmem C
  let ι : Plane →ₗ[ℝ] (Plane × ℝ) := LinearMap.inl ℝ Plane ℝ
  have hι : Function.Injective ι := fun _ _ h => congrArg Prod.fst h
  have hrange (z : Plane × ℝ) : z ∈ LinearMap.range ι ↔ z.2 = 0 := by
    constructor
    · rintro ⟨w, rfl⟩
      rfl
    · intro hz
      exact ⟨z.1, Prod.ext rfl hz.symm⟩
  have hplane : ∀ᶠ z in 𝓝 (e x), z ∈ S' ↔ z ∈ LinearMap.range ι := by
    filter_upwards [hmem S, e.open_target.mem_nhds (e.map_source hx)] with z hz hzt
    rw [hz, hrange, hS (e.symm z) (e.map_target hzt), e.right_inv hzt]
  have hix : ι (e x).1 = e x := Prod.ext rfl hxz.symm
  have hpre (T : Set E) (hTz : ∀ y ∈ T, (e y).2 = 0) :
      ι ⁻¹' (e '' T) = (fun y => (e y).1) '' T := by
    ext z
    constructor
    · rintro ⟨y, hy, hyz⟩
      exact ⟨y, hy, congrArg Prod.fst hyz⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, Prod.ext rfl (hTz y hy)⟩
  have hresult := (hix.symm ▸ hcross').preimage_linearMap ι hι
    (by simp) (hix.symm ▸ hplane)
  simpa only [hpre A hAz, hpre C hCz] using hresult

end DifferentialGeometry.Topology.PiecewiseLinear
