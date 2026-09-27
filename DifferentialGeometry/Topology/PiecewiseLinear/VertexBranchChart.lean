/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.TransversePlaneNormalForm
import DifferentialGeometry.Topology.PiecewiseLinear.VertexCrossingLevel

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_isPLHomeomorphOn_closedStar_pair_of_geometricLink_section [DecidableEq E]
    [DecidableEq F] (hn : Module.finrank ℝ E = 3) (hn' : Module.finrank ℝ F = 3)
    (K M : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (K' M' : Geometry.SimplicialComplex ℝ F) [Finite K'.faces]
    (hM : M.faces ⊆ K.faces) (hM' : M'.faces ⊆ K'.faces)
    {p : E} {p' : F} (hp : {p} ∈ M.faces) (hp' : {p'} ∈ M'.faces)
    (hK : K.space ∈ 𝓝 p) (hK' : K'.space ∈ 𝓝 p')
    (ℓ : E →L[ℝ] ℝ) (ℓ' : F →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hℓ' : ℓ' ≠ 0)
    (hpℓ : ℓ p = 0) (hp'ℓ' : ℓ' p' = 0)
    (hside : ∀ s ∈ K.faces, convexHull ℝ (s : Set E) ⊆ {x | ℓ x ≤ 0} ∨
      convexHull ℝ (s : Set E) ⊆ {x | 0 ≤ ℓ x})
    (hside' : ∀ s ∈ K'.faces, convexHull ℝ (s : Set F) ⊆ {x | ℓ' x ≤ 0} ∨
      convexHull ℝ (s : Set F) ⊆ {x | 0 ≤ ℓ' x})
    (hlink : IsPLSphere 1 (SimplicialComplex.geometricLink M {p}).space)
    (hlink' : IsPLSphere 1 (SimplicialComplex.geometricLink M' {p'}).space)
    {a b : E} {a' b' : F} (hab : a ≠ b) (hab' : a' ≠ b')
    (hzero : (SimplicialComplex.geometricLink M {p}).space ∩ {x | ℓ x = 0} = {a, b})
    (hzero' : (SimplicialComplex.geometricLink M' {p'}).space ∩ {x | ℓ' x = 0} = {a', b'})
    (hpos : ∃ x ∈ (SimplicialComplex.geometricLink M {p}).space, 0 < ℓ x)
    (hneg : ∃ x ∈ (SimplicialComplex.geometricLink M {p}).space, ℓ x < 0)
    (hpos' : ∃ x ∈ (SimplicialComplex.geometricLink M' {p'}).space, 0 < ℓ' x)
    (hneg' : ∃ x ∈ (SimplicialComplex.geometricLink M' {p'}).space, ℓ' x < 0) :
    ∃ g : E → F, IsPLHomeomorphOn g (closedStar K p) (closedStar K' p') ∧ g p = p' ∧
      g '' closedStar M p = closedStar M' p' ∧
      g '' (closedStar K p ∩ {x | ℓ x = 0}) = closedStar K' p' ∩ {x | ℓ' x = 0} := by
  have hlinkMK : (SimplicialComplex.geometricLink M {p}).space ⊆
      (SimplicialComplex.geometricLink K {p}).space := by
    apply space_mono_of_faces_subset
    intro s hs
    obtain ⟨hne, hps, hs'⟩ := (SimplicialComplex.mem_geometricLink_singleton M p s).mp hs
    exact (SimplicialComplex.mem_geometricLink_singleton K p s).mpr ⟨hne, hps, hM hs'⟩
  have hlinkM'K' : (SimplicialComplex.geometricLink M' {p'}).space ⊆
      (SimplicialComplex.geometricLink K' {p'}).space := by
    apply space_mono_of_faces_subset
    intro s hs
    obtain ⟨hne, hps, hs'⟩ := (SimplicialComplex.mem_geometricLink_singleton M' p' s).mp hs
    exact (SimplicialComplex.mem_geometricLink_singleton K' p' s).mpr ⟨hne, hps, hM' hs'⟩
  obtain ⟨f, hf, hfM, hfzero, -, -, -, -⟩ :=
    exists_isPLHomeomorphOn_geometricLink_pair hn hn' K K' (hM hp) (hM' hp') hK hK'
      ℓ ℓ' hℓ hℓ' hpℓ hp'ℓ' hside hside' hlink hlink' hlinkMK hlinkM'K'
      hab hab' hzero hzero' hpos hneg hpos' hneg'
  exact exists_isPLHomeomorphOn_closedStar_pair K K' M M' hM hM' hp hp' hf hfM
    ℓ.toLinearMap ℓ'.toLinearMap hpℓ hp'ℓ' hfzero

theorem exists_linearEquiv_normalForm_of_geometricLink_section [DecidableEq E]
    (hn : Module.finrank ℝ E = 3) (K M : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] [Finite M.faces] (hM : M.faces ⊆ K.faces) {p : E} (hp : {p} ∈ M.faces)
    (hK : K.space ∈ 𝓝 p) (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hside : ∀ s ∈ K.faces, convexHull ℝ (s : Set E) ⊆ {x | ℓ x ≤ ℓ p} ∨
      convexHull ℝ (s : Set E) ⊆ {x | ℓ p ≤ ℓ x})
    (hlink : IsPLSphere 1 (SimplicialComplex.geometricLink M {p}).space)
    {a b : E} (hab : a ≠ b)
    (hlevel : (SimplicialComplex.geometricLink M {p}).space ∩ {x | ℓ x = ℓ p} = {a, b})
    (hpos : ∃ x ∈ (SimplicialComplex.geometricLink M {p}).space, ℓ p < ℓ x)
    (hneg : ∃ x ∈ (SimplicialComplex.geometricLink M {p}).space, ℓ x < ℓ p) :
    ∃ (U V : Set E) (h : E → E) (L : E ≃ₗ[ℝ] ℝ × ℝ × ℝ),
      IsOpen U ∧ IsOpen V ∧ p ∈ U ∧ IsPLHomeomorphOn h U V ∧ h p = 0 ∧
        ∀ᶠ y in 𝓝 p, (y ∈ M.space → (L (h y)).2.2 = 0) ∧ (ℓ y = ℓ p → (L (h y)).2.1 = 0) := by
  obtain ⟨U, V, h, L, hU, hV, hpU, hPLh, hhp, hcase⟩ :=
    (hasPLCrossingAt_fiber_of_geometricLink_section_at hn K M hM hp hK ℓ hℓ hside hlink hab
      hlevel hpos hneg).exists_linearEquiv_normalForm
  refine ⟨U, V, h, L, hU, hV, hpU, hPLh, hhp, ?_⟩
  rcases hcase with hc | hc | hc
  · filter_upwards [hc] with y hy
    exact ⟨fun hyM => hy.1.mp hyM, fun hyℓ => hy.2.mp hyℓ⟩
  · filter_upwards [hc] with y hy
    exact ⟨fun hyM => hy.1.mp hyM, fun hyℓ => (hy.2.mp hyℓ).1⟩
  · filter_upwards [hc] with y hy
    exact ⟨fun hyM => (hy.1.mp hyM).1, fun hyℓ => hy.2.mp hyℓ⟩

end DifferentialGeometry.Topology.PiecewiseLinear
