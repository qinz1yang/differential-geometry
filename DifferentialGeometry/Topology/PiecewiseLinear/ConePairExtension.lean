/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ConeExtension

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def coneSet (p : E) (X : Set E) : Set E :=
  {x | x = p ∨ ∃ z ∈ X, ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ x = p + s • (z - p)}

theorem mem_coneSet_iff {p : E} {X : Set E} {x : E} :
    x ∈ coneSet p X ↔
      x = p ∨ ∃ z ∈ X, ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ x = p + s • (z - p) := Iff.rfl

theorem apex_mem_coneSet (p : E) (X : Set E) : p ∈ coneSet p X := Or.inl rfl

theorem subset_coneSet (p : E) (X : Set E) : X ⊆ coneSet p X := fun z hz =>
  Or.inr ⟨z, hz, 1, one_pos, le_rfl, by rw [one_smul, add_sub_cancel]⟩

theorem coneSet_mono (p : E) {X Y : Set E} (h : X ⊆ Y) : coneSet p X ⊆ coneSet p Y := by
  intro x hx
  rcases mem_coneSet_iff.mp hx with rfl | ⟨z, hz, s, hs, hs', rfl⟩
  · exact apex_mem_coneSet _ _
  · exact Or.inr ⟨z, h hz, s, hs, hs', rfl⟩

theorem coneComplex_space_eq_coneSet [DecidableEq E] {p : E}
    {L : Geometry.SimplicialComplex ℝ E} (h : IsConeBase p L) :
    (coneComplex h).space = coneSet p L.space :=
  Set.ext fun _ => mem_coneComplex_space_iff h

theorem coneSet_subset_coneComplex_space [DecidableEq E] {p : E}
    {L : Geometry.SimplicialComplex ℝ E} (h : IsConeBase p L) {X : Set E} (hX : X ⊆ L.space) :
    coneSet p X ⊆ (coneComplex h).space := fun _ hx =>
  (coneComplex_space_eq_coneSet h).ge (coneSet_mono p hX hx)

theorem image_coneSet_of_radial {p : E} {q : F} {g f : E → F} {S : Set E} (hgp : g p = q)
    (hrad : ∀ z ∈ S, ∀ s : ℝ, 0 ≤ s → s ≤ 1 → g (p + s • (z - p)) = q + s • (f z - q))
    {X : Set E} (hXS : X ⊆ S) : g '' coneSet p X = coneSet q (f '' X) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases mem_coneSet_iff.mp hx with rfl | ⟨z, hz, s, hs, hs', rfl⟩
    · exact Or.inl hgp
    · exact Or.inr ⟨f z, mem_image_of_mem f hz, s, hs, hs', hrad z (hXS hz) s hs.le hs'⟩
  · intro hy
    rcases mem_coneSet_iff.mp hy with rfl | ⟨w, hw, s, hs, hs', rfl⟩
    · exact ⟨p, apex_mem_coneSet p X, hgp⟩
    · obtain ⟨z, hz, rfl⟩ := hw
      exact ⟨p + s • (z - p), Or.inr ⟨z, hz, s, hs, hs', rfl⟩, hrad z (hXS hz) s hs.le hs'⟩

theorem eqOn_id_coneSet_of_radial {p : E} {g f : E → E} {S : Set E} (hgp : g p = p)
    (hrad : ∀ z ∈ S, ∀ s : ℝ, 0 ≤ s → s ≤ 1 → g (p + s • (z - p)) = p + s • (f z - p))
    {X : Set E} (hXS : X ⊆ S) (hfix : EqOn f id X) : EqOn g id (coneSet p X) := by
  intro x hx
  rcases mem_coneSet_iff.mp hx with rfl | ⟨z, hz, s, hs, hs', rfl⟩
  · exact hgp
  · rw [hrad z (hXS hz) s hs.le hs', hfix hz]
    rfl

theorem exists_isPLHomeomorphOn_coneComplex_pair [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [DecidableEq E] [DecidableEq F] {p : E} {L : Geometry.SimplicialComplex ℝ E} [Finite L.faces]
    (hL : IsConeBase p L) {q : F} {L' : Geometry.SimplicialComplex ℝ F} [Finite L'.faces]
    (hL' : IsConeBase q L') {f : E → F} (hf : IsPLHomeomorphOn f L.space L'.space) :
    ∃ g : E → F, IsPLHomeomorphOn g (coneComplex hL).space (coneComplex hL').space ∧
      EqOn g f L.space ∧ g p = q ∧
      (∀ z ∈ L.space, ∀ s : ℝ, 0 ≤ s → s ≤ 1 → g (p + s • (z - p)) = q + s • (f z - q)) ∧
      ∀ X ⊆ L.space, g '' coneSet p X = coneSet q (f '' X) := by
  obtain ⟨g, hg, hgf, hgp, hrad⟩ := exists_isPLHomeomorphOn_coneComplex hL hL' hf
  exact ⟨g, hg, hgf, hgp, hrad, fun _ hX => image_coneSet_of_radial hgp hrad hX⟩

theorem exists_isPLHomeomorphOn_coneComplex_sheets [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [DecidableEq E] [DecidableEq F] {p : E} {L : Geometry.SimplicialComplex ℝ E} [Finite L.faces]
    (hL : IsConeBase p L) {q : F} {L' : Geometry.SimplicialComplex ℝ F} [Finite L'.faces]
    (hL' : IsConeBase q L') {f : E → F} (hf : IsPLHomeomorphOn f L.space L'.space)
    {A B : Set E} {A' B' : Set F} (hA : A ⊆ L.space) (hB : B ⊆ L.space)
    (hfA : f '' A = A') (hfB : f '' B = B') :
    ∃ g : E → F, IsPLHomeomorphOn g (coneComplex hL).space (coneComplex hL').space ∧
      EqOn g f L.space ∧ g p = q ∧
      g '' coneSet p A = coneSet q A' ∧ g '' coneSet p B = coneSet q B' ∧
      g '' coneSet p (A ∩ B) = coneSet q (A' ∩ B') := by
  obtain ⟨g, hg, hgf, hgp, hrad, hpair⟩ :=
    exists_isPLHomeomorphOn_coneComplex_pair hL hL' hf
  have hinter : f '' (A ∩ B) = A' ∩ B' := by
    rw [hf.bijOn.injOn.image_inter hA hB, hfA, hfB]
  exact ⟨g, hg, hgf, hgp, hfA ▸ hpair A hA, hfB ▸ hpair B hB,
    hinter ▸ hpair (A ∩ B) ((inter_subset_left).trans hA)⟩

theorem exists_isPLHomeomorphOn_coneComplex_fixing [FiniteDimensional ℝ E] [DecidableEq E] {p : E}
    {L L' : Geometry.SimplicialComplex ℝ E} [Finite L.faces] [Finite L'.faces]
    (hL : IsConeBase p L) (hL' : IsConeBase p L') {f : E → E}
    (hf : IsPLHomeomorphOn f L.space L'.space) {Z : Set E} (hZ : Z ⊆ L.space)
    (hfix : EqOn f id Z) :
    ∃ g : E → E, IsPLHomeomorphOn g (coneComplex hL).space (coneComplex hL').space ∧
      EqOn g f L.space ∧ g p = p ∧ EqOn g id (coneSet p Z) ∧
      ∀ X ⊆ L.space, g '' coneSet p X = coneSet p (f '' X) := by
  obtain ⟨g, hg, hgf, hgp, hrad, hpair⟩ :=
    exists_isPLHomeomorphOn_coneComplex_pair hL hL' hf
  exact ⟨g, hg, hgf, hgp, eqOn_id_coneSet_of_radial hgp hrad hZ hfix, hpair⟩

end DifferentialGeometry.Topology.PiecewiseLinear
