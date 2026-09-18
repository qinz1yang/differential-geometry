/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryCrossingChart

/-!
# Boundary charts for double point sets
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem frontier_image_halfSpace_iff
    {X F : Type*} [TopologicalSpace X] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (e : OpenPartialHomeomorph X F) (ℓ : F →L[ℝ] ℝ)
    (hℓ : ℓ ≠ 0) {x : X} (hx : x ∈ e.source) :
    x ∈ frontier (e.symm '' (e.target ∩ {z | 0 ≤ ℓ z})) ↔
      x ∈ e.symm '' (e.target ∩ {z | ℓ z = 0}) := by
  have himage (S : Set F) : e.IsImage (e.symm '' (e.target ∩ S)) S := by
    intro y hy
    constructor
    · intro hS
      exact ⟨e y, ⟨e.map_source hy, hS⟩, e.left_inv hy⟩
    · rintro ⟨z, ⟨hzt, hzS⟩, hzy⟩
      have hze : z = e y := by
        have h := congrArg e hzy
        rwa [e.right_inv hzt] at h
      exact hze ▸ hzS
  have hsurj : Function.Surjective ℓ := ℓ.toLinearMap.surjective (by
    intro h
    apply hℓ
    ext z
    exact LinearMap.congr_fun h z)
  have hfront : frontier {z | 0 ≤ ℓ z} = {z | ℓ z = 0} := by
    change frontier (ℓ ⁻¹' Ici 0) = _
    rw [ℓ.frontier_preimage hsurj, frontier_Ici]
    rfl
  have h := (himage {z | 0 ≤ ℓ z}).frontier hx
  rw [hfront] at h
  exact h.symm.trans (himage {z | ℓ z = 0} hx)

theorem HasPLBoundaryCrossingAt.not_eventuallyEq
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {M A B : Set F} {y : F} (hcross : HasPLBoundaryCrossingAt M A B y) :
    ¬A =ᶠ[𝓝 y] B := by
  intro hAB
  have hW : {z | z ∈ A ↔ z ∈ B} ∈ 𝓝 y := by
    filter_upwards [hAB] with z hz
    exact iff_of_eq hz
  obtain ⟨e, hye, heW, he0, _, _, _, _, hA, hB, _⟩ :=
    hcross.exists_openPartialHomeomorph_halfSpace hW
  have htarget : e.target ∈ 𝓝 (0 : ℝ × ℝ × ℝ) :=
    e.open_target.mem_nhds (he0 ▸ e.map_source hye)
  have hcont : Continuous (fun t : ℝ => (t, (0 : ℝ), t)) :=
    continuous_id.prodMk (continuous_const.prodMk continuous_id)
  have htend : Filter.Tendsto (fun t : ℝ => (t, (0 : ℝ), t)) (𝓝[>] 0)
      (𝓝 (0 : ℝ × ℝ × ℝ)) := by
    convert (hcont.tendsto 0).mono_left nhdsWithin_le_nhds using 1
    rfl
  obtain ⟨t, ht, hpos⟩ := ((htend.eventually_mem htarget).and self_mem_nhdsWithin).exists
  have hsrc : e.symm (t, 0, t) ∈ e.source := e.map_target ht
  have hmemB : e.symm (t, 0, t) ∈ B := (hB hsrc).mp (by
    change (e (e.symm (t, 0, t))).2.1 = 0 ∧ 0 ≤ (e (e.symm (t, 0, t))).1
    rw [e.right_inv ht]
    exact ⟨rfl, hpos.le⟩)
  have hmemA : e.symm (t, 0, t) ∈ A := (heW hsrc).mpr hmemB
  have hzero := ((hA hsrc).mpr hmemA).1
  rw [e.right_inv ht] at hzero
  exact hpos.ne' hzero

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem HasPLBoundaryDoubleCrossingAt.exists_openPartialHomeomorph_doublePointSet
    {f : E → F} {P : Set E} {M W : Set F} {y : F}
    (hD : HasPLBoundaryDoubleCrossingAt f P M y) (hW : W ∈ 𝓝 y) :
    ∃ (A B : Set E) (e : OpenPartialHomeomorph F (ℝ × ℝ × ℝ)),
      A ⊆ P ∧ B ⊆ P ∧ Disjoint A B ∧
        IsPLHomeomorphOn f A (f '' A) ∧ IsPLHomeomorphOn f B (f '' B) ∧
          y ∈ e.source ∧ e.source ⊆ W ∧ e y = 0 ∧
            IsPiecewiseAffineOn e e.source ∧ IsPiecewiseAffineOn e.symm e.target ∧
              e.IsImage M {z | 0 ≤ z.1} ∧ e.IsImage (frontier M) {z | z.1 = 0} ∧
                e.IsImage (f '' A) {z | z.2.2 = 0 ∧ 0 ≤ z.1} ∧
                  e.IsImage (f '' B) {z | z.2.1 = 0 ∧ 0 ≤ z.1} ∧
                    e.IsImage (doublePointSet f P) {z | z.2 = 0 ∧ 0 ≤ z.1} ∧
                      ∀ z ∈ e.source, P ∩ f ⁻¹' {z} ⊆ A ∪ B := by
  obtain ⟨a, b, A, B, ha, hb, hfa, hfb, hAP, hBP, hdis, hA, hB, hfA, hfB,
    hcross, hcover⟩ := hD
  obtain ⟨O, hOsub, hO, hyO⟩ := mem_nhds_iff.mp hcover
  obtain ⟨e, hye, heW, he0, he, hei, hM, hBd, hAe, hBe, hABe⟩ :=
    hcross.exists_openPartialHomeomorph_halfSpace (Filter.inter_mem hW (hO.mem_nhds hyO))
  have hcover' : ∀ z ∈ e.source, P ∩ f ⁻¹' {z} ⊆ A ∪ B :=
    fun z hz => hOsub (heW hz).2
  refine ⟨A, B, e, hAP, hBP, hdis, hfA, hfB, hye, heW.trans inter_subset_left,
    he0, he, hei, hM, hBd, hAe, hBe, ?_, hcover'⟩
  intro z hz
  exact (hABe hz).trans (mem_doublePointSet_iff_mem_image_inter_of_injOn f hAP hBP hdis
    hfA.bijOn.injOn hfB.bijOn.injOn (hcover' z hz)).symm

theorem HasPLBoundaryDoubleCrossingAt.exists_openPartialHomeomorph_doublePointSet_of_halfSpace_chart
    {f : E → F} {P : Set E} (e : OpenPartialHomeomorph F F) (ℓ : F →L[ℝ] ℝ)
    (hℓ : ℓ ≠ 0) {y : F} (hy : y ∈ e.source)
    (hD : HasPLBoundaryDoubleCrossingAt f P (e.symm '' (e.target ∩ {z | 0 ≤ ℓ z})) y)
    {W : Set F} (hW : W ∈ 𝓝 y) :
    ∃ (A B : Set E) (j : OpenPartialHomeomorph F (ℝ × ℝ × ℝ)),
      A ⊆ P ∧ B ⊆ P ∧ Disjoint A B ∧
        IsPLHomeomorphOn f A (f '' A) ∧ IsPLHomeomorphOn f B (f '' B) ∧
          y ∈ j.source ∧ j.source ⊆ W ∩ e.source ∧ j y = 0 ∧
            IsPiecewiseAffineOn j j.source ∧ IsPiecewiseAffineOn j.symm j.target ∧
              j.IsImage (e.symm '' (e.target ∩ {z | 0 ≤ ℓ z})) {z | 0 ≤ z.1} ∧
                j.IsImage (e.symm '' (e.target ∩ {z | ℓ z = 0})) {z | z.1 = 0} ∧
                  j.IsImage (f '' A) {z | z.2.2 = 0 ∧ 0 ≤ z.1} ∧
                    j.IsImage (f '' B) {z | z.2.1 = 0 ∧ 0 ≤ z.1} ∧
                      j.IsImage (doublePointSet f P) {z | z.2 = 0 ∧ 0 ≤ z.1} ∧
                        ∀ z ∈ j.source, P ∩ f ⁻¹' {z} ⊆ A ∪ B := by
  obtain ⟨A, B, j, hAP, hBP, hdis, hfA, hfB, hyj, hjW, hj0, hj, hji,
    hM, hBd, hA, hB, hdouble, hcover⟩ :=
    hD.exists_openPartialHomeomorph_doublePointSet
      (Filter.inter_mem hW (e.open_source.mem_nhds hy))
  refine ⟨A, B, j, hAP, hBP, hdis, hfA, hfB, hyj, hjW, hj0, hj, hji, hM, ?_,
    hA, hB, hdouble, hcover⟩
  intro z hz
  exact (hBd hz).trans (frontier_image_halfSpace_iff e ℓ hℓ (hjW hz).2)

end DifferentialGeometry.Topology.PiecewiseLinear
