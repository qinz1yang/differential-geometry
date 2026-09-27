/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CellPairBoundaryOrientation
import DifferentialGeometry.Topology.PiecewiseLinear.CircleOrientationParity
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphIntoInverse

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem isPLCirclePositive_of_commuting_corrections
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S : Set E} (hS : IsPLSphere 1 S) {a b k d : E → E}
    (ha : IsPLHomeomorphOn a S S) (hb : IsPLHomeomorphOn b S S)
    (hk : IsPLHomeomorphOn k S S) (hd : IsPLHomeomorphOn d S S)
    (heq : EqOn (d ∘ b) (a ∘ k) S)
    (hpar : circleOrientationParity S k =
      circleOrientationParity S a + circleOrientationParity S b) :
    IsPLCirclePositive S d := by
  have he := circleOrientationParity_congr heq
  rw [circleOrientationParity_comp hS hd hb, circleOrientationParity_comp hS ha hk, hpar] at he
  have hz : ∀ x : ZMod 2, x + x = 0 := by decide
  rw [← add_assoc, hz, zero_add] at he
  exact circleOrientationParity_eq_zero_iff.mp (add_right_cancel (he.trans (zero_add _).symm))

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]

theorem IsPLHomeomorphInto.isPLHomeomorphOn_chart_rim
    {D J : Set M} {K : M → M} (hK : IsPLHomeomorphInto 3 K D)
    (hD : IsPLCellOn 2 D J) (hKim : K '' D = D)
    {c : OpenPartialHomeomorph M E3} (hc : c ∈ (plGroupoid 3).maximalAtlas M)
    (hDc : D ⊆ c.source) :
    IsPLHomeomorphOn (c ∘ K ∘ c.symm) (c '' J) (c '' J) := by
  have hJc := hD.boundary_subset.trans hDc
  have hDi := hD.image hK
  rw [hKim] at hDi
  have hKJ := hDi.boundary_eq hD
  obtain ⟨r, hr, hJ⟩ := hD.exists_isPLHomeomorphOn_image_chart hc hDc
  have hpoly : IsPolyhedron (c '' D) := IsPLBall.isPolyhedron ⟨r, hr⟩
  have hJpoly : IsPolyhedron (c '' J) := by
    rw [hJ]
    exact (hr.isPLSphere_image_stdSimplexBoundary (n := 1)).isPolyhedron
  have hk := hK.isPLHomeomorphOn_chart_conjugate hKim hc hDc hpoly
  have heq : EqOn ((c ∘ K ∘ c.symm) ∘ c) (c ∘ K) J := by
    intro x hx
    change c (K (c.symm (c x))) = c (K x)
    rw [c.left_inv (hJc hx)]
  have him : (c ∘ K ∘ c.symm) '' (c '' J) = c '' J := by
    rw [← image_comp, heq.image_eq, image_comp, hKJ]
  have ht := hk.restrict hJpoly (image_mono hD.boundary_subset)
  rwa [him] at ht

theorem exists_positive_disk_correction_of_vertex_parities
    {D J : Set M} (hD : IsPLCellOn 2 D J) {a b k : M → M}
    (ha : IsPLHomeomorphInto 3 a D) (hb : IsPLHomeomorphInto 3 b D)
    (hk : IsPLHomeomorphInto 3 k D)
    (haD : a '' D = D) (hbD : b '' D = D) (hkD : k '' D = D)
    {c : OpenPartialHomeomorph M E3} (hc : c ∈ (plGroupoid 3).maximalAtlas M)
    (hDc : D ⊆ c.source)
    (hpar : circleOrientationParity (c '' J) (c ∘ k ∘ c.symm) =
      circleOrientationParity (c '' J) (c ∘ a ∘ c.symm) +
        circleOrientationParity (c '' J) (c ∘ b ∘ c.symm)) :
    ∃ d : M → M, IsPLHomeomorphInto 3 d D ∧ d '' D = D ∧
      EqOn (d ∘ b) (a ∘ k) D ∧
      IsPLCirclePositive (c '' J) (c ∘ d ∘ c.symm) := by
  have : Nonempty M := ⟨hD.nonempty.choose⟩
  let i := Function.invFunOn b D
  have hbbi : BijOn b D D := ⟨fun _ hx => hbD ▸ mem_image_of_mem b hx, hb.injOn, hbD.ge⟩
  have hibi : BijOn i D D := hbbi.invOn_invFunOn.symm.bijOn
    hbbi.surjOn.mapsTo_invFunOn hbbi.mapsTo
  have hi : IsPLHomeomorphInto 3 i D := hbD ▸ hb.invFunOn
  have hki : IsPLHomeomorphInto 3 (k ∘ i) D :=
    hi.comp_of_image_eq (by rw [hibi.image_eq]; exact hk)
  have hkiD : (k ∘ i) '' D = D := by rw [image_comp, hibi.image_eq, hkD]
  let d := a ∘ k ∘ i
  have hd : IsPLHomeomorphInto 3 d D :=
    hki.comp_of_image_eq (by rw [hkiD]; exact ha)
  have hdD : d '' D = D := by change (a ∘ (k ∘ i)) '' D = D; rw [image_comp, hkiD, haD]
  have heq : EqOn (d ∘ b) (a ∘ k) D := by
    intro x hx
    change a (k (Function.invFunOn b D (b x))) = a (k x)
    rw [hb.injOn.leftInvOn_invFunOn hx]
  have heqc : EqOn ((c ∘ d ∘ c.symm) ∘ (c ∘ b ∘ c.symm))
      ((c ∘ a ∘ c.symm) ∘ (c ∘ k ∘ c.symm)) (c '' J) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxD := hD.boundary_subset hx
    have hbx : b x ∈ D := hbD ▸ mem_image_of_mem b hxD
    have hkx : k x ∈ D := hkD ▸ mem_image_of_mem k hxD
    change c (d (c.symm (c (b (c.symm (c x)))))) =
      c (a (c.symm (c (k (c.symm (c x))))))
    simp only [c.left_inv (hDc hxD), c.left_inv (hDc hbx), c.left_inv (hDc hkx)]
    exact congrArg c (heq hxD)
  obtain ⟨r, hr, hJ⟩ := hD.exists_isPLHomeomorphOn_image_chart hc hDc
  have hS : IsPLSphere 1 (c '' J) := by
    rw [hJ]
    exact hr.isPLSphere_image_stdSimplexBoundary (n := 1)
  exact ⟨d, hd, hdD, heq, isPLCirclePositive_of_commuting_corrections hS
    (ha.isPLHomeomorphOn_chart_rim hD haD hc hDc)
    (hb.isPLHomeomorphOn_chart_rim hD hbD hc hDc)
    (hk.isPLHomeomorphOn_chart_rim hD hkD hc hDc)
    (hd.isPLHomeomorphOn_chart_rim hD hdD hc hDc) heqc hpar⟩

end DifferentialGeometry.Topology.PiecewiseLinear
