/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PieceTransition
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralGraph
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundary

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]

theorem LocallyFinitePLPieceIn.isPiecewiseAffineOn_invFunOn_comp {Y : Set X}
    (T : LocallyFinitePLPieceIn E n X Y)
    {m : ℕ} {f : EuclideanSpace ℝ (Fin m) → X}
    {S : Set (EuclideanSpace ℝ (Fin m))} (hf : IsPLOn m n f S) :
    IsPiecewiseAffineOn (Function.invFunOn T.map T.complex.space ∘ f) (S ∩ f ⁻¹' Y) := by
  intro x hx
  let e := chartAt (EuclideanSpace ℝ (Fin n)) (f x)
  have he : e ∈ atlas (EuclideanSpace ℝ (Fin n)) X := chart_mem_atlas _ _
  have hxe : f x ∈ e.source := mem_chart_source _ _
  have h₁ := (hf x hx.1).prop
  change IsPiecewiseAffineWithinAt (e ∘ f) S x at h₁
  have h₂ := T.isPiecewiseAffineOn_chart_symm e he (e (f x))
    ⟨e.map_source hxe, by
      change e.symm (e (f x)) ∈ Y
      rw [e.left_inv hxe]
      exact hx.2⟩
  have hcomp := h₂.comp (f := e ∘ f) (x := x) h₁
  have hfcont : ContinuousOn f S := fun z hz => (hf z hz).continuousWithinAt
  obtain ⟨O, hO, hpre⟩ := continuousOn_iff'.mp hfcont e.source e.open_source
  have hxO : x ∈ O := (hpre ▸ (show x ∈ f ⁻¹' e.source ∩ S from ⟨hxe, hx.1⟩)).1
  have hlocal := hcomp.inter_of_mem_nhds (hO.mem_nhds hxO)
  have hdomain :
      (S ∩ (e ∘ f) ⁻¹' (e.target ∩ e.symm ⁻¹' Y)) ∩ O = (S ∩ f ⁻¹' Y) ∩ O := by
    ext z
    constructor
    · rintro ⟨⟨hzS, hztarget, hzY⟩, hzO⟩
      have hzsource : f z ∈ e.source := by
        have hz : z ∈ f ⁻¹' e.source ∩ S := by
          rw [hpre]
          exact ⟨hzO, hzS⟩
        exact hz.1
      refine ⟨⟨hzS, ?_⟩, hzO⟩
      change e.symm (e (f z)) ∈ Y at hzY
      change f z ∈ Y
      simpa only [e.left_inv hzsource] using hzY
    · rintro ⟨⟨hzS, hzY⟩, hzO⟩
      have hzsource : f z ∈ e.source := by
        have hz : z ∈ f ⁻¹' e.source ∩ S := by
          rw [hpre]
          exact ⟨hzO, hzS⟩
        exact hz.1
      refine ⟨⟨hzS, e.map_source hzsource, ?_⟩, hzO⟩
      change f z ∈ Y at hzY
      change e.symm (e (f z)) ∈ Y
      simpa only [e.left_inv hzsource] using hzY
  rw [hdomain] at hlocal
  apply (hlocal.congr fun z hz => ?_).of_inter_of_mem_nhds (hO.mem_nhds hxO)
  have hzsource : f z ∈ e.source := by
    have hz' : z ∈ f ⁻¹' e.source ∩ S := by
      rw [hpre]
      exact ⟨hz.2, hz.1.1⟩
    exact hz'.1
  simp only [Function.comp_apply, e.left_inv hzsource]

section Cells

variable [FiniteDimensional ℝ E] {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {U : Set M}

open Classical in
theorem LocallyFinitePLPieceIn.exists_isPLHomeomorphOn_cell_preimage
    (T : LocallyFinitePLPieceIn E 3 M U) {d : ℕ} {C B : Set M}
    (hC : IsPLCellOn d C B) (hCU : C ⊆ U) :
    ∃ r : (Fin (d + 1) → ℝ) → E,
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin (d + 1)))
        (T.complex.space ∩ T.map ⁻¹' C) ∧
      r '' stdSimplexBoundary d = T.complex.space ∩ T.map ⁻¹' B := by
  obtain ⟨P, p, u, hp, hu, hCP, hBP⟩ := hC
  let g := Function.invFunOn T.map T.complex.space ∘ u
  have huU : MapsTo u P U := by
    intro x hx
    apply hCU
    rw [hCP]
    exact mem_image_of_mem u hx
  have hgK : MapsTo g P T.complex.space := fun x hx =>
    T.bijOn.surjOn.mapsTo_invFunOn (huU hx)
  have hcancel : ∀ x ∈ P, T.map (g x) = u x := fun x hx =>
    T.bijOn.invOn_invFunOn.2 (huU hx)
  have hbij : BijOn g P (T.complex.space ∩ T.map ⁻¹' C) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      refine ⟨hgK hx, ?_⟩
      change T.map (g x) ∈ C
      rw [hcancel x hx, hCP]
      exact mem_image_of_mem u hx
    · intro x hx y hy hxy
      apply hu.injOn hx hy
      exact (hcancel x hx).symm.trans ((congrArg T.map hxy).trans (hcancel y hy))
    · rintro y ⟨hy, hyC⟩
      rw [hCP] at hyC
      obtain ⟨x, hx, hxy⟩ := hyC
      refine ⟨x, hx, ?_⟩
      change Function.invFunOn T.map T.complex.space (u x) = y
      rw [hxy, T.bijOn.invOn_invFunOn.1 hy]
  have hgpl : IsPiecewiseAffineOn g P := by
    have h := T.isPiecewiseAffineOn_invFunOn_comp hu.isPLOn
    rw [inter_eq_left.mpr (show P ⊆ u ⁻¹' U from huU)] at h
    exact h
  have hg : IsPLHomeomorphOn g P (T.complex.space ∩ T.map ⁻¹' C) :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn
      (IsPLBall.isPolyhedron ⟨p, hp⟩) hgpl hbij
  refine ⟨g ∘ p, hp.trans hg, ?_⟩
  rw [image_comp]
  ext y
  constructor
  · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
    have hpz : p z ∈ P := hp.bijOn.mapsTo hz.1
    refine ⟨hgK hpz, ?_⟩
    change T.map (g (p z)) ∈ B
    rw [hcancel _ hpz, hBP]
    exact ⟨p z, ⟨z, hz, rfl⟩, rfl⟩
  · rintro ⟨hyK, hyB⟩
    rw [hBP] at hyB
    obtain ⟨x, hx, hxy⟩ := hyB
    refine ⟨x, hx, ?_⟩
    change Function.invFunOn T.map T.complex.space (u x) = y
    rw [hxy, T.bijOn.invOn_invFunOn.1 hyK]

theorem LocallyFinitePLPieceIn.isPLBall_preimage_of_isPLCellOn
    (T : LocallyFinitePLPieceIn E 3 M U) {d : ℕ} {C B : Set M}
    (hC : IsPLCellOn d C B) (hCU : C ⊆ U) :
    IsPLBall d (T.complex.space ∩ T.map ⁻¹' C) := by
  obtain ⟨r, hr, -⟩ := T.exists_isPLHomeomorphOn_cell_preimage hC hCU
  exact ⟨r, hr⟩

end Cells

end DifferentialGeometry.Topology.PiecewiseLinear
