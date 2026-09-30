/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePieceCellModel
import DifferentialGeometry.Topology.PiecewiseLinear.PieceMap
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePieceRestriction

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]

open Classical in
theorem LocallyFinitePLPieceIn.continuousOn_invFunOn {Y : Set X}
    (T : LocallyFinitePLPieceIn E n X Y) :
    ContinuousOn (Function.invFunOn T.map T.complex.space) Y := by
  let g : Y → T.complex.space := fun y =>
    ⟨Function.invFunOn T.map T.complex.space y, T.bijOn.surjOn.mapsTo_invFunOn y.2⟩
  have hg : Continuous g := T.isEmbedding.continuous_iff.mpr (by
    have hval : Continuous (fun y : Y => (y : X)) := continuous_subtype_val
    exact hval.congr (fun y => (T.bijOn.invOn_invFunOn.2 y.2).symm))
  exact continuousOn_iff_continuous_domRestrict.mpr (continuous_subtype_val.comp hg)

theorem LocallyFinitePLPieceIn.isPLOn_comp {Y : Set X}
    (T : LocallyFinitePLPieceIn E n X Y)
    {f : EuclideanSpace ℝ (Fin m) → E} {P : Set (EuclideanSpace ℝ (Fin m))}
    (hf : IsPiecewiseAffineOn f P) (hmap : MapsTo f P T.complex.space) :
    IsPLOn m n (T.map ∘ f) P := by
  have hcont := T.continuousOn.comp hf.continuousOn hmap
  intro x hx
  apply (StructureGroupoid.liftPropWithinAt_self_source).mpr
  refine ⟨hcont x hx, ?_⟩
  let e := chartAt (EuclideanSpace ℝ (Fin n)) (T.map (f x))
  have hfx : f x ∈ T.complex.space ∩ T.map ⁻¹' e.source :=
    ⟨hmap hx, mem_chart_source _ _⟩
  have hpl := (T.isPiecewiseAffineOn_chart e (chart_mem_atlas _ _) (f x) hfx).comp (hf x hx)
  have hnhds : P ∩ f ⁻¹' (T.complex.space ∩ T.map ⁻¹' e.source) ∈ 𝓝[P] x := by
    have hevent := (hcont x hx).preimage_mem_nhdsWithin
      (e.open_source.mem_nhds (mem_chart_source _ _))
    filter_upwards [self_mem_nhdsWithin, hevent] with y hy hye
    exact ⟨hy, hmap hy, hye⟩
  have hfilter : 𝓝[P] x = 𝓝[P ∩ f ⁻¹' (T.complex.space ∩ T.map ⁻¹' e.source)] x := by
    rw [← nhdsWithin_inter_of_mem' hnhds, inter_eq_right.mpr inter_subset_left]
  obtain ⟨ι, hι, C, A, hC, hCx⟩ := hpl
  refine ⟨ι, hι, C, A, fun i =>
    ⟨(hC i).1, (hC i).2.1.trans inter_subset_left, (hC i).2.2⟩, ?_⟩
  rwa [hfilter]

open Classical in
theorem LocallyFinitePLPieceIn.isPLHomeomorphInto_comp [FiniteDimensional ℝ E]
    {Y : Set X} (T : LocallyFinitePLPieceIn E n X Y)
    {ρ : EuclideanSpace ℝ (Fin n) → E} {Q : Set (EuclideanSpace ℝ (Fin n))} {P : Set E}
    (hρ : IsPLHomeomorphOn ρ Q P) (hPK : P ⊆ T.complex.space) :
    IsPLHomeomorphInto n (T.map ∘ ρ) Q := by
  let g := Function.invFunOn ρ Q ∘ Function.invFunOn T.map T.complex.space
  have himage : (T.map ∘ ρ) '' Q = T.map '' P := by rw [image_comp, hρ.image_eq]
  have hinvP : MapsTo (Function.invFunOn T.map T.complex.space) (T.map '' P) P := by
    rintro _ ⟨z, hz, rfl⟩
    simpa only [T.bijOn.invOn_invFunOn.1 (hPK hz)] using hz
  have himageY : T.map '' P ⊆ Y := by
    rintro _ ⟨z, hz, rfl⟩
    exact T.bijOn.mapsTo (hPK hz)
  have hgcont : ContinuousOn g (T.map '' P) :=
    hρ.isPiecewiseAffineOn_invFunOn.continuousOn.comp
      (T.continuousOn_invFunOn.mono himageY) hinvP
  have hgpl : IsPLOn n n g (T.map '' P) := by
    intro y hy
    let e := chartAt (EuclideanSpace ℝ (Fin n)) y
    have hey : y ∈ e.source := mem_chart_source _ _
    apply (StructureGroupoid.liftPropWithinAt_self_target).mpr
    refine ⟨hgcont y hy, ?_⟩
    have hlocal := hρ.isPiecewiseAffineOn_invFunOn.comp
      (T.isPiecewiseAffineOn_chart_symm e (chart_mem_atlas _ _))
    have hdomain :
        (e.target ∩ e.symm ⁻¹' Y) ∩
          (Function.invFunOn T.map T.complex.space ∘ e.symm) ⁻¹' P =
        e.symm ⁻¹' (T.map '' P) ∩ e.target := by
      ext z
      constructor
      · rintro ⟨⟨hzT, hzY⟩, hzP⟩
        exact ⟨⟨Function.invFunOn T.map T.complex.space (e.symm z), hzP,
          T.bijOn.invOn_invFunOn.2 hzY⟩, hzT⟩
      · rintro ⟨⟨w, hw, hwe⟩, hzT⟩
        refine ⟨⟨hzT, ?_⟩, ?_⟩
        · change e.symm z ∈ Y
          rw [← hwe]
          exact T.bijOn.mapsTo (hPK hw)
        · change Function.invFunOn T.map T.complex.space (e.symm z) ∈ P
          rw [← hwe, T.bijOn.invOn_invFunOn.1 (hPK hw)]
          exact hw
    rw [hdomain] at hlocal
    have hpoint : e y ∈ e.symm ⁻¹' (T.map '' P) ∩ e.target := by
      exact ⟨by simpa only [mem_preimage, e.left_inv hey] using hy, e.map_source hey⟩
    exact (hlocal (e y) hpoint).of_inter_of_mem_nhds
      (e.open_target.mem_nhds (e.map_source hey))
  rw [isPLHomeomorphInto_iff_exists_inverse]
  refine ⟨T.isPLOn_comp hρ.isPiecewiseAffineOn
    (fun z hz => hPK (hρ.bijOn.mapsTo hz)), ?_, g, ?_, ?_⟩
  · intro x hx z hz hxz
    exact hρ.bijOn.injOn hx hz (T.bijOn.injOn
      (hPK (hρ.bijOn.mapsTo hx)) (hPK (hρ.bijOn.mapsTo hz)) hxz)
  · rwa [himage]
  · intro x hx
    dsimp [g]
    rw [T.bijOn.invOn_invFunOn.1 (hPK (hρ.bijOn.mapsTo hx)),
      hρ.bijOn.invOn_invFunOn.1 hx]

section Cells

variable [FiniteDimensional ℝ E] {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {U : Set M}

open Classical in
theorem LocallyFinitePLPieceIn.isPLCellOn_image
    (T : LocallyFinitePLPieceIn E 3 M U) {d : ℕ} (hd : d ≤ 3)
    {P : Set E} {r : (Fin (d + 1) → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin (d + 1))) P)
    (hPK : P ⊆ T.complex.space) :
    IsPLCellOn d (T.map '' P) (T.map '' (r '' stdSimplexBoundary d)) := by
  obtain ⟨S, B, ⟨Q, p, u, hp, -, -, -⟩, -⟩ := exists_isPLCellOn_of_le_three d hd
  let ρ := r ∘ Function.invFunOn p (Convexity.StdSimplex.coordinateSet ℝ (Fin (d + 1)))
  have hρ : IsPLHomeomorphOn ρ Q P := hp.symm.trans hr
  have hbsub : stdSimplexBoundary d ⊆ Convexity.StdSimplex.coordinateSet ℝ (Fin (d + 1)) :=
    fun _ hx => hx.1
  have hbd : ρ '' (p '' stdSimplexBoundary d) = r '' stdSimplexBoundary d := by
    have h : EqOn
        (Function.invFunOn p (Convexity.StdSimplex.coordinateSet ℝ (Fin (d + 1))) ∘ p) id
        (stdSimplexBoundary d) :=
      fun x hx => hp.bijOn.invOn_invFunOn.1 (hbsub hx)
    calc
      ρ '' (p '' stdSimplexBoundary d) = (ρ ∘ p) '' stdSimplexBoundary d := by
        rw [← image_comp]
      _ = (r ∘ (Function.invFunOn p (Convexity.StdSimplex.coordinateSet ℝ (Fin (d + 1))) ∘ p)) ''
          stdSimplexBoundary d := by rfl
      _ = r '' ((Function.invFunOn p (Convexity.StdSimplex.coordinateSet ℝ (Fin (d + 1))) ∘ p) ''
          stdSimplexBoundary d) := by rw [image_comp]
      _ = r '' stdSimplexBoundary d :=
        congrArg (fun A => r '' A) (h.image_eq.trans (image_id _))
  refine ⟨Q, p, T.map ∘ ρ, hp, T.isPLHomeomorphInto_comp hρ hPK, ?_, ?_⟩
  · rw [image_comp, hρ.image_eq]
  · rw [image_comp, hbd]

end Cells

end DifferentialGeometry.Topology.PiecewiseLinear
