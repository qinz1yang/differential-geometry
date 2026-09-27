/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryDouble
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ProjectedBoundaryHalfSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private def plTranslation (v : EuclideanSpace ℝ (Fin 3)) :
    OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)) :=
  (Homeomorph.addRight v).toOpenPartialHomeomorph

private theorem plTranslation_mem_plGroupoid (v : EuclideanSpace ℝ (Fin 3)) :
    plTranslation v ∈ plGroupoid 3 := by
  rw [mem_plGroupoid_iff]
  refine ⟨(isPLHomeomorphOn_add_const v).isPiecewiseAffineOn, ?_⟩
  change IsPiecewiseAffineOn (fun x => x + (-v)) univ
  exact (isPLHomeomorphOn_add_const (-v)).isPiecewiseAffineOn

private theorem trans_plTranslation_mem_maximalAtlas
    {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    {e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin 3))}
    (he : e ∈ (plGroupoid 3).maximalAtlas X) (v : EuclideanSpace ℝ (Fin 3)) :
    e.trans (plTranslation v) ∈ (plGroupoid 3).maximalAtlas X := by
  intro e' he'
  have ht := plTranslation_mem_plGroupoid v
  constructor
  · rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc]
    exact (plGroupoid 3).trans ((plGroupoid 3).symm ht) (he e' he').1
  · rw [← OpenPartialHomeomorph.trans_assoc]
    exact (plGroupoid 3).trans (he e' he').2 ht

private def proj0 : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ where
  toFun z := z 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem proj0_ne_zero : proj0 ≠ 0 := by
  intro h
  let z : EuclideanSpace ℝ (Fin 3) := (WithLp.equiv 2 (Fin 3 → ℝ)).symm (fun _ => (1 : ℝ))
  have hv := congrArg (fun l : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ => l z) h
  change (1 : ℝ) = 0 at hv
  norm_num at hv

open Classical in
theorem exists_adaptedHalfSpaceChart_in_double {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] (hK : IsCombinatorialManifoldWithBoundary 3 K) :
    letI := combinatorialChartedSpace (double 3 K)
      (isCombinatorialManifold_double_succ_succ K hK)
    let ι := simplicialMap K (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 K) id)
    let C := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹' (ι '' K.space)
    let Bd := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹'
      (ι '' (PiecewiseLinear.boundaryComplex 3 K).space)
    ∀ (y : (double 3 K).space) (U : Set (double 3 K).space), U ∈ 𝓝 y →
      ∃ (ec : OpenPartialHomeomorph (double 3 K).space (EuclideanSpace ℝ (Fin 3)))
        (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ),
        ec ∈ (plGroupoid 3).maximalAtlas (double 3 K).space ∧ ℓ ≠ 0 ∧
          y ∈ ec.source ∧ ec.source ⊆ U ∧
          (∀ x ∈ ec.source, x ∈ C ↔ 0 ≤ ℓ (ec x)) ∧
          (∀ x ∈ ec.source, x ∈ Bd ↔ ℓ (ec x) = 0) := by
  intro ι C Bd y U hU
  have hL : IsCombinatorialManifold 3 (double 3 K) :=
    isCombinatorialManifold_double_succ_succ K hK
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (double 3 K).space :=
    combinatorialChartedSpace (double 3 K) hL
  let _ : HasGroupoid (double 3 K).space (plGroupoid 3) :=
    combinatorialChartedSpace_hasGroupoid (double 3 K) hL
  let _ : Finite (glued₂ K (PiecewiseLinear.boundaryComplex 3 K) id).faces :=
    (glued₂_faces_finite K (PiecewiseLinear.boundaryComplex 3 K) id).to_subtype
  have hC_eq : C = ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹'
      (glued₂ K (PiecewiseLinear.boundaryComplex 3 K) id).space := by
    rw [glued₂_space]
  have hC_closed : IsClosed C := by
    rw [hC_eq]
    exact (isPolyhedron_space (glued₂ K (PiecewiseLinear.boundaryComplex 3 K) id)).isClosed.preimage
      continuous_subtype_val
  have hBd_eq : frontier C = Bd := by
    rw [hC_eq]
    exact frontier_preimage_glued₂_space_in_double (n := 1) K hK
  obtain ⟨V, hVU, hVopen, hyV⟩ := mem_nhds_iff.mp hU
  by_cases hyBd : y ∈ Bd
  · have hyFrontier : y ∈ frontier C := hBd_eq.symm ▸ hyBd
    obtain ⟨b, hb, -⟩ := hyBd
    have hbK : b ∈ K.space :=
      space_mono_of_faces_subset (boundaryComplex_faces_subset 3 K) hb
    let p : K.space := ⟨b, hbK⟩
    obtain ⟨e, ℓ, he, hℓ, hye, hCiff, hBdiff⟩ :=
      exists_halfSpace_chart_glued₂_space_in_double K hK p y hyFrontier
    let ec := e.restr V
    have hec_atlas : ec ∈ (plGroupoid 3).maximalAtlas (double 3 K).space :=
      restr_mem_maximalAtlas (G := plGroupoid 3) he hVopen
    have hyec : y ∈ ec.source := ⟨hye, hVopen.interior_eq.symm ▸ hyV⟩
    have hec_sub : ec.source ⊆ U := fun x hx => hVU (interior_subset hx.2)
    refine ⟨ec, ℓ, hec_atlas, hℓ, hyec, hec_sub, ?_, ?_⟩
    · intro x hx
      exact hCiff x hx.1
    · intro x hx
      rw [← hBd_eq]
      exact hBdiff x hx.1
  · by_cases hyC : y ∈ C
    · have hyInt : y ∈ interior C :=
        (mem_interior_iff_notMem_frontier hyC).mpr (hBd_eq.symm ▸ hyBd)
      let e0 := chartAt (EuclideanSpace ℝ (Fin 3)) y
      have he0 : e0 ∈ (plGroupoid 3).maximalAtlas (double 3 K).space :=
        StructureGroupoid.chart_mem_maximalAtlas (plGroupoid 3) y
      have hye0 : y ∈ e0.source := mem_chart_source (EuclideanSpace ℝ (Fin 3)) y
      let targetPt : EuclideanSpace ℝ (Fin 3) :=
        (WithLp.equiv 2 (Fin 3 → ℝ)).symm (fun _ => 1)
      let v := targetPt - e0 y
      let e1 := e0.trans (plTranslation v)
      have he1 : e1 ∈ (plGroupoid 3).maximalAtlas (double 3 K).space :=
        trans_plTranslation_mem_maximalAtlas he0 v
      have hye1 : y ∈ e1.source := by
        rw [OpenPartialHomeomorph.trans_source]
        exact ⟨hye0, mem_univ _⟩
      have he1y : e1 y = targetPt := by
        change e0 y + v = targetPt
        dsimp [v]
        rw [add_sub_cancel]
      have he1y0 : 0 < proj0 (e1 y) := by
        rw [he1y]
        change 0 < (1 : ℝ)
        norm_num
      let S : Set (EuclideanSpace ℝ (Fin 3)) := proj0 ⁻¹' Ioi 0
      have hS : IsOpen S :=
        isOpen_Ioi.preimage (LinearMap.continuous_of_finiteDimensional proj0)
      have hOopen : IsOpen (e1.source ∩ e1 ⁻¹' S) :=
        e1.continuousOn.isOpen_inter_preimage e1.open_source hS
      let W := (e1.source ∩ e1 ⁻¹' S) ∩ V ∩ interior C
      have hWopen : IsOpen W := (hOopen.inter hVopen).inter isOpen_interior
      have hyW : y ∈ W := ⟨⟨⟨hye1, he1y0⟩, hyV⟩, hyInt⟩
      let ec := e1.restr W
      have hec_atlas : ec ∈ (plGroupoid 3).maximalAtlas (double 3 K).space :=
        restr_mem_maximalAtlas (G := plGroupoid 3) he1 hWopen
      have hyec : y ∈ ec.source := ⟨hye1, hWopen.interior_eq.symm ▸ hyW⟩
      have hec_sub : ec.source ⊆ U := fun x hx => hVU (interior_subset hx.2).1.2
      refine ⟨ec, proj0, hec_atlas, proj0_ne_zero, hyec, hec_sub, ?_, ?_⟩
      · intro x hx
        have hxW : x ∈ W := interior_subset hx.2
        have hxC : x ∈ C := interior_subset hxW.2
        have hxpos : 0 < proj0 (ec x) := hxW.1.1.2
        exact iff_of_true hxC hxpos.le
      · intro x hx
        have hxW : x ∈ W := interior_subset hx.2
        have hxBd : x ∉ Bd := by
          rw [← hBd_eq]
          exact fun hxFr => (hxFr.2 hxW.2).elim
        have hxne : proj0 (ec x) ≠ 0 := hxW.1.1.2.ne'
        exact iff_of_false hxBd hxne
    · let e0 := chartAt (EuclideanSpace ℝ (Fin 3)) y
      have he0 : e0 ∈ (plGroupoid 3).maximalAtlas (double 3 K).space :=
        StructureGroupoid.chart_mem_maximalAtlas (plGroupoid 3) y
      have hye0 : y ∈ e0.source := mem_chart_source (EuclideanSpace ℝ (Fin 3)) y
      let targetPt : EuclideanSpace ℝ (Fin 3) :=
        (WithLp.equiv 2 (Fin 3 → ℝ)).symm (fun _ => -1)
      let v := targetPt - e0 y
      let e1 := e0.trans (plTranslation v)
      have he1 : e1 ∈ (plGroupoid 3).maximalAtlas (double 3 K).space :=
        trans_plTranslation_mem_maximalAtlas he0 v
      have hye1 : y ∈ e1.source := by
        rw [OpenPartialHomeomorph.trans_source]
        exact ⟨hye0, mem_univ _⟩
      have he1y : e1 y = targetPt := by
        change e0 y + v = targetPt
        dsimp [v]
        rw [add_sub_cancel]
      have he1y0 : proj0 (e1 y) < 0 := by
        rw [he1y]
        change (-1 : ℝ) < 0
        norm_num
      let S : Set (EuclideanSpace ℝ (Fin 3)) := proj0 ⁻¹' Iio 0
      have hS : IsOpen S :=
        isOpen_Iio.preimage (LinearMap.continuous_of_finiteDimensional proj0)
      have hOopen : IsOpen (e1.source ∩ e1 ⁻¹' S) :=
        e1.continuousOn.isOpen_inter_preimage e1.open_source hS
      let W := (e1.source ∩ e1 ⁻¹' S) ∩ V ∩ Cᶜ
      have hWopen : IsOpen W := (hOopen.inter hVopen).inter hC_closed.isOpen_compl
      have hyW : y ∈ W := ⟨⟨⟨hye1, he1y0⟩, hyV⟩, hyC⟩
      let ec := e1.restr W
      have hec_atlas : ec ∈ (plGroupoid 3).maximalAtlas (double 3 K).space :=
        restr_mem_maximalAtlas (G := plGroupoid 3) he1 hWopen
      have hyec : y ∈ ec.source := ⟨hye1, hWopen.interior_eq.symm ▸ hyW⟩
      have hec_sub : ec.source ⊆ U := fun x hx => hVU (interior_subset hx.2).1.2
      refine ⟨ec, proj0, hec_atlas, proj0_ne_zero, hyec, hec_sub, ?_, ?_⟩
      · intro x hx
        have hxW : x ∈ W := interior_subset hx.2
        have hxC : x ∉ C := hxW.2
        have hxneg : proj0 (ec x) < 0 := hxW.1.1.2
        exact ⟨fun h => (hxC h).elim, fun hge => (not_lt_of_ge hge hxneg).elim⟩
      · intro x hx
        have hxW : x ∈ W := interior_subset hx.2
        have hxBd : x ∉ Bd := by
          rw [← hBd_eq]
          intro hxFr
          exact hxW.2 (hC_closed.frontier_subset hxFr)
        have hxne : proj0 (ec x) ≠ 0 := hxW.1.1.2.ne
        exact iff_of_false hxBd hxne

end DifferentialGeometry.Topology.PiecewiseLinear
