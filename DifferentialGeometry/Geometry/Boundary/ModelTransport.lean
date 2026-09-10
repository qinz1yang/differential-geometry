import DifferentialGeometry.Geometry.Boundary.Model.Basic
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.MeasureTheory.Measure.Haar.Unique

noncomputable section
open Set Function Topology
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

namespace Poincare.Geometry.Boundary

universe u v

@[instance_reducible]
def hasSmoothBoundaryOfContinuousLinearEquiv
    {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : Type v} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [hI : HasSmoothBoundary E H I] (e : E ≃L[ℝ] F) :
    HasSmoothBoundary F H (I.transContinuousLinearEquiv e) where
  boundaryE := hI.boundaryE
  boundaryENormedGroup := inferInstance
  boundaryENormedSpace := inferInstance
  boundaryEInnerProductSpace := inferInstance
  boundaryEFiniteDimensional := inferInstance
  boundaryH := hI.boundaryH
  boundaryHTopologicalSpace := inferInstance
  boundaryI := hI.boundaryI
  boundaryIBoundaryless := inferInstance
  inclH := hI.inclH
  inclH_continuous := hI.inclH_continuous
  inclH_injective := hI.inclH_injective
  inclH_isInducing := hI.inclH_isInducing
  inclH_isClosed_image := by
    change IsClosed (range (e ∘ (I ∘ hI.inclH)))
    rw [range_comp]
    exact e.toHomeomorph.isClosedMap _ hI.inclH_isClosed_image
  projE := hI.projE ∘ e.symm
  projE_continuous := hI.projE_continuous.comp e.symm.continuous
  projE_contDiff := hI.projE_contDiff.comp e.symm.contDiff
  I_inclH_boundaryI_symm_contDiff := e.contDiff.comp hI.I_inclH_boundaryI_symm_contDiff
  range_I_inclH := by
    change range (e ∘ (I ∘ hI.inclH)) = frontier (range (e ∘ I))
    rw [range_comp e (I ∘ hI.inclH), range_comp e I, hI.range_I_inclH]
    exact e.toHomeomorph.image_frontier (range I)
  proj_inclH_compat := by
    intro x
    change hI.projE (e.symm (e (I (hI.inclH x)))) = hI.boundaryI x
    rw [e.symm_apply_apply]
    exact hI.proj_inclH_compat x
  inwardCoordE := e hI.inwardCoordE
  inwardCoordE_enters := by
    intro y hy
    have hfront : frontier (range (I.transContinuousLinearEquiv e)) = e '' frontier (range I) := by
      rw [I.transContinuousLinearEquiv_range]
      exact (e.toHomeomorph.image_frontier (range I)).symm
    rw [hfront] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨δ, hδ, henter⟩ := hI.inwardCoordE_enters x hx
    refine ⟨δ, hδ, ?_⟩
    intro t ht
    have hint : interior (range (I.transContinuousLinearEquiv e)) = e '' interior (range I) := by
      rw [I.transContinuousLinearEquiv_range]
      exact (e.toHomeomorph.image_interior (range I)).symm
    rw [hint]
    exact ⟨x + t • hI.inwardCoordE, henter t ht, by simp⟩
  inwardCoordE_transverse := by
    intro y
    change e hI.inwardCoordE ∉ range (fderiv ℝ (e ∘ (I ∘ hI.inclH ∘ hI.boundaryI.symm)) y)
    rw [fderiv_comp y e.differentiableAt
      (hI.I_inclH_boundaryI_symm_contDiff.differentiable (by decide) y)]
    have he : fderiv ℝ (e : E → F) ((I ∘ hI.inclH ∘ hI.boundaryI.symm) y) =
        (e : E →L[ℝ] F) := e.toContinuousLinearMap.fderiv
    rw [he]
    rintro ⟨z, hz⟩
    exact hI.inwardCoordE_transverse y ⟨z, e.injective hz⟩
  range_frontier_basis_addHaar_zero := by
    intro _
    let : MeasurableSpace E := borel E
    have : BorelSpace E := ⟨rfl⟩
    let : MeasurableSpace F := borel F
    have : BorelSpace F := ⟨rfl⟩
    let μ := (Module.finBasis ℝ E).addHaar
    let ν := (Module.finBasis ℝ F).addHaar
    have hzero : (μ.map e) (frontier (range (I.transContinuousLinearEquiv e))) = 0 := by
      rw [MeasureTheory.Measure.map_apply e.continuous.measurable isClosed_frontier.measurableSet,
        I.transContinuousLinearEquiv_range]
      have hfront : frontier (e '' range I) = e '' frontier (range I) :=
        (e.toHomeomorph.image_frontier (range I)).symm
      rw [hfront, e.injective.preimage_image]
      exact hI.range_frontier_basis_addHaar_zero
    exact (MeasureTheory.Measure.absolutelyContinuous_isAddHaarMeasure ν (μ.map e)) hzero
  finrank_boundaryE_succ := by
    intro _
    exact hI.finrank_boundaryE_succ.trans e.toLinearEquiv.finrank_eq

theorem boundary_transContinuousLinearEquiv
    {E F H W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) [TopologicalSpace W] [ChartedSpace H W]
    (e : E ≃L[ℝ] F) : (I.transContinuousLinearEquiv e).boundary W = I.boundary W := by
  let d := e.toTransContinuousLinearEquiv I W (n := ∞)
  ext w
  exact ((d.isLocalDiffeomorph w).isBoundaryPoint_iff (by decide)).symm

theorem injective_mfderiv_transContinuousLinearEquiv_left
    {E F H W G K M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace W] [ChartedSpace H W]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace K] (J : ModelWithCorners ℝ G K)
    [TopologicalSpace M] [ChartedSpace K M]
    (e : E ≃L[ℝ] F) (f : W → M) (hf : ContMDiff I J ∞ f)
    (w : W) (hinj : Function.Injective (mfderiv I J f w)) :
    Function.Injective (mfderiv (I.transContinuousLinearEquiv e) J f w) := by
  let d := e.toTransContinuousLinearEquiv I W (n := ∞)
  have hcomp : mfderiv (I.transContinuousLinearEquiv e) J (f ∘ d.symm) w =
      (mfderiv I J f w).comp (mfderiv (I.transContinuousLinearEquiv e) I d.symm w) :=
    mfderiv_comp w (hf.mdifferentiable (by decide) w) (d.symm.contMDiff.mdifferentiable (by decide) w)
  change Function.Injective (mfderiv (I.transContinuousLinearEquiv e) J (f ∘ d.symm) w)
  rw [hcomp]
  exact hinj.comp (d.symm.mfderivToContinuousLinearEquiv (by decide) w).injective

end Poincare.Geometry.Boundary
