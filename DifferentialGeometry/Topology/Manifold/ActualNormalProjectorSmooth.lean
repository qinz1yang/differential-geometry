import DifferentialGeometry.Analysis.InnerProductSpace.NormalGramProjector
import DifferentialGeometry.Topology.Manifold.NearestNormalProjector
import DifferentialGeometry.Topology.Manifold.SmoothMapDifferentialCoordinates
import Mathlib.Analysis.Normed.Lp.PiLp

/-! The actual orthogonal normal projector varies smoothly in the unchanged embedding atlas. -/

set_option autoImplicit false
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace GC.MetricGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] {k : ℕ} {Z : Set H} [ChartedSpace (Fin k → ℝ) Z]
  [IsManifold 𝓘(ℝ, Fin k → ℝ) ∞ Z]

omit [FiniteDimensional ℝ H] in
theorem actualEmbeddingTangentCoordinate_eq (p x : Z)
    (hx : x ∈ (chartAt (Fin k → ℝ) p).source) :
    inTangentCoordinates 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) id
      (Subtype.val : Z → H) (mfderiv 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) Subtype.val) p x =
      (mfderiv 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) (Subtype.val : Z → H) x).comp
        ((DifferentialGeometry.Topology.Manifold.preferredChartTangentEquiv
          𝓘(ℝ, Fin k → ℝ) p x hx).symm : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ)) := by
  have h := inTangentCoordinates_eq_mfderiv_comp (I := 𝓘(ℝ, Fin k → ℝ)) (I' := 𝓘(ℝ, H))
    (f := id) (g := (Subtype.val : Z → H))
    (ϕ := mfderiv 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) (Subtype.val : Z → H)) hx (mem_univ _)
  have hc : (mfderiv 𝓘(ℝ, H) 𝓘(ℝ, H) (extChartAt 𝓘(ℝ, H) (p : H)) (x : H) :
      H →L[ℝ] H) = ContinuousLinearMap.id ℝ H := by
    rw [extChartAt_model_space_eq_id]
    change mfderiv 𝓘(ℝ, H) 𝓘(ℝ, H) (id : H → H) (x : H) = _
    rw [mfderiv_id]
    rfl
  apply ContinuousLinearMap.ext
  intro v
  have hv := congrArg (fun A : (Fin k → ℝ) →L[ℝ] H => A v) h
  change inTangentCoordinates 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) id
    (Subtype.val : Z → H) (mfderiv 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) Subtype.val) p x v =
    (mfderiv 𝓘(ℝ, H) 𝓘(ℝ, H) (extChartAt 𝓘(ℝ, H) (p : H)) (x : H))
      ((mfderiv 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) (Subtype.val : Z → H) x)
        (mfderivWithin 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, Fin k → ℝ)
          (extChartAt 𝓘(ℝ, Fin k → ℝ) p).symm (range 𝓘(ℝ, Fin k → ℝ))
          (extChartAt 𝓘(ℝ, Fin k → ℝ) p x) v)) at hv
  rw [hc] at hv
  exact hv.trans (congrArg (mfderiv 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) (Subtype.val : Z → H) x)
    (DifferentialGeometry.Topology.Manifold.preferredChartTangentEquiv_symm_apply
      𝓘(ℝ, Fin k → ℝ) p x hx v).symm)


def actualEmbeddingTangentCoordinates (k : ℕ) (Z : Set H)
    [ChartedSpace (Fin k → ℝ) Z] [IsManifold 𝓘(ℝ, Fin k → ℝ) ∞ Z]
    (p x : Z) : EuclideanSpace ℝ (Fin k) →L[ℝ] H :=
  (inTangentCoordinates 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) id (Subtype.val : Z → H)
    (mfderiv 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) Subtype.val) p x).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _i : Fin k => ℝ)).toContinuousLinearMap

omit [FiniteDimensional ℝ H] in
theorem actualEmbeddingTangentCoordinates_range (p x : Z)
    (hx : x ∈ (chartAt (Fin k → ℝ) p).source) :
    LinearMap.range (actualEmbeddingTangentCoordinates k Z p x).toLinearMap =
      actualZeroSetTangentSpace k Z x := by
  let D : (Fin k → ℝ) →L[ℝ] H :=
    mfderiv 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) (Subtype.val : Z → H) x
  let e := DifferentialGeometry.Topology.Manifold.preferredChartTangentEquiv
    𝓘(ℝ, Fin k → ℝ) p x hx
  let l : EuclideanSpace ℝ (Fin k) ≃L[ℝ] (Fin k → ℝ) :=
    PiLp.continuousLinearEquiv 2 ℝ (fun _i : Fin k => ℝ)
  have he : Function.Surjective
      ((e.symm : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ)).comp l.toContinuousLinearMap) := by
    change Function.Surjective (fun v => e.symm (l v))
    exact e.symm.surjective.comp l.surjective
  unfold actualEmbeddingTangentCoordinates
  rw [actualEmbeddingTangentCoordinate_eq p x hx]
  change LinearMap.range (D.toLinearMap.comp (e.symm.toLinearMap.comp l.toLinearMap)) = _
  exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr he)

omit [FiniteDimensional ℝ H] in
theorem actualEmbeddingTangentCoordinates_injective
    (hemb : IsSmoothEmbedding 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) ∞ (Subtype.val : Z → H))
    (p x : Z) (hx : x ∈ (chartAt (Fin k → ℝ) p).source) :
    Function.Injective (actualEmbeddingTangentCoordinates k Z p x) := by
  unfold actualEmbeddingTangentCoordinates
  rw [actualEmbeddingTangentCoordinate_eq p x hx]
  exact ((hemb.isImmersion.mfderiv_injective (by simp) x).comp
    (DifferentialGeometry.Topology.Manifold.preferredChartTangentEquiv
      𝓘(ℝ, Fin k → ℝ) p x hx).symm.injective).comp
        (PiLp.continuousLinearEquiv 2 ℝ (fun _i : Fin k => ℝ)).injective

theorem actualNormalProjector_eq_normalGram
    (hemb : IsSmoothEmbedding 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) ∞ (Subtype.val : Z → H))
    (p x : Z) (hx : x ∈ (chartAt (Fin k → ℝ) p).source) :
    actualZeroSetNormalProjector k Z x =
      normalGramProjector (actualEmbeddingTangentCoordinates k Z p x) := by
  rw [normalGramProjector_eq_starProjection _
    (actualEmbeddingTangentCoordinates_injective hemb p x hx)]
  simp only [actualEmbeddingTangentCoordinates_range p x hx, actualZeroSetNormalProjector]

theorem contMDiff_actualZeroSetNormalProjector
    (hemb : IsSmoothEmbedding 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) ∞ (Subtype.val : Z → H)) :
    ContMDiff 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H →L[ℝ] H) ∞
      (actualZeroSetNormalProjector k Z) := by
  intro p
  let l : EuclideanSpace ℝ (Fin k) →L[ℝ] (Fin k → ℝ) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _i : Fin k => ℝ)).toContinuousLinearMap
  have hc : ContMDiffAt 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, (Fin k → ℝ) →L[ℝ] H) ∞
      (inTangentCoordinates 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) id (Subtype.val : Z → H)
        (mfderiv 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) Subtype.val) p) p :=
    hemb.contMDiff.contMDiffAt.mfderiv_const (m := ∞) (by simp)
  have hl : ContMDiffAt 𝓘(ℝ, Fin k → ℝ)
      𝓘(ℝ, EuclideanSpace ℝ (Fin k) →L[ℝ] (Fin k → ℝ)) ∞ (fun _x : Z => l) p :=
    contMDiffAt_const
  have ha : ContMDiffAt 𝓘(ℝ, Fin k → ℝ)
      𝓘(ℝ, EuclideanSpace ℝ (Fin k) →L[ℝ] H) ∞
      (actualEmbeddingTangentCoordinates k Z p) p :=
    hc.clm_comp hl
  have hi := actualEmbeddingTangentCoordinates_injective hemb p p
    (mem_chart_source (Fin k → ℝ) p)
  have hg : ContDiffAt ℝ ∞
      (normalGramProjector : (EuclideanSpace ℝ (Fin k) →L[ℝ] H) → H →L[ℝ] H)
      (actualEmbeddingTangentCoordinates k Z p p) :=
    contDiffAt_normalGramProjector contDiffAt_id hi
  apply (hg.contMDiffAt.comp p ha).congr_of_eventuallyEq
  filter_upwards [(chartAt (Fin k → ℝ) p).open_source.mem_nhds
    (mem_chart_source (Fin k → ℝ) p)] with x hx
  exact actualNormalProjector_eq_normalGram hemb p x hx

end GC.MetricGeometry
