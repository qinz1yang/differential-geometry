import DifferentialGeometry.Integral.Connection.RawConnLapChartComponentFrameTrace
import DifferentialGeometry.Integral.Connection.ChartFrameNormGlobalSmoothCoordBasisExpansion
import DifferentialGeometry.Integral.Connection.RawTensorConnLapIterL2WtwokTwoBound

/-!
# Chart-α `(Idx, Jdx)`-projection of the raw tensor connection Laplacian as a
chart-coordinate-weighted bundle second covariant derivative double sum minus a
chart-frame trace Γ-correction

For a smooth closed Riemannian manifold `(M, g)`, fixed ranks `(r, s)`, a smooth
compactly-supported `(r, s)`-tensor section `T₀ : SmoothCcTensor g r s`, a chart
base point `α : M`, and component multi-indices `(Idx, Jdx)`, this file ships
the identity that expresses the chart-α `(Idx, Jdx)` raw scalar component of
the trivialized raw tensor connection Laplacian at a base point `b` lying in
the chart-α partition-of-unity tsupport intersected with the chart-α
Levi-Civita good set, as a finite double sum

```
Σ_i Σ_l C(b)^l_i ·
   [chart-α (Idx, Jdx) projection of
      (cov_RS).toFun (covApply cov_RS B_i T₀.toSection) b
        (chartBasisVecFiber α l b)]
```

where `B_i = chartFrameNormGlobalSmooth g α i` is the chart-α globally smooth
orthonormal frame and `C(b)^l_i =
chartFrameNormGlobalSmoothCoordMatrix g α i l b` is its coordinate matrix in
the chart-α coordinate basis, minus the chart-frame trace Γ-correction

```
Σ_i [chart-α (Idx, Jdx) projection of
       (cov_RS).toFun T₀.toSection b ((LC g) B_i b (B_i b))]
```

(unchanged from the underlying frame-trace identity).

The identity is unconditional in the chart atlas: no chart-locality predicate
is required. It is the natural composition of:

* the chart-α `(Idx, Jdx)`-projection of the chart-frame trace identity for
  the raw tensor connection Laplacian
  (`tensorChartComponentRaw_rawTensorConnLap_eq_chart_frame_trace_sum`); and
* the coordinate-basis expansion of the chart-α globally smooth orthonormal
  frame
  (`chartFrameNormGlobalSmooth_eq_coordMatrix_sum`), applied in the *outer*
  tangent-vector slot of the first piece of the chart-frame trace summand.

The distribution through the chart-α `(Idx, Jdx)`-projection is by linearity
of the trivialization continuous-linear-map composed with the dual coordinate
projection; the distribution through the outer tangent-vector slot of the
bundle covariant derivative is by `ContinuousLinearMap.map_smul` /
`ContinuousLinearMap.map_sum` of the bundle covariant derivative's continuous
linear action on `TangentSpace I b`. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- **Coordinate-basis expansion of the outer tangent-vector slot of one
chart-frame trace summand for the raw tensor connection Laplacian.**

For a base point `b` in the chart-α Levi-Civita good set and an index
`i : Fin n`, the value of the bundle covariant derivative
`cov_RS (∇_{B_i} T₀) b (B_i b)` decomposes, via the chart-α coordinate-basis
expansion of `B_i(b)` and the continuous linearity of
`cov_RS (∇_{B_i} T₀) b` on `TangentSpace I b`, as the finite sum

```
Σ_l C(b)^l_i · cov_RS (∇_{B_i} T₀) b (chartBasisVecFiber α l b)
```

over the chart-α coordinate-basis index `l`. -/
private lemma covRS_covApply_B_i_T₀_at_B_i_eq_coord_sum_outer
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (i : Fin (Module.finrank ℝ E))
    {b : M}
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).toFun
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g))
          (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
          (fun z : M => T₀.toSection z)) b
        ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b) =
      ∑ l : Fin (Module.finrank ℝ E),
        chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b •
          (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)).toFun
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
              (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
              (fun z : M => T₀.toSection z)) b
            (chartBasisVecFiber (I := I) α l b) := by
  classical
  have hExpand :
      (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b =
        ∑ l : Fin (Module.finrank ℝ E),
          chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b •
            chartBasisVecFiber (I := I) α l b := by
    have h := chartFrameNormGlobalSmooth_eq_coordMatrix_sum
      (I := I) (M := M) g α i (b := b) hb
    have hcoerce : ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i :
          Π b : M, TangentSpace I b) b)
        = (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b := rfl
    rw [hcoerce] at h
    exact h
  rw [hExpand]
  set Lcov : TangentSpace I b →L[ℝ] TensorRSSpace r s I b :=
    (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).toFun
      (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g))
        (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
        (fun z : M => T₀.toSection z)) b
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [Lcov.map_smul]

/-- **Chart-α `(Idx, Jdx)`-projection of one outer-coordinate-basis-expanded
chart-frame trace summand.**

For a base point `b` in the chart-α Levi-Civita good set and an index
`i : Fin n`, applying the continuous linear functional
`tensorChartComponentProjection r s Idx Jdx ∘ (triv α).clmAt b` to both sides
of the coordinate-basis expansion of `cov_RS (∇_{B_i} T₀) b (B_i b)` yields
the chart-α `(Idx, Jdx)` scalar of the LHS as a finite sum over `l` of
`C(b)^l_i ·` (chart-α `(Idx, Jdx)` scalar of `cov_RS (∇_{B_i} T₀) b (∂_l b)`).
-/
private lemma chart_α_proj_covRS_covApply_B_i_T₀_at_B_i_eq_coord_sum_outer
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (i : Fin (Module.finrank ℝ E))
    {b : M}
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    tensorChartComponentProjection (E := E) r s Idx Jdx
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          ((TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
              (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g))
                (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                (fun z : M => T₀.toSection z)) b
              ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))) =
      ∑ l : Fin (Module.finrank ℝ E),
        chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b *
          tensorChartComponentProjection (E := E) r s Idx Jdx
            ((trivializationAt (TensorRSModel r s ℝ E)
                (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
              ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g)).toFun
                  (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                    (LeviCivita (I := I) g))
                    (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                    (fun z : M => T₀.toSection z)) b
                  (chartBasisVecFiber (I := I) α l b))) := by
  classical
  rw [covRS_covApply_B_i_T₀_at_B_i_eq_coord_sum_outer
      (I := I) (M := M) g r s α T₀ i (b := b) hb]
  set L : TensorRSSpace r s I b →L[ℝ] ℝ :=
    (tensorChartComponentProjection (E := E) r s Idx Jdx).comp
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b)
    with hL_def
  have hApply :
      L (∑ l : Fin (Module.finrank ℝ E),
            chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b •
              (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun
                (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g))
                  (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                  (fun z : M => T₀.toSection z)) b
                (chartBasisVecFiber (I := I) α l b)) =
        ∑ l : Fin (Module.finrank ℝ E),
          chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b •
            L ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun
                (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g))
                  (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                  (fun z : M => T₀.toSection z)) b
                (chartBasisVecFiber (I := I) α l b)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [L.map_smul]
  simp only [hL_def, ContinuousLinearMap.comp_apply, smul_eq_mul] at hApply
  exact hApply

/-- **Chart-α `(Idx, Jdx)` raw component of `rawTensorConnLapSmooth T₀` as a
chart-coordinate-weighted bundle second covariant derivative double sum minus
a chart-frame trace Γ-correction.**

For a base point `b` lying in the chart-α partition-of-unity tsupport
intersected with the chart-α Levi-Civita good set, the chart-α `(Idx, Jdx)`
raw scalar component of `rawTensorConnLapSmooth g r s T₀` at `b` decomposes as
a double finite sum over `(i, l)` of `C(b)^l_i ·` (chart-α `(Idx, Jdx)`
projection of `cov_RS (∇_{B_i} T₀) b (∂_l b)`), minus a single finite sum over
`i` of (chart-α `(Idx, Jdx)` projection of `cov_RS T₀ b ((LC g) B_i b (B_i b))`).

The coefficient `C(b)^l_i = chartFrameNormGlobalSmoothCoordMatrix g α i l b` is
the chart-α coordinate matrix of the chart-α globally smooth orthonormal frame
`B_i = chartFrameNormGlobalSmooth g α i`.

The identity is unconditional in the chart atlas: no chart-locality predicate
is required. It is the natural combination of the chart-α `(Idx, Jdx)`-projection
of the chart-frame trace identity for the raw tensor connection Laplacian and
the coordinate-basis expansion of the chart-α globally smooth orthonormal
frame, applied in the outer tangent-vector slot of the first piece of each
chart-frame trace summand. -/
theorem chartPushed_rawConnLap_chart_α_proj_eq_weighted_secondCovDeriv_minus_frameTraceΓ
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M}
    (hb : b ∈ tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
      chartLeviCivitaGoodSet (I := I) α) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (rawTensorConnLapSmooth (I := I) g r s T₀) α Idx Jdx b =
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b *
            tensorChartComponentProjection (E := E) r s Idx Jdx
              ((trivializationAt (TensorRSModel r s ℝ E)
                  (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
                ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                    (LeviCivita (I := I) g)).toFun
                  (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                    (LeviCivita (I := I) g))
                    (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                    (fun z : M => T₀.toSection z)) b
                  (chartBasisVecFiber (I := I) α l b)))) -
      (∑ i : Fin (Module.finrank ℝ E),
        tensorChartComponentProjection (E := E) r s Idx Jdx
          ((trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun
              (fun z : M => T₀.toSection z) b
              ((LeviCivita (I := I) g).toFun
                (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
                ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))))) := by
  classical
  have hLHS_eq :
      tensorChartComponentRaw (I := I) (M := M) g r s
          (rawTensorConnLapSmooth (I := I) g r s T₀) α Idx Jdx b =
        tensorChartComponentProjection (E := E) r s Idx Jdx
          ((trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (rawTensorConnLap (I := I) g r s
              (fun z : M => T₀.toSection z) b)) := by
    unfold tensorChartComponentRaw tensorTrivProj
    rw [rawTensorConnLapSmooth_toSection_apply (I := I) g r s T₀ b]
  rw [hLHS_eq]
  have hStep2 :=
    tensorChartComponentRaw_rawTensorConnLap_eq_chart_frame_trace_sum
      (I := I) (M := M) g r s α T₀ Idx Jdx (b := b) hb
  rw [hStep2]
  have hperI : ∀ i : Fin (Module.finrank ℝ E),
      tensorChartComponentProjection (E := E) r s Idx Jdx
          ((trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g)).toFun
                (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g))
                  (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                  (fun z : M => T₀.toSection z)) b
                ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b) -
              (TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g)).toFun
                (fun z : M => T₀.toSection z) b
                ((LeviCivita (I := I) g).toFun
                  (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
                  ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)))) =
        (∑ l : Fin (Module.finrank ℝ E),
            chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b *
              tensorChartComponentProjection (E := E) r s Idx Jdx
                ((trivializationAt (TensorRSModel r s ℝ E)
                    (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
                  ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                      (LeviCivita (I := I) g)).toFun
                    (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                      (LeviCivita (I := I) g))
                      (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                      (fun z : M => T₀.toSection z)) b
                    (chartBasisVecFiber (I := I) α l b)))) -
          tensorChartComponentProjection (E := E) r s Idx Jdx
            ((trivializationAt (TensorRSModel r s ℝ E)
                (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
              ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g)).toFun
                (fun z : M => T₀.toSection z) b
                ((LeviCivita (I := I) g).toFun
                  (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
                  ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)))) := by
    intro i
    rw [map_sub, map_sub]
    rw [chart_α_proj_covRS_covApply_B_i_T₀_at_B_i_eq_coord_sum_outer
        (I := I) (M := M) g r s α T₀ Idx Jdx i (b := b) hb.2]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
        tensorChartComponentProjection (E := E) r s Idx Jdx
          ((trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g)).toFun
                (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g))
                  (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                  (fun z : M => T₀.toSection z)) b
                ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b) -
              (TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g)).toFun
                (fun z : M => T₀.toSection z) b
                ((LeviCivita (I := I) g).toFun
                  (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
                  ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))))) =
      ∑ i : Fin (Module.finrank ℝ E),
        ((∑ l : Fin (Module.finrank ℝ E),
            chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b *
              tensorChartComponentProjection (E := E) r s Idx Jdx
                ((trivializationAt (TensorRSModel r s ℝ E)
                    (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
                  ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                      (LeviCivita (I := I) g)).toFun
                    (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                      (LeviCivita (I := I) g))
                      (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                      (fun z : M => T₀.toSection z)) b
                    (chartBasisVecFiber (I := I) α l b)))) -
          tensorChartComponentProjection (E := E) r s Idx Jdx
            ((trivializationAt (TensorRSModel r s ℝ E)
                (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
              ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g)).toFun
                (fun z : M => T₀.toSection z) b
                ((LeviCivita (I := I) g).toFun
                  (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
                  ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))))) from
    Finset.sum_congr rfl (fun i _ => hperI i)]
  rw [Finset.sum_sub_distrib]

end Connection
end Integral
end DifferentialGeometry

end
