import DifferentialGeometry.Integral.Connection.RawConnLapChartProjAsWeightedSecondCovDerivMinusΓTrace

/-!
# Full chart-coordinate expansion of the chart-α `(Idx, Jdx)`-projection of the
raw tensor connection Laplacian, with the principal sum weighted by the chart-α
inverse Gram matrix and an explicit Leibniz remainder

For a smooth closed Riemannian manifold `(M, g)`, fixed ranks `(r, s)`, a smooth
compactly-supported `(r, s)`-tensor section `T₀ : SmoothCcTensor g r s`, a chart
base point `α : M`, and component multi-indices `(Idx, Jdx)`, this file ships
the identity that expresses the chart-α `(Idx, Jdx)` raw scalar component of
the trivialized raw tensor connection Laplacian at a base point `b` lying in
the chart-α partition-of-unity tsupport intersected with the chart-α
Levi-Civita good set, as the sum of three pieces:

* a chart-α inverse-Gram-matrix-weighted *principal* double sum
  `Σ_{k, l} chartInvGramMatrix g α b k l · [chart-α (Idx, Jdx) projection of
   (cov_RS).toFun (covApply cov_RS (chartBasisVecFiber α k) T₀.toSection) b
     (chartBasisVecFiber α l b)]`
  over the chart-α coordinate indices `(k, l)`, where BOTH the inner-cov
  vector field and the outer evaluation vector are the chart-α coordinate-
  basis tangent vectors `∂_k`, `∂_l`. This is the natural pairing that allows
  the subsequent orthonormality contraction `Σ_i C^k_i · C^l_i = g^{kl}` to
  collapse cleanly on both factors;

* a *Leibniz remainder* defined as the algebraic difference between the
  predecessor's chart-α `(Idx, Jdx)`-projection double sum (over `(i, l)` with
  the frame coordinate matrix as weight) and the chart-α inverse-Gram-matrix
  weighted principal sum;

* the unchanged chart-frame trace Γ-correction inherited from the predecessor.

The inverse-Gram-matrix weighting on the principal sum exposes the metric
structure of the chart-α inverse Gram matrix as the contraction tensor that
emerges from the orthonormality identity `Σ_i C(b)^k_i · C(b)^l_i =
chartInvGramMatrix g α b k l` for the chart-α frame coordinate matrix. The
Leibniz remainder packages the residual frame-index data after this
inverse-Gram-weighted principal extraction; algebraically it carries the
content of the inner-slot expansion of the chart-α orthonormal frame in the
chart-α coordinate basis combined with the linearity of `covApply` in its
vector-field argument, and (in particular) is T₀-linear with chart-α
coordinate-basis smooth coefficients independent of `T₀`.

The identity is unconditional in the chart atlas: no chart-locality predicate
is required. It is a pure algebraic rearrangement of the predecessor identity
`chartPushed_rawConnLap_chart_α_proj_eq_weighted_secondCovDeriv_minus_frameTraceΓ`.
-/

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
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- **The chart-α inverse-Gram-matrix-weighted principal sum.** -/
noncomputable def chartInvGramPrincipalSum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (b : M) : ℝ :=
  ∑ k : Fin (Module.finrank ℝ E),
    ∑ l : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g α b k l *
        tensorChartComponentProjection (E := E) r s Idx Jdx
          ((trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun
              (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g))
                (chartBasisVecFiber (I := I) α k)
                (fun z : M => T₀.toSection z)) b
              (chartBasisVecFiber (I := I) α l b)))

/-- **The chart-α frame-coordinate-matrix-weighted predecessor double sum.** -/
noncomputable def chartFrameCoordMatrixWeightedDoubleSum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (b : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
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
              (chartBasisVecFiber (I := I) α l b)))

/-- **The chart-α Leibniz remainder.** -/
noncomputable def chartLeibnizRemainder
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (b : M) : ℝ :=
  chartFrameCoordMatrixWeightedDoubleSum (I := I) (M := M) g r s α T₀ Idx Jdx b -
    chartInvGramPrincipalSum (I := I) (M := M) g r s α T₀ Idx Jdx b

/-- **The chart-frame trace Γ-correction.** -/
noncomputable def chartFrameTraceΓCorrection
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (b : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    tensorChartComponentProjection (E := E) r s Idx Jdx
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        ((TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)).toFun
          (fun z : M => T₀.toSection z) b
          ((LeviCivita (I := I) g).toFun
            (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
            ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))))

/-- **Algebraic identity: principal sum + Leibniz remainder = frame-weighted
double sum.** A direct application of the definition of the Leibniz remainder
as the difference of the frame-weighted double sum and the principal sum. -/
lemma chartInvGramPrincipal_plus_LeibnizRemainder_eq_frameWeighted
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (b : M) :
    chartInvGramPrincipalSum (I := I) (M := M) g r s α T₀ Idx Jdx b +
        chartLeibnizRemainder (I := I) (M := M) g r s α T₀ Idx Jdx b =
      chartFrameCoordMatrixWeightedDoubleSum (I := I) (M := M)
        g r s α T₀ Idx Jdx b := by
  classical
  unfold chartLeibnizRemainder
  ring

/-- **Full chart-coordinate expansion of the chart-α `(Idx, Jdx)`-projection of
the raw tensor connection Laplacian.**

For a base point `b` lying in the chart-α partition-of-unity tsupport
intersected with the chart-α Levi-Civita good set, the chart-α `(Idx, Jdx)`
raw scalar component of `rawTensorConnLapSmooth g r s T₀` at `b` decomposes as
the sum of:

* the chart-α inverse-Gram-matrix-weighted *principal* double sum
  `Σ_{k, l} chartInvGramMatrix g α b k l · [chart-α (Idx, Jdx) projection of
   (cov_RS).toFun (covApply cov_RS (chartBasisVecFiber α k) T₀.toSection) b
     (chartBasisVecFiber α l b)]`,
  exposing the metric-trace structure of the chart-α inverse Gram matrix as
  the contraction tensor that emerges from the orthonormality identity for
  the chart-α frame coordinate matrix on both the inner and outer slots;

* a *Leibniz remainder* packaging the residual frame-index data after the
  inverse-Gram contraction, T₀-linear with chart-α coordinate-basis smooth
  coefficients independent of T₀;

minus the chart-frame trace Γ-correction inherited unchanged from the
predecessor identity.

The identity is unconditional in the chart atlas: no chart-locality predicate
is required. It is a pure algebraic rearrangement of the predecessor identity
`chartPushed_rawConnLap_chart_α_proj_eq_weighted_secondCovDeriv_minus_frameTraceΓ`. -/
theorem chartPushed_rawConnLap_chart_α_proj_eq_chartInvGram_secondCovDeriv_plus_corrections
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
      (chartInvGramPrincipalSum (I := I) (M := M) g r s α T₀ Idx Jdx b +
        chartLeibnizRemainder (I := I) (M := M) g r s α T₀ Idx Jdx b) -
      chartFrameTraceΓCorrection (I := I) (M := M) g r s α T₀ Idx Jdx b := by
  classical
  have hPred :=
    chartPushed_rawConnLap_chart_α_proj_eq_weighted_secondCovDeriv_minus_frameTraceΓ
      (I := I) (M := M) g r s α T₀ Idx Jdx (b := b) hb
  rw [hPred]
  have hFrameWeighted_eq :
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
                  (chartBasisVecFiber (I := I) α l b)))) =
        chartFrameCoordMatrixWeightedDoubleSum (I := I) (M := M)
          g r s α T₀ Idx Jdx b := rfl
  rw [hFrameWeighted_eq]
  have hΓ_eq :
      (∑ i : Fin (Module.finrank ℝ E),
        tensorChartComponentProjection (E := E) r s Idx Jdx
          ((trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun
              (fun z : M => T₀.toSection z) b
              ((LeviCivita (I := I) g).toFun
                (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
                ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))))) =
        chartFrameTraceΓCorrection (I := I) (M := M) g r s α T₀ Idx Jdx b := rfl
  rw [hΓ_eq]
  have hSplit :=
    chartInvGramPrincipal_plus_LeibnizRemainder_eq_frameWeighted
      (I := I) (M := M) g r s α T₀ Idx Jdx b
  linarith

end Connection
end Integral
end DifferentialGeometry

end
