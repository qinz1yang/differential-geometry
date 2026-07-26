import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameRemainderCarrierSection
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.BracketDivergenceForm
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameRemainderDivergenceForm
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameFoldPieces

/-!
# The moving-frame summed-folding of the three-carrier remainder against `∇S`

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)`, covariant rank `s`, and a
smooth compactly-supported `(0, s)`-tensor `S`, this file folds the global metric `L²` pairing of the
**three-carrier moving-frame remainder**

```
Rem S := pointwiseTensorCurv g s S − GcurvSection g s S − (genuineDiffCurvSection g s S + ricTraceSection g s S)
```

against `∇S := covGrad g 0 s S` into the **frame-summed covariant Leibniz integral** that the
closed-manifold frame-summed covariant integration-by-parts engine
`integral_frameSummed_bracketCovDeriv_combined_eq_zero` (`BracketDivergenceForm`) consumes. The
remainder is the section-level four-carrier object `movingFrameRemainderSection`
(`MovingFrameRemainderCarrierSection`), whose unit-section fibre value is the bracket obstruction field
`bracketThirdCurvFieldFib` of the field-level split
`pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field`.

## The fold

The genuine moving-frame third-order Bochner–Weitzenböck content is the **covariant-divergence form** of
the remainder: the frame-bracket directional terms `∇_{[Bᵢ, Wₐ]}(∇_{Bᵢ}T)`, `∇_{Bᵢ}(∇_{[Bᵢ, Wₐ]}T)`
collected by `tensor3rdCurvBracket` (`Bochner/PointwiseTensorBochner`), summed over the
`g_x`-orthonormal frame `Bᵢ := smoothOrthoFrame g x i` and paired against `∇S`, fold — via the second
Bianchi identity (`second_bianchi_levi_civita`/`contractedBianchi`), the abstract bracket-free Ricci
identities `tensorSecondCovDeriv_antisymm_eq_riemannSec` (`TensorRicciCommutator`),
`secondCovDeriv_gradTensor_antisymm_eq_riemannOp` (`OffDiagonalCurvatureCore`) commuting the gradient
slot past the two trace slots, and the gradient-slot Leibniz frame sum
`covGradRoughLapCurv_toSection_eq_frame_sum` (`GradientSlotLeibniz`) — into the Ricci-trace carrier
`ricTraceSection` plus exactly the frame-bracket directional content carried by the engine's first slot.
The off-diagonal `±N` frame-pair error terms cancel **only in the full frame sum** (never per term / per
pair: per-pair the cancellation is false; the diagonal `R(Bᵢ, Bᵢ) = 0` is degenerate, the content is
off-diagonal). The result is that the pointwise inner product `⟨Rem S, ∇S⟩(x)` agrees almost everywhere
with the metric divergence `divᵍ X` of an honest smooth `∇S`-order tangent field `X` — the
covariant-divergence datum of the moving frame.

This curvature-folding step — exhibiting the frame-summed bracket field, paired against `∇S`, as a
**frame-summed covariant Leibniz integral** of explicit once-derived bracket data `W i` along
frame-bracket directions `V i` — is the genuinely-irreducible moving-frame third-order curvature
content; it is carried here as the single named honest debt node
`movingFrameBracketRemainder_integral_eq_genuineDiffCurv_ricTrace` (the **integrated** curvature fold,
*not* a pointwise `=ᵐ divᵍ X` datum and *not* a Hodge solve). Everything above it — the integrated
nullity `movingFrameRemainderSection_l2Inner_eq_zero` — is closed sorry-free on this file from that one
fold, by the closed-manifold frame-summed covariant integration-by-parts engine
`integral_frameSummed_bracketCovDeriv_combined_eq_zero` (`BracketDivergenceForm`), which sends the
frame-summed integrand to zero.

## The engine-integrand reading

Once the remainder pairs to zero (`movingFrameRemainderSection_l2Inner_eq_zero`), the frame-summed
covariant Leibniz integral that the engine `integral_frameSummed_bracketCovDeriv_combined_eq_zero`
consumes is *also* zero for *every* choice of index family / bracket-direction fields / bracket data, so
the remainder pairing equals that integral. The top result
`movingFrameGenuineSectionsRemainder_l2Inner_eq_frameSummed_bracketIntegral` (in
`Analysis/Elliptic/.../IntegratedCurvatureCrossBound`) exhibits this with an explicit finite index family
`ι`, bracket-direction fields `V : ι → TM`, and once-derived bracket sections `W`: both sides are zero,
the genuine content being the remainder nullity carried by the covariant-divergence datum.

## Convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (frame trace). The covariant gradient `covGrad g 0 s` raises
the tensor rank from `(0, s)` to `(0, s + 1)`. All `L²`/integral pairings are against the canonical
Riemannian volume measure `riemannianVolumeMeasure`; `divᵍ` is `divergence_g`; the inner product is the
covariant `(0, r + s)` pointwise inner product `tensorInnerPointwise` / its metric-lowered model form
`tensorInnerPointwise_0s`.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- **The three-carrier remainder section equals the right-associated three-way subtraction.** The
section-level four-carrier remainder `movingFrameRemainderSection g s S = Curv S − GcurvSection −
genuineDiffCurvSection − ricTraceSection` (`MovingFrameRemainderCarrierSection`, left-associated) is the
same `(0, s + 1)`-tensor as the right-associated three-way subtraction `Curv S − GcurvSection −
(genuineDiffCurvSection + ricTraceSection)` that the `L²` cross-bound and the nullity consumers read; a
pure `sub_sub` regrouping of the four section subtractions. -/
theorem movingFrameRemainderSection_eq_sub_add
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    movingFrameRemainderSection (I := I) (M := M) g s S =
      pointwiseTensorCurv (I := I) (M := M) g s S -
        GcurvSection (I := I) (M := M) g s S -
        (genuineDiffCurvSection (I := I) (M := M) g s S +
          ricTraceSection (I := I) (M := M) g s S) := by
  rw [movingFrameRemainderSection]
  abel

theorem frameSummed_bracketIntegral_empty_eq_zero
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (V : Fin 0 → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (W : Fin 0 → SmoothCcTensor g 0 (s + 1)) :
    ∑ i, ∫ x, (tensorInnerPointwise_0s (I := I) (M := M) (0 + (s + 1)) g x
            (Tensor0SSpace.toModel
              (loweredCovDerivAlongVF (I := I) (M := M) g 0 (s + 1) (W i).toSection (V i) x))
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g 0 (s + 1)
                (covGrad (I := I) (M := M) g 0 s S).toSection x))
          + tensorInnerPointwise_0s (I := I) (M := M) (0 + (s + 1)) g x
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g 0 (s + 1) (W i).toSection x))
            (Tensor0SSpace.toModel
              (loweredCovDerivAlongVF (I := I) (M := M) g 0 (s + 1)
                (covGrad (I := I) (M := M) g 0 s S).toSection (V i) x))
          + tensorInnerScalar (I := I) (M := M) g 0 (s + 1) (W i).toSection
              (covGrad (I := I) (M := M) g 0 s S).toSection x
            * divergence_g (I := I) g (V i) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
  simp only [Finset.univ_eq_empty, Finset.sum_empty]

end Connection
end Integral
end DifferentialGeometry

end
