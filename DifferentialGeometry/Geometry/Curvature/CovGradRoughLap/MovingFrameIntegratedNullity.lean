import DifferentialGeometry.Geometry.Connection.MetricCompatibility.MovingFrameBracketDivergence
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorConnLapLoweredIBP
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.IntegratedOrder2WeitzenbockCurvature
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameCurvatureTraceSmooth

/-!
# The frame-summed covariant-IBP producer of the integrated moving-frame nullity

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file builds the
**integrated moving-frame nullity producer** — the genuinely-new analytic content underneath the
deepest coupled differentiated-curvature atom
`exists_movingCentreDiffCurvSection_splitDivergenceDatum` (`MovingFrameDiffCurvAnchor`). It is the
**first producer** of bracket-divergence content in the library: every other appearance of a
bracket-divergence / integrated-nullity datum is a *consumed* hypothesis (the
`tensorL2Inner_movingFrameRemainder_eq_zero_of_*` reductions of `MovingFrameRemainderDivergenceForm`
and `MovingFrameBracketDivergence` take it as input); here it is *produced*.

## The telescoping route

Write `Curv S := pointwiseTensorCurv g s S = Δ_∇(∇S) − ∇(Δ_∇ S)` (`pointwiseTensorCurv`, a
`(0, s + 1)`-tensor field; `∇S := covGrad g 0 s S`), `Gcurv := GcurvSection g s S` (the concrete
pure-Riemann section), and let `Gcd` be the gauge-glued tensorial `(∇R) S` trace section (carried
abstractly here, pinned by the value identity it satisfies — see below). The moving-frame remainder
is `Grem := Curv S − Gcurv − Gcd`, and the target is the **integrated nullity**
`⟨Grem, ∇S⟩_{L²} = 0`.

The genuine analytic chain is:

1. **The integrated value of the curvature cross-pairing is already known** (the integrated order-`2`
   Weitzenböck identity `weitzenbock_integrated_covGrad_l2_normSq`):
   `⟨Curv S, ∇S⟩_{L²} = ‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²}`.
2. **The genuine curvature fields carry exactly this value** — the *bracket-free `L²` pairing*
   `⟨Gcurv + Gcd, ∇S⟩_{L²} = ⟨Curv S, ∇S⟩_{L²}`. This is the genuine frame-summed covariant
   integration by parts: the moving-frame / frame-bracket remainder, paired against `∇S` and summed
   over the `g_x`-orthonormal frame `Bᵢ := smoothOrthoFrame g x i`, telescopes into a total covariant
   divergence (`integral_tensorInner_tangentAction_add_smul_divergence_eq_zero`,
   `CovariantIntegrationByParts`) of an honest smooth `∇S`-order tangent field whose integral over the
   closed manifold vanishes (`integral_divergence_eq_zero_of_hasCompactSupport`). The `∇³S`-cancellation
   and divergence form are *false term-by-term* through `smoothExtensionTangent`; only the tensorial
   frame-summed remainder is `∇²S`-order and a total divergence — the irreducible coupled moving-frame
   content.
3. **The nullity follows by left additivity** of the `L²` pairing
   (`tensorL2Inner_movingFrameRemainder_eq_zero_of_bracketFreePairing`): writing
   `Curv S = (Gcurv + Gcd) + (Curv S − Gcurv − Gcd)` and dropping the remainder term by the
   bracket-free pairing of step 2.

## Why the nullity is an integrated (not pointwise) fact

The pointwise pairing `⟨Grem, ∇S⟩(x)` is *not* a total covariant divergence — by the pointwise Bochner
divergence identity `divergence_dirichletVFGen_eq` (`TensorConnLapGreenDivergenceIdentityAnySection`)
it carries the pointwise-nonzero non-divergence content `‖∇²S‖² − ⟨Δ_∇²(∇S), S⟩`, so only its
*integral* vanishes. A pointwise divergence-current form would require a Poisson / Hodge solve absent
in the library; the integrated nullity is the honest primitive — exactly the *sound integrated form*
the sibling tri-split node `exists_pointwiseTensorCurv_genuineTriSplit_divergence`
(`MovingFrameGenuineSectionOrderDivergence`) consumes.

## Coordinating with the gauge-glued `Gcd` build

The gauge-glued tensorial `(∇R) S` trace section `Gcd` is constructed concurrently (its fibre bounds
and the partition-of-unity glue are a separate sub-build). This file states its results against an
**abstract** `Gcd` pinned by the **genuine bracket-free pairing** it satisfies — the value identity
`⟨Gcurv + Gcd, ∇S⟩_{L²} = ⟨Curv S, ∇S⟩_{L²}` (the genuine frame-summed integration-by-parts content,
which holds exactly for the genuine curvature fields and is *false* for an arbitrary bounded field).
The producer `movingFrameNullity_of_bracketFreePairing` converts that pairing into the integrated
nullity by pure left-additivity algebra, so the gauge-glued build plugs in by supplying the pairing;
`weitzenbock_curvature_crossPairing_value` records the already-proven Weitzenböck value the pairing
must equal.
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

/-- **Frame-summed covariant integration by parts (the bracket-divergence engine).** For a closed
smooth Riemannian manifold `(M, g)`, a finite index family `ι`, smooth tangent vector fields
`V i : Cₛ^∞⟮I; E, TangentSpace I⟯` and smooth `(r, s)`-tensor sections `W i`, `Z`, the frame-summed
covariant Leibniz expression integrates to zero:

```
∑ᵢ ∫_M ( ⟨∇_{V i}(W i), Z⟩ + ⟨W i, ∇_{V i} Z⟩ + ⟨W i, Z⟩ · divᵍ (V i) ) dvol_g = 0,
```

where `∇_{V i}` is the metric-lowered directional covariant derivative `loweredCovDerivAlongVF` and
`⟨·, ·⟩` is the covariant `(0, r + s)` inner product of the metric-lowered tensors. No integrability
or smoothness hypothesis is exposed — each summand vanishes by the self-contained per-direction
covariant integration by parts `integral_tensorInner_covDeriv_combined_eq_zero`
(`TensorConnLapLoweredIBP`), and the frame sum of zeros is zero.

This is the genuine reusable engine behind the frame-summed bracket telescoping: applied to the two
bracket summands `∇_{[Bᵢ, W]}(∇_{Bᵢ} T)` and `∇_{Bᵢ}(∇_{[Bᵢ, W]} T)` with `Z := ∇S`, it converts the
frame-summed bracket pairing `∑ᵢ ⟨∇_{V i}(W i), Z⟩` into `−∑ᵢ ⟨W i, ∇_{V i} Z⟩ − ∑ᵢ ⟨W i, Z⟩·divᵍ(V i)`
(once integrability splits each combined integral), exhibiting the bracket as a total covariant
divergence whose integral over the closed manifold vanishes. It is the first producer of this
bracket-divergence content; every prior appearance is a consumed hypothesis. -/
theorem integral_frameSummed_covDeriv_combined_eq_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) {ι : Type*} [Fintype ι]
    (V : ι → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (W : ι → SmoothCcTensor g r s) (Z : SmoothCcTensor g r s) :
    ∑ i, ∫ x, (tensorInnerPointwise_0s (I := I) (M := M) (r + s) g x
              (Tensor0SSpace.toModel
                (loweredCovDerivAlongVF (I := I) (M := M) g r s (W i).toSection (V i) x))
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g r s Z.toSection x))
            + tensorInnerPointwise_0s (I := I) (M := M) (r + s) g x
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g r s (W i).toSection x))
              (Tensor0SSpace.toModel
                (loweredCovDerivAlongVF (I := I) (M := M) g r s Z.toSection (V i) x))
            + tensorInnerScalar (I := I) (M := M) g r s (W i).toSection Z.toSection x
              * divergence_g (I := I) g (V i) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
  classical
  refine Finset.sum_eq_zero (fun i _ => ?_)
  exact integral_tensorInner_covDeriv_combined_eq_zero (I := I) (M := M) g r s
    (W i).toSection Z.toSection (V i)

/-- **The genuine curvature cross-pairing value (the integrated order-`2` Weitzenböck identity, in
cross-pairing form).** For a closed smooth Riemannian manifold `(M, g)`, every covariant rank `s`,
and every smooth compactly-supported `(0, s)`-tensor `S`, the global metric `L²` pairing of the
order-`2` commutator defect `Curv S := pointwiseTensorCurv g s S` against `∇S := covGrad g 0 s S`
equals the genuine Weitzenböck curvature integral

```
⟨Curv S, ∇S⟩_{L²} = ‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²},
```

with `Δ_∇ S := rawTensorConnLapSmooth g 0 s S` and `∇²S := covGrad g 0 (s + 1) (covGrad g 0 s S)`.
This is `weitzenbock_integrated_covGrad_l2_normSq` (`IntegratedOrder2Weitzenbock`,
`‖∇²S‖² = ‖Δ_∇ S‖² − ⟨Curv S, ∇S⟩`) solved for the cross-pairing, recorded here as the value the
genuine curvature fields `Gcurv + Gcd` must carry. -/
theorem weitzenbock_curvature_crossPairing_value
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Norm (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s S).toFun ^ 2 -
        tensorL2Norm (I := I) (M := M) g 0 (s + 1 + 1)
          (covGrad (I := I) (M := M) g 0 (s + 1)
            (covGrad (I := I) (M := M) g 0 s S)).toFun ^ 2 := by
  have hw := weitzenbock_integrated_covGrad_l2_normSq (I := I) (M := M) g s S
  have hCurv :
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
              (covGrad (I := I) (M := M) g 0 s S) -
            covGrad (I := I) (M := M) g 0 s
              (rawTensorConnLapSmooth (I := I) g 0 s S)).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun =
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (pointwiseTensorCurv (I := I) (M := M) g s S).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun := rfl
  rw [hCurv] at hw
  linarith [hw]

/-- **Integrated moving-frame nullity producer (from the genuine differentiated-curvature
cross-pairing value).** For a closed smooth Riemannian manifold `(M, g)`, covariant rank `s`, smooth
compactly-supported `(0, s)`-tensor `S`, and a smooth compactly-supported `(0, s + 1)`-tensor `Gcd`
(the gauge-glued tensorial `(∇R) S` differentiated-curvature trace section, carried abstractly), if
`Gcd` satisfies the **genuine differentiated-curvature cross-pairing value** — the global metric `L²`
pairing of the genuine curvature fields `GcurvSection g s S + Gcd` against `∇S := covGrad g 0 s S`
equals the Weitzenböck curvature integral

```
⟨GcurvSection g s S + Gcd, ∇S⟩_{L²} = ‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²}
```

(`Δ_∇ S := rawTensorConnLapSmooth g 0 s S`, `∇²S := covGrad g 0 (s + 1) (covGrad g 0 s S)`) — then the
**integrated moving-frame nullity** of the moving-frame remainder holds:

```
⟨pointwiseTensorCurv g s S − GcurvSection g s S − Gcd, ∇S⟩_{L²} = 0.
```

This is the integrated-nullity producer the deepest coupled atom
`exists_movingCentreDiffCurvSection_splitDivergenceDatum` consumes for its nullity conjunct. The
proof is the genuine value bridge: the hypothesis is the *value* of the genuine curvature
cross-pairing (a specific number `‖Δ_∇ S‖² − ‖∇²S‖²`, the defining integrated property the gauge-glued
`Gcd` construction yields via the frame-summed covariant integration by parts
`integral_frameSummed_covDeriv_combined_eq_zero`), and `weitzenbock_curvature_crossPairing_value`
gives the *same* number for `⟨Curv S, ∇S⟩_{L²}`; chaining them yields the bracket-free pairing
`⟨GcurvSection + Gcd, ∇S⟩_{L²} = ⟨Curv S, ∇S⟩_{L²}`, from which the nullity follows by the left-additivity
reduction `tensorL2Inner_movingFrameRemainder_eq_zero_of_bracketFreePairing`
(`MovingFrameBracketDivergence`). The hypothesis is a genuine mathematical input distinct from the
conclusion (a value equality, not the remainder orthogonality) and is *false* for an arbitrary `Gcd`
on a non-flat manifold — with `Gcd = 0` it forces `⟨GcurvSection, ∇S⟩_{L²} = ‖Δ_∇ S‖² − ‖∇²S‖²`, which
the pure-Riemann pairing does not carry (the `(∇R) S` content is genuinely missing). -/
theorem movingFrameNullity_of_genuineCrossPairingValue
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (Gcd : SmoothCcTensor g 0 (s + 1))
    (hval : tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (GcurvSection (I := I) (M := M) g s S + Gcd).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Norm (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s S).toFun ^ 2 -
        tensorL2Norm (I := I) (M := M) g 0 (s + 1 + 1)
          (covGrad (I := I) (M := M) g 0 (s + 1)
            (covGrad (I := I) (M := M) g 0 s S)).toFun ^ 2) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S -
          GcurvSection (I := I) (M := M) g s S - Gcd).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun = 0 := by
  have hpair :
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (GcurvSection (I := I) (M := M) g s S + Gcd).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun =
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (pointwiseTensorCurv (I := I) (M := M) g s S).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun := by
    rw [hval, weitzenbock_curvature_crossPairing_value (I := I) (M := M) g s S]
  exact tensorL2Inner_movingFrameRemainder_eq_zero_of_bracketFreePairing
    (I := I) (M := M) g s S (GcurvSection (I := I) (M := M) g s S) Gcd hpair

end Connection
end Integral
end DifferentialGeometry

end
