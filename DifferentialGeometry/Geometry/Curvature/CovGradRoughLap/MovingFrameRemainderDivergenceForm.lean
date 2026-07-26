import DifferentialGeometry.Geometry.Connection.MetricCompatibility.MovingFrameBracketDivergence
import DifferentialGeometry.Geometry.Curvature.Bochner.PointwiseTensorBochnerFieldSplit

/-!
# The moving-frame bracket remainder is `L²`-orthogonal to `∇S` (divergence-form core)

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file isolates the
**bracket-free-pairing core** of the genuine moving-frame third-order Bochner–Weitzenböck field
decomposition of the rank-generic order-`2` rough-Laplacian / covariant-gradient commutator defect

```
Curv S := Δ_∇(∇S) − ∇(Δ_∇ S)
```

(`pointwiseTensorCurv g s S`, a `(0, s + 1)`-tensor field; `∇S = covGrad g 0 s S`). Once the two
genuine curvature contraction fields `Gcurv = R(∇S)` and `GcurvDeriv = (∇R) S` are subtracted, the
surviving **moving-frame remainder** `Curv S − Gcurv − GcurvDeriv` — whose fibre value is the
explicit obstruction field `bracketThirdCurvFieldFib` of the field-level split
`pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field` (`tensor3rdCurvBracket` together with
the frame-trace discrepancy `covGradRoughLapTraceDiscrepancy_gen` and the moving-frame residual
`covGradRoughLapMovingFrameResidual_gen`) — is a **total covariant divergence** of an `∇S`-order
field, so its global metric `L²` pairing against `∇S` vanishes, and the genuine curvature fields
carry the entire cross-pairing `⟨Curv S, ∇S⟩_{L²}`.

## The divergence form is the genuine moving-frame input (not term-by-term)

The pairing `⟨Curv S, ∇S⟩_{L²}` is *not* zero: by the already-proved integrated order-`2`
Weitzenböck identity (`weitzenbock_integrated_covGrad_l2_normSq`) it equals
`‖Δ_∇S‖²_{L²} − ‖∇²S‖²_{L²}`, the genuine Weitzenböck curvature integral. Only the surviving
moving-frame remainder pairs to zero, and only *under the integral*: the per-direction covariant
integration by parts `integral_tensorInner_tangentAction_add_smul_divergence_eq_zero`, summed over
the `g_x`-orthonormal frame `Bᵢ := smoothOrthoFrame g x i`, exhibits the remainder pairing as the
integral of a metric divergence `divᵍ X` of an honest smooth `∇S`-order tangent field `X`, whose
value vanishes on the closed manifold (`integral_divergence_eq_zero_of_hasCompactSupport`). The
cancellation is *false term-by-term* through `smoothExtensionTangent`: the bracket's second summand
`∑ᵢ ∇_{Bᵢ}(∇_{[Bᵢ, W]} T)` is manifestly a covariant `Bᵢ`-divergence, but the first summand
`∑ᵢ ∇_{[Bᵢ, W]}(∇_{Bᵢ} T)` is not — only the *frame-summed* moving-frame remainder, paired against
`∇S`, telescopes into a total covariant divergence whose integral vanishes.

This file owns the **integration-by-parts ⟹ nullity ⟹ bracket-free pairing** reduction: it takes the
genuine moving-frame divergence datum — a smooth tangent field `X` whose metric divergence `divᵍ X`
agrees almost everywhere with the pointwise inner product `⟨Curv S − Gcurv − GcurvDeriv, ∇S⟩` of the
remainder against `∇S` — and converts it into the integrated nullity and the bracket-free pairing.
The divergence datum is the genuine moving-frame third-order curvature content: exhibiting it
(identifying the frame-summed bracket field with `∑ᵢ ∇_{Bᵢ}(W)` for an honest smooth `∇S`-order
field `W`) is the deeper moving-frame curvature-endomorphism node, supplied here as a hypothesis so
this core stays independent of the genuine-field construction. (The divergence datum is *false* for
an arbitrary pair `Gcurv, GcurvDeriv` — it holds exactly for the genuine curvature fields — so it is
a genuine mathematical hypothesis, not a posited universal.)

## Main results

* `tensorL2Inner_movingFrameRemainder_eq_zero_of_pointwise_divergence` — the **integrated
  divergence-nullity**: from the divergence datum `⟨Curv S − Gcurv − GcurvDeriv, ∇S⟩ =ᵐ divᵍ X`,
  the global `L²` pairing of the moving-frame remainder against `∇S` vanishes,
  `⟨Curv S − Gcurv − GcurvDeriv, ∇S⟩_{L²} = 0`. This is the closed-manifold divergence theorem
  specialised to the remainder pairing.

* `tensorL2Inner_genuineFields_covGrad_eq_pointwiseTensorCurv_of_pointwise_divergence` — the
  **bracket-free `L²` pairing** (the exact conjunct consumed by the genuine moving-frame
  third-order Weitzenböck field decomposition
  `exists_pointwiseTensorCurv_movingFrameField_orderSeparated_bracketFreePairing`): from the same
  divergence datum, the genuine fields carry the entire cross-pairing,
  `⟨Gcurv + GcurvDeriv, ∇S⟩_{L²} = ⟨Curv S, ∇S⟩_{L²}`. The proof writes
  `Curv S = (Gcurv + GcurvDeriv) + (Curv S − Gcurv − GcurvDeriv)`, splits the `L²` pairing by left
  additivity, and drops the remainder term by the nullity.

## Convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (frame trace) for the rough Laplacian. The covariant
gradient `covGrad g 0 s` raises the tensor rank from `(0, s)` to `(0, s + 1)`. All `L²` pairings are
the global metric `L²` pairing `tensorL2Inner` against the canonical Riemannian volume measure;
`divᵍ` is `divergence_g`.
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

/-- **Integrated divergence-nullity of the moving-frame bracket remainder.** Fix a closed smooth
Riemannian manifold `(M, g)`, a covariant rank `s`, a smooth compactly-supported `(0, s)`-tensor `S`,
and two `(0, s + 1)`-tensor fields `Gcurv`, `GcurvDeriv`. If the genuine moving-frame divergence
datum holds — a smooth tangent vector field `X` whose metric divergence `divᵍ X` agrees almost
everywhere with the pointwise metric inner product `⟨Curv S − Gcurv − GcurvDeriv, ∇S⟩` of the
moving-frame remainder against `∇S = covGrad g 0 s S` (`Curv S := pointwiseTensorCurv g s S`) — then
the global metric `L²` pairing of the remainder against `∇S` vanishes:

```
⟨Curv S − Gcurv − GcurvDeriv, ∇S⟩_{L²} = 0.
```

This is the closed-manifold divergence theorem (`integral_divergence_eq_zero_of_hasCompactSupport`,
in the inner-product form `tensorL2Inner_eq_zero_of_pointwise_inner_eq_divergence`) specialised to
the moving-frame remainder pairing: the frame-summed bracket field, paired against `∇S`, telescopes
into the total covariant divergence `divᵍ X`, whose integral over the closed manifold is zero. The
divergence datum is the genuine moving-frame third-order curvature content (the frame-summed bracket
field is `∑ᵢ ∇_{Bᵢ}(W)` for an honest smooth `∇S`-order field `W`), supplied here as a hypothesis so
this nullity core is independent of the genuine-field construction. -/
theorem tensorL2Inner_movingFrameRemainder_eq_zero_of_pointwise_divergence
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (Gcurv GcurvDeriv : SmoothCcTensor g 0 (s + 1))
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hdiv : (fun x : M => tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
              ((pointwiseTensorCurv (I := I) (M := M) g s S - Gcurv - GcurvDeriv).toFun x)
              ((covGrad (I := I) (M := M) g 0 s S).toFun x))
        =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x : M => divergence_g (I := I) g X x)) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S - Gcurv - GcurvDeriv).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun = 0 :=
  tensorL2Inner_eq_zero_of_pointwise_inner_eq_divergence (I := I) (M := M) g s
    (pointwiseTensorCurv (I := I) (M := M) g s S - Gcurv - GcurvDeriv)
    (covGrad (I := I) (M := M) g 0 s S) X hdiv

/-- **The bracket-free `L²` pairing of the genuine moving-frame third-order curvature fields.** Fix a
closed smooth Riemannian manifold `(M, g)`, a covariant rank `s`, a smooth compactly-supported
`(0, s)`-tensor `S`, and two genuine curvature fields `Gcurv`, `GcurvDeriv : SmoothCcTensor g 0 (s + 1)`.
If the genuine moving-frame divergence datum holds — a smooth tangent vector field `X` whose metric
divergence `divᵍ X` agrees almost everywhere with the pointwise metric inner product
`⟨Curv S − Gcurv − GcurvDeriv, ∇S⟩` of the moving-frame remainder against `∇S = covGrad g 0 s S`
(`Curv S := pointwiseTensorCurv g s S`) — then the genuine fields carry the entire curvature
cross-pairing:

```
⟨Gcurv + GcurvDeriv, ∇S⟩_{L²} = ⟨Curv S, ∇S⟩_{L²}.
```

This is the *bracket-free `L²` pairing* — the integrated half of the moving-frame Weitzenböck
cancellation, and the exact conjunct consumed by the genuine moving-frame third-order Weitzenböck
field decomposition `exists_pointwiseTensorCurv_movingFrameField_orderSeparated_bracketFreePairing`.
The proof writes `Curv S = (Gcurv + GcurvDeriv) + (Curv S − Gcurv − GcurvDeriv)`, splits the `L²`
pairing by left additivity (`tensorL2Inner_add_left`, the cross-term integrabilities supplied by
`SmoothCcTensor.integrable_inner_cross`), and drops the moving-frame remainder term by the integrated
divergence-nullity `tensorL2Inner_movingFrameRemainder_eq_zero_of_pointwise_divergence` — leaving the
genuine curvature fields to carry the entire pairing. The divergence datum is the genuine moving-frame
third-order curvature content (the frame-summed bracket remainder is a total covariant divergence of
an `∇S`-order field), supplied here as a hypothesis so this pairing core is independent of the
genuine-field construction; it is *false* for an arbitrary pair `Gcurv, GcurvDeriv` and holds exactly
for the genuine curvature fields, so it is a genuine mathematical hypothesis rather than a posited
universal. -/
theorem tensorL2Inner_genuineFields_covGrad_eq_pointwiseTensorCurv_of_pointwise_divergence
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (Gcurv GcurvDeriv : SmoothCcTensor g 0 (s + 1))
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hdiv : (fun x : M => tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
              ((pointwiseTensorCurv (I := I) (M := M) g s S - Gcurv - GcurvDeriv).toFun x)
              ((covGrad (I := I) (M := M) g 0 s S).toFun x))
        =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x : M => divergence_g (I := I) g X x)) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1) (Gcurv + GcurvDeriv).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun := by
  classical
  set Curv : SmoothCcTensor g 0 (s + 1) := pointwiseTensorCurv (I := I) (M := M) g s S with hCurv
  set gradS : SmoothCcTensor g 0 (s + 1) := covGrad (I := I) (M := M) g 0 s S with hgrad
  have hnull :
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (Curv - Gcurv - GcurvDeriv).toFun gradS.toFun = 0 :=
    tensorL2Inner_movingFrameRemainder_eq_zero_of_pointwise_divergence
      (I := I) (M := M) g s S Gcurv GcurvDeriv X hdiv
  have hCurv_eq : Curv = (Gcurv + GcurvDeriv) + (Curv - Gcurv - GcurvDeriv) := by abel
  have hfun : ((Gcurv + GcurvDeriv) + (Curv - Gcurv - GcurvDeriv)).toFun =
      (Gcurv + GcurvDeriv).toFun + (Curv - Gcurv - GcurvDeriv).toFun :=
    SmoothCcTensor.toFun_add _ _
  have hint₁ := SmoothCcTensor.integrable_inner_cross (I := I) (M := M) (Gcurv + GcurvDeriv) gradS
  have hint₂ :=
    SmoothCcTensor.integrable_inner_cross (I := I) (M := M) (Curv - Gcurv - GcurvDeriv) gradS
  have hsplit :
      tensorL2Inner (I := I) (M := M) g 0 (s + 1) Curv.toFun gradS.toFun =
        tensorL2Inner (I := I) (M := M) g 0 (s + 1) (Gcurv + GcurvDeriv).toFun gradS.toFun +
          tensorL2Inner (I := I) (M := M) g 0 (s + 1)
            (Curv - Gcurv - GcurvDeriv).toFun gradS.toFun := by
    nth_rewrite 1 [hCurv_eq]
    rw [hfun]
    exact tensorL2Inner_add_left (I := I) (M := M) g 0 (s + 1)
      (Gcurv + GcurvDeriv).toFun (Curv - Gcurv - GcurvDeriv).toFun gradS.toFun hint₁ hint₂
  rw [hnull] at hsplit
  linarith [hsplit]

/-- **The bracket-free `L²` pairing from the integrated moving-frame nullity.** Fix a closed smooth
Riemannian manifold `(M, g)`, a covariant rank `s`, a smooth compactly-supported `(0, s)`-tensor `S`,
and two genuine curvature fields `Gcurv`, `GcurvDeriv : SmoothCcTensor g 0 (s + 1)`. If the integrated
moving-frame nullity holds — the global metric `L²` pairing of the moving-frame remainder
`Curv S − Gcurv − GcurvDeriv` (`Curv S := pointwiseTensorCurv g s S`) against `∇S = covGrad g 0 s S`
vanishes,

```
⟨Curv S − Gcurv − GcurvDeriv, ∇S⟩_{L²} = 0,
```

— then the genuine fields carry the entire curvature cross-pairing:

```
⟨Gcurv + GcurvDeriv, ∇S⟩_{L²} = ⟨Curv S, ∇S⟩_{L²}.
```

This is the integrated-form sibling of
`tensorL2Inner_genuineFields_covGrad_eq_pointwiseTensorCurv_of_pointwise_divergence`: it consumes the
integrated nullity directly (the divergence datum's already-integrated half) rather than the pointwise
`=ᵐ divᵍ X` datum, so the consumer never threads the divergence current `X`. The proof writes
`Curv S = (Gcurv + GcurvDeriv) + (Curv S − Gcurv − GcurvDeriv)`, splits the `L²` pairing by left
additivity (`tensorL2Inner_add_left`, the cross-term integrabilities supplied by
`SmoothCcTensor.integrable_inner_cross`), and drops the remainder term by the supplied nullity. The
nullity is the genuine moving-frame third-order curvature content (the frame-summed bracket remainder
is a total covariant divergence of an `∇S`-order field, integrating to zero); it is *false* for an
arbitrary pair `Gcurv, GcurvDeriv` and holds exactly for the genuine curvature fields, so it is a
genuine mathematical hypothesis, not a posited universal. -/
theorem tensorL2Inner_genuineFields_covGrad_eq_pointwiseTensorCurv_of_movingFrameRemainder_nullity
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (Gcurv GcurvDeriv : SmoothCcTensor g 0 (s + 1))
    (hnull : tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S - Gcurv - GcurvDeriv).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun = 0) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1) (Gcurv + GcurvDeriv).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun := by
  classical
  set Curv : SmoothCcTensor g 0 (s + 1) := pointwiseTensorCurv (I := I) (M := M) g s S with hCurv
  set gradS : SmoothCcTensor g 0 (s + 1) := covGrad (I := I) (M := M) g 0 s S with hgrad
  have hCurv_eq : Curv = (Gcurv + GcurvDeriv) + (Curv - Gcurv - GcurvDeriv) := by abel
  have hfun : ((Gcurv + GcurvDeriv) + (Curv - Gcurv - GcurvDeriv)).toFun =
      (Gcurv + GcurvDeriv).toFun + (Curv - Gcurv - GcurvDeriv).toFun :=
    SmoothCcTensor.toFun_add _ _
  have hint₁ := SmoothCcTensor.integrable_inner_cross (I := I) (M := M) (Gcurv + GcurvDeriv) gradS
  have hint₂ :=
    SmoothCcTensor.integrable_inner_cross (I := I) (M := M) (Curv - Gcurv - GcurvDeriv) gradS
  have hsplit :
      tensorL2Inner (I := I) (M := M) g 0 (s + 1) Curv.toFun gradS.toFun =
        tensorL2Inner (I := I) (M := M) g 0 (s + 1) (Gcurv + GcurvDeriv).toFun gradS.toFun +
          tensorL2Inner (I := I) (M := M) g 0 (s + 1)
            (Curv - Gcurv - GcurvDeriv).toFun gradS.toFun := by
    nth_rewrite 1 [hCurv_eq]
    rw [hfun]
    exact tensorL2Inner_add_left (I := I) (M := M) g 0 (s + 1)
      (Gcurv + GcurvDeriv).toFun (Curv - Gcurv - GcurvDeriv).toFun gradS.toFun hint₁ hint₂
  rw [hnull] at hsplit
  linarith [hsplit]

end Connection
end Integral
end DifferentialGeometry

end
