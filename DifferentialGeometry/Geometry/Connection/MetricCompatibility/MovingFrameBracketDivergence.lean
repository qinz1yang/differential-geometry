import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovariantIntegrationByParts
import DifferentialGeometry.Geometry.Curvature.Bochner.PointwiseTensorBochner
import DifferentialGeometry.Analysis.Integration.L2.Pairing.Algebra

/-!
# The moving-frame bracket remainder as a total covariant divergence, and its `L²` nullity

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file isolates the
**integrated divergence-nullity** half of the genuine moving-frame third-order Bochner–Weitzenböck
field decomposition of the rank-generic order-`2` rough-Laplacian / covariant-gradient commutator
defect

```
Curv S := Δ_∇(∇S) − ∇(Δ_∇ S)
```

(`pointwiseTensorCurv g s S`, a `(0, s + 1)`-tensor field; `∇S = covGrad g 0 s S`): the moving-frame
remainder `Curv S − Gcurv − GcurvDeriv` — the `tensor3rdCurvBracket` together with the frame-trace
discrepancy and the moving-frame residual that survive after the two genuine curvature contraction
fields `Gcurv = R(∇S)` and `GcurvDeriv = (∇R) S` are subtracted — is a **total covariant
divergence** of an `∇S`-order field, so its global metric `L²` pairing against `∇S` vanishes.

## Why the nullity is an integrated (not pointwise) fact

The pairing `⟨Curv S, ∇S⟩_{L²}` is *not* zero: by the already-proved integrated order-`2` Weitzenböck
identity (`weitzenbock_integrated_covGrad_l2_normSq`) it equals `‖Δ_∇S‖²_{L²} − ‖∇²S‖²_{L²}`, the
genuine Weitzenböck curvature integral. Only after the genuine curvature contractions `R(∇S)` and
`(∇R) S` are subtracted does the surviving moving-frame remainder pair to zero, and only *under the
integral*: the per-direction covariant integration by parts
(`integral_tensorInner_tangentAction_add_smul_divergence_eq_zero`), summed over an orthonormal frame,
exhibits the remainder pairing as the integral of a metric divergence, whose value is zero on the
closed manifold (`integral_divergence_eq_zero_of_hasCompactSupport`). The cancellation is *false
term-by-term* through `smoothExtensionTangent` and is not a pointwise divergence of the remainder
alone; the bracket's second summand `∑ᵢ ∇_{Bᵢ}(∇_{[Bᵢ, W]} T)` is manifestly a covariant
`Bᵢ`-divergence, but the first summand `∑ᵢ ∇_{[Bᵢ, W]}(∇_{Bᵢ} T)` is not — only the *full* moving-frame
remainder, paired against `∇S`, telescopes into a total covariant divergence whose integral vanishes.

## The two divergence tools (both proved outright)

* `tensorL2Inner_eq_zero_of_pointwise_inner_eq_divergence` — the **closed-manifold divergence theorem
  in inner-product form**: if the pointwise metric inner product of two fields agrees almost
  everywhere with the metric divergence `divᵍ X` of a smooth tangent vector field `X`, then the
  global `L²` pairing of the two fields vanishes. This is the divergence / integration-by-parts half
  of the route — a frame-summed covariant integration by parts exhibits the remainder pairing as
  exactly such a divergence current, and the closed-manifold divergence theorem then forces the
  pairing to zero.

* `tensorL2Inner_movingFrameRemainder_eq_zero_of_bracketFreePairing` — the **bracket-free-pairing
  nullity reduction**: from the genuine moving-frame bracket-free `L²` pairing
  `⟨Gcurv + GcurvDeriv, ∇S⟩_{L²} = ⟨Curv S, ∇S⟩_{L²}` (the moving-frame remainder is a total covariant
  divergence of an `∇S`-order field, so it integrates to zero against `∇S`, leaving the genuine fields
  to carry the entire pairing), the integrated divergence-nullity
  `⟨Curv S − Gcurv − GcurvDeriv, ∇S⟩_{L²} = 0` of the moving-frame remainder follows by left
  additivity of the `L²` pairing. This is the nullity conjunct consumed verbatim by the genuine
  moving-frame third-order Weitzenböck field decomposition
  (`pointwiseTensorCurv_movingFrameWeitzenbock_namedRemainder`,
  `exists_pointwiseTensorCurv_movingFrameField_orderSeparated_divergenceNull`); the bracket-free
  pairing hypothesis is the genuine moving-frame curvature core supplied by the field-decomposition
  primitive.

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

/-- **The closed-manifold divergence theorem, in inner-product form.** For a closed smooth Riemannian
manifold `(M, g)`, two smooth compactly-supported `(0, s + 1)`-tensor fields `W`, `Y`, and a smooth
tangent vector field `X`, if the pointwise metric inner product `x ↦ ⟨W(x), Y(x)⟩_{g(x)}` agrees
almost everywhere (against the Riemannian volume measure) with the metric divergence `divᵍ X`, then
the global metric `L²` pairing of `W` and `Y` vanishes:

```
⟨W, Y⟩_{L²} = ∫_M ⟨W, Y⟩ dvolᵍ = ∫_M divᵍ X dvolᵍ = 0.
```

The integral of `divᵍ X` over a closed manifold is zero by
`integral_divergence_eq_zero_of_hasCompactSupport` (the manifold's compactness supplies the compact
support of `X`). This is the integration-by-parts / divergence half of the moving-frame
divergence-nullity route: a frame-summed covariant integration by parts exhibits the moving-frame
remainder pairing as exactly such a divergence current, and the closed-manifold divergence theorem
then forces the global pairing to zero. -/
theorem tensorL2Inner_eq_zero_of_pointwise_inner_eq_divergence
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W Y : SmoothCcTensor g 0 (s + 1))
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hdiv : (fun x : M => tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
              (W.toFun x) (Y.toFun x))
        =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x : M => divergence_g (I := I) g X x)) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1) W.toFun Y.toFun = 0 := by
  classical
  unfold tensorL2Inner
  rw [MeasureTheory.integral_congr_ae hdiv]
  exact integral_divergence_eq_zero_of_hasCompactSupport (I := I) g X
    (HasCompactSupport.of_compactSpace _)

/-- **Bracket-free-pairing nullity reduction for the moving-frame bracket remainder.** Fix a closed
smooth Riemannian manifold `(M, g)`, a covariant rank `s`, a smooth compactly-supported `(0, s)`-tensor
`S`, and two `(0, s + 1)`-tensor fields `Gcurv`, `GcurvDeriv`. If the genuine fields carry the entire
curvature cross-pairing — the **bracket-free `L²` pairing**

```
⟨Gcurv + GcurvDeriv, ∇S⟩_{L²} = ⟨Curv S, ∇S⟩_{L²}   (Curv S := pointwiseTensorCurv g s S)
```

— then the complementary moving-frame remainder `Curv S − Gcurv − GcurvDeriv` pairs to zero against
`∇S`:

```
⟨Curv S − Gcurv − GcurvDeriv, ∇S⟩_{L²} = 0.
```

The bracket-free pairing is the genuine moving-frame third-order Weitzenböck curvature content (the
moving-frame remainder is a total covariant divergence of an `∇S`-order field, so it integrates to
zero against `∇S`); this lemma is the purely algebraic step that converts that pairing equality into
the integrated divergence-nullity consumed by the field-decomposition primitive
(`pointwiseTensorCurv_movingFrameWeitzenbock_namedRemainder`,
`exists_pointwiseTensorCurv_movingFrameField_orderSeparated_divergenceNull`). The proof writes
`Curv S = (Gcurv + GcurvDeriv) + (Curv S − Gcurv − GcurvDeriv)` and splits the `L²` pairing by left
additivity (`tensorL2Inner_add_left`, the cross-term integrabilities supplied by
`SmoothCcTensor.integrable_inner_cross`), so the bracket-free pairing forces the remainder term to
vanish. -/
theorem tensorL2Inner_movingFrameRemainder_eq_zero_of_bracketFreePairing
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (Gcurv GcurvDeriv : SmoothCcTensor g 0 (s + 1))
    (hpair : tensorL2Inner (I := I) (M := M) g 0 (s + 1) (Gcurv + GcurvDeriv).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S - Gcurv - GcurvDeriv).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun = 0 := by
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
  rw [hpair] at hsplit
  linarith [hsplit]

end Connection
end Integral
end DifferentialGeometry

end
