import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameCurvatureTraceSmooth

/-!
# Section-level carriers of the order-`2` commutator defect (the moving-frame remainder)

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file lifts the
**fibre-level** genuine + obstruction split of the rank-generic order-`2` rough-Laplacian /
covariant-gradient commutator defect

```
Curv S := Δ_∇(∇S) − ∇(Δ_∇ S)
```

(`pointwiseTensorCurv g s S`, a `(0, s + 1)`-tensor field; `∇S = covGrad g 0 s S`) to the
**section level** (`SmoothCcTensor`), tying the section-level carriers to the explicit moving-frame
fibre fields of `pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field`
(`PointwiseTensorBochnerFieldSplit`). It is the foundational carrier infrastructure for the
moving-frame summed-folding nullity: it isolates *which* concrete `SmoothCcTensor` carries the
surviving fibre obstruction and exactly *which* fibre fields its unit-section reconstructs to.

## The reconstruction frame

The field split of `pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field` and the pure-Riemann
section identity `GcurvSection_toSection_eq_genuineThirdCurvFieldFibPureR` are each stated for an
*existentially-quantified* `g_x`-orthonormal reconstruction frame, with mutually opaque witnesses. To
*combine* them both reconstructions must be read at the *same* frame. This file generalises the field
split to read at *any* `g_x`-orthonormal frame, so it can be evaluated at the (otherwise opaque)
witness frame of `GcurvSection`'s identity, through the slot-`0` orthonormal uncurry reconstruction
`tensor0S_uncurry_cons_eval_orthonormal` and the Parseval expansion `orthonormalFrame_parseval_expand`
(re-proved here from public primitives, deriving the expansion from orthonormality alone).

## Main results

* `orthonormalFrame_parseval_expand` — the `g_x`-orthonormal Parseval expansion of a tangent vector
  against any `g_x`-orthonormal frame (`n = finrank`), derived from orthonormality.

* `pointwiseTensorCurv_toSection_eq_genuine_add_bracket_ofOrthonormal` — the field split read at any
  `g_x`-orthonormal frame `e`:
  ```
  toModel ((Curv S).toSection x (unit)) (Fin.cons w m)
    = genuineThirdCurvFieldFib g s S x e w m + bracketThirdCurvFieldFib g s S x e w m.
  ```

* `genuineCurvPureRSubtracted` — the **pure-Riemann-subtracted carrier section**
  `Curv S − GcurvSection g s S`, a `SmoothCcTensor g 0 (s + 1)` (no frame-jet smoothness debt: a
  subtraction of two smooth sections).

* `genuineCurvPureRSubtracted_toSection_eq_covDeriv_add_bracket` — the **section-level carrier
  identity** (the corrected target): at the moving frame `e := smoothOrthoFrame g x · x`, the
  unit-section fibre value of the pure-Riemann-subtracted carrier reconstructs as the sum of the
  surviving genuine differentiated-curvature fibre field and the bracket obstruction fibre field:
  ```
  toModel ((Curv S − GcurvSection g s S).toSection x (unit)) (Fin.cons w m)
    = genuineThirdCurvFieldFibCovDeriv g s S x e w m + bracketThirdCurvFieldFib g s S x e w m.
  ```

* `movingFrameRemainderSection` — the **four-carrier moving-frame remainder section**
  `Curv S − GcurvSection g s S − genuineDiffCurvSection g s S − ricTraceSection g s S`, a
  `SmoothCcTensor g 0 (s + 1)` (the exact object whose `L²` pairing against `∇S` the summed-folding
  nullity consumes), with its `toSection`-difference rewrite.

## A note on the differentiated-curvature carrier (the genuine soundness boundary)

The surviving fibre field of the pure-Riemann-subtracted carrier is the *extension-curried*
differentiated trace `genuineThirdCurvFieldFibCovDeriv` (the frame sum of `∑ᵢ ∇_{Bᵢ}(R(Bᵢ, Wₐ) S)`
against the smooth extensions `Wₐ := smoothExtensionTangent x (eₐ)`). It is **not** the fibre value
of the tensorial section `genuineDiffCurvSection g s S = appCc (covGrad (curvOpField g s)) S`: by
construction (`pureRGenuineDiffOp`, the sound analogue of the unsound `pureRFrozenDiffOp`) the
tensorial differentiated-curvature section differentiates only the curvature factor and never a
frame jet, whereas the extension-curried trace `genuineThirdCurvFieldFibCovDeriv` does see the first
jet of the frame extension. The two agree only *under the integral against `∇S` on the closed
manifold* (the frame-jet discrepancy is a total covariant divergence) — this is the moving-frame
summed-folding content carried by `(ii)`/`(iii)`, not a pointwise fibre identity. Accordingly the
section-level carrier identity here is stated against the honest extension-curried field
`genuineThirdCurvFieldFibCovDeriv`, never asserting a false pointwise `genuineDiffCurvSection`
equality.

## Convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (frame trace). The covariant gradient `covGrad g 0 s`
curries the new tangent-direction slot as the leftmost covariant slot. All fibre values are read at
the unit `(0, 0)`-covector through `unitZeroSec`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators RealInnerProductSpace

namespace DifferentialGeometry
namespace Integral
namespace Connection

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

/-- **Parseval expansion of a generic `g_x`-orthonormal frame.** For any tangent frame `e` indexed by
`Fin n` with `n = finrank` that is `g_x`-orthonormal (`g.inner x (e i) (e j) = if i = j then 1 else
0`), every tangent vector at `x` is its `g_x`-orthonormal expansion against `e`. Derived from
orthonormality + the cardinality match through `basisOfLinearIndependentOfCardEqFinrank`; the
curvature-side analogue of `orthoFrame_parseval_expand`, with no privacy on the frame's origin (so it
applies to the existential witness of `GcurvSection`'s identity as well as to `smoothOrthoFrame`). -/
theorem orthonormalFrame_parseval_expand
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hn : n = Module.finrank ℝ (TangentSpace I x))
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (u : TangentSpace I x) :
    u = ∑ a : Fin n, g.inner x (e a) u • e a := by
  classical
  have hfinrank_eq : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := rfl
  haveI : Nonempty (Fin n) := by
    refine ⟨⟨0, ?_⟩⟩
    rw [hn, hfinrank_eq]
    exact Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))
  have he_li : LinearIndependent ℝ e := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner x (e k) (∑ j ∈ fs, c j • e j) = 0 := by rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs,
        g.inner x (e k) (c j • e j) = c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [(g.inner x (e k)).map_smul (c j) (e j), smul_eq_mul, horth k j]
    rw [Finset.sum_congr rfl h_pull, Finset.sum_eq_single_of_mem k hk_mem] at h_zero
    · rwa [if_pos rfl, mul_one] at h_zero
    · intro j _ hjk; rw [if_neg (fun h => hjk h.symm), mul_zero]
  have hcard : Fintype.card (Fin n) = Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin]; exact hn
  set bse : Module.Basis (Fin n) ℝ (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank he_li hcard with hbse_def
  have hbse_eq : ∀ i, bse i = e i := by
    intro i; rw [hbse_def]
    exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank he_li hcard) i
  conv_lhs => rw [← bse.sum_repr u]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [hbse_eq a]
  congr 1
  have hrepr : g.inner x (e a) u =
      ∑ b : Fin n, bse.repr u b * g.inner x (e a) (e b) := by
    conv_lhs => rw [show u = ∑ b : Fin n,
      bse.repr u b • bse b from (bse.sum_repr u).symm]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [(g.inner x (e a)).map_smul (bse.repr u b) (bse b), smul_eq_mul, hbse_eq b]
  rw [hrepr, Finset.sum_eq_single a]
  · rw [horth a a, if_pos rfl, mul_one]
  · intro b _ hba; rw [horth a b, if_neg (fun h => hba h.symm), mul_zero]
  · intro h; exact absurd (Finset.mem_univ a) h

/-- **The field-level genuine + bracket split of the order-`2` commutator defect, read at any
`g_x`-orthonormal frame.** This is `pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field`
generalised to read its reconstruction at *any* `g_x`-orthonormal frame `e` (with `n = finrank`), not
only the existential witness, so that it can be combined with the pure-Riemann section identity
`GcurvSection_toSection_eq_genuineThirdCurvFieldFibPureR` at the *same* frame:
```
toModel ((Curv S).toSection x (unit)) (Fin.cons w m)
  = genuineThirdCurvFieldFib g s S x e w m + bracketThirdCurvFieldFib g s S x e w m.
```
The proof reconstructs the unit-section of `Curv S` from its slot-`0` curried slices through the
orthonormal Parseval expansion `orthonormalFrame_parseval_expand` and the slot-`0` orthonormal
uncurry `tensor0S_uncurry_cons_eval_orthonormal`, then resolves each slot-`0` slice by
`tensor0S_curry_pointwiseTensorCurv_eq_genuine_add_obstruction`. -/
theorem pointwiseTensorCurv_toSection_eq_genuine_add_bracket_ofOrthonormal
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hn : n = Module.finrank ℝ (TangentSpace I x))
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (w : TangentSpace I x) (m : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) (Fin.cons w m) =
      genuineThirdCurvFieldFib (I := I) (M := M) g s S x e w m +
        bracketThirdCurvFieldFib (I := I) (M := M) g s S x e w m := by
  classical
  have hexp : ∀ u : TangentSpace I x, u = ∑ a : Fin n,
      g.inner x (e a) u • e a := fun u =>
    orthonormalFrame_parseval_expand (I := I) (M := M) g x e hn horth u
  rw [tensor0S_uncurry_cons_eval_orthonormal (I := I) (M := M) g
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)
      (unitZeroSec (I := I) (M := M) x)) e hexp w m]
  rw [genuineThirdCurvFieldFib, bracketThirdCurvFieldFib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [tensor0S_curry_pointwiseTensorCurv_eq_genuine_add_obstruction
    (I := I) (M := M) g s S x (e a)]
  rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply, smul_add]

/-- **The pure-Riemann-subtracted carrier section** `Curv S − GcurvSection g s S`, a smooth
compactly-supported `(0, s + 1)`-tensor. Once the pure-Riemann curvature section `GcurvSection g s S`
(`= R(∇S)`) is subtracted from the commutator defect `Curv S := pointwiseTensorCurv g s S`, the
surviving carrier holds the differentiated-curvature trace together with the moving-frame bracket
obstruction. It is a subtraction of two smooth sections, hence carries no frame-jet smoothness debt.
-/
noncomputable def genuineCurvPureRSubtracted
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    SmoothCcTensor g 0 (s + 1) :=
  pointwiseTensorCurv (I := I) (M := M) g s S - GcurvSection (I := I) (M := M) g s S

/-- The `toSection` of the pure-Riemann-subtracted carrier is the difference of the underlying
sections. Definitional through `SmoothCcTensor.toSection_sub`. -/
@[simp] lemma genuineCurvPureRSubtracted_toSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    (genuineCurvPureRSubtracted (I := I) (M := M) g s S).toSection =
      (pointwiseTensorCurv (I := I) (M := M) g s S).toSection -
        (GcurvSection (I := I) (M := M) g s S).toSection := by
  rw [genuineCurvPureRSubtracted, SmoothCcTensor.toSection_sub]

/-- **The section-level carrier identity of the pure-Riemann-subtracted carrier.** There is a
`g_x`-orthonormal frame `e` (the witness frame of `GcurvSection`'s pure-Riemann reconstruction) in
which the unit-section fibre value of the pure-Riemann-subtracted carrier `Curv S − GcurvSection g s
S` reconstructs as the sum of the surviving genuine differentiated-curvature fibre field
`genuineThirdCurvFieldFibCovDeriv` and the bracket obstruction fibre field `bracketThirdCurvFieldFib`:
```
toModel ((Curv S − GcurvSection g s S).toSection x (unit)) (Fin.cons w m)
  = genuineThirdCurvFieldFibCovDeriv g s S x e w m + bracketThirdCurvFieldFib g s S x e w m.
```

**Proof.** The witness frame `e` and its orthonormality come from
`GcurvSection_toSection_eq_genuineThirdCurvFieldFibPureR`. The unit-section subtraction distributes
through the `(0, s + 1)`-section difference (`SmoothCcTensor.toSection_sub`,
`ContinuousLinearMap.sub_apply`, `Tensor0SSpace.toModel_sub`). The `Curv S` summand resolves by the
frame-generic field split `pointwiseTensorCurv_toSection_eq_genuine_add_bracket_ofOrthonormal` at
this same frame `e` into `genuineThirdCurvFieldFib + bracketThirdCurvFieldFib`, with the genuine
field split further into its pure-Riemann and differentiated-curvature parts by
`genuineThirdCurvFieldFib_eq_pureR_add_covDeriv`; the `GcurvSection` summand resolves into exactly the
pure-Riemann field `genuineThirdCurvFieldFibPureR` at `e`, which cancels, leaving the
differentiated-curvature field plus the bracket obstruction. -/
theorem genuineCurvPureRSubtracted_toSection_eq_covDeriv_add_bracket
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) ∧
      ∀ (w : TangentSpace I x) (m : Fin s → TangentSpace I x),
        Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              (genuineCurvPureRSubtracted (I := I) (M := M) g s S).toSection x)
              (unitZeroSec (I := I) (M := M) x)) (Fin.cons w m) =
          genuineThirdCurvFieldFibCovDeriv (I := I) (M := M) g s S x e w m +
            bracketThirdCurvFieldFib (I := I) (M := M) g s S x e w m := by
  classical
  obtain ⟨n, e, hn, horth, hGcurv⟩ :=
    GcurvSection_toSection_eq_genuineThirdCurvFieldFibPureR (I := I) (M := M) g s S x
  refine ⟨n, e, hn, horth, fun w m => ?_⟩

  have hsub : Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (genuineCurvPureRSubtracted (I := I) (M := M) g s S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) (Fin.cons w m) =
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)
            (unitZeroSec (I := I) (M := M) x)) (Fin.cons w m) -
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            (GcurvSection (I := I) (M := M) g s S).toSection x)
            (unitZeroSec (I := I) (M := M) x)) (Fin.cons w m) := by
    rw [genuineCurvPureRSubtracted_toSection]
    rw [show ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection -
        (GcurvSection (I := I) (M := M) g s S).toSection) x =
      (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x -
        (GcurvSection (I := I) (M := M) g s S).toSection x from rfl]
    rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x -
            (GcurvSection (I := I) (M := M) g s S).toSection x)
          (unitZeroSec (I := I) (M := M) x) =
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)
          (unitZeroSec (I := I) (M := M) x) -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (GcurvSection (I := I) (M := M) g s S).toSection x)
          (unitZeroSec (I := I) (M := M) x) from
      ContinuousLinearMap.sub_apply _ _ _]
    rw [Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]
  rw [hsub]

  rw [pointwiseTensorCurv_toSection_eq_genuine_add_bracket_ofOrthonormal
    (I := I) (M := M) g s S x e hn horth w m]
  rw [genuineThirdCurvFieldFib_eq_pureR_add_covDeriv (I := I) (M := M) g s S x e w m]
  rw [hGcurv w m]
  ring

/-- **The four-carrier moving-frame remainder section** `Curv S − GcurvSection g s S −
genuineDiffCurvSection g s S − ricTraceSection g s S`, a smooth compactly-supported
`(0, s + 1)`-tensor. This is the exact object whose global metric `L²` pairing against
`∇S := covGrad g 0 s S` the moving-frame summed-folding nullity reduces to a frame-summed covariant
Leibniz integral (the divergence-form content of `(ii)`/`(iii)`). It is a subtraction of four smooth
sections, hence carries no frame-jet smoothness debt.

Its unit-section fibre value is **not** the bare bracket obstruction field `bracketThirdCurvFieldFib`
of the field split: the tensorial differentiated-curvature section `genuineDiffCurvSection g s S` and
the Ricci-trace section `ricTraceSection g s S` are frame-jet-free (sound) carriers that differ from
the extension-curried fibre fields by a total covariant divergence; the equality of the remainder's
pairing with the bracket data holds only *under the integral against `∇S` on the closed manifold*
(the summed-folding identity), never as a pointwise fibre identity. -/
noncomputable def movingFrameRemainderSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    SmoothCcTensor g 0 (s + 1) :=
  pointwiseTensorCurv (I := I) (M := M) g s S - GcurvSection (I := I) (M := M) g s S -
    genuineDiffCurvSection (I := I) (M := M) g s S - ricTraceSection (I := I) (M := M) g s S

/-- The `toSection` of the four-carrier moving-frame remainder is the iterated difference of the
underlying sections. Definitional through `SmoothCcTensor.toSection_sub`. -/
@[simp] lemma movingFrameRemainderSection_toSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    (movingFrameRemainderSection (I := I) (M := M) g s S).toSection =
      (pointwiseTensorCurv (I := I) (M := M) g s S).toSection -
          (GcurvSection (I := I) (M := M) g s S).toSection -
          (genuineDiffCurvSection (I := I) (M := M) g s S).toSection -
        (ricTraceSection (I := I) (M := M) g s S).toSection := by
  rw [movingFrameRemainderSection, SmoothCcTensor.toSection_sub,
    SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_sub]

/-- **The four-carrier remainder is the pure-Riemann-subtracted carrier minus the two frame-jet-free
genuine carriers.** A pure regrouping of the section subtractions: `Curv − GcurvSection −
genuineDiffCurvSection − ricTraceSection = (Curv − GcurvSection) − (genuineDiffCurvSection +
ricTraceSection)`. This exhibits the four-carrier remainder consumed by the summed-folding nullity in
terms of the pure-Riemann-subtracted carrier whose fibre split is established here. -/
theorem movingFrameRemainderSection_eq_pureRSubtracted_sub_genuineDiff_ricTrace
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    movingFrameRemainderSection (I := I) (M := M) g s S =
      genuineCurvPureRSubtracted (I := I) (M := M) g s S -
        (genuineDiffCurvSection (I := I) (M := M) g s S +
          ricTraceSection (I := I) (M := M) g s S) := by
  rw [movingFrameRemainderSection, genuineCurvPureRSubtracted]
  abel

end Connection
end Integral
end DifferentialGeometry
