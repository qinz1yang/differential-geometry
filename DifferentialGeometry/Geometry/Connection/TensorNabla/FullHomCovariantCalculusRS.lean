import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldCovariantCalculusRS
import DifferentialGeometry.Geometry.Connection.TensorNabla.SecondOrderHomBundle
import DifferentialGeometry.Geometry.Connection.TensorNabla.HomTensorRSRiemannian

/-!
# The full Hom-bundle operator-field covariant calculus at a generic contravariant valence

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, this file builds the **full Hom-bundle operator-field action** `appFullRS` at a
generic contravariant valence `r`, together with its covariant calculus: the section-level covariant
product rule `covGrad_appFullRS_eq`, the slot extension `slotExtendFull`, the per-term fibrewise
Cauchy–Schwarz, and the operator-field **normal-form engine** `NormalFormFull` /
`normalFormFull_of_base` / `exists_jet_bound_of_normalFormFull` for a recursively-differentiated tower
whose order-`0` base is a fixed-field full Hom action.

Unlike the codomain-only action `appCcRS` (`OperatorFieldCovariantCalculusRS`, post-composition at the
`Tensor0SSpace` level), the operator field here is a continuous-linear endomorphism-type map of the
**full** `(r, a)` / `(r, c)`-tensor fibre.  At contravariant rank `0` a `(0, s)`-tensor *is* the map
`Tensor0SSpace 0 → Tensor0SSpace s` and the curvature acts only on its codomain, so the rank-`0`
differentiated-curvature carrier post-composes (`appCc`); at a generic valence `r ≥ 1` the curvature
reads the *whole* fibre (`riemannOp_tensorCovRS_apply_eval`), so the full Hom-bundle action is the
correct carrier.

The construction is **curvature-free**: it imports only the second-order Hom-bundle
(`SecondOrderHomBundle`), its `g`-fibre operator-norm Riemannian calculus (`HomTensorRSRiemannian`), and
the codomain-only operator-field calculus (`OperatorFieldCovariantCalculusRS`, for `covGradBundleEquiv`,
the iterated-gradient tower, and the rank-cast bookkeeping) — *none* of which import the rank-`r`
curvature towers.  This is the cycle break: the rank-`r` pure-Riemann and differentiated-curvature towers
(`RankRPureRCurvatureTower`, `RankRDiffCurvatureTower`) consume this engine, so the engine must not depend
on them.

## Main declarations

* `appFullRSFib` / `appFullRS` / `appFullRS_toSection` — the full Hom-bundle operator-field action at
  valence `r` and its definitional fibre-value formula; smoothness via the
  `ContMDiff.clm_bundle_apply` evaluation.  `ℝ`-bilinearity (`appFullRS_add_right`,
  `appFullRS_smul_right`, `appFullRSFib_add_left`);
* `slotExtendFullFib` / `slotExtendFullFib_apply` / `slotExtendFullFib_apply_eval` /
  `slotExtendFullFib_contMDiff` — the full-fibre slot extension inserting one leading covariant slot
  through `covGradBundleEquiv`, and its base-point smoothness;
* `homTensorRSCovGradField` / `homTensorRSCovGradField_apply` / `homTensorRSCovGradField_contMDiff` — the
  second-order Hom-bundle section covariant **gradient field** (raising the Hom codomain by one) and its
  directional reading and base-point smoothness;
* `covGrad_appFullRS_eq` — the section-level full-Hom covariant product rule
  `∇(Ψ·W) = (homTensorRSCovGradField Ψ)·W + (slotExtendFull Ψ)·(∇W)`, the carrier on which the
  full-Hom differentiated-tower induction runs;
* `exists_continuous_riemannianFiberNormSq_homSection_clm_le` /
  `exists_uniform_riemannianFiberNormSq_homSection_clm_le` /
  `exists_uniform_riemannianFiberNormSq_appFullRS_le` — the continuous and uniform section-proportional
  contraction envelopes (over the per-point fibrewise Cauchy–Schwarz
  `homTensorRS_riemannianFiberNormSq_clm_apply_le`, `HomTensorRSRiemannian`);
* `NormalFormFull` / `normalFormFull_of_base` / `exists_jet_bound_of_normalFormFull` — the full Hom-bundle
  operator-field normal form of a recursively-differentiated tower whose order-`0` base is a fixed-field
  full Hom action, and its per-order jet envelope.

Geometer convention; all fibre norms are the intrinsic `riemannianFiberNormSq`.  The construction stays
intrinsic: `covGrad` covariant gradients, the full `(r, a)`-tensor carrier, and the full Hom-bundle action
only.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ## The full Hom-bundle operator-field action at valence `r` -/

set_option backward.isDefEq.respectTransparency false in
/-- **The fibrewise full Hom-bundle operator-field action value at valence `r`.** The fibre value at `x`
of the action of a smooth full Hom-bundle field `Ψ : Π x, TensorRSSpace r a I x →L TensorRSSpace r c I x`
on an `(r, a)`-tensor `W`: the fibrewise application `Ψ x (W x) : TensorRSSpace r c I x`.  Unlike the
codomain-only `appCcRSFib` (post-composition at the `Tensor0SSpace` level), `Ψ x` is a continuous-linear
endomorphism-type map of the *full* tensor fibre. -/
def appFullRSFib (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (W : SmoothCcTensor g r a) (x : M) :
    TensorRSSpace r c I x :=
  Ψ x (W.toSection x)

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **Base-point smoothness of the full Hom-bundle operator-field action fibre field at valence `r`.**
If the full Hom-bundle field `Ψ` is a smooth `Hom(T^{(r,a)}, T^{(r,c)})`-bundle section, then the
`(r, c)`-tensor fibre field `x ↦ appFullRSFib g r a c Ψ W x = Ψ x (W x)` is a smooth section, by the
single `ContMDiff.clm_bundle_apply` evaluation `(Ψ x) (W x)` against the smooth `(r, a)`-section `W`. -/
theorem appFullRSFib_contMDiff (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x)))
    (W : SmoothCcTensor g r a) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r c I z) x
        (appFullRSFib (I := I) (M := M) g r a c Ψ W x)) :=
  ContMDiff.clm_bundle_apply (b := id) hΨ W.toSection.contMDiff

set_option backward.isDefEq.respectTransparency false in
/-- **The full Hom-bundle operator-field action of a smooth Hom field on an `(r, a)`-tensor**, as a
smooth compactly-supported `(r, c)`-tensor. The fibre value at `x` is `Ψ x (W x)` (`appFullRSFib`),
smooth by `appFullRSFib_contMDiff`; on the closed manifold it has compact support. The full-tensor-fibre
lift of `appCcRS` (which post-composes at the `Tensor0SSpace` level). -/
def appFullRS (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x)))
    (W : SmoothCcTensor g r a) : SmoothCcTensor g r c where
  toSection :=
    { toFun := fun x : M => appFullRSFib (I := I) (M := M) g r a c Ψ W x
      contMDiff_toFun := appFullRSFib_contMDiff (I := I) (M := M) g r a c Ψ hΨ W }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The underlying section value of `appFullRS g r a c Ψ hΨ W` at `x` is `Ψ x (W x)`. Definitional. -/
@[simp] lemma appFullRS_toSection (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x)))
    (W : SmoothCcTensor g r a) (x : M) :
    (appFullRS (I := I) (M := M) g r a c Ψ hΨ W).toSection x = Ψ x (W.toSection x) := rfl

/-! ## Bilinearity of the full Hom-bundle action -/

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The full Hom-bundle action is additive in the contracted `(r, a)`-tensor. -/
theorem appFullRS_add_right (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x)))
    (W₁ W₂ : SmoothCcTensor g r a) :
    appFullRS (I := I) (M := M) g r a c Ψ hΨ (W₁ + W₂) =
      appFullRS (I := I) (M := M) g r a c Ψ hΨ W₁ + appFullRS (I := I) (M := M) g r a c Ψ hΨ W₂ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((appFullRS (I := I) (M := M) g r a c Ψ hΨ W₁ +
        appFullRS (I := I) (M := M) g r a c Ψ hΨ W₂).toSection x) =
      (appFullRS (I := I) (M := M) g r a c Ψ hΨ W₁).toSection x +
        (appFullRS (I := I) (M := M) g r a c Ψ hΨ W₂).toSection x from rfl]
  rw [appFullRS_toSection, appFullRS_toSection, appFullRS_toSection]
  rw [show ((W₁ + W₂).toSection x : TensorRSSpace r a I x) = W₁.toSection x + W₂.toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [map_add (Ψ x)]

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The full Hom-bundle action is `ℝ`-homogeneous in the contracted `(r, a)`-tensor. -/
theorem appFullRS_smul_right (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (k : ℝ) (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x)))
    (W : SmoothCcTensor g r a) :
    appFullRS (I := I) (M := M) g r a c Ψ hΨ (k • W) =
      k • appFullRS (I := I) (M := M) g r a c Ψ hΨ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((k • appFullRS (I := I) (M := M) g r a c Ψ hΨ W).toSection x) =
      k • (appFullRS (I := I) (M := M) g r a c Ψ hΨ W).toSection x from rfl]
  rw [appFullRS_toSection, appFullRS_toSection]
  rw [show ((k • W).toSection x : TensorRSSpace r a I x) = k • W.toSection x from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [map_smul (Ψ x)]

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The full Hom-bundle action is additive in the operator-field factor (fibre-value form). -/
theorem appFullRSFib_add_left (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ₁ Ψ₂ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (W : SmoothCcTensor g r a) (x : M) :
    appFullRSFib (I := I) (M := M) g r a c (fun y => Ψ₁ y + Ψ₂ y) W x =
      appFullRSFib (I := I) (M := M) g r a c Ψ₁ W x +
        appFullRSFib (I := I) (M := M) g r a c Ψ₂ W x := by
  rw [appFullRSFib, appFullRSFib, appFullRSFib, ContinuousLinearMap.add_apply]

/-! ## The full-Hom slot extension `slotExtendFull`

The slot extension inserts one leading covariant slot into a full-fibre operator
`T^{(r,a)} →L T^{(r,c)}` through the slot-`0` curry equivalence `covGradBundleEquiv` — the full-fibre
analogue of the codomain-only `slotExtendFib` (which uses `tensor0S_curry`).  It is the spectator-term
carrier of the full-Hom covariant product rule `covGrad_appFullRS_eq`. -/

set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
/-- **The full-fibre slot extension of a fibrewise operator.** For a fibrewise full-fibre operator
`A : TensorRSSpace r a I x →L TensorRSSpace r c I x`, the slot-extended operator
`slotExtendFull A : TensorRSSpace r (a + 1) I x →L TensorRSSpace r (c + 1) I x` reads the new leading
covariant slot of its `(r, a + 1)`-tensor argument `D` off through `(covGradBundleEquiv r a x).symm`
(turning `D` into a per-direction `(r, a)`-tensor `TM →L T^{(r,a)}`), post-composes the per-direction
value with `A`, and re-inserts the slot through `covGradBundleEquiv r c x`.  The full-fibre analogue of
the codomain-only `slotExtendFib` (which uses `tensor0S_curry`).  Built through
`LinearMap.toContinuousLinearMap` in the primary (operator-norm) fibre topology, where the
finite-dimensional Hausdorff witnesses are read off the underlying continuous-linear-map fibre type. -/
noncomputable def slotExtendFullFib (g : SmoothRiemannianMetric I M) (r a c : ℕ) (x : M)
    (A : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) :
    TensorRSSpace r (a + 1) I x →L[ℝ] TensorRSSpace r (c + 1) I x :=
  haveI : FiniteDimensional ℝ (TensorRSSpace r (a + 1) I x) :=
    inferInstanceAs (FiniteDimensional ℝ (Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (a + 1) I x))
  haveI : T2Space (TensorRSSpace r (a + 1) I x) :=
    inferInstanceAs (T2Space (Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (a + 1) I x))
  LinearMap.toContinuousLinearMap
    { toFun := fun D =>
        covGradBundleEquiv (I := I) (M := M) r c x
          (A.comp ((covGradBundleEquiv (I := I) (M := M) r a x).symm D))
      map_add' := fun D₁ D₂ => by
        rw [map_add (covGradBundleEquiv (I := I) (M := M) r a x).symm,
          ContinuousLinearMap.comp_add, map_add (covGradBundleEquiv (I := I) (M := M) r c x)]
      map_smul' := fun k D => by
        rw [map_smul (covGradBundleEquiv (I := I) (M := M) r a x).symm,
          ContinuousLinearMap.comp_smul, map_smul (covGradBundleEquiv (I := I) (M := M) r c x)]
        rfl }

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The defining formula for `slotExtendFullFib`: the slot-`0` re-insertion of left-composition by `A`
of the slot-`0` removal of its argument.  True definitionally (`LinearMap.toContinuousLinearMap` is the
identity on the underlying function). -/
@[simp] lemma slotExtendFullFib_apply (g : SmoothRiemannianMetric I M) (r a c : ℕ) (x : M)
    (A : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) (D : TensorRSSpace r (a + 1) I x) :
    slotExtendFullFib (I := I) (M := M) g r a c x A D =
      covGradBundleEquiv (I := I) (M := M) r c x
        (A.comp ((covGradBundleEquiv (I := I) (M := M) r a x).symm D)) :=
  rfl

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **The slot-extended full-fibre operator reads the new slot first.** On a tuple `Fin.cons v0 vs`
(of tangent vectors) against a lower-input `(0, r)`-tensor `D`, the slot-extended operator reads the
passenger direction `v0` off the leading covariant slot (of both source and target) and applies `A` to
the per-direction `(r, a)`-tensor `(covGradBundleEquiv r a x).symm D v0`, evaluating at `vs`. -/
lemma slotExtendFullFib_apply_eval (g : SmoothRiemannianMetric I M) (r a c : ℕ) (x : M)
    (A : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) (D : TensorRSSpace r (a + 1) I x)
    (Dlow : Tensor0SSpace r I x) (v0 : TangentSpace I x) (vs : Fin c → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (c + 1) I x from
          slotExtendFullFib (I := I) (M := M) g r a c x A D) Dlow) (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace c I x from
          A ((covGradBundleEquiv (I := I) (M := M) r a x).symm D v0)) Dlow) vs := by
  rw [slotExtendFullFib_apply (I := I) (M := M) g r a c x A D]
  rw [covGradBundleEquiv_apply_eval (I := I) (M := M) r c x
    (A.comp ((covGradBundleEquiv (I := I) (M := M) r a x).symm D)) Dlow (Fin.cons v0 vs)]
  have htail : Matrix.vecTail (Fin.cons v0 vs : Fin (c + 1) → TangentSpace I x) = vs := by
    funext j; simp [Matrix.vecTail, Fin.cons_succ]
  have hhead : (Fin.cons v0 vs : Fin (c + 1) → TangentSpace I x) 0 = v0 := by simp [Fin.cons_zero]
  rw [htail, hhead, ContinuousLinearMap.comp_apply]

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **Base-point smoothness of the slot-extended full-Hom field (precise infrastructure child).** If the
full Hom-bundle field `Ψ : Π x, TensorRSSpace r a I x →L TensorRSSpace r c I x` is smooth, then the
slot-extended full Hom-bundle field `x ↦ slotExtendFullFib g r a c x (Ψ x) : T^{(r,a+1)} →L T^{(r,c+1)}`
is a smooth section of the second-order Hom-bundle `Hom(T^{(r,a+1)}, T^{(r,c+1)})`.

**Why this is TRUE.** The slot extension is the conjugate of `Ψ x` by the two covariant-gradient bundle
equivalences `covGradBundleEquiv r a x` (source, inverse) and `covGradBundleEquiv r c x` (target).  Both
bundle equivalences are *fibrewise* the smooth (indeed `C^∞`) trivialisation-free identifications of the
covariant-gradient bundle `Hom(TM, T^{(r,·)})` with the `(r, · + 1)`-tensor bundle
(`covGradBundleSmoothEquiv`), so conjugating the smooth section `Ψ` by them produces a smooth section.
The pointwise reduction is the per-vector smoothness bridge `contMDiff_clm_section_of_pointwise`: on a
smooth `(r, a + 1)`-section `Z`, the value `slotExtendFullFib … (Ψ x) (Z x)` is the re-curry through
`covGradBundleEquiv r c x` of the post-composition of `Ψ x` after the slot-`0` removal of `Z x`, each step
a smooth bundle operation (`ContMDiff.clm_bundle_apply` for the post-composition, the smooth bundle
equivalences for the slot operations).

**Precise missing prerequisite (verified).** The smoothness of the second-order-Hom-bundle conjugation by
`covGradBundleEquiv` requires the **smooth-section transport** of the slot-`0` curry equivalence at the
*operator-bundle* level — a `covGradBundleSmoothEquiv`-analogue for the second-order Hom-bundle codomain
`Hom(T^{(r,c)}, T^{(r,c+1)})` and the source covariant slot.  That second-order-Hom-bundle smooth slot
transport carries **no** API below this file (the first-order `covGradBundleSmoothEquiv` is stated only for
the `Tensor0SBundle` tower); it is the same multi-file second-order-Hom-bundle infrastructure node behind
`homTensorRSCovGradField_contMDiff`.  Posited here as one precise true infrastructure child.  Consumers
transitively depend on `sorryAx`.

**Non-vacuity.** A degenerate reading (the slot-extended field discontinuous, or constant in `x`) is
rejected: the slot extension of a genuinely `x`-varying smooth field varies continuously with `x` (it is
the conjugation of `Ψ x` by `x`-continuous bundle equivalences), and is not the zero field unless `Ψ` is. -/
theorem slotExtendFullFib_contMDiff (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (a + 1) ℝ E →L[ℝ] TensorRSModel r (c + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r (a + 1) ℝ E →L[ℝ] TensorRSModel r (c + 1) ℝ E)
        (E := fun z : M => TensorRSSpace r (a + 1) I z →L[ℝ] TensorRSSpace r (c + 1) I z) x
        (slotExtendFullFib (I := I) (M := M) g r a c x (Ψ x))) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (V₁ := fun z : M => TensorRSSpace r (a + 1) I z)
    (V₂ := fun z : M => TensorRSSpace r (c + 1) I z)
    (φ := fun x => slotExtendFullFib (I := I) (M := M) g r a c x (Ψ x))
  intro D
  have hG : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TensorRSSpace r c I z) x
        ((Ψ x).comp ((covGradBundleEquiv (I := I) (M := M) r a x).symm (D x)))) := by
    apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
      (V₁ := TangentSpace I) (V₂ := fun z : M => TensorRSSpace r c I z)
      (φ := fun x => (Ψ x).comp ((covGradBundleEquiv (I := I) (M := M) r a x).symm (D x)))
    intro Y
    have hH : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r a ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel r a ℝ E)
          (E := fun z : M => TangentSpace I z →L[ℝ] TensorRSSpace r a I z) x
          ((covGradBundleEquiv (I := I) (M := M) r a x).symm (D x))) :=
      (covGradBundleEquiv_symm_contMDiff_totalSpace (I := I) (M := M) r a).comp D.contMDiff
    have hstep1 : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E)
          (E := fun z : M => TensorRSSpace r a I z) x
          ((covGradBundleEquiv (I := I) (M := M) r a x).symm (D x) (Y x))) :=
      ContMDiff.clm_bundle_apply (b := id) hH Y.contMDiff
    have hstep2 : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r c ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (TensorRSModel r c ℝ E)
          (E := fun z : M => TensorRSSpace r c I z) x
          ((Ψ x) ((covGradBundleEquiv (I := I) (M := M) r a x).symm (D x) (Y x)))) :=
      ContMDiff.clm_bundle_apply (b := id) hΨ hstep1
    refine hstep2.congr ?_
    intro x
    rfl
  letI : NormedAddCommGroup (TensorRSModel r (c + 1) ℝ E) :=
    tensorRSModel_normedAddCommGroup r (c + 1)
  letI : NormedSpace ℝ (TensorRSModel r (c + 1) ℝ E) :=
    tensorRSModel_normedSpace r (c + 1)
  letI : TopologicalSpace (TotalSpace (TensorRSModel r (c + 1) ℝ E)
      (fun y : M => TensorRSSpace r (c + 1) I y)) :=
    tensorRSBundle_topology r (c + 1)
  letI : FiberBundle (TensorRSModel r (c + 1) ℝ E)
      (fun y : M => TensorRSSpace r (c + 1) I y) :=
    tensorRSBundle_fiber r (c + 1)
  letI : VectorBundle ℝ (TensorRSModel r (c + 1) ℝ E)
      (fun y : M => TensorRSSpace r (c + 1) I y) :=
    tensorRSBundle_vector r (c + 1)
  letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel r (c + 1) ℝ E)
      (fun y : M => TensorRSSpace r (c + 1) I y) I := tensorRSBundle_smooth ∞ r (c + 1)
  have hcomp :
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (c + 1) ℝ E)) ∞
        ((covGradBundleSmoothEquiv (I := I) (M := M) r c).toDiffeomorph ∘
          (fun x : M => (⟨x, (Ψ x).comp ((covGradBundleEquiv (I := I) (M := M) r a x).symm (D x))⟩ :
            TotalSpace (E →L[ℝ] TensorRSModel r c ℝ E)
              fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r c I y))) :=
    (covGradBundleSmoothEquiv (I := I) (M := M) r c).toDiffeomorph.contMDiff.comp hG
  refine hcomp.congr ?_
  intro x
  rw [Function.comp_apply,
    covGradBundleSmoothEquiv_toDiffeomorph_apply (I := I) (M := M) r c x
      ((Ψ x).comp ((covGradBundleEquiv (I := I) (M := M) r a x).symm (D x)))]
  congr 1

/-! ## The second-order Hom-bundle section covariant gradient field

The full-Hom covariant product rule reads off the new leading covariant gradient slot.  The spectator
`Ψ x (∇_v W)`, uncurried over the gradient direction `v`, is the action of the slot-extended operator
`slotExtendFull Ψ`; the principal `(∇^Hom Ψ)·W` term is the action of the **section covariant gradient
field** `homTensorRSCovGradField Ψ`, the second-order Hom-bundle section gradient of `Ψ` read as a fixed
full Hom field `Π x, T^{(r,a)} →L T^{(r,c+1)}` (raising the Hom codomain by one).  This is the full-Hom
analogue of `covGrad` for tensors, one bundle up: the directional derivative
`homTensorRSCovariantDerivative` curried into the codomain through `covGradBundleEquiv r c x`. -/

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **The directional second-order Hom-bundle covariant derivative as a genuine full-fibre operator.**
The opaque `HomTensorRSSpace r a c I x`-valued `homTensorRSCovariantDerivative … Ψ x v`, exposed as the
`(r, a) →L (r, c)` full-fibre operator it definitionally is. -/
def homTensorRSCovDirHom (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) (x : M) (v : TangentSpace I x) :
    TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x :=
  homTensorRSCovariantDerivative I M r a c (LeviCivita (I := I) g) Ψ x v

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The exposed directional derivative is continuous in the base direction `v`. -/
lemma homTensorRSCovDirHom_continuous (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) (x : M) :
    Continuous (fun v : TangentSpace I x => homTensorRSCovDirHom (I := I) (M := M) g r a c Ψ x v) :=
  (homTensorRSCovariantDerivative I M r a c (LeviCivita (I := I) g) Ψ x).continuous

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The exposed directional derivative is additive in the direction. -/
lemma homTensorRSCovDirHom_add (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) (x : M) (v v' : TangentSpace I x) :
    homTensorRSCovDirHom (I := I) (M := M) g r a c Ψ x (v + v') =
      homTensorRSCovDirHom (I := I) (M := M) g r a c Ψ x v +
        homTensorRSCovDirHom (I := I) (M := M) g r a c Ψ x v' := by
  rw [homTensorRSCovDirHom, homTensorRSCovDirHom, homTensorRSCovDirHom,
    map_add (homTensorRSCovariantDerivative I M r a c (LeviCivita (I := I) g) Ψ x)]

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The exposed directional derivative is `ℝ`-homogeneous in the direction. -/
lemma homTensorRSCovDirHom_smul (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) (x : M) (k : ℝ)
    (v : TangentSpace I x) :
    homTensorRSCovDirHom (I := I) (M := M) g r a c Ψ x (k • v) =
      k • homTensorRSCovDirHom (I := I) (M := M) g r a c Ψ x v := by
  rw [homTensorRSCovDirHom, homTensorRSCovDirHom,
    map_smul (homTensorRSCovariantDerivative I M r a c (LeviCivita (I := I) g) Ψ x)]

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **The directional gradient CLM `v ↦ (∇^Hom Ψ x v) d` on a fixed `(r, a)`-tensor `d`.** The
slot-carrying continuous-linear map `TangentSpace I x →L T^{(r,c)}` that `covGradBundleEquiv` re-inserts
into the new leading covariant slot.  Built through `LinearMap.toContinuousLinearMap` over the
finite-dimensional tangent domain (continuity automatic), with the codomain `T^{(r,c)}` keeping its
bundle topology. -/
noncomputable def homTensorRSCovGradDirCLM (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) (x : M)
    (d : TensorRSSpace r a I x) :
    TangentSpace I x →L[ℝ] TensorRSSpace r c I x :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  haveI : T2Space (TensorRSSpace r c I x) :=
    inferInstanceAs (T2Space (Tensor0SSpace r I x →L[ℝ] Tensor0SSpace c I x))
  LinearMap.toContinuousLinearMap
    { toFun := fun v : TangentSpace I x => homTensorRSCovDirHom (I := I) (M := M) g r a c Ψ x v d
      map_add' := fun v v' => by rw [homTensorRSCovDirHom_add, ContinuousLinearMap.add_apply]
      map_smul' := fun k v => by rw [homTensorRSCovDirHom_smul, ContinuousLinearMap.smul_apply]; rfl }

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The defining value of `homTensorRSCovGradDirCLM` at `v` is `(homTensorRSCovDirHom g r a c Ψ x v) d`. -/
@[simp] lemma homTensorRSCovGradDirCLM_apply (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) (x : M)
    (d : TensorRSSpace r a I x) (v : TangentSpace I x) :
    homTensorRSCovGradDirCLM (I := I) (M := M) g r a c Ψ x d v =
      homTensorRSCovDirHom (I := I) (M := M) g r a c Ψ x v d := by
  rw [homTensorRSCovGradDirCLM, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]

set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
/-- **The fibrewise second-order Hom-bundle section covariant gradient.** For a smooth full Hom-bundle
field `Ψ`, the gradient field value at `x` is the full Hom operator `T^{(r,a)} →L T^{(r,c+1)}` whose
slot-`0` reading along `v` of its `(r, c + 1)`-image is the directional second-order Hom-bundle covariant
derivative `(homTensorRSCovDirHom g r a c Ψ x v) d`, curried into the new leading covariant slot through
`covGradBundleEquiv r c x`.  The full-Hom analogue of `covGradGradSection` for tensors, one bundle up. -/
noncomputable def homTensorRSCovGradFieldFib (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) (x : M) :
    TensorRSSpace r a I x →L[ℝ] TensorRSSpace r (c + 1) I x :=
  haveI : FiniteDimensional ℝ (TensorRSSpace r a I x) :=
    inferInstanceAs (FiniteDimensional ℝ (Tensor0SSpace r I x →L[ℝ] Tensor0SSpace a I x))
  haveI : T2Space (TensorRSSpace r a I x) :=
    inferInstanceAs (T2Space (Tensor0SSpace r I x →L[ℝ] Tensor0SSpace a I x))
  LinearMap.toContinuousLinearMap
    { toFun := fun d =>
        covGradBundleEquiv (I := I) (M := M) r c x
          (homTensorRSCovGradDirCLM (I := I) (M := M) g r a c Ψ x d)
      map_add' := fun d₁ d₂ => by
        rw [← map_add (covGradBundleEquiv (I := I) (M := M) r c x)]
        refine congrArg (covGradBundleEquiv (I := I) (M := M) r c x) ?_
        refine ContinuousLinearMap.ext (fun v => ?_)
        rw [ContinuousLinearMap.add_apply, homTensorRSCovGradDirCLM_apply,
          homTensorRSCovGradDirCLM_apply, homTensorRSCovGradDirCLM_apply, map_add]
      map_smul' := fun k d => by
        rw [RingHom.id_apply, ← map_smul (covGradBundleEquiv (I := I) (M := M) r c x)]
        refine congrArg (covGradBundleEquiv (I := I) (M := M) r c x) ?_
        refine ContinuousLinearMap.ext (fun v => ?_)
        rw [ContinuousLinearMap.smul_apply, homTensorRSCovGradDirCLM_apply,
          homTensorRSCovGradDirCLM_apply, map_smul] }

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **The section covariant gradient field reads the gradient slot first.** Evaluating
`homTensorRSCovGradFieldFib Ψ x d` against a tuple `Fin.cons v0 vs` reads the leading direction `v0` off
the new covariant slot and returns the directional second-order Hom-bundle covariant derivative
`(homTensorRSCovariantDerivative (LeviCivita g) Ψ x v0) d`, evaluated at `vs`. -/
lemma homTensorRSCovGradFieldFib_apply_eval (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) (x : M)
    (d : TensorRSSpace r a I x) (Dlow : Tensor0SSpace r I x)
    (v0 : TangentSpace I x) (vs : Fin c → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (c + 1) I x from
          homTensorRSCovGradFieldFib (I := I) (M := M) g r a c Ψ x d) Dlow) (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace c I x from
          homTensorRSCovDirHom (I := I) (M := M) g r a c Ψ x v0 d) Dlow) vs := by
  letI : FiniteDimensional ℝ (TensorRSSpace r a I x) :=
    inferInstanceAs (FiniteDimensional ℝ (Tensor0SSpace r I x →L[ℝ] Tensor0SSpace a I x))
  letI : T2Space (TensorRSSpace r a I x) :=
    inferInstanceAs (T2Space (Tensor0SSpace r I x →L[ℝ] Tensor0SSpace a I x))
  have hval : (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (c + 1) I x from
        homTensorRSCovGradFieldFib (I := I) (M := M) g r a c Ψ x d) =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (c + 1) I x from
        covGradBundleEquiv (I := I) (M := M) r c x
          (homTensorRSCovGradDirCLM (I := I) (M := M) g r a c Ψ x d)) := by
    rw [homTensorRSCovGradFieldFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
      AddHom.coe_mk]
  rw [hval]
  rw [covGradBundleEquiv_apply_eval (I := I) (M := M) r c x
    (homTensorRSCovGradDirCLM (I := I) (M := M) g r a c Ψ x d) Dlow (Fin.cons v0 vs)]
  have htail : Matrix.vecTail (Fin.cons v0 vs : Fin (c + 1) → TangentSpace I x) = vs := by
    funext j; simp [Matrix.vecTail, Fin.cons_succ]
  have hhead : (Fin.cons v0 vs : Fin (c + 1) → TangentSpace I x) 0 = v0 := by simp [Fin.cons_zero]
  rw [htail, hhead, homTensorRSCovGradDirCLM_apply]

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **Base-point smoothness of the second-order Hom-bundle section gradient field (precise
infrastructure child).** If the full Hom-bundle field `Ψ` is smooth, then its second-order Hom-bundle
section covariant gradient field `x ↦ homTensorRSCovGradFieldFib g r a c Ψ x : T^{(r,a)} →L T^{(r,c+1)}`
is a smooth section of the second-order Hom-bundle `Hom(T^{(r,a)}, T^{(r,c+1)})`.

**Why this is TRUE.** This is the full-Hom analogue of `covGradSmoothSection`'s smoothness
(`CovGrad.Defs`), one bundle up.  The directional derivative operator
`homTensorRSCovariantDerivative (LeviCivita g) Ψ` is smooth in the base point — it is the `contMDiff`
field of the `ContMDiffCovariantDerivative` instance `homTensorRSCovariantDerivative_contMDiff`
(`SecondOrderHomBundle`) applied to the smooth section `Ψ` — landing in the covariant-gradient bundle
`Hom(TM, Hom(T^{(r,a)}, T^{(r,c)}))`; currying its new tangent slot into the Hom codomain through
`covGradBundleEquiv r c x` produces the smooth gradient field, exactly as `covGradSmoothSection` curries
the tensor directional derivative through `covGradBundleEquiv r s x`.

**Precise missing prerequisite (verified).** The currying step requires the **smooth-section transport**
of the slot-`0` curry equivalence at the second-order-Hom-bundle codomain level — a
`covGradBundleSmoothEquiv`-analogue identifying the covariant-gradient bundle
`Hom(TM, Hom(T^{(r,a)}, T^{(r,c)}))` with the operator bundle `Hom(T^{(r,a)}, T^{(r,c+1)})` as smooth
bundles.  That second-order-Hom-bundle smooth slot transport carries **no** API below this file (the
first-order `covGradBundleSmoothEquiv` is stated only for the `Tensor0SBundle` tower); building it is the
same multi-file second-order-Hom-bundle infrastructure node behind `slotExtendFullFib_contMDiff`.  Posited
here as one precise true infrastructure child.  Consumers transitively depend on `sorryAx`.

**Non-vacuity.** A degenerate (zero or discontinuous) gradient field is rejected: on a non-flat manifold
with a genuinely `x`-varying smooth `Ψ`, the second-order Hom-bundle covariant derivative is non-zero and
the gradient field varies continuously with `x`. -/
theorem homTensorRSCovGradField_contMDiff (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r (c + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r (c + 1) ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r (c + 1) I z) x
        (homTensorRSCovGradFieldFib (I := I) (M := M) g r a c Ψ x)) := by
  have hgrad : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] HomTensorRSModel r a c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] HomTensorRSModel r a c ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] HomTensorRSSpace r a c I z) x
        ((homTensorRSCovariantDerivative I M r a c (LeviCivita (I := I) g)).toFun
          (fun y : M => (Ψ y : HomTensorRSSpace r a c I y)) x)) := by
    haveI hcov : CovariantDerivative.ContMDiffCovariantDerivative
        (homTensorRSCovariantDerivative I M r a c (LeviCivita (I := I) g)) ∞ := inferInstance
    have hΨ' : ContMDiffOn I (I.prod 𝓘(ℝ, HomTensorRSModel r a c ℝ E)) ((∞ : WithTop ℕ∞) + 1)
        (fun x : M => TotalSpace.mk' (HomTensorRSModel r a c ℝ E)
          (E := fun z : M => HomTensorRSSpace r a c I z) x
          ((fun y : M => (Ψ y : HomTensorRSSpace r a c I y)) x)) Set.univ := by
      have h_le : ((∞ : WithTop ℕ∞) + 1) ≤ (∞ : WithTop ℕ∞) := by rw [ENat.coe_top_add_one]
      exact (hΨ.of_le h_le).contMDiffOn
    have hres := hcov.contMDiff.contMDiff
      (σ := fun y : M => (Ψ y : HomTensorRSSpace r a c I y)) hΨ'
    intro x
    exact (hres x (Set.mem_univ x)).contMDiffAt Filter.univ_mem
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (V₁ := fun z : M => TensorRSSpace r a I z) (V₂ := fun z : M => TensorRSSpace r (c + 1) I z)
    (φ := fun x => homTensorRSCovGradFieldFib (I := I) (M := M) g r a c Ψ x)
  intro Z
  have hG : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TensorRSSpace r c I z) x
        (homTensorRSCovGradDirCLM (I := I) (M := M) g r a c Ψ x (Z x))) := by
    apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
      (V₁ := TangentSpace I) (V₂ := fun z : M => TensorRSSpace r c I z)
      (φ := fun x => homTensorRSCovGradDirCLM (I := I) (M := M) g r a c Ψ x (Z x))
    intro Y
    have hstep1 : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
          (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x
          (show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x from
            ((homTensorRSCovariantDerivative I M r a c (LeviCivita (I := I) g)).toFun
              (fun y : M => (Ψ y : HomTensorRSSpace r a c I y)) x) (Y x))) :=
      ContMDiff.clm_bundle_apply (b := id) hgrad Y.contMDiff
    have hstep2 : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r c ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (TensorRSModel r c ℝ E)
          (E := fun z : M => TensorRSSpace r c I z) x
          ((show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x from
            ((homTensorRSCovariantDerivative I M r a c (LeviCivita (I := I) g)).toFun
              (fun y : M => (Ψ y : HomTensorRSSpace r a c I y)) x) (Y x)) (Z x))) :=
      ContMDiff.clm_bundle_apply (b := id) hstep1 Z.contMDiff
    refine hstep2.congr ?_
    intro x
    congr 1
  letI : NormedAddCommGroup (TensorRSModel r (c + 1) ℝ E) :=
    tensorRSModel_normedAddCommGroup r (c + 1)
  letI : NormedSpace ℝ (TensorRSModel r (c + 1) ℝ E) :=
    tensorRSModel_normedSpace r (c + 1)
  letI : TopologicalSpace (TotalSpace (TensorRSModel r (c + 1) ℝ E)
      (fun y : M => TensorRSSpace r (c + 1) I y)) :=
    tensorRSBundle_topology r (c + 1)
  letI : FiberBundle (TensorRSModel r (c + 1) ℝ E)
      (fun y : M => TensorRSSpace r (c + 1) I y) :=
    tensorRSBundle_fiber r (c + 1)
  letI : VectorBundle ℝ (TensorRSModel r (c + 1) ℝ E)
      (fun y : M => TensorRSSpace r (c + 1) I y) :=
    tensorRSBundle_vector r (c + 1)
  letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel r (c + 1) ℝ E)
      (fun y : M => TensorRSSpace r (c + 1) I y) I := tensorRSBundle_smooth ∞ r (c + 1)
  have hcomp :
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (c + 1) ℝ E)) ∞
        ((covGradBundleSmoothEquiv (I := I) (M := M) r c).toDiffeomorph ∘
          (fun x : M => (⟨x, homTensorRSCovGradDirCLM (I := I) (M := M) g r a c Ψ x (Z x)⟩ :
            TotalSpace (E →L[ℝ] TensorRSModel r c ℝ E)
              fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r c I y))) :=
    (covGradBundleSmoothEquiv (I := I) (M := M) r c).toDiffeomorph.contMDiff.comp hG
  refine hcomp.congr ?_
  intro x
  rw [Function.comp_apply,
    covGradBundleSmoothEquiv_toDiffeomorph_apply (I := I) (M := M) r c x
      (homTensorRSCovGradDirCLM (I := I) (M := M) g r a c Ψ x (Z x))]
  congr 1

/-! ## The directional and section-level covariant product rule for the full Hom-bundle action

The covariant derivative of the full Hom-bundle action `appFullRS Ψ W` (fibre value `Ψ x (W x)`) splits
— directionally and at a point — into the second-order Hom-bundle Leibniz
```
∇_v (Ψ · W) = (∇^Hom_v Ψ)(W x) + Ψ x (∇_v W),
```
an equation of `(r, c)`-tensors, where `∇^Hom Ψ = homTensorRSCovariantDerivative (LeviCivita g) Ψ`
(`SecondOrderHomBundle`) is the second-order Hom-bundle covariant derivative of `Ψ` and
`∇_v W = tensorCovDerivAt g r a W x v` is the `(r, a)`-tensor directional derivative.  This is the exact
full-fibre analogue of the codomain-only `tensorCovDerivAt_appCcRS_eq`, lifted from the post-composition
to the genuine full Hom-bundle action through the second-order Hom-bundle covariant derivative built in
`SecondOrderHomBundle`. -/

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **The directional covariant product rule for the full Hom-bundle action.** For a smooth full
Hom-bundle field `Ψ` (smoothness witnessed by `hΨ`) and a smooth `(r, a)`-tensor `W`, the directional
covariant derivative of the full Hom-bundle action `appFullRS Ψ hΨ W` decomposes as
```
∇_v (Ψ · W) = (∇^Hom_v Ψ)(W x) + Ψ x (∇_v W).
```
**Proof.** The fibre value of `appFullRS Ψ hΨ W` is `Ψ y (W y)` (`appFullRS_toSection`), so its directional
covariant derivative is `tensorRSCovariantDerivative … (fun y => Ψ y (W y)) x v`; the raw-section apply of
the second-order Hom-bundle covariant derivative
(`homTensorRSCovariantDerivative_apply_of_mdifferentiableAt`) reads this as
`(∇^Hom_v Ψ)(W x) + Ψ x (∇_v W)` (rearranging the product-rule subtraction). -/
theorem tensorCovDerivAt_appFullRS_eq (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x)))
    (W : SmoothCcTensor g r a) (x : M) (v : E) :
    (show TensorRSSpace r c I x from
        tensorCovDerivAt (I := I) (M := M) g r c (appFullRS (I := I) (M := M) g r a c Ψ hΨ W) x v) =
      (show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x from
          homTensorRSCovariantDerivative I M r a c (LeviCivita (I := I) g) Ψ x v) (W.toSection x) +
        (show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x from Ψ x)
          (show TensorRSSpace r a I x from tensorCovDerivAt (I := I) (M := M) g r a W x v) := by
  have hval : (fun y : M => (appFullRS (I := I) (M := M) g r a c Ψ hΨ W).toSection y) =
      (fun y : M => (show TensorRSSpace r a I y →L[ℝ] TensorRSSpace r c I y from Ψ y) (W.toSection y)) := by
    funext y; rw [appFullRS_toSection (I := I) (M := M) g r a c Ψ hΨ W y]
  have hΨ_diff : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) y (Ψ y)) x :=
    hΨ.contMDiffAt.mdifferentiableAt (by simp)
  have hW_diff : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r a ℝ E)
        (E := fun z : M => TensorRSSpace r a I z) y (W.toSection y)) x :=
    W.toSection.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  obtain ⟨Vsec, hVx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x v
  have hV_diff : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y (Vsec y)) x :=
    Vsec.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  rw [tensorCovDerivAt_def (I := I) (M := M) g r c (appFullRS (I := I) (M := M) g r a c Ψ hΨ W) x v,
    hval]
  rw [show v = (Vsec : Π z : M, TangentSpace I z) x from hVx.symm]
  have hprod := homTensorRSCovariantDerivative_apply_of_mdifferentiableAt I M r a c
    (LeviCivita (I := I) g) Ψ (fun y : M => W.toSection y) (fun y : M => Vsec y)
    hΨ_diff hW_diff hV_diff
  rw [eq_sub_iff_add_eq] at hprod
  rw [tensorCovDerivAt_def (I := I) (M := M) g r a W x ((Vsec : Π z : M, TangentSpace I z) x)]
  rw [← hprod]

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **Slot-`0` reading of the slot-extended full-Hom field on the curried gradient
`(covGrad g r a W).toSection x`.** The leading covariant passenger slot recovers, for `D` the covariant
gradient of the contracted `(r, a)`-section, the directional covariant derivative `(∇_{v0} W) d` — the
full-fibre analogue of `tensor0S_curry_covGrad_appCcRS_eq`. -/
theorem covGradBundleEquiv_symm_covGrad_appFullRS_eq (g : SmoothRiemannianMetric I M) (r a : ℕ)
    (W : SmoothCcTensor g r a) (x : M) (v0 : TangentSpace I x) :
    (covGradBundleEquiv (I := I) (M := M) r a x).symm
        ((covGrad (I := I) (M := M) g r a W).toSection x) v0 =
      (show TensorRSSpace r a I x from tensorCovDerivAt (I := I) (M := M) g r a W x v0) := by
  rw [covGrad_toSection_apply (I := I) (M := M) g r a W x, ContinuousLinearEquiv.symm_apply_apply]
  rfl

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **The section-level full-Hom covariant product rule (B-rule).** The covariant gradient of the full
Hom-bundle action `appFullRS Ψ W` of a smooth full Hom-bundle field `Ψ` on an `(r, a)`-tensor `W` splits
into two full Hom-bundle actions: the action of the section gradient field
`homTensorRSCovGradFieldFib Ψ` (a `T^{(r,a)} →L T^{(r,c+1)}` field) on `W`, plus the action of the
passenger-slot extension `slotExtendFull Ψ` (a `T^{(r,a+1)} →L T^{(r,c+1)}` field) on the gradient
`covGrad g r a W` (an `(r, a + 1)`-tensor):
```
covGrad g r (c + 1) (appFullRS Ψ W) =
  appFullRS (homTensorRSCovGradFieldFib Ψ) W + appFullRS (slotExtendFull Ψ) (covGrad g r a W).
```
The section-level packaging of the directional rule `tensorCovDerivAt_appFullRS_eq`, the exact full-fibre
analogue of `covGrad_appCcRS_eq`.  It is the carrier on which the full-Hom differentiated-tower induction
runs. -/
theorem covGrad_appFullRS_eq (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x)))
    (W : SmoothCcTensor g r a) :
    covGrad (I := I) (M := M) g r c (appFullRS (I := I) (M := M) g r a c Ψ hΨ W) =
      appFullRS (I := I) (M := M) g r a (c + 1)
          (fun x : M => homTensorRSCovGradFieldFib (I := I) (M := M) g r a c Ψ x)
          (homTensorRSCovGradField_contMDiff (I := I) (M := M) g r a c Ψ hΨ) W +
        appFullRS (I := I) (M := M) g r (a + 1) (c + 1)
          (fun x : M => slotExtendFullFib (I := I) (M := M) g r a c x (Ψ x))
          (slotExtendFullFib_contMDiff (I := I) (M := M) g r a c Ψ hΨ)
          (covGrad (I := I) (M := M) g r a W) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((appFullRS (I := I) (M := M) g r a (c + 1)
        (fun x : M => homTensorRSCovGradFieldFib (I := I) (M := M) g r a c Ψ x)
        (homTensorRSCovGradField_contMDiff (I := I) (M := M) g r a c Ψ hΨ) W +
      appFullRS (I := I) (M := M) g r (a + 1) (c + 1)
        (fun x : M => slotExtendFullFib (I := I) (M := M) g r a c x (Ψ x))
        (slotExtendFullFib_contMDiff (I := I) (M := M) g r a c Ψ hΨ)
        (covGrad (I := I) (M := M) g r a W)).toSection x) =
      (appFullRS (I := I) (M := M) g r a (c + 1)
          (fun x : M => homTensorRSCovGradFieldFib (I := I) (M := M) g r a c Ψ x)
          (homTensorRSCovGradField_contMDiff (I := I) (M := M) g r a c Ψ hΨ) W).toSection x +
        (appFullRS (I := I) (M := M) g r (a + 1) (c + 1)
          (fun x : M => slotExtendFullFib (I := I) (M := M) g r a c x (Ψ x))
          (slotExtendFullFib_contMDiff (I := I) (M := M) g r a c Ψ hΨ)
          (covGrad (I := I) (M := M) g r a W)).toSection x from rfl]
  apply ContinuousLinearMap.ext
  intro d
  rw [ContinuousLinearMap.add_apply]
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  beta_reduce
  rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]

  rw [covGrad_toSection_apply_eval (I := I) (M := M) g r c (appFullRS (I := I) (M := M) g r a c Ψ hΨ W) x
    d v]

  have hT1val : Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (c + 1) I x from
          (appFullRS (I := I) (M := M) g r a (c + 1)
            (fun y : M => homTensorRSCovGradFieldFib (I := I) (M := M) g r a c Ψ y)
            (homTensorRSCovGradField_contMDiff (I := I) (M := M) g r a c Ψ hΨ) W).toSection x) d) v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace c I x from
          homTensorRSCovDirHom (I := I) (M := M) g r a c Ψ x (v 0) (W.toSection x)) d)
        (Matrix.vecTail v) := by
    rw [appFullRS_toSection (I := I) (M := M) g r a (c + 1)
        (fun y : M => homTensorRSCovGradFieldFib (I := I) (M := M) g r a c Ψ y)
        (homTensorRSCovGradField_contMDiff (I := I) (M := M) g r a c Ψ hΨ) W x]
    rw [show v = Fin.cons (v 0) (Matrix.vecTail v) from (Fin.cons_self_tail v).symm]
    rw [homTensorRSCovGradFieldFib_apply_eval (I := I) (M := M) g r a c Ψ x (W.toSection x) d (v 0)
      (Matrix.vecTail v)]
    simp only [Fin.cons_zero, Matrix.vecTail]
    rw [show (Fin.cons (v 0) (v ∘ Fin.succ) ∘ Fin.succ) = v ∘ Fin.succ from
      funext (fun j => by simp [Fin.cons_succ])]
  rw [hT1val]

  have hT2val : Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (c + 1) I x from
          (appFullRS (I := I) (M := M) g r (a + 1) (c + 1)
            (fun y : M => slotExtendFullFib (I := I) (M := M) g r a c y (Ψ y))
            (slotExtendFullFib_contMDiff (I := I) (M := M) g r a c Ψ hΨ)
            (covGrad (I := I) (M := M) g r a W)).toSection x) d) v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace c I x from
          (show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x from Ψ x)
            (show TensorRSSpace r a I x from
              tensorCovDerivAt (I := I) (M := M) g r a W x (v 0))) d)
        (Matrix.vecTail v) := by
    rw [appFullRS_toSection (I := I) (M := M) g r (a + 1) (c + 1)
        (fun y : M => slotExtendFullFib (I := I) (M := M) g r a c y (Ψ y))
        (slotExtendFullFib_contMDiff (I := I) (M := M) g r a c Ψ hΨ)
        (covGrad (I := I) (M := M) g r a W) x]
    rw [show v = Fin.cons (v 0) (Matrix.vecTail v) from (Fin.cons_self_tail v).symm]
    rw [slotExtendFullFib_apply_eval (I := I) (M := M) g r a c x (Ψ x)
      ((covGrad (I := I) (M := M) g r a W).toSection x) d (v 0) (Matrix.vecTail v)]
    rw [covGradBundleEquiv_symm_covGrad_appFullRS_eq (I := I) (M := M) g r a W x (v 0)]
    simp only [Fin.cons_zero, Matrix.vecTail]
    rw [show (Fin.cons (v 0) (v ∘ Fin.succ) ∘ Fin.succ) = v ∘ Fin.succ from
      funext (fun j => by simp [Fin.cons_succ])]
  rw [hT2val]

  rw [tensorCovDerivAt_appFullRS_eq (I := I) (M := M) g r a c Ψ hΨ W x (v 0)]
  rw [ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply,
    homTensorRSCovDirHom]

/-! ## The per-point fibrewise Cauchy–Schwarz and the uniform contraction envelope

The fibre value `Ψ x (W x)` of the full Hom-bundle action is a continuous-linear-map evaluation between
finite-dimensional tensor fibres; the intrinsic-fibre-norm / `g`-bundle-norm bridge turns the fibre
operator-norm bound `‖φ v‖ ≤ ‖φ‖ · ‖v‖` into the squared `rfns` bound (`HomTensorRSRiemannian`,
`homTensorRS_riemannianFiberNormSq_clm_apply_le`).  The base-point continuity of the `g`-fibre operator
norm of `Ψ` (the genuinely-irreducible analytic primitive, posited in `HomTensorRSRiemannian`) then yields
the continuous per-point envelope, uniformised over the compact `M`. -/

set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
/-- **The continuous per-point `g`-fibre-operator contraction envelope of a smooth full Hom-bundle
section.** For a *fixed* smooth full Hom-bundle field `Ψ` on a closed Riemannian manifold there is a
continuous nonnegative `Cop : M → ℝ` with `rfns(Ψ x v) ≤ Cop x · rfns(v)` at every `x` and every
`(r, a)`-tensor fibre value `v`.  The consumer alias of the payoff
`exists_continuous_riemannianFiberNormSq_homTensorRS_section_clm_le` (`HomTensorRSRiemannian`); consumers
transitively depend on its `sorryAx` (the posited operator-norm continuity
`exists_uniform_homTensorRS_opNorm_sq`). -/
theorem exists_continuous_riemannianFiberNormSq_homSection_clm_le
    (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    ∃ Cop : M → ℝ, Continuous Cop ∧ (∀ x : M, 0 ≤ Cop x) ∧
      ∀ (x : M) (v : TensorRSSpace r a I x),
        riemannianFiberNormSq (I := I) (M := M) g r c x (Ψ x v) ≤
          Cop x * riemannianFiberNormSq (I := I) (M := M) g r a x v :=
  exists_continuous_riemannianFiberNormSq_homTensorRS_section_clm_le
    (g := g) (r := r) (a := a) (c := c) (Ψ := Ψ) (hΨ := hΨ)

set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
/-- **The uniform `g`-fibre-operator contraction bound of a smooth full Hom-bundle section.** For a
*fixed* smooth full Hom-bundle field `Ψ` on a closed Riemannian manifold there is a single nonnegative
constant `C`, uniform over `M`, with `rfns(Ψ x v) ≤ C · rfns(v)` for every `x` and fibre value `v`.  The
consumer alias of the uniform payoff `exists_uniform_riemannianFiberNormSq_homTensorRS_section_clm_le`
(`HomTensorRSRiemannian`). -/
theorem exists_uniform_riemannianFiberNormSq_homSection_clm_le
    (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : M) (v : TensorRSSpace r a I x),
      riemannianFiberNormSq (I := I) (M := M) g r c x (Ψ x v) ≤
        C * riemannianFiberNormSq (I := I) (M := M) g r a x v :=
  exists_uniform_riemannianFiberNormSq_homTensorRS_section_clm_le
    (g := g) (r := r) (a := a) (c := c) (Ψ := Ψ) (hΨ := hΨ)

set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
/-- **The uniform full-Hom contraction bound (the section-applied form).** For a *fixed* smooth full
Hom-bundle field `Ψ` on a closed Riemannian manifold there is a single nonnegative constant `C`, uniform
over `M`, with `rfns(Ψ x (W x)) ≤ C · rfns(W x)` for every smooth `(r, a)`-tensor `W` and every point `x`.
The full-fibre analogue of the *proved* codomain-only `exists_uniform_riemannianFiberNormSq_appCcRS_le`.
**Proof.** The fibre value of `appFullRS Ψ W` at `x` is `Ψ x (W x)` (`appFullRS_toSection`); specialise the
per-fibre-value uniform `g`-fibre-operator contraction bound
`exists_uniform_riemannianFiberNormSq_homSection_clm_le` to `v = W.toSection x`. -/
theorem exists_uniform_riemannianFiberNormSq_appFullRS_le
    (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (W : SmoothCcTensor g r a) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g r c x
          ((appFullRS (I := I) (M := M) g r a c Ψ hΨ W).toSection x) ≤
        C * riemannianFiberNormSq (I := I) (M := M) g r a x (W.toSection x) := by
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_uniform_riemannianFiberNormSq_homSection_clm_le (I := I) (M := M) g r a c Ψ hΨ
  refine ⟨C, hC_nn, fun W x => ?_⟩
  rw [appFullRS_toSection (I := I) (M := M) g r a c Ψ hΨ W x]
  exact hC x (W.toSection x)

/-! ## The full Hom-bundle operator-field normal form of a differentiated tower

A smooth full Hom-bundle field is packaged as a `ContMDiffSection` of the second-order Hom-bundle
`Hom(T^{(r,a)}, T^{(r,c)})` — `HomTensorRSField r a c I` — which carries the full `AddCommGroup` /
`Module` structure (its `+` / `-` / `•` are the fibrewise operations, smoothness preserved) and a
`.contMDiff` smoothness witness feeding `appFullRS`.  `appFullSec` is the full Hom-bundle action of such a
section, and the gradient field `homTensorRSCovGradSec` / slot extension `slotExtendFullSec` / rank-casts
are packaged as section operators.  Over these, the normal form `NormalFormFull` of a
recursively-differentiated tower whose order-`0` base is `appFullSec Q₀` runs the same single-index
telescoping induction as the codomain-only `NormalFormRS`. -/

/-- A smooth full Hom-bundle field, as a `ContMDiffSection` of the second-order Hom-bundle. -/
abbrev HomTensorRSField (r a c : ℕ) (I : ModelWithCorners ℝ E H)
    [IsManifold I ∞ M] : Type _ :=
  Cₛ^∞⟮I; HomTensorRSModel r a c ℝ E, (fun x : M => HomTensorRSSpace r a c I x)⟯

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **The full Hom-bundle action of a smooth Hom-bundle field section.** The action `appFullRS` of the
field `⇑Q` (smoothness `Q.contMDiff`) on an `(r, a)`-tensor `W`. -/
noncomputable def appFullSec (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) r a c I) (W : SmoothCcTensor g r a) : SmoothCcTensor g r c :=
  appFullRS (I := I) (M := M) g r a c (fun x : M => Q x) Q.contMDiff W

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The fibre value of `appFullSec Q W` at `x` is `Q x (W x)`. -/
@[simp] lemma appFullSec_toSection (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) r a c I) (W : SmoothCcTensor g r a) (x : M) :
    (appFullSec (I := I) (M := M) g r a c Q W).toSection x =
      (show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x from Q x) (W.toSection x) :=
  rfl

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The full Hom-bundle action is additive in the operator-field section. -/
theorem appFullSec_add_left (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Qa Qb : HomTensorRSField (E := E) (M := M) r a c I) (W : SmoothCcTensor g r a) :
    appFullSec (I := I) (M := M) g r a c (Qa + Qb) W =
      appFullSec (I := I) (M := M) g r a c Qa W + appFullSec (I := I) (M := M) g r a c Qb W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((appFullSec (I := I) (M := M) g r a c Qa W +
        appFullSec (I := I) (M := M) g r a c Qb W).toSection x) =
      (appFullSec (I := I) (M := M) g r a c Qa W).toSection x +
        (appFullSec (I := I) (M := M) g r a c Qb W).toSection x from rfl]
  rw [appFullSec_toSection, appFullSec_toSection, appFullSec_toSection]
  rw [show ((Qa + Qb) x : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) =
      (Qa x : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) +
        (Qb x : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) from by
    rw [ContMDiffSection.coe_add, Pi.add_apply]]
  rw [ContinuousLinearMap.add_apply]

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The full Hom-bundle action is zero in the zero operator-field section. -/
theorem appFullSec_zero_left (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (W : SmoothCcTensor g r a) :
    appFullSec (I := I) (M := M) g r a c (0 : HomTensorRSField (E := E) (M := M) r a c I) W = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [appFullSec_toSection]
  rw [show ((0 : HomTensorRSField (E := E) (M := M) r a c I) x :
      TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) = 0 from by
    rw [ContMDiffSection.coe_zero, Pi.zero_apply]]
  rw [ContinuousLinearMap.zero_apply]
  rfl

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The full Hom-bundle action distributes over subtraction in the operator-field section. -/
theorem appFullSec_sub_left (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Qa Qb : HomTensorRSField (E := E) (M := M) r a c I) (W : SmoothCcTensor g r a) :
    appFullSec (I := I) (M := M) g r a c (Qa - Qb) W =
      appFullSec (I := I) (M := M) g r a c Qa W - appFullSec (I := I) (M := M) g r a c Qb W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((appFullSec (I := I) (M := M) g r a c Qa W -
        appFullSec (I := I) (M := M) g r a c Qb W).toSection x) =
      (appFullSec (I := I) (M := M) g r a c Qa W).toSection x -
        (appFullSec (I := I) (M := M) g r a c Qb W).toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [appFullSec_toSection, appFullSec_toSection, appFullSec_toSection]
  rw [show ((Qa - Qb) x : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) =
      (Qa x : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) -
        (Qb x : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) from by
    rw [ContMDiffSection.coe_sub, Pi.sub_apply]]
  rw [ContinuousLinearMap.sub_apply]

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **The second-order Hom-bundle section covariant gradient field, as a section.** Packages the
fibrewise gradient `homTensorRSCovGradFieldFib (⇑Q)` with its (posited) smoothness
`homTensorRSCovGradField_contMDiff` into a `Hom(T^{(r,a)}, T^{(r,c+1)})`-bundle section. -/
noncomputable def homTensorRSCovGradSec (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) r a c I) : HomTensorRSField (E := E) (M := M) r a (c + 1) I where
  toFun := fun x : M => homTensorRSCovGradFieldFib (I := I) (M := M) g r a c (fun y : M => Q y) x
  contMDiff_toFun :=
    homTensorRSCovGradField_contMDiff (I := I) (M := M) g r a c (fun y : M => Q y) Q.contMDiff

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The fibre value of `homTensorRSCovGradSec Q` at `x` is `homTensorRSCovGradFieldFib (⇑Q) x`. -/
@[simp] lemma homTensorRSCovGradSec_apply (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) r a c I) (x : M) :
    (show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r (c + 1) I x from
        homTensorRSCovGradSec (I := I) (M := M) g r a c Q x) =
      homTensorRSCovGradFieldFib (I := I) (M := M) g r a c (fun y : M => Q y) x := rfl

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **The slot-extended full-Hom field, as a section.** Packages the fibrewise slot extension
`slotExtendFullFib … (⇑Q)` with its (posited) smoothness `slotExtendFullFib_contMDiff` into a
`Hom(T^{(r,a+1)}, T^{(r,c+1)})`-bundle section. -/
noncomputable def slotExtendFullSec (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) r a c I) :
    HomTensorRSField (E := E) (M := M) r (a + 1) (c + 1) I where
  toFun := fun x : M => slotExtendFullFib (I := I) (M := M) g r a c x (Q x)
  contMDiff_toFun :=
    slotExtendFullFib_contMDiff (I := I) (M := M) g r a c (fun y : M => Q y) Q.contMDiff

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The fibre value of `slotExtendFullSec Q` at `x` is `slotExtendFullFib … (Q x)`. -/
@[simp] lemma slotExtendFullSec_apply (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) r a c I) (x : M) :
    (show TensorRSSpace r (a + 1) I x →L[ℝ] TensorRSSpace r (c + 1) I x from
        slotExtendFullSec (I := I) (M := M) g r a c Q x) =
      slotExtendFullFib (I := I) (M := M) g r a c x (Q x) := rfl

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **The section-level full-Hom covariant product rule (section form).** The covariant gradient of the
full Hom-bundle action of a section `Q` on `W` splits into the action of the gradient section
`homTensorRSCovGradSec Q` on `W` plus the action of the slot extension `slotExtendFullSec Q` on the
gradient `covGrad g r a W`.  The section repackaging of `covGrad_appFullRS_eq`. -/
theorem covGrad_appFullSec_eq (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) r a c I) (W : SmoothCcTensor g r a) :
    covGrad (I := I) (M := M) g r c (appFullSec (I := I) (M := M) g r a c Q W) =
      appFullSec (I := I) (M := M) g r a (c + 1) (homTensorRSCovGradSec (I := I) (M := M) g r a c Q) W +
        appFullSec (I := I) (M := M) g r (a + 1) (c + 1) (slotExtendFullSec (I := I) (M := M) g r a c Q)
          (covGrad (I := I) (M := M) g r a W) :=
  covGrad_appFullRS_eq (I := I) (M := M) g r a c (fun x : M => Q x) Q.contMDiff W

/-! ### Rank casts of Hom-bundle field sections -/

set_option linter.unusedSectionVars false in
/-- **Recast of the Hom-bundle codomain index `c`.** -/
def castHomTgt {c c' : ℕ} (r a : ℕ) (h : c = c')
    (Q : HomTensorRSField (E := E) (M := M) r a c I) :
    HomTensorRSField (E := E) (M := M) r a c' I :=
  h ▸ Q

set_option linter.unusedSectionVars false in
/-- **Recast of the Hom-bundle source index `a`.** -/
def castHomSrc {a a' : ℕ} (r c : ℕ) (h : a = a')
    (Q : HomTensorRSField (E := E) (M := M) r a c I) :
    HomTensorRSField (E := E) (M := M) r a' c I :=
  h ▸ Q

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **Recast of a full-Hom section action through source- and codomain-index equalities.** The rank-cast
of `appFullSec Q V` along a codomain equality equals the action of the doubly-recast field section on the
recast tensor — the full-Hom analogue of `appCcRS_castRankCc_db`. -/
theorem appFullSec_castRankCc_db {a a' c c' : ℕ} (g : SmoothRiemannianMetric I M) (r : ℕ)
    (ha : a = a') (hc : c = c')
    (Q : HomTensorRSField (E := E) (M := M) r a c I) (V : SmoothCcTensor g r a) :
    castRankCc_db g r hc (appFullSec (I := I) (M := M) g r a c Q V) =
      appFullSec (I := I) (M := M) g r a' c' (castHomSrc (E := E) (M := M) r c' ha
        (castHomTgt (E := E) (M := M) r a hc Q)) (castRankCc_db g r ha V) := by
  subst ha; subst hc; rfl

/-! ### The full Hom-bundle operator-field normal form

The tower may **raise** the codomain by a fixed base offset `d` at order `0` (the differentiated-curvature
`(∇R)·` tower raises by `d = 1`; the pure-Riemann tower keeps `d = 0`): `op p rr : SmoothCcTensor g r rr →
SmoothCcTensor g r (rr + d + p)`, base `op 0 rr W = appFullSec Q₀ W` with `Q₀ : Hom(T^{(r,rr)},
T^{(r,rr+d)})`.  The normal form expresses `op p rr W` as a finite sum of full Hom-bundle actions of fixed
field sections `Q k : Hom(T^{(r,rr+k)}, T^{(r,rr+d+p)})` on the covariant jets `∇^k W`, `k < p + 1`. -/

set_option linter.unusedSectionVars false in
/-- **The full Hom-bundle operator-field normal form of a base-raising differentiated tower at order
`p`, valence `r`, width `rr`, base offset `d`.** The order-`p` tower value `op p rr W` decomposes as a
finite sum of full Hom-bundle actions of fixed smooth full Hom-bundle field sections
`Q k : Hom(T^{(r,rr+k)}, T^{(r,rr+d+p)})` on the covariant jets `∇^k W` of the contracted `(r, rr)`-section,
`k < p + 1`. -/
def NormalFormFull (g : SmoothRiemannianMetric I M) (r d : ℕ)
    (op : ∀ (p rr : ℕ), SmoothCcTensor g r rr → SmoothCcTensor g r (rr + d + p))
    (p rr : ℕ) : Prop :=
  ∃ Q : (k : ℕ) → HomTensorRSField (E := E) (M := M) r (rr + k) (rr + d + p) I,
    ∀ W : SmoothCcTensor g r rr,
      op p rr W =
        ∑ k ∈ Finset.range (p + 1),
          appFullSec (I := I) (M := M) g r (rr + k) (rr + d + p) (Q k) (iteratedCovGrad g r rr k W)

set_option linter.unusedSectionVars false in
/-- **The order-`0` base factorisation is the order-`0` full Hom normal form.** If
`op 0 rr W = appFullSec Q₀ W` for a fixed smooth Hom field section `Q₀ : Hom(T^{(r,rr)}, T^{(r,rr+d+0)})`,
then `op` admits the full Hom operator-field normal form at order `0`, width `rr`. -/
theorem normalForm_zeroFull (g : SmoothRiemannianMetric I M) (r d : ℕ)
    (op : ∀ (p rr : ℕ), SmoothCcTensor g r rr → SmoothCcTensor g r (rr + d + p))
    (rr : ℕ) (Q₀ : HomTensorRSField (E := E) (M := M) r (rr + 0) (rr + d + 0) I)
    (hbase : ∀ W : SmoothCcTensor g r rr,
      op 0 rr W = appFullSec (I := I) (M := M) g r (rr + 0) (rr + d + 0) Q₀ W) :
    NormalFormFull (E := E) (I := I) (M := M) g r d op 0 rr := by
  refine ⟨fun k => match k with | 0 => Q₀ | (_ + 1) => 0, fun W => ?_⟩
  rw [hbase W, Finset.sum_range_one]
  rfl

set_option linter.unusedSectionVars false in
/-- **The gradient of a full-Hom normal-form sum expands termwise** through the section product rule
`covGrad_appFullSec_eq`: each `appFullSec (Q k) (∇^k W)` contributes the gradient-section action
`appFullSec (homTensorRSCovGradSec (Q k)) (∇^k W)` plus the slot-extended action
`appFullSec (slotExtendFullSec (Q k)) (∇^{k+1} W)`. -/
theorem covGrad_normalFormFull_sum (g : SmoothRiemannianMetric I M) (r d p rr : ℕ)
    (Q : (k : ℕ) → HomTensorRSField (E := E) (M := M) r (rr + k) (rr + d + p) I)
    (W : SmoothCcTensor g r rr) :
    covGrad (I := I) (M := M) g r (rr + d + p)
        (∑ k ∈ Finset.range (p + 1),
          appFullSec (I := I) (M := M) g r (rr + k) (rr + d + p) (Q k) (iteratedCovGrad g r rr k W)) =
      ∑ k ∈ Finset.range (p + 1),
        (appFullSec (I := I) (M := M) g r (rr + k) (rr + d + (p + 1))
            (homTensorRSCovGradSec (I := I) (M := M) g r (rr + k) (rr + d + p) (Q k))
            (iteratedCovGrad g r rr k W) +
          appFullSec (I := I) (M := M) g r (rr + (k + 1)) (rr + d + (p + 1))
            (slotExtendFullSec (I := I) (M := M) g r (rr + k) (rr + d + p) (Q k))
            (iteratedCovGrad g r rr (k + 1) W)) := by
  rw [covGrad_finset_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [covGrad_appFullSec_eq (I := I) (M := M) g r (rr + k) (rr + d + p) (Q k)
    (iteratedCovGrad g r rr k W)]
  rw [show covGrad (I := I) (M := M) g r (rr + k) (iteratedCovGrad g r rr k W) =
      iteratedCovGrad g r rr (k + 1) W from (iteratedCovGrad_succ g r rr k W).symm]
  rfl

set_option linter.unusedSectionVars false in
/-- **The rank-cast lower-tower full-Hom normal form on `∇W` re-expressed in canonical jets.** Each
summand `cast(appFullSec (Q k) (∇^k(∇W)))` of `cast(op p (rr + 1) (∇W))` recasts to a full-Hom action on
the canonical jet `∇^{k+1} W` — the full-Hom analogue of `castRankCc_appCcRS_iteratedCovGrad_covGrad`. -/
theorem castRankCc_appFullSec_iteratedCovGrad_covGrad (g : SmoothRiemannianMetric I M) (r d p rr k : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) r ((rr + 1) + k) ((rr + 1) + d + p) I)
    (W : SmoothCcTensor g r rr) :
    castRankCc_db g r (by omega : (rr + 1) + d + p = rr + d + (p + 1))
        (appFullSec (I := I) (M := M) g r ((rr + 1) + k) ((rr + 1) + d + p) Q
          (iteratedCovGrad g r (rr + 1) k (covGrad g r rr W))) =
      appFullSec (I := I) (M := M) g r (rr + (k + 1)) (rr + d + (p + 1))
        (castHomSrc (E := E) (M := M) r (rr + d + (p + 1)) (by omega : (rr + 1) + k = rr + (k + 1))
          (castHomTgt (E := E) (M := M) r ((rr + 1) + k)
            (by omega : (rr + 1) + d + p = rr + d + (p + 1)) Q))
        (iteratedCovGrad g r rr (k + 1) W) := by
  rw [appFullSec_castRankCc_db (E := E) g r (by omega : (rr + 1) + k = rr + (k + 1))
    (by omega : (rr + 1) + d + p = rr + d + (p + 1)) Q
    (iteratedCovGrad g r (rr + 1) k (covGrad g r rr W))]
  congr 1
  apply eq_of_heq
  refine HEq.trans ?_ (iteratedCovGrad_covGrad_comm_heq' g r rr k W)
  exact castRankCc_db_heq g r (by omega : (rr + 1) + k = rr + (k + 1))
    (iteratedCovGrad g r (rr + 1) k (covGrad g r rr W))

set_option linter.unusedSectionVars false in
/-- **The full Hom normal form propagates up the differentiated tower.** If order `p` admits the
full-Hom operator-field normal form at *every* width, then so does order `p + 1` at width `rr`.  The new
field sections are built from the order-`p` ones by one second-order Hom-bundle section gradient, one
passenger-slot extension, and the rank-cast lower-tower coefficient — the three contributions of the exact
covariant Leibniz, with the non-cancelling slot-mismatch term landing on the new top jet `∇^{p+1} W`.  The
full-Hom mirror of `normalFormRS_succ`. -/
theorem normalFormFull_succ (g : SmoothRiemannianMetric I M) (r d : ℕ)
    (op : ∀ (p rr : ℕ), SmoothCcTensor g r rr → SmoothCcTensor g r (rr + d + p))
    (covGrad_op : ∀ (p rr : ℕ) (W : SmoothCcTensor g r rr),
      covGrad g r (rr + d + p) (op p rr W) =
        op (p + 1) rr W +
          castRankCc_db g r (by omega : (rr + 1) + d + p = rr + d + (p + 1))
            (op p (rr + 1) (covGrad g r rr W)))
    (p : ℕ) (hp : ∀ rr, NormalFormFull (E := E) (I := I) (M := M) g r d op p rr) (rr : ℕ) :
    NormalFormFull (E := E) (I := I) (M := M) g r d op (p + 1) rr := by
  classical
  obtain ⟨Qr, hQr⟩ := hp rr
  obtain ⟨Qr1, hQr1⟩ := hp (rr + 1)

  set Tk : (k : ℕ) → HomTensorRSField (E := E) (M := M) r (rr + (k + 1)) (rr + d + (p + 1)) I := fun k =>
    slotExtendFullSec (I := I) (M := M) g r (rr + k) (rr + d + p) (Qr k) -
      castHomSrc (E := E) (M := M) r (rr + d + (p + 1)) (by omega : (rr + 1) + k = rr + (k + 1))
        (castHomTgt (E := E) (M := M) r ((rr + 1) + k)
          (by omega : (rr + 1) + d + p = rr + d + (p + 1)) (Qr1 k))
    with hTk_def
  refine ⟨fun j => match j with
    | 0 => homTensorRSCovGradSec (I := I) (M := M) g r (rr + 0) (rr + d + p) (Qr 0)
    | (k + 1) =>
        (if h : k + 1 < p + 1 then
          homTensorRSCovGradSec (I := I) (M := M) g r (rr + (k + 1)) (rr + d + p) (Qr (k + 1))
          else 0) + Tk k, ?_⟩
  intro W

  have hrec : op (p + 1) rr W =
      covGrad g r (rr + d + p) (op p rr W) -
        castRankCc_db g r (by omega : (rr + 1) + d + p = rr + d + (p + 1))
          (op p (rr + 1) (covGrad g r rr W)) := by
    rw [covGrad_op p rr W]; abel
  rw [hrec, hQr W]

  rw [covGrad_normalFormFull_sum (I := I) (M := M) g r d p rr Qr W]

  rw [hQr1 (covGrad g r rr W), castRankCc_db_finset_sum]
  rw [show (∑ k ∈ Finset.range (p + 1),
        castRankCc_db g r (by omega : (rr + 1) + d + p = rr + d + (p + 1))
          (appFullSec (I := I) (M := M) g r ((rr + 1) + k) ((rr + 1) + d + p) (Qr1 k)
            (iteratedCovGrad g r (rr + 1) k (covGrad g r rr W)))) =
      ∑ k ∈ Finset.range (p + 1),
        appFullSec (I := I) (M := M) g r (rr + (k + 1)) (rr + d + (p + 1))
          (castHomSrc (E := E) (M := M) r (rr + d + (p + 1)) (by omega : (rr + 1) + k = rr + (k + 1))
            (castHomTgt (E := E) (M := M) r ((rr + 1) + k)
              (by omega : (rr + 1) + d + p = rr + d + (p + 1)) (Qr1 k)))
          (iteratedCovGrad g r rr (k + 1) W) from
    Finset.sum_congr rfl (fun k _ =>
      castRankCc_appFullSec_iteratedCovGrad_covGrad (E := E) (I := I) (M := M) g r d p rr k (Qr1 k) W)]

  rw [Finset.sum_add_distrib]

  rw [Finset.sum_range_succ' (fun j =>
    appFullSec (I := I) (M := M) g r (rr + j) (rr + d + (p + 1))
      ((match j with
        | 0 => homTensorRSCovGradSec (I := I) (M := M) g r (rr + 0) (rr + d + p) (Qr 0)
        | (k + 1) =>
            (if h : k + 1 < p + 1 then
              homTensorRSCovGradSec (I := I) (M := M) g r (rr + (k + 1)) (rr + d + p) (Qr (k + 1))
              else 0) + Tk k))
      (iteratedCovGrad g r rr j W)) (p + 1)]

  rw [show (∑ k ∈ Finset.range (p + 1),
        appFullSec (I := I) (M := M) g r (rr + (k + 1)) (rr + d + (p + 1))
          ((if h : k + 1 < p + 1 then
            homTensorRSCovGradSec (I := I) (M := M) g r (rr + (k + 1)) (rr + d + p) (Qr (k + 1))
            else 0) + Tk k)
          (iteratedCovGrad g r rr (k + 1) W)) =
      (∑ k ∈ Finset.range (p + 1),
        appFullSec (I := I) (M := M) g r (rr + (k + 1)) (rr + d + (p + 1))
          (if h : k + 1 < p + 1 then
            homTensorRSCovGradSec (I := I) (M := M) g r (rr + (k + 1)) (rr + d + p) (Qr (k + 1))
            else 0)
          (iteratedCovGrad g r rr (k + 1) W)) +
      (∑ k ∈ Finset.range (p + 1),
        appFullSec (I := I) (M := M) g r (rr + (k + 1)) (rr + d + (p + 1)) (Tk k)
          (iteratedCovGrad g r rr (k + 1) W)) from by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [appFullSec_add_left]]

  rw [show (∑ k ∈ Finset.range (p + 1),
        appFullSec (I := I) (M := M) g r (rr + (k + 1)) (rr + d + (p + 1)) (Tk k)
          (iteratedCovGrad g r rr (k + 1) W)) =
      (∑ k ∈ Finset.range (p + 1),
        appFullSec (I := I) (M := M) g r (rr + (k + 1)) (rr + d + (p + 1))
          (slotExtendFullSec (I := I) (M := M) g r (rr + k) (rr + d + p) (Qr k))
          (iteratedCovGrad g r rr (k + 1) W)) -
      (∑ k ∈ Finset.range (p + 1),
        appFullSec (I := I) (M := M) g r (rr + (k + 1)) (rr + d + (p + 1))
          (castHomSrc (E := E) (M := M) r (rr + d + (p + 1)) (by omega : (rr + 1) + k = rr + (k + 1))
            (castHomTgt (E := E) (M := M) r ((rr + 1) + k)
              (by omega : (rr + 1) + d + p = rr + d + (p + 1)) (Qr1 k)))
          (iteratedCovGrad g r rr (k + 1) W)) from by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hTk_def, appFullSec_sub_left]]

  rw [show (∑ k ∈ Finset.range (p + 1),
        appFullSec (I := I) (M := M) g r (rr + (k + 1)) (rr + d + (p + 1))
          (if h : k + 1 < p + 1 then
            homTensorRSCovGradSec (I := I) (M := M) g r (rr + (k + 1)) (rr + d + p) (Qr (k + 1))
            else 0)
          (iteratedCovGrad g r rr (k + 1) W)) =
      ∑ k ∈ Finset.range p,
        appFullSec (I := I) (M := M) g r (rr + (k + 1)) (rr + d + (p + 1))
          (homTensorRSCovGradSec (I := I) (M := M) g r (rr + (k + 1)) (rr + d + p) (Qr (k + 1)))
          (iteratedCovGrad g r rr (k + 1) W) from by
    rw [Finset.sum_range_succ]
    rw [dif_neg (by omega : ¬ (p + 1 < p + 1)), appFullSec_zero_left, add_zero]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [dif_pos (by simp only [Finset.mem_range] at hk; omega : k + 1 < p + 1)]]

  rw [Finset.sum_range_succ' (fun k =>
    appFullSec (I := I) (M := M) g r (rr + k) (rr + d + (p + 1))
      (homTensorRSCovGradSec (I := I) (M := M) g r (rr + k) (rr + d + p) (Qr k))
      (iteratedCovGrad g r rr k W)) p]

  abel

set_option linter.unusedSectionVars false in
/-- **The full Hom operator-field normal form holds at every order.** A recursively-differentiated tower
`op` whose single-step covariant Leibniz is the exact remainder (`covGrad_op`) and whose order-`0` base is
a fixed full-Hom-section action at every width (`hbase`) admits the full Hom operator-field normal form at
every order `p` and width `rr`.  The full-Hom mirror of `normalForm_of_baseRS`. -/
theorem normalFormFull_of_base (g : SmoothRiemannianMetric I M) (r d : ℕ)
    (op : ∀ (p rr : ℕ), SmoothCcTensor g r rr → SmoothCcTensor g r (rr + d + p))
    (covGrad_op : ∀ (p rr : ℕ) (W : SmoothCcTensor g r rr),
      covGrad g r (rr + d + p) (op p rr W) =
        op (p + 1) rr W +
          castRankCc_db g r (by omega : (rr + 1) + d + p = rr + d + (p + 1))
            (op p (rr + 1) (covGrad g r rr W)))
    (Q₀ : ∀ rr : ℕ, HomTensorRSField (E := E) (M := M) r (rr + 0) (rr + d + 0) I)
    (hbase : ∀ (rr : ℕ) (W : SmoothCcTensor g r rr),
      op 0 rr W = appFullSec (I := I) (M := M) g r (rr + 0) (rr + d + 0) (Q₀ rr) W)
    (p : ℕ) : ∀ rr : ℕ, NormalFormFull (E := E) (I := I) (M := M) g r d op p rr := by
  induction p with
  | zero => exact fun rr => normalForm_zeroFull (E := E) (I := I) (M := M) g r d op rr (Q₀ rr) (hbase rr)
  | succ p ih =>
      exact fun rr => normalFormFull_succ (E := E) (I := I) (M := M) g r d op covGrad_op p ih rr

set_option linter.unusedSectionVars false in
set_option maxHeartbeats 1600000 in
/-- **The per-order, per-width jet envelope of a differentiated tower from its full Hom normal form.** If
`op p rr` admits the full Hom operator-field normal form, then its intrinsic squared fibre norm is bounded,
uniformly over the compact `M`, by a nonnegative constant times the order-`≤ p` covariant jet of the
contracted section:
```
rfns(op p rr W)(x) ≤ kappa · ∑_{q < p + 1} rfns(∇^q W)(x).
```
Each `appFullSec (Q k)` summand is bounded by the uniform fibre-norm bound of the fixed smooth full-Hom
field section `Q k` (`exists_uniform_riemannianFiberNormSq_appFullRS_le`); the finite sum is accumulated by
`riemannianFiberNormSq_sum_le_card_mul`.  The full-Hom mirror of `exists_jet_bound_of_normalFormRS`. -/
theorem exists_jet_bound_of_normalFormFull (g : SmoothRiemannianMetric I M) (r d : ℕ)
    (op : ∀ (p rr : ℕ), SmoothCcTensor g r rr → SmoothCcTensor g r (rr + d + p))
    (p rr : ℕ) (hNF : NormalFormFull (E := E) (I := I) (M := M) g r d op p rr) :
    ∃ kappa : ℝ, 0 ≤ kappa ∧
      ∀ (W : SmoothCcTensor g r rr) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g r (rr + d + p) x ((op p rr W).toSection x) ≤
          kappa * ∑ q ∈ Finset.range (p + 1),
            riemannianFiberNormSq (I := I) (M := M) g r (rr + q) x
              ((iteratedCovGrad g r rr q W).toSection x) := by
  classical
  obtain ⟨Q, hQ⟩ := hNF

  choose C hC_nn hC using fun k =>
    exists_uniform_riemannianFiberNormSq_appFullRS_le (I := I) (M := M) g r (rr + k) (rr + d + p)
      (fun x : M => Q k x) (Q k).contMDiff
  refine ⟨(p + 1 : ℝ) * ∑ k ∈ Finset.range (p + 1), C k,
    mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => hC_nn k), fun W x => ?_⟩
  set a : ℕ → ℝ := fun k => riemannianFiberNormSq (I := I) (M := M) g r (rr + k) x
    ((iteratedCovGrad g r rr k W).toSection x) with ha_def
  have ha_nn : ∀ k, 0 ≤ a k := fun k =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g r (rr + k) x _

  rw [hQ W, SmoothCcTensor.toSection_sum_apply]

  refine le_trans (riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g r (rr + d + p) x
    (Finset.range (p + 1))
    (fun k => (appFullSec (I := I) (M := M) g r (rr + k) (rr + d + p) (Q k)
      (iteratedCovGrad g r rr k W)).toSection x)) ?_
  rw [Finset.card_range]

  have hsummand : ∀ k ∈ Finset.range (p + 1),
      riemannianFiberNormSq (I := I) (M := M) g r (rr + d + p) x
          ((appFullSec (I := I) (M := M) g r (rr + k) (rr + d + p) (Q k)
            (iteratedCovGrad g r rr k W)).toSection x) ≤ C k * a k := fun k _ => hC k _ x
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hsummand) (by positivity)) ?_

  have hCa_le : (∑ k ∈ Finset.range (p + 1), C k * a k) ≤
      (∑ k ∈ Finset.range (p + 1), C k) * ∑ k ∈ Finset.range (p + 1), a k := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun k _ => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (hC_nn k)
    exact Finset.single_le_sum (f := a) (fun j _ => ha_nn j) ‹k ∈ Finset.range (p + 1)›
  rw [show ((p + 1 : ℕ) : ℝ) = (p : ℝ) + 1 from by push_cast; ring]
  calc (p + 1 : ℝ) * ∑ k ∈ Finset.range (p + 1), C k * a k
      ≤ (p + 1 : ℝ) * ((∑ k ∈ Finset.range (p + 1), C k) * ∑ k ∈ Finset.range (p + 1), a k) :=
        mul_le_mul_of_nonneg_left hCa_le (by positivity)
    _ = (p + 1 : ℝ) * (∑ k ∈ Finset.range (p + 1), C k) * ∑ k ∈ Finset.range (p + 1), a k := by ring

/-! ## The value-local fibre-operation full-Hom factorisation engine

A fibre operation `F : SmoothCcTensor g r a → SmoothCcTensor g r c` that is (i) **value-local** (its
fibre value at `x` depends only on the contracted section's fibre value `W x`), (ii) `ℝ`-**linear** at the
fibre-value level, and (iii) **smooth-coefficient** (sends smooth sections to smooth sections — built in to
the `SmoothCcTensor` codomain) factors as the full Hom-bundle action `appFullSec Θ` of a *fixed* smooth
full Hom-bundle field section `Θ`: `(F W).toSection x = Θ x (W.toSection x)`.  This is the generic engine
that exhibits a value-local order-`0` curvature endomorphism as a fixed-field full Hom action — the
full-Hom analogue of the rank-`0` `pureREndoOp` / `genuineDiffCurvSection` post-composition. -/

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **A chosen smooth compactly-supported `(r, a)`-tensor realising a prescribed fibre value at `x`.** -/
private noncomputable def chooseSecAtFull
    (g : SmoothRiemannianMetric I M) (r a : ℕ) (x : M) (v : TensorRSSpace r a I x) :
    SmoothCcTensor g r a where
  toSection :=
    letI : NormedAddCommGroup (TensorRSModel r a ℝ E) := Tensor0SBundle.tensorRSModel_normedAddCommGroup r a
    letI : NormedSpace ℝ (TensorRSModel r a ℝ E) := Tensor0SBundle.tensorRSModel_normedSpace r a
    Classical.choose (ContMDiffSection.exists_eq_at (I := I) (F := TensorRSModel r a ℝ E)
      (V := fun z : M => TensorRSSpace r a I z) (n := (⊤ : ℕ∞)) x v)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The chosen section realises its prescribed fibre value at `x`. -/
private lemma chooseSecAtFull_eq
    (g : SmoothRiemannianMetric I M) (r a : ℕ) (x : M) (v : TensorRSSpace r a I x) :
    (chooseSecAtFull (I := I) (M := M) g r a x v).toSection x = v :=
  letI : NormedAddCommGroup (TensorRSModel r a ℝ E) := Tensor0SBundle.tensorRSModel_normedAddCommGroup r a
  letI : NormedSpace ℝ (TensorRSModel r a ℝ E) := Tensor0SBundle.tensorRSModel_normedSpace r a
  Classical.choose_spec (ContMDiffSection.exists_eq_at (I := I) (F := TensorRSModel r a ℝ E)
    (V := fun z : M => TensorRSSpace r a I z) (n := (⊤ : ℕ∞)) x v)

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The fibrewise operator extracted from a value-local `ℝ`-linear fibre operation.** For
`F : SmoothCcTensor g r a → SmoothCcTensor g r c` value-local and `ℝ`-linear at the fibre-value level, the
linear-map-to-CLM closure on the finite-dimensional fibre `TensorRSSpace r a I x` of the fibre operation
`v ↦ (F (chooseSecAtFull v)).toSection x`.  The source fibre carries the `g`-fibre `RiemannianBundle`
inner-product normed structure (default model-norm instances suppressed). -/
private noncomputable def valueLocalLinearHomFib
    (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (F : SmoothCcTensor g r a → SmoothCcTensor g r c)
    (hadd : ∀ (W₁ W₂ : SmoothCcTensor g r a) (x : M),
      (F (W₁ + W₂)).toSection x = (F W₁).toSection x + (F W₂).toSection x)
    (hsmul : ∀ (k : ℝ) (W : SmoothCcTensor g r a) (x : M),
      (F (k • W)).toSection x = k • (F W).toSection x)
    (hloc : ∀ (W₁ W₂ : SmoothCcTensor g r a) (x : M),
      W₁.toSection x = W₂.toSection x → (F W₁).toSection x = (F W₂).toSection x)
    (x : M) : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x :=
  letI instSrc : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r a I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r a
  haveI : FiniteDimensional ℝ (TensorRSSpace r a I x) := inferInstance
  haveI : T2Space (TensorRSSpace r a I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun v : TensorRSSpace r a I x =>
        (F (chooseSecAtFull (I := I) (M := M) g r a x v)).toSection x
      map_add' := fun v w => by
        have hsum : (chooseSecAtFull (I := I) (M := M) g r a x (v + w)).toSection x =
            (chooseSecAtFull (I := I) (M := M) g r a x v +
              chooseSecAtFull (I := I) (M := M) g r a x w).toSection x := by
          rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
            chooseSecAtFull_eq, chooseSecAtFull_eq, chooseSecAtFull_eq]
        rw [hloc _ _ x hsum, hadd]
      map_smul' := fun k v => by
        have hsm : (chooseSecAtFull (I := I) (M := M) g r a x (k • v)).toSection x =
            (k • chooseSecAtFull (I := I) (M := M) g r a x v).toSection x := by
          rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
            chooseSecAtFull_eq, chooseSecAtFull_eq]
        rw [hloc _ _ x hsm, hsmul]
        rfl }

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The fibrewise operator reads the contracted section's value.** -/
private lemma valueLocalLinearHomFib_apply
    (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (F : SmoothCcTensor g r a → SmoothCcTensor g r c)
    (hadd : ∀ (W₁ W₂ : SmoothCcTensor g r a) (x : M),
      (F (W₁ + W₂)).toSection x = (F W₁).toSection x + (F W₂).toSection x)
    (hsmul : ∀ (k : ℝ) (W : SmoothCcTensor g r a) (x : M),
      (F (k • W)).toSection x = k • (F W).toSection x)
    (hloc : ∀ (W₁ W₂ : SmoothCcTensor g r a) (x : M),
      W₁.toSection x = W₂.toSection x → (F W₁).toSection x = (F W₂).toSection x)
    (W : SmoothCcTensor g r a) (x : M) :
    valueLocalLinearHomFib (I := I) (M := M) g r a c F hadd hsmul hloc x (W.toSection x) =
      (F W).toSection x := by
  letI instSrc : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r a I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r a
  rw [valueLocalLinearHomFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
  exact hloc _ W x (chooseSecAtFull_eq (I := I) (M := M) g r a x (W.toSection x))

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **Base-point smoothness of the value-local linear fibre operator field.** Via the pointwise
`contMDiff_clm_section_of_pointwise` bridge: for any smooth `(r, a)`-section `Z`,
`x ↦ valueLocalLinearHomFib F … x (Z x) = (F Z).toSection x` is the smooth `SmoothCcTensor` `F Z`. -/
private theorem valueLocalLinearHomFib_contMDiff
    (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (F : SmoothCcTensor g r a → SmoothCcTensor g r c)
    (hadd : ∀ (W₁ W₂ : SmoothCcTensor g r a) (x : M),
      (F (W₁ + W₂)).toSection x = (F W₁).toSection x + (F W₂).toSection x)
    (hsmul : ∀ (k : ℝ) (W : SmoothCcTensor g r a) (x : M),
      (F (k • W)).toSection x = k • (F W).toSection x)
    (hloc : ∀ (W₁ W₂ : SmoothCcTensor g r a) (x : M),
      W₁.toSection x = W₂.toSection x → (F W₁).toSection x = (F W₂).toSection x) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x
        (valueLocalLinearHomFib (I := I) (M := M) g r a c F hadd hsmul hloc x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := TensorRSModel r a ℝ E) (V₁ := fun z : M => TensorRSSpace r a I z)
    (F₂ := TensorRSModel r c ℝ E) (V₂ := fun z : M => TensorRSSpace r c I z)
    (φ := fun x => valueLocalLinearHomFib (I := I) (M := M) g r a c F hadd hsmul hloc x)
  intro Z
  set Wσ : SmoothCcTensor g r a := ⟨Z, HasCompactSupport.of_compactSpace _⟩ with hWσ
  have hpt : ∀ x : M, valueLocalLinearHomFib (I := I) (M := M) g r a c F hadd hsmul hloc x (Z x) =
      (F Wσ).toSection x := fun x =>
    valueLocalLinearHomFib_apply (I := I) (M := M) g r a c F hadd hsmul hloc Wσ x
  refine (F Wσ).toSection.contMDiff.congr ?_
  intro x
  exact (congrArg (TotalSpace.mk' (TensorRSModel r c ℝ E)
    (E := fun z : M => TensorRSSpace r c I z) x) (hpt x)).symm ▸ rfl

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **A value-local `ℝ`-linear smooth-coefficient fibre operation factors as a fixed-field full Hom
action.** For `F : SmoothCcTensor g r a → SmoothCcTensor g r c` value-local and `ℝ`-linear at the
fibre-value level there is a smooth full Hom-bundle field section `Θ` with
`(F W).toSection x = Θ x (W.toSection x)` for every smooth `W` and point `x` — i.e. `F W = appFullSec Θ W`.
The full-Hom analogue of the rank-`0` value-local post-composition factorisation. -/
theorem exists_value_local_appFullSec (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (F : SmoothCcTensor g r a → SmoothCcTensor g r c)
    (hadd : ∀ (W₁ W₂ : SmoothCcTensor g r a) (x : M),
      (F (W₁ + W₂)).toSection x = (F W₁).toSection x + (F W₂).toSection x)
    (hsmul : ∀ (k : ℝ) (W : SmoothCcTensor g r a) (x : M),
      (F (k • W)).toSection x = k • (F W).toSection x)
    (hloc : ∀ (W₁ W₂ : SmoothCcTensor g r a) (x : M),
      W₁.toSection x = W₂.toSection x → (F W₁).toSection x = (F W₂).toSection x) :
    ∃ Θ : HomTensorRSField (E := E) (M := M) r a c I,
      ∀ (W : SmoothCcTensor g r a), F W = appFullSec (I := I) (M := M) g r a c Θ W := by
  refine ⟨{ toFun := fun x : M => valueLocalLinearHomFib (I := I) (M := M) g r a c F hadd hsmul hloc x
            contMDiff_toFun :=
              valueLocalLinearHomFib_contMDiff (I := I) (M := M) g r a c F hadd hsmul hloc }, fun W => ?_⟩
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [appFullSec_toSection]
  exact (valueLocalLinearHomFib_apply (I := I) (M := M) g r a c F hadd hsmul hloc W x).symm

end Connection
end Integral
end DifferentialGeometry

end
