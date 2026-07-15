import DifferentialGeometry.Geometry.Curvature.Bochner.PointwiseTensorCurvFirstOrderBound
import DifferentialGeometry.Geometry.Connection.TensorNabla.FullHomCovariantCalculusRS
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.Slot0CurryReconstruction
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection

/-!
# The first-order Hom-field section identity of the order-`2` commutator defect

For a closed smooth Riemannian manifold `(M, g)` this file upgrades the *fibre-norm bound* of the
order-`2` rough-Laplacian / covariant-gradient commutator defect
```
Curv S := pointwiseTensorCurv g s S = Δ_∇(∇S) − ∇(Δ_∇ S)
```
(a `(0, s + 1)`-tensor field, `∇S := covGrad g 0 s S`) to a **fixed smooth Hom-field section
identity**: there are fixed smooth full Hom-bundle field sections
`H_R : Hom(T^{(0,s+1)}, T^{(0,s+1)})` and `H_dR : Hom(T^{(0,s)}, T^{(0,s+1)})` such that, for every
smooth compactly-supported `(0, s)`-tensor `S`,
```
Curv S = H_R · ∇S + H_dR · S
```
(the action is the full Hom-bundle action `appFullSec`).  This is the **first-order** content: the
defect carries the `1`-jet `(∇S, S)` only, never `∇²S`.

## The construction

The proof is the section-level upgrade of the proven first-order frame-free *value* identity
`slot0_read_curv_eq_frameFree` (`PointwiseTensorCurvFirstOrderBound`): the wrapped slot-`0` `X`-read of
the defect is the frame-free combination
```
∑ᵢ (∇R)(Bᵢ, Bᵢ, X) S + 2 ∑ᵢ R(Bᵢ, X)(∇_{Bᵢ} S) − ∑ᵢ ∇_{R(Bᵢ, X) Bᵢ} S
```
(`Bᵢ := smoothOrthoFrame g x i`), each term value-local and `ℝ`-linear in the `1`-jet `(∇S, S)`:
the `∇R`-arm reads `S(x)` (the genuine `(∇R)·S` content, value-local by the Leibniz-contracted
`nablaTensor0SCurv` divergence-of-curvature collapse, no surviving `∇S`), and the two `R(∇S)`-arms
read `∇S(x)` (the directional covariant derivative `∇_{Bᵢ}S` is a slot-`0` slice of the gradient
value `∇S(x)`).

The two value-local `ℝ`-linear fibre functionals — the gradient-reading arm
`F_R : SmoothCcTensor g 0 (s+1) → SmoothCcTensor g 0 (s+1)` and the section-reading arm
`F_dR : SmoothCcTensor g 0 s → SmoothCcTensor g 0 (s+1)` — are then each factored as a smooth full
Hom-bundle field action through the value-local representation theorem
`exists_value_local_appFullSec` (`FullHomCovariantCalculusRS`), giving the fixed fields `H_R, H_dR`.

The `F_R`-arm is built as a concrete smooth section whose fibre value reads the gradient value's
slot-`0` slices; `F_dR` is the residual `Curv S − F_R(∇S)`, whose value-locality in `S(x)` is exactly
the proven `∇R`-arm value-locality.

## Convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (frame trace).  The covariant gradient `covGrad g 0 s`
raises the tensor rank from `(0, s)` to `(0, s + 1)`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 6400000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

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

/-- **Parseval expansion in the moving orthonormal frame `smoothOrthoFrame g x`.** Every tangent
vector at `x` is its `g_x`-orthonormal expansion against the moving frame `smoothOrthoFrame g x`
(orthonormal at its centre `x`).  Re-derived here from the public orthonormality
`smoothOrthoFrame_orthonormal_at_center` so the slot-`0` reconstruction can be read at the canonical
frame the frame-free value identity uses. -/
private lemma smoothOrthoFrame_parsevalExpand
    (g : SmoothRiemannianMetric I M) (x : M) (u : TangentSpace I x) :
    u = ∑ a : Fin (Module.finrank ℝ E),
      g.inner x (smoothOrthoFrame (I := I) g x a x) u • (smoothOrthoFrame (I := I) g x a x) := by
  classical
  haveI : Nonempty (Fin (Module.finrank ℝ E)) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  set e : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun a => smoothOrthoFrame (I := I) g x a x with he_def
  have horth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0 := fun i j =>
    smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  have he_li : LinearIndependent ℝ e := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner x (e k) (∑ j ∈ fs, c j • e j) = 0 := by rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g.inner x (e k) (c j • e j) = c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [(g.inner x (e k)).map_smul (c j) (e j), smul_eq_mul, horth k j]
    rw [Finset.sum_congr rfl h_pull, Finset.sum_eq_single_of_mem k hk_mem] at h_zero
    · rwa [if_pos rfl, mul_one] at h_zero
    · intro j _ hjk; rw [if_neg (fun h => hjk h.symm), mul_zero]
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) = Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin]; rfl
  set bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank he_li hcard with hbse_def
  have hbse_eq : ∀ i, bse i = e i := by
    intro i; rw [hbse_def]; exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank he_li hcard) i
  conv_lhs => rw [← bse.sum_repr u]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [hbse_eq a]
  congr 1
  have hrepr : g.inner x (e a) u =
      ∑ b : Fin (Module.finrank ℝ E), bse.repr u b * g.inner x (e a) (e b) := by
    conv_lhs => rw [show u = ∑ b : Fin (Module.finrank ℝ E),
      bse.repr u b • bse b from (bse.sum_repr u).symm]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [(g.inner x (e a)).map_smul (bse.repr u b) (bse b), smul_eq_mul, hbse_eq b]
  rw [hrepr, Finset.sum_eq_single a]
  · rw [horth a a, if_pos rfl, mul_one]
  · intro b _ hba; rw [horth a b, if_neg (fun h => hba h.symm), mul_zero]
  · intro h; exact absurd (Finset.mem_univ a) h

/-! ## The directional slot-`0` slice of a `(0, s + 1)`-value -/

/-- **The `(0, t)`-tensor wrapper is additive.** `tensor0SAsRS x (C + D) = tensor0SAsRS x C +
tensor0SAsRS x D` — the wrapper is `(tensor00Scalar x).smulRight ·`, additive in the value. -/
private lemma tensor0SAsRS_add_loc {t : ℕ} (x : M) (C D : Tensor0SSpace t I x) :
    tensor0SAsRS (I := I) (M := M) x (C + D) =
      tensor0SAsRS (I := I) (M := M) x C + tensor0SAsRS (I := I) (M := M) x D := by
  apply tensorRSSpace_ext (𝕜 := ℝ) 0 t x
  intro τ
  rw [tensor0SAsRS_apply (I := I) (M := M) x (C + D) τ]
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        tensor0SAsRS (I := I) (M := M) x C + tensor0SAsRS (I := I) (M := M) x D) τ =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        tensor0SAsRS (I := I) (M := M) x C) τ +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
          tensor0SAsRS (I := I) (M := M) x D) τ from by
    rw [ContinuousLinearMap.add_apply]]
  rw [tensor0SAsRS_apply (I := I) (M := M) x C τ, tensor0SAsRS_apply (I := I) (M := M) x D τ,
    smul_add]

/-- **The `(0, t)`-tensor wrapper commutes with scalar multiplication.** -/
private lemma tensor0SAsRS_smul_loc {t : ℕ} (x : M) (c : ℝ) (C : Tensor0SSpace t I x) :
    tensor0SAsRS (I := I) (M := M) x (c • C) =
      c • tensor0SAsRS (I := I) (M := M) x C := by
  apply tensorRSSpace_ext (𝕜 := ℝ) 0 t x
  intro τ
  rw [tensor0SAsRS_apply (I := I) (M := M) x (c • C) τ]
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        c • tensor0SAsRS (I := I) (M := M) x C) τ =
      c • (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        tensor0SAsRS (I := I) (M := M) x C) τ from by
    rw [ContinuousLinearMap.smul_apply]]
  rw [tensor0SAsRS_apply (I := I) (M := M) x C τ, smul_comm]

/-- **The directional slot-`0` slice of a `(0, s + 1)`-tensor value, as a continuous linear map.**
For a tangent direction `v`, the slice `Wx ↦ tensor0SAsRS x (tensor0S_curry s x (Wx (unit)) v)` reads
the slot-`0` of the value `Wx`'s unit-evaluation along `v`, re-wrapping the resulting `(0, s)`-model
tensor as a `(0, s)`-tensor.  It is continuous-linear in `Wx` (composition of the linear unit-eval,
the curry equivalence at `v`, and the wrapper `tensor0SAsRS`).  When `Wx = (∇S)(x)` the slice is the
directional covariant derivative `(∇_v S)(x)` (`slot0SliceFib_covGrad_eq`). -/
noncomputable def slot0SliceFib (x : M) (s : ℕ)
    (v : TangentSpace I x) :
    TensorRSSpace 0 (s + 1) I x →L[ℝ] TensorRSSpace 0 s I x :=
  haveI : FiniteDimensional ℝ (TensorRSSpace 0 (s + 1) I x) :=
    inferInstanceAs (FiniteDimensional ℝ (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x))
  haveI : T2Space (TensorRSSpace 0 (s + 1) I x) :=
    inferInstanceAs (T2Space (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x))
  LinearMap.toContinuousLinearMap
    { toFun := fun Wx =>
        tensor0SAsRS (I := I) (M := M) x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from Wx)
              (unitZeroSec (I := I) (M := M) x)) v)
      map_add' := fun W₁ W₂ => by
        have hval : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from W₁ + W₂)
            (unitZeroSec (I := I) (M := M) x) =
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from W₁)
              (unitZeroSec (I := I) (M := M) x) +
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from W₂)
              (unitZeroSec (I := I) (M := M) x) := by
          rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from W₁ + W₂) =
              (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from W₁) +
                (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from W₂) from rfl,
            ContinuousLinearMap.add_apply]
        rw [hval, map_add (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x),
          ContinuousLinearMap.add_apply,
          tensor0SAsRS_add_loc (I := I) (M := M) x]
      map_smul' := fun c W => by
        have hval : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from c • W)
            (unitZeroSec (I := I) (M := M) x) =
            c • (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from W)
              (unitZeroSec (I := I) (M := M) x) := by
          rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from c • W) =
              c • (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from W) from rfl,
            ContinuousLinearMap.smul_apply]
        rw [hval, map_smul (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x),
          ContinuousLinearMap.smul_apply, tensor0SAsRS_smul_loc (I := I) (M := M) x]
        rfl }

set_option linter.unusedSectionVars false in
/-- The defining formula for `slot0SliceFib`. -/
lemma slot0SliceFib_apply (x : M) (s : ℕ) (v : TangentSpace I x)
    (Wx : TensorRSSpace 0 (s + 1) I x) :
    slot0SliceFib (I := I) (M := M) x s v Wx =
      tensor0SAsRS (I := I) (M := M) x
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from Wx)
            (unitZeroSec (I := I) (M := M) x)) v) := by
  haveI : FiniteDimensional ℝ (TensorRSSpace 0 (s + 1) I x) :=
    inferInstanceAs (FiniteDimensional ℝ (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x))
  haveI : T2Space (TensorRSSpace 0 (s + 1) I x) :=
    inferInstanceAs (T2Space (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x))
  rw [slot0SliceFib, LinearMap.coe_toContinuousLinearMap']
  rfl

/-- **The directional slot-`0` slice is the `covGradBundleEquiv`-inverse reading.** For any
`(0, s + 1)`-value `T`, the slice `slot0SliceFib x s v T` equals the gradient-bundle inverse reading
`(covGradBundleEquiv 0 s x).symm T v`: both reconstruct, model-tuple by model-tuple, the same
`(0, s + 1)`-evaluation `toModel (T (unit)) (Fin.cons v ·)`.  This identifies the slot-`0` slice with the
on-disk frozen-frame reading `pureRFrozenDirCLM`, letting that tower's smoothness and frame-independence
transfer to the gradient arm. -/
lemma slot0SliceFib_eq_covGradBundleEquiv_symm (x : M) (s : ℕ) (v : TangentSpace I x)
    (T : TensorRSSpace 0 (s + 1) I x) :
    slot0SliceFib (I := I) (M := M) x s v T =
      (show TangentSpace I x →L[ℝ] TensorRSSpace 0 s I x from
        (covGradBundleEquiv (I := I) (M := M) 0 s x).symm T) v := by
  classical
  apply tensorRSSpace_ext (𝕜 := ℝ) 0 s x
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  rw [slot0SliceFib_apply]

  rw [tensor0SAsRS_apply (I := I) (M := M) x _ D]
  simp only [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply]
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from T)
        (unitZeroSec (I := I) (M := M) x)) (v0 := v) (vs := m)]

  rw [covGradBundleEquiv_symm_apply_eval (I := I) (M := M) 0 s x T v D m]

  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from T) D =
      tensor00Scalar (I := I) (M := M) x D •
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from T)
          (unitZeroSec (I := I) (M := M) x) from by
    conv_lhs => rw [tensor0S_zero_span' (I := I) (M := M) x D]
    rw [ContinuousLinearMap.map_smul]]
  simp only [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply]

/-- **The directional slot-`0` slice of `∇S` is the directional covariant derivative.** At
`Wx = (∇S)(x) := (covGrad g 0 s S).toSection x`, the slice along `v` equals the directional covariant
derivative value `(∇_v S)(x) = (tensorCov g 0 s).toFun (S.toSection) x v`.  By
`curry_covGrad_unit_eval_genVal` (the slot-`0` curry of the unit-evaluated gradient is the directional
derivative's unit-evaluation) and `tensor0SAsRS_unit_recover` (the wrapper recovers the tensor). -/
lemma slot0SliceFib_covGrad_eq (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (x : M) (v : TangentSpace I x) :
    slot0SliceFib (I := I) (M := M) x s v ((covGrad (I := I) (M := M) g 0 s S).toSection x) =
      (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x v := by
  rw [slot0SliceFib_apply]
  rw [curry_covGrad_unit_eval_genVal (I := I) (M := M) g s S x v]
  exact tensor0SAsRS_unit_recover (I := I) (M := M) s x
    ((tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x v)

set_option linter.unusedSectionVars false in
/-- **The slice along a direction is `ℝ`-linear in the direction.** For fixed `Wx`, the map
`v ↦ slot0SliceFib x s v Wx` is additive and `ℝ`-homogeneous: `slot0SliceFib` reads the slot-`0` curry
`tensor0S_curry s x (Wx (unit))` at `v`, and `tensor0S_curry s x (Wx (unit))` is itself continuous
linear in `v`. -/
lemma slot0SliceFib_dir_add (x : M) (s : ℕ) (v v' : TangentSpace I x)
    (Wx : TensorRSSpace 0 (s + 1) I x) :
    slot0SliceFib (I := I) (M := M) x s (v + v') Wx =
      slot0SliceFib (I := I) (M := M) x s v Wx + slot0SliceFib (I := I) (M := M) x s v' Wx := by
  rw [slot0SliceFib_apply, slot0SliceFib_apply, slot0SliceFib_apply]
  rw [map_add (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from Wx)
      (unitZeroSec (I := I) (M := M) x)))]
  rw [tensor0SAsRS_add_loc (I := I) (M := M) x]

set_option linter.unusedSectionVars false in
/-- The slice along a direction is `ℝ`-homogeneous in the direction. -/
lemma slot0SliceFib_dir_smul (x : M) (s : ℕ) (c : ℝ) (v : TangentSpace I x)
    (Wx : TensorRSSpace 0 (s + 1) I x) :
    slot0SliceFib (I := I) (M := M) x s (c • v) Wx =
      c • slot0SliceFib (I := I) (M := M) x s v Wx := by
  rw [slot0SliceFib_apply, slot0SliceFib_apply]
  rw [map_smul (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from Wx)
      (unitZeroSec (I := I) (M := M) x)))]
  rw [tensor0SAsRS_smul_loc (I := I) (M := M) x]

/-! ## The gradient-reading curvature arm operator field -/

/-- **The per-direction gradient-reading curvature arm, as a linear map in the reconstruction
direction.** For a smooth frame field `B`, point `x`, and `(0, s + 1)`-value `Wx`, the linear map
sending a reconstruction direction `w` to the frame-summed first-order curvature contraction of the
slot-`0` slices of `Wx`:
```
w ↦ ∑ᵢ [ 2 • R(Bᵢ, w)(slice_{Bᵢ} Wx) − slice_{R(Bᵢ, w) Bᵢ} Wx ],
```
with `slice_v Wx := slot0SliceFib x s v Wx`, `R := riemannOp (tensorCov g 0 s) x` the bundled tensor
curvature operator (linear in its middle slot `w`), and `R(Bᵢ, w)Bᵢ := riemannOp (LeviCivita g) x
(Bᵢ x) w (Bᵢ x)` the Levi-Civita curvature direction (linear in `w`).  These are the two `R(∇S)`-arms
of `slot0_read_curv_eq_frameFree` read off the gradient value's slices; both are linear in `w`. -/
noncomputable def gradArmDirLM
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (x : M) (Wx : TensorRSSpace 0 (s + 1) I x) :
    TangentSpace I x →ₗ[ℝ] TensorRSSpace 0 s I x where
  toFun w := ∑ i : Fin (Module.finrank ℝ E),
    ((2 : ℝ) • riemannOp (tensorCov (I := I) g 0 s) x (B i x) w
        (slot0SliceFib (I := I) (M := M) x s (B i x) Wx) -
      slot0SliceFib (I := I) (M := M) x s
        (riemannOp (LeviCivita (I := I) g) x (B i x) w (B i x)) Wx)
  map_add' w w' := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_add (riemannOp (tensorCov (I := I) g 0 s) x (B i x)) w w',
      ContinuousLinearMap.add_apply, smul_add]
    rw [map_add (riemannOp (LeviCivita (I := I) g) x (B i x)) w w',
      ContinuousLinearMap.add_apply, slot0SliceFib_dir_add (I := I) (M := M) x s]
    abel
  map_smul' c w := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul (riemannOp (tensorCov (I := I) g 0 s) x (B i x)) c w,
      ContinuousLinearMap.smul_apply, smul_comm (2 : ℝ) c]
    rw [map_smul (riemannOp (LeviCivita (I := I) g) x (B i x)) c w,
      ContinuousLinearMap.smul_apply, slot0SliceFib_dir_smul (I := I) (M := M) x s]
    rw [smul_sub]

/-- The defining formula for `gradArmDirLM`. -/
@[simp] lemma gradArmDirLM_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (x : M) (Wx : TensorRSSpace 0 (s + 1) I x) (w : TangentSpace I x) :
    gradArmDirLM (I := I) (M := M) g s B x Wx w =
      ∑ i : Fin (Module.finrank ℝ E),
        ((2 : ℝ) • riemannOp (tensorCov (I := I) g 0 s) x (B i x) w
            (slot0SliceFib (I := I) (M := M) x s (B i x) Wx) -
          slot0SliceFib (I := I) (M := M) x s
            (riemannOp (LeviCivita (I := I) g) x (B i x) w (B i x)) Wx) := rfl

/-- **The gradient-reading curvature arm direction map, as a continuous linear map.** The
continuous-linear closure of `gradArmDirLM` on the finite-dimensional tangent fibre. -/
noncomputable def gradArmDirCLM
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (x : M) (Wx : TensorRSSpace 0 (s + 1) I x) :
    TangentSpace I x →L[ℝ] TensorRSSpace 0 s I x :=
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap (gradArmDirLM (I := I) (M := M) g s B x Wx)

@[simp] lemma gradArmDirCLM_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (x : M) (Wx : TensorRSSpace 0 (s + 1) I x) (w : TangentSpace I x) :
    gradArmDirCLM (I := I) (M := M) g s B x Wx w =
      ∑ i : Fin (Module.finrank ℝ E),
        ((2 : ℝ) • riemannOp (tensorCov (I := I) g 0 s) x (B i x) w
            (slot0SliceFib (I := I) (M := M) x s (B i x) Wx) -
          slot0SliceFib (I := I) (M := M) x s
            (riemannOp (LeviCivita (I := I) g) x (B i x) w (B i x)) Wx) := by
  rw [gradArmDirCLM, LinearMap.coe_toContinuousLinearMap']
  rfl

/-- **The direction map is `ℝ`-linear in the `(0, s + 1)`-value.** `gradArmDirCLM g s B x` is
additive and `ℝ`-homogeneous in `Wx`: every summand reads `Wx` through the continuous-linear slices
`slot0SliceFib`. -/
lemma gradArmDirCLM_value_add
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (x : M) (W₁ W₂ : TensorRSSpace 0 (s + 1) I x) :
    gradArmDirCLM (I := I) (M := M) g s B x (W₁ + W₂) =
      gradArmDirCLM (I := I) (M := M) g s B x W₁ + gradArmDirCLM (I := I) (M := M) g s B x W₂ := by
  apply ContinuousLinearMap.ext
  intro w
  rw [ContinuousLinearMap.add_apply, gradArmDirCLM_apply, gradArmDirCLM_apply, gradArmDirCLM_apply,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_add (slot0SliceFib (I := I) (M := M) x s (B i x)) W₁ W₂,
    map_add (riemannOp (tensorCov (I := I) g 0 s) x (B i x) w), smul_add,
    map_add (slot0SliceFib (I := I) (M := M) x s
      (riemannOp (LeviCivita (I := I) g) x (B i x) w (B i x))) W₁ W₂]
  abel

lemma gradArmDirCLM_value_smul
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (x : M) (c : ℝ) (W : TensorRSSpace 0 (s + 1) I x) :
    gradArmDirCLM (I := I) (M := M) g s B x (c • W) =
      c • gradArmDirCLM (I := I) (M := M) g s B x W := by
  apply ContinuousLinearMap.ext
  intro w
  rw [ContinuousLinearMap.smul_apply, gradArmDirCLM_apply, gradArmDirCLM_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_smul (slot0SliceFib (I := I) (M := M) x s (B i x)) c W,
    map_smul (riemannOp (tensorCov (I := I) g 0 s) x (B i x) w),
    map_smul (slot0SliceFib (I := I) (M := M) x s
      (riemannOp (LeviCivita (I := I) g) x (B i x) w (B i x))) c W]
  rw [smul_sub, smul_comm (2 : ℝ) c]

/-- **The gradient-reading curvature arm fibre operator.** The slot-`0` uncurry, through
`(tensor0S_curry s x).symm`, of the gradient-reading curvature direction map `gradArmDirCLM g s B x`:
the fixed `(0, s + 1)`-endomorphism whose slot-`0` curry along `w` is the frame-summed first-order
curvature contraction `∑ᵢ [2 R(Bᵢ, w)(slice_{Bᵢ} Wx) − slice_{R(Bᵢ, w)Bᵢ} Wx]` of the slices of `Wx`.
It is `ℝ`-linear in `Wx` (`gradArmDirCLM_value_add` / `_smul`). -/
noncomputable def gradArmFib
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (x : M) :
    TensorRSSpace 0 (s + 1) I x →L[ℝ] TensorRSSpace 0 (s + 1) I x :=
  haveI : FiniteDimensional ℝ (TensorRSSpace 0 (s + 1) I x) :=
    inferInstanceAs (FiniteDimensional ℝ (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x))
  haveI : T2Space (TensorRSSpace 0 (s + 1) I x) :=
    inferInstanceAs (T2Space (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x))
  LinearMap.toContinuousLinearMap
    { toFun := fun Wx =>
        covGradBundleEquiv (I := I) (M := M) 0 s x
          (gradArmDirCLM (I := I) (M := M) g s B x Wx)
      map_add' := fun W₁ W₂ => by
        rw [gradArmDirCLM_value_add (I := I) (M := M) g s B x W₁ W₂, map_add]
      map_smul' := fun c W => by
        rw [gradArmDirCLM_value_smul (I := I) (M := M) g s B x c W, map_smul]
        rfl }

set_option linter.unusedSectionVars false in
/-- The defining formula for `gradArmFib`. -/
lemma gradArmFib_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (x : M) (Wx : TensorRSSpace 0 (s + 1) I x) :
    gradArmFib (I := I) (M := M) g s B x Wx =
      covGradBundleEquiv (I := I) (M := M) 0 s x
        (gradArmDirCLM (I := I) (M := M) g s B x Wx) := by
  haveI : FiniteDimensional ℝ (TensorRSSpace 0 (s + 1) I x) :=
    inferInstanceAs (FiniteDimensional ℝ (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x))
  haveI : T2Space (TensorRSSpace 0 (s + 1) I x) :=
    inferInstanceAs (T2Space (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x))
  rw [gradArmFib, LinearMap.coe_toContinuousLinearMap']
  rfl

/-- **The wrapped slot-`0` slice of the gradient-arm operator at `∇S` is the two `R(∇S)`-arms.** With
the moving frame `B := smoothOrthoFrame g x`, the wrapped slot-`0` `Bₐ`-read of the gradient-arm
operator `gradArmFib` applied to the gradient value `(∇S)(x)` equals the two `R(∇S)`-arms of
`slot0_read_curv_eq_frameFree` (the `2 R(Bᵢ, Bₐ)(∇_{Bᵢ}S)` and `−∇_{R(Bᵢ, Bₐ)Bᵢ}S` terms):
```
tensor0SAsRS x (curry ((gradArmFib (∇S)(x))(unit)) (Bₐ x))
  = 2 ∑ᵢ R(Bᵢ, Bₐ)(∇_{Bᵢ}S)(x) − ∑ᵢ ∇_{R(Bᵢ, Bₐ)Bᵢ}S(x).
```
The slot-`0` curry reads the direction map (`tensor0S_curry_covGradBundleEquiv_unit_genVal`,
`tensor0SAsRS_unit_recover`), and each slice is the directional covariant derivative
(`slot0SliceFib_covGrad_eq`); the curvature contraction is read back to `riemannSec` form
(`riemannSec_eq_riemannOp_tensorCov`). -/
lemma gradArmFib_covGrad_slice_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (a : Fin (Module.finrank ℝ E)) :
    tensor0SAsRS (I := I) (M := M) x
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            gradArmFib (I := I) (M := M) g s (smoothOrthoFrame (I := I) g x) x
              ((covGrad (I := I) (M := M) g 0 s S).toSection x))
            (unitZeroSec (I := I) (M := M) x))
          (smoothOrthoFrame (I := I) g x a x)) =
      (2 : ℝ) • ∑ i : Fin (Module.finrank ℝ E),
          riemannSec (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame (I := I) g x a)
            (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
              (fun y : M => S.toSection y)) x -
        ∑ i : Fin (Module.finrank ℝ E),
          (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x
            (riemannOp (LeviCivita (I := I) g) x (smoothOrthoFrame (I := I) g x i x)
              (smoothOrthoFrame (I := I) g x a x) (smoothOrthoFrame (I := I) g x i x)) := by
  classical
  set B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b :=
    fun i => smoothOrthoFrame (I := I) g x i with hB
  set Wx : TensorRSSpace 0 (s + 1) I x := (covGrad (I := I) (M := M) g 0 s S).toSection x with hWx

  rw [gradArmFib_apply (I := I) (M := M) g s B x Wx]
  rw [tensor0S_curry_covGradBundleEquiv_unit_genVal (I := I) (M := M) s x
    (gradArmDirCLM (I := I) (M := M) g s B x Wx) (B a x)]
  rw [tensor0SAsRS_unit_recover (I := I) (M := M) s x
    (gradArmDirCLM (I := I) (M := M) g s B x Wx (B a x))]
  rw [gradArmDirCLM_apply (I := I) (M := M) g s B x Wx (B a x)]

  rw [Finset.sum_sub_distrib, Finset.smul_sum]
  congr 1
  · refine Finset.sum_congr rfl (fun i _ => ?_)

    rw [hWx, slot0SliceFib_covGrad_eq (I := I) (M := M) g s S x (B i x)]
    rw [riemannSec_eq_riemannOp_tensorCov (I := I) g 0 s
      (smoothOrthoFrame_smooth (I := I) g x i) (smoothOrthoFrame_smooth (I := I) g x a)
      (covApplyRS_contMDiff (I := I) g 0 s S.toSection.contMDiff
        (smoothOrthoFrame_smooth (I := I) g x i))]
    rfl
  · refine Finset.sum_congr rfl (fun i _ => ?_)

    rw [hWx, slot0SliceFib_covGrad_eq (I := I) (M := M) g s S x
      (riemannOp (LeviCivita (I := I) g) x (B i x) (B a x) (B i x))]

/-! ## Smoothness of the gradient-arm operator field -/

set_option linter.unusedVariables false in
/-- **Smoothness of the slot-`0` slice section along a smooth direction.** For a smooth `(0, s + 1)`
section `Y` and a smooth tangent direction field `V`, the section `x ↦ slot0SliceFib x s (V x) (Y x)`
is `C^∞`.  By the bridge `slot0SliceFib_eq_covGradBundleEquiv_symm` it is the gradient-bundle inverse
reading `(covGradBundleEquiv 0 s x).symm (Y x) (V x)`, the application of the smooth `Hom`-section
`x ↦ (covGradBundleEquiv 0 s x).symm (Y x)` (smooth by `covGradBundleEquiv_symm_contMDiff_totalSpace`)
at the smooth field `V`. -/
lemma slot0SliceFib_section_contMDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    {Y : Π b : M, TensorRSSpace 0 (s + 1) I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (s + 1) ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (s + 1) I z) b (Y b)))
    {V : Π b : M, TangentSpace I b}
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) b
        (slot0SliceFib (I := I) (M := M) b s (V b) (Y b))) := by

  have heq : (fun b : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
      (E := fun z : M => TensorRSSpace 0 s I z) b
      (slot0SliceFib (I := I) (M := M) b s (V b) (Y b))) =
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) b
        ((show TangentSpace I b →L[ℝ] TensorRSSpace 0 s I b from
          (covGradBundleEquiv (I := I) (M := M) 0 s b).symm (Y b)) (V b))) := by
    funext b
    rw [slot0SliceFib_eq_covGradBundleEquiv_symm (I := I) (M := M) b s (V b) (Y b)]
  rw [heq]

  have hHom : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel 0 s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel 0 s ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TensorRSSpace 0 s I z) b
        ((covGradBundleEquiv (I := I) (M := M) 0 s b).symm (Y b))) :=
    (covGradBundleEquiv_symm_contMDiff_totalSpace (I := I) (M := M) 0 s).comp hY
  exact ContMDiff.clm_bundle_apply (b := fun b : M => b)
    (ϕ := fun b => (covGradBundleEquiv (I := I) (M := M) 0 s b).symm (Y b))
    (v := fun b => V b) hHom hV

/-- **The gradient-arm direction Hom-section is smooth (frozen frame).** For a fixed smooth frame `B`
and a smooth `(0, s + 1)`-section `Y`, the `Hom(TM, T^{(0,s)})`-section
`x ↦ gradArmDirCLM g s B x (Y x)` is `C^∞`.  By `contMDiff_clm_section_of_pointwise` it suffices that
for every smooth tangent field `Z` the section `x ↦ gradArmDirCLM g s B x (Y x) (Z x)` is smooth; that
value is the frame sum of the two curvature arms, each smooth: the `R`-arm is a `riemannSec`
contraction of the smooth slice section (`riemannSec_contMDiff`, `slot0SliceFib_section_contMDiff`),
the `C5`-arm is a slot-`0` slice along the smooth curvature direction `R(Bᵢ, Z)Bᵢ`
(`slot0SliceFib_section_contMDiff`, the direction smooth by `riemannSec_contMDiff` of the Levi-Civita
connection). -/
lemma gradArmDirCLM_homSection_contMDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    {Y : Π b : M, TensorRSSpace 0 (s + 1) I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (s + 1) ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (s + 1) I z) b (Y b))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel 0 s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel 0 s ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TensorRSSpace 0 s I z) x
        (gradArmDirCLM (I := I) (M := M) g s B x (Y x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := E) (V₁ := fun z : M => TangentSpace I z)
    (F₂ := TensorRSModel 0 s ℝ E) (V₂ := fun z : M => TensorRSSpace 0 s I z)
    (φ := fun x => gradArmDirCLM (I := I) (M := M) g s B x (Y x))
  intro Z

  have hval : (fun x : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
      (E := fun z : M => TensorRSSpace 0 s I z) x
      (gradArmDirCLM (I := I) (M := M) g s B x (Y x) (Z x))) =
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) x
        (∑ i : Fin (Module.finrank ℝ E),
          ((2 : ℝ) • riemannOp (tensorCov (I := I) g 0 s) x (B i x) (Z x)
              (slot0SliceFib (I := I) (M := M) x s (B i x) (Y x)) -
            slot0SliceFib (I := I) (M := M) x s
              (riemannOp (LeviCivita (I := I) g) x (B i x) (Z x) (B i x)) (Y x)))) := by
    funext x
    rw [gradArmDirCLM_apply]
  rw [hval]

  refine ContMDiff.sum_section (s := Finset.univ) (fun i _ => ?_)

  have hRarm : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) x
        ((2 : ℝ) • riemannOp (tensorCov (I := I) g 0 s) x (B i x) (Z x)
          (slot0SliceFib (I := I) (M := M) x s (B i x) (Y x)))) := by
    have hslice := slot0SliceFib_section_contMDiff (I := I) (M := M) g s hY (hB i)
    have hRsec : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
          (E := fun z : M => TensorRSSpace 0 s I z) x
          (riemannSec (tensorCov (I := I) g 0 s) (B i) Z
            (fun y : M => slot0SliceFib (I := I) (M := M) y s (B i y) (Y y)) x)) :=
      riemannSec_contMDiff (cov := tensorCov (I := I) g 0 s) (hB i) Z.contMDiff hslice
    have hpt : (fun x : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) x
        ((2 : ℝ) • riemannOp (tensorCov (I := I) g 0 s) x (B i x) (Z x)
          (slot0SliceFib (I := I) (M := M) x s (B i x) (Y x)))) =
        (fun x : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
          (E := fun z : M => TensorRSSpace 0 s I z) x
          ((2 : ℝ) • riemannSec (tensorCov (I := I) g 0 s) (B i) Z
            (fun y : M => slot0SliceFib (I := I) (M := M) y s (B i y) (Y y)) x)) := by
      funext x
      rw [riemannOp_apply_smooth (cov := tensorCov (I := I) g 0 s) (hB i) Z.contMDiff hslice]
    rw [hpt]
    exact ContMDiff.smul_section (𝕜 := ℝ) (contMDiff_const (c := (2 : ℝ))) hRsec

  have hC5arm : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) x
        (slot0SliceFib (I := I) (M := M) x s
          (riemannOp (LeviCivita (I := I) g) x (B i x) (Z x) (B i x)) (Y x))) := by

    have hdir : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (T% (fun x : M => riemannOp (LeviCivita (I := I) g) x (B i x) (Z x) (B i x))) := by
      have hsec : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
          (T% (fun y : M => riemannSec (LeviCivita (I := I) g) (B i) Z (B i) y)) :=
        riemannSec_contMDiff (cov := LeviCivita (I := I) g) (hB i) Z.contMDiff (hB i)
      refine hsec.congr ?_
      intro x
      exact congrArg (TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x)
        (riemannOp_apply_smooth (cov := LeviCivita (I := I) g) (hB i) Z.contMDiff (hB i))
    exact slot0SliceFib_section_contMDiff (I := I) (M := M) g s hY hdir
  exact hRarm.sub_section hC5arm

/-- **Smoothness of the gradient-arm section applied to a smooth `(0, s + 1)`-section (frozen
frame).** For a fixed smooth frame `B` and a smooth `(0, s + 1)`-section `Y`, the section
`x ↦ gradArmFib g s B x (Y x)` is `C^∞`: it is the `covGradBundleEquiv`-uncurry
(`covGradBundleEquiv_contMDiff_totalSpace`) of the smooth gradient-arm direction Hom-section
(`gradArmDirCLM_homSection_contMDiff`). -/
lemma gradArmFib_frozen_section_contMDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    {Y : Π b : M, TensorRSSpace 0 (s + 1) I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (s + 1) ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (s + 1) I z) b (Y b))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (s + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (s + 1) I z) x
        (gradArmFib (I := I) (M := M) g s B x (Y x))) := by
  have heq : (fun x : M => TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
      (E := fun z : M => TensorRSSpace 0 (s + 1) I z) x
      (gradArmFib (I := I) (M := M) g s B x (Y x))) =
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (s + 1) I z) x
        (covGradBundleEquiv (I := I) (M := M) 0 s x
          (gradArmDirCLM (I := I) (M := M) g s B x (Y x)))) := by
    funext x
    rw [gradArmFib_apply (I := I) (M := M) g s B x (Y x)]
  rw [heq]
  exact (covGradBundleEquiv_contMDiff_totalSpace (I := I) (M := M) 0 s).comp
    (gradArmDirCLM_homSection_contMDiff (I := I) (M := M) g s hB hY)

/-! ## Frame independence of the gradient-arm direction map -/

/-- **The frame sum of the Levi-Civita curvature contracted direction is `−Ric♯`.** For any
`g_x`-orthonormal frame `e` (indexed by `Fin (finrank E)`), the contracted-curvature direction
`∑ᵢ R(eᵢ, v) eᵢ` equals the negated raised Ricci endomorphism `−ricEndoRaisedFib g x v`.  Proof by
`g`-non-degeneracy (`SmoothRiemannianMetric.eq_of_inner_eq`): pairing against `ζ`, the curvature's
metric skew-adjointness `riemannOp_metric_skew` flips `⟨R(eᵢ, v) eᵢ, ζ⟩` to `−⟨R(eᵢ, v) ζ, eᵢ⟩`, whose
frame sum is the Ricci trace `Ric(v, ζ) = ⟨ricEndoRaisedFib g x v, ζ⟩`
(`ricciTensor_eq_orthonormal_trace`, `inner_ricEndoRaisedFib`).  The right-hand side is frame-free. -/
lemma frameSum_riemannOp_LeviCivita_eq_neg_ricEndoRaised
    (g : SmoothRiemannianMetric I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (horth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (v : TangentSpace I x) :
    ∑ i : Fin (Module.finrank ℝ E), riemannOp (LeviCivita (I := I) g) x (e i) v (e i) =
      - ricEndoRaisedFib (I := I) g x v := by
  classical
  apply SmoothRiemannianMetric.eq_of_inner_eq (I := I) g
  intro ζ
  rw [map_sum, ContinuousLinearMap.sum_apply, map_neg]

  have hflip : ∀ i : Fin (Module.finrank ℝ E),
      g.inner x (riemannOp (LeviCivita (I := I) g) x (e i) v (e i)) ζ =
        - g.inner x (riemannOp (LeviCivita (I := I) g) x (e i) v ζ) (e i) := by
    intro i
    have hskew := riemannOp_metric_skew (I := I) g x (e i) v (e i) ζ
    have hsymm : g.inner x (e i) (riemannOp (LeviCivita (I := I) g) x (e i) v ζ) =
        g.inner x (riemannOp (LeviCivita (I := I) g) x (e i) v ζ) (e i) :=
      g.symm x _ _
    rw [hsymm] at hskew
    linarith [hskew]
  rw [Finset.sum_congr rfl (fun i _ => hflip i), Finset.sum_neg_distrib]

  rw [ContinuousLinearMap.neg_apply, inner_ricEndoRaisedFib (I := I) (M := M) g x v ζ,
    ricciTensor_eq_orthonormal_trace (I := I) g x v ζ e horth]

/-- **The `R`-arm scalarised diagonal trace, as a continuous bilinear form.** For a fixed
reconstruction direction `w`, value `Wx`, and model tuple `m`, the map
`(a, b) ↦ toModel ((R(a, w)(slice_b Wx)) (unit)) m` is a continuous bilinear form on `T_x M`: linear in
`a` through the curvature operator's first slot, in `b` through the slice's direction-linearity.  It is
built as a composition of continuous linear maps: the slice direction CLM, the curvature first-slot CLM,
the unit-evaluation, and the model-tuple evaluation. -/
private noncomputable def rArmBilin
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) (w : TangentSpace I x)
    (Wx : TensorRSSpace 0 (s + 1) I x) (m : Fin s → E) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  haveI iFD : FiniteDimensional ℝ (TensorRSSpace 0 s I x) :=
    inferInstanceAs (FiniteDimensional ℝ (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x))
  haveI iT2 : T2Space (TensorRSSpace 0 s I x) :=
    inferInstanceAs (T2Space (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x))

  let evalCLM : TensorRSSpace 0 s I x →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun T => Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T)
            (unitZeroSec (I := I) (M := M) x)) m
        map_add' := fun T T' => by
          simp only [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T + T') =
              (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T) +
                (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T') from rfl,
            ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add,
            ContinuousMultilinearMap.add_apply]
        map_smul' := fun c T => by
          simp only [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from c • T) =
              c • (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T) from rfl,
            ContinuousLinearMap.smul_apply, Tensor0SSpace.toModel_smul,
            ContinuousMultilinearMap.smul_apply, RingHom.id_apply] }

  let sliceDirCLM : TangentSpace I x →L[ℝ] TensorRSSpace 0 s I x :=
    LinearMap.toContinuousLinearMap
      { toFun := fun b => slot0SliceFib (I := I) (M := M) x s b Wx
        map_add' := fun b b' => slot0SliceFib_dir_add (I := I) (M := M) x s b b' Wx
        map_smul' := fun c b => slot0SliceFib_dir_smul (I := I) (M := M) x s c b Wx }
  LinearMap.toContinuousLinearMap
    { toFun := fun a => evalCLM.comp
        ((riemannOp (tensorCov (I := I) g 0 s) x a w).comp sliceDirCLM)
      map_add' := fun a a' => by
        apply ContinuousLinearMap.ext; intro b
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
          map_add (riemannOp (tensorCov (I := I) g 0 s) x) a a',
          ContinuousLinearMap.add_apply, map_add evalCLM]
      map_smul' := fun c a => by
        apply ContinuousLinearMap.ext; intro b
        simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
          RingHom.id_apply, map_smul (riemannOp (tensorCov (I := I) g 0 s) x) c a,
          ContinuousLinearMap.smul_apply, map_smul evalCLM] }

@[simp] private lemma rArmBilin_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) (w : TangentSpace I x)
    (Wx : TensorRSSpace 0 (s + 1) I x) (m : Fin s → E) (a b : TangentSpace I x) :
    rArmBilin (I := I) (M := M) g s x w Wx m a b =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          riemannOp (tensorCov (I := I) g 0 s) x a w
            (slot0SliceFib (I := I) (M := M) x s b Wx))
          (unitZeroSec (I := I) (M := M) x)) m := by
  rw [rArmBilin]
  simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearMap.comp_apply]

/-- **The unit-tuple read of one gradient-arm summand.** Records the `(0, s)`-model evaluation of the
`i`-th gradient-arm summand at frame `B`, separating the `R`-arm (the `rArmBilin` diagonal entry) from
the `C5`-arm slice. -/
private lemma gradArmDirCLM_summand_toModel
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (w : TangentSpace I x) (Wx : TensorRSSpace 0 (s + 1) I x) (m : Fin s → E)
    (i : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          (2 : ℝ) • riemannOp (tensorCov (I := I) g 0 s) x (B i x) w
              (slot0SliceFib (I := I) (M := M) x s (B i x) Wx) -
            slot0SliceFib (I := I) (M := M) x s
              (riemannOp (LeviCivita (I := I) g) x (B i x) w (B i x)) Wx)
          (unitZeroSec (I := I) (M := M) x)) m =
      (2 : ℝ) * rArmBilin (I := I) (M := M) g s x w Wx m (B i x) (B i x) -
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
            slot0SliceFib (I := I) (M := M) x s
              (riemannOp (LeviCivita (I := I) g) x (B i x) w (B i x)) Wx)
            (unitZeroSec (I := I) (M := M) x)) m := by
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        (2 : ℝ) • riemannOp (tensorCov (I := I) g 0 s) x (B i x) w
            (slot0SliceFib (I := I) (M := M) x s (B i x) Wx) -
          slot0SliceFib (I := I) (M := M) x s
            (riemannOp (LeviCivita (I := I) g) x (B i x) w (B i x)) Wx) =
      (2 : ℝ) • (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          riemannOp (tensorCov (I := I) g 0 s) x (B i x) w
            (slot0SliceFib (I := I) (M := M) x s (B i x) Wx)) -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          slot0SliceFib (I := I) (M := M) x s
            (riemannOp (LeviCivita (I := I) g) x (B i x) w (B i x)) Wx) from rfl]
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    Tensor0SSpace.toModel_sub, Tensor0SSpace.toModel_smul,
    ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.smul_apply]
  rw [rArmBilin_apply (I := I) (M := M) g s x w Wx m (B i x) (B i x)]
  rfl

/-- **Model-tuple read of a finite sum of `(0, s)`-values at the unit, distributed over the sum.** -/
private lemma toModel_unit_finsum {ι : Type*} (s : ℕ) (x : M) (fs : Finset ι)
    (T : ι → TensorRSSpace 0 s I x) (m : Fin s → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from ∑ i ∈ fs, T i)
          (unitZeroSec (I := I) (M := M) x)) m =
      ∑ i ∈ fs, Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T i)
          (unitZeroSec (I := I) (M := M) x)) m := by
  classical
  induction fs using Finset.induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
            (0 : TensorRSSpace 0 s I x)) (unitZeroSec (I := I) (M := M) x) =
          (0 : Tensor0SSpace s I x) from ContinuousLinearMap.zero_apply _]
      rw [Tensor0SSpace.toModel_zero, ContinuousMultilinearMap.zero_apply]
  | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T a + ∑ i ∈ t, T i)
            (unitZeroSec (I := I) (M := M) x) =
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T a)
              (unitZeroSec (I := I) (M := M) x) +
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from ∑ i ∈ t, T i)
              (unitZeroSec (I := I) (M := M) x) from by
        rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T a + ∑ i ∈ t, T i) =
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T a) +
              (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from ∑ i ∈ t, T i) from rfl,
          ContinuousLinearMap.add_apply]]
      rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply, ih]

/-- **The gradient-arm direction map is frame-independent.** For two `g_x`-orthonormal frames `B`, `C`
(indexed by `Fin (finrank E)`) and any `(0, s + 1)`-value `Wx`,
`gradArmDirCLM g s B x Wx = gradArmDirCLM g s C x Wx`.  The `R`-arm `∑ᵢ R(Bᵢ, w)(slice_{Bᵢ} Wx)`, read
on a model tuple, is the diagonal trace `∑ᵢ rArmBilin(Bᵢ, Bᵢ)` of the bilinear form `rArmBilin`,
frame-independent by `orthonormal_basis_bilin_trace`; the `C5`-arm direction
`∑ᵢ R(Bᵢ, w)Bᵢ = −Ric♯(w)` is frame-independent by
`frameSum_riemannOp_LeviCivita_eq_neg_ricEndoRaised`. -/
lemma gradArmDirCLM_frame_independent
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (B C : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hBorth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i x) (B j x) = if i = j then (1 : ℝ) else 0)
    (hCorth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (C i x) (C j x) = if i = j then (1 : ℝ) else 0)
    (Wx : TensorRSSpace 0 (s + 1) I x) :
    gradArmDirCLM (I := I) (M := M) g s B x Wx =
      gradArmDirCLM (I := I) (M := M) g s C x Wx := by
  classical
  apply ContinuousLinearMap.ext
  intro w
  rw [gradArmDirCLM_apply, gradArmDirCLM_apply]

  apply tensorRSSpace_ext (𝕜 := ℝ) 0 s x
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)

  have hredD : ∀ F : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b,
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
            ∑ i : Fin (Module.finrank ℝ E),
              ((2 : ℝ) • riemannOp (tensorCov (I := I) g 0 s) x (F i x) w
                  (slot0SliceFib (I := I) (M := M) x s (F i x) Wx) -
                slot0SliceFib (I := I) (M := M) x s
                  (riemannOp (LeviCivita (I := I) g) x (F i x) w (F i x)) Wx)) D) m =
        tensor00Scalar (I := I) (M := M) x D *
          ∑ i : Fin (Module.finrank ℝ E),
            Tensor0SSpace.toModel
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
                (2 : ℝ) • riemannOp (tensorCov (I := I) g 0 s) x (F i x) w
                    (slot0SliceFib (I := I) (M := M) x s (F i x) Wx) -
                  slot0SliceFib (I := I) (M := M) x s
                    (riemannOp (LeviCivita (I := I) g) x (F i x) w (F i x)) Wx)
                (unitZeroSec (I := I) (M := M) x)) m := by
    intro F
    set T : TensorRSSpace 0 s I x :=
      ∑ i : Fin (Module.finrank ℝ E),
        ((2 : ℝ) • riemannOp (tensorCov (I := I) g 0 s) x (F i x) w
            (slot0SliceFib (I := I) (M := M) x s (F i x) Wx) -
          slot0SliceFib (I := I) (M := M) x s
            (riemannOp (LeviCivita (I := I) g) x (F i x) w (F i x)) Wx) with hT
    have hstep : Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T) D) m =
        tensor00Scalar (I := I) (M := M) x D *
          Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T)
              (unitZeroSec (I := I) (M := M) x)) m := by
      conv_lhs => rw [tensor0S_zero_span' (I := I) (M := M) x D]
      rw [ContinuousLinearMap.map_smul]
      simp only [Tensor0SSpace.toModel_smul,
        ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    rw [hstep, hT]
    apply congrArg (fun z : ℝ => tensor00Scalar (I := I) (M := M) x D * z)
    exact toModel_unit_finsum (I := I) (M := M) s x Finset.univ
      (fun i => (2 : ℝ) • riemannOp (tensorCov (I := I) g 0 s) x (F i x) w
            (slot0SliceFib (I := I) (M := M) x s (F i x) Wx) -
          slot0SliceFib (I := I) (M := M) x s
            (riemannOp (LeviCivita (I := I) g) x (F i x) w (F i x)) Wx) m
  rw [hredD B, hredD C]
  apply congrArg (fun z : ℝ => tensor00Scalar (I := I) (M := M) x D * z)

  rw [Finset.sum_congr rfl (fun i _ =>
    gradArmDirCLM_summand_toModel (I := I) (M := M) g s x B w Wx m i),
    Finset.sum_congr rfl (fun i _ =>
    gradArmDirCLM_summand_toModel (I := I) (M := M) g s x C w Wx m i)]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  apply congrArg₂ (fun a b : ℝ => a - b)
  · -- `R`-arm: the diagonal trace is frame-independent.
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    apply congrArg (fun z : ℝ => 2 * z)
    rw [orthonormal_basis_bilin_trace (I := I) g x (rArmBilin (I := I) (M := M) g s x w Wx m)
        (fun i => B i x) hBorth,
      orthonormal_basis_bilin_trace (I := I) g x (rArmBilin (I := I) (M := M) g s x w Wx m)
        (fun i => C i x) hCorth]
  · -- `C5`-arm: the direction sum collapses to `−Ric♯(w)`, frame-free; pull the slice through the sum.
    have hsliceSum : ∀ F : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b,
        (∑ i : Fin (Module.finrank ℝ E),
            Tensor0SSpace.toModel ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
              slot0SliceFib (I := I) (M := M) x s
                (riemannOp (LeviCivita (I := I) g) x (F i x) w (F i x)) Wx)
              (unitZeroSec (I := I) (M := M) x)) m) =
          Tensor0SSpace.toModel ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
            slot0SliceFib (I := I) (M := M) x s
              (∑ i : Fin (Module.finrank ℝ E),
                riemannOp (LeviCivita (I := I) g) x (F i x) w (F i x)) Wx)
            (unitZeroSec (I := I) (M := M) x)) m := by
      intro F

      let sliceLM : TangentSpace I x →ₗ[ℝ] TensorRSSpace 0 s I x :=
        { toFun := fun v => slot0SliceFib (I := I) (M := M) x s v Wx
          map_add' := fun v v' => slot0SliceFib_dir_add (I := I) (M := M) x s v v' Wx
          map_smul' := fun c v => slot0SliceFib_dir_smul (I := I) (M := M) x s c v Wx }
      have hdir : slot0SliceFib (I := I) (M := M) x s
            (∑ i : Fin (Module.finrank ℝ E),
              riemannOp (LeviCivita (I := I) g) x (F i x) w (F i x)) Wx =
          ∑ i : Fin (Module.finrank ℝ E),
            slot0SliceFib (I := I) (M := M) x s
              (riemannOp (LeviCivita (I := I) g) x (F i x) w (F i x)) Wx :=
        map_sum sliceLM (fun i => riemannOp (LeviCivita (I := I) g) x (F i x) w (F i x))
          Finset.univ
      rw [hdir]
      exact (toModel_unit_finsum (I := I) (M := M) s x Finset.univ
        (fun i => slot0SliceFib (I := I) (M := M) x s
          (riemannOp (LeviCivita (I := I) g) x (F i x) w (F i x)) Wx) m).symm
    rw [hsliceSum B, hsliceSum C]
    rw [frameSum_riemannOp_LeviCivita_eq_neg_ricEndoRaised (I := I) (M := M) g x
        (fun i => B i x) hBorth w,
      frameSum_riemannOp_LeviCivita_eq_neg_ricEndoRaised (I := I) (M := M) g x
        (fun i => C i x) hCorth w]

/-! ## The moving-frame gradient-arm section -/

/-- **Smoothness of the moving-frame gradient-arm section.** For a smooth `(0, s + 1)`-section `Y`, the
section `x ↦ gradArmFib g s (smoothOrthoFrame g x) x (Y x)` (read at the moving frame centred at each
base point) is `C^∞`.  At each `x₀` it agrees, on the orthonormality neighbourhood
`smoothOrthoFrameNbhd x₀`, with the frozen-frame section `gradArmFib g s (smoothOrthoFrame g x₀) x (Y x)`
(`gradArmDirCLM_frame_independent`, both frames being `g_y`-orthonormal there), which is smooth
(`gradArmFib_frozen_section_contMDiff`); `ContMDiffAt.congr_of_eventuallyEq` transfers smoothness. -/
lemma gradArmFib_moving_section_contMDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    {Y : Π b : M, TensorRSSpace 0 (s + 1) I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (s + 1) ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (s + 1) I z) b (Y b))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (s + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (s + 1) I z) x
        (gradArmFib (I := I) (M := M) g s (smoothOrthoFrame (I := I) g x) x (Y x))) := by
  classical
  intro x₀

  have hfrozen : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel 0 (s + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (s + 1) I z) x
        (gradArmFib (I := I) (M := M) g s (smoothOrthoFrame (I := I) g x₀) x (Y x))) x₀ :=
    gradArmFib_frozen_section_contMDiff (I := I) (M := M) g s
      (fun i => smoothOrthoFrame_smooth (I := I) g x₀ i) hY x₀
  refine hfrozen.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy

  refine congrArg (TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
    (E := fun z : M => TensorRSSpace 0 (s + 1) I z) y) ?_
  rw [gradArmFib_apply, gradArmFib_apply,
    gradArmDirCLM_frame_independent (I := I) (M := M) g s y
      (fun i => smoothOrthoFrame (I := I) g y i) (fun i => smoothOrthoFrame (I := I) g x₀ i)
      (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g y i j)
      (fun i j => smoothOrthoFrame_orthonormal (I := I) g x₀ hy i j) (Y y)]

/-- **The gradient-reading curvature arm as a section operator.** For a smooth compactly-supported
`(0, s + 1)`-tensor `W`, the moving-frame gradient-arm operator field applied to `W`:
```
gradArmSection g s W := x ↦ gradArmFib g s (smoothOrthoFrame g x) x (W.toSection x),
```
a smooth compactly-supported `(0, s + 1)`-tensor (smoothness `gradArmFib_moving_section_contMDiff`).
Its fibre value at `x` is a fixed (`W`-independent) continuous linear map applied to `W.toSection x`,
so it is value-local and `ℝ`-linear in the gradient value. -/
noncomputable def gradArmSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (W : SmoothCcTensor g 0 (s + 1)) :
    SmoothCcTensor g 0 (s + 1) where
  toSection :=
    { toFun := fun x : M =>
        gradArmFib (I := I) (M := M) g s (smoothOrthoFrame (I := I) g x) x (W.toSection x)
      contMDiff_toFun :=
        gradArmFib_moving_section_contMDiff (I := I) (M := M) g s W.toSection.contMDiff_toFun }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

@[simp] lemma gradArmSection_toSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (W : SmoothCcTensor g 0 (s + 1)) (x : M) :
    (gradArmSection (I := I) (M := M) g s W).toSection x =
      gradArmFib (I := I) (M := M) g s (smoothOrthoFrame (I := I) g x) x (W.toSection x) := rfl

/-! ## The differentiated-curvature arm and the first-order section identity -/

/-- **The differentiated-curvature arm section.** The residual of the defect after removing the
gradient-reading curvature arm:
```
diffArmSection g s S := pointwiseTensorCurv g s S − gradArmSection g s (∇S),
```
a smooth compactly-supported `(0, s + 1)`-tensor.  By the frame-free slice identity its wrapped slot-`0`
`Bₐ`-slice is the differentiated-curvature `(∇R)·S` arm `∑ᵢ (∇R)(Bᵢ, Bᵢ, Bₐ) S`
(`nablaTensorCurvSec`), value-local and `ℝ`-linear in `S(x)` alone (the proven divergence-of-curvature
collapse `frame_sum_nablaTensor0SCurv_diag_baseSlot_eval`). -/
noncomputable def diffArmSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    SmoothCcTensor g 0 (s + 1) :=
  pointwiseTensorCurv (I := I) (M := M) g s S -
    gradArmSection (I := I) (M := M) g s (covGrad (I := I) (M := M) g 0 s S)

/-- **The wrapped slot-`0` slice of the differentiated-curvature arm is the `(∇R)·S` arm.** With the
moving frame `Bₐ := smoothOrthoFrame g x a`, the wrapped slot-`0` `Bₐ`-slice of `diffArmSection g s S`
equals `∑ᵢ nablaTensorCurvSec g (tensorCov g 0 s) Bᵢ Bᵢ Bₐ S`.  The defect slice
`slot0_read_curv_eq_frameFree` is `A_a + (2 R(∇S) − C5)`, the gradient-arm slice
(`gradArmFib_covGrad_slice_eq`) is exactly `2 R(∇S) − C5`, so their difference is the `∇R`-arm `A_a`. -/
lemma diffArmSection_slice_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (a : Fin (Module.finrank ℝ E)) :
    tensor0SAsRS (I := I) (M := M) x
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            (diffArmSection (I := I) (M := M) g s S).toSection x)
            (unitZeroSec (I := I) (M := M) x))
          (smoothOrthoFrame (I := I) g x a x)) =
      ∑ i : Fin (Module.finrank ℝ E),
        nablaTensorCurvSec (I := I) g (tensorCov (I := I) g 0 s)
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
          (smoothOrthoFrame (I := I) g x a) (fun y : M => S.toSection y) x := by
  classical

  have hsub : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (diffArmSection (I := I) (M := M) g s S).toSection x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x) -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (gradArmSection (I := I) (M := M) g s
            (covGrad (I := I) (M := M) g 0 s S)).toSection x) := by
    rw [diffArmSection, SmoothCcTensor.toSection_sub]; rfl
  rw [hsub, ContinuousLinearMap.sub_apply, map_sub, ContinuousLinearMap.sub_apply,
    tensor0SAsRS_sub' (I := I) (M := M) s x]

  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (gradArmSection (I := I) (M := M) g s
          (covGrad (I := I) (M := M) g 0 s S)).toSection x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        gradArmFib (I := I) (M := M) g s (smoothOrthoFrame (I := I) g x) x
          ((covGrad (I := I) (M := M) g 0 s S).toSection x)) from rfl]
  rw [slot0_read_curv_eq_frameFree (I := I) (M := M) g s S
    (smoothOrthoFrame_smooth (I := I) g x a) x]
  rw [gradArmFib_covGrad_slice_eq (I := I) (M := M) g s S x a]
  abel

/-- **The `(∇R)·S` arm slice, read on a model tuple, depends only on the value `S(x)`.** The wrapped
slot-`0` `Bₐ`-slice of `diffArmSection g s S`, evaluated at the unit on the trailing tuple `m`, is the
divergence-of-curvature contraction `−∑ₖ toModel (unitEvalSection S x) (update m k (∑ᵢ ∇R(Bᵢ,Bₐ) ))`,
which reads `S` only through `unitEvalSection g s S x = (S.toSection x)(unit)`.  The proof passes the
`nablaTensorCurvSec` frame sum to the abstract `(0, s)`-tensor curvature `nablaTensor0SCurv`
(`nablaTensorCurvSec_tensorRSCov_unitEval`) and collapses the diagonal frame trace by the contracted
second Bianchi identity (`frame_sum_nablaTensor0SCurv_diag_baseSlot_eval`). -/
lemma diffArmSection_slice_toModel_value_local
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (a : Fin (Module.finrank ℝ E)) (m : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          tensor0SAsRS (I := I) (M := M) x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
                (diffArmSection (I := I) (M := M) g s S).toSection x)
                (unitZeroSec (I := I) (M := M) x))
              (smoothOrthoFrame (I := I) g x a x)))
          (unitZeroSec (I := I) (M := M) x)) m =
      - ∑ k : Fin s,
          Tensor0SSpace.toModel (unitEvalSection (I := I) (M := M) g s S x)
            (Function.update m k
              (∑ i : Fin (Module.finrank ℝ E),
                nablaBaseSlotCurv (I := I) g
                  (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
                    (smoothOrthoFrame_smooth (I := I) g x i))
                  (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
                    (smoothOrthoFrame_smooth (I := I) g x i))
                  (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x a)
                    (smoothOrthoFrame_smooth (I := I) g x a)) x (m k))) := by
  classical
  set Ba : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothOrthoFrame (I := I) g x a)
      (smoothOrthoFrame_smooth (I := I) g x a) with hBa
  set A : Π b : M, Tensor0SSpace s I b := unitEvalSection (I := I) (M := M) g s S with hA

  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensor0SAsRS (I := I) (M := M) x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              (diffArmSection (I := I) (M := M) g s S).toSection x)
              (unitZeroSec (I := I) (M := M) x))
            (smoothOrthoFrame (I := I) g x a x))) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        ∑ i : Fin (Module.finrank ℝ E),
          nablaTensorCurvSec (I := I) g (tensorCov (I := I) g 0 s)
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame (I := I) g x a) (fun y : M => S.toSection y) x) from
    diffArmSection_slice_eq (I := I) (M := M) g s S x a]
  rw [toModel_unit_finsum (I := I) (M := M) s x Finset.univ
    (fun i => nablaTensorCurvSec (I := I) g (tensorCov (I := I) g 0 s)
      (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
      (smoothOrthoFrame (I := I) g x a) (fun y : M => S.toSection y) x) m]
  have hper : ∀ i : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        nablaTensorCurvSec (I := I) g (tensorCov (I := I) g 0 s)
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
          (smoothOrthoFrame (I := I) g x a) (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x)) m =
      Tensor0SSpace.toModel
        (nablaTensor0SCurv (I := I) g s
          (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame_smooth (I := I) g x i))
          (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame_smooth (I := I) g x i)) Ba A x) m := by
    intro i
    exact nablaTensorCurvSec_tensorRSCov_unitEval (I := I) (M := M) g s
      (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
        (smoothOrthoFrame_smooth (I := I) g x i))
      (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
        (smoothOrthoFrame_smooth (I := I) g x i))
      (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x a)
        (smoothOrthoFrame_smooth (I := I) g x a)) S.toSection x ▸ rfl
  rw [Finset.sum_congr rfl (fun i _ => hper i)]

  rw [frame_sum_nablaTensor0SCurv_diag_baseSlot_eval (I := I) g s Ba A
    (contMDiff_unitEvalSection (I := I) (M := M) g s S) x m]

set_option maxHeartbeats 6400000 in
/-- **The differentiated-curvature arm is value-local.** If `S₁.toSection x = S₂.toSection x` then
`(diffArmSection g s S₁).toSection x = (diffArmSection g s S₂).toSection x`: the arm reads `S` only
through its value `S(x)`.  Two `(0, s + 1)`-tensors are equal iff their slot-`0` slices, read on the
moving frame, agree on every model tuple (`tensor0S_uncurry_cons_eval_orthonormal`,
`smoothOrthoFrame_parsevalExpand`); each slice is the divergence-of-curvature contraction of
`unitEvalSection g s S x = (S.toSection x)(unit)` (`diffArmSection_slice_toModel_value_local`), which is
equal under `S₁.toSection x = S₂.toSection x`. -/
lemma diffArmSection_value_local
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S₁ S₂ : SmoothCcTensor g 0 s) (x : M)
    (hx : S₁.toSection x = S₂.toSection x) :
    (diffArmSection (I := I) (M := M) g s S₁).toSection x =
      (diffArmSection (I := I) (M := M) g s S₂).toSection x := by
  classical

  apply tensorRSSpace_ext (𝕜 := ℝ) 0 (s + 1) x
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun v => ?_)

  have hredD : ∀ T : TensorRSSpace 0 (s + 1) I x,
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from T) D) v =
        tensor00Scalar (I := I) (M := M) x D *
          Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from T)
              (unitZeroSec (I := I) (M := M) x)) v := by
    intro T
    conv_lhs => rw [tensor0S_zero_span' (I := I) (M := M) x D]
    rw [ContinuousLinearMap.map_smul]
    simp only [Tensor0SSpace.toModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [hredD, hredD]
  congr 1

  obtain ⟨w, m, hcons⟩ : ∃ (w : TangentSpace I x) (m : Fin s → TangentSpace I x),
      v = Fin.cons w m := ⟨v 0, Fin.tail v, (Fin.cons_self_tail v).symm⟩
  subst hcons
  rw [tensor0S_uncurry_cons_eval_orthonormal (I := I) g _
    (fun a => smoothOrthoFrame (I := I) g x a x)
    (fun u => smoothOrthoFrame_parsevalExpand (I := I) (M := M) g x u) w m,
    tensor0S_uncurry_cons_eval_orthonormal (I := I) g _
    (fun a => smoothOrthoFrame (I := I) g x a x)
    (fun u => smoothOrthoFrame_parsevalExpand (I := I) (M := M) g x u) w m]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  congr 1

  have hbridge : ∀ S : SmoothCcTensor g 0 s,
      Tensor0SSpace.toModel
          (tensor0S_curry (I := I) (M := M) s x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              (diffArmSection (I := I) (M := M) g s S).toSection x)
              (unitZeroSec (I := I) (M := M) x))
            (smoothOrthoFrame (I := I) g x a x)) m =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
            tensor0SAsRS (I := I) (M := M) x
              (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
                ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
                  (diffArmSection (I := I) (M := M) g s S).toSection x)
                  (unitZeroSec (I := I) (M := M) x))
                (smoothOrthoFrame (I := I) g x a x)))
            (unitZeroSec (I := I) (M := M) x)) m := by
    intro S
    rw [tensor0SAsRS_apply (I := I) (M := M) x _ (unitZeroSec (I := I) (M := M) x),
      tensor00Scalar_unitZeroSec' (I := I) (M := M) x, one_smul]
  rw [hbridge S₁, hbridge S₂]
  rw [diffArmSection_slice_toModel_value_local (I := I) (M := M) g s S₁ x a m,
    diffArmSection_slice_toModel_value_local (I := I) (M := M) g s S₂ x a m]
  rw [show unitEvalSection (I := I) (M := M) g s S₁ x =
      unitEvalSection (I := I) (M := M) g s S₂ x from by
    rw [unitEvalSection_apply, unitEvalSection_apply, hx]]

/-! ## Value-locality and `ℝ`-linearity of the two arms -/

/-- The gradient-arm section is additive at the fibre value (the fibre operator is continuous-linear,
and `gradArmFib` is `ℝ`-linear in the value). -/
lemma gradArmSection_toSection_add
    (g : SmoothRiemannianMetric I M) (s : ℕ) (W₁ W₂ : SmoothCcTensor g 0 (s + 1)) (x : M) :
    (gradArmSection (I := I) (M := M) g s (W₁ + W₂)).toSection x =
      (gradArmSection (I := I) (M := M) g s W₁).toSection x +
        (gradArmSection (I := I) (M := M) g s W₂).toSection x := by
  rw [gradArmSection_toSection, gradArmSection_toSection, gradArmSection_toSection]
  rw [show (W₁ + W₂).toSection x = W₁.toSection x + W₂.toSection x from by
    rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]]
  rw [map_add]

/-- The gradient-arm section commutes with scalar multiplication at the fibre value. -/
lemma gradArmSection_toSection_smul
    (g : SmoothRiemannianMetric I M) (s : ℕ) (c : ℝ) (W : SmoothCcTensor g 0 (s + 1)) (x : M) :
    (gradArmSection (I := I) (M := M) g s (c • W)).toSection x =
      c • (gradArmSection (I := I) (M := M) g s W).toSection x := by
  rw [gradArmSection_toSection, gradArmSection_toSection]
  rw [show (c • W).toSection x = c • W.toSection x from by
    rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply]]
  rw [map_smul]

/-- The gradient-arm section is value-local. -/
lemma gradArmSection_value_local
    (g : SmoothRiemannianMetric I M) (s : ℕ) (W₁ W₂ : SmoothCcTensor g 0 (s + 1)) (x : M)
    (hx : W₁.toSection x = W₂.toSection x) :
    (gradArmSection (I := I) (M := M) g s W₁).toSection x =
      (gradArmSection (I := I) (M := M) g s W₂).toSection x := by
  rw [gradArmSection_toSection, gradArmSection_toSection, hx]

/-- **The gradient-arm section as a fixed smooth Hom-field action.**  By the value-local representation
theorem `exists_value_local_appFullSec`, there is a smooth full Hom-bundle field `H_R` with
`gradArmSection g s W = appFullSec H_R W` for every smooth compactly-supported `(0, s + 1)`-tensor `W`. -/
theorem exists_gradArmSection_appFullSec (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ H_R : HomTensorRSField (E := E) (M := M) 0 (s + 1) (s + 1) I,
      ∀ W : SmoothCcTensor g 0 (s + 1),
        gradArmSection (I := I) (M := M) g s W =
          appFullSec (I := I) (M := M) g 0 (s + 1) (s + 1) H_R W :=
  exists_value_local_appFullSec (I := I) (M := M) g 0 (s + 1) (s + 1)
    (fun W => gradArmSection (I := I) (M := M) g s W)
    (fun W₁ W₂ x => gradArmSection_toSection_add (I := I) (M := M) g s W₁ W₂ x)
    (fun c W x => gradArmSection_toSection_smul (I := I) (M := M) g s c W x)
    (fun W₁ W₂ x hW => gradArmSection_value_local (I := I) (M := M) g s W₁ W₂ x hW)

/-- The order-`2` commutator defect is additive at the section level: `Δ_∇(∇·) − ∇(Δ_∇ ·)` is `ℝ`-linear,
each constituent (`rawTensorConnLapSmooth`, `covGrad`) preserving `SmoothCcTensor` addition. -/
lemma pointwiseTensorCurv_toSection_add
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S₁ S₂ : SmoothCcTensor g 0 s) (x : M) :
    (pointwiseTensorCurv (I := I) (M := M) g s (S₁ + S₂)).toSection x =
      (pointwiseTensorCurv (I := I) (M := M) g s S₁).toSection x +
        (pointwiseTensorCurv (I := I) (M := M) g s S₂).toSection x := by
  classical
  have hRoughGrad : rawTensorConnLapSmooth (I := I) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s (S₁ + S₂)) =
      rawTensorConnLapSmooth (I := I) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S₁) +
        rawTensorConnLapSmooth (I := I) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S₂) := by
    rw [covGrad_add (I := I) (M := M) g 0 s S₁ S₂]
    apply SmoothCcTensor.ext; apply ContMDiffSection.ext; intro y
    rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
      rawTensorConnLapSmooth_toSection_apply, rawTensorConnLapSmooth_toSection_apply,
      rawTensorConnLapSmooth_toSection_apply]
    rw [show (fun z : M => (covGrad (I := I) (M := M) g 0 s S₁ +
          covGrad (I := I) (M := M) g 0 s S₂).toSection z) =
        (fun z : M => (covGrad (I := I) (M := M) g 0 s S₁).toSection z) +
          (fun z : M => (covGrad (I := I) (M := M) g 0 s S₂).toSection z) from by
      funext z; rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]]
    exact rawTensorConnLap_add (I := I) g 0 (s + 1)
      (fun z => ((covGrad (I := I) (M := M) g 0 s S₁).toSection.contMDiff z).mdifferentiableAt
        (by simp))
      (fun z => ((covGrad (I := I) (M := M) g 0 s S₂).toSection.contMDiff z).mdifferentiableAt
        (by simp))
      (fun z i => (covApplyRS_contMDiff (I := I) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s S₁).toSection.contMDiff
        (smoothOrthoFrame_smooth (I := I) g z i) z).mdifferentiableAt (by simp))
      (fun z i => (covApplyRS_contMDiff (I := I) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s S₂).toSection.contMDiff
        (smoothOrthoFrame_smooth (I := I) g z i) z).mdifferentiableAt (by simp)) y
  have hGradRough : covGrad (I := I) (M := M) g 0 s
        (rawTensorConnLapSmooth (I := I) g 0 s (S₁ + S₂)) =
      covGrad (I := I) (M := M) g 0 s (rawTensorConnLapSmooth (I := I) g 0 s S₁) +
        covGrad (I := I) (M := M) g 0 s (rawTensorConnLapSmooth (I := I) g 0 s S₂) := by
    rw [← covGrad_add (I := I) (M := M) g 0 s]
    refine congrArg (covGrad (I := I) (M := M) g 0 s) ?_
    apply SmoothCcTensor.ext; apply ContMDiffSection.ext; intro y
    rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
      rawTensorConnLapSmooth_toSection_apply, rawTensorConnLapSmooth_toSection_apply,
      rawTensorConnLapSmooth_toSection_apply]
    rw [show (fun z : M => (S₁ + S₂).toSection z) =
        (fun z : M => S₁.toSection z) + (fun z : M => S₂.toSection z) from by
      funext z; rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]]
    exact rawTensorConnLap_add (I := I) g 0 s
      (fun z => (S₁.toSection.contMDiff z).mdifferentiableAt (by simp))
      (fun z => (S₂.toSection.contMDiff z).mdifferentiableAt (by simp))
      (fun z i => (covApplyRS_contMDiff (I := I) g 0 s S₁.toSection.contMDiff
        (smoothOrthoFrame_smooth (I := I) g z i) z).mdifferentiableAt (by simp))
      (fun z i => (covApplyRS_contMDiff (I := I) g 0 s S₂.toSection.contMDiff
        (smoothOrthoFrame_smooth (I := I) g z i) z).mdifferentiableAt (by simp)) y
  rw [pointwiseTensorCurv_toSection_eq_sub, pointwiseTensorCurv_toSection_eq_sub,
    pointwiseTensorCurv_toSection_eq_sub, hRoughGrad, hGradRough]
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
  abel

/-- The order-`2` commutator defect commutes with scalar multiplication at the section level. -/
lemma pointwiseTensorCurv_toSection_smul
    (g : SmoothRiemannianMetric I M) (s : ℕ) (c : ℝ) (S : SmoothCcTensor g 0 s) (x : M) :
    (pointwiseTensorCurv (I := I) (M := M) g s (c • S)).toSection x =
      c • (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x := by
  classical
  have hRoughGrad : rawTensorConnLapSmooth (I := I) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s (c • S)) =
      c • rawTensorConnLapSmooth (I := I) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S) := by
    rw [covGrad_smul (I := I) (M := M) g 0 s c S]
    apply SmoothCcTensor.ext; apply ContMDiffSection.ext; intro y
    rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
      rawTensorConnLapSmooth_toSection_apply, rawTensorConnLapSmooth_toSection_apply]
    rw [show (fun z : M => (c • covGrad (I := I) (M := M) g 0 s S).toSection z) =
        (fun z : M => c • (covGrad (I := I) (M := M) g 0 s S).toSection z) from by
      funext z; rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply]]
    exact rawTensorConnLap_smul (I := I) g 0 (s + 1) c
      (fun z => ((covGrad (I := I) (M := M) g 0 s S).toSection.contMDiff z).mdifferentiableAt
        (by simp))
      (fun z i => (covApplyRS_contMDiff (I := I) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s S).toSection.contMDiff
        (smoothOrthoFrame_smooth (I := I) g z i) z).mdifferentiableAt (by simp)) y
  have hGradRough : covGrad (I := I) (M := M) g 0 s
        (rawTensorConnLapSmooth (I := I) g 0 s (c • S)) =
      c • covGrad (I := I) (M := M) g 0 s (rawTensorConnLapSmooth (I := I) g 0 s S) := by
    rw [← covGrad_smul (I := I) (M := M) g 0 s]
    refine congrArg (covGrad (I := I) (M := M) g 0 s) ?_
    apply SmoothCcTensor.ext; apply ContMDiffSection.ext; intro y
    rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
      rawTensorConnLapSmooth_toSection_apply, rawTensorConnLapSmooth_toSection_apply]
    rw [show (fun z : M => (c • S).toSection z) =
        (fun z : M => c • S.toSection z) from by
      funext z; rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply]]
    exact rawTensorConnLap_smul (I := I) g 0 s c
      (fun z => (S.toSection.contMDiff z).mdifferentiableAt (by simp))
      (fun z i => (covApplyRS_contMDiff (I := I) g 0 s S.toSection.contMDiff
        (smoothOrthoFrame_smooth (I := I) g z i) z).mdifferentiableAt (by simp)) y
  rw [pointwiseTensorCurv_toSection_eq_sub, pointwiseTensorCurv_toSection_eq_sub,
    hRoughGrad, hGradRough]
  rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
    SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply, smul_sub]

/-- The differentiated-curvature arm `diffArmSection g s S = Curv S − gradArmSection g s (∇S)` is
additive at the section level (both `Curv` and `gradArmSection ∘ ∇` are `ℝ`-linear). -/
lemma diffArmSection_toSection_add
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S₁ S₂ : SmoothCcTensor g 0 s) (x : M) :
    (diffArmSection (I := I) (M := M) g s (S₁ + S₂)).toSection x =
      (diffArmSection (I := I) (M := M) g s S₁).toSection x +
        (diffArmSection (I := I) (M := M) g s S₂).toSection x := by
  rw [diffArmSection, diffArmSection, diffArmSection]
  rw [SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_sub,
    ContMDiffSection.coe_sub, ContMDiffSection.coe_sub, ContMDiffSection.coe_sub,
    Pi.sub_apply, Pi.sub_apply, Pi.sub_apply]
  rw [pointwiseTensorCurv_toSection_add (I := I) (M := M) g s S₁ S₂]
  rw [covGrad_add (I := I) (M := M) g 0 s S₁ S₂,
    gradArmSection_toSection_add (I := I) (M := M) g s
      (covGrad (I := I) (M := M) g 0 s S₁) (covGrad (I := I) (M := M) g 0 s S₂) x]
  abel

/-- The differentiated-curvature arm commutes with scalar multiplication at the section level. -/
lemma diffArmSection_toSection_smul
    (g : SmoothRiemannianMetric I M) (s : ℕ) (c : ℝ) (S : SmoothCcTensor g 0 s) (x : M) :
    (diffArmSection (I := I) (M := M) g s (c • S)).toSection x =
      c • (diffArmSection (I := I) (M := M) g s S).toSection x := by
  rw [diffArmSection, diffArmSection]
  rw [SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_sub,
    ContMDiffSection.coe_sub, ContMDiffSection.coe_sub, Pi.sub_apply, Pi.sub_apply]
  rw [pointwiseTensorCurv_toSection_smul (I := I) (M := M) g s c S]
  rw [covGrad_smul (I := I) (M := M) g 0 s c S,
    gradArmSection_toSection_smul (I := I) (M := M) g s c
      (covGrad (I := I) (M := M) g 0 s S) x]
  rw [smul_sub]

/-- **The differentiated-curvature arm as a fixed smooth Hom-field action.**  By the value-local
representation theorem `exists_value_local_appFullSec` (value-locality `diffArmSection_value_local`,
`ℝ`-linearity `diffArmSection_toSection_add` / `_smul`), there is a smooth full Hom-bundle field `H_dR`
with `diffArmSection g s S = appFullSec H_dR S` for every smooth compactly-supported `(0, s)`-tensor `S`. -/
theorem exists_diffArmSection_appFullSec (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ H_dR : HomTensorRSField (E := E) (M := M) 0 s (s + 1) I,
      ∀ S : SmoothCcTensor g 0 s,
        diffArmSection (I := I) (M := M) g s S =
          appFullSec (I := I) (M := M) g 0 s (s + 1) H_dR S :=
  exists_value_local_appFullSec (I := I) (M := M) g 0 s (s + 1)
    (fun S => diffArmSection (I := I) (M := M) g s S)
    (fun S₁ S₂ x => diffArmSection_toSection_add (I := I) (M := M) g s S₁ S₂ x)
    (fun c S x => diffArmSection_toSection_smul (I := I) (M := M) g s c S x)
    (fun S₁ S₂ x hS => diffArmSection_value_local (I := I) (M := M) g s S₁ S₂ x hS)

/-- **The first-order Hom-field section identity of the order-`2` commutator defect.** For a closed
smooth Riemannian manifold `(M, g)` there are fixed smooth full Hom-bundle field sections
`H_R : Hom(T^{(0,s+1)}, T^{(0,s+1)})` and `H_dR : Hom(T^{(0,s)}, T^{(0,s+1)})` such that, for every
smooth compactly-supported `(0, s)`-tensor `S`,
```
pointwiseTensorCurv g s S = H_R · ∇S + H_dR · S
```
where `Curv S := Δ_∇(∇S) − ∇(Δ_∇ S)`, `∇S := covGrad g 0 s S`, and `·` is the full Hom-bundle action
`appFullSec`.  This is the **first-order** content of the defect: it carries the `1`-jet `(∇S, S)` only,
never `∇²S`.

The two fields are the gradient-reading curvature arm `H_R` (the `R(∇S)`-content, the moving-frame
curvature trace `gradArmSection`, value-local in `∇S(x)`) and the differentiated-curvature arm `H_dR`
(the `(∇R)·S`-content, `diffArmSection = Curv − gradArmSection(∇S)`, value-local in `S(x)` by the
proven divergence-of-curvature collapse).  The defining decomposition `Curv S = gradArmSection g s (∇S)
+ diffArmSection g s S` holds by definition of `diffArmSection`; each arm is then factored as a fixed
smooth Hom-field action through the value-local representation theorem `exists_value_local_appFullSec`. -/
theorem exists_pointwiseTensorCurv_firstOrder_homField_section
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ (H_R : HomTensorRSField (E := E) (M := M) 0 (s + 1) (s + 1) I)
      (H_dR : HomTensorRSField (E := E) (M := M) 0 s (s + 1) I),
      ∀ S : SmoothCcTensor g 0 s,
        pointwiseTensorCurv (I := I) (M := M) g s S =
          appFullSec (I := I) (M := M) g 0 (s + 1) (s + 1) H_R
            (covGrad (I := I) (M := M) g 0 s S) +
          appFullSec (I := I) (M := M) g 0 s (s + 1) H_dR S := by
  obtain ⟨H_R, hH_R⟩ := exists_gradArmSection_appFullSec (I := I) (M := M) (E := E) g s
  obtain ⟨H_dR, hH_dR⟩ := exists_diffArmSection_appFullSec (I := I) (M := M) (E := E) g s
  refine ⟨H_R, H_dR, fun S => ?_⟩

  have hdecomp : pointwiseTensorCurv (I := I) (M := M) g s S =
      gradArmSection (I := I) (M := M) g s (covGrad (I := I) (M := M) g 0 s S) +
        diffArmSection (I := I) (M := M) g s S := by
    rw [diffArmSection]
    abel
  rw [hdecomp, hH_R (covGrad (I := I) (M := M) g 0 s S), hH_dR S]

end Connection
end Integral
end DifferentialGeometry

end
