import DifferentialGeometry.PDE.RicciFlow.SobolevEmbedding
import DifferentialGeometry.PDE.RicciFlow.SobolevEmbeddingCmRankReduction
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcDense
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Module.Completion

/-!
# The continuous Sobolev embedding as a continuous linear map

For a closed Riemannian manifold `(M, g)` and a supercritical order
`2 * k > dim M`, the intrinsic order-`2k` Sobolev space of `(r, s)`-tensor
sections embeds continuously into the sup-norm space of bounded continuous
tensor sections.  The pointwise bound

  `‖T.toSection x‖_g ≤ C * ‖T.toHs (2k)‖`

(proved on the dense smooth subspace by `tensorPouSobolevHilbert_embedding_Ck`,
in the genuine Riemannian fibre norm) is here promoted from the dense subspace
of smooth compactly-supported sections to a genuine **continuous linear map** on
the whole Sobolev Hilbert space `TensorPouSobolevHilbert g r s (2k)`.

## The sup-norm target Banach space

The model fibre norm of the tensor bundle is chart-dependent and has unbounded
operator norm on compact multi-chart manifolds (the chart-transition Jacobian
blows up), so the target cannot be the model-norm bounded-continuous-functions
space.  Instead the target is built from the **Riemannian fibre norm**: the
seminorm

  `‖T‖_{C⁰} = ⨆ x, ‖T.toSection x‖_g`

on smooth compactly-supported sections (finite by the embedding bound at
supercritical order), realized as a `SeminormedAddCommGroup` and completed to a
genuine Banach space `CSupBanach`.  The completion is the abstract
chart-locality-free `C⁰` space of `(r, s)`-tensor sections.

## Main definitions

* `gSupSeminorm g r s k` — the `C⁰` Riemannian-fibre sup-seminorm on
  `SmoothCcTensorHs g r s (2k)` (packaged as an `AddGroupSeminorm`), with its
  induced `SeminormedAddCommGroup` / `NormedSpace ℝ` structure on the wrapper
  `CSupTensor g r s k`.
* `CSupBanach g r s k` — the completion of `CSupTensor g r s k`, a real Banach
  space (the abstract sup-norm `C⁰` tensor-section space).
* `tensorHsToC0 g r s k h_super` — the **continuous linear map**
  `TensorPouSobolevHilbert g r s (2k) →L[ℝ] CSupBanach g r s k`, the unique
  bounded linear extension of `T ↦ T.toSection` from the dense smooth subspace.

## Main results

* `tensorHsToC0_apply_coe` — `tensorHsToC0` agrees with the canonical sup-norm
  inclusion of a smooth section on the dense subspace.
* `tensorHsToC0_opNorm_le` — the operator-norm bound
  `‖tensorHsToC0 …‖ ≤ C`, the embedding constant.
* `tensorHsToC0_norm_apply_le` — the pointwise norm bound
  `‖tensorHsToC0 … u‖ ≤ C * ‖u‖` for every `u : H^{2k}`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle Topology Metric
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

set_option linter.unusedSectionVars false in
/-- The fibre value of a sum of sections is the sum of the fibre values. -/
lemma smoothCcTensor_toSection_add_apply
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (S T : SmoothCcTensor g r s) (x : M) :
    (S + T).toSection x = S.toSection x + T.toSection x := by
  rw [SmoothCcTensor.toSection_add]; rfl

set_option linter.unusedSectionVars false in
/-- The fibre value of a scalar multiple of a section is the scalar multiple of
the fibre value. -/
lemma smoothCcTensor_toSection_smul_apply
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (c : ℝ) (T : SmoothCcTensor g r s) (x : M) :
    (c • T).toSection x = c • (T.toSection x) := by
  rw [SmoothCcTensor.toSection_smul]; rfl

set_option linter.unusedSectionVars false in
/-- The fibre value of the negation of a section is the negation of the fibre
value. -/
lemma smoothCcTensor_toSection_neg_apply
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (T : SmoothCcTensor g r s) (x : M) :
    (-T).toSection x = -(T.toSection x) := by
  rw [SmoothCcTensor.toSection_neg]; rfl

set_option linter.unusedSectionVars false in
/-- The fibre value of the zero section is zero. -/
lemma smoothCcTensor_toSection_zero_apply
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (x : M) :
    (0 : SmoothCcTensor g r s).toSection x = 0 := by
  rw [SmoothCcTensor.toSection_zero]; rfl

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- The `C⁰` Riemannian-fibre sup value of a smooth section:
`⨆ x, ‖T.toSection x‖_g`, in the genuine `g`-fibre norm. -/
def gSupVal (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) : ℝ :=
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  ⨆ x : M, ‖T.toSection x‖

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- At supercritical order `2k > dim M`, the fibre-norm range of a smooth
section is bounded above, with explicit bound `C * ‖T.toHs (2k)‖` provided by
the proven Sobolev embedding `tensorPouSobolevHilbert_embedding_Ck`. -/
lemma bddAbove_section_norm_range
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) (T : SmoothCcTensor g r s) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    BddAbove (Set.range (fun x : M => ‖T.toSection x‖)) := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  obtain ⟨C, _, hC⟩ := tensorPouSobolevHilbert_embedding_Ck (I := I) (M := M)
    (g := g) (r := r) (s := s) (k := k) (m := 0) (by omega)
  exact ⟨C * ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) T‖,
    by rintro _ ⟨x, rfl⟩; exact hC T x⟩

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
set_option linter.unusedSectionVars false in
/-- The `C⁰` sup value is nonnegative. -/
lemma gSupVal_nonneg (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) : 0 ≤ gSupVal (I := I) (M := M) g r s T := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  rcases isEmpty_or_nonempty M with hM | hM
  · rw [gSupVal, Real.iSup_of_isEmpty]
  · rw [gSupVal]; exact Real.iSup_nonneg (fun x => norm_nonneg _)

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
set_option linter.unusedSectionVars false in
/-- The `C⁰` sup value of the zero section is zero. -/
lemma gSupVal_zero (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    gSupVal (I := I) (M := M) g r s 0 = 0 := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  rw [gSupVal]
  have hz : (fun x : M => ‖(0 : SmoothCcTensor g r s).toSection x‖)
      = fun _ => (0 : ℝ) := by
    funext x; rw [smoothCcTensor_toSection_zero_apply, norm_zero]
  rw [hz]
  rcases isEmpty_or_nonempty M with hM | hM
  · rw [Real.iSup_of_isEmpty]
  · rw [ciSup_const]

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
set_option linter.unusedSectionVars false in
/-- The `C⁰` sup value is invariant under negation. -/
lemma gSupVal_neg (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) :
    gSupVal (I := I) (M := M) g r s (-T) = gSupVal (I := I) (M := M) g r s T := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  rw [gSupVal, gSupVal]
  congr 1; funext x
  rw [smoothCcTensor_toSection_neg_apply, norm_neg]

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
set_option linter.unusedSectionVars false in
/-- Subadditivity of the `C⁰` sup value (at supercritical order, where the
ranges are bounded above). -/
lemma gSupVal_add_le (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) (S T : SmoothCcTensor g r s) :
    gSupVal (I := I) (M := M) g r s (S + T) ≤
      gSupVal (I := I) (M := M) g r s S + gSupVal (I := I) (M := M) g r s T := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  rcases isEmpty_or_nonempty M with hM | hM
  · simp only [gSupVal]
    rw [Real.iSup_of_isEmpty, Real.iSup_of_isEmpty, Real.iSup_of_isEmpty]; norm_num
  · have hbS := bddAbove_section_norm_range (I := I) (M := M) g r s k hk S
    have hbT := bddAbove_section_norm_range (I := I) (M := M) g r s k hk T
    rw [gSupVal, gSupVal, gSupVal]
    refine Real.iSup_le (fun x => ?_)
      (add_nonneg (gSupVal_nonneg (I := I) (M := M) g r s S)
        (gSupVal_nonneg (I := I) (M := M) g r s T))
    have hpt : ‖(S + T).toSection x‖ ≤ ‖S.toSection x‖ + ‖T.toSection x‖ := by
      rw [smoothCcTensor_toSection_add_apply]; exact norm_add_le _ _
    exact le_trans hpt (add_le_add (le_ciSup hbS x) (le_ciSup hbT x))

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
set_option linter.unusedSectionVars false in
/-- Absolute homogeneity of the `C⁰` sup value (at supercritical order). -/
lemma gSupVal_smul_le (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) (c : ℝ) (T : SmoothCcTensor g r s) :
    gSupVal (I := I) (M := M) g r s (c • T) ≤
      |c| * gSupVal (I := I) (M := M) g r s T := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  rcases isEmpty_or_nonempty M with hM | hM
  · simp only [gSupVal]
    rw [Real.iSup_of_isEmpty, Real.iSup_of_isEmpty, mul_zero]
  · have hbT := bddAbove_section_norm_range (I := I) (M := M) g r s k hk T
    rw [gSupVal, gSupVal]
    refine Real.iSup_le (fun x => ?_)
      (mul_nonneg (abs_nonneg c) (gSupVal_nonneg (I := I) (M := M) g r s T))
    have hpt : ‖(c • T).toSection x‖ = |c| * ‖T.toSection x‖ := by
      rw [smoothCcTensor_toSection_smul_apply, norm_smul, Real.norm_eq_abs]
    rw [hpt]
    exact mul_le_mul_of_nonneg_left (le_ciSup hbT x) (abs_nonneg c)

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
set_option linter.unusedSectionVars false in
/-- Absolute homogeneity (equality) of the `C⁰` sup value at supercritical
order.  At supercritical order all fibre-norm ranges are bounded above, so the
suprema are genuine; the reverse inequality to `gSupVal_smul_le` is recovered by
applying `gSupVal_smul_le` to `c⁻¹ • (c • T)`. -/
lemma gSupVal_smul (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) (c : ℝ) (T : SmoothCcTensor g r s) :
    gSupVal (I := I) (M := M) g r s (c • T) =
      |c| * gSupVal (I := I) (M := M) g r s T := by
  rcases eq_or_ne c 0 with hc | hc
  · subst hc
    rw [zero_smul, gSupVal_zero, abs_zero, zero_mul]
  · refine le_antisymm (gSupVal_smul_le (I := I) (M := M) g r s k hk c T) ?_
    have hstep := gSupVal_smul_le (I := I) (M := M) g r s k hk c⁻¹ (c • T)
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul] at hstep
    have hcpos : 0 < |c| := abs_pos.mpr hc
    rw [abs_inv] at hstep
    have h2 : |c| * gSupVal (I := I) (M := M) g r s T ≤
        |c| * (|c|⁻¹ * gSupVal (I := I) (M := M) g r s (c • T)) :=
      mul_le_mul_of_nonneg_left hstep (le_of_lt hcpos)
    rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hcpos), one_mul] at h2

/-- A fresh Lean wrapper around the order-`2k` smooth pre-Hilbert sections,
carrying the `C⁰` Riemannian-fibre sup-seminorm (instead of the `H^{2k}`
Sobolev norm).  Used as the pre-completion type of the abstract `C⁰` Banach
space. -/
structure CSupTensor (g : SmoothRiemannianMetric I M) (r s k : ℕ) where
  /-- The underlying order-`2k` smooth compactly-supported section wrapper. -/
  toHsTensor : IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k)

namespace CSupTensor

variable {g : SmoothRiemannianMetric I M} {r s k : ℕ}

/-- Two `CSupTensor` are equal iff their underlying section wrappers agree. -/
@[ext] theorem ext {S T : CSupTensor g r s k}
    (h : S.toHsTensor = T.toHsTensor) : S = T := by
  cases S; cases T; congr

/-- `toHsTensor` is injective. -/
lemma toHsTensor_injective :
    Function.Injective
      (fun S : CSupTensor g r s k => S.toHsTensor) := by
  intro S T h; exact ext h

instance : Zero (CSupTensor g r s k) := ⟨⟨0⟩⟩
instance : Add (CSupTensor g r s k) :=
  ⟨fun S T => ⟨S.toHsTensor + T.toHsTensor⟩⟩
instance : Neg (CSupTensor g r s k) := ⟨fun S => ⟨-S.toHsTensor⟩⟩
instance : Sub (CSupTensor g r s k) :=
  ⟨fun S T => ⟨S.toHsTensor - T.toHsTensor⟩⟩
instance : SMul ℝ (CSupTensor g r s k) :=
  ⟨fun c S => ⟨c • S.toHsTensor⟩⟩

@[simp] lemma toHsTensor_zero :
    (0 : CSupTensor g r s k).toHsTensor = 0 := rfl
@[simp] lemma toHsTensor_add (S T : CSupTensor g r s k) :
    (S + T).toHsTensor = S.toHsTensor + T.toHsTensor := rfl
@[simp] lemma toHsTensor_neg (S : CSupTensor g r s k) :
    (-S).toHsTensor = -S.toHsTensor := rfl
@[simp] lemma toHsTensor_sub (S T : CSupTensor g r s k) :
    (S - T).toHsTensor = S.toHsTensor - T.toHsTensor := rfl
@[simp] lemma toHsTensor_smul (c : ℝ) (S : CSupTensor g r s k) :
    (c • S).toHsTensor = c • S.toHsTensor := rfl

instance : SMul ℕ (CSupTensor g r s k) := ⟨nsmulRec⟩
instance : SMul ℤ (CSupTensor g r s k) := ⟨zsmulRec⟩

@[simp] lemma toHsTensor_nsmul (S : CSupTensor g r s k) (n : ℕ) :
    (n • S).toHsTensor = n • S.toHsTensor := by
  induction n with
  | zero =>
      change (nsmulRec 0 S).toHsTensor = (0 : ℕ) • S.toHsTensor
      simp [nsmulRec]
  | succ n ih =>
      change (nsmulRec (n + 1) S).toHsTensor = (n + 1) • S.toHsTensor
      change (nsmulRec n S + S).toHsTensor = (n + 1) • S.toHsTensor
      have hn : (nsmulRec n S).toHsTensor = n • S.toHsTensor := ih
      rw [toHsTensor_add, hn, succ_nsmul]

@[simp] lemma toHsTensor_zsmul (S : CSupTensor g r s k) (z : ℤ) :
    (z • S).toHsTensor = z • S.toHsTensor := by
  rcases z with n | n
  · change (n • S).toHsTensor = (Int.ofNat n) • S.toHsTensor
    rw [toHsTensor_nsmul]; simp
  · change (-((n + 1) • S)).toHsTensor = (Int.negSucc n) • S.toHsTensor
    rw [toHsTensor_neg, toHsTensor_nsmul]
    show -((n + 1) • S.toHsTensor) = Int.negSucc n • S.toHsTensor
    rw [show (Int.negSucc n : ℤ) = -((n + 1 : ℕ) : ℤ) from rfl,
      neg_zsmul, natCast_zsmul]

instance : AddCommGroup (CSupTensor g r s k) :=
  toHsTensor_injective.addCommGroup
    (fun S => S.toHsTensor)
    toHsTensor_zero
    toHsTensor_add
    toHsTensor_neg
    toHsTensor_sub
    toHsTensor_nsmul
    toHsTensor_zsmul

/-- Additive-monoid hom to the underlying order-`2k` section wrapper. -/
def toHsTensorAddHom :
    CSupTensor g r s k →+ IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k) where
  toFun := fun S => S.toHsTensor
  map_zero' := toHsTensor_zero
  map_add' := toHsTensor_add

instance : Module ℝ (CSupTensor g r s k) :=
  toHsTensor_injective.module ℝ toHsTensorAddHom toHsTensor_smul

/-- The wrapping `SmoothCcTensorHs g r s (2k) → CSupTensor g r s k` as an
`ℝ`-linear map (it reuses the underlying additive / module structure). -/
def ofHs :
    IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k) →ₗ[ℝ] CSupTensor g r s k where
  toFun := fun S => ⟨S⟩
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

@[simp] lemma ofHs_apply
    (S : IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k)) :
    (ofHs (g := g) (r := r) (s := s) (k := k) S).toHsTensor = S := rfl

/-- The underlying raw smooth section of a `CSupTensor`. -/
def toCc (S : CSupTensor g r s k) : SmoothCcTensor g r s :=
  S.toHsTensor.toCcTensor

@[simp] lemma toCc_zero : (0 : CSupTensor g r s k).toCc = 0 := rfl
@[simp] lemma toCc_add (S T : CSupTensor g r s k) :
    (S + T).toCc = S.toCc + T.toCc := rfl
@[simp] lemma toCc_neg (S : CSupTensor g r s k) : (-S).toCc = -S.toCc := rfl
@[simp] lemma toCc_smul (c : ℝ) (S : CSupTensor g r s k) :
    (c • S).toCc = c • S.toCc := rfl

end CSupTensor

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
set_option linter.unusedSectionVars false in
/-- The `C⁰` Riemannian-fibre sup-seminorm packaged as an `AddGroupSeminorm` on
`CSupTensor g r s k`, valid at supercritical order `2k > dim M`. -/
def gSupAddGroupSeminorm (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) :
    AddGroupSeminorm (CSupTensor g r s k) where
  toFun := fun S => gSupVal (I := I) (M := M) g r s S.toCc
  map_zero' := by
    change gSupVal (I := I) (M := M) g r s (0 : CSupTensor g r s k).toCc = 0
    rw [CSupTensor.toCc_zero, gSupVal_zero]
  add_le' := fun S T => by
    change gSupVal (I := I) (M := M) g r s (S + T).toCc ≤
      gSupVal (I := I) (M := M) g r s S.toCc +
        gSupVal (I := I) (M := M) g r s T.toCc
    rw [CSupTensor.toCc_add]
    exact gSupVal_add_le (I := I) (M := M) g r s k hk S.toCc T.toCc
  neg' := fun S => by
    change gSupVal (I := I) (M := M) g r s (-S).toCc =
      gSupVal (I := I) (M := M) g r s S.toCc
    rw [CSupTensor.toCc_neg, gSupVal_neg]

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
set_option linter.unusedSectionVars false in
/-- The `SeminormedAddCommGroup` structure on `CSupTensor g r s k` induced by the
`C⁰` sup-seminorm, valid at supercritical order. -/
@[reducible] noncomputable def csupSeminormedAddCommGroup
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) :
    SeminormedAddCommGroup (CSupTensor g r s k) :=
  AddGroupSeminorm.toSeminormedAddCommGroup
    (gSupAddGroupSeminorm (I := I) (M := M) g r s k hk)

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
set_option linter.unusedSectionVars false in
/-- The norm on `CSupTensor g r s k` (with the sup-seminorm structure) is exactly
the `C⁰` sup value of the underlying section. -/
lemma csupSeminormedAddCommGroup_norm
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) (S : CSupTensor g r s k) :
    @norm _ (csupSeminormedAddCommGroup (I := I) (M := M) g r s k hk).toNorm S =
      gSupVal (I := I) (M := M) g r s S.toCc := rfl

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
set_option linter.unusedSectionVars false in
/-- The `NormedSpace ℝ` structure on `CSupTensor g r s k` for the sup-seminorm,
valid at supercritical order. -/
@[reducible] noncomputable def csupNormedSpace
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) :
    letI := csupSeminormedAddCommGroup (I := I) (M := M) g r s k hk
    NormedSpace ℝ (CSupTensor g r s k) :=
  letI := csupSeminormedAddCommGroup (I := I) (M := M) g r s k hk
  NormedSpace.mk (𝕜 := ℝ) (E := CSupTensor g r s k) fun c S => by
    have h1 : ‖c • S‖ = gSupVal (I := I) (M := M) g r s (c • S).toCc :=
      csupSeminormedAddCommGroup_norm (I := I) (M := M) g r s k hk (c • S)
    have h2 : ‖S‖ = gSupVal (I := I) (M := M) g r s S.toCc :=
      csupSeminormedAddCommGroup_norm (I := I) (M := M) g r s k hk S
    rw [h1, h2, CSupTensor.toCc_smul,
      gSupVal_smul (I := I) (M := M) g r s k hk c S.toCc, Real.norm_eq_abs]

/-- The abstract `C⁰` tensor-section Banach space: the completion of
`CSupTensor g r s k` in the `C⁰` sup-seminorm.  This is a genuine real Banach
space (complete, `NormedAddCommGroup`, `NormedSpace ℝ`), chart-locality-free. -/
noncomputable def CSupBanach (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) : Type _ :=
  letI := csupSeminormedAddCommGroup (I := I) (M := M) g r s k hk
  UniformSpace.Completion (CSupTensor g r s k)

noncomputable instance instCSupBanachNormedAddCommGroup
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) :
    NormedAddCommGroup (CSupBanach (I := I) (M := M) g r s k hk) :=
  letI := csupSeminormedAddCommGroup (I := I) (M := M) g r s k hk
  (inferInstance :
    NormedAddCommGroup (UniformSpace.Completion (CSupTensor g r s k)))

noncomputable instance instCSupBanachNormedSpace
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) :
    NormedSpace ℝ (CSupBanach (I := I) (M := M) g r s k hk) :=
  letI := csupSeminormedAddCommGroup (I := I) (M := M) g r s k hk
  letI := csupNormedSpace (I := I) (M := M) g r s k hk
  (inferInstance :
    NormedSpace ℝ (UniformSpace.Completion (CSupTensor g r s k)))

instance instCSupBanachCompleteSpace
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) :
    CompleteSpace (CSupBanach (I := I) (M := M) g r s k hk) :=
  letI := csupSeminormedAddCommGroup (I := I) (M := M) g r s k hk
  (inferInstance :
    CompleteSpace (UniformSpace.Completion (CSupTensor g r s k)))

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
set_option linter.unusedSectionVars false in
/-- The smooth-level `C⁰` inclusion: a linear map sending a smooth section
(viewed at order `2k`) to its image in the abstract `C⁰` Banach space.  It is
the composite of `CSupTensor.ofHs` with the completion coercion `toComplL`. -/
noncomputable def smoothToC0Lin
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) :
    IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k) →ₗ[ℝ]
      CSupBanach (I := I) (M := M) g r s k hk :=
  letI := csupSeminormedAddCommGroup (I := I) (M := M) g r s k hk
  letI := csupNormedSpace (I := I) (M := M) g r s k hk
  (UniformSpace.Completion.toComplL :
    CSupTensor g r s k →L[ℝ]
      UniformSpace.Completion (CSupTensor g r s k)).toLinearMap.comp
    (CSupTensor.ofHs (g := g) (r := r) (s := s) (k := k))

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
set_option linter.unusedSectionVars false in
/-- The norm of the smooth-level `C⁰` inclusion of a section equals the `C⁰`
sup value of the underlying raw section. -/
lemma norm_smoothToC0Lin
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E)
    (S : IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k)) :
    ‖smoothToC0Lin (I := I) (M := M) g r s k hk S‖ =
      gSupVal (I := I) (M := M) g r s S.toCcTensor := by
  letI := csupSeminormedAddCommGroup (I := I) (M := M) g r s k hk
  letI := csupNormedSpace (I := I) (M := M) g r s k hk
  have hiso :=
    (UniformSpace.Completion.toComplₗᵢ :
        CSupTensor g r s k →ₗᵢ[ℝ]
          UniformSpace.Completion (CSupTensor g r s k)).norm_map
      (CSupTensor.ofHs (g := g) (r := r) (s := s) (k := k) S)
  have hval : ‖smoothToC0Lin (I := I) (M := M) g r s k hk S‖ =
      ‖(CSupTensor.ofHs (g := g) (r := r) (s := s) (k := k) S :
        CSupTensor g r s k)‖ := hiso
  rw [hval, csupSeminormedAddCommGroup_norm (I := I) (M := M) g r s k hk]
  rfl

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
set_option linter.unusedSectionVars false in
/-- The norm of the canonical inclusion of `S` into the source Sobolev Hilbert
space equals the `H^{2k}` norm of the underlying section. -/
lemma norm_coe_toCompl_eq_toHs
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (S : IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k)) :
    ‖(S : TensorPouSobolevHilbert g r s (2 * k))‖ =
      ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) S.toCcTensor‖ := by
  have hrhs : SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) S.toCcTensor =
      ((⟨S.toCcTensor⟩ : IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k)) :
        TensorPouSobolevHilbert g r s (2 * k)) := rfl
  have hS : (⟨S.toCcTensor⟩ : IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k)) = S := by
    cases S; rfl
  rw [hrhs, hS]

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
set_option linter.unusedSectionVars false in
/-- The smooth-level `C⁰` inclusion is bounded by the embedding constant times
the `H^{2k}` inclusion: this is the proven Sobolev embedding bound, repackaged
on the dense subspace.  Output: there is `0 < C` such that for every smooth
section `S`,
`‖smoothToC0Lin S‖_{C⁰} ≤ C * ‖(S : H^{2k})‖`. -/
lemma exists_smoothToC0Lin_norm_le
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) :
    ∃ C : ℝ, 0 < C ∧
      ∀ S : IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k),
        ‖smoothToC0Lin (I := I) (M := M) g r s k hk S‖ ≤
          C * ‖(S : TensorPouSobolevHilbert g r s (2 * k))‖ := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  obtain ⟨C, hCpos, hC⟩ := tensorPouSobolevHilbert_embedding_Ck (I := I) (M := M)
    (g := g) (r := r) (s := s) (k := k) (m := 0) (by omega)
  refine ⟨C, hCpos, fun S => ?_⟩
  rw [norm_smoothToC0Lin (I := I) (M := M) g r s k hk S,
    norm_coe_toCompl_eq_toHs (I := I) (M := M) g r s k S]
  rcases isEmpty_or_nonempty M with hM | hM
  · rw [gSupVal, Real.iSup_of_isEmpty]
    exact mul_nonneg (le_of_lt hCpos) (norm_nonneg _)
  · rw [gSupVal]
    refine Real.iSup_le (fun x => ?_)
      (mul_nonneg (le_of_lt hCpos) (norm_nonneg _))
    exact hC S.toCcTensor x

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
set_option linter.unusedSectionVars false in
/-- **The continuous Sobolev embedding as a continuous linear map.**

At supercritical order `2k > dim M`, the intrinsic order-`2k` Sobolev Hilbert
space of `(r, s)`-tensor sections embeds **continuously and linearly** into the
abstract `C⁰` Banach space `CSupBanach g r s k hk` (bounded continuous sections
in the Riemannian fibre sup-norm).  It is the unique bounded linear extension of
the smooth-level inclusion `smoothToC0Lin` along the dense linear coercion into
the completion, produced by `LinearMap.extendOfNorm`. -/
noncomputable def tensorHsToC0
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) :
    TensorPouSobolevHilbert g r s (2 * k) →L[ℝ]
      CSupBanach (I := I) (M := M) g r s k hk :=
  (smoothToC0Lin (I := I) (M := M) g r s k hk).extendOfNorm
    (UniformSpace.Completion.toComplL :
      IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k) →L[ℝ]
        TensorPouSobolevHilbert g r s (2 * k)).toLinearMap

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
set_option linter.unusedSectionVars false in
/-- The dense linear coercion `SmoothCcTensorHs g r s (2k) → H^{2k}` has dense
range. -/
lemma denseRange_toComplL_toLinearMap
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    DenseRange
      ⇑(UniformSpace.Completion.toComplL :
        IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k) →L[ℝ]
          TensorPouSobolevHilbert g r s (2 * k)).toLinearMap := by
  have hcoe : ⇑(UniformSpace.Completion.toComplL :
        IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k) →L[ℝ]
          TensorPouSobolevHilbert g r s (2 * k)).toLinearMap =
      ((↑) : IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k) →
        UniformSpace.Completion (IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k))) := by
    funext S; rfl
  rw [hcoe]
  exact UniformSpace.Completion.denseRange_coe

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
set_option linter.unusedSectionVars false in
/-- **Agreement on the dense smooth subspace.**  On a smooth section `S`, the
continuous linear embedding `tensorHsToC0` agrees with the smooth-level
inclusion `smoothToC0Lin S` (the canonical `C⁰` image of `S`). -/
theorem tensorHsToC0_coe
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E)
    (S : IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k)) :
    tensorHsToC0 (I := I) (M := M) g r s k hk
        (S : TensorPouSobolevHilbert g r s (2 * k)) =
      smoothToC0Lin (I := I) (M := M) g r s k hk S := by
  obtain ⟨C, _, hC⟩ := exists_smoothToC0Lin_norm_le (I := I) (M := M) g r s k hk
  have h := LinearMap.extendOfNorm_eq
    (f := smoothToC0Lin (I := I) (M := M) g r s k hk)
    (e := (UniformSpace.Completion.toComplL :
      IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k) →L[ℝ]
        TensorPouSobolevHilbert g r s (2 * k)).toLinearMap)
    (denseRange_toComplL_toLinearMap (I := I) (M := M) g r s k)
    ⟨C, hC⟩ S
  exact h

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
set_option linter.unusedSectionVars false in
/-- **The pointwise norm bound.**  For every Sobolev element `u : H^{2k}`,
`‖tensorHsToC0 u‖_{C⁰} ≤ C * ‖u‖_{H^{2k}}`, where `C` is the embedding constant.
This is the headline continuous embedding `H^{2k} ↪ C⁰`. -/
theorem tensorHsToC0_norm_apply_le
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) :
    ∃ C : ℝ, 0 < C ∧
      ∀ u : TensorPouSobolevHilbert g r s (2 * k),
        ‖tensorHsToC0 (I := I) (M := M) g r s k hk u‖ ≤ C * ‖u‖ := by
  obtain ⟨C, hCpos, hC⟩ := exists_smoothToC0Lin_norm_le (I := I) (M := M) g r s k hk
  refine ⟨C, hCpos, fun u => ?_⟩
  exact LinearMap.norm_extendOfNorm_apply_le
    (denseRange_toComplL_toLinearMap (I := I) (M := M) g r s k) C hC u

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
set_option linter.unusedSectionVars false in
/-- **The operator-norm bound.**  The operator norm of the continuous Sobolev
embedding `tensorHsToC0` is bounded by the embedding constant `C`. -/
theorem tensorHsToC0_opNorm_le
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) :
    ∃ C : ℝ, 0 < C ∧ ‖tensorHsToC0 (I := I) (M := M) g r s k hk‖ ≤ C := by
  obtain ⟨C, hCpos, hC⟩ := exists_smoothToC0Lin_norm_le (I := I) (M := M) g r s k hk
  refine ⟨C, hCpos, ?_⟩
  exact LinearMap.opNorm_extendOfNorm_le
    (denseRange_toComplL_toLinearMap (I := I) (M := M) g r s k)
    (le_of_lt hCpos) hC

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
set_option linter.unusedSectionVars false in
/-- **The eigenfunction sup bound (unit-element form).**  For a Sobolev element
`u` of unit `H^{2k}` norm, its `C⁰` (Riemannian-fibre sup) norm is bounded by
the embedding constant `C`.  Applied to an `H^{2k}`-normalised eigentensor of
the resolvent `(1 - Δ)`, this is exactly the per-eigenfunction sup bound used by
the spectral counting argument: if `‖b‖_{H^{2k}} ≤ (1 + λ)^k` then
`‖tensorHsToC0 b‖_{C⁰} ≤ C (1 + λ)^k`. -/
theorem tensorHsToC0_norm_le_of_norm_le
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : TensorPouSobolevHilbert g r s (2 * k)) (B : ℝ), ‖u‖ ≤ B →
        ‖tensorHsToC0 (I := I) (M := M) g r s k hk u‖ ≤ C * B := by
  obtain ⟨C, hCpos, hC⟩ := tensorHsToC0_norm_apply_le (I := I) (M := M) g r s k hk
  refine ⟨C, hCpos, fun u B hB => ?_⟩
  calc ‖tensorHsToC0 (I := I) (M := M) g r s k hk u‖ ≤ C * ‖u‖ := hC u
    _ ≤ C * B := mul_le_mul_of_nonneg_left hB (le_of_lt hCpos)

end DifferentialGeometry.PDE.RicciFlow

end
