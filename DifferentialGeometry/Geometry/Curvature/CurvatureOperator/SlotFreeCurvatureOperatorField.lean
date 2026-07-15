import DifferentialGeometry.Geometry.Connection.TensorNabla.FullHomCovariantCalculusRS
import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldCovariantCalculus
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradParallelNaturality
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection

/-!
# The two-free-slot curvature operator Hom-field

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file constructs the
**two-free-slot curvature operator Hom-field** `Θ s : Hom(T^{(0,s)}, T^{(0,s+2)})`: the fixed smooth
second-order Hom-bundle field whose full Hom-bundle action `appFullSec (Θ s) S` on a smooth
compactly-supported `(0, s)`-tensor `S` evaluates, in the two leading free slots `(u, w)`, to *minus*
the slot-wise curvature sum

```
(Θ s · S)(x)(u, w, m₁, …, m_s) = − ∑ₖ S(x)(m₁, …, R_x(u, w) m_k, …, m_s),
```

the derivation action of the tangent-bundle Riemann curvature `R = riemannOp (LeviCivita g)` across
the `s` covariant slots of `S`, with the two curvature directions `(u, w)` re-exposed as the two new
leading covariant slots.  This is exactly the value of the curvature operator of the induced
`(0, s)`-tensor connection, packaged frame-free as a *fixed* smooth Hom-bundle field, so that the
operator-field covariant calculus (`covGrad_appFullSec_eq`) and the uniform fibre contraction
envelope (`exists_uniform_riemannianFiberNormSq_appFullRS_le`) apply to it `S`- and `x`-uniformly.

## Construction

Everything is assembled from two elementary fibre operators and their base-point smoothness:

* `slotInsertEndoFib s k x Λ` — the **slot-`k` insertion endomorphism** of the `(0, s)`-tensor
  fibre: precompose the `k`-th covariant slot with a fixed tangent endomorphism `Λ`,
  `A ↦ A(…, Λ(·_k), …)`, realised through `ContinuousMultilinearMap.compContinuousLinearMap` with
  the identity in every other slot.  Its smoothness in the base point (for a smooth endomorphism
  field `Λ = φ x`) is proved by induction on `s` through the two leading-slot conjugation
  identities: at slot `0` it is the curry conjugation of right-composition by `φ x`
  (`tensor0S_curry`), and at slot `k + 1` it is the slot extension (`slotExtendFib`) of the slot-`k`
  insertion one rank below.
* `slotCurvSumFib g s x u w` — minus the sum over `k` of the slot-`k` insertions of the curvature
  endomorphism `R_x(u, w)`; bilinear in `(u, w)` because `riemannOp` is.
* `slotFreeCurvOpFib g s x` — the fibre operator `T^{(0,s)}_x →L T^{(0,s+2)}_x`: the double
  leading-slot uncurry (`tensor0S_curry.symm`, twice) of `(u, w) ↦ slotCurvSumFib g s x u w A`.
* `slotFreeCurvHomField g s` — the Hom-bundle field `Θ s`, post-composition by
  `slotFreeCurvOpFib g s x` on the `(0, s)`-tensor fibre, packaged as a smooth section of the
  second-order Hom-bundle `Hom(T^{(0,s)}, T^{(0,s+2)})`.

## Main result

* `exists_slotFreeCurvOpField_baseSlot_eval` — the existence form consumed by the bracket-channel
  fibre-order line: a Hom-field family `Θ` such that for every rank `s`, tensor `S`, point `x` and
  tangent data `(u, w, m)`,
  `(appFullSec (Θ s) S)(x)(unit)(u, w, m) = − ∑ₖ S(x)(unit)(m with slot k hit by R_x(u, w))`.

The construction is frame-free: only the smooth metric `g` and the bundled Levi-Civita curvature
operator `riemannOp (LeviCivita g)` (smooth by `riemannOp_section_contMDiff`) enter; no orthonormal
frame, chart selection, or per-direction extension jet appears in the field.
-/

noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2
open TensorMultilinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option linter.unusedSectionVars false in
/-- Two `(0, s)`-tensor fibre elements agreeing on every model tuple under
`Tensor0SSpace.toModel` are equal: the model identification is a continuous linear equivalence,
hence injective, and continuous multilinear maps are determined by their values. -/
private lemma tensor0S_eq_of_toModel_eq {s : ℕ} {x : M} {T T' : Tensor0SSpace s I x}
    (h : ∀ v : Fin s → E, Tensor0SSpace.toModel T v = Tensor0SSpace.toModel T' v) : T = T' := by
  have hM : Tensor0SSpace.toModel T = Tensor0SSpace.toModel T' :=
    ContinuousMultilinearMap.ext h
  exact Tensor0SSpace.toModel_injective hM

set_option linter.unusedSectionVars false in
/-- `Tensor0SSpace.toModel` commutes with finite sums. -/
private lemma tensor0S_toModel_sum {s : ℕ} {x : M} {ι : Type*} (t : Finset ι)
    (f : ι → Tensor0SSpace s I x) :
    Tensor0SSpace.toModel (∑ i ∈ t, f i) = ∑ i ∈ t, Tensor0SSpace.toModel (f i) := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Tensor0SSpace.toModel_add, ih]

/-! ## The slot-`k` insertion endomorphism of the `(0, s)`-tensor fibre -/

set_option backward.isDefEq.respectTransparency false in
/-- **The slot-`k` insertion endomorphism.** For a fixed tangent endomorphism
`Λ : T_x M →L T_x M`, the continuous linear endomorphism of the `(0, s)`-tensor fibre that
precomposes the `k`-th covariant slot with `Λ` and leaves every other slot untouched:
`A ↦ A(m₁, …, Λ m_k, …, m_s)`.  Realised through the model identification and
`ContinuousMultilinearMap.compContinuousLinearMap` with the slot family `(id, …, Λ, …, id)`. -/
def slotInsertEndoFib (s : ℕ) (k : Fin s) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) :
    Tensor0SSpace s I x →L[ℝ] Tensor0SSpace s I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace s I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun A => Tensor0SSpace.ofModel
        ((Tensor0SSpace.toModel A).compContinuousLinearMap
          (fun i : Fin s => if i = k then Λ else ContinuousLinearMap.id ℝ E))
      map_add' := fun A A' => by
        apply tensor0S_eq_of_toModel_eq (I := I) (M := M)
        intro v
        simp
      map_smul' := fun c A => by
        apply tensor0S_eq_of_toModel_eq (I := I) (M := M)
        intro v
        simp }

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The defining formula for `slotInsertEndoFib`. -/
@[simp] lemma slotInsertEndoFib_apply (s : ℕ) (k : Fin s) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) (A : Tensor0SSpace s I x) :
    slotInsertEndoFib (I := I) (M := M) s k x Λ A =
      Tensor0SSpace.ofModel
        ((Tensor0SSpace.toModel A).compContinuousLinearMap
          (fun i : Fin s => if i = k then Λ else ContinuousLinearMap.id ℝ E)) := by
  rw [slotInsertEndoFib, LinearMap.coe_toContinuousLinearMap']
  rfl

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **The slot-`k` insertion reads its slot through `Λ`:** on a tuple `m` the inserted tensor is
the original tensor on the tuple with the `k`-th entry replaced by `Λ (m k)`. -/
lemma slotInsertEndoFib_apply_eval (s : ℕ) (k : Fin s) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) (A : Tensor0SSpace s I x)
    (m : Fin s → E) :
    Tensor0SSpace.toModel (slotInsertEndoFib (I := I) (M := M) s k x Λ A) m =
      Tensor0SSpace.toModel A (Function.update m k (Λ (m k))) := by
  rw [slotInsertEndoFib_apply, Tensor0SSpace.toModel_ofModel]
  have hfam : (fun i : Fin s =>
      (if i = k then Λ else ContinuousLinearMap.id ℝ E) (m i)) =
      Function.update m k (Λ (m k)) := by
    funext i
    by_cases h : i = k
    · subst h
      simp
    · rw [if_neg h, Function.update_of_ne h]
      rfl
  exact congrArg (fun t => Tensor0SSpace.toModel A t) hfam

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The slot-`k` insertion is additive in the inserted endomorphism. -/
lemma slotInsertEndoFib_add_left (s : ℕ) (k : Fin s) (x : M)
    (Λ₁ Λ₂ : TangentSpace I x →L[ℝ] TangentSpace I x) :
    slotInsertEndoFib (I := I) (M := M) s k x (Λ₁ + Λ₂) =
      slotInsertEndoFib (I := I) (M := M) s k x Λ₁ +
        slotInsertEndoFib (I := I) (M := M) s k x Λ₂ := by
  apply ContinuousLinearMap.ext
  intro A
  rw [ContinuousLinearMap.add_apply]
  apply tensor0S_eq_of_toModel_eq (I := I) (M := M)
  intro v
  rw [slotInsertEndoFib_apply_eval, Tensor0SSpace.toModel_add,
    ContinuousMultilinearMap.add_apply, slotInsertEndoFib_apply_eval,
    slotInsertEndoFib_apply_eval, ContinuousLinearMap.add_apply,
    ContinuousMultilinearMap.map_update_add]

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The slot-`k` insertion is `ℝ`-homogeneous in the inserted endomorphism. -/
lemma slotInsertEndoFib_smul_left (s : ℕ) (k : Fin s) (x : M) (c : ℝ)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) :
    slotInsertEndoFib (I := I) (M := M) s k x (c • Λ) =
      c • slotInsertEndoFib (I := I) (M := M) s k x Λ := by
  apply ContinuousLinearMap.ext
  intro A
  rw [ContinuousLinearMap.smul_apply]
  apply tensor0S_eq_of_toModel_eq (I := I) (M := M)
  intro v
  rw [slotInsertEndoFib_apply_eval, Tensor0SSpace.toModel_smul,
    ContinuousMultilinearMap.smul_apply, slotInsertEndoFib_apply_eval,
    ContinuousLinearMap.smul_apply, ContinuousMultilinearMap.map_update_smul]

/-! ## The two leading-slot conjugation identities

The slot-`0` insertion is the curry conjugation of right-composition by `Λ`; the slot-`(k + 1)`
insertion is the slot extension (`slotExtendFib`) of the slot-`k` insertion one rank below.  These
two identities drive the base-point smoothness induction. -/

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **Slot-`0` insertion is the curry conjugation of right-composition.** -/
lemma slotInsertEndoFib_zero (s : ℕ) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) (A : Tensor0SSpace (s + 1) I x) :
    slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x Λ A =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        (((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) A).comp Λ) := by
  have hcurry : tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
      (slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x Λ A) =
      ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) A).comp Λ := by
    apply ContinuousLinearMap.ext
    intro v0
    apply tensor0S_eq_of_toModel_eq (I := I) (M := M)
    intro vt
    rw [tensor0S_curry_apply_eval, slotInsertEndoFib_apply_eval,
      ContinuousLinearMap.comp_apply, tensor0S_curry_apply_eval]
    congr 1
    rw [Fin.cons_zero, Fin.update_cons_zero]
  rw [← hcurry, ContinuousLinearEquiv.symm_apply_apply]

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **Slot-`(k + 1)` insertion is the slot extension of the slot-`k` insertion.** -/
lemma slotInsertEndoFib_succ (g : SmoothRiemannianMetric I M) (s : ℕ) (j : Fin s) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) :
    slotInsertEndoFib (I := I) (M := M) (s + 1) j.succ x Λ =
      slotExtendFib (I := I) (M := M) g s s x
        (slotInsertEndoFib (I := I) (M := M) s j x Λ) := by
  apply ContinuousLinearMap.ext
  intro A
  have hcurry : tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
      (slotInsertEndoFib (I := I) (M := M) (s + 1) j.succ x Λ A) =
      (slotInsertEndoFib (I := I) (M := M) s j x Λ).comp
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) A) := by
    apply ContinuousLinearMap.ext
    intro v0
    apply tensor0S_eq_of_toModel_eq (I := I) (M := M)
    intro vt
    rw [tensor0S_curry_apply_eval, slotInsertEndoFib_apply_eval,
      ContinuousLinearMap.comp_apply, slotInsertEndoFib_apply_eval,
      tensor0S_curry_apply_eval]
    congr 1
    rw [Fin.cons_succ, ← Fin.cons_update]
  rw [slotExtendFib_apply (I := I) (M := M) g s s x, ← hcurry,
    ContinuousLinearEquiv.symm_apply_apply]

/-! ## Base-point smoothness of the slot-insertion operator field -/

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **Base-point smoothness of the slot-insertion operator field.** For a smooth tangent
endomorphism field `φ`, the fibre field `x ↦ slotInsertEndoFib s k x (φ x)` is a smooth section of
the `(s, s)`-tensor (operator) bundle.  Induction on `s`: at slot `0` the insertion is the curry
conjugation of right-composition by `φ x` (`slotInsertEndoFib_zero`), smooth by the curried-section
transfer and `ContMDiff.clm_bundle_apply`; at slot `k + 1` it is the slot extension of the slot-`k`
insertion one rank below (`slotInsertEndoFib_succ`), smooth by `slotExtendFib_contMDiff` over the
inductive hypothesis. -/
theorem slotInsertEndoFib_contMDiff (g : SmoothRiemannianMetric I M) :
    ∀ (s : ℕ) (k : Fin s) (φ : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x),
      ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
        (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
          (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) x (φ x)) →
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel s s ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (TensorRSModel s s ℝ E)
          (E := fun z : M => TensorRSSpace s s I z) x
          (TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) s k x (φ x)))) := by
  intro s
  induction s with
  | zero => exact fun k => k.elim0
  | succ s ih =>
      intro k φ hφ
      induction k using Fin.cases with
      | zero =>
          apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
            (F₁ := Tensor0SModel (s + 1) ℝ E) (V₁ := fun z : M => Tensor0SSpace (s + 1) I z)
            (F₂ := Tensor0SModel (s + 1) ℝ E) (V₂ := fun z : M => Tensor0SSpace (s + 1) I z)
            (φ := fun x => slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x (φ x))
          intro Y
          have heq : (fun x : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
              (E := fun z : M => Tensor0SSpace (s + 1) I z) x
              (slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x (φ x) (Y x))) =
              (fun x : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
              (E := fun z : M => Tensor0SSpace (s + 1) I z) x
              ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
                (((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x)).comp (φ x)))) := by
            funext x
            rw [slotInsertEndoFib_zero]
          rw [heq]
          have hcurriedY : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)) ∞
              (fun x : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
                (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SSpace s I z) x
                ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x))) :=
            fun x => contMDiffAt_curriedSection_of_contMDiffAt_section (I := I) (M := M)
              (fun y : M => Y y) x (Y.contMDiff x)
          have hG : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)) ∞
              (fun x : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
                (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SSpace s I z) x
                (((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x)).comp (φ x))) := by
            apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
              (F₁ := E) (V₁ := fun z : M => TangentSpace I z)
              (F₂ := Tensor0SModel s ℝ E) (V₂ := fun z : M => Tensor0SSpace s I z)
              (φ := fun x => ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x)).comp (φ x))
            intro Z
            have heqZ : (fun x : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
                (E := fun z : M => Tensor0SSpace s I z) x
                ((((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x)).comp (φ x)) (Z x))) =
                (fun x : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
                (E := fun z : M => Tensor0SSpace s I z) x
                ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x) (φ x (Z x)))) := by
              funext x; rfl
            rw [heqZ]
            have hinner : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
                (fun x : M => TotalSpace.mk' E
                  (E := fun z : M => TangentSpace I z) x (φ x (Z x))) :=
              ContMDiff.clm_bundle_apply (b := id) hφ Z.contMDiff
            exact ContMDiff.clm_bundle_apply (b := id) hcurriedY hinner
          exact contMDiff_uncurriedSection_of_contMDiff_homSection (I := I) (M := M)
            (fun x : M => ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x)).comp (φ x)) hG
      | succ j =>
          have hIH := ih j φ hφ
          set Φ : SmoothCcTensor g s s :=
            { toSection :=
                { toFun := fun x : M =>
                    TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) s j x (φ x))
                  contMDiff_toFun := hIH }
              hasCompactSupport := HasCompactSupport.of_compactSpace _ } with hΦ_def
          have hext := slotExtendFib_contMDiff (I := I) (M := M) g s s Φ
          refine hext.congr ?_
          intro x
          rw [show TensorRSSpace.ofCLM
                (slotInsertEndoFib (I := I) (M := M) (s + 1) (Fin.succ j) x (φ x)) =
              slotExtendFib (I := I) (M := M) g s s x
                (slotInsertEndoFib (I := I) (M := M) s j x (φ x)) from
            slotInsertEndoFib_succ (I := I) (M := M) g s j x (φ x)]
          rfl

/-! ## The bracket slot-sum fibre operator and its bilinearity -/

set_option backward.isDefEq.respectTransparency false in
/-- **The two-direction curvature slot-sum fibre operator.** For tangent vectors `u, w` at `x`,
minus the sum over the `s` covariant slots of the slot-`k` insertion of the curvature endomorphism
`R_x(u, w) = riemannOp (LeviCivita g) x u w`:
`A ↦ − ∑ₖ A(…, R_x(u, w)(·_k), …)`. -/
def slotCurvSumFib (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (u w : TangentSpace I x) :
    Tensor0SSpace s I x →L[ℝ] Tensor0SSpace s I x :=
  -(∑ k : Fin s, slotInsertEndoFib (I := I) (M := M) s k x
      (riemannOp (LeviCivita (I := I) g) x u w))

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **The slot-sum operator evaluates to minus the slot-wise curvature sum.** -/
lemma slotCurvSumFib_apply_eval (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (u w : TangentSpace I x) (A : Tensor0SSpace s I x) (m : Fin s → E) :
    Tensor0SSpace.toModel (slotCurvSumFib (I := I) (M := M) g s x u w A) m =
      - ∑ k : Fin s, Tensor0SSpace.toModel A
          (Function.update m k (riemannOp (LeviCivita (I := I) g) x u w (m k))) := by
  rw [slotCurvSumFib, ContinuousLinearMap.neg_apply, ContinuousLinearMap.sum_apply,
    Tensor0SSpace.toModel_neg, tensor0S_toModel_sum,
    ContinuousMultilinearMap.neg_apply, ContinuousMultilinearMap.sum_apply]
  congr 1
  exact Finset.sum_congr rfl fun k _ =>
    slotInsertEndoFib_apply_eval (I := I) (M := M) s k x
      (riemannOp (LeviCivita (I := I) g) x u w) A m

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The slot-sum operator is additive in the first curvature direction. -/
lemma slotCurvSumFib_add_left (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (u u' w : TangentSpace I x) :
    slotCurvSumFib (I := I) (M := M) g s x (u + u') w =
      slotCurvSumFib (I := I) (M := M) g s x u w +
        slotCurvSumFib (I := I) (M := M) g s x u' w := by
  have hR : riemannOp (LeviCivita (I := I) g) x (u + u') w =
      riemannOp (LeviCivita (I := I) g) x u w +
        riemannOp (LeviCivita (I := I) g) x u' w := by
    rw [map_add (riemannOp (LeviCivita (I := I) g) x), ContinuousLinearMap.add_apply]
  rw [slotCurvSumFib, slotCurvSumFib, slotCurvSumFib, hR]
  rw [Finset.sum_congr rfl fun k _ =>
    slotInsertEndoFib_add_left (I := I) (M := M) s k x
      (riemannOp (LeviCivita (I := I) g) x u w)
      (riemannOp (LeviCivita (I := I) g) x u' w)]
  rw [Finset.sum_add_distrib, neg_add]

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The slot-sum operator is `ℝ`-homogeneous in the first curvature direction. -/
lemma slotCurvSumFib_smul_left (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) (c : ℝ)
    (u w : TangentSpace I x) :
    slotCurvSumFib (I := I) (M := M) g s x (c • u) w =
      c • slotCurvSumFib (I := I) (M := M) g s x u w := by
  have hR : riemannOp (LeviCivita (I := I) g) x (c • u) w =
      c • riemannOp (LeviCivita (I := I) g) x u w := by
    rw [map_smul (riemannOp (LeviCivita (I := I) g) x), ContinuousLinearMap.smul_apply]
  rw [slotCurvSumFib, slotCurvSumFib, hR]
  rw [Finset.sum_congr rfl fun k _ =>
    slotInsertEndoFib_smul_left (I := I) (M := M) s k x c
      (riemannOp (LeviCivita (I := I) g) x u w)]
  rw [← Finset.smul_sum, ← smul_neg]

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The slot-sum operator is additive in the second curvature direction. -/
lemma slotCurvSumFib_add_right (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (u w w' : TangentSpace I x) :
    slotCurvSumFib (I := I) (M := M) g s x u (w + w') =
      slotCurvSumFib (I := I) (M := M) g s x u w +
        slotCurvSumFib (I := I) (M := M) g s x u w' := by
  have hR : riemannOp (LeviCivita (I := I) g) x u (w + w') =
      riemannOp (LeviCivita (I := I) g) x u w +
        riemannOp (LeviCivita (I := I) g) x u w' :=
    map_add (riemannOp (LeviCivita (I := I) g) x u) w w'
  rw [slotCurvSumFib, slotCurvSumFib, slotCurvSumFib, hR]
  rw [Finset.sum_congr rfl fun k _ =>
    slotInsertEndoFib_add_left (I := I) (M := M) s k x
      (riemannOp (LeviCivita (I := I) g) x u w)
      (riemannOp (LeviCivita (I := I) g) x u w')]
  rw [Finset.sum_add_distrib, neg_add]

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The slot-sum operator is `ℝ`-homogeneous in the second curvature direction. -/
lemma slotCurvSumFib_smul_right (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) (c : ℝ)
    (u w : TangentSpace I x) :
    slotCurvSumFib (I := I) (M := M) g s x u (c • w) =
      c • slotCurvSumFib (I := I) (M := M) g s x u w := by
  have hR : riemannOp (LeviCivita (I := I) g) x u (c • w) =
      c • riemannOp (LeviCivita (I := I) g) x u w :=
    map_smul (riemannOp (LeviCivita (I := I) g) x u) c w
  rw [slotCurvSumFib, slotCurvSumFib, hR]
  rw [Finset.sum_congr rfl fun k _ =>
    slotInsertEndoFib_smul_left (I := I) (M := M) s k x c
      (riemannOp (LeviCivita (I := I) g) x u w)]
  rw [← Finset.smul_sum, ← smul_neg]

/-! ## The two-free-slot curvature operator fibre CLM -/

set_option backward.isDefEq.respectTransparency false in
/-- The inner (second-direction) continuous linear layer: for fixed `A` and `u`, the map
`w ↦ slotCurvSumFib g s x u w A`. -/
def slotFreeCurvWCLM (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (A : Tensor0SSpace s I x) (u : TangentSpace I x) :
    TangentSpace I x →L[ℝ] Tensor0SSpace s I x :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  LinearMap.toContinuousLinearMap
    { toFun := fun w => slotCurvSumFib (I := I) (M := M) g s x u w A
      map_add' := fun w w' => by
        rw [slotCurvSumFib_add_right (I := I) (M := M) g s x u w w',
          ContinuousLinearMap.add_apply]
      map_smul' := fun c w => by
        rw [slotCurvSumFib_smul_right (I := I) (M := M) g s x c u w,
          ContinuousLinearMap.smul_apply]
        rfl }

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The defining formula for `slotFreeCurvWCLM`. -/
@[simp] lemma slotFreeCurvWCLM_apply (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (A : Tensor0SSpace s I x) (u w : TangentSpace I x) :
    slotFreeCurvWCLM (I := I) (M := M) g s x A u w =
      slotCurvSumFib (I := I) (M := M) g s x u w A := by
  rw [slotFreeCurvWCLM, LinearMap.coe_toContinuousLinearMap']
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The middle (first-direction) continuous linear layer: for fixed `A`, the map
`u ↦ (tensor0S_curry s x).symm (slotFreeCurvWCLM g s x A u)`, valued in `(0, s + 1)`-tensors. -/
def slotFreeCurvUCLM (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (A : Tensor0SSpace s I x) :
    TangentSpace I x →L[ℝ] Tensor0SSpace (s + 1) I x :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  LinearMap.toContinuousLinearMap
    { toFun := fun u => (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        (slotFreeCurvWCLM (I := I) (M := M) g s x A u)
      map_add' := fun u u' => by
        have hW : slotFreeCurvWCLM (I := I) (M := M) g s x A (u + u') =
            slotFreeCurvWCLM (I := I) (M := M) g s x A u +
              slotFreeCurvWCLM (I := I) (M := M) g s x A u' := by
          apply ContinuousLinearMap.ext
          intro w
          rw [ContinuousLinearMap.add_apply, slotFreeCurvWCLM_apply, slotFreeCurvWCLM_apply,
            slotFreeCurvWCLM_apply, slotCurvSumFib_add_left (I := I) (M := M) g s x u u' w,
            ContinuousLinearMap.add_apply]
        rw [hW, map_add ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm)]
      map_smul' := fun c u => by
        have hW : slotFreeCurvWCLM (I := I) (M := M) g s x A (c • u) =
            c • slotFreeCurvWCLM (I := I) (M := M) g s x A u := by
          apply ContinuousLinearMap.ext
          intro w
          rw [ContinuousLinearMap.smul_apply, slotFreeCurvWCLM_apply, slotFreeCurvWCLM_apply,
            slotCurvSumFib_smul_left (I := I) (M := M) g s x c u w,
            ContinuousLinearMap.smul_apply]
        rw [hW, map_smul ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm)]
        rfl }

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The defining formula for `slotFreeCurvUCLM`. -/
@[simp] lemma slotFreeCurvUCLM_apply (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (A : Tensor0SSpace s I x) (u : TangentSpace I x) :
    slotFreeCurvUCLM (I := I) (M := M) g s x A u =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        (slotFreeCurvWCLM (I := I) (M := M) g s x A u) := by
  rw [slotFreeCurvUCLM, LinearMap.coe_toContinuousLinearMap']
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **The two-free-slot curvature operator fibre CLM.** The continuous linear map
`T^{(0,s)}_x →L T^{(0,s+2)}_x` sending `A` to the double leading-slot uncurry of the bilinear
slot-sum `(u, w) ↦ slotCurvSumFib g s x u w A`: the `(0, s + 2)`-tensor reading
`(u, w, m) ↦ − ∑ₖ A(m with slot k hit by R_x(u, w))`. -/
def slotFreeCurvOpFib (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) :
    Tensor0SSpace s I x →L[ℝ] Tensor0SSpace (s + 2) I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace s I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun A => (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm
        (slotFreeCurvUCLM (I := I) (M := M) g s x A)
      map_add' := fun A A' => by
        have hU : slotFreeCurvUCLM (I := I) (M := M) g s x (A + A') =
            slotFreeCurvUCLM (I := I) (M := M) g s x A +
              slotFreeCurvUCLM (I := I) (M := M) g s x A' := by
          apply ContinuousLinearMap.ext
          intro u
          have hW : slotFreeCurvWCLM (I := I) (M := M) g s x (A + A') u =
              slotFreeCurvWCLM (I := I) (M := M) g s x A u +
                slotFreeCurvWCLM (I := I) (M := M) g s x A' u := by
            apply ContinuousLinearMap.ext
            intro w
            rw [ContinuousLinearMap.add_apply, slotFreeCurvWCLM_apply, slotFreeCurvWCLM_apply,
              slotFreeCurvWCLM_apply,
              map_add (slotCurvSumFib (I := I) (M := M) g s x u w)]
          rw [ContinuousLinearMap.add_apply, slotFreeCurvUCLM_apply, slotFreeCurvUCLM_apply,
            slotFreeCurvUCLM_apply, hW,
            map_add ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm)]
        rw [hU, map_add ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm)]
      map_smul' := fun c A => by
        have hU : slotFreeCurvUCLM (I := I) (M := M) g s x (c • A) =
            c • slotFreeCurvUCLM (I := I) (M := M) g s x A := by
          apply ContinuousLinearMap.ext
          intro u
          have hW : slotFreeCurvWCLM (I := I) (M := M) g s x (c • A) u =
              c • slotFreeCurvWCLM (I := I) (M := M) g s x A u := by
            apply ContinuousLinearMap.ext
            intro w
            rw [ContinuousLinearMap.smul_apply, slotFreeCurvWCLM_apply, slotFreeCurvWCLM_apply,
              map_smul (slotCurvSumFib (I := I) (M := M) g s x u w)]
          rw [ContinuousLinearMap.smul_apply, slotFreeCurvUCLM_apply, slotFreeCurvUCLM_apply,
            hW, map_smul ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm)]
        rw [hU, map_smul ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm)]
        rfl }

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The defining formula for `slotFreeCurvOpFib`. -/
@[simp] lemma slotFreeCurvOpFib_apply (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (A : Tensor0SSpace s I x) :
    slotFreeCurvOpFib (I := I) (M := M) g s x A =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm
        (slotFreeCurvUCLM (I := I) (M := M) g s x A) := by
  rw [slotFreeCurvOpFib, LinearMap.coe_toContinuousLinearMap']
  rfl

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **The two-free-slot curvature operator reads its two leading slots as the curvature
directions:** on a tuple `Fin.cons u (Fin.cons w m)`, the value is minus the sum over the `s`
trailing slots of `A` evaluated with slot `k` hit by `R_x(u, w)`. -/
lemma slotFreeCurvOpFib_apply_eval (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (A : Tensor0SSpace s I x) (u w : TangentSpace I x) (m : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel (slotFreeCurvOpFib (I := I) (M := M) g s x A)
        (Fin.cons u (Fin.cons w m)) =
      - ∑ k : Fin s, Tensor0SSpace.toModel A
          (Function.update m k (riemannOp (LeviCivita (I := I) g) x u w (m k))) := by
  rw [← tensor0S_curry_apply_eval (I := I) (M := M) (n := s + 1)
    (T := slotFreeCurvOpFib (I := I) (M := M) g s x A) (v0 := u) (vs := Fin.cons w m)]
  have hcurry1 : tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
      (slotFreeCurvOpFib (I := I) (M := M) g s x A) =
      slotFreeCurvUCLM (I := I) (M := M) g s x A := by
    rw [slotFreeCurvOpFib_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [hcurry1, slotFreeCurvUCLM_apply]
  rw [← tensor0S_curry_apply_eval (I := I) (M := M) (n := s)
    (T := (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
      (slotFreeCurvWCLM (I := I) (M := M) g s x A u)) (v0 := w) (vs := m)]
  rw [ContinuousLinearEquiv.apply_symm_apply, slotFreeCurvWCLM_apply]
  exact slotCurvSumFib_apply_eval (I := I) (M := M) g s x u w A m

/-! ## Base-point smoothness of the two-free-slot curvature operator field -/

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **Base-point smoothness of the two-free-slot curvature operator field.** The fibre field
`x ↦ slotFreeCurvOpFib g s x` is a smooth section of the `(s, s + 2)`-tensor (operator) bundle.
By `contMDiff_clm_section_of_pointwise` it suffices that for every smooth `(0, s)`-tensor `Y` the
value section `x ↦ slotFreeCurvOpFib g s x (Y x)` is smooth; that value is the double uncurry
(`contMDiff_uncurriedSection_of_contMDiff_homSection`, twice) of the per-direction slot-sum
`x ↦ slotCurvSumFib g s x (U x) (W x) (Y x)`, which is the negated finite sum of the slot-insertion
fields (`slotInsertEndoFib_contMDiff`) applied to `Y` along the smooth curvature endomorphism field
`x ↦ R_x(U x, W x)` (`riemannOp_section_contMDiff`, two `ContMDiff.clm_bundle_apply`). -/
theorem slotFreeCurvOpFib_contMDiff (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel s (s + 2) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel s (s + 2) ℝ E)
        (E := fun z : M => TensorRSSpace s (s + 2) I z) x
        (TensorRSSpace.ofCLM (slotFreeCurvOpFib (I := I) (M := M) g s x))) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel s ℝ E) (V₁ := fun z : M => Tensor0SSpace s I z)
    (F₂ := Tensor0SModel (s + 2) ℝ E) (V₂ := fun z : M => Tensor0SSpace (s + 2) I z)
    (φ := fun x => slotFreeCurvOpFib (I := I) (M := M) g s x)
  intro Y
  have heq : (fun x : M => TotalSpace.mk' (Tensor0SModel (s + 2) ℝ E)
      (E := fun z : M => Tensor0SSpace (s + 2) I z) x
      (slotFreeCurvOpFib (I := I) (M := M) g s x (Y x))) =
      (fun x : M => TotalSpace.mk' (Tensor0SModel (s + 2) ℝ E)
      (E := fun z : M => Tensor0SSpace (s + 2) I z) x
      ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm
        (slotFreeCurvUCLM (I := I) (M := M) g s x (Y x)))) := by
    funext x
    rw [slotFreeCurvOpFib_apply]
  rw [heq]
  have hU : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel (s + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SSpace (s + 1) I z) x
        (slotFreeCurvUCLM (I := I) (M := M) g s x (Y x))) := by
    apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
      (F₁ := E) (V₁ := fun z : M => TangentSpace I z)
      (F₂ := Tensor0SModel (s + 1) ℝ E) (V₂ := fun z : M => Tensor0SSpace (s + 1) I z)
      (φ := fun x => slotFreeCurvUCLM (I := I) (M := M) g s x (Y x))
    intro U
    have heqU : (fun x : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (s + 1) I z) x
        (slotFreeCurvUCLM (I := I) (M := M) g s x (Y x) (U x))) =
        (fun x : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (s + 1) I z) x
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
          (slotFreeCurvWCLM (I := I) (M := M) g s x (Y x) (U x)))) := by
      funext x
      rw [slotFreeCurvUCLM_apply]
    rw [heqU]
    have hW : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
          (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SSpace s I z) x
          (slotFreeCurvWCLM (I := I) (M := M) g s x (Y x) (U x))) := by
      apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
        (F₁ := E) (V₁ := fun z : M => TangentSpace I z)
        (F₂ := Tensor0SModel s ℝ E) (V₂ := fun z : M => Tensor0SSpace s I z)
        (φ := fun x => slotFreeCurvWCLM (I := I) (M := M) g s x (Y x) (U x))
      intro W
      have hR1 : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E)) ∞
          (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
            (E := fun z : M =>
              TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] TangentSpace I z) x
            (riemannOp (LeviCivita (I := I) g) x (U x))) :=
        ContMDiff.clm_bundle_apply (b := id)
          (riemannOp_section_contMDiff (I := I) (M := M) g) U.contMDiff
      have hR2 : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
          (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
            (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) x
            (riemannOp (LeviCivita (I := I) g) x (U x) (W x))) :=
        ContMDiff.clm_bundle_apply (b := id) hR1 W.contMDiff
      set T : Fin s → Cₛ^∞⟮I; Tensor0SModel s ℝ E, (fun z : M => Tensor0SSpace s I z)⟯ :=
        fun k =>
          { toFun := fun x : M => slotInsertEndoFib (I := I) (M := M) s k x
              (riemannOp (LeviCivita (I := I) g) x (U x) (W x)) (Y x)
            contMDiff_toFun := ContMDiff.clm_bundle_apply (b := id)
              (slotInsertEndoFib_contMDiff (I := I) (M := M) g s k
                (fun x => riemannOp (LeviCivita (I := I) g) x (U x) (W x)) hR2)
              Y.contMDiff } with hT_def
      have hsum := (-(∑ k : Fin s, T k) :
        Cₛ^∞⟮I; Tensor0SModel s ℝ E, (fun z : M => Tensor0SSpace s I z)⟯).contMDiff
      refine hsum.congr ?_
      intro x
      have hcoe : (-(∑ k : Fin s, T k) :
          Cₛ^∞⟮I; Tensor0SModel s ℝ E, (fun z : M => Tensor0SSpace s I z)⟯) x =
          -(∑ k : Fin s, T k x) := by
        have hs : ((∑ k : Fin s, T k :
            Cₛ^∞⟮I; Tensor0SModel s ℝ E, (fun z : M => Tensor0SSpace s I z)⟯) :
              Π z : M, Tensor0SSpace s I z) = ∑ k : Fin s, ⇑(T k) :=
          map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel s ℝ E) ∞
            (fun z : M => Tensor0SSpace s I z)) T Finset.univ
        rw [ContMDiffSection.coe_neg, Pi.neg_apply, hs, Finset.sum_apply]
      rw [hcoe]
      have hval : slotFreeCurvWCLM (I := I) (M := M) g s x (Y x) (U x) (W x) =
          -(∑ k : Fin s, T k x) := by
        rw [slotFreeCurvWCLM_apply, slotCurvSumFib, ContinuousLinearMap.neg_apply,
          ContinuousLinearMap.sum_apply]
        rfl
      rw [hval]
    exact contMDiff_uncurriedSection_of_contMDiff_homSection (I := I) (M := M)
      (fun x : M => slotFreeCurvWCLM (I := I) (M := M) g s x (Y x) (U x)) hW
  exact contMDiff_uncurriedSection_of_contMDiff_homSection (I := I) (M := M)
    (fun x : M => slotFreeCurvUCLM (I := I) (M := M) g s x (Y x)) hU

/-! ## The two-free-slot curvature operator Hom-field -/

set_option backward.isDefEq.respectTransparency false in
/-- **The two-free-slot curvature operator Hom-fibre.** The fibre value of the Hom-field `Θ s` at
`x`: post-composition of an `(0, s)`-tensor (read as the map `T^{(0,0)} →L T^{(0,s)}`) by the
two-free-slot curvature operator fibre CLM `slotFreeCurvOpFib g s x`. -/
def slotFreeCurvHomFib (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) :
    TensorRSSpace 0 s I x →L[ℝ] TensorRSSpace 0 (s + 2) I x :=
  haveI : FiniteDimensional ℝ (TensorRSSpace 0 s I x) :=
    inferInstanceAs (FiniteDimensional ℝ (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x))
  haveI : T2Space (TensorRSSpace 0 s I x) :=
    inferInstanceAs (T2Space (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x))
  LinearMap.toContinuousLinearMap
    { toFun := fun T => (slotFreeCurvOpFib (I := I) (M := M) g s x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T)
      map_add' := fun T T' => by
        rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T + T') =
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T) +
              (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T') from rfl,
          ContinuousLinearMap.comp_add]
      map_smul' := fun c T => by
        rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from c • T) =
            c • (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T) from rfl,
          ContinuousLinearMap.comp_smul]
        rfl }

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The defining formula for `slotFreeCurvHomFib`. -/
@[simp] lemma slotFreeCurvHomFib_apply (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (T : TensorRSSpace 0 s I x) :
    slotFreeCurvHomFib (I := I) (M := M) g s x T =
      (slotFreeCurvOpFib (I := I) (M := M) g s x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T) := by
  haveI : FiniteDimensional ℝ (TensorRSSpace 0 s I x) :=
    inferInstanceAs (FiniteDimensional ℝ (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x))
  haveI : T2Space (TensorRSSpace 0 s I x) :=
    inferInstanceAs (T2Space (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x))
  rw [slotFreeCurvHomFib, LinearMap.coe_toContinuousLinearMap']
  rfl

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **Base-point smoothness of the two-free-slot curvature operator Hom-fibre field.** Reduced by
the pointwise criterion (twice) to the evaluation
`x ↦ slotFreeCurvOpFib g s x ((Z x) (ζ x))`, two `ContMDiff.clm_bundle_apply` over the smooth
operator field `slotFreeCurvOpFib_contMDiff`. -/
theorem slotFreeCurvHomFib_contMDiff (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E →L[ℝ] TensorRSModel 0 (s + 2) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E →L[ℝ] TensorRSModel 0 (s + 2) ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z →L[ℝ] TensorRSSpace 0 (s + 2) I z) x
        (slotFreeCurvHomFib (I := I) (M := M) g s x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := TensorRSModel 0 s ℝ E) (V₁ := fun z : M => TensorRSSpace 0 s I z)
    (F₂ := TensorRSModel 0 (s + 2) ℝ E) (V₂ := fun z : M => TensorRSSpace 0 (s + 2) I z)
    (φ := fun x => slotFreeCurvHomFib (I := I) (M := M) g s x)
  intro Z
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 0 ℝ E) (V₁ := fun z : M => Tensor0SSpace 0 I z)
    (F₂ := Tensor0SModel (s + 2) ℝ E) (V₂ := fun z : M => Tensor0SSpace (s + 2) I z)
    (φ := fun x => (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from
      slotFreeCurvHomFib (I := I) (M := M) g s x (Z x)))
  intro ζ
  have hZζ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from Z x) (ζ x))) :=
    ContMDiff.clm_bundle_apply (b := id) Z.contMDiff ζ.contMDiff
  have happ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 2) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel (s + 2) ℝ E)
        (E := fun z : M => Tensor0SSpace (s + 2) I z) x
        (slotFreeCurvOpFib (I := I) (M := M) g s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from Z x) (ζ x)))) :=
    ContMDiff.clm_bundle_apply (b := id)
      (slotFreeCurvOpFib_contMDiff (I := I) (M := M) g s) hZζ
  refine happ.congr ?_
  intro x
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from
      slotFreeCurvHomFib (I := I) (M := M) g s x (Z x)) (ζ x) =
    slotFreeCurvOpFib (I := I) (M := M) g s x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from Z x) (ζ x)) from by
    rw [slotFreeCurvHomFib_apply, ContinuousLinearMap.comp_apply]]

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **The two-free-slot curvature operator Hom-field `Θ s`**, as a smooth section of the
second-order Hom-bundle `Hom(T^{(0,s)}, T^{(0,s+2)})`.  Its fibre value at `x` is post-composition
by the two-free-slot curvature operator fibre CLM `slotFreeCurvOpFib g s x`. -/
def slotFreeCurvHomField (g : SmoothRiemannianMetric I M) (s : ℕ) :
    HomTensorRSField (E := E) (M := M) 0 s (s + 2) I where
  toFun := fun x : M => slotFreeCurvHomFib (I := I) (M := M) g s x
  contMDiff_toFun := slotFreeCurvHomFib_contMDiff (I := I) (M := M) g s

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The fibre value of `slotFreeCurvHomField g s` at `x` is `slotFreeCurvHomFib g s x`.
Definitional. -/
@[simp] lemma slotFreeCurvHomField_apply (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) :
    (show TensorRSSpace 0 s I x →L[ℝ] TensorRSSpace 0 (s + 2) I x from
        slotFreeCurvHomField (I := I) (M := M) g s x) =
      slotFreeCurvHomFib (I := I) (M := M) g s x := rfl

/-! ## The existence form consumed by the bracket-channel fibre-order line -/

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **The two-free-slot curvature operator Hom-field and its base-slot evaluation.** There is a
family of fixed smooth Hom-bundle fields `Θ s : Hom(T^{(0,s)}, T^{(0,s+2)})` whose full Hom-bundle
action on a smooth compactly-supported `(0, s)`-tensor `S` evaluates, in the two leading free slots
`(u, w)`, to *minus* the slot-wise curvature sum:

```
(appFullSec (Θ s) S)(x)(unit)(u, w, m) = − ∑ₖ S(x)(unit)(m with slot k hit by R_x(u, w)),
```

with `R = riemannOp (LeviCivita g)` the bundled Levi-Civita curvature operator.  The witness is
`slotFreeCurvHomField`: frame-free (built from the smooth curvature operator field alone) and
smooth, so the operator-field covariant calculus and the uniform fibre contraction envelope apply
to it `S`- and `x`-uniformly. -/
theorem exists_slotFreeCurvOpField_baseSlot_eval (g : SmoothRiemannianMetric I M) :
    ∃ Θ : ∀ s : ℕ, HomTensorRSField (E := E) (M := M) 0 s (s + 2) I,
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) (u w : TangentSpace I x)
        (m : Fin s → TangentSpace I x),
        Tensor0SSpace.toModel ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from
            (appFullSec (I := I) (M := M) g 0 s (s + 2) (Θ s) S).toSection x)
            (unitZeroSec (I := I) (M := M) x))
          (Fin.cons u (Fin.cons w m)) =
        - ∑ k : Fin s, Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
              S.toSection x) (unitZeroSec (I := I) (M := M) x))
          (Function.update m k (riemannOp (LeviCivita (I := I) g) x u w (m k))) := by
  refine ⟨fun s => slotFreeCurvHomField (I := I) (M := M) g s, fun s S x u w m => ?_⟩
  have hval : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from
      (appFullSec (I := I) (M := M) g 0 s (s + 2)
        (slotFreeCurvHomField (I := I) (M := M) g s) S).toSection x)
      (unitZeroSec (I := I) (M := M) x) =
      slotFreeCurvOpFib (I := I) (M := M) g s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
          (unitZeroSec (I := I) (M := M) x)) := by
    rw [show (appFullSec (I := I) (M := M) g 0 s (s + 2)
        (slotFreeCurvHomField (I := I) (M := M) g s) S).toSection x =
      (show TensorRSSpace 0 s I x →L[ℝ] TensorRSSpace 0 (s + 2) I x from
        slotFreeCurvHomField (I := I) (M := M) g s x) (S.toSection x) from
      appFullSec_toSection (I := I) (M := M) g 0 s (s + 2)
        (slotFreeCurvHomField (I := I) (M := M) g s) S x]
    rw [slotFreeCurvHomField_apply, slotFreeCurvHomFib_apply]
    rfl
  rw [hval, slotFreeCurvOpFib_apply_eval (I := I) (M := M) g s x _ u w m]

end Connection
end Integral
end DifferentialGeometry

end
