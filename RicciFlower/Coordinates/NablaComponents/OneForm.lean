import RicciFlower.Coordinates.NablaComponents.Basic
import RicciFlower.VectorBundle.PartialMfderiv

/-!
# Coordinate one-form covariant derivative components

This file contains the `(0,1)` coordinate-frame component formulas and the
moving-slot product-rule bridges for `nabla0SFun 1`.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RicciFlower
namespace Coordinates

open Bundle Set Tensor0SBundle TensorLieDeriv
open scoped BigOperators Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [Module.Finite 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]
variable [IsManifold I (∞ : WithTop ℕ∞) M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-- Coordinate-frame component formula for the covariant derivative of a one-form,
with the derivative term kept in the chart-model form used by `nabla0SFun`. -/
theorem nabla0S_one_model_coord
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (x₀ : M) (j : CoordinateIdx (𝕜 := 𝕜) E) :
    coordComponent0SAt (I := I)
        (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          1 cov X α x₀)
        (fun _ : Fin 1 => j) =
      modelDeriv0SAt (I := I) X x₀ (fun x => α x) (fun _ : Fin 1 => j) -
        ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
          christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            x₀ (X x₀) j k *
            coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => k) := by
  have h := nabla0S_model_coordFrame_slots
    (I := I) cov X α x₀ (fun _ : Fin 1 => j)
  have hupdate (k : CoordinateIdx (𝕜 := 𝕜) E) :
      Function.update (fun _ : Fin 1 => j) 0 k = fun _ : Fin 1 => k := by
    funext q
    fin_cases q
    simp
  simpa only [Fin.sum_univ_one, hupdate] using h

/-- Coordinate-frame component formula for one-forms, after supplying the
derivative-identification bridge. -/
theorem nabla0S_one_coord
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (x₀ : M) (hderiv : ModelDerivEqCoordDeriv0SAt (I := I) X x₀ (fun x => α x))
    (j : CoordinateIdx (𝕜 := 𝕜) E) :
    coordComponent0SAt (I := I)
        (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          1 cov X α x₀)
        (fun _ : Fin 1 => j) =
      coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => α x) (fun _ : Fin 1 => j) -
        ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
          christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            x₀ (X x₀) j k *
            coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => k) := by
  have h := nabla0S_coordFrame_slots
    (I := I) cov X α x₀ hderiv (fun _ : Fin 1 => j)
  have hupdate (k : CoordinateIdx (𝕜 := 𝕜) E) :
      Function.update (fun _ : Fin 1 => j) 0 k = fun _ : Fin 1 => k := by
    funext q
    fin_cases q
    simp
  simpa only [Fin.sum_univ_one, hupdate] using h

/-- Evaluation form of `nabla0S_one_coord` on a coordinate-frame basis vector.

This is the coordinate-frame bridge from the canonical raw derivative
`nabla0SFun` to the usual one-form Christoffel component formula.  It is not the
intrinsic moving-vector-field identity
`(∇_X α)(Z) = X(α Z) - α(∇_X Z)`; that identity additionally needs a product
rule for differentiating the scalar pairing `p ↦ α p (Z p)`. -/
theorem nabla0SFun_one_eval_coordFrame
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (x₀ : M) (hderiv : ModelDerivEqCoordDeriv0SAt (I := I) X x₀ (fun x => α x))
    (j : CoordinateIdx (𝕜 := 𝕜) E) :
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      1 cov X α x₀)
        (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j x₀) =
      coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => α x) (fun _ : Fin 1 => j) -
        ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
          christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            x₀ (X x₀) j k *
            coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => k) := by
  simpa [coordComponent0SAt, component0S] using
    nabla0S_one_coord (I := I) cov X α x₀ hderiv j

/-- Evaluate a one-form on an arbitrary tangent vector by expanding the vector
in the coordinate-frame basis at the base point. -/
theorem tensor0S_one_eval_coordFrame_sum
    {x₀ : M}
    (αx : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) 1 x₀)
    (Z : TangentSpace I x₀) :
    αx (fun _ : Fin 1 => Z) =
      ∑ j : CoordinateIdx (𝕜 := 𝕜) E,
        (coordinateFrameAt_toBasis (I := I) x₀).coord j Z *
          αx (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j x₀) := by
  classical
  let b := coordinateFrameAt_toBasis (I := I) x₀
  have hupdate (w : TangentSpace I x₀) :
      Function.update (fun _ : Fin 1 => Z) (0 : Fin 1) w =
        fun _ : Fin 1 => w := by
    funext q
    fin_cases q
    simp
  have hmap := αx.toMultilinearMap.map_update_sum
    (Finset.univ : Finset (CoordinateIdx (𝕜 := 𝕜) E)) (0 : Fin 1)
    (fun j : CoordinateIdx (𝕜 := 𝕜) E => b.coord j Z • b j) (fun _ : Fin 1 => Z)
  calc
    αx (fun _ : Fin 1 => Z)
        = αx (Function.update (fun _ : Fin 1 => Z) (0 : Fin 1)
            (∑ j : CoordinateIdx (𝕜 := 𝕜) E, b.coord j Z • b j)) := by
          rw [hupdate]
          congr 1
          funext q
          exact (b.sum_repr Z).symm
    _ = ∑ j : CoordinateIdx (𝕜 := 𝕜) E,
          αx (Function.update (fun _ : Fin 1 => Z) (0 : Fin 1)
            (b.coord j Z • b j)) := by
          simpa using hmap
    _ = ∑ j : CoordinateIdx (𝕜 := 𝕜) E,
          b.coord j Z * αx (fun _ : Fin 1 => b j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hupdate]
          have hconst :
              (fun _ : Fin 1 => b.coord j Z • b j) =
                Function.update (fun _ : Fin 1 => b j) (0 : Fin 1)
                  (b.coord j Z • b j) := by
            funext q
            fin_cases q
            simp
          rw [hconst]
          rw [αx.map_update_smul]
          simp [smul_eq_mul]
    _ = ∑ j : CoordinateIdx (𝕜 := 𝕜) E,
          (coordinateFrameAt_toBasis (I := I) x₀).coord j Z *
            αx (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j x₀) := by
          simp [b]


private theorem tensor0S_one_eval_finset_sum
    {ι : Type*} {x : M}
    (αx : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) 1 x)
    (t : Finset ι) (V : ι -> TangentSpace I x) :
    αx (fun _ : Fin 1 => t.sum V) =
      t.sum (fun i => αx (fun _ : Fin 1 => V i)) := by
  classical
  have hupdate (w : TangentSpace I x) :
      Function.update (fun _ : Fin 1 => t.sum V) (0 : Fin 1) w =
        fun _ : Fin 1 => w := by
    funext q
    fin_cases q
    simp
  have hmap := αx.toMultilinearMap.map_update_sum
    t (0 : Fin 1) V (fun _ : Fin 1 => t.sum V)
  calc
    αx (fun _ : Fin 1 => t.sum V)
        = αx (Function.update (fun _ : Fin 1 => t.sum V) (0 : Fin 1)
            (t.sum V)) := by
          rw [hupdate]
    _ = t.sum (fun i =>
          αx (Function.update (fun _ : Fin 1 => t.sum V) (0 : Fin 1)
            (V i))) := by
          simpa using hmap
    _ = t.sum (fun i => αx (fun _ : Fin 1 => V i)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hupdate]

private theorem mdifferentiableAt_finset_sum
    {ι : Type*} (t : Finset ι) (f : ι -> M -> 𝕜) {x : M}
    (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(𝕜, 𝕜) (f i) x) :
    MDifferentiableAt I 𝓘(𝕜, 𝕜) (t.sum f) x := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simpa using (mdifferentiableAt_const
        (I := I) (I' := 𝓘(𝕜, 𝕜)) (c := (0 : 𝕜)) (x := x))
  | insert i t hit ih =>
      have hfi : MDifferentiableAt I 𝓘(𝕜, 𝕜) (f i) x := hf i (by simp [hit])
      have hft : ∀ j ∈ t, MDifferentiableAt I 𝓘(𝕜, 𝕜) (f j) x := by
        intro j hj
        exact hf j (by simp [hj])
      have hsum : MDifferentiableAt I 𝓘(𝕜, 𝕜) (t.sum f) x := ih hft
      have hadd : MDifferentiableAt I 𝓘(𝕜, 𝕜) (f i + t.sum f) x := hfi.add hsum
      simpa [Finset.sum_insert, hit] using hadd

private theorem extDerivFun_finset_sum
    {ι : Type*} (t : Finset ι) (f : ι -> M -> 𝕜)
    {x : M} (v : TangentSpace I x)
    (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(𝕜, 𝕜) (f i) x) :
    extDerivFun (I := I) (t.sum f) x v =
      t.sum (fun i => extDerivFun (I := I) (f i) x v) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp
  | insert i t hit ih =>
      have hfi : MDifferentiableAt I 𝓘(𝕜, 𝕜) (f i) x := hf i (by simp [hit])
      have hft : ∀ j ∈ t, MDifferentiableAt I 𝓘(𝕜, 𝕜) (f j) x := by
        intro j hj
        exact hf j (by simp [hj])
      have hsum : MDifferentiableAt I 𝓘(𝕜, 𝕜) (t.sum f) x := by
        exact mdifferentiableAt_finset_sum (I := I) t f hft
      calc
        extDerivFun (I := I) ((insert i t).sum f) x v
            = extDerivFun (I := I)
                (f i + t.sum f) x v := by
              simp [Finset.sum_insert, hit]
        _ = extDerivFun (I := I) (f i) x v +
              extDerivFun (I := I) (t.sum f) x v := by
              have hadd := congr($(extDerivFun_add
                (I := I) (g := f i) (g' := t.sum f)
                (x := x) hfi hsum) v)
              simpa [Pi.add_apply] using hadd
        _ = (insert i t).sum (fun j => extDerivFun (I := I) (f j) x v) := by
              rw [ih hft]
              simp [Finset.sum_insert, hit]

private theorem extDerivFun_mul
    {f g : M -> 𝕜} {x : M} (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(𝕜, 𝕜) f x)
    (hg : MDifferentiableAt I 𝓘(𝕜, 𝕜) g x) :
    extDerivFun (I := I) (fun y : M => f y * g y) x v =
      f x * extDerivFun (I := I) g x v +
        extDerivFun (I := I) f x v * g x := by
  change extDerivFun (I := I) (f • g) x v =
      f x * extDerivFun (I := I) g x v +
        extDerivFun (I := I) f x v * g x
  have hprod := fromTangentSpace_mfderiv_smul_apply
    (I := I) (f := f) (g := g) hf hg v
  simpa [extDerivFun, Pi.smul_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    using hprod

private theorem covariantDerivative_finset_sum
    {ι : Type*} (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (t : Finset ι) (σ : ι -> (x : M) -> TangentSpace I x)
    {x : M} (v : TangentSpace I x)
    (hσ : ∀ i, MDiffAt (T% (σ i)) x) :
    (cov (t.sum σ) x) v = t.sum (fun i => (cov (σ i) x) v) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp [cov.isCovariantDerivativeOnUniv.zero]
  | insert i t hit ih =>
      have hσi : MDiffAt (T% (σ i)) x := hσ i
      have hsum : MDiffAt (T% (t.sum σ)) x := by
        have hsum_raw := MDifferentiableAt.sum_section (s := t) (t := σ) hσ
        simpa using hsum_raw
      calc
        (cov ((insert i t).sum σ) x) v
            = (cov (σ i + t.sum σ) x) v := by
              simp [Finset.sum_insert, hit]
        _ = ((cov (σ i) x + cov (t.sum σ) x) v) := by
              rw [cov.isCovariantDerivativeOnUniv.add hσi hsum]
        _ = (cov (σ i) x) v + (cov (t.sum σ) x) v := by
              simp
        _ = (insert i t).sum (fun j => (cov (σ j) x) v) := by
              rw [ih]
              simp [Finset.sum_insert, hit]

private theorem coordinateFrame_coeff_at_base_eq_coord
    (x₀ : M) (Z : TangentSpace I x₀) (j : CoordinateIdx (𝕜 := 𝕜) E) :
    (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j x₀ Z =
      (coordinateFrameAt_toBasis (I := I) x₀).coord j Z := by
  have hbasis :
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀).toBasisAt
          (coordinateFrameAt_mem (I := I) x₀) =
        coordinateFrameAt_toBasis (I := I) x₀ := by
    ext k
    rw [IsLocalFrameOn.toBasisAt_coe]
    rw [coordinateFrameAt_toBasis_apply]
  unfold IsLocalFrameOn.coeff
  rw [dif_pos (coordinateFrameAt_mem (I := I) x₀)]
  rw [hbasis]

private theorem extDerivFun_congr_eventually
    {f g : M -> 𝕜} {x : M} (v : TangentSpace I x)
    (h : f =ᶠ[𝓝 x] g) :
    extDerivFun (I := I) f x v = extDerivFun (I := I) g x v := by
  have hmf := Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(𝕜, 𝕜)) h
  have hx : f x = g x := h.eq_of_nhds
  unfold extDerivFun
  rw [hmf, hx]

theorem oneForm_pair_coordFrame_eventually
    (Z : (x : M) -> TangentSpace I x)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (x₀ : M) :
    (fun y : M => α y (fun _ : Fin 1 => Z y)) =ᶠ[𝓝 x₀]
      (fun y : M =>
        ∑ j : CoordinateIdx (𝕜 := 𝕜) E,
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y) *
            α y (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j y)) := by
  classical
  filter_upwards
    [(coordinateFrameSet_open (I := I) x₀).mem_nhds
      (coordinateFrameAt_mem (I := I) x₀)] with y hy
  let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x₀
  have hZ :
      Z y = ∑ j : CoordinateIdx (𝕜 := 𝕜) E,
        hframe.coeff j y (Z y) • coordinateFrameAt (I := I) x₀ j y := by
    exact hframe.coeff_sum_eq (fun y => Z y) hy
  have hupdate (w : TangentSpace I y) :
      Function.update (fun _ : Fin 1 => Z y) (0 : Fin 1) w =
        fun _ : Fin 1 => w := by
    funext q
    fin_cases q
    simp
  have hmap := (α y).toMultilinearMap.map_update_sum
    (Finset.univ : Finset (CoordinateIdx (𝕜 := 𝕜) E)) (0 : Fin 1)
    (fun j : CoordinateIdx (𝕜 := 𝕜) E =>
      hframe.coeff j y (Z y) • coordinateFrameAt (I := I) x₀ j y)
    (fun _ : Fin 1 => Z y)
  calc
    α y (fun _ : Fin 1 => Z y)
        = α y (Function.update (fun _ : Fin 1 => Z y) (0 : Fin 1)
            (∑ j : CoordinateIdx (𝕜 := 𝕜) E,
              hframe.coeff j y (Z y) • coordinateFrameAt (I := I) x₀ j y)) := by
          congr 1
          funext q
          fin_cases q
          exact hZ
    _ = ∑ j : CoordinateIdx (𝕜 := 𝕜) E,
          α y (Function.update (fun _ : Fin 1 => Z y) (0 : Fin 1)
            (hframe.coeff j y (Z y) • coordinateFrameAt (I := I) x₀ j y)) := by
          simpa using hmap
    _ = ∑ j : CoordinateIdx (𝕜 := 𝕜) E,
          hframe.coeff j y (Z y) *
            α y (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j y) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hupdate]
          have hconst :
              (fun _ : Fin 1 =>
                  hframe.coeff j y (Z y) • coordinateFrameAt (I := I) x₀ j y) =
                Function.update
                  (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j y)
                  (0 : Fin 1)
                  (hframe.coeff j y (Z y) • coordinateFrameAt (I := I) x₀ j y) := by
            funext q
            fin_cases q
            simp
          rw [hconst]
          rw [(α y).map_update_smul]
          simp [smul_eq_mul]

/-- Product rule for the scalar pairing `p ↦ α_p (Z_p)` in the coordinate
frame.  This is the previously external `hpair` input for the moving-slot
one-form formula.  The remaining hypotheses only say that the coordinate
coefficient functions and fixed-slot tensor components are differentiable at
the base point, and identify `dz` with the directional derivatives of the
coefficients of `Z`. -/
theorem oneForm_pair_coordFrame_product_rule
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Z : (x : M) -> TangentSpace I x)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (x₀ : M) (z dz : CoordinateIdx (𝕜 := 𝕜) E -> 𝕜)
    (hz : ∀ j : CoordinateIdx (𝕜 := 𝕜) E,
      z j = (coordinateFrameAt_toBasis (I := I) x₀).coord j (Z x₀))
    (hdz : ∀ j : CoordinateIdx (𝕜 := 𝕜) E,
      dz j =
        extDerivFun (I := I)
          (fun y : M =>
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y))
          x₀ (X x₀))
    (hdiff_z : ∀ j : CoordinateIdx (𝕜 := 𝕜) E,
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun y : M =>
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y)) x₀)
    (hdiff_α : ∀ j : CoordinateIdx (𝕜 := 𝕜) E,
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun y : M => α y (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j y)) x₀) :
    extDerivFun (I := I) (fun y : M => α y (fun _ : Fin 1 => Z y)) x₀ (X x₀) =
      ∑ j : CoordinateIdx (𝕜 := 𝕜) E,
        (dz j * coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => j) +
          z j *
            coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => α x)
              (fun _ : Fin 1 => j)) := by
  classical
  let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x₀
  let zfun : CoordinateIdx (𝕜 := 𝕜) E -> M -> 𝕜 :=
    fun j y => hframe.coeff j y (Z y)
  let afun : CoordinateIdx (𝕜 := 𝕜) E -> M -> 𝕜 :=
    fun j y => α y (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j y)
  have hpair_ev := oneForm_pair_coordFrame_eventually (I := I) Z α x₀
  have hderiv_congr :
      extDerivFun (I := I) (fun y : M => α y (fun _ : Fin 1 => Z y)) x₀ (X x₀) =
        extDerivFun (I := I)
          (fun y : M => ∑ j : CoordinateIdx (𝕜 := 𝕜) E, zfun j y * afun j y) x₀ (X x₀) := by
    exact extDerivFun_congr_eventually (I := I) (X x₀) (by
      simpa [zfun, afun] using hpair_ev)
  rw [hderiv_congr]
  have hsum_fun :
      (fun y : M => ∑ j : CoordinateIdx (𝕜 := 𝕜) E, zfun j y * afun j y) =
        Finset.univ.sum (fun j : CoordinateIdx (𝕜 := 𝕜) E =>
          fun y : M => zfun j y * afun j y) := by
    funext y
    simp
  rw [hsum_fun]
  rw [extDerivFun_finset_sum (I := I) (t := Finset.univ)
    (f := fun j y => zfun j y * afun j y) (x := x₀) (v := X x₀)]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [extDerivFun_mul (I := I) (f := zfun j) (g := afun j) (x := x₀)
      (v := X x₀) (hdiff_z j) (hdiff_α j)]
    have hzj : zfun j x₀ = z j := by
      rw [hz j]
      exact coordinateFrame_coeff_at_base_eq_coord (I := I) x₀ (Z x₀) j
    have hdzj : extDerivFun (I := I) (zfun j) x₀ (X x₀) = dz j := by
      exact (hdz j).symm
    have haj :
        afun j x₀ = coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => j) := by
      simp [afun, coordComponent0SAt, component0S]
    have hdaj :
        extDerivFun (I := I) (afun j) x₀ (X x₀) =
          coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => α x)
            (fun _ : Fin 1 => j) := by
      change (mfderiv I 𝓘(𝕜, 𝕜) (afun j) x₀) (X x₀) =
          coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => α x)
            (fun _ : Fin 1 => j)
      simp [afun, coordDeriv0SAt]
    rw [hzj, hdzj, haj, hdaj]
    ring
  · intro j _
    exact (hdiff_z j).mul (hdiff_α j)

/-- Coordinate expansion of `α(∇_X Z)` in the coordinate frame.  This is the
connection-side product rule matching `oneForm_pair_coordFrame_product_rule`.
-/
theorem oneForm_covariantDerivative_coordFrame_product_rule
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Z : (x : M) -> TangentSpace I x)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (x₀ : M) (z dz : CoordinateIdx (𝕜 := 𝕜) E -> 𝕜)
    (hz : ∀ j : CoordinateIdx (𝕜 := 𝕜) E,
      z j = (coordinateFrameAt_toBasis (I := I) x₀).coord j (Z x₀))
    (hdz : ∀ j : CoordinateIdx (𝕜 := 𝕜) E,
      dz j =
        extDerivFun (I := I)
          (fun y : M =>
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y))
          x₀ (X x₀))
    (hdiff_z : ∀ j : CoordinateIdx (𝕜 := 𝕜) E,
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun y : M =>
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y)) x₀)
    (hZ_diff : MDiffAt (T% Z) x₀) :
    α x₀ (fun _ : Fin 1 => (cov (fun y : M => Z y) x₀) (X x₀)) =
      ∑ j : CoordinateIdx (𝕜 := 𝕜) E,
        (dz j * coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => j) +
          z j *
            (∑ k : CoordinateIdx (𝕜 := 𝕜) E,
              christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
                (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
                x₀ (X x₀) j k *
                coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => k))) := by
  classical
  let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x₀
  let frame := coordinateFrameAt (I := I) x₀
  let zfun : CoordinateIdx (𝕜 := 𝕜) E -> M -> 𝕜 :=
    fun j y => hframe.coeff j y (Z y)
  let term : CoordinateIdx (𝕜 := 𝕜) E -> (x : M) -> TangentSpace I x :=
    fun j => zfun j • frame j
  have hframe_diff (j : CoordinateIdx (𝕜 := 𝕜) E) : MDiffAt (T% (frame j)) x₀ :=
    (hframe.contMDiffAt (coordinateFrameSet_open (I := I) x₀)
      (coordinateFrameAt_mem (I := I) x₀) j).mdifferentiableAt one_ne_zero
  have hterm_diff : ∀ j ∈ (Finset.univ : Finset (CoordinateIdx (𝕜 := 𝕜) E)),
      MDiffAt (T% (term j)) x₀ := by
    intro j _
    exact (hdiff_z j).smul_section (hframe_diff j)
  have hsum_diff :
      MDiffAt (T% ((Finset.univ : Finset (CoordinateIdx (𝕜 := 𝕜) E)).sum term)) x₀ := by
    classical
    exact (by
      have hterm_all : ∀ j : CoordinateIdx (𝕜 := 𝕜) E, MDiffAt (T% (term j)) x₀ := by
        intro j
        exact hterm_diff j (by simp)
      simpa using MDifferentiableAt.sum_section
        (s := (Finset.univ : Finset (CoordinateIdx (𝕜 := 𝕜) E))) (t := term) hterm_all)
  have hZ_ev : (fun y : M => Z y) =ᶠ[𝓝 x₀]
      (fun y : M => ∑ j : CoordinateIdx (𝕜 := 𝕜) E, term j y) := by
    exact hframe.eventually_eq_sum_coeff_smul (fun y => Z y)
      ((coordinateFrameSet_open (I := I) x₀).mem_nhds
        (coordinateFrameAt_mem (I := I) x₀))
  have hcov_congr :
      cov (fun y : M => Z y) x₀ =
        cov ((Finset.univ : Finset (CoordinateIdx (𝕜 := 𝕜) E)).sum term) x₀ :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hZ_diff hsum_diff
      (by simp)
      (by simpa [term] using hZ_ev)
  have hcov_sum :
      (cov (fun y : M => Z y) x₀) (X x₀) =
        ∑ j : CoordinateIdx (𝕜 := 𝕜) E,
          (dz j • frame j x₀ + z j • (cov (frame j) x₀) (X x₀)) := by
    calc
      (cov (fun y : M => Z y) x₀) (X x₀)
          = (cov ((Finset.univ : Finset (CoordinateIdx (𝕜 := 𝕜) E)).sum term) x₀) (X x₀) := by
            rw [hcov_congr]
      _ = ∑ j : CoordinateIdx (𝕜 := 𝕜) E, (cov (term j) x₀) (X x₀) := by
            rw [covariantDerivative_finset_sum (I := I) cov
              (Finset.univ : Finset (CoordinateIdx (𝕜 := 𝕜) E)) term (X x₀) (by
                intro j
                exact hterm_diff j (by simp))]
      _ = ∑ j : CoordinateIdx (𝕜 := 𝕜) E,
            (dz j • frame j x₀ + z j • (cov (frame j) x₀) (X x₀)) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            have hleib := congr($(cov.isCovariantDerivativeOnUniv.leibniz
              (σ := frame j) (g := zfun j) (x := x₀)
              (hframe_diff j) (hdiff_z j)) (X x₀))
            have hzj : zfun j x₀ = z j := by
              rw [hz j]
              exact coordinateFrame_coeff_at_base_eq_coord (I := I) x₀ (Z x₀) j
            have hdzj : extDerivFun (I := I) (zfun j) x₀ (X x₀) = dz j := by
              exact (hdz j).symm
            simpa [term, zfun, hzj, hdzj, add_comm] using hleib
  rw [hcov_sum]
  rw [tensor0S_one_eval_finset_sum (I := I)]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hcov_frame :
      (cov (frame j) x₀) (X x₀) =
        ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
          christoffelAlongInFrame cov frame hframe x₀ (X x₀) j k • frame k x₀ := by
    exact hframe.coeff_sum_eq
      (fun y => (cov (frame j) y) (X y))
      (coordinateFrameAt_mem (I := I) x₀)
  have h_eval_cov :
      α x₀ (fun _ : Fin 1 => (cov (frame j) x₀) (X x₀)) =
        ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
          christoffelAlongInFrame cov frame hframe x₀ (X x₀) j k *
            coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => k) := by
    rw [hcov_frame]
    rw [tensor0S_one_eval_finset_sum (I := I)]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hupdate :
        (fun _ : Fin 1 =>
            christoffelAlongInFrame cov frame hframe x₀ (X x₀) j k • frame k x₀) =
          Function.update (fun _ : Fin 1 => frame k x₀) (0 : Fin 1)
            (christoffelAlongInFrame cov frame hframe x₀ (X x₀) j k • frame k x₀) := by
      funext q
      fin_cases q
      simp
    rw [hupdate, (α x₀).map_update_smul]
    have hframe_eval :
        α x₀ (fun _ : Fin 1 => frame k x₀) =
          coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => k) := by
      simp [frame, coordComponent0SAt, component0S]
    have hupdate0 :
        Function.update (fun _ : Fin 1 => frame k x₀) (0 : Fin 1) (frame k x₀) =
          fun _ : Fin 1 => frame k x₀ := by
      funext q
      fin_cases q
      simp
    rw [hupdate0, hframe_eval]
    simp [smul_eq_mul]
  have h_eval_frame :
      α x₀ (fun _ : Fin 1 => frame j x₀) =
        coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => j) := by
    simp [frame, coordComponent0SAt, component0S]
  change α x₀ (fun _ : Fin 1 => dz j • frame j x₀ + z j • (cov (frame j) x₀) (X x₀)) =
      dz j * coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => j) +
        z j *
          (∑ k : CoordinateIdx (𝕜 := 𝕜) E,
            christoffelAlongInFrame cov frame hframe x₀ (X x₀) j k *
              coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => k))
  have hconst_add :
      (fun _ : Fin 1 => dz j • frame j x₀ + z j • (cov (frame j) x₀) (X x₀)) =
        Function.update
          (fun _ : Fin 1 => dz j • frame j x₀ + z j • (cov (frame j) x₀) (X x₀))
          (0 : Fin 1)
          (dz j • frame j x₀ + z j • (cov (frame j) x₀) (X x₀)) := by
    funext q
    fin_cases q
    simp
  rw [hconst_add]
  rw [(α x₀).map_update_add]
  have h_up1 :
      Function.update
        (fun _ : Fin 1 => dz j • frame j x₀ + z j • (cov (frame j) x₀) (X x₀))
        (0 : Fin 1) (dz j • frame j x₀) =
        fun _ : Fin 1 => dz j • frame j x₀ := by
    funext q
    fin_cases q
    simp
  have h_up2 :
      Function.update
        (fun _ : Fin 1 => dz j • frame j x₀ + z j • (cov (frame j) x₀) (X x₀))
        (0 : Fin 1) (z j • (cov (frame j) x₀) (X x₀)) =
        fun _ : Fin 1 => z j • (cov (frame j) x₀) (X x₀) := by
    funext q
    fin_cases q
    simp
  rw [h_up1, h_up2]
  rw [show α x₀ (fun _ : Fin 1 => dz j • frame j x₀) =
      dz j * coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => j) by
    have hupdate :
        (fun _ : Fin 1 => dz j • frame j x₀) =
          Function.update (fun _ : Fin 1 => frame j x₀) (0 : Fin 1)
            (dz j • frame j x₀) := by
      funext q
      fin_cases q
      simp
    rw [hupdate, (α x₀).map_update_smul]
    simp [h_eval_frame, smul_eq_mul]]
  rw [show α x₀ (fun _ : Fin 1 => z j • (cov (frame j) x₀) (X x₀)) =
      z j * (∑ k : CoordinateIdx (𝕜 := 𝕜) E,
          christoffelAlongInFrame cov frame hframe x₀ (X x₀) j k *
            coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => k)) by
    have hupdate :
        (fun _ : Fin 1 => z j • (cov (frame j) x₀) (X x₀)) =
          Function.update
            (fun _ : Fin 1 => (cov (frame j) x₀) (X x₀))
            (0 : Fin 1)
            (z j • (cov (frame j) x₀) (X x₀)) := by
      funext q
      fin_cases q
      simp
    rw [hupdate, (α x₀).map_update_smul]
    simp [h_eval_cov, smul_eq_mul]]

/-- Coordinate expansion of `nabla0SFun 1` evaluated on an arbitrary tangent
vector.  This is the fixed-coordinate-slot theorem plus multilinearity in the
slot being evaluated. -/
theorem nabla0SFun_one_eval_coordFrame_expanded
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (x₀ : M) (hderiv : ModelDerivEqCoordDeriv0SAt (I := I) X x₀ (fun x => α x))
    (Z : TangentSpace I x₀) :
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      1 cov X α x₀) (fun _ : Fin 1 => Z) =
      ∑ j : CoordinateIdx (𝕜 := 𝕜) E,
        (coordinateFrameAt_toBasis (I := I) x₀).coord j Z *
          (coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => α x)
              (fun _ : Fin 1 => j) -
            ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
              christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
                (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
                x₀ (X x₀) j k *
                coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => k)) := by
  classical
  rw [tensor0S_one_eval_coordFrame_sum (I := I)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [nabla0SFun_one_eval_coordFrame (I := I) cov X α x₀ hderiv j]

/-- Coordinate product-rule reduction for the intrinsic one-form formula.

The two hypotheses are the genuine moving-slot product-rule inputs:
* `hpair` differentiates the scalar pairing `p ↦ α_p (Z_p)` in coordinates;
* `hcovZ` gives the coordinate formula for `α(∇_X Z)`.

Once those are supplied, the canonical derivative `nabla0SFun 1` satisfies the
textbook evaluation formula
`(∇_X α)(Z) = X(α Z) - α(∇_X Z)` at the base point. -/
theorem nabla0SFun_one_eval_of_coordFrame_product
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Z : (x : M) -> TangentSpace I x)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (x₀ : M) (hderiv : ModelDerivEqCoordDeriv0SAt (I := I) X x₀ (fun x => α x))
    (z dz : CoordinateIdx (𝕜 := 𝕜) E -> 𝕜)
    (hz : ∀ j : CoordinateIdx (𝕜 := 𝕜) E,
      z j = (coordinateFrameAt_toBasis (I := I) x₀).coord j (Z x₀))
    (hpair :
      extDerivFun (I := I) (fun y : M => α y (fun _ : Fin 1 => Z y)) x₀ (X x₀) =
        ∑ j : CoordinateIdx (𝕜 := 𝕜) E,
          (dz j * coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => j) +
            z j *
              coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => α x)
                (fun _ : Fin 1 => j)))
    (hcovZ :
      α x₀ (fun _ : Fin 1 => (cov (fun y : M => Z y) x₀) (X x₀)) =
        ∑ j : CoordinateIdx (𝕜 := 𝕜) E,
          (dz j * coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => j) +
            z j *
              (∑ k : CoordinateIdx (𝕜 := 𝕜) E,
                christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
                  (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
                  x₀ (X x₀) j k *
                  coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => k)))) :
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      1 cov X α x₀) (fun _ : Fin 1 => Z x₀) =
      extDerivFun (I := I) (fun y : M => α y (fun _ : Fin 1 => Z y)) x₀ (X x₀) -
        α x₀ (fun _ : Fin 1 => (cov (fun y : M => Z y) x₀) (X x₀)) := by
  classical
  rw [nabla0SFun_one_eval_coordFrame_expanded (I := I) cov X α x₀ hderiv (Z x₀)]
  rw [hpair, hcovZ]
  simp_rw [← hz]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  simp_rw [Finset.sum_add_distrib]
  ring

/-- Version of `nabla0SFun_one_eval_of_coordFrame_product` with the scalar
pairing product rule discharged by `oneForm_pair_coordFrame_product_rule`. -/
theorem nabla0SFun_one_eval_of_coordFrame_product_rule
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Z : (x : M) -> TangentSpace I x)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (x₀ : M) (hderiv : ModelDerivEqCoordDeriv0SAt (I := I) X x₀ (fun x => α x))
    (z dz : CoordinateIdx (𝕜 := 𝕜) E -> 𝕜)
    (hz : ∀ j : CoordinateIdx (𝕜 := 𝕜) E,
      z j = (coordinateFrameAt_toBasis (I := I) x₀).coord j (Z x₀))
    (hdz : ∀ j : CoordinateIdx (𝕜 := 𝕜) E,
      dz j =
        extDerivFun (I := I)
          (fun y : M =>
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y))
          x₀ (X x₀))
    (hdiff_z : ∀ j : CoordinateIdx (𝕜 := 𝕜) E,
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun y : M =>
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y)) x₀)
    (hdiff_α : ∀ j : CoordinateIdx (𝕜 := 𝕜) E,
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun y : M => α y (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j y)) x₀)
    (hcovZ :
      α x₀ (fun _ : Fin 1 => (cov (fun y : M => Z y) x₀) (X x₀)) =
        ∑ j : CoordinateIdx (𝕜 := 𝕜) E,
          (dz j * coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => j) +
            z j *
              (∑ k : CoordinateIdx (𝕜 := 𝕜) E,
                christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
                  (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
                  x₀ (X x₀) j k *
                  coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => k)))) :
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      1 cov X α x₀) (fun _ : Fin 1 => Z x₀) =
      extDerivFun (I := I) (fun y : M => α y (fun _ : Fin 1 => Z y)) x₀ (X x₀) -
        α x₀ (fun _ : Fin 1 => (cov (fun y : M => Z y) x₀) (X x₀)) := by
  exact nabla0SFun_one_eval_of_coordFrame_product
    (I := I) cov X Z α x₀ hderiv z dz hz
    (oneForm_pair_coordFrame_product_rule
      (I := I) X Z α x₀ z dz hz hdz hdiff_z hdiff_α)
    hcovZ

/-- Version of `nabla0SFun_one_eval_of_coordFrame_product` with both moving-slot
product rules discharged in the coordinate frame.  This is the main
coordinate-frame bridge toward the textbook one-form formula
`(∇_X α)(Z) = X(α Z) - α(∇_X Z)`. -/
theorem nabla0SFun_one_eval_of_coordFrame_product_rules
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Z : (x : M) -> TangentSpace I x)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (x₀ : M) (hderiv : ModelDerivEqCoordDeriv0SAt (I := I) X x₀ (fun x => α x))
    (z dz : CoordinateIdx (𝕜 := 𝕜) E -> 𝕜)
    (hz : ∀ j : CoordinateIdx (𝕜 := 𝕜) E,
      z j = (coordinateFrameAt_toBasis (I := I) x₀).coord j (Z x₀))
    (hdz : ∀ j : CoordinateIdx (𝕜 := 𝕜) E,
      dz j =
        extDerivFun (I := I)
          (fun y : M =>
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y))
          x₀ (X x₀))
    (hdiff_z : ∀ j : CoordinateIdx (𝕜 := 𝕜) E,
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun y : M =>
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y)) x₀)
    (hdiff_α : ∀ j : CoordinateIdx (𝕜 := 𝕜) E,
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun y : M => α y (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j y)) x₀)
    (hZ_diff : MDiffAt (T% Z) x₀) :
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      1 cov X α x₀) (fun _ : Fin 1 => Z x₀) =
      extDerivFun (I := I) (fun y : M => α y (fun _ : Fin 1 => Z y)) x₀ (X x₀) -
        α x₀ (fun _ : Fin 1 => (cov (fun y : M => Z y) x₀) (X x₀)) := by
  exact nabla0SFun_one_eval_of_coordFrame_product_rule
    (I := I) cov X Z α x₀ hderiv z dz hz hdz hdiff_z hdiff_α
    (oneForm_covariantDerivative_coordFrame_product_rule
      (I := I) cov X Z α x₀ z dz hz hdz hdiff_z hZ_diff)

/-- Coordinate-frame moving-slot evaluation formula for a one-form.

This discharges the auxiliary coordinate coefficient choices from
`nabla0SFun_one_eval_of_coordFrame_product_rules`.  The remaining hypotheses
are exactly the fixed-slot model-derivative bridge and the differentiability of
the coordinate coefficient functions appearing in the two product rules. -/
theorem nabla0SFun_one_eval_coordFrame_moving
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X Z : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (x₀ : M) (hderiv : ModelDerivEqCoordDeriv0SAt (I := I) X x₀ (fun x => α x))
    (hdiff_z : ∀ j : CoordinateIdx (𝕜 := 𝕜) E,
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun y : M =>
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y)) x₀)
    (hdiff_α : ∀ j : CoordinateIdx (𝕜 := 𝕜) E,
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun y : M => α y (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j y)) x₀) :
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      1 cov X α x₀) (fun _ : Fin 1 => Z x₀) =
      extDerivFun (I := I) (fun y : M => α y (fun _ : Fin 1 => Z y)) x₀ (X x₀) -
        α x₀ (fun _ : Fin 1 => (cov (fun y : M => Z y) x₀) (X x₀)) := by
  let z : CoordinateIdx (𝕜 := 𝕜) E -> 𝕜 :=
    fun j => (coordinateFrameAt_toBasis (I := I) x₀).coord j (Z x₀)
  let dz : CoordinateIdx (𝕜 := 𝕜) E -> 𝕜 :=
    fun j =>
      extDerivFun (I := I)
        (fun y : M =>
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y))
        x₀ (X x₀)
  exact nabla0SFun_one_eval_of_coordFrame_product_rules
    (I := I) cov X Z α x₀ hderiv z dz (by intro j; rfl) (by intro j; rfl)
    hdiff_z hdiff_α
    (Z.contMDiff.contMDiffAt.mdifferentiableAt (by simp))

/-- Local/raw version of `nabla0SFun_one_eval_coordFrame_moving`.

The moving slot only has to be differentiable at the point, with the coordinate
coefficient differentiability hypotheses stated explicitly. This is the local
bridge needed for coordinate-frame fields, which are naturally local rather
than global smooth sections. -/
theorem nabla0SFun_one_eval_coordFrame_moving_raw
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Z : (x : M) -> TangentSpace I x)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (x₀ : M) (hderiv : ModelDerivEqCoordDeriv0SAt (I := I) X x₀ (fun x => α x))
    (hdiff_z : ∀ j : CoordinateIdx (𝕜 := 𝕜) E,
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun y : M =>
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y)) x₀)
    (hdiff_α : ∀ j : CoordinateIdx (𝕜 := 𝕜) E,
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun y : M => α y (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j y)) x₀)
    (hZ_diff : MDiffAt (T% Z) x₀) :
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      1 cov X α x₀) (fun _ : Fin 1 => Z x₀) =
      extDerivFun (I := I) (fun y : M => α y (fun _ : Fin 1 => Z y)) x₀ (X x₀) -
        α x₀ (fun _ : Fin 1 => (cov Z x₀) (X x₀)) := by
  let z : CoordinateIdx (𝕜 := 𝕜) E -> 𝕜 :=
    fun j => (coordinateFrameAt_toBasis (I := I) x₀).coord j (Z x₀)
  let dz : CoordinateIdx (𝕜 := 𝕜) E -> 𝕜 :=
    fun j =>
      extDerivFun (I := I)
        (fun y : M =>
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y))
        x₀ (X x₀)
  exact nabla0SFun_one_eval_of_coordFrame_product_rules
    (I := I) cov X Z α x₀ hderiv z dz (by intro j; rfl) (by intro j; rfl)
    hdiff_z hdiff_α hZ_diff

private theorem coordinateFrame_coeff_contMDiffAt
    (Z : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M) (j : CoordinateIdx (𝕜 := 𝕜) E) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
      (fun y : M =>
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y)) x₀ := by
  let e := coordinateTrivializationAt (I := I) x₀
  have hx : x₀ ∈ e.baseSet := by
    simp [e, coordinateTrivializationAt]
  have hcoeff :=
    contMDiffAt_localFrame_coeff
      (I := I) (V := TangentSpace I) (e := e)
      (b := Module.finBasis 𝕜 E) (s := fun y : M => Z y)
      (k := (∞ : WithTop ℕ∞)) hx Z.contMDiff.contMDiffAt j
  simpa [e, coordinateTrivializationAt, coordinateFrameAt_isLocalFrame_one,
    coordinateFrameAt] using hcoeff

private theorem coordinateFrame_coeff_contMDiffAt_of_contMDiffAt
    (Z : (x : M) -> TangentSpace I x) {x₀ : M}
    (hZ : ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
      (fun y : M => (⟨y, Z y⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x₀)
    (j : CoordinateIdx (𝕜 := 𝕜) E) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
      (fun y : M =>
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y)) x₀ := by
  let e := coordinateTrivializationAt (I := I) x₀
  have hx : x₀ ∈ e.baseSet := by
    simp [e, coordinateTrivializationAt]
  have hcoeff :=
    contMDiffAt_localFrame_coeff
      (I := I) (V := TangentSpace I) (e := e)
      (b := Module.finBasis 𝕜 E) (s := Z)
      (k := (∞ : WithTop ℕ∞)) hx hZ j
  simpa [e, coordinateTrivializationAt, coordinateFrameAt_isLocalFrame_one,
    coordinateFrameAt] using hcoeff

set_option backward.isDefEq.respectTransparency false in
theorem oneForm_eval_coordinateFrame_contMDiffAt
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (x₀ : M) (j : CoordinateIdx (𝕜 := 𝕜) E) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
      (fun y : M => α y (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j y)) x₀ := by
  have hα_top := α.contMDiff x₀
  have hα := hα_top.of_le
    (by simp : (∞ : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  have hframe :
      ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
        (fun y : M =>
          (⟨y, coordinateFrameAt (I := I) x₀ j y⟩ :
            TotalSpace E (TangentSpace I : M -> Type _))) x₀ :=
    (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
      (coordinateFrameSet_open (I := I) x₀)
      (coordinateFrameAt_mem (I := I) x₀) j
  have hEval := TensorMultilinear.contMDiffAt_section_apply
    (I := I) (M := M) (n := 1) (x₀ := x₀)
    (T := fun y : M => α y) hα
    (v := fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j)
    (hv := fun _ : Fin 1 => hframe)
  simpa [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply] using hEval

/-- Intrinsic one-form covariant derivative formula for smooth moving slots. -/
theorem nabla0SFun_one_eval_smooth_slots
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X Z : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (x₀ : M) :
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      1 cov X α x₀) (fun _ : Fin 1 => Z x₀) =
      extDerivFun (I := I) (fun y : M => α y (fun _ : Fin 1 => Z y)) x₀ (X x₀) -
        α x₀ (fun _ : Fin 1 => (cov (fun y : M => Z y) x₀) (X x₀)) := by
  rw [nabla0SFun_one_eval_coordFrame_moving
    (I := I) cov X Z α x₀
    (modelDeriv_eq_coordDeriv0SAt (I := I) X x₀ α)
    (fun j =>
      (coordinateFrame_coeff_contMDiffAt (I := I) Z x₀ j).mdifferentiableAt
        (by simp))
    (fun j =>
      (oneForm_eval_coordinateFrame_contMDiffAt (I := I) α x₀ j).mdifferentiableAt
        (by simp))]

private theorem coordinateFrame_covariantDeriv_apply_contMDiffAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M) (j : CoordinateIdx (𝕜 := 𝕜) E) :
    ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, (cov (coordinateFrameAt (I := I) x₀ j) p) (X p)⟩ :
          TotalSpace E (TangentSpace I : M -> Type _))) x₀ := by
  let u := coordinateFrameSet (I := I) x₀
  let frame := coordinateFrameAt (I := I) x₀
  have hu : IsOpen u := coordinateFrameSet_open (I := I) x₀
  have hx₀ : x₀ ∈ u := coordinateFrameAt_mem (I := I) x₀
  have hframe_smooth :
      CMDiff[u] ((∞ : WithTop ℕ∞) + 1) (T% (frame j)) := by
    exact ((coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffOn j).of_le
      (by simp)
  have hcov_frame :
      ContMDiffOn I (I.prod 𝓘(𝕜, E →L[𝕜] E)) (∞ : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, cov (frame j) p⟩ :
            TotalSpace (E →L[𝕜] E)
              (fun p : M => TangentSpace I p →L[𝕜] TangentSpace I p)))
        u := by
    simpa [u, frame] using (hcov hu).contMDiff hframe_smooth
  have hX_on :
      CMDiff[u] (∞ : WithTop ℕ∞) (T% (fun p : M => X p)) :=
    (X.contMDiff.of_le (by simp :
      (∞ : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))).contMDiffOn
  have hW_on :
      ContMDiffOn I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, (cov (frame j) p) (X p)⟩ :
            TotalSpace E (TangentSpace I : M -> Type _)))
        u := by
    simpa [frame] using hcov_frame.clm_bundle_apply hX_on
  exact (hW_on x₀ hx₀).contMDiffAt (hu.mem_nhds hx₀)

set_option backward.isDefEq.respectTransparency false in
/-- Smoothness of the scalar function obtained by evaluating `nabla0SFun 1`
on a smooth vector field.

This is the intrinsic one-form smoothness input: use the moving-slot formula,
then prove smoothness of the exterior-derivative term and the correction term
separately. -/
theorem nabla0SFun_one_eval_contMDiff
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative cov (∞ : WithTop ℕ∞))
    (X Z : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1) :
    ContMDiff I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          1 cov X α p) (fun _ : Fin 1 => Z p)) := by
  let pair : M -> 𝕜 := fun y => α y (fun _ : Fin 1 => Z y)
  let Xinf : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    ⟨fun p : M => X p, X.contMDiff.of_le (by simp)⟩
  let Zinf : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    ⟨fun p : M => Z p, Z.contMDiff.of_le (by simp)⟩
  let αinf : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 :=
    ⟨fun p : M => α p, α.contMDiff.of_le (by simp)⟩
  have hpair : ContMDiff I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞) pair := by
    simpa [pair, αinf, Zinf] using
      (TensorMultilinear.contMDiff_tensor0SField_apply
        (E := E) (H := H) (I := I) (M := M) (n := 1)
        αinf (fun _ : Fin 1 => Zinf))
  have hderiv :
      ContMDiff I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M => extDerivFun (I := I) pair p (X p)) :=
    extDerivFun_apply_contMDiff (I := I) pair hpair Xinf
  let W : (p : M) -> TangentSpace I p :=
    fun p : M => (cov (fun q : M => Z q) p) (X p)
  have hWtop :
      ContMDiff I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
        (fun p : M => (⟨p, W p⟩ :
          TotalSpace E (TangentSpace I : M -> Type _))) := by
    simpa [W] using
      (TensorLieDeriv.covariantDeriv_vectorField_contMDiff
        (𝕜 := 𝕜) (I := I) (M := M) cov hcov X Z)
  let Winf : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    ⟨W, hWtop.of_le (by simp)⟩
  have hcorr_raw :
      ContMDiff I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M => αinf p (fun _ : Fin 1 => Winf p)) := by
    simpa using
      (TensorMultilinear.contMDiff_tensor0SField_apply
        (E := E) (H := H) (I := I) (M := M) (n := 1)
        αinf (fun _ : Fin 1 => Winf))
  have hcorr :
      ContMDiff I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M => α p
          (fun _ : Fin 1 => (cov (fun q : M => Z q) p) (X p))) := by
    refine hcorr_raw.congr ?_
    intro p
    simp [αinf, Winf, W]
  have hmain :
      ContMDiff I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M =>
          extDerivFun (I := I) pair p (X p) -
            α p (fun _ : Fin 1 => (cov (fun q : M => Z q) p) (X p))) :=
    hderiv.sub hcorr
  refine hmain.congr ?_
  intro p
  rw [nabla0SFun_one_eval_coordFrame_moving
    (I := I) cov X Z α p
    (modelDeriv_eq_coordDeriv0SAt (I := I) X p α)
    (fun j =>
      (coordinateFrame_coeff_contMDiffAt (I := I) Z p j).mdifferentiableAt
        (by simp))
    (fun j =>
        (oneForm_eval_coordinateFrame_contMDiffAt (I := I) α p j).mdifferentiableAt
        (by simp))]

set_option backward.isDefEq.respectTransparency false in
/-- Local coordinate-frame scalar smoothness for `nabla0SFun 1`.

This is the local-frame version of `nabla0SFun_one_eval_contMDiff`: the moving
slot is the chart-induced coordinate-frame field around `x₀`, which is only
known to be smooth locally. The proof uses
`ContMDiffCovariantDerivativeLocally`, not global smooth-section extension. -/
theorem nabla0SFun_one_eval_coordinateFrame_contMDiffAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (x₀ : M) (j : CoordinateIdx (𝕜 := 𝕜) E) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          1 cov X α p)
          (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j p)) x₀ := by
  let Z : (p : M) -> TangentSpace I p := coordinateFrameAt (I := I) x₀ j
  let pair : M -> 𝕜 := fun p => α p (fun _ : Fin 1 => Z p)
  let Xinf : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    ⟨fun p : M => X p, X.contMDiff.of_le (by simp)⟩
  let αinf : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 :=
    ⟨fun p : M => α p, α.contMDiff.of_le (by simp)⟩
  have hpair : ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞) pair x₀ := by
    simpa [pair, Z] using oneForm_eval_coordinateFrame_contMDiffAt
      (I := I) α x₀ j
  have hderiv :
      ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M => extDerivFun (I := I) pair p (X p)) x₀ :=
    extDerivFun_apply_contMDiffAt (I := I) hpair Xinf
  let W : (p : M) -> TangentSpace I p :=
    fun p : M => (cov Z p) (X p)
  have hW :
      ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
        (fun p : M => (⟨p, W p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x₀ := by
    simpa [W, Z] using
      coordinateFrame_covariantDeriv_apply_contMDiffAt
        (I := I) cov hcov X x₀ j
  have hcorr_raw :
      ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M => αinf p (fun _ : Fin 1 => W p)) x₀ := by
    simpa using
      (TensorMultilinear.contMDiffAt_section_apply
        (I := I) (M := M) (n := 1) (x₀ := x₀)
        (T := fun p : M => αinf p) αinf.contMDiff.contMDiffAt
        (v := fun _ : Fin 1 => W)
        (hv := fun _ : Fin 1 => hW))
  have hcorr :
      ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M => α p (fun _ : Fin 1 => W p)) x₀ := by
    refine hcorr_raw.congr_of_eventuallyEq ?_
    filter_upwards with p
    simp [αinf]
  have hmain :
      ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M =>
          extDerivFun (I := I) pair p (X p) -
            α p (fun _ : Fin 1 => W p)) x₀ :=
    hderiv.sub hcorr
  refine hmain.congr_of_eventuallyEq ?_
  filter_upwards [(coordinateFrameSet_open (I := I) x₀).mem_nhds
      (coordinateFrameAt_mem (I := I) x₀)] with p hp
  have hZ_at :
      ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
        (fun y : M => (⟨y, Z y⟩ : TotalSpace E (TangentSpace I : M -> Type _))) p := by
    simpa [Z] using
      (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
        (coordinateFrameSet_open (I := I) x₀) hp j
  rw [nabla0SFun_one_eval_coordFrame_moving_raw
    (I := I) cov X Z α p
    (modelDeriv_eq_coordDeriv0SAt (I := I) X p α)
    (fun k =>
      (coordinateFrame_coeff_contMDiffAt_of_contMDiffAt
        (I := I) Z hZ_at k).mdifferentiableAt (by simp))
    (fun k =>
      (oneForm_eval_coordinateFrame_contMDiffAt
        (I := I) α p k).mdifferentiableAt (by simp))
    (hZ_at.mdifferentiableAt (by simp))]

set_option backward.isDefEq.respectTransparency false in
/-- Local-frame proof that `nabla0SFun 1` is a smooth one-form section.

This avoids global extension of coordinate-frame fields. Smoothness is checked
in local tensor-bundle coordinates, whose basis coefficients are exactly the
scalar evaluations handled by
`nabla0SFun_one_eval_coordinateFrame_contMDiffAt`. -/
theorem nabla0SFun_one_contMDiff
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1) :
    letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) 1
    ContMDiff I (I.prod 𝓘(𝕜, Tensor0SModel 1 𝕜 E)) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          1 cov X α p⟩ :
          TotalSpace (Tensor0SModel 1 𝕜 E) (fun p : M => Tensor0SSpace 1 I p))) := by
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I)
    (M := M) 1
  let F : (p : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) 1 p :=
    fun p : M =>
      nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        1 cov X α p
  let d := Module.finrank 𝕜 E
  let b : Module.Basis (Fin d) 𝕜 E := Module.finBasis 𝕜 E
  refine (contMDiff_multilinearSection_iff_coord (TangentSpace I)
    (∞ : WithTop ℕ∞) b F).mpr ?_
  intro σ x₀
  let j : CoordinateIdx (𝕜 := 𝕜) E := σ 0
  have hframe_eval :=
    nabla0SFun_one_eval_coordinateFrame_contMDiffAt
      (I := I) cov hcov X α x₀ j
  refine hframe_eval.congr_of_eventuallyEq ?_
  filter_upwards
    [(coordinateFrameSet_open (I := I) x₀).mem_nhds
      (coordinateFrameAt_mem (I := I) x₀)] with p hp
  have hslot :
      (fun a : Fin 1 =>
          (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL 𝕜 p
            (b (σ a))) =
        fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j p := by
    funext a
    fin_cases a
    have hp_src : p ∈ (chartAt H x₀).source := by
      simpa [coordinateFrameSet, coordinateTrivializationAt] using hp
    rw [coordinateFrameAt_apply_of_mem (I := I) (x₀ := x₀) (x := p) hp j]
    simpa [j, b] using
      congrArg
        (fun L : E →L[𝕜] TangentSpace I p => L (b j))
        (TangentBundle.symmL_trivializationAt (I := I) (𝕜 := 𝕜) hp_src)
  rw [continuousMultilinearMap_basis_repr]
  change ((trivializationAt (Tensor0SModel 1 𝕜 E)
      (Bundle.continuousMultilinearMap 𝕜 1 E (TangentSpace I : M -> Type _)) x₀
      ⟨p, F p⟩).2)
      (fun a : Fin 1 => b (σ a)) =
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      1 cov X α p) (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j p)
  change (F p).compContinuousLinearMap
      (fun _ : Fin 1 =>
        (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL 𝕜 p)
      (fun a : Fin 1 => b (σ a)) =
    F p (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j p)
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [hslot]

end Coordinates
end RicciFlower
