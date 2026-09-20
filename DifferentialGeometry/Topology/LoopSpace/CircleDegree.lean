/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopClassReparametrization
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Degree of a self map of the loop circle

`LoopClassReparametrization` treats the degree `±1` case: a homeomorphism of `loopCircle` lifts
to an affine periodic homeomorphism of `ℝ` of shift `1`, and precomposition with it does not
change the free homotopy class of a loop.  This file treats an arbitrary degree.

A continuous self map `ρ` of `loopCircle` lifts through the covering `ℝ → loopCircle` to a
continuous `f : ℝ → ℝ` with `f (t + 1) = f t + n` for a fixed integer `n`; this `n` is the degree
of `ρ`.  (The existence of such a lift is `exists_real_lift_intShift`, proved elsewhere; it is an
input here, never reproved.)  The two steps carried out below are:

* `freeLoop_comp_intShiftCircleMap_homotopic`: a self map with lift shift `n` is freely homotopic
  to the standard degree `n` map `circlePow n`, by the straight line homotopy in the lift.  This
  is the exact analogue of `freeLoop_comp_affineCircleMap_homotopic` with target `n * t` in place
  of `t`.
* `loopDegreeClass_eq_zpow`: precomposing a loop with `circlePow n` raises its based homotopy
  class to the `n`-th power.  The proof reads the precomposed loop as `γ` transported along the
  straight real path from `0` to `n` in the covering; since `ℝ` is simply connected, only the
  endpoints of that real path matter, and concatenating two such paths multiplies the classes.

Main results.

* `circlePow`: the standard degree `n` self map of `loopCircle`, induced by `t ↦ n * t`.
* `freeLoop_comp_homotopic_circlePow`: if `ρ` has a lift of shift `n`, then `γ.comp ρ` is freely
  homotopic to `γ.comp (circlePow n)`.
* `basedCircleFundamentalGroupClass_comp_circlePow`: the based class of `γ.comp (circlePow n)` at
  `γ 0` is the `n`-th power of the based class of `γ`.
* `FreeLoop.conjugacyClass_comp_circlePow` and
  `FreeLoop.conjugacyClass_comp_of_lift_intShift`: the free homotopy class of the precomposed
  loop is the `n`-th power of the class of `γ`, in the `ConjClasses.mk (... ^ n)` form required to
  discharge the `hpow` hypothesis of
  `EmbeddedDisk.not_loopClassMeets_paramLoop_of_conjugacyClass_eq_zpow`.

The basepoint of the free class is arbitrary, but a `PathConnectedSpace` assumption is needed for
`FreeLoop.conjugacyClass` to be available at all, exactly as in the degree `±1` statements.
-/

noncomputable section

namespace DifferentialGeometry.Topology

universe u

variable {X : Type u} [TopologicalSpace X]

/-- An integer, viewed as a real number, is zero in `loopCircle`. -/
theorem loopCircle_intCast_eq_zero (n : ℤ) : (((n : ℝ)) : loopCircle) = 0 := by
  refine (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mpr ⟨n, ?_⟩
  simp

/-- Translating a real number by an integer does not change its class in `loopCircle`. -/
theorem loopCircle_coe_add_intCast (t : ℝ) (n : ℤ) :
    ((t + (n : ℝ) : ℝ) : loopCircle) = ((t : ℝ) : loopCircle) := by
  rw [AddCircle.coe_add, loopCircle_intCast_eq_zero, add_zero]

/-- The self map of `loopCircle` descended from a continuous real map whose shift over one period
is the constant integer `n`.  This is `affineCircleMap` with the shift `1` replaced by `n`. -/
def intShiftCircleMap (f : ℝ → ℝ) (hc : Continuous f) (n : ℤ)
    (hp : ∀ t, f (t + 1) = f t + (n : ℝ)) : C(loopCircle, loopCircle) :=
  periodicLoop (fun t => ((f t : ℝ) : loopCircle))
    (by
      intro t
      change ((f (t + 1) : ℝ) : loopCircle) = ((f t : ℝ) : loopCircle)
      rw [hp, loopCircle_coe_add_intCast])
    ((AddCircle.continuous_mk' (1 : ℝ)).comp hc)

/-- `intShiftCircleMap` evaluates through the covering by applying the lift. -/
@[simp] theorem intShiftCircleMap_coe (f : ℝ → ℝ) (hc : Continuous f) (n : ℤ)
    (hp : ∀ t, f (t + 1) = f t + (n : ℝ)) (t : ℝ) :
    intShiftCircleMap f hc n hp (t : loopCircle) = ((f t : ℝ) : loopCircle) := rfl

/-- The standard degree `n` self map of `loopCircle`, induced by `t ↦ n * t` on the covering. -/
def circlePow (n : ℤ) : C(loopCircle, loopCircle) :=
  intShiftCircleMap (fun t => (n : ℝ) * t) (continuous_const.mul continuous_id) n
    (by intro t; ring)

/-- `circlePow n` multiplies a representative in the covering by `n`. -/
@[simp] theorem circlePow_coe (n : ℤ) (t : ℝ) :
    circlePow n (t : loopCircle) = (((n : ℝ) * t : ℝ) : loopCircle) := rfl

/-- The standard degree `n` map fixes the basepoint of `loopCircle`. -/
theorem circlePow_apply_zero (n : ℤ) : circlePow n 0 = 0 := by
  have h : circlePow n (((0 : ℝ) : loopCircle)) = (((n : ℝ) * 0 : ℝ) : loopCircle) := rfl
  rw [mul_zero] at h
  exact h

/-- Precomposition with the standard degree `n` map preserves the value at the basepoint. -/
theorem comp_circlePow_apply_zero (γ : freeLoop X) (n : ℤ) :
    (γ.comp (circlePow n)) 0 = γ 0 := by
  change γ (circlePow n 0) = γ 0
  rw [circlePow_apply_zero]

/-- The straight line interpolation between a lift of shift `n` and the map `t ↦ n * t` is
continuous. -/
theorem continuous_intShiftInterpolate (f : ℝ → ℝ) (hc : Continuous f) (n : ℤ) (s : ℝ) :
    Continuous (fun t : ℝ => (1 - s) * f t + s * ((n : ℝ) * t)) :=
  (continuous_const.mul hc).add (continuous_const.mul (continuous_const.mul continuous_id))

/-- The straight line interpolation between a lift of shift `n` and the map `t ↦ n * t` again has
shift `n`. -/
theorem intShiftInterpolate_periodic (f : ℝ → ℝ) (n : ℤ)
    (hp : ∀ t, f (t + 1) = f t + (n : ℝ)) (s : ℝ) :
    ∀ t, (1 - s) * f (t + 1) + s * ((n : ℝ) * (t + 1)) =
      (1 - s) * f t + s * ((n : ℝ) * t) + (n : ℝ) := by
  intro t
  rw [hp]
  ring

/-- A self map of `loopCircle` with a lift of shift `n` precomposes a loop in the same way, up to
free homotopy, as the standard degree `n` map does.  The homotopy is the straight line homotopy
in the covering. -/
theorem freeLoop_comp_intShiftCircleMap_homotopic (γ : freeLoop X) (f : ℝ → ℝ)
    (hc : Continuous f) (n : ℤ) (hp : ∀ t, f (t + 1) = f t + (n : ℝ)) :
    (γ.comp (intShiftCircleMap f hc n hp)).Homotopic (γ.comp (circlePow n)) := by
  refine ⟨⟨⟨fun z : unitInterval × loopCircle =>
      γ (intShiftCircleMap (fun t => (1 - (z.1 : ℝ)) * f t + (z.1 : ℝ) * ((n : ℝ) * t))
        (continuous_intShiftInterpolate f hc n _) n
        (intShiftInterpolate_periodic f n hp _) z.2), ?_⟩, ?_, ?_⟩⟩
  · apply (unitInterval_to_loopCircle_prod_quotient unitInterval).continuous_iff.mpr
    exact γ.continuous.comp ((AddCircle.continuous_mk' (1 : ℝ)).comp
      (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        (hc.comp (continuous_subtype_val.comp continuous_snd))).add
        ((continuous_subtype_val.comp continuous_fst).mul
          (continuous_const.mul (continuous_subtype_val.comp continuous_snd)))))
  · intro θ
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
    change γ (((1 - ((0 : unitInterval) : ℝ)) * f t +
      ((0 : unitInterval) : ℝ) * ((n : ℝ) * t) : ℝ) : loopCircle) = γ ((f t : ℝ) : loopCircle)
    norm_num
  · intro θ
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
    change γ (((1 - ((1 : unitInterval) : ℝ)) * f t +
      ((1 : unitInterval) : ℝ) * ((n : ℝ) * t) : ℝ) : loopCircle) =
      γ (((n : ℝ) * t : ℝ) : loopCircle)
    norm_num

/-- If `ρ` lifts to a continuous real map of shift `n`, then `γ.comp ρ` is freely homotopic to
`γ.comp (circlePow n)`. -/
theorem freeLoop_comp_homotopic_circlePow (γ : freeLoop X) (ρ : C(loopCircle, loopCircle))
    (f : ℝ → ℝ) (hc : Continuous f) (n : ℤ)
    (hlift : ∀ t : ℝ, ((f t : ℝ) : loopCircle) = ρ ((t : ℝ) : loopCircle))
    (hp : ∀ t : ℝ, f (t + 1) = f t + (n : ℝ)) :
    (γ.comp ρ).Homotopic (γ.comp (circlePow n)) := by
  have hρ : ρ = intShiftCircleMap f hc n hp := by
    ext θ
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
    exact (hlift t).symm
  rw [hρ]
  exact freeLoop_comp_intShiftCircleMap_homotopic γ f hc n hp

/-- A free loop read through the covering `ℝ → loopCircle`. -/
def loopLift (γ : freeLoop X) : C(ℝ, X) :=
  γ.comp ⟨fun t : ℝ => (t : loopCircle), AddCircle.continuous_mk' (1 : ℝ)⟩

/-- `loopLift` evaluates by projecting to `loopCircle` first. -/
theorem loopLift_apply (γ : freeLoop X) (t : ℝ) :
    loopLift γ t = γ ((t : ℝ) : loopCircle) := rfl

/-- `loopLift` sends `0` to the basepoint value of the loop. -/
theorem loopLift_zero (γ : freeLoop X) : loopLift γ 0 = γ 0 := rfl

/-- `loopLift` is invariant under integer translations. -/
theorem loopLift_add_intCast (γ : freeLoop X) (t : ℝ) (n : ℤ) :
    loopLift γ (t + (n : ℝ)) = loopLift γ t := by
  rw [loopLift_apply, loopLift_apply, loopCircle_coe_add_intCast]

/-- `loopLift` sends every integer to the basepoint value of the loop. -/
theorem loopLift_intCast (γ : freeLoop X) (n : ℤ) : loopLift γ ((n : ℝ)) = γ 0 := by
  have h := loopLift_add_intCast γ 0 n
  rw [zero_add] at h
  rw [h, loopLift_zero]

/-- The straight real path from `0` to `c`. -/
def realRay (c : ℝ) : Path (0 : ℝ) c where
  toFun t := c * (t : ℝ)
  continuous_toFun := continuous_const.mul continuous_subtype_val
  source' := by simp
  target' := by simp

/-- The straight real path from `k` to `k + c`. -/
def shiftedRay (k c : ℝ) : Path k (k + c) where
  toFun t := c * (t : ℝ) + k
  continuous_toFun := (continuous_const.mul continuous_subtype_val).add continuous_const
  source' := by simp
  target' := by simp [add_comm]

/-- A path in `X` obtained by reading a free loop along a path in the covering `ℝ`. -/
def loopAlong (γ : freeLoop X) {a c : ℝ} (u : Path a c) {x y : X}
    (hx : loopLift γ a = x) (hy : loopLift γ c = y) : Path x y :=
  (u.map (loopLift γ).continuous).cast hx.symm hy.symm

/-- `loopAlong` evaluates by reading the covering path through `loopLift`. -/
theorem loopAlong_apply (γ : freeLoop X) {a c : ℝ} (u : Path a c) {x y : X}
    (hx : loopLift γ a = x) (hy : loopLift γ c = y) (t : unitInterval) :
    loopAlong γ u hx hy t = loopLift γ (u t) := rfl

/-- Only the endpoints of the covering path matter up to homotopy of paths with fixed endpoints,
because `ℝ` is simply connected. -/
theorem loopAlong_homotopic (γ : freeLoop X) {a c a' c' : ℝ} (u : Path a c) (v : Path a' c')
    {x y : X} (hx : loopLift γ a = x) (hy : loopLift γ c = y)
    (hx' : loopLift γ a' = x) (hy' : loopLift γ c' = y) (h0 : a = a') (h1 : c = c') :
    (loopAlong γ u hx hy).Homotopic (loopAlong γ v hx' hy') := by
  subst h0
  subst h1
  exact Path.Homotopic.pathCast
    (Path.Homotopic.map (SimplyConnectedSpace.paths_homotopic u v) (loopLift γ)) hx.symm hy.symm

/-- Concatenating covering paths concatenates the loops they are read along. -/
theorem loopAlong_trans (γ : freeLoop X) {a c d : ℝ} (u : Path a c) (v : Path c d) {x y z : X}
    (hx : loopLift γ a = x) (hy : loopLift γ c = y) (hz : loopLift γ d = z) :
    loopAlong γ (u.trans v) hx hz = (loopAlong γ u hx hy).trans (loopAlong γ v hy hz) := by
  change ((u.trans v).map (loopLift γ).continuous).cast hx.symm hz.symm = _
  rw [Path.map_trans]
  exact Path.cast_trans _ _ hx.symm hy.symm hz.symm

/-- The loop at `γ 0` that runs `γ` exactly `n` times around the circle. -/
def intLoop (γ : freeLoop X) (n : ℤ) : Path (γ 0) (γ 0) :=
  loopAlong γ (realRay ((n : ℝ))) (loopLift_zero γ) (loopLift_intCast γ n)

/-- `intLoop` is the reading of `γ` along the straight covering path from `0` to `n`, for any
proofs of the endpoint conditions. -/
theorem loopAlong_realRay_intCast (γ : freeLoop X) (n : ℤ) (hx : loopLift γ 0 = γ 0)
    (hy : loopLift γ ((n : ℝ)) = γ 0) : loopAlong γ (realRay ((n : ℝ))) hx hy = intLoop γ n := rfl

/-- `intLoop` evaluates by multiplying the parameter by `n` in the covering. -/
theorem intLoop_apply (γ : freeLoop X) (n : ℤ) (t : unitInterval) :
    intLoop γ n t = γ ((((n : ℝ)) * (t : ℝ) : ℝ) : loopCircle) := rfl

/-- Running `γ` zero times gives the constant loop. -/
theorem intLoop_zero (γ : freeLoop X) : intLoop γ 0 = Path.refl (γ 0) := by
  ext t
  rw [intLoop_apply]
  simp only [Int.cast_zero, zero_mul, Path.refl_apply]
  rfl

/-- Running `γ` once gives the based loop attached to `γ` itself. -/
theorem intLoop_one (γ : freeLoop X) :
    intLoop γ 1 = circleToPath (⟨γ, rfl⟩ : basedCircleLoop (γ 0)) := by
  ext t
  rw [intLoop_apply]
  simp only [Int.cast_one, one_mul]
  rfl

/-- Running `γ` `n` times is exactly precomposition with the standard degree `n` map. -/
theorem intLoop_eq_circleToPath_comp_circlePow (γ : freeLoop X) (n : ℤ) :
    intLoop γ n =
      circleToPath (⟨γ.comp (circlePow n), comp_circlePow_apply_zero γ n⟩ :
        basedCircleLoop (γ 0)) := by
  ext t
  rfl

/-- The class in the fundamental group at `γ 0` of the loop running `γ` exactly `n` times. -/
def loopDegreeClass (γ : freeLoop X) (n : ℤ) : FundamentalGroup X (γ 0) :=
  Path.Homotopic.Quotient.mk (intLoop γ n)

/-- Running `γ` zero times gives the identity of the fundamental group. -/
theorem loopDegreeClass_zero (γ : freeLoop X) : loopDegreeClass γ 0 = 1 := by
  have h : loopDegreeClass γ 0 = Path.Homotopic.Quotient.mk (Path.refl (γ 0)) := by
    unfold loopDegreeClass
    rw [intLoop_zero]
  rw [h, Path.Homotopic.Quotient.mk_refl]
  exact FundamentalGroup.one_def.symm

/-- Running `γ` `j + k` times multiplies the classes of running it `j` and `k` times. -/
theorem loopDegreeClass_add (γ : freeLoop X) (j k : ℤ) :
    loopDegreeClass γ (j + k) = loopDegreeClass γ k * loopDegreeClass γ j := by
  have hzero : loopLift γ 0 = γ 0 := loopLift_zero γ
  have hj : loopLift γ ((j : ℝ)) = γ 0 := loopLift_intCast γ j
  have hjk : loopLift γ (((j + k : ℤ) : ℝ)) = γ 0 := loopLift_intCast γ (j + k)
  have hsum : loopLift γ ((j : ℝ) + (k : ℝ)) = γ 0 := by
    have h := loopLift_add_intCast γ ((k : ℝ)) j
    rw [add_comm ((k : ℝ)) ((j : ℝ))] at h
    rw [h]
    exact loopLift_intCast γ k
  have hcast : ((j + k : ℤ) : ℝ) = (j : ℝ) + (k : ℝ) := by push_cast; ring
  have htrans := loopAlong_trans γ (realRay ((j : ℝ))) (shiftedRay ((j : ℝ)) ((k : ℝ)))
    hzero hj hsum
  have hsecond : loopAlong γ (shiftedRay ((j : ℝ)) ((k : ℝ))) hj hsum = intLoop γ k := by
    ext t
    rw [loopAlong_apply]
    change loopLift γ ((k : ℝ) * (t : ℝ) + (j : ℝ)) = intLoop γ k t
    rw [loopLift_add_intCast]
    rfl
  have hhom := loopAlong_homotopic γ (realRay (((j + k : ℤ) : ℝ)))
    ((realRay ((j : ℝ))).trans (shiftedRay ((j : ℝ)) ((k : ℝ)))) hzero hjk hzero hsum rfl hcast
  rw [loopAlong_realRay_intCast γ (j + k) hzero hjk, htrans, hsecond,
    loopAlong_realRay_intCast γ j hzero hj] at hhom
  rw [FundamentalGroup.mul_def]
  change Path.Homotopic.Quotient.mk (intLoop γ (j + k)) =
    Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.mk (intLoop γ j))
      (Path.Homotopic.Quotient.mk (intLoop γ k))
  rw [← Path.Homotopic.Quotient.mk_trans]
  exact Path.Homotopic.Quotient.eq.mpr hhom

/-- Running `γ` backwards once inverts the class of `γ`. -/
theorem loopDegreeClass_neg_one (γ : freeLoop X) :
    loopDegreeClass γ (-1) = (loopDegreeClass γ 1)⁻¹ := by
  have h := loopDegreeClass_add γ 1 (-1)
  rw [show (1 : ℤ) + (-1) = 0 from by ring, loopDegreeClass_zero] at h
  exact eq_inv_of_mul_eq_one_left h.symm

/-- Running `γ` exactly `n` times raises the class of `γ` to the `n`-th power. -/
theorem loopDegreeClass_eq_zpow (γ : freeLoop X) (n : ℤ) :
    loopDegreeClass γ n = loopDegreeClass γ 1 ^ n := by
  induction n using Int.induction_on with
  | zero => rw [loopDegreeClass_zero, zpow_zero]
  | succ i ih =>
      calc loopDegreeClass γ ((i : ℤ) + 1)
          = loopDegreeClass γ 1 * loopDegreeClass γ (i : ℤ) := loopDegreeClass_add γ i 1
        _ = loopDegreeClass γ 1 ^ (1 : ℤ) * loopDegreeClass γ 1 ^ (i : ℤ) := by
              rw [ih, zpow_one]
        _ = loopDegreeClass γ 1 ^ ((1 : ℤ) + (i : ℤ)) := (zpow_add _ _ _).symm
        _ = loopDegreeClass γ 1 ^ ((i : ℤ) + 1) := by rw [add_comm]
  | pred i ih =>
      calc loopDegreeClass γ (-(i : ℤ) - 1)
          = loopDegreeClass γ ((-(i : ℤ)) + (-1)) := by rw [sub_eq_add_neg]
        _ = loopDegreeClass γ (-1) * loopDegreeClass γ (-(i : ℤ)) :=
              loopDegreeClass_add γ (-(i : ℤ)) (-1)
        _ = loopDegreeClass γ 1 ^ (-1 : ℤ) * loopDegreeClass γ 1 ^ (-(i : ℤ)) := by
              rw [loopDegreeClass_neg_one, ih, zpow_neg_one]
        _ = loopDegreeClass γ 1 ^ ((-1 : ℤ) + -(i : ℤ)) := (zpow_add _ _ _).symm
        _ = loopDegreeClass γ 1 ^ (-(i : ℤ) - 1) := by rw [show (-1 : ℤ) + -(i : ℤ) =
              -(i : ℤ) - 1 from by ring]

/-- Precomposing with the standard degree `n` map raises the based fundamental group class of the
loop to the `n`-th power. -/
theorem basedCircleFundamentalGroupClass_comp_circlePow (γ : freeLoop X) (n : ℤ) :
    basedCircleFundamentalGroupClass
        (⟨γ.comp (circlePow n), comp_circlePow_apply_zero γ n⟩ : basedCircleLoop (γ 0)) =
      basedCircleFundamentalGroupClass (⟨γ, rfl⟩ : basedCircleLoop (γ 0)) ^ n := by
  have hleft : basedCircleFundamentalGroupClass
      (⟨γ.comp (circlePow n), comp_circlePow_apply_zero γ n⟩ : basedCircleLoop (γ 0)) =
      loopDegreeClass γ n := by
    unfold basedCircleFundamentalGroupClass loopDegreeClass
    rw [intLoop_eq_circleToPath_comp_circlePow]
  have hright : basedCircleFundamentalGroupClass (⟨γ, rfl⟩ : basedCircleLoop (γ 0)) =
      loopDegreeClass γ 1 := by
    unfold basedCircleFundamentalGroupClass loopDegreeClass
    rw [intLoop_one]
  rw [hleft, hright]
  exact loopDegreeClass_eq_zpow γ n

/-- Conjugate group elements have conjugate integer powers. -/
theorem isConj_zpow {G : Type*} [Group G] {a b : G} (h : IsConj a b) (n : ℤ) :
    IsConj (a ^ n) (b ^ n) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  exact isConj_iff.mpr ⟨c, by rw [← hc, conj_zpow]⟩

/-- The free homotopy class of `γ` precomposed with the standard degree `n` map is the `n`-th
power of the free homotopy class of `γ`. -/
theorem FreeLoop.conjugacyClass_comp_circlePow [PathConnectedSpace X] (γ : freeLoop X) (n : ℤ)
    (x : X) :
    FreeLoop.conjugacyClass (γ.comp (circlePow n)) x =
      ConjClasses.mk (FreeLoop.fundamentalGroupRepresentative γ x ^ n) := by
  classical
  have q : Path x (γ 0) := PathConnectedSpace.somePath x (γ 0)
  have hA := FreeLoop.conjugacyClass_eq_mk_loopRepresentativeAlong q
    (⟨γ.comp (circlePow n), comp_circlePow_apply_zero γ n⟩ : basedCircleLoop (γ 0))
  have hB : ConjClasses.mk (FreeLoop.fundamentalGroupRepresentative γ x) =
      ConjClasses.mk (loopRepresentativeAlong q (⟨γ, rfl⟩ : basedCircleLoop (γ 0))) :=
    FreeLoop.conjugacyClass_eq_mk_loopRepresentativeAlong q (⟨γ, rfl⟩ : basedCircleLoop (γ 0))
  have hrep : loopRepresentativeAlong q
      (⟨γ.comp (circlePow n), comp_circlePow_apply_zero γ n⟩ : basedCircleLoop (γ 0)) =
      loopRepresentativeAlong q (⟨γ, rfl⟩ : basedCircleLoop (γ 0)) ^ n := by
    unfold loopRepresentativeAlong
    rw [basedCircleFundamentalGroupClass_comp_circlePow γ n, map_zpow]
  calc FreeLoop.conjugacyClass (γ.comp (circlePow n)) x
      = ConjClasses.mk (loopRepresentativeAlong q
        (⟨γ.comp (circlePow n), comp_circlePow_apply_zero γ n⟩ : basedCircleLoop (γ 0))) := hA
    _ = ConjClasses.mk (loopRepresentativeAlong q (⟨γ, rfl⟩ : basedCircleLoop (γ 0)) ^ n) := by
          rw [hrep]
    _ = ConjClasses.mk (FreeLoop.fundamentalGroupRepresentative γ x ^ n) :=
          ConjClasses.mk_eq_mk_iff_isConj.mpr
            (isConj_zpow (ConjClasses.mk_eq_mk_iff_isConj.mp hB).symm n)

/-- The free homotopy class of `γ.comp ρ` is the `n`-th power of the free homotopy class of `γ`,
whenever `ρ` lifts through the covering `ℝ → loopCircle` to a continuous real map whose shift over
one period is the constant integer `n`.  Combined with `exists_real_lift_intShift`, which produces
such a lift for an arbitrary continuous self map of `loopCircle`, this discharges the `hpow`
hypothesis of `EmbeddedDisk.not_loopClassMeets_paramLoop_of_conjugacyClass_eq_zpow`. -/
theorem FreeLoop.conjugacyClass_comp_of_lift_intShift [PathConnectedSpace X] (γ : freeLoop X)
    (ρ : C(loopCircle, loopCircle)) (f : ℝ → ℝ) (hc : Continuous f) (n : ℤ)
    (hlift : ∀ t : ℝ, ((f t : ℝ) : loopCircle) = ρ ((t : ℝ) : loopCircle))
    (hp : ∀ t : ℝ, f (t + 1) = f t + (n : ℝ)) (x : X) :
    FreeLoop.conjugacyClass (γ.comp ρ) x =
      ConjClasses.mk (FreeLoop.fundamentalGroupRepresentative γ x ^ n) := by
  rw [FreeLoop.conjugacyClass_eq_of_homotopic
    (freeLoop_comp_homotopic_circlePow γ ρ f hc n hlift hp) x]
  exact FreeLoop.conjugacyClass_comp_circlePow γ n x

end DifferentialGeometry.Topology
