import Mathlib.Analysis.Calculus.MeanValue


import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import DifferentialGeometry.Geometry.Connection.LeviCivita.Variation.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry

attribute [local instance] Fintype.ofFinite
namespace HCGCompactness

open scoped Manifold ContDiff Topology

section ScalarLogDerivative

theorem exp_bounds_of_abs_log_sub_le
    {fa fb R : Real}
    (hfa : 0 < fa) (hfb : 0 < fb)
    (hlog : |Real.log fb - Real.log fa| <= R) :
    Real.exp (-R) * fa <= fb /\ fb <= Real.exp R * fa := by
  have hlow : -R <= Real.log fb - Real.log fa := (abs_le.mp hlog).1
  have hhigh : Real.log fb - Real.log fa <= R := (abs_le.mp hlog).2
  have hratio_pos : 0 < fb / fa := div_pos hfb hfa
  constructor
  · have hlog_ratio : -R <= Real.log (fb / fa) := by
      simpa [Real.log_div hfb.ne' hfa.ne'] using hlow
    have hratio_lower : Real.exp (-R) <= fb / fa :=
      (Real.le_log_iff_exp_le hratio_pos).mp hlog_ratio
    calc
      Real.exp (-R) * fa <= (fb / fa) * fa :=
        mul_le_mul_of_nonneg_right hratio_lower (le_of_lt hfa)
      _ = fb := by
        field_simp [hfa.ne']
  · have hlog_ratio : Real.log (fb / fa) <= R := by
      simpa [Real.log_div hfb.ne' hfa.ne'] using hhigh
    have hratio_upper : fb / fa <= Real.exp R :=
      (Real.log_le_iff_le_exp hratio_pos).mp hlog_ratio
    calc
      fb = (fb / fa) * fa := by
        field_simp [hfa.ne']
      _ <= Real.exp R * fa :=
        mul_le_mul_of_nonneg_right hratio_upper (le_of_lt hfa)

theorem exp_bounds_of_log_deriv_bound
    (f f' : Real -> Real) {a b Lambda : Real}
    (hf_pos : forall s : Real, s ∈ Set.uIcc a b -> 0 < f s)
    (hf_deriv :
      forall s : Real, s ∈ Set.uIcc a b -> HasDerivAt f (f' s) s)
    (hbound :
      forall s : Real, s ∈ Set.uIcc a b -> |f' s / f s| <= Lambda) :
    Real.exp (-Lambda * |b - a|) * f a <= f b /\
      f b <= Real.exp (Lambda * |b - a|) * f a := by
  have hlog_deriv :
      forall s : Real, s ∈ Set.uIcc a b ->
        HasDerivWithinAt (fun y : Real => Real.log (f y)) (f' s / f s)
          (Set.uIcc a b) s := by
    intro s hs
    exact ((hf_deriv s hs).log (ne_of_gt (hf_pos s hs))).hasDerivWithinAt
  have hnorm_bound :
      forall s : Real, s ∈ Set.uIcc a b -> ‖f' s / f s‖ <= Lambda := by
    intro s hs
    simpa only [Real.norm_eq_abs] using hbound s hs
  have hdist :=
    (convex_uIcc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      hlog_deriv hnorm_bound Set.left_mem_uIcc Set.right_mem_uIcc
  have hlog :
      |Real.log (f b) - Real.log (f a)| <= Lambda * |b - a| := by
    simpa [Real.norm_eq_abs] using hdist
  simpa [neg_mul] using
    exp_bounds_of_abs_log_sub_le (hf_pos a Set.left_mem_uIcc)
      (hf_pos b Set.right_mem_uIcc) hlog

theorem affineGronwall_of_abs_deriv_le
    (U U' : Real -> Real) {t0 t alpha beta : Real}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hU_nonneg : forall s : Real, s ∈ Set.uIcc t0 t -> 0 <= U s)
    (hU_deriv :
      forall s : Real, s ∈ Set.uIcc t0 t -> HasDerivAt U (U' s) s)
    (hbound :
      forall s : Real, s ∈ Set.uIcc t0 t -> |U' s| <= alpha * U s + beta) :
    U t <= Real.exp (alpha * |t - t0|) * (U t0 + beta / alpha) := by
  have ha0 : alpha ≠ 0 := ne_of_gt halpha
  have hbpos : 0 < beta / alpha := div_pos hbeta halpha
  have hcancel : alpha * (beta / alpha) = beta := by field_simp
  set W : Real -> Real := fun s => U s + beta / alpha with hW
  have hW_pos : forall s : Real, s ∈ Set.uIcc t0 t -> 0 < W s := by
    intro s hs
    have h1 := hU_nonneg s hs
    have h2 : (0 : Real) < U s + beta / alpha := by linarith
    simpa [hW] using h2
  have hW_deriv :
      forall s : Real, s ∈ Set.uIcc t0 t -> HasDerivAt W (U' s) s := by
    intro s hs
    simpa [hW] using (hU_deriv s hs).add_const (beta / alpha)
  have hW_bound :
      forall s : Real, s ∈ Set.uIcc t0 t -> |U' s / W s| <= alpha := by
    intro s hs
    have hWs : 0 < W s := hW_pos s hs
    rw [abs_div, abs_of_pos hWs, div_le_iff₀ hWs]
    calc |U' s| <= alpha * U s + beta := hbound s hs
      _ = alpha * (U s + beta / alpha) := by rw [mul_add, hcancel]
      _ = alpha * W s := by rw [hW]
  have hmain :=
    (exp_bounds_of_log_deriv_bound W U' hW_pos hW_deriv hW_bound).2
  simp only [hW] at hmain
  linarith [hbpos]

open scoped RealInnerProductSpace in
theorem hasDerivAt_normSq_abs_deriv_le
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
    {c : Real -> F} {c' : F} {t : Real}
    (hc : HasDerivAt c c' t) :
    exists d : Real,
      HasDerivAt (fun s : Real => ‖c s‖ ^ 2) d t ∧
        |d| <= ‖c t‖ ^ 2 + ‖c'‖ ^ 2 := by
  have hbnd : |2 * ⟪c t, c'⟫| <= ‖c t‖ ^ 2 + ‖c'‖ ^ 2 := by
    have hCS : |⟪c t, c'⟫| <= ‖c t‖ * ‖c'‖ := abs_real_inner_le_norm (c t) c'
    have hyoung : 2 * ‖c t‖ * ‖c'‖ <= ‖c t‖ ^ 2 + ‖c'‖ ^ 2 :=
      two_mul_le_add_sq _ _
    calc |2 * ⟪c t, c'⟫|
        = 2 * |⟪c t, c'⟫| := by rw [abs_mul, abs_two]
      _ <= 2 * (‖c t‖ * ‖c'‖) :=
            mul_le_mul_of_nonneg_left hCS (by norm_num)
      _ = 2 * ‖c t‖ * ‖c'‖ := by ring
      _ <= ‖c t‖ ^ 2 + ‖c'‖ ^ 2 := hyoung
  exact ⟨_, hc.norm_sq, hbnd⟩

theorem norm_le_initial_add_deriv_bound
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
    (f f' : Real -> F) {a b L : Real}
    (hf_deriv :
      forall s : Real, s ∈ Set.uIcc a b -> HasDerivAt f (f' s) s)
    (hbound :
      forall s : Real, s ∈ Set.uIcc a b -> ‖f' s‖ <= L) :
    ‖f b‖ <= L * |b - a| + ‖f a‖ := by
  have hderivWithin :
      forall s : Real, s ∈ Set.uIcc a b ->
        HasDerivWithinAt f (f' s) (Set.uIcc a b) s := by
    intro s hs
    exact (hf_deriv s hs).hasDerivWithinAt
  have hdist :=
    (convex_uIcc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      hderivWithin hbound Set.left_mem_uIcc Set.right_mem_uIcc
  have hsub : ‖f b - f a‖ <= L * |b - a| := by
    simpa [Real.norm_eq_abs] using hdist
  calc
    ‖f b‖ = ‖(f b - f a) + f a‖ := by rw [sub_add_cancel]
    _ <= ‖f b - f a‖ + ‖f a‖ := norm_add_le _ _
    _ <= L * |b - a| + ‖f a‖ := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right hsub ‖f a‖

theorem norm_le_initial_add_derivWithin_bound
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
    (f f' : Real -> F) {a b L : Real}
    (hf_deriv :
      forall s : Real, s ∈ Set.uIcc a b ->
        HasDerivWithinAt f (f' s) (Set.uIcc a b) s)
    (hbound :
      forall s : Real, s ∈ Set.uIcc a b -> ‖f' s‖ <= L) :
    ‖f b‖ <= L * |b - a| + ‖f a‖ := by
  have hdist :=
    (convex_uIcc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      hf_deriv hbound Set.left_mem_uIcc Set.right_mem_uIcc
  have hsub : ‖f b - f a‖ <= L * |b - a| := by
    simpa [Real.norm_eq_abs] using hdist
  calc
    ‖f b‖ = ‖(f b - f a) + f a‖ := by rw [sub_add_cancel]
    _ <= ‖f b - f a‖ + ‖f a‖ := norm_add_le _ _
    _ <= L * |b - a| + ‖f a‖ := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right hsub ‖f a‖

end ScalarLogDerivative

section ComponentL2

variable {Idx : Type*}

noncomputable def componentVec3
    (A : Idx -> Idx -> Idx -> Real) :
    EuclideanSpace Real (Idx × Idx × Idx) :=
  WithLp.toLp 2 (fun p : Idx × Idx × Idx => A p.1 p.2.1 p.2.2)

@[simp]
theorem componentVec3_apply
    (A : Idx -> Idx -> Idx -> Real)
    (p : Idx × Idx × Idx) :
    componentVec3 A p = A p.1 p.2.1 p.2.2 := by
  simp [componentVec3, PiLp.toLp_apply]

section FintypeNorm

variable [Fintype Idx]

theorem norm_componentVec3
    (A : Idx -> Idx -> Idx -> Real) :
    ‖componentVec3 A‖ = Real.sqrt (DifferentialGeometry.Geometry.Connection.componentL2Sq3 A) := by
  rw [EuclideanSpace.norm_eq]
  simp [componentVec3, DifferentialGeometry.Geometry.Connection.componentL2Sq3, Real.norm_eq_abs,
    sq_abs]

end FintypeNorm

theorem hasDerivAt_componentVec3
    [finiteIdx : Finite Idx]
    (A A' : Real -> Idx -> Idx -> Idx -> Real) {t : Real}
    (hderiv :
      forall p : Idx × Idx × Idx,
        HasDerivAt (fun s : Real => A s p.1 p.2.1 p.2.2)
          (A' t p.1 p.2.1 p.2.2) t) :
    HasDerivAt (fun s : Real => componentVec3 (A s))
      (componentVec3 (A' t)) t := by
  classical
  letI : Fintype Idx := Fintype.ofFinite Idx
  let L :
      (((Idx × Idx × Idx) → Real) →L[Real]
        EuclideanSpace Real (Idx × Idx × Idx)) :=
    (PiLp.continuousLinearEquiv 2 Real
      (fun _ : Idx × Idx × Idx => Real)).symm.toContinuousLinearMap
  have hpi :
      HasDerivAt
        (fun s : Real => fun p : Idx × Idx × Idx => A s p.1 p.2.1 p.2.2)
        (fun p : Idx × Idx × Idx => A' t p.1 p.2.1 p.2.2) t := by
    rw [hasDerivAt_pi]
    intro p
    exact hderiv p
  have hL :
      HasDerivAt
        (fun s : Real =>
          L (fun p : Idx × Idx × Idx => A s p.1 p.2.1 p.2.2))
        (L (fun p : Idx × Idx × Idx => A' t p.1 p.2.1 p.2.2)) t := by
    have hconst :
        HasDerivAt (fun _s : Real => L)
          (0 : ((Idx × Idx × Idx) → Real) →L[Real]
            EuclideanSpace Real (Idx × Idx × Idx)) t := by
      simpa using hasDerivAt_const (x := t) (c := L)
    simpa using hconst.clm_apply hpi
  simpa [componentVec3, L, PiLp.coe_symm_continuousLinearEquiv] using hL

theorem hasDerivWithinAt_componentVec3
    [finiteIdx : Finite Idx]
    (A A' : Real -> Idx -> Idx -> Idx -> Real) {s : Set Real} {t : Real}
    (hderiv :
      forall p : Idx × Idx × Idx,
        HasDerivWithinAt (fun r : Real => A r p.1 p.2.1 p.2.2)
          (A' t p.1 p.2.1 p.2.2) s t) :
    HasDerivWithinAt (fun r : Real => componentVec3 (A r))
      (componentVec3 (A' t)) s t := by
  classical
  letI : Fintype Idx := Fintype.ofFinite Idx
  let L :
      (((Idx × Idx × Idx) -> Real) →L[Real]
        EuclideanSpace Real (Idx × Idx × Idx)) :=
    (PiLp.continuousLinearEquiv 2 Real
      (fun _ : Idx × Idx × Idx => Real)).symm.toContinuousLinearMap
  have hpi :
      HasDerivWithinAt
        (fun r : Real => fun p : Idx × Idx × Idx => A r p.1 p.2.1 p.2.2)
        (fun p : Idx × Idx × Idx => A' t p.1 p.2.1 p.2.2) s t := by
    rw [hasDerivWithinAt_pi]
    intro p
    exact hderiv p
  have hL :
      HasDerivWithinAt
        (fun r : Real =>
          L (fun p : Idx × Idx × Idx => A r p.1 p.2.1 p.2.2))
        (L (fun p : Idx × Idx × Idx => A' t p.1 p.2.1 p.2.2)) s t := by
    have hconst :
        HasDerivWithinAt (fun _r : Real => L)
          (0 : ((Idx × Idx × Idx) -> Real) →L[Real]
            EuclideanSpace Real (Idx × Idx × Idx)) s t := by
      simpa using (hasDerivAt_const (x := t) (c := L)).hasDerivWithinAt
    simpa using hconst.clm_apply hpi
  simpa [componentVec3, L, PiLp.coe_symm_continuousLinearEquiv] using hL

variable [Fintype Idx]

theorem componentL2_le_initial_add
    (A A' : Real -> Idx -> Idx -> Idx -> Real) {a b L : Real}
    (hderiv :
      forall s : Real, s ∈ Set.uIcc a b ->
        forall p : Idx × Idx × Idx,
          HasDerivAt (fun r : Real => A r p.1 p.2.1 p.2.2)
            (A' s p.1 p.2.1 p.2.2) s)
    (hbound :
      forall s : Real, s ∈ Set.uIcc a b ->
        Real.sqrt (DifferentialGeometry.Geometry.Connection.componentL2Sq3 (A' s)) <= L) :
    Real.sqrt (DifferentialGeometry.Geometry.Connection.componentL2Sq3 (A b)) <=
      L * |b - a| + Real.sqrt (DifferentialGeometry.Geometry.Connection.componentL2Sq3 (A a)) := by
  have hvecDeriv :
      forall s : Real, s ∈ Set.uIcc a b ->
        HasDerivAt (fun r : Real => componentVec3 (A r))
          (componentVec3 (A' s)) s := by
    intro s hs
    exact hasDerivAt_componentVec3 (A := A) (A' := A') (t := s)
      (hderiv s hs)
  have hvecBound :
      forall s : Real, s ∈ Set.uIcc a b ->
        ‖componentVec3 (A' s)‖ <= L := by
    intro s hs
    simpa [norm_componentVec3] using hbound s hs
  have h :=
    norm_le_initial_add_deriv_bound
      (fun s : Real => componentVec3 (A s))
      (fun s : Real => componentVec3 (A' s))
      (a := a) (b := b) (L := L) hvecDeriv hvecBound
  simpa [norm_componentVec3] using h

theorem componentL2_le_initial_add_within
    (A A' : Real -> Idx -> Idx -> Idx -> Real) {a b L : Real}
    (hderiv :
      forall s : Real, s ∈ Set.uIcc a b ->
        forall p : Idx × Idx × Idx,
          HasDerivWithinAt (fun r : Real => A r p.1 p.2.1 p.2.2)
            (A' s p.1 p.2.1 p.2.2) (Set.uIcc a b) s)
    (hbound :
      forall s : Real, s ∈ Set.uIcc a b ->
        Real.sqrt (DifferentialGeometry.Geometry.Connection.componentL2Sq3 (A' s)) <= L) :
    Real.sqrt (DifferentialGeometry.Geometry.Connection.componentL2Sq3 (A b)) <=
      L * |b - a| + Real.sqrt (DifferentialGeometry.Geometry.Connection.componentL2Sq3 (A a)) := by
  have hvecDeriv :
      forall s : Real, s ∈ Set.uIcc a b ->
        HasDerivWithinAt (fun r : Real => componentVec3 (A r))
          (componentVec3 (A' s)) (Set.uIcc a b) s := by
    intro s hs
    exact hasDerivWithinAt_componentVec3 (A := A) (A' := A') (t := s)
      (s := Set.uIcc a b) (hderiv s hs)
  have hvecBound :
      forall s : Real, s ∈ Set.uIcc a b ->
        ‖componentVec3 (A' s)‖ <= L := by
    intro s hs
    simpa [norm_componentVec3] using hbound s hs
  have h :=
    norm_le_initial_add_derivWithin_bound
      (fun s : Real => componentVec3 (A s))
      (fun s : Real => componentVec3 (A' s))
      (a := a) (b := b) (L := L) hvecDeriv hvecBound
  simpa [norm_componentVec3] using h

theorem componentL2_le_initial_add_on_subset
    (A A' : Real -> Idx -> Idx -> Idx -> Real) {S : Set Real} {a b L : Real}
    (hsub : Set.uIcc a b ⊆ S)
    (hderiv :
      forall s : Real, s ∈ Set.uIcc a b ->
        forall p : Idx × Idx × Idx,
          HasDerivWithinAt (fun r : Real => A r p.1 p.2.1 p.2.2)
            (A' s p.1 p.2.1 p.2.2) S s)
    (hbound :
      forall s : Real, s ∈ Set.uIcc a b ->
        Real.sqrt (DifferentialGeometry.Geometry.Connection.componentL2Sq3 (A' s)) <= L) :
    Real.sqrt (DifferentialGeometry.Geometry.Connection.componentL2Sq3 (A b)) <=
      L * |b - a| + Real.sqrt (DifferentialGeometry.Geometry.Connection.componentL2Sq3 (A a)) := by
  refine componentL2_le_initial_add_within
    (A := A) (A' := A') (a := a) (b := b) (L := L) ?_ hbound
  intro s hs p
  exact (hderiv s hs p).mono hsub

theorem gammaL2_le_initial_add
    (Gamma dGamma nablaRic : Real -> Idx -> Idx -> Idx -> Real)
    {a b R : Real}
    (hderiv :
      forall s : Real, s ∈ Set.uIcc a b ->
        forall p : Idx × Idx × Idx,
          HasDerivAt
            (fun r : Real => Gamma r p.1 p.2.1 p.2.2)
            (dGamma s p.1 p.2.1 p.2.2) s)
    (hcombo :
      forall s : Real, s ∈ Set.uIcc a b ->
        forall i j k : Idx,
          dGamma s i j k =
            -nablaRic s i j k - nablaRic s j i k + nablaRic s k i j)
    (hRic :
      forall s : Real, s ∈ Set.uIcc a b ->
        Real.sqrt (DifferentialGeometry.Geometry.Connection.componentL2Sq3 (nablaRic s)) <= R) :
    Real.sqrt (DifferentialGeometry.Geometry.Connection.componentL2Sq3 (Gamma b)) <=
      3 * R * |b - a| +
        Real.sqrt (DifferentialGeometry.Geometry.Connection.componentL2Sq3 (Gamma a)) := by
  refine componentL2_le_initial_add
    (A := Gamma) (A' := dGamma) (a := a) (b := b) (L := 3 * R)
    hderiv ?_
  intro s hs
  exact le_trans
    (DifferentialGeometry.Geometry.Connection.gammaEvol_l2_le (Idx := Idx) (nablaRic s) (dGamma s)
      (hcombo s hs))
    (mul_le_mul_of_nonneg_left (hRic s hs) (by norm_num : (0 : Real) <= 3))

theorem gammaL2_le_initial_add_within
    (Gamma dGamma nablaRic : Real -> Idx -> Idx -> Idx -> Real)
    {a b R : Real}
    (hderiv :
      forall s : Real, s ∈ Set.uIcc a b ->
        forall p : Idx × Idx × Idx,
          HasDerivWithinAt
            (fun r : Real => Gamma r p.1 p.2.1 p.2.2)
            (dGamma s p.1 p.2.1 p.2.2) (Set.uIcc a b) s)
    (hcombo :
      forall s : Real, s ∈ Set.uIcc a b ->
        forall i j k : Idx,
          dGamma s i j k =
            -nablaRic s i j k - nablaRic s j i k + nablaRic s k i j)
    (hRic :
      forall s : Real, s ∈ Set.uIcc a b ->
        Real.sqrt (DifferentialGeometry.Geometry.Connection.componentL2Sq3 (nablaRic s)) <= R) :
    Real.sqrt (DifferentialGeometry.Geometry.Connection.componentL2Sq3 (Gamma b)) <=
      3 * R * |b - a| +
        Real.sqrt (DifferentialGeometry.Geometry.Connection.componentL2Sq3 (Gamma a)) := by
  refine componentL2_le_initial_add_within
    (A := Gamma) (A' := dGamma) (a := a) (b := b) (L := 3 * R)
    hderiv ?_
  intro s hs
  exact le_trans
    (DifferentialGeometry.Geometry.Connection.gammaEvol_l2_le (Idx := Idx) (nablaRic s) (dGamma s)
      (hcombo s hs))
    (mul_le_mul_of_nonneg_left (hRic s hs) (by norm_num : (0 : Real) <= 3))

theorem gammaL2_le_initial_add_on_subset
    (Gamma dGamma nablaRic : Real -> Idx -> Idx -> Idx -> Real)
    {S : Set Real} {a b R : Real}
    (hsub : Set.uIcc a b ⊆ S)
    (hderiv :
      forall s : Real, s ∈ Set.uIcc a b ->
        forall p : Idx × Idx × Idx,
          HasDerivWithinAt
            (fun r : Real => Gamma r p.1 p.2.1 p.2.2)
            (dGamma s p.1 p.2.1 p.2.2) S s)
    (hcombo :
      forall s : Real, s ∈ Set.uIcc a b ->
        forall i j k : Idx,
          dGamma s i j k =
            -nablaRic s i j k - nablaRic s j i k + nablaRic s k i j)
    (hRic :
      forall s : Real, s ∈ Set.uIcc a b ->
        Real.sqrt (DifferentialGeometry.Geometry.Connection.componentL2Sq3 (nablaRic s)) <= R) :
    Real.sqrt (DifferentialGeometry.Geometry.Connection.componentL2Sq3 (Gamma b)) <=
      3 * R * |b - a| +
        Real.sqrt (DifferentialGeometry.Geometry.Connection.componentL2Sq3 (Gamma a)) := by
  refine componentL2_le_initial_add_on_subset
    (A := Gamma) (A' := dGamma) (S := S) (a := a) (b := b)
    (L := 3 * R) hsub hderiv ?_
  intro s hs
  exact le_trans
    (DifferentialGeometry.Geometry.Connection.gammaEvol_l2_le (Idx := Idx) (nablaRic s) (dGamma s)
      (hcombo s hs))
    (mul_le_mul_of_nonneg_left (hRic s hs) (by norm_num : (0 : Real) <= 3))

theorem gammaL2_le_initial_add_regular
    (Gamma dGamma nablaRic : Real -> Idx -> Idx -> Idx -> Real)
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval} {a b R : Real}
    (hsub : Set.uIcc a b ⊆ D.carrier)
    (hregular : forall s : Real, s ∈ Set.uIcc a b -> s ∈ D.regular)
    (hderiv :
      forall t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D,
        forall p : Idx × Idx × Idx,
          HasDerivWithinAt
            (fun r : Real => Gamma r p.1 p.2.1 p.2.2)
            (dGamma (t : Real) p.1 p.2.1 p.2.2) D.carrier (t : Real))
    (hcombo :
      forall s : Real, s ∈ Set.uIcc a b ->
        forall i j k : Idx,
          dGamma s i j k =
            -nablaRic s i j k - nablaRic s j i k + nablaRic s k i j)
    (hRic :
      forall s : Real, s ∈ Set.uIcc a b ->
        Real.sqrt (DifferentialGeometry.Geometry.Connection.componentL2Sq3 (nablaRic s)) <= R) :
    Real.sqrt (DifferentialGeometry.Geometry.Connection.componentL2Sq3 (Gamma b)) <=
      3 * R * |b - a| +
        Real.sqrt (DifferentialGeometry.Geometry.Connection.componentL2Sq3 (Gamma a)) := by
  refine gammaL2_le_initial_add_on_subset
    (Gamma := Gamma) (dGamma := dGamma) (nablaRic := nablaRic)
    (S := D.carrier) (a := a) (b := b) (R := R) hsub ?_ hcombo hRic
  intro s hs p
  simpa using hderiv ⟨s, hregular s hs⟩ p

end ComponentL2

end HCGCompactness
end DifferentialGeometry
