import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.LocalPropagation
import DifferentialGeometry.Analysis.Calculus.Derivative.LeftEndpoint


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u uE uH

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open Bundle DifferentialGeometry.Tensor0SBundle
open Filter
open scoped Manifold ContDiff ENNReal Topology

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [T2Space M]
variable {D : RealTimeInterval}


theorem scalar_le_of_left_derivative_bounds
    {S : SolutionOn (I := I) (M := M) D} (hS : IsSolutionOn (I := I) S)
    {CStar Q Hd L t0 s v : Real} {z y : M}
    (hCStar : 0 ≤ CStar) (hQ : 0 < Q) (hL1 : 1 ≤ L)
    (hHd : 2 * localPropagationRadius CStar ≤ Hd)
    (hJ : Set.Icc (t0 - Hd / Q) t0 ⊆ D.carrier)
    (hleft : ∀ rho ∈ Set.Icc (t0 - Hd / Q) t0, D.carrier ∈ 𝓝[≤] rho)
    (hbound : ∀ (w : M) (t : Real), t ∈ Set.Icc (t0 - Hd / Q) t0 →
      2 * Q ≤ S.scalar t w →
      (∀ a : TangentSpace I w, |scalarDifferential (I := I) S t w a| ≤
        2 * CStar * (S.scalar t w * Real.sqrt (S.scalar t w)) *
          Real.sqrt ((S.base.metric t).inner w a a)) ∧
      |derivWithin (fun rho : Real => S.scalar rho w) (Set.Iic t) t| ≤
        CStar * S.scalar t w ^ 2)
    (hs : s ∈ Set.Icc (t0 - Hd / (2 * Q)) t0)
    (hz : S.scalar s z ≤ Q * (L - 1))
    (hy : y ∈ riemannianClosedBallOf (I := I) (S.base.metric s) z
      (localPropagationRadius CStar / Real.sqrt (Q * L)))
    (hv : v ∈ Set.Icc (s - localPropagationRadius CStar / (Q * L)) s) :
    S.scalar v y ≤ 4 * (Q * L) := by
  have hLpos : (0 : Real) < L := lt_of_lt_of_le zero_lt_one hL1
  have hP : (0 : Real) < Q * L := mul_pos hQ hLpos
  have hQL : Q ≤ Q * L := by nlinarith
  have hcpos : 0 < localPropagationRadius CStar := localPropagationRadius_pos hCStar
  have hcsmall : CStar * localPropagationRadius CStar < 1 / 20 :=
    mul_localPropagationRadius_lt hCStar
  have hQinv : (0 : Real) < Q⁻¹ := inv_pos.2 hQ
  have hcQpos : (0 : Real) < localPropagationRadius CStar / Q := div_pos hcpos hQ
  have hshift : localPropagationRadius CStar / (Q * L) ≤ localPropagationRadius CStar / Q :=
    div_le_div_of_nonneg_left hcpos.le hQ hQL
  have hhalf : Hd / (2 * Q) + localPropagationRadius CStar / Q ≤ Hd / Q := by
    have e1 : Hd / (2 * Q) = Hd / 2 * Q⁻¹ := by
      field_simp
    have e2 : localPropagationRadius CStar / Q = localPropagationRadius CStar * Q⁻¹ :=
      div_eq_mul_inv _ _
    have e3 : Hd / Q = Hd * Q⁻¹ := div_eq_mul_inv _ _
    rw [e1, e2, e3, ← add_mul]
    exact mul_le_mul_of_nonneg_right (by linarith) hQinv.le
  have hsJ : s ∈ Set.Icc (t0 - Hd / Q) t0 := by
    refine ⟨?_, hs.2⟩
    have h1 := hs.1
    linarith
  have hwin : Set.Icc (s - localPropagationRadius CStar / (Q * L)) s ⊆
      Set.Icc (t0 - Hd / Q) t0 := by
    intro w hw
    refine ⟨?_, le_trans hw.2 hs.2⟩
    have h1 := hs.1
    have h2 := hw.1
    linarith
  have hradpos : 0 < localPropagationRadius CStar / Real.sqrt (Q * L) :=
    div_pos hcpos (Real.sqrt_pos.2 hP)
  have hsqP : (0 : Real) < Real.sqrt (Q * L) := Real.sqrt_pos.2 hP
  obtain ⟨gam, hgam, hgam0, hgam1, hspeed⟩ :=
    exists_path_lintegral_speed_lt_of_mem_closedBall (I := I) (S.base.metric s)
      hradpos.le hradpos hy
  have hspeed2 := hspeed.le
  rw [show localPropagationRadius CStar / Real.sqrt (Q * L) +
        localPropagationRadius CStar / Real.sqrt (Q * L) =
      2 * (localPropagationRadius CStar / Real.sqrt (Q * L)) from by ring] at hspeed2
  have hbudnn : (0 : Real) ≤ 2 * (localPropagationRadius CStar / Real.sqrt (Q * L)) := by
    positivity
  have hstep1 : S.scalar s y ≤ 3 * (Q * L) := by
    have hcont : ContinuousOn (fun sig : Real => S.scalar s (gam sig)) (Set.Icc 0 1) :=
      (((scalarSmoothOfSolution (I := I) S s).continuous).comp hgam.continuous).continuousOn
    have hkey : ∀ t ∈ Set.Icc (0 : Real) 1,
        (fun sig : Real => S.scalar s (gam sig)) t ≤ 3 * (Q * L) := by
      refine forall_le_of_no_crossing (B := 2 * Q) (by linarith) hcont ?_
      intro uu vv h0u huv hv1 hge hstart hend
      have hsub : Set.Icc uu vv ⊆ Set.Icc (0 : Real) 1 := Set.Icc_subset_Icc h0u hv1
      have hpos : ∀ w ∈ Set.Icc uu vv, 0 < S.scalar s (gam w) := by
        intro w hw
        exact lt_of_lt_of_le (by linarith) (hge w hw)
      have hderiv : ∀ w ∈ Set.Icc uu vv,
          HasDerivAt (fun sig : Real => (Real.sqrt (S.scalar s (gam sig)))⁻¹)
            (-(1 / (2 * Real.sqrt (S.scalar s (gam w))) *
                scalarDifferential (I := I) S s (gam w)
                  (mfderiv 𝓘(Real, Real) I gam w (realTangentOne w))) /
                Real.sqrt (S.scalar s (gam w)) ^ 2) w := by
        intro w hw
        exact hasDerivAt_inv_sqrt (hasDerivAt_scalar_comp (I := I) S s hgam w) (hpos w hw)
      have hbdd : ∀ w ∈ Set.Icc uu vv,
          |-(1 / (2 * Real.sqrt (S.scalar s (gam w))) *
              scalarDifferential (I := I) S s (gam w)
                (mfderiv 𝓘(Real, Real) I gam w (realTangentOne w))) /
              Real.sqrt (S.scalar s (gam w)) ^ 2| ≤
            CStar * Real.sqrt ((S.base.metric s).inner (gam w)
              (mfderiv 𝓘(Real, Real) I gam w (realTangentOne w))
              (mfderiv 𝓘(Real, Real) I gam w (realTangentOne w))) := by
        intro w hw
        refine abs_deriv_inv_sqrt_le (hpos w hw) ?_
        have hgd := (hbound (gam w) s hsJ (hge w hw)).1
          (mfderiv 𝓘(Real, Real) I gam w (realTangentOne w))
        have hring : 2 * (CStar * Real.sqrt ((S.base.metric s).inner (gam w)
              (mfderiv 𝓘(Real, Real) I gam w (realTangentOne w))
              (mfderiv 𝓘(Real, Real) I gam w (realTangentOne w)))) *
            (S.scalar s (gam w) * Real.sqrt (S.scalar s (gam w))) =
          2 * CStar * (S.scalar s (gam w) * Real.sqrt (S.scalar s (gam w))) *
            Real.sqrt ((S.base.metric s).inner (gam w)
              (mfderiv 𝓘(Real, Real) I gam w (realTangentOne w))
              (mfderiv 𝓘(Real, Real) I gam w (realTangentOne w))) := by
          ring
        rw [hring]
        exact hgd
      have hbud : |(Real.sqrt (S.scalar s (gam vv)))⁻¹ -
          (Real.sqrt (S.scalar s (gam uu)))⁻¹| ≤
            CStar * (2 * (localPropagationRadius CStar / Real.sqrt (Q * L))) :=
        abs_sub_le_of_hasDerivAt_of_lintegral_le
          (f := fun sig : Real => (Real.sqrt (S.scalar s (gam sig)))⁻¹)
          (a := uu) (b := vv)
          (v := fun w : Real => Real.sqrt ((S.base.metric s).inner (gam w)
            (mfderiv 𝓘(Real, Real) I gam w (realTangentOne w))
            (mfderiv 𝓘(Real, Real) I gam w (realTangentOne w))))
          huv hsub hCStar hbudnn hderiv hbdd hspeed2
      have huupos : 0 < S.scalar s (gam uu) := hpos uu (Set.left_mem_Icc.2 huv)
      have hstart' : S.scalar s (gam uu) ≤ max (2 * Q) (S.scalar s (gam 0)) := hstart
      rw [hgam0] at hstart'
      have hend' : 3 * (Q * L) ≤ S.scalar s (gam vv) := hend
      have hstart2 : S.scalar s (gam uu) ≤ 2 * (Q * L) := by
        refine le_trans hstart' (max_le (by linarith) ?_)
        nlinarith [hz, hP, hQ]
      have hA : (Real.sqrt (2 * (Q * L)))⁻¹ ≤ (Real.sqrt (S.scalar s (gam uu)))⁻¹ := by
        have h2 := one_div_le_one_div_of_le (Real.sqrt_pos.2 huupos)
          (Real.sqrt_le_sqrt hstart2)
        rwa [one_div, one_div] at h2
      have hB : (Real.sqrt (S.scalar s (gam vv)))⁻¹ ≤ (Real.sqrt (3 * (Q * L)))⁻¹ := by
        have h2 := one_div_le_one_div_of_le
          (Real.sqrt_pos.2 (by linarith : (0 : Real) < 3 * (Q * L)))
          (Real.sqrt_le_sqrt hend')
        rwa [one_div, one_div] at h2
      have hgapEq : (Real.sqrt (2 * (Q * L)))⁻¹ - (Real.sqrt (3 * (Q * L)))⁻¹ =
          ((Real.sqrt 2)⁻¹ - (Real.sqrt 3)⁻¹) * (Real.sqrt (Q * L))⁻¹ := by
        rw [Real.sqrt_mul (by norm_num : (0 : Real) ≤ 2),
          Real.sqrt_mul (by norm_num : (0 : Real) ≤ 3), mul_inv, mul_inv]
        ring
      have hbudEq : CStar * (2 * (localPropagationRadius CStar / Real.sqrt (Q * L))) =
          2 * (CStar * localPropagationRadius CStar) * (Real.sqrt (Q * L))⁻¹ := by
        rw [div_eq_mul_inv]
        ring
      have hnum : 2 * (CStar * localPropagationRadius CStar) <
          (Real.sqrt 2)⁻¹ - (Real.sqrt 3)⁻¹ := by
        linarith [one_div_ten_lt_inv_sqrt_two_sub_inv_sqrt_three]
      have hfin : CStar * (2 * (localPropagationRadius CStar / Real.sqrt (Q * L))) <
          (Real.sqrt (2 * (Q * L)))⁻¹ - (Real.sqrt (3 * (Q * L)))⁻¹ := by
        rw [hgapEq, hbudEq]
        exact mul_lt_mul_of_pos_right hnum (inv_pos.2 hsqP)
      have hdrop : (Real.sqrt (2 * (Q * L)))⁻¹ - (Real.sqrt (3 * (Q * L)))⁻¹ ≤
          CStar * (2 * (localPropagationRadius CStar / Real.sqrt (Q * L))) := by
        refine le_trans ?_ hbud
        linarith [hA, hB, neg_le_abs ((Real.sqrt (S.scalar s (gam vv)))⁻¹ -
          (Real.sqrt (S.scalar s (gam uu)))⁻¹)]
      linarith
    have h1 : S.scalar s (gam 1) ≤ 3 * (Q * L) := hkey 1 ⟨by norm_num, le_rfl⟩
    rwa [hgam1] at h1
  have hvs : v ≤ s := hv.2
  have hsv : (0 : Real) ≤ s - v := by linarith
  have hsvle : s - v ≤ localPropagationRadius CStar / (Q * L) := by
    have h1 := hv.1
    linarith
  have htimes : ∀ sg ∈ Set.Icc (0 : Real) 1,
      s - sg * (s - v) ∈ Set.Icc (s - localPropagationRadius CStar / (Q * L)) s := by
    intro sg hsg
    exact ⟨by nlinarith [hsg.1, hsg.2], by nlinarith [hsg.1]⟩
  have hdiffy : ∀ rho ∈ Set.Icc (s - localPropagationRadius CStar / (Q * L)) s,
      HasDerivWithinAt (fun sigma : Real => S.scalar sigma y)
        (derivWithin (fun sigma : Real => S.scalar sigma y) (Set.Iic rho) rho) D.carrier rho := by
    intro rho hrho
    exact hasDerivWithinAt_left_of_mem_nhdsLE
      (hS.scalarTime (K := D.carrier) (hJ (hwin hrho)) Set.Subset.rfl y)
      (hleft rho (hwin hrho))
  have hftd : ∀ sg ∈ Set.Icc (0 : Real) 1,
      HasDerivWithinAt (fun sig : Real => S.scalar (s - sig * (s - v)) y)
        (derivWithin (fun rho : Real => S.scalar rho y) (Set.Iic (s - sg * (s - v)))
          (s - sg * (s - v)) * -(s - v)) (Set.Icc 0 1) sg := by
    intro sg hsg
    have hline : HasDerivAt (fun sig : Real => s - sig * (s - v)) (-(s - v)) sg := by
      simpa using ((hasDerivAt_id sg).mul_const (s - v)).const_sub s
    exact (hdiffy _ (htimes sg hsg)).comp sg hline.hasDerivWithinAt
      (fun r hr => hJ (hwin (htimes r hr)))
  have hcontT : ContinuousOn (fun sig : Real => S.scalar (s - sig * (s - v)) y)
      (Set.Icc 0 1) := fun sg hsg => (hftd sg hsg).continuousWithinAt
  have hkeyT : ∀ t ∈ Set.Icc (0 : Real) 1,
      (fun sig : Real => S.scalar (s - sig * (s - v)) y) t ≤ 4 * (Q * L) := by
    refine forall_le_of_no_crossing (B := 2 * Q) (by linarith) hcontT ?_
    intro uu vv h0u huv hv1 hge hstart hend
    have hsub : Set.Icc uu vv ⊆ Set.Icc (0 : Real) 1 := Set.Icc_subset_Icc h0u hv1
    have hpos : ∀ w ∈ Set.Icc uu vv, 0 < S.scalar (s - w * (s - v)) y := by
      intro w hw
      exact lt_of_lt_of_le (by linarith) (hge w hw)
    have hderiv : ∀ w ∈ Set.Icc uu vv,
        HasDerivWithinAt (fun sig : Real => (S.scalar (s - sig * (s - v)) y)⁻¹)
          (-(derivWithin (fun rho : Real => S.scalar rho y) (Set.Iic (s - w * (s - v))) (s - w * (s - v)) *
              -(s - v)) / S.scalar (s - w * (s - v)) y ^ 2) (Set.Icc uu vv) w := by
      intro w hw
      exact ((hftd w (hsub hw)).inv (ne_of_gt (hpos w hw))).mono hsub
    have hbdd : ∀ w ∈ Set.Icc uu vv,
        ‖-(derivWithin (fun rho : Real => S.scalar rho y) (Set.Iic (s - w * (s - v))) (s - w * (s - v)) *
            -(s - v)) / S.scalar (s - w * (s - v)) y ^ 2‖ ≤ CStar * (s - v) := by
      intro w hw
      rw [Real.norm_eq_abs]
      refine abs_deriv_inv_le (hpos w hw) ?_
      have htb := (hbound y (s - w * (s - v)) (hwin (htimes w (hsub hw))) (hge w hw)).2
      have habs : |derivWithin (fun rho : Real => S.scalar rho y) (Set.Iic (s - w * (s - v))) (s - w * (s - v)) * -(s - v)|
          = |derivWithin (fun rho : Real => S.scalar rho y) (Set.Iic (s - w * (s - v))) (s - w * (s - v))| * (s - v) := by
        rw [abs_mul, abs_neg, abs_of_nonneg hsv]
      rw [habs]
      nlinarith [htb, hsv, sq_nonneg (S.scalar (s - w * (s - v)) y)]
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbdd
      (convex_Icc uu vv) (Set.left_mem_Icc.2 huv) (Set.right_mem_Icc.2 huv)
    have hlen : ‖vv - uu‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : Real) ≤ vv - uu)]
      linarith
    have hCnn : (0 : Real) ≤ CStar * (s - v) := mul_nonneg hCStar hsv
    have hbud : ‖(S.scalar (s - vv * (s - v)) y)⁻¹ - (S.scalar (s - uu * (s - v)) y)⁻¹‖ ≤
        CStar * (s - v) := by
      refine le_trans hmvt ?_
      nlinarith [hlen, hCnn]
    have huupos : 0 < S.scalar (s - uu * (s - v)) y := hpos uu (Set.left_mem_Icc.2 huv)
    have hstart' : S.scalar (s - uu * (s - v)) y ≤
        max (2 * Q) (S.scalar (s - 0 * (s - v)) y) := hstart
    rw [zero_mul, sub_zero] at hstart'
    have hend' : 4 * (Q * L) ≤ S.scalar (s - vv * (s - v)) y := hend
    have hstart2 : S.scalar (s - uu * (s - v)) y ≤ 3 * (Q * L) :=
      le_trans hstart' (max_le (by linarith) hstep1)
    have hA : (3 * (Q * L))⁻¹ ≤ (S.scalar (s - uu * (s - v)) y)⁻¹ := by
      have h2 := one_div_le_one_div_of_le huupos hstart2
      rwa [one_div, one_div] at h2
    have hB : (S.scalar (s - vv * (s - v)) y)⁻¹ ≤ (4 * (Q * L))⁻¹ := by
      have h2 := one_div_le_one_div_of_le (by linarith : (0 : Real) < 4 * (Q * L)) hend'
      rwa [one_div, one_div] at h2
    have hgapEq : (3 * (Q * L))⁻¹ - (4 * (Q * L))⁻¹ = 1 / 12 * (Q * L)⁻¹ := by
      rw [mul_inv, mul_inv]
      ring
    have hbudLe : CStar * (s - v) ≤ CStar * localPropagationRadius CStar * (Q * L)⁻¹ := by
      have h1 : s - v ≤ localPropagationRadius CStar * (Q * L)⁻¹ := by
        rw [← div_eq_mul_inv]
        exact hsvle
      nlinarith [hCStar, h1]
    have hfin : CStar * localPropagationRadius CStar * (Q * L)⁻¹ < 1 / 12 * (Q * L)⁻¹ :=
      mul_lt_mul_of_pos_right (by linarith) (inv_pos.2 hP)
    have hdrop : (3 * (Q * L))⁻¹ - (4 * (Q * L))⁻¹ ≤ CStar * (s - v) := by
      refine le_trans ?_ hbud
      rw [Real.norm_eq_abs]
      linarith [hA, hB, neg_le_abs ((S.scalar (s - vv * (s - v)) y)⁻¹ -
        (S.scalar (s - uu * (s - v)) y)⁻¹)]
    rw [hgapEq] at hdrop
    linarith
  have hfinal : S.scalar (s - 1 * (s - v)) y ≤ 4 * (Q * L) := hkeyT 1 ⟨by norm_num, le_rfl⟩
  rwa [one_mul, sub_sub_cancel] at hfinal

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
