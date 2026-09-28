import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Hamilton.Basic


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open scoped BigOperators Manifold ContDiff Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
  [TopologicalSpace H] {I : ModelWithCorners Real E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

private theorem hasDerivAt_scalar_cutoff_trace
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (alpha : Real → M)
    (P : Fin (Module.finrank Real E) → ∀ r, TangentSpace I (alpha r))
    (chi : Real → Real) {s q : Real} (hs : s ≠ 0) (hchi : HasDerivAt chi q s)
    (ht : T - s ^ 2 ∈ D.regular)
    (halpha : MDifferentiableAt (modelWithCornersSelf Real Real) I alpha s)
    (hP : ∀ i, DifferentiableAt Real (chartRepAt (I := I) alpha (P i) s) s)
    (hDP : ∀ i, IsLAdaptedAt S T alpha (P i) s)
    (hON : ∀ i j,
      (S.base.metric (T - s ^ 2)).inner (alpha s) (P i s) (P j s) =
        if i = j then 1 else 0) :
    HasDerivAt (fun r ↦ r * (chi r) ^ 2 * S.scalar (T - r ^ 2) (alpha r))
      ((Module.finrank Real E : Real) / 2 * q ^ 2 -
        (∑ i : Fin (Module.finrank Real E),
          lRegularizedIndexIntegrand S T alpha (fun r ↦ chi r • P i r)
            (fun r ↦ chi r • P i r) s) -
        (chi s / s) ^ 2 * lHamSq S T alpha s) s := by
  have hRic :
      (∑ i : Fin (Module.finrank Real E),
        S.ricciAt (T - s ^ 2) (alpha s) (vec2 (P i s) (P i s))) =
          S.scalar (T - s ^ 2) (alpha s) := by
    let g := S.base.metric (T - s ^ 2)
    let x := alpha s
    calc
      (∑ i : Fin (Module.finrank Real E),
          S.ricciAt (T - s ^ 2) (alpha s) (vec2 (P i s) (P i s))) =
          ∑ i : Fin (Module.finrank Real E), ricciTensor (I := I) g x (P i s) (P i s) := by
        apply Finset.sum_congr rfl
        intro i _
        exact metricRicciAt_apply_eq_ricciTensor (I := I) g x (P i s) (P i s)
      _ = scalarCurv (I := I) g x :=
        (scalarCurv_eq_orthonormal_trace (I := I) g x (fun i ↦ P i s) hON).symm
      _ = metricScalarAt (I := I) g x := (metricScalar_eq_scal (I := I) g x).symm
      _ = S.scalar (T - s ^ 2) (alpha s) := rfl
  have hscaled :
      (∑ i : Fin (Module.finrank Real E),
        lRegularizedIndexIntegrand S T alpha (fun r ↦ chi r • P i r)
          (fun r ↦ chi r • P i r) s) =
      (chi s) ^ 2 * (∑ i : Fin (Module.finrank Real E),
          lRegularizedIndexIntegrand S T alpha (P i) (P i) s) +
        (Module.finrank Real E : Real) / 2 * q ^ 2 -
        2 * s * chi s * q * S.scalar (T - s ^ 2) (alpha s) := by
    calc
      _ = ∑ i : Fin (Module.finrank Real E),
          ((chi s) ^ 2 * lRegularizedIndexIntegrand S T alpha (P i) (P i) s +
            (1 / 2 : Real) * q ^ 2 *
              (S.base.metric (T - s ^ 2)).inner (alpha s) (P i s) (P i s) -
            2 * s * chi s * q *
              S.ricciAt (T - s ^ 2) (alpha s) (vec2 (P i s) (P i s))) := by
        apply Finset.sum_congr rfl
        intro i _
        simpa only [hchi.deriv] using
          lRegularizedIndexIntegrand_smul_function_self_of_isLAdaptedAt
            (I := I) S T alpha (P i) chi s hchi.differentiableAt (hP i) (hDP i)
      _ = _ := by
        simp only [hON, ite_eq_left, mul_one, Finset.sum_sub_distrib,
          Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
          Finset.card_fin, nsmul_eq_mul]
        rw [hRic]
        ring
  have htrace := lTrace_deriv (I := I) S hS T alpha P s ht halpha hDP hON
  have hprod := ((hchi.div (hasDerivAt_id s) hs).pow 2).mul htrace
  have hfun :
      (fun r : Real ↦ (chi r / r) ^ 2 * (r ^ 3 * S.scalar (T - r ^ 2) (alpha r))) =
        fun r ↦ r * (chi r) ^ 2 * S.scalar (T - r ^ 2) (alpha r) := by
    funext r
    by_cases hr : r = 0
    · subst r
      simp
    · field_simp [hr]
  change HasDerivAt
    (fun r : Real ↦ (chi r / r) ^ 2 * (r ^ 3 * S.scalar (T - r ^ 2) (alpha r))) _ s at hprod
  rw [hfun] at hprod
  apply hprod.congr_deriv
  rw [hscaled]
  norm_num only [Pi.div_apply, Pi.pow_apply, id_eq, pow_one, mul_one]
  field_simp [hs]
  ring

theorem lRegularizedIndex_trace_smul_function
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (alpha : Real → M)
    (P : Fin (Module.finrank Real E) → ∀ r, TangentSpace I (alpha r))
    (chi dchi : Real → Real) (a b : Real) (ha : 0 < a) (hab : a ≤ b)
    (hchi : ∀ s ∈ Icc a b, HasDerivAt chi (dchi s) s)
    (ht : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular)
    (halpha : ∀ s ∈ Icc a b,
      MDifferentiableAt (modelWithCornersSelf Real Real) I alpha s)
    (hP : ∀ i s, s ∈ Icc a b →
      DifferentiableAt Real (chartRepAt (I := I) alpha (P i) s) s)
    (hDP : ∀ i, IsLAdapted S T alpha (P i) (Icc a b))
    (hON : ∀ i j,
      (S.base.metric (T - b ^ 2)).inner (alpha b) (P i b) (P j b) =
        if i = j then 1 else 0)
    (hIint : ∀ i, IntervalIntegrable
      (lRegularizedIndexIntegrand S T alpha (fun s ↦ chi s • P i s)
        (fun s ↦ chi s • P i s)) volume a b)
    (henergy : IntervalIntegrable (fun s ↦ (dchi s) ^ 2) volume a b)
    (hHam : IntervalIntegrable
      (fun s ↦ (chi s / s) ^ 2 * lHamSq S T alpha s) volume a b) :
    (∑ i : Fin (Module.finrank Real E),
      lRegularizedIndex S T alpha (fun s ↦ chi s • P i s)
        (fun s ↦ chi s • P i s) a b) =
      (Module.finrank Real E : Real) / 2 * (∫ s in a..b, (dchi s) ^ 2) -
        (b * (chi b) ^ 2 * S.scalar (T - b ^ 2) (alpha b) -
          a * (chi a) ^ 2 * S.scalar (T - a ^ 2) (alpha a)) -
        ∫ s in a..b, (chi s / s) ^ 2 * lHamSq S T alpha s := by
  have hONs (s : Real) (hs : s ∈ Icc a b)
      (i j : Fin (Module.finrank Real E)) :
      (S.base.metric (T - s ^ 2)).inner (alpha s) (P i s) (P j s) =
        if i = j then 1 else 0 := by
    rw [metric_inner_eq_of_isLAdapted (I := I) S hS T alpha (P i) (P j) hs.2
      (fun r hr ↦ ht r ⟨le_trans hs.1 hr.1, hr.2⟩)
      (fun r hr ↦ halpha r ⟨le_trans hs.1 hr.1, hr.2⟩)
      (fun r hr ↦ hP i r ⟨le_trans hs.1 hr.1, hr.2⟩)
      (fun r hr ↦ hP j r ⟨le_trans hs.1 hr.1, hr.2⟩)
      (fun r hr ↦ hDP i r ⟨le_trans hs.1 hr.1, hr.2⟩)
      (fun r hr ↦ hDP j r ⟨le_trans hs.1 hr.1, hr.2⟩)]
    exact hON i j
  let J : Real → Real := fun s ↦ ∑ i : Fin (Module.finrank Real E),
    lRegularizedIndexIntegrand S T alpha (fun r ↦ chi r • P i r)
      (fun r ↦ chi r • P i r) s
  have hJint : IntervalIntegrable J volume a b := by
    refine (IntervalIntegrable.sum Finset.univ (fun i _ ↦ hIint i)).congr ?_
    intro s _
    simp only [J, Finset.sum_apply]
  have hflux (s : Real) (hs : s ∈ Icc a b) :
      HasDerivAt (fun r ↦ r * (chi r) ^ 2 * S.scalar (T - r ^ 2) (alpha r))
        ((Module.finrank Real E : Real) / 2 * (dchi s) ^ 2 - J s -
          (chi s / s) ^ 2 * lHamSq S T alpha s) s :=
    hasDerivAt_scalar_cutoff_trace S hS T alpha P chi
      (ne_of_gt (ha.trans_le hs.1)) (hchi s hs) (ht s hs) (halpha s hs)
      (fun i ↦ hP i s hs) (fun i ↦ hDP i s hs) (hONs s hs)
  have hfluxInt : IntervalIntegrable
      (fun s ↦ (Module.finrank Real E : Real) / 2 * (dchi s) ^ 2 - J s -
        (chi s / s) ^ 2 * lHamSq S T alpha s) volume a b :=
    ((henergy.const_mul _).sub hJint).sub hHam
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs ↦ hflux s (by simpa only [uIcc_of_le hab] using hs)) hfluxInt
  have hsum : (∫ s in a..b, J s) =
      ∑ i : Fin (Module.finrank Real E),
        lRegularizedIndex S T alpha (fun s ↦ chi s • P i s)
          (fun s ↦ chi s • P i s) a b := by
    exact intervalIntegral.integral_finsetSum (fun i _ ↦ hIint i)
  rw [intervalIntegral.integral_sub ((henergy.const_mul _).sub hJint) hHam,
    intervalIntegral.integral_sub (henergy.const_mul _) hJint,
    intervalIntegral.integral_const_mul, hsum] at hFTC
  linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman
