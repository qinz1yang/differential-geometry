import DifferentialGeometry.Analysis.Calculus.CutoffProfile
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.DistanceBarrier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ShiCutoffData

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Barrier cutoffs for complete Ricci flows

This file constructs the point-centered compactly supported barrier cutoffs
used by the complete-noncompact Bernstein estimate.  The construction applies
the quantitative scalar cutoff profile to the positively rescaled evolving
distance and uses Calabi upper supports only at positive cutoff points.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Set
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff Topology Bundle

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [Module.Finite Real E] [FiniteDimensional Real E]
  [InnerProductSpace Real E] [CompleteSpace E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
  [SigmaCompactSpace M] [T2Space M]

private theorem cutoff_par_bound
    (a U c Q Cη Ccut E r P ep epp G : Real)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hU : 0 ≤ U) (hc : 0 ≤ c) (hQ : 0 ≤ Q) (hCη : 0 ≤ Cη)
    (hE0 : 0 ≤ E) (hEU : E ≤ U) (hr : 0 < r)
    (hactive : 1 ≤ a * E * r)
    (hP : -E * (2 * c / r + Q) ≤ P)
    (hep0 : ep ≤ 0) (hep : |ep| ≤ Cη) (hepp : |epp| ≤ Cη)
    (hG0 : 0 ≤ G) (hG : G ≤ a ^ 2 * U ^ 2)
    (hcut : Cη * (2 * c * U ^ 2 + U * Q + U ^ 2) ≤ Ccut) :
    ep * (a * P) - epp * G ≤ Ccut * a := by
  have ha_sq : a ^ 2 ≤ a := by nlinarith
  have hE_sq : E ^ 2 ≤ U ^ 2 :=
    (sq_le_sq₀ hE0 hU).2 hEU
  have hinv : 1 / r ≤ a * E := by
    exact (div_le_iff₀ hr).2 (by simpa [mul_assoc] using hactive)
  have hAEdiv : a * E / r ≤ a * U ^ 2 := by
    calc
      a * E / r = a * E * (1 / r) := by ring
      _ ≤ a * E * (a * E) :=
        mul_le_mul_of_nonneg_left hinv (mul_nonneg ha0 hE0)
      _ = a ^ 2 * E ^ 2 := by ring
      _ ≤ a ^ 2 * U ^ 2 :=
        mul_le_mul_of_nonneg_left hE_sq (sq_nonneg a)
      _ ≤ a * U ^ 2 :=
        mul_le_mul_of_nonneg_right ha_sq (sq_nonneg U)
  have hA :
      a * E * (2 * c / r + Q) ≤
        a * (2 * c * U ^ 2 + U * Q) := by
    calc
      a * E * (2 * c / r + Q) =
          2 * c * (a * E / r) + a * E * Q := by ring
      _ ≤ 2 * c * (a * U ^ 2) + a * U * Q :=
        add_le_add
          (mul_le_mul_of_nonneg_left hAEdiv
            (mul_nonneg (by norm_num) hc))
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hEU ha0) hQ)
      _ = a * (2 * c * U ^ 2 + U * Q) := by ring
  have hA0 : 0 ≤ a * E * (2 * c / r + Q) := by
    positivity
  have hPu :
      -(a * E * (2 * c / r + Q)) ≤ a * P := by
    have h := mul_le_mul_of_nonneg_left hP ha0
    nlinarith
  have hep_neg : -ep ≤ Cη := by
    linarith [(abs_le.mp hep).1]
  have hepp_neg : -epp ≤ Cη := by
    linarith [(abs_le.mp hepp).1]
  have hfirst :
      ep * (a * P) ≤
        Cη * (a * (2 * c * U ^ 2 + U * Q)) := by
    calc
      ep * (a * P) ≤
          ep * (-(a * E * (2 * c / r + Q))) :=
        mul_le_mul_of_nonpos_left hPu hep0
      _ = (-ep) * (a * E * (2 * c / r + Q)) := by ring
      _ ≤ Cη * (a * E * (2 * c / r + Q)) :=
        mul_le_mul_of_nonneg_right hep_neg hA0
      _ ≤ Cη * (a * (2 * c * U ^ 2 + U * Q)) :=
        mul_le_mul_of_nonneg_left hA hCη
  have hsecond : -epp * G ≤ Cη * (a * U ^ 2) := by
    calc
      -epp * G ≤ Cη * G :=
        mul_le_mul_of_nonneg_right hepp_neg hG0
      _ ≤ Cη * (a ^ 2 * U ^ 2) :=
        mul_le_mul_of_nonneg_left hG hCη
      _ ≤ Cη * (a * U ^ 2) := by
        gcongr
  calc
    ep * (a * P) - epp * G =
        ep * (a * P) + (-epp * G) := by ring
    _ ≤ Cη * (a * (2 * c * U ^ 2 + U * Q)) +
          Cη * (a * U ^ 2) :=
      add_le_add hfirst hsecond
    _ = Cη * (2 * c * U ^ 2 + U * Q + U ^ 2) * a := by
      ring
    _ ≤ Ccut * a :=
      mul_le_mul_of_nonneg_right hcut ha0

/-- A complete Ricci flow with a uniform curvature bound carries
point-centered compactly supported barrier cutoffs on every closed forward
time slab. -/
theorem shiBarrierCutoff_of_sol
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {T K : Real}
    (hT : 0 < T)
    (hslab : Set.Icc 0 T ⊆ D.carrier)
    (hreg : Set.Ioc 0 T ⊆ D.regular)
    (hcomplete :
      RiemannianMetricComplete (I := I) (S.base.metric 0))
    (hK : 0 ≤ K)
    (hcurv : ∀ s ∈ Set.Icc 0 T, ∀ y : M,
      nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K) :
    ∀ O : M,
      Nonempty
        (ShiBarrierCutoffData
          (I := I) (flowG (I := I) S) T O) := by
  classical
  intro O
  let dNat : Nat := Module.finrank Real E
  let d : Real := dNat
  let Λ : Real := d ^ 2 * Real.sqrt K
  let R : Nat → Real := fun n => (n : Real) + 1
  let a : Nat → Real := fun n => (R n)⁻¹
  let U : Real := Real.exp (Λ * T)
  let z : Nat → Real → M → ENNReal := fun n s y =>
    ENNReal.ofReal (Real.exp (Λ * s) / R n) *
      riemannianEDistOf (I := I) (S.base.metric s) O y
  let chi : Nat → Real → M → Real := fun n s y =>
    DifferentialGeometry.Analysis.CutoffProfile.evalue (z n s y)
  let support : Nat → Set M := fun n =>
    {y | riemannianEDistOf (I := I) (S.base.metric 0) O y ≤
      ENNReal.ofReal (2 * R n)}
  have hdNat_pos : 0 < Module.finrank Real E :=
    Nat.pos_of_ne_zero (NeZero.ne _)
  have hd_one : (1 : Real) ≤ d := by
    dsimp only [d]
    exact_mod_cast hdNat_pos
  have hd_sub : 0 ≤ d - 1 := sub_nonneg.mpr hd_one
  have hΛ : 0 ≤ Λ := by
    dsimp only [Λ, d]
    positivity
  have hR : ∀ n, 0 < R n := by
    intro n
    dsimp only [R]
    positivity
  have hcurv0 : ∀ s ∈ Set.Icc 0 T, ∀ y : M,
      normSq0S (I := I) (S.base.metric s) y 4
        (S.base.rm04 s y) ≤ K := by
    intro s hs y
    simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero,
      Nat.add_zero] using hcurv s hs y
  have hricQuad : ∀ s ∈ Set.Icc 0 T, ∀ y : M,
      ∀ v : TangentSpace I y,
        |ricciTensor (I := I) (S.base.metric s) y v v| ≤
          Λ * (S.base.metric s).inner y v v := by
    intro s hs y v
    simpa only [Λ, d, dNat] using
      (ricci_quad_sol (I := I) S y v (hcurv0 s hs y))
  have hpde :=
    metricPDE_Icc (I := I) S hS hT hslab hreg
  have hequiv :=
    metricEquiv_Icc (I := I) (fun s => S.base.metric s)
      hpde hricQuad
  have hedist :=
    edistCont_Icc (I := I) S hS hT hslab hreg hricQuad O
  obtain ⟨Csq, hCsq, hsq⟩ :=
    DifferentialGeometry.Analysis.CutoffProfile.exists_deriv_sq
  obtain ⟨Cη, hCη, hη₁, hη₂⟩ :=
    DifferentialGeometry.Analysis.CutoffProfile.exists_deriv_bounds
  let Q : Real := Real.sqrt ((d - 1) * Λ)
  let Ccut : Real :=
    Csq * U ^ 2 +
      Cη * (2 * (d - 1) * U ^ 2 + U * Q + U ^ 2)
  let err : Nat → Real := fun n => Ccut * a n
  have hU : 0 ≤ U := (Real.exp_pos _).le
  have hQ : 0 ≤ Q := Real.sqrt_nonneg _
  have hCcut : 0 ≤ Ccut := by
    dsimp only [Ccut]
    positivity
  have ha_pos : ∀ n, 0 < a n := by
    intro n
    exact inv_pos.mpr (hR n)
  have ha_le_one : ∀ n, a n ≤ 1 := by
    intro n
    rw [a, inv_le_one₀]
    · dsimp only [R]
      norm_num
    · exact (hR n).le
  have ha_sq : ∀ n, a n ^ 2 ≤ a n := by
    intro n
    nlinarith [ha_pos n, ha_le_one n]
  have herr_nonneg : ∀ n, 0 ≤ err n := by
    intro n
    exact mul_nonneg hCcut (ha_pos n).le
  have herr_tendsto : Tendsto err atTop (nhds 0) := by
    have hbase :
        Tendsto (fun n : Nat => (1 : Real) / ((n : Real) + 1))
          atTop (nhds 0) := by
      simpa using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
    have hmul :=
      (tendsto_const_nhds.mul hbase :
        Tendsto
          (fun n : Nat =>
            Ccut * ((1 : Real) / ((n : Real) + 1)))
          atTop (nhds (Ccut * 0)))
    simpa only [err, a, R, one_div, mul_zero] using hmul
  have hsupport_compact : ∀ n, IsCompact (support n) := by
    intro n
    simpa only [support] using
      (RiemannianMetricComplete.closedEBall_isCompact
        (I := I) hcomplete O (2 * R n))
  have hrange :
      ∀ n s y, s ∈ Set.Icc 0 T →
        chi n s y ∈ Set.Icc (0 : Real) 1 := by
    intro n s y _
    exact
      DifferentialGeometry.Analysis.CutoffProfile.evalue_mem_Icc
        (z n s y)
  have hcenter :
      ∀ s, s ∈ Set.Icc 0 T →
        ∀ᶠ n in atTop, chi n s O = 1 := by
    intro s _
    exact Filter.Eventually.of_forall fun n => by
      dsimp only [chi, z]
      apply
        DifferentialGeometry.Analysis.CutoffProfile.evalue_one_of_le
      simp only [riemannianEDistOf, Manifold.riemannianEDist_self,
        mul_zero, zero_le_one]
  have hanchor :
      ∀ s ∈ Set.Icc 0 T, ∀ y : M,
        riemannianEDistOf (I := I) (S.base.metric 0) O y ≤
          ENNReal.ofReal (Real.exp (Λ * s)) *
            riemannianEDistOf
              (I := I) (S.base.metric s) O y := by
    intro s hs y
    have hmetric :
        ∀ v : TangentSpace I y,
          (S.base.metric 0).inner y v v ≤
            Real.exp (2 * Λ * s) *
              (S.base.metric s).inner y v v := by
      intro v
      have hlo := (hequiv s hs y v).1
      have hlo' :
          Real.exp (-(2 * Λ * s)) *
              (S.base.metric 0).inner y v v ≤
            (S.base.metric s).inner y v v := by
        simpa only [sub_zero] using hlo
      calc
        (S.base.metric 0).inner y v v =
            Real.exp (2 * Λ * s) *
              (Real.exp (-(2 * Λ * s)) *
                (S.base.metric 0).inner y v v) := by
          rw [← mul_assoc, ← Real.exp_add]
          ring_nf
          simp only [Real.exp_zero, one_mul]
        _ ≤ Real.exp (2 * Λ * s) *
              (S.base.metric s).inner y v v :=
          mul_le_mul_of_nonneg_left hlo' (Real.exp_pos _).le
    have hdist :=
      edistOf_le_of_quad
        (I := I) (S.base.metric s) (S.base.metric 0)
        (Real.exp_pos (2 * Λ * s)) hmetric O y
    have hsqrt :
        Real.sqrt (Real.exp (2 * Λ * s)) =
          Real.exp (Λ * s) := by
      calc
        Real.sqrt (Real.exp (2 * Λ * s)) =
            Real.exp ((2 * Λ * s) / 2) :=
          (Real.exp_half _).symm
        _ = Real.exp (Λ * s) := by
          congr 1
          ring
    simpa only [hsqrt] using hdist
  have hzcont :
      ∀ n, ContinuousOn
        (fun p : Real × M => z n p.1 p.2)
        (Set.Icc 0 T ×ˢ (Set.univ : Set M)) := by
    intro n
    have hreal :
        Continuous
          (fun p : Real × M => Real.exp (Λ * p.1) / R n) := by
      simpa only [div_eq_mul_inv] using
        (Real.continuous_exp.comp
          (continuous_const.mul continuous_fst)).mul continuous_const
    have hcoef :
        Continuous
          (fun p : Real × M =>
            ENNReal.ofReal (Real.exp (Λ * p.1) / R n)) :=
      ENNReal.continuous_ofReal.comp hreal
    have hmul :
        ContinuousOn
          (fun p : Real × M =>
            ENNReal.ofReal (Real.exp (Λ * p.1) / R n) *
              riemannianEDistOf
                (I := I) (S.base.metric p.1) O p.2)
          (Set.Icc 0 T ×ˢ (Set.univ : Set M)) :=
      hcoef.continuousOn.ennreal_mul hedist
        (fun p _ => Or.inl
          (ENNReal.ofReal_ne_zero_iff.mpr
            (div_pos (Real.exp_pos _) (hR n))))
        (fun _ _ => Or.inr ENNReal.ofReal_ne_top)
    simpa only [z] using hmul
  have hjoint :
      ∀ n, ContinuousOn
        (fun p : Real × M => chi n p.1 p.2)
        (Set.Icc 0 T ×ˢ support n) := by
    intro n
    have hcomp :=
      DifferentialGeometry.Analysis.CutoffProfile.continuous_evalue
        |>.comp_continuousOn (hzcont n)
    have hcomp' :
        ContinuousOn
          (fun p : Real × M => chi n p.1 p.2)
          (Set.Icc 0 T ×ˢ (Set.univ : Set M)) := by
      simpa only [chi, z, Function.comp_apply] using hcomp
    exact hcomp'.mono fun p hp => ⟨hp.1, Set.mem_univ p.2⟩
  have hsupport_zero :
      ∀ n s, s ∈ Set.Icc 0 T →
        ∀ y, y ∉ support n → chi n s y = 0 := by
    intro n s hs y hy
    apply
      DifferentialGeometry.Analysis.CutoffProfile.evalue_zero_of_ge
    by_contra hz
    have hzlt : z n s y < (2 : ENNReal) := lt_of_not_ge hz
    have hR0 : ENNReal.ofReal (R n) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr (hR n)
    have hRtop : ENNReal.ofReal (R n) ≠ ⊤ :=
      ENNReal.ofReal_ne_top
    have hmul :=
      ENNReal.mul_lt_mul_left hR0 hRtop hzlt
    have hleft :
        z n s y * ENNReal.ofReal (R n) =
          ENNReal.ofReal (Real.exp (Λ * s)) *
            riemannianEDistOf
              (I := I) (S.base.metric s) O y := by
      rw [z, ENNReal.ofReal_div_of_pos (hR n)]
      calc
        (ENNReal.ofReal (Real.exp (Λ * s)) /
              ENNReal.ofReal (R n) *
            riemannianEDistOf
              (I := I) (S.base.metric s) O y) *
              ENNReal.ofReal (R n) =
            (ENNReal.ofReal (Real.exp (Λ * s)) /
                ENNReal.ofReal (R n) *
              ENNReal.ofReal (R n)) *
                riemannianEDistOf
                  (I := I) (S.base.metric s) O y := by
          ac_rfl
        _ = ENNReal.ofReal (Real.exp (Λ * s)) *
              riemannianEDistOf
                (I := I) (S.base.metric s) O y := by
          rw [ENNReal.div_mul_cancel hR0 hRtop]
    have hright :
        (2 : ENNReal) * ENNReal.ofReal (R n) =
          ENNReal.ofReal (2 * R n) := by
      calc
        (2 : ENNReal) * ENNReal.ofReal (R n) =
            ENNReal.ofReal 2 * ENNReal.ofReal (R n) := by
          norm_num
        _ = ENNReal.ofReal (2 * R n) :=
          (ENNReal.ofReal_mul (by norm_num)).symm
    have hsmall :
        ENNReal.ofReal (Real.exp (Λ * s)) *
            riemannianEDistOf
              (I := I) (S.base.metric s) O y <
          ENNReal.ofReal (2 * R n) := by
      simpa only [hleft, hright] using hmul
    have hout :
        ¬ riemannianEDistOf
            (I := I) (S.base.metric 0) O y ≤
          ENNReal.ofReal (2 * R n) := by
      simpa only [support, Set.mem_setOf_eq] using hy
    have hlarge :
        ENNReal.ofReal (2 * R n) <
          ENNReal.ofReal (Real.exp (Λ * s)) *
            riemannianEDistOf
              (I := I) (S.base.metric s) O y :=
      (lt_of_not_ge hout).trans_le (hanchor s hs y)
    exact (not_lt_of_ge hlarge.le) hsmall
  have hchi_real :
      ∀ n s y,
        riemannianEDistOf
            (I := I) (S.base.metric s) O y ≠ ⊤ →
          chi n s y =
            DifferentialGeometry.Analysis.CutoffProfile.value
              (a n * (Real.exp (Λ * s) *
                (riemannianEDistOf
                  (I := I) (S.base.metric s) O y).toReal)) := by
    intro n s y hfin
    have hzfin : z n s y ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
    dsimp only [chi]
    rw [
      DifferentialGeometry.Analysis.CutoffProfile.evalue_eq_value
        hzfin]
    congr 1
    rw [z, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal
        (div_nonneg (Real.exp_pos _).le (hR n).le)]
    dsimp only [a]
    ring
  refine
    ⟨{ chi := chi
       err := err
       support := support
       err_nonneg := herr_nonneg
       err_tendsto := herr_tendsto
       support_compact := hsupport_compact
       support_zero := hsupport_zero
       range := hrange
       center_exhausts := hcenter
       joint_cont := hjoint
       lower_support := ?_ }⟩
  intro n t ht htpos x hxchi
  by_cases hOx : O = x
  · subst x
    let phi : Real → M → Real := fun _ _ => 1
    have hchiO : chi n t O = 1 := by
      dsimp only [chi, z]
      apply
        DifferentialGeometry.Analysis.CutoffProfile.evalue_one_of_le
      simp only [riemannianEDistOf, Manifold.riemannianEDist_self,
        mul_zero, zero_le_one]
    have hz_at :
        ContinuousWithinAt
          (fun p : Real × M => z n p.1 p.2)
          (spacetimeSlab (M := M) T) (t, O) := by
      simpa only [spacetimeSlab] using
        (hzcont n (t, O) ⟨ht, Set.mem_univ O⟩)
    have hzlt : z n t O < (1 : ENNReal) := by
      dsimp only [z]
      simp only [riemannianEDistOf, Manifold.riemannianEDist_self,
        mul_zero, ENNReal.zero_lt_one]
    have hz_nhds :
        ∀ᶠ p in 𝓝[spacetimeSlab (M := M) T] (t, O),
          z n p.1 p.2 < (1 : ENNReal) :=
      hz_at (Iio_mem_nhds hzlt)
    refine
      { phi := phi
        eq_at := ?_
        lower_nhds := ?_
        time_diff := ?_
        space_diff_nhds := ?_
        grad_diff := ?_
        grad_sq_le := ?_
        parabolic_le := ?_ }
    · simpa only [phi] using hchiO.symm
    · filter_upwards [hz_nhds] with p hp
      constructor
      · exact zero_le_one
      · dsimp only [phi, chi]
        rw [
          DifferentialGeometry.Analysis.CutoffProfile.evalue_one_of_le
            hp.le]
    · exact differentiableWithinAt_const (c := (1 : Real))
    · exact Filter.Eventually.of_forall fun _ =>
        mdifferentiableAt_const
    · simpa only [phi] using
        (gradientFun_mdiffAt
          (I := I) (flowG (I := I) S).metric t
          (f := fun _ : M => (1 : Real)) contMDiff_const O)
    · have hgradzero :
          gradientFun
              (I := I) (flowG (I := I) S).metric t
              (phi t) O = 0 := by
        exact gradientFun_const
          (I := I) (flowG (I := I) S).metric t 1 O
      rw [hgradzero]
      simpa only [map_zero, herr_nonneg n, zero_le_mul]
    · have hheat_one :
          heatOperatorWithDrift
              (I := I) (flowG (I := I) S) t
              (fun y => (0 : TangentSpace I y))
              (phi t) O = 0 := by
        unfold heatOperatorWithDrift laplacianAt laplacian
          driftTerm gradientAt
        have hzero :
            gradientFun
                (I := I) (flowG (I := I) S).metric t
                (phi t) = 0 := by
          funext y
          exact gradientFun_const
            (I := I) (flowG (I := I) S).metric t 1 y
        rw [hzero]
        simp
      have hpar :
          parabolicOperatorWithDrift
              (I := I) (flowG (I := I) S) T
              (fun _ y => (0 : TangentSpace I y))
              phi t O = 0 := by
        unfold parabolicOperatorWithDrift
        rw [hheat_one]
        simp only [phi, derivWithin_const, zero_sub]
      rw [hpar]
      exact herr_nonneg n
  · have hdist_fin :
        riemannianEDistOf
            (I := I) (S.base.metric t) O x ≠ ⊤ := by
      intro htop
      have hcoef0 :
          ENNReal.ofReal (Real.exp (Λ * t) / R n) ≠ 0 :=
        ENNReal.ofReal_ne_zero_iff.mpr
          (div_pos (Real.exp_pos _) (hR n))
      have hz_top : z n t x = ⊤ := by
        rw [z, htop, ENNReal.mul_top hcoef0]
      have hchi_zero : chi n t x = 0 := by
        dsimp only [chi]
        rw [hz_top,
          DifferentialGeometry.Analysis.CutoffProfile.evalue_top]
      linarith
    obtain ⟨rho, hrho_eq, hrho_upper, hrho_time, hrho_space,
        hrho_grad, hrho_grad_sq, hrho_par⟩ :=
      scaledDist_calabiUpperSupport_of_sol
        (I := I) S hS O hT hslab hreg hcomplete hK hcurv
          ht htpos x hdist_fin hOx
    let u : Real → M → Real := fun s y => a n * rho s y
    let phi : Real → M → Real := fun s y =>
      DifferentialGeometry.Analysis.CutoffProfile.value (u s y)
    have hu_time :
        DifferentiableWithinAt Real
          (fun s => u s x) (Set.Icc 0 T) t := by
      simpa only [u] using hrho_time.const_mul (a n)
    have hu_space :
        ∀ᶠ y in 𝓝 x,
          MDifferentiableAt I 𝓘(Real, Real) (u t) y := by
      filter_upwards [hrho_space] with y hy
      simpa only [u] using hy.const_smul (a n)
    have hlin : Differentiable Real (fun q : Real => a n * q) :=
      differentiable_const.mul differentiable_id
    have hlin' :
        DifferentiableAt Real
          (deriv (fun q : Real => a n * q)) (rho t x) := by
      have hcd :
          ContDiff Real ∞ (fun q : Real => a n * q) :=
        contDiff_const.mul contDiff_id
      exact
        (hcd.deriv' (n := 1)).differentiable
          (by simp) (rho t x)
    have hu_grad :
        MDifferentiableAt I (I.prod 𝓘(Real, E))
          (T% fun y : M =>
            gradientFun
              (I := I) (flowG (I := I) S).metric t
              (u t) y) x := by
      exact grad_comp_mdiffAt
        (I := I) (flowG (I := I) S).metric t
        hlin hlin' hrho_space hrho_grad
    have hvalue :
        Differentiable Real
          DifferentialGeometry.Analysis.CutoffProfile.value :=
      DifferentialGeometry.Analysis.CutoffProfile.contDiff.differentiable
        (by simp)
    have hvalue' :
        DifferentiableAt Real
          (deriv
            DifferentialGeometry.Analysis.CutoffProfile.value)
          (u t x) := by
      exact
        (DifferentialGeometry.Analysis.CutoffProfile.contDiff.deriv'
          (n := 1)).differentiable
            (by simp) (u t x)
    have hphi_time :
        DifferentiableWithinAt Real
          (fun s => phi s x) (Set.Icc 0 T) t := by
      simpa only [phi, Function.comp_apply] using
        (hvalue (u t x)).differentiableWithinAt.comp t hu_time
    have hphi_space :
        ∀ᶠ y in 𝓝 x,
          MDifferentiableAt I 𝓘(Real, Real) (phi t) y := by
      filter_upwards [hu_space] with y hy
      exact (hvalue (u t y)).mdifferentiableAt.comp y hy
    have hphi_grad :
        MDifferentiableAt I (I.prod 𝓘(Real, E))
          (T% fun y : M =>
            gradientFun
              (I := I) (flowG (I := I) S).metric t
              (phi t) y) x := by
      exact grad_comp_mdiffAt
        (I := I) (flowG (I := I) S).metric t
        hvalue hvalue' hu_space hu_grad
    have hdist_nhds :
        ∀ᶠ p in 𝓝[spacetimeSlab (M := M) T] (t, x),
          riemannianEDistOf
              (I := I) (S.base.metric p.1) O p.2 ≠ ⊤ := by
      have hdist_at :
          ContinuousWithinAt
            (fun p : Real × M =>
              riemannianEDistOf
                (I := I) (S.base.metric p.1) O p.2)
            (spacetimeSlab (M := M) T) (t, x) := by
        simpa only [spacetimeSlab] using
          (hedist (t, x) ⟨ht, Set.mem_univ x⟩)
      have hev :
          ∀ᶠ p in 𝓝[spacetimeSlab (M := M) T] (t, x),
            riemannianEDistOf
                (I := I) (S.base.metric p.1) O p.2 < ⊤ :=
        hdist_at (Iio_mem_nhds hdist_fin.lt_top)
      filter_upwards [hev] with p hp
      exact ne_of_lt hp
    have hlower :
        ∀ᶠ p in 𝓝[spacetimeSlab (M := M) T] (t, x),
          0 ≤ phi p.1 p.2 ∧ phi p.1 p.2 ≤ chi n p.1 p.2 := by
      filter_upwards [hrho_upper, hdist_nhds] with p hp hfin
      constructor
      · exact
          (DifferentialGeometry.Analysis.CutoffProfile.mem_Icc
            (u p.1 p.2)).1
      · have hscaled :
            a n * (Real.exp (Λ * p.1) *
                (riemannianEDistOf
                  (I := I) (S.base.metric p.1) O p.2).toReal) ≤
              a n * rho p.1 p.2 :=
          mul_le_mul_of_nonneg_left hp (ha_pos n).le
        calc
          phi p.1 p.2 =
              DifferentialGeometry.Analysis.CutoffProfile.value
                (a n * rho p.1 p.2) := rfl
          _ ≤ DifferentialGeometry.Analysis.CutoffProfile.value
                (a n * (Real.exp (Λ * p.1) *
                  (riemannianEDistOf
                    (I := I) (S.base.metric p.1) O p.2).toReal)) :=
            DifferentialGeometry.Analysis.CutoffProfile.antitone_value
              hscaled
          _ = chi n p.1 p.2 :=
            (hchi_real n p.1 p.2 hfin).symm
    have heq : phi t x = chi n t x := by
      rw [hchi_real n t x hdist_fin]
      dsimp only [phi, u]
      rw [hrho_eq]
    have hquant :
        ((flowG (I := I) S).metric t).inner x
            (gradientFun
              (I := I) (flowG (I := I) S).metric t
              (phi t) x)
            (gradientFun
              (I := I) (flowG (I := I) S).metric t
              (phi t) x) ≤
          err n * phi t x ∧
        parabolicOperatorWithDrift
            (I := I) (flowG (I := I) S) T
            (fun _ y => (0 : TangentSpace I y))
            phi t x ≤ err n := by
      constructor
      · have hrho_xdiff :=
          hrho_space.self_of_nhds
        have hu_xdiff :=
          hu_space.self_of_nhds
        have hgrad_u :
            gradientFun
                (I := I) (flowG (I := I) S).metric t
                (u t) x =
              a n •
                gradientFun
                  (I := I) (flowG (I := I) S).metric t
                  (rho t) x := by
          simpa only [u, Pi.smul_apply, smul_eq_mul] using
            (gradientFun_const_smul
              (I := I) (flowG (I := I) S).metric t
              (a n) hrho_xdiff)
        have hgrad_phi :
            gradientFun
                (I := I) (flowG (I := I) S).metric t
                (phi t) x =
              deriv
                  DifferentialGeometry.Analysis.CutoffProfile.value
                  (u t x) •
                gradientFun
                  (I := I) (flowG (I := I) S).metric t
                  (u t) x := by
          simpa only [phi] using
            (gradientFun_comp
              (I := I) (flowG (I := I) S).metric t
              (hvalue (u t x)) hu_xdiff)
        have hexp_le :
            Real.exp (Λ * t) ≤ U := by
          dsimp only [U]
          exact Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left ht.2 hΛ)
        have hexp_sq :
            Real.exp (2 * Λ * t) =
              Real.exp (Λ * t) ^ 2 := by
          rw [← Real.exp_nat_mul]
          congr 1
          push_cast
          ring
        have hexp2_le :
            Real.exp (2 * Λ * t) ≤ U ^ 2 := by
          rw [hexp_sq]
          exact (sq_le_sq₀ (Real.exp_pos _).le hU).2 hexp_le
        have hgrad_u_sq :
            ((flowG (I := I) S).metric t).inner x
                (gradientFun
                  (I := I) (flowG (I := I) S).metric t
                  (u t) x)
                (gradientFun
                  (I := I) (flowG (I := I) S).metric t
                  (u t) x) ≤
              a n ^ 2 * U ^ 2 := by
          rw [hgrad_u,
            gInner_smul_self
              (I := I) (flowG (I := I) S).metric t x]
          exact
            (mul_le_mul_of_nonneg_left hrho_grad_sq
              (sq_nonneg (a n))).trans
              (mul_le_mul_of_nonneg_left hexp2_le
                (sq_nonneg (a n)))
        have hprofile :=
          hsq (u t x)
        have hphi_nonneg :
            0 ≤
              DifferentialGeometry.Analysis.CutoffProfile.value
                (u t x) :=
          (DifferentialGeometry.Analysis.CutoffProfile.mem_Icc
            (u t x)).1
        have hbracket :
            0 ≤
              2 * (d - 1) * U ^ 2 + U * Q + U ^ 2 := by
          positivity
        have hCpart : Csq * U ^ 2 ≤ Ccut := by
          dsimp only [Ccut]
          exact le_add_of_nonneg_right (mul_nonneg hCη hbracket)
        calc
          ((flowG (I := I) S).metric t).inner x
                (gradientFun
                  (I := I) (flowG (I := I) S).metric t
                  (phi t) x)
                (gradientFun
                  (I := I) (flowG (I := I) S).metric t
                  (phi t) x) =
              (deriv
                  DifferentialGeometry.Analysis.CutoffProfile.value
                  (u t x)) ^ 2 *
                ((flowG (I := I) S).metric t).inner x
                  (gradientFun
                    (I := I) (flowG (I := I) S).metric t
                    (u t) x)
                  (gradientFun
                    (I := I) (flowG (I := I) S).metric t
                    (u t) x) := by
            rw [hgrad_phi,
              gInner_smul_self
                (I := I) (flowG (I := I) S).metric t x]
          _ ≤
              (deriv
                  DifferentialGeometry.Analysis.CutoffProfile.value
                  (u t x)) ^ 2 * (a n ^ 2 * U ^ 2) :=
            mul_le_mul_of_nonneg_left hgrad_u_sq
              (sq_nonneg _)
          _ ≤
              (Csq *
                DifferentialGeometry.Analysis.CutoffProfile.value
                  (u t x)) * (a n ^ 2 * U ^ 2) :=
            mul_le_mul_of_nonneg_right hprofile
              (mul_nonneg (sq_nonneg _) (sq_nonneg _))
          _ = (Csq * U ^ 2 *
                DifferentialGeometry.Analysis.CutoffProfile.value
                  (u t x)) * a n ^ 2 := by
            ring
          _ ≤ (Csq * U ^ 2 *
                DifferentialGeometry.Analysis.CutoffProfile.value
                  (u t x)) * a n :=
            mul_le_mul_of_nonneg_left (ha_sq n)
              (mul_nonneg
                (mul_nonneg hCsq (sq_nonneg U)) hphi_nonneg)
          _ = (Csq * U ^ 2) *
                (a n *
                  DifferentialGeometry.Analysis.CutoffProfile.value
                    (u t x)) := by
            ring
          _ ≤ Ccut *
                (a n *
                  DifferentialGeometry.Analysis.CutoffProfile.value
                    (u t x)) :=
            mul_le_mul_of_nonneg_right hCpart
              (mul_nonneg (ha_pos n).le hphi_nonneg)
          _ = err n * phi t x := by
            rfl
      · have htime_u :
            derivWithin
                (fun s : Real => u s x) (Set.Icc 0 T) t =
              a n *
                derivWithin
                  (fun s : Real => rho s x) (Set.Icc 0 T) t := by
          simpa only [u] using
            (derivWithin_const_mul (a n) hrho_time)
        have hlap_u :
            laplacianAt
                (I := I) (flowG (I := I) S) t (u t) x =
              a n *
                laplacianAt
                  (I := I) (flowG (I := I) S) t (rho t) x := by
          rw [laplacianAt_eq, laplacianAt_eq]
          simpa only [u, Pi.smul_apply, smul_eq_mul] using
            (laplacian_smul_at
              (I := I)
              (LeviCivita
                (I := I) ((flowG (I := I) S).metric t))
              ((flowG (I := I) S).metric t) (a n)
              hrho_space hrho_grad)
        have hpar_u :
            parabolicOperatorWithDrift
                (I := I) (flowG (I := I) S) T
                (fun _ y => (0 : TangentSpace I y)) u t x =
              a n *
                parabolicOperatorWithDrift
                  (I := I) (flowG (I := I) S) T
                  (fun _ y => (0 : TangentSpace I y)) rho t x := by
          rw [parabolicOperatorWithDrift_eq,
            parabolicOperatorWithDrift_eq,
            heatOperatorWithDrift_zero_drift,
            heatOperatorWithDrift_zero_drift,
            heatOperator_eq_laplacianAt,
            heatOperator_eq_laplacianAt,
            htime_u, hlap_u]
          ring
        have hcomp :
            parabolicOperatorWithDrift
                (I := I) (flowG (I := I) S) T
                (fun _ y => (0 : TangentSpace I y)) phi t x =
              deriv
                    DifferentialGeometry.Analysis.CutoffProfile.value
                    (u t x) *
                  parabolicOperatorWithDrift
                    (I := I) (flowG (I := I) S) T
                    (fun _ y => (0 : TangentSpace I y)) u t x -
                deriv
                    (deriv
                      DifferentialGeometry.Analysis.CutoffProfile.value)
                    (u t x) *
                  ((flowG (I := I) S).metric t).inner x
                    (gradientFun
                      (I := I) (flowG (I := I) S).metric t
                      (u t) x)
                    (gradientFun
                      (I := I) (flowG (I := I) S).metric t
                      (u t) x) := by
          simpa only [phi, gradientAt] using
            (parabolic_comp_nhds
              (I := I) (flowG (I := I) S) T
              (fun _ y => (0 : TangentSpace I y))
              (φ :=
                DifferentialGeometry.Analysis.CutoffProfile.value)
              u t x hvalue hvalue' hu_time hu_space hu_grad)
        by_cases hsmall : u t x ≤ 1
        · calc
            parabolicOperatorWithDrift
                (I := I) (flowG (I := I) S) T
                (fun _ y => (0 : TangentSpace I y)) phi t x =
                deriv
                      DifferentialGeometry.Analysis.CutoffProfile.value
                      (u t x) *
                    parabolicOperatorWithDrift
                      (I := I) (flowG (I := I) S) T
                      (fun _ y => (0 : TangentSpace I y)) u t x -
                  deriv
                      (deriv
                        DifferentialGeometry.Analysis.CutoffProfile.value)
                      (u t x) *
                    ((flowG (I := I) S).metric t).inner x
                      (gradientFun
                        (I := I) (flowG (I := I) S).metric t
                        (u t) x)
                      (gradientFun
                        (I := I) (flowG (I := I) S).metric t
                        (u t) x) := hcomp
            _ = 0 := by
              rw [
                DifferentialGeometry.Analysis.CutoffProfile.deriv_zero_of_le
                  hsmall,
                DifferentialGeometry.Analysis.CutoffProfile.deriv2_zero_of_le
                  hsmall]
              ring
            _ ≤ err n := herr_nonneg n
        · let r0 : Real :=
              (riemannianEDistOf
                (I := I) (S.base.metric t) O x).toReal
          let e : Real := Real.exp (Λ * t)
          let Pρ : Real :=
            parabolicOperatorWithDrift
              (I := I) (flowG (I := I) S) T
              (fun _ y => (0 : TangentSpace I y)) rho t x
          let G2 : Real :=
            ((flowG (I := I) S).metric t).inner x
              (gradientFun
                (I := I) (flowG (I := I) S).metric t
                (u t) x)
              (gradientFun
                (I := I) (flowG (I := I) S).metric t
                (u t) x)
          have hu_gt : 1 < u t x := lt_of_not_ge hsmall
          have hu_eq : u t x = a n * e * r0 := by
            dsimp only [u, e, r0]
            rw [hrho_eq]
            ring
          have hactive : 1 ≤ a n * e * r0 := by
            rw [← hu_eq]
            exact hu_gt.le
          have hae_pos : 0 < a n * e :=
            mul_pos (ha_pos n) (Real.exp_pos _)
          have hr0 : 0 < r0 := by
            apply (mul_pos_iff_of_pos_left hae_pos).mp
            have hprod : 0 < a n * e * r0 := by
              rw [← hu_eq]
              exact lt_trans zero_lt_one hu_gt
            simpa only [mul_assoc] using hprod
          have he_le : e ≤ U := by
            dsimp only [e, U]
            exact Real.exp_le_exp.mpr
              (mul_le_mul_of_nonneg_left ht.2 hΛ)
          have hgrad_u :
              gradientFun
                  (I := I) (flowG (I := I) S).metric t
                  (u t) x =
                a n •
                  gradientFun
                    (I := I) (flowG (I := I) S).metric t
                    (rho t) x := by
            simpa only [u, Pi.smul_apply, smul_eq_mul] using
              (gradientFun_const_smul
                (I := I) (flowG (I := I) S).metric t
                (a n) hrho_space.self_of_nhds)
          have he_sq :
              Real.exp (2 * Λ * t) = e ^ 2 := by
            dsimp only [e]
            rw [← Real.exp_nat_mul]
            congr 1
            push_cast
            ring
          have he_sq_le : Real.exp (2 * Λ * t) ≤ U ^ 2 := by
            rw [he_sq]
            exact (sq_le_sq₀ (Real.exp_pos _).le hU).2 he_le
          have hG2_nonneg : 0 ≤ G2 := by
            dsimp only [G2]
            exact
              gInner_self_nonneg
                (I := I) ((flowG (I := I) S).metric t) x _
          have hG2 : G2 ≤ a n ^ 2 * U ^ 2 := by
            dsimp only [G2]
            rw [hgrad_u,
              gInner_smul_self
                (I := I) (flowG (I := I) S).metric t x]
            exact
              (mul_le_mul_of_nonneg_left hrho_grad_sq
                (sq_nonneg (a n))).trans
                (mul_le_mul_of_nonneg_left he_sq_le
                  (sq_nonneg (a n)))
          have hrho_par' :
              -e * (2 * (d - 1) / r0 + Q) ≤ Pρ := by
            simpa only [e, r0, Q, Pρ, d, dNat, Λ] using hrho_par
          have hPpart :
              Cη * (2 * (d - 1) * U ^ 2 + U * Q + U ^ 2) ≤
                Ccut := by
            dsimp only [Ccut]
            exact
              le_add_of_nonneg_left
                (mul_nonneg hCsq (sq_nonneg U))
          calc
            parabolicOperatorWithDrift
                (I := I) (flowG (I := I) S) T
                (fun _ y => (0 : TangentSpace I y)) phi t x =
                deriv
                      DifferentialGeometry.Analysis.CutoffProfile.value
                      (u t x) *
                    (a n * Pρ) -
                  deriv
                      (deriv
                        DifferentialGeometry.Analysis.CutoffProfile.value)
                      (u t x) * G2 := by
              rw [hcomp, hpar_u]
            _ ≤ Ccut * a n := by
              exact
                cutoff_par_bound
                  (a n) U (d - 1) Q Cη Ccut e r0 Pρ
                  (deriv
                    DifferentialGeometry.Analysis.CutoffProfile.value
                    (u t x))
                  (deriv
                    (deriv
                      DifferentialGeometry.Analysis.CutoffProfile.value)
                    (u t x))
                  G2
                  (ha_pos n).le (ha_le_one n) hU hd_sub hQ hCη
                  (Real.exp_pos _).le he_le hr0 hactive hrho_par'
                  (DifferentialGeometry.Analysis.CutoffProfile.deriv_nonpos
                    (u t x))
                  (hη₁ (u t x)) (hη₂ (u t x))
                  hG2_nonneg hG2 hPpart
            _ = err n := by rfl
    exact
      { phi := phi
        eq_at := heq
        lower_nhds := hlower
        time_diff := hphi_time
        space_diff_nhds := hphi_space
        grad_diff := hphi_grad
        grad_sq_le := hquant.1
        parabolic_le := hquant.2 }

end DifferentialGeometry.PDE.RicciFlow
