import DifferentialGeometry.Analysis.ODE.ChartLocalPicardIntegral
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SolutionSpace
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.RankZeroRealization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjGalerkinLimit
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Strong scalar conjugate-heat limit from Galerkin compactness

This file identifies the all-order coefficient limit produced by
`scalar_gal_subseq` with an actual `H¹_t H⁰_x` solution.  The proof stays in
the intrinsic spectral scale: first pass the finite coordinate ODEs to the
limit, then reconstruct the vector-valued Bochner integral identity and use
the existing `timeH1` constructor.
-/

noncomputable section

open Bundle Filter MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E

/-- The Galerkin limit, continuously extended from its compact time interval. -/
noncomputable def galLimExt
    {D : RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hτ : 0 ≤ tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim) (m : Nat) :
    Real → tensorHs (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 (m : Real) :=
  Set.IccExtend hτ (galLimPath hlim m)

/-- On the Galerkin interval, `galLimExt` is the original spectral limit. -/
@[simp] theorem galLimExt_mem
    {D : RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hτ : 0 ≤ tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim) (m : Nat)
    {t : Real} (ht : t ∈ Icc (0 : Real) tau) :
    galLimExt hτ hlim m t = galLimHs hlim m t ht := by
  rw [galLimExt, Set.IccExtend_of_mem hτ _ ht]
  rfl

/-- The extended Galerkin limit is continuous at every finite Sobolev order. -/
theorem galLimExt_cont
    {D : RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hτ : 0 ≤ tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim) (m : Nat) :
    Continuous (galLimExt hτ hlim m) := by
  exact Continuous.Icc_extend' (galLimPath_cont hlim m)

/-- The `H⁰` velocity represented by the limiting conjugate-heat equation. -/
noncomputable def galLimVel
    {D : RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hτ : 0 ≤ tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim) (t : Real) :
    tensorHs (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 0 :=
  scalarScaleLap (I := I) (M := M) (S.family.metric (T : Real))
      (galLimExt hτ hlim 2 t) +
    scalarGalPert (I := I) (M := M) S T t (galLimExt hτ hlim 2 t)

/-- The limiting equation's `H⁰` velocity is continuous on the Galerkin
interval. -/
theorem galLimVel_cont
    {D : RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hτ : 0 ≤ tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim) :
    ContinuousOn (galLimVel hτ hlim) (Icc (0 : Real) tau) := by
  have hU : ContinuousOn (galLimExt hτ hlim 2) (Icc (0 : Real) tau) :=
    (galLimExt_cont hτ hlim 2).continuousOn
  exact
    ((scalarScaleLap (I := I) (M := M)
        (S.family.metric (T : Real))).continuous.comp_continuousOn hU).add
      (hlim.pert_cont.clm_apply hU)

/-- Coordinate form of the limiting velocity on the Galerkin interval. -/
theorem galLimVel_coeff
    {D : RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hτ : 0 ≤ tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim)
    (t : Real) (ht : t ∈ Icc (0 : Real) tau)
    (i : TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0) :
    (galLimVel hτ hlim t).coeff i =
      -TensorEigenIdx.lambda (I := I) (M := M) i * ulim t i +
        (scalarGalPert (I := I) (M := M) S T t
          (galLimHs hlim 2 t ht)).coeff i := by
  simp only [galLimVel, tensorHs.add_coeff, scalarScaleLap_coeff,
    galLimExt_mem hτ hlim 2 ht, galLimHs]

/-- Every limiting spectral coordinate satisfies the integral form of the
conjugate-heat equation. -/
theorem galLim_mode_ftc
    {D : RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hτ : 0 < tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim)
    (t : Real) (ht : t ∈ Icc (0 : Real) tau)
    (i : TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0) :
    ulim t i =
      tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            (S.family.metric (T : Real)) 0 0)
          (SmoothCcTensor.toL2 u0) i +
        ∫ r in (0 : Real)..t, (galLimVel hτ.le hlim r).coeff i := by
  classical
  let q : SmoothRiemannianMetric I M := S.family.metric (T : Real)
  let Fs : Nat → Finset (TensorEigenIdx (I := I) (M := M) q 0 0) :=
    fun N => eigenFinset (I := I) (M := M) q 0 0 N
  let U : Nat → Real → tensorHs (I := I) (M := M) q 0 0 2 :=
    fun N r => scalarGalVec (I := I) (M := M) q (Fs N) (V N r) 2
  let R : Nat → Real → TensorEigenIdx (I := I) (M := M) q 0 0 → Real :=
    fun N r j =>
      -TensorEigenIdx.lambda (I := I) (M := M) j * V N r j +
        (scalarGalPert (I := I) (M := M) S T r (U N r)).coeff j
  obtain ⟨B0, hB0⟩ := hlim.energy 0
  obtain ⟨B2, hB2⟩ := hlim.energy 2
  have h0mem : (0 : Real) ∈ Icc (0 : Real) tau := ⟨le_rfl, hτ.le⟩
  have hB0_nonneg : 0 ≤ B0 :=
    (galerkinEnergy_nonneg (I := I) (M := M) (Fs 0) (V 0) 0 0).trans
      (by simpa only [Fs, q, Nat.cast_zero] using hB0 0 0 h0mem)
  have hcoord_sq (N : Nat) (r : Real) (hr : r ∈ Icc (0 : Real) tau)
      (j : TensorEigenIdx (I := I) (M := M) q 0 0) :
      (V N r j) ^ 2 ≤ B0 := by
    by_cases hj : j ∈ Fs N
    · have hterm :
          tensorSobolevWeight (I := I) (M := M) j 0 * (V N r j) ^ 2 ≤
            galerkinEnergy (I := I) (M := M) (Fs N) (V N) 0 r := by
        rw [galerkinEnergy]
        exact Finset.single_le_sum (fun k _ =>
          mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) k 0)
            (sq_nonneg _)) hj
      calc
        (V N r j) ^ 2 =
            tensorSobolevWeight (I := I) (M := M) j 0 * (V N r j) ^ 2 := by
              rw [tensorSobolevWeight_zero, one_mul]
        _ ≤ galerkinEnergy (I := I) (M := M) (Fs N) (V N) 0 r := hterm
        _ ≤ B0 := by simpa only [Fs, q, Nat.cast_zero] using hB0 N r hr
    · rw [hlim.support N r j (by simpa only [Fs, q] using hj)]
      simpa only [zero_pow (by norm_num : 2 ≠ 0)] using hB0_nonneg
  have hcoord (N : Nat) (r : Real) (hr : r ∈ Icc (0 : Real) tau)
      (j : TensorEigenIdx (I := I) (M := M) q 0 0) :
      |V N r j| ≤ Real.sqrt B0 := by
    calc
      |V N r j| = Real.sqrt ((V N r j) ^ 2) :=
        (Real.sqrt_sq_eq_abs (V N r j)).symm
      _ ≤ Real.sqrt B0 := Real.sqrt_le_sqrt (hcoord_sq N r hr j)
  have hvec_norm (N : Nat) (r : Real) (hr : r ∈ Icc (0 : Real) tau) :
      ‖U N r‖ ≤ Real.sqrt B2 := by
    have hsq : ‖U N r‖ ^ 2 ≤ B2 := by
      rw [show ‖U N r‖ ^ 2 =
          ∑ j ∈ Fs N,
            tensorSobolevWeight (I := I) (M := M) j 2 * (V N r j) ^ 2 by
        exact galVec_norm_sq (I := I) (M := M) q (Fs N) (V N r) 2]
      simpa only [Fs, U, q, galerkinEnergy] using hB2 N r hr
    have hsqrt := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _)] at hsqrt
  obtain ⟨rmax, _hrmax, hpert_max⟩ :=
    isCompact_Icc.exists_isMaxOn (s := Icc (0 : Real) tau) ⟨0, h0mem⟩
      hlim.pert_cont.norm
  let Kpert : Real := ‖scalarGalPert (I := I) (M := M) S T rmax‖
  have hKpert : 0 ≤ Kpert := norm_nonneg _
  have hpert_norm (r : Real) (hr : r ∈ Icc (0 : Real) tau) :
      ‖scalarGalPert (I := I) (M := M) S T r‖ ≤ Kpert := by
    exact hpert_max hr
  have hforce (N : Nat) (r : Real) (hr : r ∈ Icc (0 : Real) tau)
      (j : TensorEigenIdx (I := I) (M := M) q 0 0) :
      |(scalarGalPert (I := I) (M := M) S T r (U N r)).coeff j| ≤
        Kpert * Real.sqrt B2 := by
    have hcoeff := abs_coeff_le_norm (I := I) (M := M) j
      (scalarGalPert (I := I) (M := M) S T r (U N r))
    have hcoeff' :
        |(scalarGalPert (I := I) (M := M) S T r (U N r)).coeff j| ≤
          ‖scalarGalPert (I := I) (M := M) S T r (U N r)‖ := by
      simpa only [tensorSobolevWeight_zero, Real.sqrt_one, inv_one, one_mul]
        using hcoeff
    calc
      |(scalarGalPert (I := I) (M := M) S T r (U N r)).coeff j|
          ≤ ‖scalarGalPert (I := I) (M := M) S T r (U N r)‖ := hcoeff'
      _ ≤ ‖scalarGalPert (I := I) (M := M) S T r‖ * ‖U N r‖ :=
        (scalarGalPert (I := I) (M := M) S T r).le_opNorm (U N r)
      _ ≤ Kpert * Real.sqrt B2 :=
        mul_le_mul (hpert_norm r hr) (hvec_norm N r hr)
          (norm_nonneg _) hKpert
  have hRcont (N : Nat)
      (j : TensorEigenIdx (I := I) (M := M) q 0 0) :
      ContinuousOn (fun r => R N r j) (Icc (0 : Real) tau) := by
    have hVcont : ContinuousOn (fun r => V N r j) (Icc (0 : Real) tau) := by
      by_cases hj : j ∈ Fs N
      · exact hlim.cont N j (by simpa only [Fs, q] using hj)
      · have hz : (fun r : Real => V N r j) = fun _ => 0 := by
          funext r
          exact hlim.support N r j (by simpa only [Fs, q] using hj)
        rw [hz]
        exact continuousOn_const
    have hUcont : ContinuousOn (U N) (Icc (0 : Real) tau) := by
      simpa only [U, Fs, q] using
        (scalarGalVec_cont (I := I) (M := M) q (Fs N) (V N)
          (fun k hk => hlim.cont N k (by simpa only [Fs, q] using hk)))
    have hPcont : ContinuousOn
        (fun r => scalarGalPert (I := I) (M := M) S T r (U N r))
        (Icc (0 : Real) tau) := hlim.pert_cont.clm_apply hUcont
    have hPc : ContinuousOn
        (fun r => (scalarGalPert (I := I) (M := M) S T r (U N r)).coeff j)
        (Icc (0 : Real) tau) :=
      (coeffCLM (I := I) (M := M) (g := q) (r := 0) (s := 0)
        (σ := (0 : Real)) j).continuous.comp_continuousOn hPcont
    have hdiag : ContinuousOn
        (fun r => -TensorEigenIdx.lambda (I := I) (M := M) j * V N r j)
        (Icc (0 : Real) tau) := continuousOn_const.mul hVcont
    simpa only [R] using hdiag.add hPc
  have hRbound (N : Nat) (r : Real) (hr : r ∈ Icc (0 : Real) tau)
      (j : TensorEigenIdx (I := I) (M := M) q 0 0) :
      ‖R N r j‖ ≤
        TensorEigenIdx.lambda (I := I) (M := M) j * Real.sqrt B0 +
          Kpert * Real.sqrt B2 := by
    have hlam : 0 ≤ TensorEigenIdx.lambda (I := I) (M := M) j :=
      tensor_lambda_nonneg (I := I) (M := M) j
    calc
      ‖R N r j‖ =
          |-TensorEigenIdx.lambda (I := I) (M := M) j * V N r j +
            (scalarGalPert (I := I) (M := M) S T r (U N r)).coeff j| := by
              simp only [Real.norm_eq_abs, R]
      _ ≤ |-TensorEigenIdx.lambda (I := I) (M := M) j * V N r j| +
            |(scalarGalPert (I := I) (M := M) S T r (U N r)).coeff j| :=
          abs_add_le _ _
      _ = TensorEigenIdx.lambda (I := I) (M := M) j * |V N r j| +
            |(scalarGalPert (I := I) (M := M) S T r (U N r)).coeff j| := by
          rw [abs_mul, abs_neg, abs_of_nonneg hlam]
      _ ≤ TensorEigenIdx.lambda (I := I) (M := M) j * Real.sqrt B0 +
            Kpert * Real.sqrt B2 :=
          add_le_add (mul_le_mul_of_nonneg_left (hcoord N r hr j) hlam)
            (hforce N r hr j)
  have hsub : Ι (0 : Real) t ⊆ Icc (0 : Real) tau := by
    intro r hr
    rw [uIoc_of_le ht.1] at hr
    exact ⟨hr.1.le, hr.2.trans ht.2⟩
  have hmeas : ∀ᶠ n in atTop,
      AEStronglyMeasurable (fun r => R (phi n) r i)
        (volume.restrict (Ι (0 : Real) t)) := by
    filter_upwards with n
    exact ((hRcont (phi n) i).mono hsub).aestronglyMeasurable measurableSet_uIoc
  have hbound : ∀ᶠ n in atTop, ∀ᵐ r ∂volume, r ∈ Ι (0 : Real) t →
      ‖R (phi n) r i‖ ≤
        TensorEigenIdx.lambda (I := I) (M := M) i * Real.sqrt B0 +
          Kpert * Real.sqrt B2 := by
    filter_upwards with n
    filter_upwards with r
    intro hr
    exact hRbound (phi n) r (hsub hr) i
  have hbound_int : IntervalIntegrable
      (fun _ : Real =>
        TensorEigenIdx.lambda (I := I) (M := M) i * Real.sqrt B0 +
          Kpert * Real.sqrt B2) volume 0 t :=
    continuousOn_const.intervalIntegrable
  have hpoint : ∀ᵐ r ∂volume, r ∈ Ι (0 : Real) t →
      Tendsto (fun n => R (phi n) r i) atTop
        (𝒩 ((galLimVel hτ.le hlim r).coeff i)) := by
    filter_upwards with r
    intro hr
    have hrIcc : r ∈ Icc (0 : Real) tau := hsub hr
    have hVlim : Tendsto (fun n => V (phi n) r i) atTop (𝒩 (ulim r i)) :=
      (hlim.conv i).tendsto_at hrIcc
    have hUlim : Tendsto (fun n => U (phi n) r) atTop
        (𝒩 (galLimHs hlim 2 r hrIcc)) := by
      simpa only [U, Fs, q] using galLim_tendsto hlim 2 r hrIcc
    have hPlim : Tendsto
        (fun n => scalarGalPert (I := I) (M := M) S T r (U (phi n) r)) atTop
        (𝒩 (scalarGalPert (I := I) (M := M) S T r
          (galLimHs hlim 2 r hrIcc))) :=
      ((scalarGalPert (I := I) (M := M) S T r).continuous.tendsto _).comp hUlim
    have hPclim : Tendsto
        (fun n => (scalarGalPert (I := I) (M := M) S T r
          (U (phi n) r)).coeff i) atTop
        (𝒩 ((scalarGalPert (I := I) (M := M) S T r
          (galLimHs hlim 2 r hrIcc)).coeff i)) :=
      ((coeffCLM (I := I) (M := M) (g := q) (r := 0) (s := 0)
        (σ := (0 : Real)) i).continuous.tendsto _).comp hPlim
    have hdiag : Tendsto
        (fun n => -TensorEigenIdx.lambda (I := I) (M := M) i * V (phi n) r i)
        atTop (𝒩 (-TensorEigenIdx.lambda (I := I) (M := M) i * ulim r i)) :=
      tendsto_const_nhds.mul hVlim
    have hsum := hdiag.add hPclim
    simpa only [R, galLimVel_coeff hτ.le hlim r hrIcc] using hsum
  have hInt : Tendsto (fun n => ∫ r in (0 : Real)..t, R (phi n) r i) atTop
      (𝒩 (∫ r in (0 : Real)..t, (galLimVel hτ.le hlim r).coeff i)) :=
    intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ : Real =>
        TensorEigenIdx.lambda (I := I) (M := M) i * Real.sqrt B0 +
          Kpert * Real.sqrt B2)
      hmeas hbound hbound_int hpoint
  have hFs : Tendsto (fun n => Fs (phi n)) atTop atTop := by
    have hbase : Tendsto Fs atTop atTop := by
      simpa only [Fs] using eigenFinset_tendsto (I := I) (M := M) q 0 0
    exact hbase.comp hlim.mono.tendsto_atTop
  have hi : ∀ᶠ n in atTop, i ∈ Fs (phi n) := by
    have hsingle : ∀ᶠ n in atTop,
        ({i} : Finset (TensorEigenIdx (I := I) (M := M) q 0 0)) ⊆ Fs (phi n) :=
      hFs.eventually_ge_atTop {i}
    filter_upwards [hsingle] with n hn
    exact hn (Finset.mem_singleton_self i)
  have hfinite : ∀ᶠ n in atTop,
      V (phi n) t i =
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) q 0 0)
            (SmoothCcTensor.toL2 u0) i +
          ∫ r in (0 : Real)..t, R (phi n) r i := by
    filter_upwards [hi] with n hin
    have hftc := ode_right_ftc
      (hlim.cont (phi n) i (by simpa only [Fs, q] using hin))
      (fun r hr => by
        simpa only [R, U, Fs, q] using
          hlim.deriv (phi n) r hr i (by simpa only [Fs, q] using hin))
      (hRcont (phi n) i) t ht
    rw [hlim.init (phi n) i (by simpa only [Fs, q] using hin)] at hftc
    simpa only [q] using hftc
  have hleft : Tendsto (fun n => V (phi n) t i) atTop (𝒩 (ulim t i)) :=
    (hlim.conv i).tendsto_at ht
  have hright : Tendsto
      (fun n =>
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) q 0 0)
            (SmoothCcTensor.toL2 u0) i +
          ∫ r in (0 : Real)..t, R (phi n) r i) atTop
      (𝒩 (tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) q 0 0)
          (SmoothCcTensor.toL2 u0) i +
        ∫ r in (0 : Real)..t, (galLimVel hτ.le hlim r).coeff i)) :=
    tendsto_const_nhds.add hInt
  have hright' : Tendsto (fun n => V (phi n) t i) atTop
      (𝒩 (tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) q 0 0)
          (SmoothCcTensor.toL2 u0) i +
        ∫ r in (0 : Real)..t, (galLimVel hτ.le hlim r).coeff i)) :=
    hright.congr' hfinite.symm
  simpa only [q] using tendsto_nhds_unique hleft hright'

/-- The limiting coefficient identities assemble into the `H⁰`-valued
fundamental theorem of calculus, with the `H²` companion retained explicitly. -/
theorem galLim_ftc
    {D : RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hτ : 0 < tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim)
    (t : Real) (ht : t ∈ Icc (0 : Real) tau) :
    tensorHsInclusion (I := I) (M := M)
        (g := S.family.metric (T : Real)) (r := 0) (s := 0)
        (show (0 : Real) ≤ 2 by norm_num) (galLimExt hτ.le hlim 2 t) =
      ccTensorToHs (I := I) (M := M)
          (S.family.metric (T : Real)) 0 0 u0 +
        ∫ r in (0 : Real)..t, galLimVel hτ.le hlim r := by
  apply tensorHs.ext
  funext i
  have h0mem : (0 : Real) ∈ Icc (0 : Real) tau := ⟨le_rfl, hτ.le⟩
  have hInt : IntervalIntegrable (galLimVel hτ.le hlim) volume 0 t :=
    ((galLimVel_cont hτ.le hlim).mono
      (uIcc_subset_Icc h0mem ht)).intervalIntegrable
  have hmap := ContinuousLinearMap.intervalIntegral_comp_comm
    (coeffCLM (I := I) (M := M) (g := S.family.metric (T : Real))
      (r := 0) (s := 0) (σ := (0 : Real)) i) hInt
  change (∫ r in (0 : Real)..t, (galLimVel hτ.le hlim r).coeff i) =
    (∫ r in (0 : Real)..t, galLimVel hτ.le hlim r).coeff i at hmap
  simp only [tensorHsInclusion_coeff_apply,
    galLimExt_mem hτ.le hlim 2 ht, galLimHs,
    tensorHs.add_coeff, ccTensorToHs_coeff]
  rw [galLim_mode_ftc hτ hlim t ht i, hmap]

/-- A Galerkin subsequential limit is a genuine `H¹_t H⁰_x` solution whose
represented path is the `H²` spectral limit included into `H⁰`. -/
theorem scalar_gal_limit
    {D : RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hτ : 0 < tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim) :
    ∃ u : MaxRegSolutionSpace (I := I) (M := M)
        (g := S.family.metric (T : Real)) (r := 0) (s := 0) 0 tau,
      timeH1.trace0 _ tau u =
          ccTensorToHs (I := I) (M := M)
            (S.family.metric (T : Real)) 0 0 u0 ∧
      (∀ t : Icc (0 : Real) tau,
        u.toFun t =
          tensorHsInclusion (I := I) (M := M)
            (g := S.family.metric (T : Real)) (r := 0) (s := 0)
            (show (0 : Real) ≤ 2 by norm_num)
            (galLimExt hτ.le hlim 2 t)) ∧
      timeH1.timeDeriv _ tau u =
        TimeSobolev.ofContinuousOn (galLimVel_cont hτ.le hlim) := by
  let q : SmoothRiemannianMetric I M := S.family.metric (T : Real)
  let v : timeL2
      (tensorHs (I := I) (M := M) q 0 0 0) tau :=
    TimeSobolev.ofContinuousOn (galLimVel_cont hτ.le hlim)
  let init : tensorHs (I := I) (M := M) q 0 0 0 :=
    ccTensorToHs (I := I) (M := M) q 0 0 u0
  let u : MaxRegSolutionSpace (I := I) (M := M)
      (g := q) (r := 0) (s := 0) 0 tau :=
    timeH1.mk init v
  refine ⟨u, ?_, ?_, ?_⟩
  · simp only [u, init, q, timeH1.trace0_mk]
  · intro t
    have h0mem : (0 : Real) ∈ Icc (0 : Real) tau := ⟨le_rfl, hτ.le⟩
    have hrep :
        (v : Real → tensorHs (I := I) (M := M) q 0 0 0) =ᵐ[timeMeasure tau]
          galLimVel hτ.le hlim := by
      simpa only [v, q] using
        (TimeSobolev.coeFn_ofContinuousOn (galLimVel_cont hτ.le hlim))
    have hrepVol : ∀ᵐ s ∂volume, s ∈ Icc (0 : Real) tau →
        v s = galLimVel hτ.le hlim s :=
      (ae_restrict_iff' measurableSet_Icc).1 hrep
    have hintEq :
        (∫ s in (0 : Real)..(t : Real), v s) =
          ∫ s in (0 : Real)..(t : Real), galLimVel hτ.le hlim s := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hrepVol] with s hs hsI
      exact hs ((Set.uIoc_subset_uIcc).trans
        (uIcc_subset_Icc h0mem t.2) hsI)
    simp only [u, timeH1.toFun_apply, timeH1.init_mk,
      timeH1.deriv_mk]
    rw [hintEq]
    simpa only [init, q] using (galLim_ftc hτ hlim t t.2).symm
  · simp only [u, v, q, timeH1.timeDeriv_mk]

end DifferentialGeometry.PDE.RicciFlow.Entropy
