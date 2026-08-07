import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.ScalarNonautExact
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.ScalarWeyl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjGalerkinClassical
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjPotentialSpan
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

/-!
# Exact-interval scalar Galerkin reconstruction

This file upgrades a scalar Galerkin subsequence on a caller-selected regular
interval without choosing a second, shorter lifespan.
-/

noncomputable section

open Bundle Filter MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal BigOperators Interval

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization

open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E

/-- On a prescribed regular Galerkin interval, the limiting conjugate-heat
velocity has a continuous lift to every natural Sobolev order. -/
theorem galVel_lift_on
    {D : RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hS : IsSolutionOn (I := I) S) (hτ : 0 < tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim)
    (hreg : ∀ s ∈ Icc (0 : Real) tau, (T : Real) - s ∈ D.regular)
    (hcore : ∀ s ∈ Icc (0 : Real) tau,
      ∀ v : ScalarH2Core (I := I) (M := M) (S.family.metric (T : Real)),
        tensorHsZeroEquivL2 (I := I) (M := M)
            (tensorResolventL2_isCompactOperator
              (I := I) (M := M) (S.family.metric (T : Real)) 0 0)
            (lapDiffA20 (I := I) (M := M) S.family T s v.1) =
          lapDiffCore (I := I) (M := M) (S.family.metric (T : Real))
            (S.family.metric ((T : Real) - s)) v) :
    ∀ m : Nat, ∃ w : Icc (0 : Real) tau →
        tensorHs (I := I) (M := M)
          (S.family.metric (T : Real)) 0 0 (m : Real),
      Continuous w ∧
        (∀ t, tensorHsInclusion (I := I) (M := M)
            (g := S.family.metric (T : Real)) (r := 0) (s := 0)
            (by positivity : (0 : Real) ≤ (m : Real)) (w t) =
          galLimVel hτ.le hlim (t : Real)) ∧
        ∀ t, w t = galLimVelCan hτ.le hlim m (t : Real) := by
  classical
  have hnorm :=
    lapHs_norm_on (I := I) (M := M) S.family hS.smoothMetric T hreg
  have hEq :=
    lapHs_A20_on (I := I) (M := M) S.family T hcore
  let q : SmoothRiemannianMetric I M := S.family.metric (T : Real)
  let K : Set Real := Icc (0 : Real) tau
  let R : Set Real := {s : Real | (T : Real) - s ∈ D.regular}
  let zeta : Real → C^∞⟮I, M; Real⟯ := fun s =>
    conjCoeff (I := I) (M := M) S ((T : Real) - s)
  have hK : IsCompact K := by
    simpa only [K] using isCompact_Icc
  have hKR : K ⊆ R := by
    intro s hs
    simpa only [K, R] using hreg s hs
  have hzeta : ContMDiffOn (I.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞
      (fun p : M × Real => (zeta p.2 : M → Real) p.1)
      ((Set.univ : Set M) ×ˢ R) := by
    simpa only [zeta, R, conjCoeffRev] using
      conjCoeff_rev (I := I) S hS T
  intro m
  obtain ⟨B, hB⟩ := hlim.lim_mass (m + 1 + 2)
  obtain ⟨C₂, hC₂_nn, hC₂⟩ := hnorm (m + 1)
  obtain ⟨C₁, hC₁_nn, hC₁⟩ :=
    scalarPotHs_unif (I := I) (M := M) q zeta
      (K := K) (S := R) hK hKR hzeta (m + 1)
  have hfac : 0 ≤ 1 + C₂ + C₁ := by positivity
  let C : Real := (1 + C₂ + C₁) * Real.sqrt B
  have hC_nn : 0 ≤ C := by
    exact mul_nonneg hfac (Real.sqrt_nonneg B)
  let W : Icc (0 : Real) tau →
      tensorHs (I := I) (M := M) q 0 0 ((m + 1 : Nat) : Real) :=
    fun t => galLimVelHs hτ.le hlim (m + 1) t
  have hW_bound (t : Icc (0 : Real) tau) : ‖W t‖ ≤ C := by
    let U : tensorHs (I := I) (M := M) q 0 0
        (((m + 1 : Nat) : Real) + 2) :=
      tensorHs.castEquiv (I := I) (M := M)
        (g := q) (r := 0) (s := 0)
        (by norm_num : ((m + 1 + 2 : Nat) : Real) =
          ((m + 1 : Nat) : Real) + 2)
        (galLimExt hτ.le hlim (m + 1 + 2) t)
    have hincU : ((m + 1 : Nat) : Real) ≤
        ((m + 1 : Nat) : Real) + 2 := by norm_num
    let Um : tensorHs (I := I) (M := M) q 0 0
        ((m + 1 : Nat) : Real) :=
      tensorHsInclusion (I := I) (M := M)
        (g := q) (r := 0) (s := 0) hincU U
    have hExtSq : ‖galLimExt hτ.le hlim (m + 1 + 2) t‖ ^ 2 ≤ B := by
      rw [galLimExt_mem hτ.le hlim (m + 1 + 2) t.2,
        tensorHs.norm_sq_eq_tsum]
      simpa only [galLimHs] using (hB t t.2).2
    have hUnorm : ‖U‖ = ‖galLimExt hτ.le hlim (m + 1 + 2) t‖ := by
      dsimp only [U]
      exact (tensorHs.castEquiv (I := I) (M := M)
        (g := q) (r := 0) (s := 0)
        (by norm_num : ((m + 1 + 2 : Nat) : Real) =
          ((m + 1 : Nat) : Real) + 2)).norm_map _
    have hUSq : ‖U‖ ^ 2 ≤ B := by
      rw [hUnorm]
      exact hExtSq
    have hU : ‖U‖ ≤ Real.sqrt B := by
      have hsqrt := Real.sqrt_le_sqrt hUSq
      rwa [Real.sqrt_sq (norm_nonneg _)] at hsqrt
    have hUm : ‖Um‖ ≤ ‖U‖ := by
      dsimp only [Um]
      exact tensorHsInclusion_norm_le (I := I) (M := M) hincU U
    have hLap :
        ‖tensorScaleLaplacian (I := I) (M := M)
          (g := q) (r := 0) (s := 0) ((m + 1 : Nat) : Real) U‖ ≤ ‖U‖ := by
      simpa only [tensorScaleLaplacian_apply] using
        norm_scaleLaplacianFun_le (I := I) (M := M) U
    have hDiff :
        ‖lapDiffHs (I := I) (M := M) q
          (S.family.metric ((T : Real) - t)) (m + 1) U‖ ≤ C₂ * ‖U‖ := by
      calc
        _ ≤ ‖lapDiffHs (I := I) (M := M) q
              (S.family.metric ((T : Real) - t)) (m + 1)‖ * ‖U‖ :=
          (lapDiffHs (I := I) (M := M) q
            (S.family.metric ((T : Real) - t)) (m + 1)).le_opNorm U
        _ ≤ C₂ * ‖U‖ :=
          mul_le_mul_of_nonneg_right (hC₂ t t.2) (norm_nonneg U)
    have hPot :
        ‖scalarPotHs (I := I) (M := M) q (zeta t) (m + 1) Um‖ ≤
          C₁ * ‖Um‖ := by
      calc
        _ ≤ ‖scalarPotHs (I := I) (M := M) q
              (zeta t) (m + 1)‖ * ‖Um‖ :=
          (scalarPotHs (I := I) (M := M) q
            (zeta t) (m + 1)).le_opNorm Um
        _ ≤ C₁ * ‖Um‖ :=
          mul_le_mul_of_nonneg_right
            (hC₁ t (by simpa only [K] using t.2)) (norm_nonneg Um)
    change ‖
      tensorScaleLaplacian (I := I) (M := M)
          (g := q) (r := 0) (s := 0) ((m + 1 : Nat) : Real) U +
        lapDiffHs (I := I) (M := M) q
          (S.family.metric ((T : Real) - t)) (m + 1) U +
        scalarPotHs (I := I) (M := M) q (zeta t) (m + 1) Um‖ ≤ C
    calc
      _ ≤ ‖tensorScaleLaplacian (I := I) (M := M)
              (g := q) (r := 0) (s := 0) ((m + 1 : Nat) : Real) U +
            lapDiffHs (I := I) (M := M) q
              (S.family.metric ((T : Real) - t)) (m + 1) U‖ +
          ‖scalarPotHs (I := I) (M := M) q (zeta t) (m + 1) Um‖ :=
        norm_add_le _ _
      _ ≤ (‖tensorScaleLaplacian (I := I) (M := M)
              (g := q) (r := 0) (s := 0) ((m + 1 : Nat) : Real) U‖ +
            ‖lapDiffHs (I := I) (M := M) q
              (S.family.metric ((T : Real) - t)) (m + 1) U‖) +
          ‖scalarPotHs (I := I) (M := M) q (zeta t) (m + 1) Um‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ ≤ (‖U‖ + C₂ * ‖U‖) + C₁ * ‖Um‖ :=
        add_le_add (add_le_add hLap hDiff) hPot
      _ ≤ (‖U‖ + C₂ * ‖U‖) + C₁ * ‖U‖ :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hUm hC₁_nn)
      _ = (1 + C₂ + C₁) * ‖U‖ := by ring
      _ ≤ (1 + C₂ + C₁) * Real.sqrt B :=
        mul_le_mul_of_nonneg_left hU hfac
      _ = C := rfl
  have hW0 (t : Icc (0 : Real) tau) :
      tensorHsInclusion (I := I) (M := M)
          (g := q) (r := 0) (s := 0)
          (by positivity : (0 : Real) ≤ ((m + 1 : Nat) : Real)) (W t) =
        galLimVel hτ.le hlim (t : Real) := by
    have hk : (1 : Real) ≤ ((m + 1 : Nat) : Real) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
    have h0k : (0 : Real) ≤ ((m + 1 : Nat) : Real) :=
      zero_le_one.trans hk
    have hk2 : ((m + 1 : Nat) : Real) ≤
        ((m + 1 : Nat) : Real) + 2 := by norm_num
    have h2k2 : (2 : Real) ≤ ((m + 1 : Nat) : Real) + 2 := by
      linarith
    have h12 : (1 : Real) ≤ 2 := by norm_num
    have h02k : ((0 : Nat) : Real) + 2 ≤
        ((m + 1 : Nat) : Real) + 2 := by
      simpa only [Nat.cast_zero, zero_add] using h2k2
    have h20 : (2 : Real) = ((0 : Nat) : Real) + 2 := by norm_num
    have hzero : ((0 : Nat) : Real) = 0 := by norm_num
    let U₂ : tensorHs (I := I) (M := M) q 0 0 2 :=
      galLimExt hτ.le hlim 2 t
    let U : tensorHs (I := I) (M := M) q 0 0
        (((m + 1 : Nat) : Real) + 2) :=
      tensorHs.castEquiv (I := I) (M := M)
        (g := q) (r := 0) (s := 0)
        (by norm_num : ((m + 1 + 2 : Nat) : Real) =
          ((m + 1 : Nat) : Real) + 2)
        (galLimExt hτ.le hlim (m + 1 + 2) t)
    let Um : tensorHs (I := I) (M := M) q 0 0
        ((m + 1 : Nat) : Real) :=
      tensorHsInclusion (I := I) (M := M)
        (g := q) (r := 0) (s := 0) hk2 U
    have hU2 :
        tensorHsInclusion (I := I) (M := M)
            (g := q) (r := 0) (s := 0) h2k2 U = U₂ := by
      apply tensorHs.ext
      funext i
      have hi := congrArg
        (fun v : tensorHs (I := I) (M := M) q 0 0 (2 : Real) =>
          v.coeff i)
        (galLimExt_inc hτ.le hlim
          (show 2 ≤ m + 1 + 2 by omega) t.2)
      simpa only [U, U₂, tensorHsInclusion_coeff_apply,
        tensorHs.castEquiv_coeff] using hi
    have hUm1 :
        tensorHsInclusion (I := I) (M := M)
            (g := q) (r := 0) (s := 0) hk Um =
          tensorHsInclusion (I := I) (M := M)
            (g := q) (r := 0) (s := 0) h12 U₂ := by
      apply tensorHs.ext
      funext i
      have hi := congrArg
        (fun v : tensorHs (I := I) (M := M) q 0 0 (2 : Real) =>
          v.coeff i) hU2
      simpa only [Um, tensorHsInclusion_coeff_apply] using hi
    have hLap :
        tensorHsInclusion (I := I) (M := M)
            (g := q) (r := 0) (s := 0) h0k
            (tensorScaleLaplacian (I := I) (M := M)
              (g := q) (r := 0) (s := 0)
              ((m + 1 : Nat) : Real) U) =
          scalarScaleLap (I := I) (M := M) q U₂ := by
      apply tensorHs.ext
      funext i
      have hi := congrArg
        (fun v : tensorHs (I := I) (M := M) q 0 0 (2 : Real) =>
          v.coeff i) hU2
      simp only [tensorHsInclusion_coeff_apply] at hi
      simp only [tensorHsInclusion_coeff_apply,
        tensorScaleLaplacian_coeff, scalarScaleLap_coeff]
      rw [hi]
    have hU0 :
        tensorHsInclusion (I := I) (M := M)
            (g := q) (r := 0) (s := 0) h02k U =
          tensorHs.castEquiv (I := I) (M := M)
            (g := q) (r := 0) (s := 0) h20 U₂ := by
      apply tensorHs.ext
      funext i
      have hi := congrArg
        (fun v : tensorHs (I := I) (M := M) q 0 0 (2 : Real) =>
          v.coeff i) hU2
      simpa only [tensorHsInclusion_coeff_apply,
        tensorHs.castEquiv_coeff] using hi
    have hinc0 := lapHs_inc (I := I) (M := M) q
      (S.family.metric ((T : Real) - t)) (Nat.zero_le (m + 1))
    have happ := congrArg (fun L => L U) hinc0
    simp only [ContinuousLinearMap.comp_apply] at happ
    have hleft :
        tensorHsInclusion (I := I) (M := M)
            (g := q) (r := 0) (s := 0) h0k
            (lapDiffHs (I := I) (M := M) q
              (S.family.metric ((T : Real) - t)) (m + 1) U) =
          tensorHs.castEquiv (I := I) (M := M)
            (g := q) (r := 0) (s := 0) hzero
            (lapDiffHs (I := I) (M := M) q
              (S.family.metric ((T : Real) - t)) 0
              (tensorHsInclusion (I := I) (M := M)
                (g := q) (r := 0) (s := 0) h02k U)) := by
      apply tensorHs.ext
      funext i
      have hi := congrArg
        (fun v : tensorHs (I := I) (M := M) q 0 0
          ((0 : Nat) : Real) => v.coeff i) happ
      simpa only [tensorHsInclusion_coeff_apply,
        tensorHs.castEquiv_coeff] using hi
    have hDiff :
        tensorHsInclusion (I := I) (M := M)
            (g := q) (r := 0) (s := 0) h0k
            (lapDiffHs (I := I) (M := M) q
              (S.family.metric ((T : Real) - t)) (m + 1) U) =
          lapDiffA20 (I := I) (M := M) S.family T t U₂ := by
      calc
        _ = tensorHs.castEquiv (I := I) (M := M)
            (g := q) (r := 0) (s := 0) hzero
            (lapDiffHs (I := I) (M := M) q
              (S.family.metric ((T : Real) - t)) 0
              (tensorHsInclusion (I := I) (M := M)
                (g := q) (r := 0) (s := 0) h02k U)) := hleft
        _ = tensorHs.castEquiv (I := I) (M := M)
            (g := q) (r := 0) (s := 0) hzero
            (lapDiffHs (I := I) (M := M) q
              (S.family.metric ((T : Real) - t)) 0
              (tensorHs.castEquiv (I := I) (M := M)
                (g := q) (r := 0) (s := 0) h20 U₂)) := by rw [hU0]
        _ = lapDiffA20 (I := I) (M := M) S.family T t U₂ :=
          hEq t t.2 U₂
    have hPot :
        tensorHsInclusion (I := I) (M := M)
            (g := q) (r := 0) (s := 0) h0k
            (scalarPotHs (I := I) (M := M) q (zeta t) (m + 1) Um) =
          scalarPotH0 (I := I) (M := M) q (zeta t)
            (tensorHsInclusion (I := I) (M := M)
              (g := q) (r := 0) (s := 0) h12 U₂) := by
      calc
        _ = scalarPotH0 (I := I) (M := M) q (zeta t)
            (tensorHsInclusion (I := I) (M := M)
              (g := q) (r := 0) (s := 0) hk Um) :=
          scalarPotHs_inc (I := I) (M := M) q (zeta t)
            (m + 1) hk Um
        _ = _ := by rw [hUm1]
    change tensorHsInclusion (I := I) (M := M)
      (g := q) (r := 0) (s := 0) h0k
      (tensorScaleLaplacian (I := I) (M := M)
          (g := q) (r := 0) (s := 0) ((m + 1 : Nat) : Real) U +
        lapDiffHs (I := I) (M := M) q
          (S.family.metric ((T : Real) - t)) (m + 1) U +
        scalarPotHs (I := I) (M := M) q (zeta t) (m + 1) Um) =
      galLimVel hτ.le hlim t
    rw [map_add, map_add, hLap, hDiff, hPot]
    simp only [galLimVel, scalarGalPert, conjA1, zeta, q,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]
    rw [add_assoc]
  have hm : (m : Real) < ((m + 1 : Nat) : Real) := by
    exact_mod_cast Nat.lt_succ_self m
  have hvelCoeffOn
      (i : TensorEigenIdx (I := I) (M := M) q 0 0) :
      ContinuousOn
        (fun s : Real => (galLimVel hτ.le hlim s).coeff i)
        (Icc (0 : Real) tau) := by
    exact (coeffCLM (I := I) (M := M) (g := q) (r := 0) (s := 0)
      (σ := 0) i).continuous.comp_continuousOn
        (galLimVel_cont hτ.le hlim)
  have hvelCoeff
      (i : TensorEigenIdx (I := I) (M := M) q 0 0) :
      Continuous (fun t : Icc (0 : Real) tau =>
        (galLimVel hτ.le hlim (t : Real)).coeff i) :=
    (hvelCoeffOn i).restrict
  have hcoeff
      (i : TensorEigenIdx (I := I) (M := M) q 0 0) :
      Continuous (fun t : Icc (0 : Real) tau => (W t).coeff i) := by
    refine (hvelCoeff i).congr ?_
    intro t
    have hi := congrArg
      (fun v : tensorHs (I := I) (M := M) q 0 0 0 => v.coeff i)
      (hW0 t)
    simpa only [tensorHsInclusion_coeff_apply] using hi.symm
  have hdown := cont_of_coeff (I := I) (M := M) hm W hC_nn hW_bound hcoeff
  let w : Icc (0 : Real) tau →
      tensorHs (I := I) (M := M) q 0 0 (m : Real) := fun t =>
    tensorHsInclusion (I := I) (M := M)
      (g := q) (r := 0) (s := 0) hm.le (W t)
  refine ⟨w, ?_, ?_, ?_⟩
  · simpa only [w] using hdown
  · intro t
    apply tensorHs.ext
    funext i
    have hi := congrArg
      (fun v : tensorHs (I := I) (M := M) q 0 0 0 => v.coeff i)
      (hW0 t)
    simpa only [w, tensorHsInclusion_coeff_apply] using hi
  · intro t
    simp only [w, W, galLimVelCan, q]

/-- On a prescribed regular interval, every all-order Galerkin limit has its
canonical all-scale velocity as a strong derivative. -/
theorem galExt_deriv_on
    {D : RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hS : IsSolutionOn (I := I) S) (hτ : 0 < tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim)
    (hreg : ∀ s ∈ Icc (0 : Real) tau, (T : Real) - s ∈ D.regular)
    (hcore : ∀ s ∈ Icc (0 : Real) tau,
      ∀ v : ScalarH2Core (I := I) (M := M) (S.family.metric (T : Real)),
        tensorHsZeroEquivL2 (I := I) (M := M)
            (tensorResolventL2_isCompactOperator
              (I := I) (M := M) (S.family.metric (T : Real)) 0 0)
            (lapDiffA20 (I := I) (M := M) S.family T s v.1) =
          lapDiffCore (I := I) (M := M) (S.family.metric (T : Real))
            (S.family.metric ((T : Real) - s)) v) :
    ∀ m : Nat, ∃ w : Real →
        tensorHs (I := I) (M := M)
          (S.family.metric (T : Real)) 0 0 (m : Real),
      Continuous w ∧
        (∀ t ∈ Icc (0 : Real) tau,
          tensorHsInclusion (I := I) (M := M)
              (g := S.family.metric (T : Real)) (r := 0) (s := 0)
              (by positivity : (0 : Real) ≤ (m : Real)) (w t) =
            galLimVel hτ.le hlim t) ∧
        (∀ t ∈ Icc (0 : Real) tau,
          w t = galLimVelCan hτ.le hlim m t) ∧
        ∀ t ∈ Ioo (0 : Real) tau,
          HasDerivAt (galLimExt hτ.le hlim m) (w t) t := by
  classical
  have hlift := galVel_lift_on (I := I) (M := M)
    hS hτ hlim hreg hcore
  intro m
  obtain ⟨w₀, hw₀, hw₀_eq, hw₀_can⟩ := hlift m
  let w : Real → tensorHs (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 (m : Real) :=
    Set.IccExtend hτ.le w₀
  have hw : Continuous w := by
    simpa only [w] using Continuous.Icc_extend' hw₀
  have hw_mem (t : Real) (ht : t ∈ Icc (0 : Real) tau) :
      w t = w₀ ⟨t, ht⟩ := by
    simpa only [w] using Set.IccExtend_of_mem hτ.le w₀ ht
  have hw_eq (t : Real) (ht : t ∈ Icc (0 : Real) tau) :
      tensorHsInclusion (I := I) (M := M)
          (g := S.family.metric (T : Real)) (r := 0) (s := 0)
          (by positivity : (0 : Real) ≤ (m : Real)) (w t) =
        galLimVel hτ.le hlim t := by
    rw [hw_mem t ht]
    exact hw₀_eq ⟨t, ht⟩
  have hw_can (t : Real) (ht : t ∈ Icc (0 : Real) tau) :
      w t = galLimVelCan hτ.le hlim m t := by
    rw [hw_mem t ht]
    exact hw₀_can ⟨t, ht⟩
  refine ⟨w, hw, hw_eq, hw_can, ?_⟩
  have h0 : (0 : Real) ∈ Icc (0 : Real) tau := ⟨le_rfl, hτ.le⟩
  have hftc (r : Real) (hr : r ∈ Icc (0 : Real) tau) :
      galLimExt hτ.le hlim m r =
        galLimExt hτ.le hlim m 0 + ∫ s in (0 : Real)..r, w s := by
    apply tensorHs.ext
    funext i
    have hInt : IntervalIntegrable w volume 0 r :=
      hw.intervalIntegrable _ _
    have hmap := ContinuousLinearMap.intervalIntegral_comp_comm
      (coeffCLM (I := I) (M := M)
        (g := S.family.metric (T : Real)) (r := 0) (s := 0)
        (σ := (m : Real)) i) hInt
    change (∫ s in (0 : Real)..r, (w s).coeff i) =
      (∫ s in (0 : Real)..r, w s).coeff i at hmap
    have hIntEq :
        (∫ s in (0 : Real)..r, (w s).coeff i) =
          ∫ s in (0 : Real)..r, (galLimVel hτ.le hlim s).coeff i := by
      refine intervalIntegral.integral_congr (fun s hs => ?_)
      have hsI : s ∈ Icc (0 : Real) tau :=
        (uIcc_subset_Icc h0 hr) hs
      have hi := congrArg
        (fun v : tensorHs (I := I) (M := M)
          (S.family.metric (T : Real)) 0 0 0 => v.coeff i)
        (hw_eq s hsI)
      simpa only [tensorHsInclusion_coeff_apply] using hi
    simp only [galLimExt_mem hτ.le hlim m hr,
      galLimExt_mem hτ.le hlim m h0, galLimHs, tensorHs.add_coeff]
    rw [galLim_mode_ftc hτ hlim r hr i, hlim.lim_init i, ← hmap, hIntEq]
  intro t ht
  have hwIoo : ContinuousOn w (Ioo (0 : Real) tau) := hw.continuousOn
  have hwAt : ContinuousAt w t := hw.continuousAt
  have hwInt : IntervalIntegrable w volume 0 t :=
    hw.intervalIntegrable _ _
  have hwMeas : StronglyMeasurableAtFilter w (nhds t) volume :=
    hwIoo.stronglyMeasurableAtFilter isOpen_Ioo t ht
  have hprim : HasDerivAt
      (fun r : Real => ∫ s in (0 : Real)..r, w s) (w t) t :=
    intervalIntegral.integral_hasDerivAt_right hwInt hwMeas hwAt
  have hsum : HasDerivAt
      (fun r : Real => galLimExt hτ.le hlim m 0 +
        ∫ s in (0 : Real)..r, w s) (w t) t :=
    hprim.const_add (galLimExt hτ.le hlim m 0)
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [Icc_mem_nhds ht.1 ht.2] with r hr
  exact hftc r hr

/-- On a prescribed regular interval, the derivative of every all-order
Galerkin limit is its canonical all-scale velocity. -/
theorem galExt_ode_on
    {D : RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hS : IsSolutionOn (I := I) S) (hτ : 0 < tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim)
    (hreg : ∀ s ∈ Icc (0 : Real) tau, (T : Real) - s ∈ D.regular)
    (hcore : ∀ s ∈ Icc (0 : Real) tau,
      ∀ v : ScalarH2Core (I := I) (M := M) (S.family.metric (T : Real)),
        tensorHsZeroEquivL2 (I := I) (M := M)
            (tensorResolventL2_isCompactOperator
              (I := I) (M := M) (S.family.metric (T : Real)) 0 0)
            (lapDiffA20 (I := I) (M := M) S.family T s v.1) =
          lapDiffCore (I := I) (M := M) (S.family.metric (T : Real))
            (S.family.metric ((T : Real) - s)) v) :
    ∀ m : Nat, ∀ t ∈ Ioo (0 : Real) tau,
      HasDerivAt (galLimExt hτ.le hlim m)
        (galLimVelCan hτ.le hlim m t) t := by
  have hd := galExt_deriv_on (I := I) (M := M)
    hS hτ hlim hreg hcore
  intro m t ht
  obtain ⟨w, _hw, _hw0, hwCan, hwDeriv⟩ := hd m
  have h := hwDeriv t ht
  rw [hwCan t ⟨ht.1.le, ht.2.le⟩] at h
  exact h

/-- On the full positive interior of a prescribed regular interval, the
Galerkin limit is a smooth time path in every natural Sobolev order. -/
theorem galExt_smooth_on
    {D : RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hS : IsSolutionOn (I := I) S) (hτ : 0 < tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim)
    (hreg : ∀ s ∈ Icc (0 : Real) tau, (T : Real) - s ∈ D.regular)
    (hcore : ∀ s ∈ Icc (0 : Real) tau,
      ∀ v : ScalarH2Core (I := I) (M := M) (S.family.metric (T : Real)),
        tensorHsZeroEquivL2 (I := I) (M := M)
            (tensorResolventL2_isCompactOperator
              (I := I) (M := M) (S.family.metric (T : Real)) 0 0)
            (lapDiffA20 (I := I) (M := M) S.family T s v.1) =
          lapDiffCore (I := I) (M := M) (S.family.metric (T : Real))
            (S.family.metric ((T : Real) - s)) v) :
    ∀ m : Nat, ContDiffOn Real ∞
      (galLimExt hτ.le hlim m) (Ioo (0 : Real) tau) := by
  classical
  have hode := galExt_ode_on (I := I) (M := M)
    hS hτ hlim hreg hcore
  let q : SmoothRiemannianMetric I M := S.family.metric (T : Real)
  let zeta : Real → C^∞⟮I, M; Real⟯ := fun s =>
    conjCoeff (I := I) (M := M) S ((T : Real) - s)
  have hback : Ioo (0 : Real) tau ⊆
      {s : Real | (T : Real) - s ∈ D.regular} := by
    intro s hs
    exact hreg s ⟨hs.1.le, hs.2.le⟩
  have hzeta : ContMDiffOn (I.prod 𝓘(Real, Real)) 𝓘(Real, Real) ∞
      (fun p : M × Real => (zeta p.2 : M → Real) p.1)
      ((Set.univ : Set M) ×ˢ Ioo (0 : Real) tau) := by
    simpa only [zeta, conjCoeffRev] using
      (conjCoeff_rev (I := I) S hS T).mono
        (Set.prod_mono Set.Subset.rfl hback)
  have hfin : ∀ k : Nat, ∀ m : Nat, ContDiffOn Real k
      (galLimExt hτ.le hlim m) (Ioo (0 : Real) tau) := by
    intro k
    induction k with
    | zero =>
        intro m
        apply contDiffOn_zero.mpr
        exact (galLimExt_cont hτ.le hlim m).continuousOn
    | succ k ih =>
        have hvel (m : Nat) : ContDiffOn Real k
            (galLimVelCan hτ.le hlim m) (Ioo (0 : Real) tau) := by
          let e := tensorHs.castEquiv (I := I) (M := M)
            (g := q) (r := 0) (s := 0)
            (by norm_num : (((m + 1) + 2 : Nat) : Real) =
              ((m + 1 : Nat) : Real) + 2)
          let U : Real → tensorHs (I := I) (M := M) q 0 0
              (((m + 1 : Nat) : Real) + 2) := fun t =>
            e (galLimExt hτ.le hlim ((m + 1) + 2) t)
          have hU : ContDiffOn Real k U (Ioo (0 : Real) tau) := by
            simpa only [U, Function.comp_apply] using
              e.contDiff.comp_contDiffOn (ih ((m + 1) + 2))
          let Jm := tensorHsInclusion (I := I) (M := M)
            (g := q) (r := 0) (s := 0)
            (by norm_num : ((m + 1 : Nat) : Real) ≤
              ((m + 1 : Nat) : Real) + 2)
          let Um : Real → tensorHs (I := I) (M := M) q 0 0
              ((m + 1 : Nat) : Real) := fun t => Jm (U t)
          have hUm : ContDiffOn Real k Um (Ioo (0 : Real) tau) := by
            simpa only [Um, Function.comp_apply] using
              Jm.contDiff.comp_contDiffOn hU
          have hfixed : ContDiffOn Real k
              (fun t => tensorScaleLaplacian (I := I) (M := M)
                (g := q) (r := 0) (s := 0) ((m + 1 : Nat) : Real) (U t))
              (Ioo (0 : Real) tau) := by
            simpa only [Function.comp_apply] using
              (tensorScaleLaplacian (I := I) (M := M)
                (g := q) (r := 0) (s := 0)
                ((m + 1 : Nat) : Real)).contDiff.comp_contDiffOn hU
          have hdiff : ContDiffOn Real k
              (fun t => lapDiffHs (I := I) (M := M) q
                (S.family.metric ((T : Real) - t)) (m + 1) (U t))
              (Ioo (0 : Real) tau) := by
            simpa only [q] using
              lapHs_dyn_on (I := I) (M := M) S.family hS.smoothMetric T
                hreg (m + 1) k U hU
          have hpot : ContDiffOn Real k
              (fun t => scalarPotHs (I := I) (M := M) q
                (zeta t) (m + 1) (Um t))
              (Ioo (0 : Real) tau) :=
            scalarPot_dyn_fin (I := I) (M := M) q zeta isOpen_Ioo hzeta
              (m + 1) k Um hUm
          have hvhs : ContDiffOn Real k
              (galLimVelHs hτ.le hlim (m + 1)) (Ioo (0 : Real) tau) := by
            simpa only [galLimVelHs, q, e, U, Jm, Um, zeta] using
              (hfixed.add hdiff).add hpot
          let Jvel := tensorHsInclusion (I := I) (M := M)
            (g := q) (r := 0) (s := 0)
            (by exact_mod_cast Nat.le_succ m :
              (m : Real) ≤ ((m + 1 : Nat) : Real))
          have hcan : ContDiffOn Real k
              (fun t => Jvel (galLimVelHs hτ.le hlim (m + 1) t))
              (Ioo (0 : Real) tau) := by
            simpa only [Function.comp_apply] using
              Jvel.contDiff.comp_contDiffOn hvhs
          simpa only [galLimVelCan, q, Jvel] using hcan
        intro m
        have hdiff : DifferentiableOn Real (galLimExt hτ.le hlim m)
            (Ioo (0 : Real) tau) := by
          intro t ht
          exact (hode m t ht).differentiableAt.differentiableWithinAt
        have hderiv_cd : ContDiffOn Real k
            (deriv (galLimExt hτ.le hlim m)) (Ioo (0 : Real) tau) := by
          refine (hvel m).congr ?_
          intro t ht
          exact (hode m t ht).deriv
        simp only [Nat.cast_add, Nat.cast_one]
        rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
        refine ⟨hdiff, ?_, hderiv_cd⟩
        intro hk
        norm_num at hk
  intro m
  rw [contDiffOn_infty]
  intro k
  exact hfin k m

/-- On every compact subinterval of a prescribed smooth interior, all time
jets of the Galerkin coefficients have summable spectral majorants. -/
theorem galJet_mass_on
    {D : RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hS : IsSolutionOn (I := I) S) (hτ : 0 < tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim)
    (hreg : ∀ s ∈ Icc (0 : Real) tau, (T : Real) - s ∈ D.regular)
    (hcore : ∀ s ∈ Icc (0 : Real) tau,
      ∀ v : ScalarH2Core (I := I) (M := M) (S.family.metric (T : Real)),
        tensorHsZeroEquivL2 (I := I) (M := M)
            (tensorResolventL2_isCompactOperator
              (I := I) (M := M) (S.family.metric (T : Real)) 0 0)
            (lapDiffA20 (I := I) (M := M) S.family T s v.1) =
          lapDiffCore (I := I) (M := M) (S.family.metric (T : Real))
            (S.family.metric ((T : Real) - s)) v) :
    ∀ ⦃a b : Real⦄, 0 < a → a ≤ b → b < tau →
      (∀ i, ContDiffOn Real ∞ (fun t => ulim t i) (Icc a b)) ∧
      ∀ (j m : Nat),
        ∃ B : TensorEigenIdx (I := I) (M := M)
            (S.family.metric (T : Real)) 0 0 → Real,
          Summable B ∧
          ∀ i, ∀ t ∈ Icc a b,
            tensorSobolevWeight (I := I) (M := M) i (m : Real) *
              (iteratedDeriv j (fun s => ulim s i) t) ^ 2 ≤ B i := by
  classical
  have hsmooth := galExt_smooth_on (I := I) (M := M)
    hS hτ hlim hreg hcore
  let q : SmoothRiemannianMetric I M := S.family.metric (T : Real)
  have htail : EigenvalueTailSummable (I := I) (M := M) q 0 0 :=
    scalar_eigen_tail (I := I) (M := M) q
  obtain ⟨p, _hp, hpsum⟩ := htail
  intro a b ha hab hb
  have hKsub : Icc a b ⊆ Ioo (0 : Real) tau := by
    intro t ht
    exact ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩
  have hcoeff_smooth (i : TensorEigenIdx (I := I) (M := M) q 0 0) :
      ContDiffOn Real ∞ (fun t => ulim t i) (Icc a b) := by
    let L := tensorHsCoeffL (I := I) (M := M)
      (g := S.family.metric (T : Real)) (r := 0) (s := 0)
      (a := ((0 : Nat) : Real)) i
    have hcomp : ContDiffOn Real ∞
        (fun t => L (galLimExt hτ.le hlim 0 t))
        (Ioo (0 : Real) tau) := by
      simpa only [Function.comp_apply] using
        L.contDiff.comp_contDiffOn (hsmooth 0)
    have hcoeff_open : ContDiffOn Real ∞
        (fun t => ulim t i) (Ioo (0 : Real) tau) := by
      refine hcomp.congr ?_
      intro t ht
      simpa only [L, q, tensorHsCoeffL_apply] using
        (galLimExt_coeff hτ.le hlim 0 ⟨ht.1.le, ht.2.le⟩ i).symm
    exact hcoeff_open.mono hKsub
  refine ⟨hcoeff_smooth, ?_⟩
  intro j m
  obtain ⟨k : Nat, hk⟩ := exists_nat_gt p
  have hmp : (m : Real) + p ≤ ((m + k : Nat) : Real) := by
    rw [Nat.cast_add]
    nlinarith
  let J := tensorHsInclusion (I := I) (M := M)
    (g := q) (r := 0) (s := 0) hmp
  let U : Real → tensorHs (I := I) (M := M) q 0 0 ((m : Real) + p) :=
    fun t => J (galLimExt hτ.le hlim (m + k) t)
  have hU : ContDiffOn Real ∞ U (Ioo (0 : Real) tau) := by
    simpa only [U, Function.comp_apply] using
      J.contDiff.comp_contDiffOn (hsmooth (m + k))
  let W : Real → tensorHs (I := I) (M := M) q 0 0 ((m : Real) + p) :=
    fun t => iteratedDeriv j U t
  have hWopen : ContinuousOn W (Ioo (0 : Real) tau) := by
    have hF : ContinuousOn (iteratedFDeriv Real j U)
        (Ioo (0 : Real) tau) :=
      ContinuousOn.continuousOn_iteratedFDeriv hU isOpen_Ioo
        (by exact_mod_cast le_top)
    have hE :=
      (ContinuousMultilinearMap.piFieldEquiv Real (Fin j)
        (tensorHs (I := I) (M := M) q 0 0 ((m : Real) + p))).symm.continuous
        |>.comp_continuousOn hF
    simpa only [W, iteratedDeriv_eq_equiv_comp, Function.comp_apply] using hE
  have hW : ContinuousOn W (Icc a b) := hWopen.mono hKsub
  let jet : TensorEigenIdx (I := I) (M := M) q 0 0 → Real → Real :=
    fun i t => iteratedDeriv j (fun s => ulim s i) t
  have hjet (i : TensorEigenIdx (I := I) (M := M) q 0 0)
      (t : Real) (ht : t ∈ Icc a b) :
      (W t).coeff i = jet i t := by
    have htO : t ∈ Ioo (0 : Real) tau := hKsub ht
    let L := tensorHsCoeffL (I := I) (M := M)
      (g := q) (r := 0) (s := 0) (a := (m : Real) + p) i
    have hEq : Set.EqOn (fun z => L (U z)) (fun z => ulim z i)
        (Ioo (0 : Real) tau) := by
      intro z hz
      simpa only [L, U, J, q, tensorHsCoeffL_apply,
        tensorHsInclusion_coeff_apply] using
        galLimExt_coeff hτ.le hlim (m + k) ⟨hz.1.le, hz.2.le⟩ i
    have hUt : ContDiffWithinAt Real j U (Ioo (0 : Real) tau) t :=
      (hU t htO).of_le (by exact_mod_cast le_top)
    have hcomm := DifferentialGeometry.Analysis.iteratedDerivWithin_clm_comp
      L hUt (uniqueDiffOn_Ioo (0 : Real) tau) htO
    calc
      (W t).coeff i = L (iteratedDeriv j U t) := by
        simp only [W, L, tensorHsCoeffL_apply]
      _ = L (iteratedDerivWithin j U (Ioo (0 : Real) tau) t) :=
        congrArg L
          (iteratedDerivWithin_of_isOpen (f := U) isOpen_Ioo htO).symm
      _ = iteratedDerivWithin j (fun z => L (U z))
          (Ioo (0 : Real) tau) t := hcomm.symm
      _ = iteratedDerivWithin j (fun z => ulim z i)
          (Ioo (0 : Real) tau) t :=
        iteratedDerivWithin_congr hEq htO
      _ = iteratedDeriv j (fun z => ulim z i) t :=
        iteratedDerivWithin_of_isOpen isOpen_Ioo htO
      _ = jet i t := rfl
  have hneg : Summable (fun i : TensorEigenIdx (I := I) (M := M) q 0 0 =>
      tensorSobolevWeight (I := I) (M := M) i
        (-(((m : Real) + p) - (m : Real)))) := by
    simpa only [tensorSobolevWeight, sub_self, add_sub_cancel_left,
      neg_inj] using hpsum
  obtain ⟨B, hB, hB_le⟩ :=
    mass_le_of_compact (I := I) (M := M) q hneg isCompact_Icc W hW jet
      (fun t ht i => hjet i t ht)
  refine ⟨B, hB, ?_⟩
  intro i t ht
  simpa only [jet] using hB_le i t ht

/-- On compact slabs inside a prescribed positive interior, the scalar
Galerkin series is jointly smooth to every finite order. -/
theorem galJoint_fin_on
    {D : RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hS : IsSolutionOn (I := I) S) (hτ : 0 < tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim)
    (hreg : ∀ s ∈ Icc (0 : Real) tau, (T : Real) - s ∈ D.regular)
    (hcore : ∀ s ∈ Icc (0 : Real) tau,
      ∀ v : ScalarH2Core (I := I) (M := M) (S.family.metric (T : Real)),
        tensorHsZeroEquivL2 (I := I) (M := M)
            (tensorResolventL2_isCompactOperator
              (I := I) (M := M) (S.family.metric (T : Real)) 0 0)
            (lapDiffA20 (I := I) (M := M) S.family T s v.1) =
          lapDiffCore (I := I) (M := M) (S.family.metric (T : Real))
            (S.family.metric ((T : Real) - s)) v) :
    ∀ ⦃a b : Real⦄, 0 < a → a < b → b < tau → ∀ N : Nat,
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) (N : Nat)
        (fun q : Real × M =>
          scalarSpecSum (I := I) (M := M) (S.family.metric (T : Real))
            (fun i t => ulim t i) q.1 q.2)
        (Icc a b ×ˢ (Set.univ : Set M)) := by
  classical
  have hjet := galJet_mass_on (I := I) (M := M)
    hS hτ hlim hreg hcore
  let q : SmoothRiemannianMetric I M := S.family.metric (T : Real)
  have htail : EigenvalueTailSummable (I := I) (M := M) q 0 0 :=
    scalar_eigen_tail (I := I) (M := M) q
  intro a b ha hab hb N
  let a₀ : Real := a / 2
  let b₀ : Real := (b + tau) / 2
  have ha₀ : 0 < a₀ := by
    dsimp only [a₀]
    linarith
  have hab₀ : a₀ ≤ b₀ := by
    dsimp only [a₀, b₀]
    linarith
  have hb₀ : b₀ < tau := by
    dsimp only [b₀]
    linarith
  obtain ⟨hcoeff, hmass⟩ := hjet ha₀ hab₀ hb₀
  have hinner : Icc a b ⊆ Ioo a₀ b₀ := by
    intro t ht
    constructor <;> dsimp only [a₀, b₀] <;> linarith [ht.1, ht.2]
  refine scalar_path_recon (I := I) (M := M) q htail hab N
    (fun i t => ulim t i) isOpen_Ioo hinner ?_ ?_
  · intro i
    exact ((hcoeff i).mono Ioo_subset_Icc_self).of_le
      (by exact_mod_cast le_top)
  · intro j _hj m
    obtain ⟨B, hB, hB_le⟩ := hmass j m
    refine ⟨B, hB, ?_⟩
    intro i t ht
    exact hB_le i t (Ioo_subset_Icc_self (hinner ht))

/-- The scalar Galerkin series is jointly smooth on the full positive
interior of a prescribed regular interval. -/
theorem galJoint_on
    {D : RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hS : IsSolutionOn (I := I) S) (hτ : 0 < tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim)
    (hreg : ∀ s ∈ Icc (0 : Real) tau, (T : Real) - s ∈ D.regular)
    (hcore : ∀ s ∈ Icc (0 : Real) tau,
      ∀ v : ScalarH2Core (I := I) (M := M) (S.family.metric (T : Real)),
        tensorHsZeroEquivL2 (I := I) (M := M)
            (tensorResolventL2_isCompactOperator
              (I := I) (M := M) (S.family.metric (T : Real)) 0 0)
            (lapDiffA20 (I := I) (M := M) S.family T s v.1) =
          lapDiffCore (I := I) (M := M) (S.family.metric (T : Real))
            (S.family.metric ((T : Real) - s)) v) :
    ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
      (fun q : Real × M =>
        scalarSpecSum (I := I) (M := M) (S.family.metric (T : Real))
          (fun i t => ulim t i) q.1 q.2)
      (Ioo (0 : Real) tau ×ˢ (Set.univ : Set M)) := by
  have hfin := galJoint_fin_on (I := I) (M := M)
    hS hτ hlim hreg hcore
  rw [contMDiffOn_infty]
  intro N p hp
  let a : Real := p.1 / 2
  let b : Real := (p.1 + tau) / 2
  have ha : 0 < a := by
    dsimp only [a]
    linarith [hp.1.1]
  have hab : a < b := by
    dsimp only [a, b]
    linarith [hp.1.2]
  have hb : b < tau := by
    dsimp only [b]
    linarith [hp.1.2]
  have hat : a < p.1 := by
    dsimp only [a]
    linarith [hp.1.1]
  have htb : p.1 < b := by
    dsimp only [b]
    linarith [hp.1.2]
  have hpab : p ∈ Icc a b ×ˢ (Set.univ : Set M) :=
    ⟨⟨hat.le, htb.le⟩, Set.mem_univ _⟩
  have hnhds : Icc a b ×ˢ (Set.univ : Set M) ∈ 𝓝 p :=
    prod_mem_nhds (Icc_mem_nhds hat htb) univ_mem
  exact ((hfin ha hab hb N) p hpab).contMDiffAt hnhds |>.contMDiffWithinAt

/-- On the full positive interior of a prescribed regular interval, the scalar
Galerkin series solves the original-time conjugate heat equation pointwise. -/
theorem galPde_on
    {D : RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hS : IsSolutionOn (I := I) S) (hτ : 0 < tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim)
    (hreg : ∀ s ∈ Icc (0 : Real) tau, (T : Real) - s ∈ D.regular)
    (hcore : ∀ s ∈ Icc (0 : Real) tau,
      ∀ v : ScalarH2Core (I := I) (M := M) (S.family.metric (T : Real)),
        tensorHsZeroEquivL2 (I := I) (M := M)
            (tensorResolventL2_isCompactOperator
              (I := I) (M := M) (S.family.metric (T : Real)) 0 0)
            (lapDiffA20 (I := I) (M := M) S.family T s v.1) =
          lapDiffCore (I := I) (M := M) (S.family.metric (T : Real))
            (S.family.metric ((T : Real) - s)) v) :
    ∀ t ∈ Ioo (0 : Real) tau, ∀ x : M,
      HasDerivAt
        (fun s =>
          scalarSpecSum (I := I) (M := M)
            (S.family.metric (T : Real))
            (fun i r => ulim r i) s x)
        (laplacianAt (I := I) (flowG (I := I) S) ((T : Real) - t)
            (scalarSpecSum (I := I) (M := M)
              (S.family.metric (T : Real))
              (fun i r => ulim r i) t) x +
          (conjCoeff (I := I) (M := M) S ((T : Real) - t) : M → Real) x *
            scalarSpecSum (I := I) (M := M)
              (S.family.metric (T : Real))
              (fun i r => ulim r i) t x) t := by
  classical
  let q : SmoothRiemannianMetric I M := S.family.metric (T : Real)
  let hc := tensorResolventL2_isCompactOperator (I := I) (M := M) q 0 0
  have htail : EigenvalueTailSummable (I := I) (M := M) q 0 0 :=
    scalar_eigen_tail (I := I) (M := M) q
  have hjet := galJet_mass_on (I := I) (M := M)
    hS hτ hlim hreg hcore
  have hlift := galVel_lift_on (I := I) (M := M)
    hS hτ hlim hreg hcore
  obtain ⟨w, _hwcont, hw0, hwcan⟩ := hlift 0
  intro t ht x
  have htTau : t ∈ Icc (0 : Real) tau := ⟨ht.1.le, ht.2.le⟩
  obtain ⟨U, hUall, hscalar⟩ :=
    galLim_slice_cc (I := I) (M := M) hτ.le hlim htTau
  let f : M → Real :=
    TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) U.toSection
  have hf : ContMDiff I 𝓘(Real, Real) ∞ f := by
    exact TensorRSField.scalar0_smooth (n := (∞ : WithTop ℕ∞)) U.toSection
  have hscalar' :
      scalarSpecSum (I := I) (M := M) q
          (fun i s => ulim s i) t = f := by
    simpa only [q, f] using hscalar
  let h : SmoothRiemannianMetric I M := S.family.metric ((T : Real) - t)
  let zeta : C^∞⟮I, M; Real⟯ :=
    conjCoeff (I := I) (M := M) S ((T : Real) - t)
  let W : SmoothCcTensor q 0 0 :=
    rawTensorConnLapSmooth (I := I) q 0 0 U +
      scalarLapDiffCc (I := I) q h U +
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.scalarSmul
          (I := I) (M := M) q 0 0 zeta U
  let U3 : tensorHs (I := I) (M := M) q 0 0
      (((1 : Nat) : Real) + 2) :=
    ccTensorToHs (I := I) (M := M) q 0 (((1 : Nat) : Real) + 2) U
  let U1 : tensorHs (I := I) (M := M) q 0 0 ((1 : Nat) : Real) :=
    ccTensorToHs (I := I) (M := M) q 0 ((1 : Nat) : Real) U
  let Ubar : tensorHs (I := I) (M := M) q 0 0
      (((1 : Nat) : Real) + 2) :=
    tensorHs.castEquiv (I := I) (M := M)
      (g := q) (r := 0) (s := 0)
      (by norm_num : ((1 + 2 : Nat) : Real) = ((1 : Nat) : Real) + 2)
      (galLimExt hτ.le hlim (1 + 2) t)
  let U1bar : tensorHs (I := I) (M := M) q 0 0 ((1 : Nat) : Real) :=
    tensorHsInclusion (I := I) (M := M)
      (g := q) (r := 0) (s := 0)
      (by norm_num : ((1 : Nat) : Real) ≤ ((1 : Nat) : Real) + 2) Ubar
  have hUbar : Ubar = U3 := by
    apply tensorHs.ext
    funext i
    simp only [Ubar, tensorHs.castEquiv_coeff]
    have hi := congrArg
      (fun v : tensorHs (I := I) (M := M) q 0 0
          (((1 + 2 : Nat) : Real)) => v.coeff i)
      (hUall (1 + 2))
    simpa only [U3, q, ccTensorToHs_coeff] using hi.symm
  have hU1bar : U1bar = U1 := by
    apply tensorHs.ext
    funext i
    simp only [U1bar, tensorHsInclusion_coeff_apply]
    rw [hUbar]
    simp only [U3, U1, ccTensorToHs_coeff]
  have hlapCore :
      tensorScaleLaplacian (I := I) (M := M)
          (g := q) (r := 0) (s := 0) ((1 : Nat) : Real) U3 =
        ccTensorToHs (I := I) (M := M) q 0 ((1 : Nat) : Real)
          (rawTensorConnLapSmooth (I := I) q 0 0 U) := by
    simpa only [U3] using
      scalarLapHs_core (I := I) (M := M) q ((1 : Nat) : Real) U
  have hdiffCore :
      lapDiffHs (I := I) (M := M) q h 1 U3 =
        ccTensorToHs (I := I) (M := M) q 0 ((1 : Nat) : Real)
          (scalarLapDiffCc (I := I) q h U) := by
    simpa only [q, h, U3] using
      lapHs_core (I := I) (M := M) q h 1 U
  have hpotCore :
      scalarPotHs (I := I) (M := M) q zeta 1 U1 =
        ccTensorToHs (I := I) (M := M) q 0 ((1 : Nat) : Real)
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.scalarSmul
            (I := I) (M := M) q 0 0 zeta U) := by
    simpa only [U1] using
      scalarPotHs_core (I := I) (M := M) q zeta 1 U
  have hvelExpand :
      galLimVelHs hτ.le hlim 1 t =
        tensorScaleLaplacian (I := I) (M := M)
            (g := q) (r := 0) (s := 0) ((1 : Nat) : Real) Ubar +
          lapDiffHs (I := I) (M := M) q h 1 Ubar +
          scalarPotHs (I := I) (M := M) q zeta 1 U1bar := by
    rfl
  have hW1 :
      ccTensorToHs (I := I) (M := M) q 0 ((1 : Nat) : Real) W =
        galLimVelHs hτ.le hlim 1 t := by
    calc
      _ = ccTensorToHs (I := I) (M := M) q 0 ((1 : Nat) : Real)
              (rawTensorConnLapSmooth (I := I) q 0 0 U) +
            ccTensorToHs (I := I) (M := M) q 0 ((1 : Nat) : Real)
              (scalarLapDiffCc (I := I) q h U) +
            ccTensorToHs (I := I) (M := M) q 0 ((1 : Nat) : Real)
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.scalarSmul
                (I := I) (M := M) q 0 0 zeta U) := by
              simp only [W, ccTensorToHs_add]
      _ = tensorScaleLaplacian (I := I) (M := M)
              (g := q) (r := 0) (s := 0) ((1 : Nat) : Real) U3 +
            lapDiffHs (I := I) (M := M) q h 1 U3 +
            scalarPotHs (I := I) (M := M) q zeta 1 U1 := by
              rw [← hlapCore, ← hdiffCore, ← hpotCore]
      _ = _ := by
        rw [← hUbar, ← hU1bar]
        exact hvelExpand.symm
  let J10 := tensorHsInclusion (I := I) (M := M)
    (g := q) (r := 0) (s := 0)
    (by norm_num : ((0 : Nat) : Real) ≤ ((1 : Nat) : Real))
  have hcan :
      J10 (ccTensorToHs (I := I) (M := M) q 0 ((1 : Nat) : Real) W) =
        galLimVelCan hτ.le hlim 0 t := by
    have hz := congrArg J10 hW1
    simpa only [J10, galLimVelCan, q] using hz
  let tt : Icc (0 : Real) tau := ⟨t, htTau⟩
  have hWcoeff (i : TensorEigenIdx (I := I) (M := M) q 0 0) :
      tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 W) i =
        (galLimVel hτ.le hlim t).coeff i := by
    have h1 := congrArg
      (fun z : tensorHs (I := I) (M := M) q 0 0 ((0 : Nat) : Real) =>
        z.coeff i) hcan
    have h2 := congrArg
      (fun z : tensorHs (I := I) (M := M) q 0 0 ((0 : Nat) : Real) =>
        z.coeff i) (hwcan tt)
    have h3 := congrArg
      (fun z : tensorHs (I := I) (M := M) q 0 0 (0 : Real) =>
        z.coeff i) (hw0 tt)
    calc
      _ = (ccTensorToHs (I := I) (M := M) q 0
          ((1 : Nat) : Real) W).coeff i := by
        simpa only [hc] using
          (ccTensorToHs_coeff (I := I) (M := M) q 0
            ((1 : Nat) : Real) W i).symm
      _ = (galLimVelCan hτ.le hlim 0 t).coeff i := by
        simpa only [J10, tensorHsInclusion_coeff_apply] using h1
      _ = (w tt).coeff i := by
        simpa only [tt] using h2.symm
      _ = (galLimVel hτ.le hlim t).coeff i := by
        simpa only [tt, tensorHsInclusion_coeff_apply] using h3
  let a : Real := t / 2
  let b : Real := (t + tau) / 2
  have ha : 0 < a := by
    dsimp only [a]
    linarith [ht.1]
  have hab : a < b := by
    dsimp only [a, b]
    linarith [ht.2]
  have hb : b < tau := by
    dsimp only [b]
    linarith [ht.2]
  obtain ⟨_hcoeff, hmass⟩ := hjet ha hab.le hb
  have hIcc : Icc a b ⊆ Ioo (0 : Real) tau := by
    intro s hs
    exact ⟨ha.trans_le hs.1, hs.2.trans_lt hb⟩
  have htIcc : t ∈ Icc a b := by
    constructor <;> dsimp only [a, b] <;> linarith [ht.1, ht.2]
  have hat : a < t := by
    dsimp only [a]
    linarith [ht.1]
  have htb : t < b := by
    dsimp only [b]
    linarith [ht.2]
  have hmass1 : ∀ j : Nat, j ≤ 1 → ∀ m : Nat,
      ∃ B : TensorEigenIdx (I := I) (M := M) q 0 0 → Real,
        Summable B ∧
        ∀ i s, s ∈ Icc a b →
          tensorSobolevWeight (I := I) (M := M) i (m : Real) *
            (iteratedDeriv j (fun r => ulim r i) s) ^ 2 ≤ B i := by
    intro j _hj m
    simpa only [q] using hmass j m
  have hderiv :
      HasDerivAt
        (fun s => scalarSpecSum (I := I) (M := M) q
          (fun i r => ulim r i) s x)
        (scalarSpecSum (I := I) (M := M) q
          (fun i s => deriv (fun r => ulim r i) s) t x) t := by
    exact (scalarSpec_d1 (I := I) (M := M) q htail hab
      (fun i r => ulim r i) isOpen_Ioo hIcc
      (fun i => galLim_mode_c1 hτ hlim i) hmass1 x htIcc).hasDerivAt
        (Icc_mem_nhds hat htb)
  have hderivSeries :
      scalarSpecSum (I := I) (M := M) q
          (fun i s => deriv (fun r => ulim r i) s) t x =
        scalarSpecSum (I := I) (M := M) q
          (fun i _ => (galLimVel hτ.le hlim t).coeff i) t x := by
    unfold scalarSpecSum
    apply tsum_congr
    intro i
    change deriv (fun r => ulim r i) t * _ =
      (galLimVel hτ.le hlim t).coeff i * _
    rw [(galLim_mode_deriv hτ hlim ht i).deriv]
  have hseriesW :
      scalarSpecSum (I := I) (M := M) q
          (fun i _ => (galLimVel hτ.le hlim t).coeff i) t x =
        TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) W.toSection x := by
    calc
      _ = scalarSpecSum (I := I) (M := M) q
          (fun i _ => tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 W) i) 0 x := by
              unfold scalarSpecSum
              apply tsum_congr
              intro i
              change (galLimVel hτ.le hlim t).coeff i * _ =
                tensorL2Coeff (I := I) (M := M) hc
                  (SmoothCcTensor.toL2 W) i * _
              rw [hWcoeff i]
      _ = _ := congrFun (scalarSpec_cc (I := I) (M := M) q W) x
  have htime :
      HasDerivAt
        (fun s => scalarSpecSum (I := I) (M := M) q
          (fun i r => ulim r i) s x)
        (TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) W.toSection x) t :=
    hderiv.congr_deriv (hderivSeries.trans hseriesW)
  have hWscalar :
      TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) W.toSection x =
        Δ_g (I := I) h ⟨_, hf⟩ x + (zeta : M → Real) x * f x := by
    simp only [W, SmoothCcTensor.toSection_add, TensorRSField.scalar0_add,
      Pi.add_apply, rawLap_cc_scalar (I := I) (M := M) q U x,
      scalarLapDiff_eq (I := I) (M := M) q h U x,
      DifferentialGeometry.Analysis.Sobolev.scalar0_smul_cc
        (I := I) (M := M) q zeta U x, f]
    ring
  have hlap :
      laplacianAt (I := I) (flowG (I := I) S) ((T : Real) - t) f x =
        Δ_g (I := I) h ⟨_, hf⟩ x := by
    simpa only [h] using
      (laplacianAt_eq_delta (I := I) (M := M)
        (flowG (I := I) S) ((T : Real) - t) hf (by rfl) x)
  refine htime.congr_deriv ?_
  rw [hscalar', hlap]
  simpa only [zeta] using hWscalar

/-- A scalar Galerkin limit on a prescribed regular interval is a genuine
classical heat potential on that entire interval. -/
theorem gallim_on
    {D : RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hS : IsSolutionOn (I := I) S) (hτ : 0 < tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim)
    (hreg : ∀ s ∈ Icc (0 : Real) tau, (T : Real) - s ∈ D.regular)
    (hcore : ∀ s ∈ Icc (0 : Real) tau,
      ∀ v : ScalarH2Core (I := I) (M := M) (S.family.metric (T : Real)),
        tensorHsZeroEquivL2 (I := I) (M := M)
            (tensorResolventL2_isCompactOperator
              (I := I) (M := M) (S.family.metric (T : Real)) 0 0)
            (lapDiffA20 (I := I) (M := M) S.family T s v.1) =
          lapDiffCore (I := I) (M := M) (S.family.metric (T : Real))
            (S.family.metric ((T : Real) - s)) v) :
    DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn
      (RealTimeInterval.closed 0 tau hτ.le)
      (reverseFamily (I := I) (M := M) (flowG (I := I) S) (T : Real))
      (fun s x =>
        (conjCoeff (I := I) (M := M) S ((T : Real) - s) : M → Real) x)
      (fun s x =>
        scalarSpecSum (I := I) (M := M) (S.family.metric (T : Real))
          (fun i r => ulim r i) s x) := by
  have hjoint := galJoint_on (I := I) (M := M)
    hS hτ hlim hreg hcore
  have hcont := galLim_joint_cont (I := I) (M := M) hτ hlim
  have hpde := galPde_on (I := I) (M := M)
    hS hτ hlim hreg hcore
  refine
    { jointSmooth := hjoint
      jointCont := hcont
      sliceSmooth := ?_
      equation := ?_ }
  · intro s hs
    change s ∈ Icc (0 : Real) tau at hs
    obtain ⟨U, _hU, hscalar⟩ :=
      galLim_slice_cc (I := I) (M := M) hτ.le hlim hs
    rw [hscalar]
    exact TensorRSField.scalar0_smooth
      (n := (∞ : WithTop ℕ∞)) U.toSection
  · intro s hs x
    change s ∈ Ioo (0 : Real) tau at hs
    simpa only [reverseFamily] using hpde s hs x

/-- A positive initial scalar Galerkin datum stays positive on a prescribed
regular interval contained in a compact regular-time slab. -/
theorem gallim_pos_on
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {a b : Real} (hab : Icc a b ⊆ D.regular)
    (T : D.RegularTime) (hT : (T : Real) ∈ Icc a b)
    {tau : Real} (hτ : 0 < tau) (hleft : a ≤ (T : Real) - tau)
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim)
    (hu : DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn
      (RealTimeInterval.closed 0 tau hτ.le)
      (reverseFamily (I := I) (M := M) (flowG (I := I) S) (T : Real))
      (fun s x =>
        (conjCoeff (I := I) (M := M) S ((T : Real) - s) : M → Real) x)
      (fun s x =>
        scalarSpecSum (I := I) (M := M) (S.family.metric (T : Real))
          (fun i r => ulim r i) s x))
    (hinit : ∀ x : M,
      0 < TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) u0.toSection x) :
    ∀ s ∈ Icc (0 : Real) tau, ∀ x : M,
      0 < scalarSpecSum (I := I) (M := M)
        (S.family.metric (T : Real)) (fun i r => ulim r i) s x := by
  obtain ⟨C, _hCnn, hC⟩ := conjCoeff_span (I := I) (M := M) S hS hab
  have hvar (s : Real) (hs : s ∈ Icc (0 : Real) tau) :
      (T : Real) - s ∈ Icc a b := by
    constructor <;> linarith [hs.1, hs.2, hT.1, hT.2]
  have hV : ∀ s : Real, s ∈ Icc (0 : Real) tau → ∀ x : M,
      |(conjCoeff (I := I) (M := M) S
        ((T : Real) - s) : M → Real) x| ≤ C := by
    intro s hs x
    exact hC ((T : Real) - s) (hvar s hs) x
  have huinit : ∀ x : M,
      0 < scalarSpecSum (I := I) (M := M)
        (S.family.metric (T : Real)) (fun i r => ulim r i) 0 x := by
    intro x
    rw [galLim_initial (I := I) (M := M) hlim]
    exact hinit x
  exact DifferentialGeometry.Analysis.Parabolic.heat_pot_pos
    (I := I) (M := M)
    (reverseFamily (I := I) (M := M) (flowG (I := I) S) (T : Real))
    hτ.le
    (fun s x =>
      (conjCoeff (I := I) (M := M) S ((T : Real) - s) : M → Real) x)
    (fun s x =>
      scalarSpecSum (I := I) (M := M) (S.family.metric (T : Real))
        (fun i r => ulim r i) s x)
    hu C hV huinit

end DifferentialGeometry.PDE.RicciFlow.Entropy

end
