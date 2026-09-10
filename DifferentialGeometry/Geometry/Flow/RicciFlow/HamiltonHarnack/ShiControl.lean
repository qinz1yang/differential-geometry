import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.CompactSlab
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.ActualEvolution

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

theorem hamiltonBlock_coefficients_bound_on_slab
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {alpha beta psi C : Real}
    (halphaBeta : alpha < beta)
    (hbetaPsi : beta <= psi)
    (hslab : Set.Icc alpha psi ⊆ D.carrier)
    (hreg : Set.Ioc alpha psi ⊆ D.regular)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric alpha))
    (hC : 0 <= C)
    (hcurv : forall t, t ∈ Set.Icc alpha psi -> forall x : M,
      DifferentialGeometry.Tensor0SBundle.normSq0S (I := I)
        (S.base.metric t) x 4 (S.base.rm04 t x) <= C) :
    exists B : Real, 0 <= B ∧
      forall (clock : HarnackClock), clock.time ∈ Set.Icc beta psi ->
      clock.elapsed <= psi - beta -> forall (x : M),
      forall basis : Module.Basis (Fin (Module.finrank Real E)) Real
        (TangentSpace I x),
      (forall i j,
        (S.base.metric clock.time).inner x (basis i) (basis j) =
          if i = j then (1 : Real) else 0) ->
      (forall a b c d,
        |S.base.rm04 clock.time x
          (vec4 (I := I) (basis a) (basis b) (basis c) (basis d))| <= B) ∧
      (forall a b c,
        |hamiltonPComponent
          (fun i j k => metricNablaRic (I := I) (M := M)
            (S.base.metric clock.time) x
            (vec3 (I := I) (basis i) (basis j) (basis k))) a b c| <= B) ∧
      (forall a b,
        |hamiltonMComponent clock
          (fun i j k l => S.base.rm04 clock.time x
            (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
          (fun i j => metricRicci (I := I) (M := M)
            (S.base.metric clock.time) x
            (vec2 (I := I) (basis i) (basis j)))
          (fun i j => hamiltonDivPAt (I := I)
            (S.base.metric clock.time) x
            (vec2 (I := I) (basis i) (basis j))) a b| <=
          B / clock.elapsed) ∧
      (forall a b,
        |metricRicci (I := I) (M := M) (S.base.metric clock.time) x
          (vec2 (I := I) (basis a) (basis b))| <= B) := by
  obtain ⟨K, _, hShi⟩ := shi_curvature_derivative_bound_on_slab
    (I := I) S hS halphaBeta hbetaPsi hslab hreg hcomplete hC hcurv
  let A := Real.sqrt K
  let N : Real := Module.finrank Real E
  let B := A + N * A + N * A +
    (psi - beta) * (N ^ 2 * A + N ^ 3 * A ^ 2) + N * A / 2
  refine ⟨B, ?_, ?_⟩
  · dsimp [B]
    positivity
  · intro clock htime helapsed x basis horth
    have htreg : clock.time ∈ D.regular := hreg
      ⟨lt_of_lt_of_le halphaBeta htime.1, htime.2⟩
    have hcoeff := hamiltonBlock_coefficients_bound_of_curvature_derivative_bound
      (I := I) S clock htreg x basis horth K (psi - beta)
      (sub_nonneg.mpr hbetaPsi) helapsed
      (fun k hk => hShi k hk clock.time htime x)
    exact hcoeff.2

theorem hamilton_unshifted_coefficients_bound_on_slab
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {alpha beta psi C : Real}
    (halphaBeta : alpha < beta)
    (hbetaPsi : beta <= psi)
    (hslab : Set.Icc alpha psi ⊆ D.carrier)
    (hreg : Set.Ioc alpha psi ⊆ D.regular)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric alpha))
    (hC : 0 <= C)
    (hcurv : forall t, t ∈ Set.Icc alpha psi -> forall x : M,
      DifferentialGeometry.Tensor0SBundle.normSq0S (I := I)
        (S.base.metric t) x 4 (S.base.rm04 t x) <= C) :
    exists B : Real, 0 <= B ∧
      forall t, t ∈ Set.Icc beta psi -> forall (x : M),
      forall basis : Module.Basis (Fin (Module.finrank Real E)) Real
        (TangentSpace I x),
      (forall i j,
        (S.base.metric t).inner x (basis i) (basis j) =
          if i = j then (1 : Real) else 0) ->
      (forall a b c,
        |hamiltonPComponent
          (fun i j k => metricNablaRic (I := I) (M := M)
            (S.base.metric t) x
            (vec3 (I := I) (basis i) (basis j) (basis k))) a b c| <= B) ∧
      (forall a b,
        |hamiltonMbarAt (I := I) (S.base.metric t) x
          (vec2 (I := I) (basis a) (basis b))| <= B) := by
  obtain ⟨K, _, hShi⟩ := shi_curvature_derivative_bound_on_slab
    (I := I) S hS halphaBeta hbetaPsi hslab hreg hcomplete hC hcurv
  let A := Real.sqrt K
  let N : Real := Module.finrank Real E
  let B0 := A + N * A + N * A +
    (N ^ 2 * A + N ^ 3 * A ^ 2) + N * A / 2
  let B := 2 * B0
  have hB0 : 0 <= B0 := by
    dsimp only [B0, A, N]
    positivity
  refine ⟨B, mul_nonneg (by norm_num) hB0, ?_⟩
  intro t ht x basis horth
  let unitClock : HarnackClock :=
    ⟨t - 1, t, by linarith⟩
  have hunit : unitClock.elapsed = 1 := by
    simp [unitClock, HarnackClock.elapsed]
  have htreg : t ∈ D.regular := hreg
    ⟨lt_of_lt_of_le halphaBeta ht.1, ht.2⟩
  have hcoeff := hamiltonBlock_coefficients_bound_of_curvature_derivative_bound
    (I := I) S unitClock htreg x basis horth K 1 (by norm_num)
      (by simp [hunit]) (fun k hk => hShi k hk t ht x)
  dsimp only at hcoeff
  have hB0' : 0 <= B0 := by
    simpa only [B0, A, N, Nat.cast_ofNat, one_mul] using hcoeff.1
  refine ⟨?_, ?_⟩
  · intro a b c
    have hP := hcoeff.2.2.1 a b c
    calc
      |hamiltonPComponent
          (fun i j k => metricNablaRic (I := I) (M := M)
            (S.base.metric t) x
            (vec3 (I := I) (basis i) (basis j) (basis k))) a b c| <= B0 := by
        simpa only [B0, A, N, Nat.cast_ofNat, one_mul] using hP
      _ <= B := by
        dsimp only [B]
        linarith
  · intro a b
    have hM := hcoeff.2.2.2.1 a b
    have hMbridge := hamiltonMComponent_eq_hamiltonMAt_orthonormal
      (I := I) S hS unitClock htreg x basis horth a b
    have hMbridgeBase :
        hamiltonMComponent unitClock
            (fun i j k l => S.base.rm04 unitClock.time x
              (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
            (fun i j => metricRicci (I := I) (M := M)
              (S.base.metric unitClock.time) x
              (vec2 (I := I) (basis i) (basis j)))
            (fun i j => hamiltonDivPAt (I := I)
              (S.base.metric unitClock.time) x
              (vec2 (I := I) (basis i) (basis j))) a b =
          hamiltonMAt (I := I) unitClock (S.base.metric unitClock.time) x
            (vec2 (I := I) (basis a) (basis b)) := by
      simpa only [SolutionOn.family, SolutionFamily.rm04] using hMbridge
    rw [hMbridgeBase] at hM
    have hM' :
        |hamiltonMAt (I := I) unitClock (S.base.metric t) x
          (vec2 (I := I) (basis a) (basis b))| <= B0 := by
      simpa only [B0, A, N, unitClock, hunit, div_one, Nat.cast_ofNat, one_mul] using hM
    have hRic := hcoeff.2.2.2.2 a b
    have hRic' :
        |metricRicci (I := I) (M := M) (S.base.metric t) x
          (vec2 (I := I) (basis a) (basis b))| <= B0 := by
      simpa only [B0, A, N, unitClock, Nat.cast_ofNat, one_mul] using hRic
    have hsplit :
        hamiltonMbarAt (I := I) (S.base.metric t) x
            (vec2 (I := I) (basis a) (basis b)) =
          hamiltonMAt (I := I) unitClock (S.base.metric t) x
              (vec2 (I := I) (basis a) (basis b)) -
            (1 / 2 : Real) *
              metricRicci (I := I) (M := M) (S.base.metric t) x
                (vec2 (I := I) (basis a) (basis b)) := by
      simp [hamiltonMAt, hunit]
    rw [hsplit]
    calc
      |hamiltonMAt (I := I) unitClock (S.base.metric t) x
            (vec2 (I := I) (basis a) (basis b)) -
          (1 / 2 : Real) *
            metricRicci (I := I) (M := M) (S.base.metric t) x
              (vec2 (I := I) (basis a) (basis b))| <=
          |hamiltonMAt (I := I) unitClock (S.base.metric t) x
            (vec2 (I := I) (basis a) (basis b))| +
          |(1 / 2 : Real) *
            metricRicci (I := I) (M := M) (S.base.metric t) x
              (vec2 (I := I) (basis a) (basis b))| := abs_sub _ _
      _ <= B0 + (1 / 2 : Real) * B0 := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) <= 1 / 2)]
        exact add_le_add hM' (mul_le_mul_of_nonneg_left hRic' (by norm_num))
      _ <= B := by
        dsimp only [B]
        linarith

theorem exists_hamiltonPerturbedBlock_slab_control
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {alpha beta psi C0 : Real}
    (halphaBeta : alpha < beta)
    (hbetaPsi : beta <= psi)
    (hslab : Set.Icc alpha psi ⊆ D.carrier)
    (hreg : Set.Ioc alpha psi ⊆ D.regular)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric alpha))
    (hC0 : 0 <= C0)
    (hcurv : forall t, t ∈ Set.Icc alpha psi -> forall x : M,
      DifferentialGeometry.Tensor0SBundle.normSq0S (I := I)
        (S.base.metric t) x 4 (S.base.rm04 t x) <= C0) :
    let N : Real := Module.finrank Real E
    let S0 := psi - beta
    exists K B C : Real,
      0 <= K ∧ 0 <= B ∧ 0 <= C ∧
      B = Real.sqrt K + N * Real.sqrt K + N * Real.sqrt K +
        S0 * (N ^ 2 * Real.sqrt K + N ^ 3 * (Real.sqrt K) ^ 2) +
        N * Real.sqrt K / 2 ∧
      2 * (B + 1) * N ^ 3 <= C ∧
      2 * B * S0 * N ^ 3 + 4 * B * S0 ^ 2 * N ^ 4 +
          B * S0 ^ 2 * N ^ 2 + 4 * B ^ 2 * S0 ^ 2 * N ^ 2 +
          N ^ 2 <= C ∧
      4 * B * N ^ 3 + (8 * B + 4) * N ^ 4 + B * N +
          2 * B * N ^ 2 + 1 <= C ∧
      forall k : Nat, k <= 2 -> forall t, t ∈ Set.Icc beta psi ->
        forall x : M, nablaKRm04NormSqIntrinsic (I := I) S k t x <= K := by
  dsimp only
  obtain ⟨K, hK, hShi⟩ := shi_curvature_derivative_bound_on_slab
    (I := I) S hS halphaBeta hbetaPsi hslab hreg hcomplete hC0 hcurv
  let N : Real := Module.finrank Real E
  let S0 := psi - beta
  let B := Real.sqrt K + N * Real.sqrt K + N * Real.sqrt K +
    S0 * (N ^ 2 * Real.sqrt K + N ^ 3 * (Real.sqrt K) ^ 2) +
    N * Real.sqrt K / 2
  have hB : 0 <= B := by
    dsimp only [B]
    positivity
  obtain ⟨C, hC, hCphi, hCpsiW, hCpsiU⟩ :=
    exists_hamiltonPerturbedBlock_control_constant
      (Idx := Fin (Module.finrank Real E)) B S0
  simp only [Fintype.card_fin] at hCphi hCpsiW hCpsiU
  exact ⟨K, B, C, hK, hB, hC, rfl, hCphi, hCpsiW, hCpsiU, hShi⟩

end DifferentialGeometry.PDE.RicciFlow
