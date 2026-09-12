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

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem hamilton_bianchi_trace_at_orthonormal
    {D : RealTimeInterval} {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : ∀ i j,
      (S.base.metric t).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0) :
    SecondBianchiAt (I := I) (nablaRm04Field (I := I) S t x) ∧
      NablaRmSymmAt (I := I) (nablaRm04Field (I := I) S t x) ∧
        NablaRicTraceAt (I := I) basis
          (fun i j => if i = j then (1 : Real) else 0)
          (nablaRm04Field (I := I) S t x)
          (metricNablaRic (I := I) (M := M) (S.base.metric t) x) := by
  have hinv := DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal
    (I := I) (S.base.metric t) basis horth
  simpa [nablaRm04Field, SolutionOn.family, SolutionFamily.connection,
    SolutionFamily.rm04, metricNablaRic, metricCov, metricRm04, metricRicci,
    DifferentialGeometry.Geometry.Curvature.metricCov,
    DifferentialGeometry.Geometry.Curvature.metricRm04,
    DifferentialGeometry.Geometry.Curvature.metricRicci] using
    (DifferentialGeometry.Geometry.Connection.levi_civita_bianchi_trace_identities
      (I := I) (M := M) (S.base.metric t) basis
        (fun i j => if i = j then (1 : Real) else 0) hinv)

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem hamilton_nabla_rm_components_pair_symm
    {D : RealTimeInterval} {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : ∀ i j,
      (S.base.metric t).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0) :
    ∀ e, Rm04PairSymm (fun a b c d =>
      nablaRm04Field (I := I) S t x
        (vec5 (I := I) (basis e) (basis a) (basis b) (basis c) (basis d))) := by
  have hSymm := (hamilton_bianchi_trace_at_orthonormal
    (I := I) S t x basis horth).2.1
  intro e
  refine ⟨?_, ?_, ?_⟩
  · intro a b c d
    simpa only [vec5] using
      hSymm.2.1 (basis e) (basis b) (basis a) (basis c) (basis d)
  · intro a b c d
    simpa only [vec5] using
      hSymm.1 (basis e) (basis a) (basis b) (basis c) (basis d)
  · intro a b c d
    simpa only [vec5] using
      hSymm.2.2 (basis e) (basis a) (basis b) (basis c) (basis d)

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem hamilton_rm_components_symm
    {D : RealTimeInterval} {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (t : RealTimeInterval.RegularTime D) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x)) :
    Rm04Symm (fun a b c d => S.base.rm04 (t : Real) x
      (vec4 (I := I) (basis a) (basis b) (basis c) (basis d))) := by
  have hRm13 := fun tau : RealTimeInterval.RegularTime D =>
    rm13OfSolution (I := I) S (tau : Real)
  have hLower := fun
      (tau : RealTimeInterval.RegularTime D) (y : M) =>
    solution_rm04LowersRm13At (I := I) S (tau : Real) y
  have hInput := rm04InputSkew_regular
    (I := I) S S.base.rm13 S.base.rm04 hRm13 hLower t x
  have hOutput := rm04OutputSkew_regular
    (I := I) S S.base.rm13 S.base.rm04 hRm13 hLower t x
  have hPair := rm04PairSymm_regular
    (I := I) S S.base.rm13 S.base.rm04 hRm13 hLower t x
  have hFirst := rm04FirstBianchi_regular
    (I := I) S S.base.rm13 S.base.rm04 hRm13 hLower t x
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j k l
    simpa only [vec4] using
      hInput (basis j) (basis i) (basis k) (basis l)
  · intro i j k l
    simpa only [vec4] using
      hOutput (basis i) (basis j) (basis k) (basis l)
  · intro i j k l
    simpa only [vec4] using
      hPair (basis i) (basis j) (basis k) (basis l)
  · intro i j k l
    simpa only [vec4] using
      hFirst (basis i) (basis j) (basis k) (basis l)

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem hamilton_curvature_ricci_trace_components
    {D : RealTimeInterval} {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (t : RealTimeInterval.RegularTime D) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : ∀ i j,
      (S.base.metric (t : Real)).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0) :
    curvatureRicciTraceComponents
      (fun a b c d => S.base.rm04 (t : Real) x
        (vec4 (I := I) (basis a) (basis b) (basis c) (basis d)))
      (fun a b => metricRicci (I := I) (M := M)
        (S.base.metric (t : Real)) x
          (vec2 (I := I) (basis a) (basis b))) := by
  intro i j
  symm
  simpa only [SolutionOn.ricci, SolutionFamily.ricci] using
    (ricci_diag_eq_sum_rm04_diag_of_orthonormal
      (I := I) (S.base.metric (t : Real)) basis
      (S.ricci (t : Real)) (S.base.rm13 (t : Real)) (S.base.rm04 (t : Real))
      (ricciTraceOfSolution (I := I) S (t : Real))
      (solution_rm04LowersRm13At (I := I) S (t : Real) x) horth i j)

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem hamilton_contracted_curvature_derivative_components
    {D : RealTimeInterval} {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : ∀ i j,
      (S.base.metric t).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0) :
    contractedCurvatureDerivativeComponents
      (fun e a b c d => nablaRm04Field (I := I) S t x
        (vec5 (I := I) (basis e) (basis a) (basis b) (basis c) (basis d)))
      (fun a b c => metricNablaRic (I := I) (M := M)
        (S.base.metric t) x
          (vec3 (I := I) (basis a) (basis b) (basis c))) := by
  intro p q r
  have hcore := hamilton_bianchi_trace_at_orthonormal
    (I := I) S t x basis horth
  have hDiv := curvature_divergence_eq_hamiltonP (I := I) basis
    (fun i j => if i = j then (1 : Real) else 0)
    (nablaRm04Field (I := I) S t x)
    (metricNablaRic (I := I) (M := M) (S.base.metric t) x)
    hcore.1 hcore.2.1 hcore.2.2 (basis r) (basis q) (basis p)
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, hamiltonP_apply] at hDiv
  rw [metricNablaRic_last_two_symm (I := I) (M := M)
      (S.base.metric t) x (basis q) (basis r) (basis p),
    metricNablaRic_last_two_symm (I := I) (M := M)
      (S.base.metric t) x (basis r) (basis q) (basis p)] at hDiv
  simpa only [vec3, vec5] using hDiv

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [SigmaCompactSpace M] in
theorem exists_hamiltonPerturbedBlock_reaction_lower_bound
    (K S0 : Real) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ {D : RealTimeInterval}
        (S : SolutionOn (I := I) (M := M) D),
        IsSolutionOn (I := I) S →
        ∀ (clock : HarnackClock), clock.time ∈ D.regular →
        ∀ (x : M) {n : Nat}
        (basis : Module.Basis (Fin n) Real (TangentSpace I x)),
        (∀ i j, (S.base.metric clock.time).inner x (basis i) (basis j) =
          if i = j then (1 : Real) else 0) →
        ∀ (phi Lphi psi psi' : Real)
        (U : Fin n → Fin n → Real) (W : Fin n → Real),
        (∀ k : Nat, k ≤ 2 → nablaKRm04NormSqIntrinsic (I := I) S k clock.time x ≤ K) →
        clock.elapsed ≤ S0 → 0 ≤ phi → 0 ≤ psi → psi ≤ 1 →
        (∀ a b, U a b = -U b a) →
        let R : Fin n → Fin n → Fin n → Fin n → Real := fun a b c d ↦
          S.base.rm04 clock.time x
            (vec4 (I := I) (basis a) (basis b) (basis d) (basis c))
        let P : Fin n → Fin n → Fin n → Real := fun a b c ↦
          hamiltonPField (I := I) (S.base.metric clock.time) x
            (vec3 (I := I) (basis a) (basis b) (basis c))
        let Mbar : Fin n → Fin n → Real := fun a b ↦
          hamiltonMOriginField (I := I) clock.origin clock.time
            (S.base.metric clock.time) x (vec2 (I := I) (basis a) (basis b))
        let Ric : Fin n → Fin n → Real := fun a b ↦
          metricRicci (I := I) (M := M) (S.base.metric clock.time) x
            (vec2 (I := I) (basis a) (basis b))
        hamiltonBlockJ (hamiltonPerturbedCurvatureBlock R psi) P
            (hamiltonPerturbedMBlock clock Mbar phi) U W +
          hamiltonBlockSigmaSquare (hamiltonPerturbedCurvatureBlock R psi) P U W +
          (Lphi / clock.elapsed + phi / clock.elapsed ^ 2 -
              C * psi / clock.elapsed ^ 2 - C * phi / clock.elapsed) *
            (∑ a, (W a) ^ 2) +
          (psi' - C * psi) * (∑ a, ∑ b, (U a b) ^ 2) ≤
        hamiltonBlockJ R P Mbar U W + hamiltonBlockSigmaSquare R P U W +
          (Lphi / clock.elapsed + phi / clock.elapsed ^ 2) * (∑ a, (W a) ^ 2) +
          psi' * (∑ a, ∑ b, (U a b) ^ 2) -
          2 * psi * (∑ e, ∑ a, ∑ b,
            (hamiltonTestJetDU clock Ric
              (fun i j ↦ if i = j then (1 : Real) else 0) W e a b) ^ 2) := by
  classical
  let B : Real :=
    Real.sqrt K + (Module.finrank Real E : Real) * Real.sqrt K +
      (Module.finrank Real E : Real) * Real.sqrt K +
      S0 * ((Module.finrank Real E : Real) ^ 2 * Real.sqrt K +
        (Module.finrank Real E : Real) ^ 3 * (Real.sqrt K) ^ 2) +
      (Module.finrank Real E : Real) * Real.sqrt K / 2
  obtain ⟨C, hC, hCphi, hCpsiW, hCpsiU⟩ :=
    exists_hamiltonPerturbedBlock_control_constant
      (Idx := Fin (Module.finrank Real E)) B S0
  simp only [Fintype.card_fin] at hCphi hCpsiW hCpsiU
  refine ⟨C, hC, ?_⟩
  intro D S hS clock ht x n basis horth phi Lphi psi psi' U W hderiv helapsed
    hphi hpsi hpsi1 hU
  dsimp only
  have hn : (n : Real) = (Module.finrank Real E : Real) := by
    have h : Module.finrank Real E = n := by
      have h' : Module.finrank Real (TangentSpace I x) = n := by
        simpa only [Fintype.card_fin] using
          (Module.finrank_eq_card_basis (R := Real) basis)
      rwa [show Module.finrank Real (TangentSpace I x) =
        Module.finrank Real E from rfl] at h'
    exact_mod_cast h.symm
  have hS0 : 0 ≤ S0 := le_trans clock.elapsed_pos.le helapsed
  have hB : B = Real.sqrt K + (n : Real) * Real.sqrt K +
      (n : Real) * Real.sqrt K +
      S0 * ((n : Real) ^ 2 * Real.sqrt K +
        (n : Real) ^ 3 * (Real.sqrt K) ^ 2) +
      (n : Real) * Real.sqrt K / 2 := by
    dsimp only [B]
    rw [hn]
  have hCphi' : 2 * (B + 1) * (n : Real) ^ 3 ≤ C := by
    simpa only [← hn] using hCphi
  have hCpsiW' : 2 * B * S0 * (n : Real) ^ 3 +
      4 * B * S0 ^ 2 * (n : Real) ^ 4 +
      B * S0 ^ 2 * (n : Real) ^ 2 +
      4 * B ^ 2 * S0 ^ 2 * (n : Real) ^ 2 + (n : Real) ^ 2 ≤ C := by
    simpa only [← hn] using hCpsiW
  have hCpsiU' : 4 * B * (n : Real) ^ 3 +
      (8 * B + 4) * (n : Real) ^ 4 + B * (n : Real) +
      2 * B * (n : Real) ^ 2 + 1 ≤ C := by
    simpa only [← hn] using hCpsiU
  let R : Fin n → Fin n → Fin n → Fin n → Real := fun a b c d =>
    S.base.rm04 clock.time x
      (vec4 (I := I) (basis a) (basis b) (basis c) (basis d))
  let Ric : Fin n → Fin n → Real := fun a b =>
    metricRicci (I := I) (M := M) (S.base.metric clock.time) x
      (vec2 (I := I) (basis a) (basis b))
  let nablaR : Fin n → Fin n → Fin n → Fin n → Fin n → Real := fun e a b c d =>
    nablaRm04Field (I := I) S clock.time x
      (vec5 (I := I) (basis e) (basis a) (basis b) (basis c) (basis d))
  let nablaRic : Fin n → Fin n → Fin n → Real := fun a b c =>
    metricNablaRic (I := I) (M := M) (S.base.metric clock.time) x
      (vec3 (I := I) (basis a) (basis b) (basis c))
  let nablaP : Fin n → Fin n → Fin n → Fin n → Real := fun e a b c =>
    metricNabla2Ric (I := I) (M := M) (S.base.metric clock.time) x
        (vec4 (I := I) (basis e) (basis a) (basis b) (basis c)) -
      metricNabla2Ric (I := I) (M := M) (S.base.metric clock.time) x
        (vec4 (I := I) (basis e) (basis b) (basis a) (basis c))
  have hdiv : ∀ a b, (∑ e, nablaP e e a b) =
      hamiltonDivPAt (I := I) (S.base.metric clock.time) x
        (vec2 (I := I) (basis a) (basis b)) := by
    intro a b
    have hinvTrace :=
      DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal
      (I := I) (S.base.metric clock.time) basis horth
    have htrace := hamiltonDivPAt_apply_eq_trace_hamiltonNablaP
      (I := I) (S.base.metric clock.time) basis
        (DifferentialGeometry.Tensor0SBundle.identityInvMetric (Idx := Fin n))
        hinvTrace (basis a) (basis b)
    simp only [DifferentialGeometry.Tensor0SBundle.identityInvMetric,
      DifferentialGeometry.Tensor0SBundle.diagonalInvMetric, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] at htrace
    symm
    simpa only [nablaP, hamiltonNablaPField_apply] using htrace
  have hMAt_eq : hamiltonMAt (I := I) clock (S.base.metric clock.time) x =
      hamiltonDivPAt (I := I) (S.base.metric clock.time) x +
        hamiltonCurvatureRicciAt (I := I) (S.base.metric clock.time) x +
        (1 / (2 * clock.elapsed) : Real) •
          metricRicci (I := I) (M := M) (S.base.metric clock.time) x := by
    simpa only [SolutionOn.family] using
      hamiltonMAt_eq_hamiltonDivPAt_add (I := I) S hS clock ht x
  have hMoriginEq : hamiltonMOriginField (I := I) clock.origin clock.time
        (S.base.metric clock.time) x =
      hamiltonDivPAt (I := I) (S.base.metric clock.time) x +
        hamiltonCurvatureRicciAt (I := I) (S.base.metric clock.time) x +
        (1 / (2 * clock.elapsed) : Real) •
          metricRicci (I := I) (M := M) (S.base.metric clock.time) x := by
    rw [hamiltonMOriginField_apply (I := I) clock.origin clock.time
      (S.base.metric clock.time) x]
    simp only [HarnackClock.elapsed]
  have hMoriginMAt : hamiltonMOriginField (I := I) clock.origin clock.time
        (S.base.metric clock.time) x =
      hamiltonMAt (I := I) clock (S.base.metric clock.time) x :=
    hMoriginEq.trans hMAt_eq.symm
  have hMAtOrigin : ∀ A B : TangentSpace I x,
      hamiltonMAt (I := I) clock (S.base.metric clock.time) x
          (vec2 (I := I) A B) =
        hamiltonMOriginField (I := I) clock.origin clock.time
          (S.base.metric clock.time) x (vec2 (I := I) A B) :=
    fun A B => (congrArg (fun F => F (vec2 (I := I) A B)) hMoriginMAt).symm
  have hMcomp : hamiltonMComponent clock R Ric (fun i j => ∑ e, nablaP e e i j) =
      fun a b => hamiltonMOriginField (I := I) clock.origin clock.time
        (S.base.metric clock.time) x (vec2 (I := I) (basis a) (basis b)) := by
    funext a b
    simp_rw [hdiv]
    calc
      hamiltonMComponent clock R Ric
          (fun i j => hamiltonDivPAt (I := I)
            (S.base.metric clock.time) x
              (vec2 (I := I) (basis i) (basis j))) a b =
          hamiltonMAt (I := I) clock (S.base.metric clock.time) x
            (vec2 (I := I) (basis a) (basis b)) := by
        change hamiltonMComponent clock
            (fun i j k l => metricRm04 (I := I) (M := M)
              (S.family.metric clock.time) x
              (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
            (fun i j => metricRicci (I := I) (M := M)
              (S.family.metric clock.time) x
              (vec2 (I := I) (basis i) (basis j)))
            (fun i j => hamiltonDivPAt (I := I)
              (S.family.metric clock.time) x
              (vec2 (I := I) (basis i) (basis j))) a b = _
        exact hamiltonMComponent_eq_hamiltonMAt_orthonormal
          (I := I) S hS clock ht x basis horth a b
      _ = hamiltonMOriginField (I := I) clock.origin clock.time
          (S.base.metric clock.time) x
            (vec2 (I := I) (basis a) (basis b)) :=
        hMAtOrigin (basis a) (basis b)
  have hPcomp : hamiltonPComponent nablaRic =
      fun a b c => hamiltonPField (I := I) (S.base.metric clock.time) x
        (vec3 (I := I) (basis a) (basis b) (basis c)) := by
    funext a b c
    simp only [nablaRic, hamiltonPComponent, hamiltonPField_apply,
      hamiltonPAt_apply]
  have hRm : Rm04Symm R := by
    simpa only [R] using
      hamilton_rm_components_symm (I := I) S ⟨clock.time, ht⟩ x basis
  have hNablaRm : ∀ e, Rm04PairSymm (nablaR e) := by
    intro e
    simpa only [nablaR] using
      hamilton_nabla_rm_components_pair_symm
        (I := I) S clock.time x basis horth e
  have hRic : ∀ a b, Ric a b = Ric b a := by
    intro a b
    simpa only [Ric, metricRicci_apply] using
      metricRicciAt_symm (I := I) (M := M) (S.base.metric clock.time) x
        (basis a) (basis b)
  have hNablaRic : ∀ a b c, nablaRic a b c = nablaRic a c b := by
    intro a b c
    simpa only [nablaRic] using
      metricNablaRic_last_two_symm (I := I) (M := M)
        (S.base.metric clock.time) x (basis a) (basis b) (basis c)
  have hTrace : curvatureRicciTraceComponents R Ric := by
    simpa only [R, Ric] using
      hamilton_curvature_ricci_trace_components
        (I := I) S ⟨clock.time, ht⟩ x basis horth
  have hContract : contractedCurvatureDerivativeComponents nablaR nablaRic := by
    simpa only [nablaR, nablaRic] using
      hamilton_contracted_curvature_derivative_components
        (I := I) S clock.time x basis horth
  have hNablaPSkew : ∀ e a b c, nablaP e a b c = -nablaP e b a c := by
    intro e a b c
    dsimp only [nablaP]
    ring
  have hM : ∀ a b, hamiltonMComponent clock R Ric
        (fun i j => ∑ e, nablaP e e i j) a b =
      hamiltonMComponent clock R Ric (fun i j => ∑ e, nablaP e e i j) b a := by
    intro a b
    have hsym : hamiltonMAt (I := I) clock (S.base.metric clock.time) x
          (vec2 (I := I) (basis a) (basis b)) =
        hamiltonMAt (I := I) clock (S.base.metric clock.time) x
          (vec2 (I := I) (basis b) (basis a)) := by
      simpa only [SolutionOn.family] using
        hamiltonMAt_symm (I := I) S clock ht x (basis a) (basis b)
    rw [hMcomp]
    exact (hMAtOrigin (basis a) (basis b)).symm.trans
      (hsym.trans (hMAtOrigin (basis b) (basis a)))
  have heq := hamiltonPerturbedBlock_heat_product_eq_j_add_sigma_square
    clock R Ric nablaR nablaRic nablaP (fun _ _ _ => 0)
    phi Lphi psi psi' U W hRm hNablaRm hRic hNablaRic hTrace hContract
    hNablaPSkew hM hU
  have hmain := hamiltonPerturbedBlock_reaction_ge_of_curvature_derivative_bound
    (I := I) S hS clock ht x basis horth K S0 B C phi Lphi psi psi'
    hS0 helapsed hderiv hB hCphi' hCpsiW' hCpsiU' U W hU hphi hpsi hpsi1
  dsimp only at hmain
  rw [heq] at hmain
  rw [hPcomp, hMcomp] at hmain
  exact hmain

end DifferentialGeometry.PDE.RicciFlow
