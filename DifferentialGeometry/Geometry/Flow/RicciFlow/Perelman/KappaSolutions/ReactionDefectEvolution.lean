import DifferentialGeometry.Analysis.ODE.HamiltonIvey
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Scalar.Weak
import DifferentialGeometry.Analysis.Parabolic.Operator
import DifferentialGeometry.Geometry.Curvature.DimensionThree.Algebra.Pinching
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReactionDefectVanishing

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem ricciReactionDefectAt_eq_curvatureReactionSumSquares3
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    (lambda mu nu : Real)
    (hdiag : RicciDiagAt (I := I)
      (metricRicciAt (I := I) (M := M) g x)
      (metricScalarAt (I := I) (M := M) g x)
      ((mu + nu) / 2) ((lambda + nu) / 2) ((lambda + mu) / 2) basis) :
    ricciReactionDefectAt (I := I) g x =
      curvatureReactionSumSquares3 lambda mu nu := by
  rw [ricciReactionDefectAt_eq_curvatureReactionPolynomial3 (I := I) (M := M) g x basis horth
    lambda mu nu hdiag, curvatureReactionPolynomial3_eq_sum_squares]

noncomputable def curvatureReactionDefectDirectional3
    (lambda mu nu dlambda dmu dnu : Real) : Real :=
  ((2 * lambda * mu ^ 2 - 2 * lambda * mu * nu + 2 * lambda * nu ^ 2 -
      mu ^ 2 * nu - mu * nu ^ 2) / 4) * dlambda +
    ((2 * mu * lambda ^ 2 - 2 * lambda * mu * nu - lambda ^ 2 * nu -
      lambda * nu ^ 2 + 2 * mu * nu ^ 2) / 4) * dmu +
      ((2 * nu * lambda ^ 2 + 2 * nu * mu ^ 2 - lambda ^ 2 * mu -
        lambda * mu ^ 2 - 2 * lambda * mu * nu) / 4) * dnu

noncomputable def curvatureReactionDefectRate3 (lambda mu nu : Real) : Real :=
  curvatureReactionDefectDirectional3 lambda mu nu
    (lambda + lambda ^ 2 + mu * nu) (mu + mu ^ 2 + lambda * nu)
    (nu + nu ^ 2 + lambda * mu)

theorem curvatureReactionDefectDirectional3_eq_directional_derivative
    (lambda mu nu dlambda dmu dnu : Real) :
    curvatureReactionDefectDirectional3 lambda mu nu dlambda dmu dnu =
      dlambda * ((2 * lambda * mu ^ 2 - 2 * lambda * mu * nu + 2 * lambda * nu ^ 2 -
          mu ^ 2 * nu - mu * nu ^ 2) / 4) +
        dmu * ((2 * mu * lambda ^ 2 - 2 * lambda * mu * nu - lambda ^ 2 * nu -
          lambda * nu ^ 2 + 2 * mu * nu ^ 2) / 4) +
          dnu * ((2 * nu * lambda ^ 2 + 2 * nu * mu ^ 2 - lambda ^ 2 * mu -
            lambda * mu ^ 2 - 2 * lambda * mu * nu) / 4) := by
  unfold curvatureReactionDefectDirectional3
  ring

theorem curvatureReactionDefectRate3_add_four_mul (lambda mu nu : Real) :
    curvatureReactionDefectRate3 lambda mu nu =
      4 * curvatureReactionSumSquares3 lambda mu nu +
        (lambda * mu + lambda * nu + mu * nu) *
          (mu * (lambda - nu) ^ 2 + nu * (mu - lambda) ^ 2 +
            lambda * (nu - mu) ^ 2) / 4 := by
  unfold curvatureReactionDefectRate3 curvatureReactionDefectDirectional3
    curvatureReactionSumSquares3
  ring

theorem four_mul_curvatureReactionSumSquares3_le_curvatureReactionDefectRate3
    {lambda mu nu : Real} (hl : 0 ≤ lambda) (hm : 0 ≤ mu) (hn : 0 ≤ nu) :
    4 * curvatureReactionSumSquares3 lambda mu nu ≤
      curvatureReactionDefectRate3 lambda mu nu := by
  rw [curvatureReactionDefectRate3_add_four_mul]
  have h1 : 0 ≤ lambda * mu + lambda * nu + mu * nu := by nlinarith
  have h2 : 0 ≤ mu * (lambda - nu) ^ 2 + nu * (mu - lambda) ^ 2 +
      lambda * (nu - mu) ^ 2 :=
    add_nonneg (add_nonneg (mul_nonneg hm (sq_nonneg _)) (mul_nonneg hn (sq_nonneg _)))
      (mul_nonneg hl (sq_nonneg _))
  have h3 : 0 ≤ (lambda * mu + lambda * nu + mu * nu) *
      (mu * (lambda - nu) ^ 2 + nu * (mu - lambda) ^ 2 +
        lambda * (nu - mu) ^ 2) / 4 :=
    div_nonneg (mul_nonneg h1 h2) (by norm_num)
  linarith

theorem curvatureReactionDefectRate3_pos_of_sumSquares3_pos
    {lambda mu nu : Real} (hl : 0 ≤ lambda) (hm : 0 ≤ mu) (hn : 0 ≤ nu)
    (hpos : 0 < curvatureReactionSumSquares3 lambda mu nu) :
    0 < curvatureReactionDefectRate3 lambda mu nu :=
  lt_of_lt_of_le (by linarith)
    (four_mul_curvatureReactionSumSquares3_le_curvatureReactionDefectRate3 hl hm hn)

theorem curvatureReactionDefectRate3_eq_zero_of_sumSquares3_eq_zero
    {lambda mu nu : Real} (h : curvatureReactionSumSquares3 lambda mu nu = 0) :
    curvatureReactionDefectRate3 lambda mu nu = 0 := by
  have hcases :=
    (curvatureReactionSumSquares3_eq_zero_iff_of_const_or_two_zero lambda mu nu).mp h
  rw [curvatureReactionDefectRate3_add_four_mul, h, mul_zero, zero_add]
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
    ring
  · rw [h1, h2]
    ring
  · rw [h1, h2]
    ring
  · rw [h1, h2]
    ring

theorem curvatureReactionDefectRate3_one_one_zero :
    curvatureReactionDefectRate3 1 1 0 = 3 / 2 := by
  rw [curvatureReactionDefectRate3_add_four_mul]
  norm_num [curvatureReactionSumSquares3]

theorem curvatureReactionDefectRate3_one_zero_zero :
    curvatureReactionDefectRate3 1 0 0 = 0 :=
  curvatureReactionDefectRate3_eq_zero_of_sumSquares3_eq_zero
    (curvatureReactionSumSquares3_one_zero_zero)

theorem not_curvatureReactionDefectRate3_one_one_zero_add_mul_le_zero {c : Real}
    (hc : 0 ≤ c) :
    ¬ (curvatureReactionDefectRate3 1 1 0 +
      c * curvatureReactionSumSquares3 1 1 0 ≤ 0) := by
  rw [curvatureReactionDefectRate3_one_one_zero, curvatureReactionSumSquares3_one_one_zero]
  intro h
  nlinarith

theorem hasDerivWithinAt_curvatureReactionSumSquares3_comp
    {lambda mu nu : Real → Real} {J : Set Real} {t dlambda dmu dnu : Real}
    (hl : HasDerivWithinAt lambda dlambda J t) (hm : HasDerivWithinAt mu dmu J t)
    (hn : HasDerivWithinAt nu dnu J t) :
    HasDerivWithinAt (fun s => curvatureReactionSumSquares3 (lambda s) (mu s) (nu s))
      (curvatureReactionDefectDirectional3 (lambda t) (mu t) (nu t)
        dlambda dmu dnu) J t := by
  have hl1 : HasDerivWithinAt (fun s => lambda s) dlambda J t := hl
  have hm1 : HasDerivWithinAt (fun s => mu s) dmu J t := hm
  have hn1 : HasDerivWithinAt (fun s => nu s) dnu J t := hn
  have hmn : HasDerivWithinAt (fun s => mu s - nu s) (dmu - dnu) J t := hm1.sub hn1
  have hln : HasDerivWithinAt (fun s => lambda s - nu s) (dlambda - dnu) J t := hl1.sub hn1
  have hlm : HasDerivWithinAt (fun s => lambda s - mu s) (dlambda - dmu) J t := hl1.sub hm1
  have h1 := (hl1.pow 2).mul (hmn.pow 2)
  have h2 := (hm1.pow 2).mul (hln.pow 2)
  have h3 := (hn1.pow 2).mul (hlm.pow 2)
  have h4 := ((h1.add h2).add h3).div_const 8
  have hnorm : HasDerivWithinAt
      (fun x => (lambda x ^ 2 * (mu x - nu x) ^ 2 +
          mu x ^ 2 * (lambda x - nu x) ^ 2 +
            nu x ^ 2 * (lambda x - mu x) ^ 2) / 8)
      ((2 * lambda t * dlambda * (mu t - nu t) ^ 2 +
          lambda t ^ 2 * (2 * (mu t - nu t) * (dmu - dnu)) +
            (2 * mu t * dmu * (lambda t - nu t) ^ 2 +
              mu t ^ 2 * (2 * (lambda t - nu t) * (dlambda - dnu))) +
              (2 * nu t * dnu * (lambda t - mu t) ^ 2 +
                nu t ^ 2 * (2 * (lambda t - mu t) * (dlambda - dmu)))) / 8) J t := by
    simpa only [Pi.pow_apply, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.div_apply,
      Nat.reduceSub, Nat.cast_ofNat, pow_one] using h4
  have hfun : (fun s => curvatureReactionSumSquares3 (lambda s) (mu s) (nu s)) =
      (fun x => (lambda x ^ 2 * (mu x - nu x) ^ 2 +
          mu x ^ 2 * (lambda x - nu x) ^ 2 +
            nu x ^ 2 * (lambda x - mu x) ^ 2) / 8) := by
    funext s
    unfold curvatureReactionSumSquares3
    ring
  have hderiv :
      (2 * lambda t * dlambda * (mu t - nu t) ^ 2 +
          lambda t ^ 2 * (2 * (mu t - nu t) * (dmu - dnu)) +
            (2 * mu t * dmu * (lambda t - nu t) ^ 2 +
              mu t ^ 2 * (2 * (lambda t - nu t) * (dlambda - dnu))) +
              (2 * nu t * dnu * (lambda t - mu t) ^ 2 +
                nu t ^ 2 * (2 * (lambda t - mu t) * (dlambda - dmu)))) / 8 =
      curvatureReactionDefectDirectional3 (lambda t) (mu t) (nu t) dlambda dmu dnu := by
    unfold curvatureReactionDefectDirectional3
    ring
  rw [hfun]
  simpa [hderiv] using hnorm

end DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

open DifferentialGeometry.Analysis.ODE
open scoped _root_.Matrix.Norms.Elementwise

theorem hasDerivWithinAt_curvatureReactionSumSquares3_of_normalized_curvature_reaction_ode
    {A : Real → Matrix (Fin 3) (Fin 3) Real} {J : Set Real} {t : Real}
    (hA : IsIntegralCurveOn A (fun _ C => C + curvatureOperatorReaction3 C) J)
    (ht : t ∈ J)
    (hdiag : A t = Matrix.diagonal ![A t 0 0, A t 1 1, A t 2 2]) :
    HasDerivWithinAt
      (fun s => DifferentialGeometry.Geometry.Curvature.curvatureReactionSumSquares3
        (A s 0 0) (A s 1 1) (A s 2 2))
      (DifferentialGeometry.Geometry.Curvature.curvatureReactionDefectRate3
        (A t 0 0) (A t 1 1) (A t 2 2)) J t := by
  have h := hasDerivWithinAt_diagonal_of_normalized_curvature_reaction_ode hA ht hdiag
  have h0 : HasDerivWithinAt (fun s => A s 0 0)
      (A t 0 0 + A t 0 0 ^ 2 + A t 1 1 * A t 2 2) J t := by
    simpa using h 0
  have h1 : HasDerivWithinAt (fun s => A s 1 1)
      (A t 1 1 + A t 1 1 ^ 2 + A t 0 0 * A t 2 2) J t := by
    simpa using h 1
  have h2 : HasDerivWithinAt (fun s => A s 2 2)
      (A t 2 2 + A t 2 2 ^ 2 + A t 0 0 * A t 1 1) J t := by
    simpa using h 2
  exact DifferentialGeometry.Geometry.Curvature.hasDerivWithinAt_curvatureReactionSumSquares3_comp
    h0 h1 h2

end DifferentialGeometry.Geometry.Curvature.DimensionThree

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Operator
open Bundle

theorem le_zero_of_forall_exp_mul_le {u c B : ℝ} (hc : 0 < c)
    (h : ∀ a : ℝ, a < 0 → u ≤ Real.exp (c * a) * B) : u ≤ 0 := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  by_cases hBε : B ≤ ε
  · have h1 := h (-1) (by norm_num)
    have hexp : Real.exp (c * (-1)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    have h2 : Real.exp (c * (-1)) * B ≤ ε := by
      by_cases hB0 : B ≤ 0
      · have h : Real.exp (c * (-1)) * B ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos (c * (-1))).le hB0
        linarith
      · have hB0' : 0 < B := lt_of_not_ge hB0
        have h : Real.exp (c * (-1)) * B ≤ B :=
          mul_le_of_le_one_left hB0'.le hexp
        linarith
    linarith
  · have hεB : ε < B := lt_of_not_ge hBε
    have hBpos : 0 < B := lt_trans hε hεB
    have hratio : 0 < ε / B := div_pos hε hBpos
    have hratio1 : ε / B < 1 := (div_lt_one hBpos).mpr hεB
    have hlog : Real.log (ε / B) < 0 := Real.log_neg hratio hratio1
    have haneq : Real.log (ε / B) / c - 1 < 0 := by
      have hquot : Real.log (ε / B) / c < 0 := div_neg_of_neg_of_pos hlog hc
      linarith
    have hbound := h (Real.log (ε / B) / c - 1) haneq
    have hval : Real.exp (c * (Real.log (ε / B) / c - 1)) * B = ε * Real.exp (-c) := by
      have harg : c * (Real.log (ε / B) / c - 1) = Real.log (ε / B) - c := by
        rw [mul_sub, mul_one, ← mul_div_assoc, mul_div_cancel_left₀ _ (ne_of_gt hc)]
      rw [harg, Real.exp_sub, Real.exp_log hratio, Real.exp_neg]
      field_simp
    rw [hval] at hbound
    have hlt : ε * Real.exp (-c) < ε := by
      have hone : Real.exp (-c) < 1 := by
        rw [Real.exp_lt_one_iff]
        linarith
      nlinarith
    linarith

section ReactionDefectEvolution

universe u₁ uE₁ uH₁

variable {E : Type uE₁} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H : Type uH₁} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {D : RealTimeInterval} (F : PointedFlowData.{u₁, uE₁, uH₁} (I := I) D)

local instance reactionDefectEvolutionTopology : TopologicalSpace F.M := F.topology
local instance reactionDefectEvolutionCharted : ChartedSpace H F.M := F.charted
local instance reactionDefectEvolutionSmooth : IsManifold I ∞ F.M := F.smooth
local instance reactionDefectEvolutionC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance reactionDefectEvolutionC2 : IsManifold I 2 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance reactionDefectEvolutionT2 : T2Space F.M := F.t2
local instance reactionDefectEvolutionSigma : SigmaCompactSpace F.M := F.sigmaCompact

noncomputable def reactionDefectAtTime (t : ℝ) (x : F.M) : ℝ :=
  ricciReactionDefectAt (I := I) (F.S.base.metric t) x

def FarPastReactionDefectComparison (c B : ℝ) : Prop :=
  ∀ ⦃a b : ℝ⦄, a ≤ b → b ≤ 0 → a ∈ D.regular → ∀ x : F.M,
    reactionDefectAtTime F b x ≤ Real.exp (c * (a - b)) * B

noncomputable def ReactionDefectParabolicDecay (T c B : ℝ) : Prop :=
  ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : F.M,
    -c * (Real.exp (-c * t) * B - reactionDefectAtTime F t x) ≤
      parabolicOperatorWithDrift (I := I) (flowG (I := I) F.S) T
        (fun _ y => (0 : TangentSpace I y))
        (fun s y => Real.exp (-c * s) * B - reactionDefectAtTime F s y) t x

theorem reactionDefectAtTime_le_exp_mul_of_parabolicDecay [CompactSpace F.M]
    {T c B : ℝ} (hc : 0 ≤ c) (hdecay : ReactionDefectParabolicDecay F T c B)
    (hcont : ContinuousOn (fun p : ℝ × F.M =>
      Real.exp (-c * p.1) * B - reactionDefectAtTime F p.1 p.2)
        (spacetimeSlab (M := F.M) T))
    (htime : ∀ t ∈ Set.Icc 0 T, ∀ x : F.M,
      DifferentiableWithinAt ℝ
        (fun s : ℝ => Real.exp (-c * s) * B - reactionDefectAtTime F s x)
        (Set.Icc 0 T) t)
    (hmdiff : ∀ t ∈ Set.Icc 0 T, ∀ x : F.M,
      MDifferentiableAt I 𝓘(ℝ, ℝ)
        (fun y : F.M => Real.exp (-c * t) * B - reactionDefectAtTime F t y) x)
    (hgrad : ∀ t ∈ Set.Icc 0 T, ∀ x : F.M,
      MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun y : F.M => TotalSpace.mk' E y
          (gradientFun (I := I) ((flowG (I := I) F.S).metric t)
            (fun z : F.M => Real.exp (-c * t) * B - reactionDefectAtTime F t z) y)) x)
    (hinit : ∀ x : F.M, 0 ≤ B - reactionDefectAtTime F 0 x) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : F.M,
      reactionDefectAtTime F t x ≤ Real.exp (-c * t) * B := by
  have h := scalar_weak_maximum_principle_supersolution_lower_bound (I := I) (M := F.M)
    (flowG (I := I) F.S) T (fun _ y => (0 : TangentSpace I y))
    (fun s y => Real.exp (-c * s) * B - reactionDefectAtTime F s y) 0
    (by simpa using hcont) (by simpa using htime) (by simpa using hmdiff)
    (by simpa using hgrad) (by simpa using hinit) ?_
  · intro t ht x
    have hv := h t ht x
    have hsub : 0 ≤ Real.exp (-c * t) * B - reactionDefectAtTime F t x := by simpa using hv
    linarith
  · intro t ht x hneg
    rcases eq_or_lt_of_le ht.1 with ht0 | htpos
    · rw [← ht0] at hneg
      simp only [mul_zero, Real.exp_zero, one_mul] at hneg
      exact absurd (hinit x) (not_le_of_gt hneg)
    · have hd := hdecay t ht htpos x
      have hnn : 0 ≤ -c * (Real.exp (-c * t) * B - reactionDefectAtTime F t x) :=
        mul_nonneg_of_nonpos_of_nonpos (by linarith) hneg.le
      simpa only [sub_zero] using le_trans hnn hd

theorem reactionDefectAtTime_terminal_eq_zero_of_farPastComparison
    {c B : ℝ} (hc : 0 < c)
    (hreg : ∀ a : ℝ, a < 0 → a ∈ D.regular)
    (hcmp : FarPastReactionDefectComparison F c B)
    (hnonneg : ∀ x : F.M, 0 ≤ reactionDefectAtTime F 0 x) :
    ∀ x : F.M, reactionDefectAtTime F 0 x = 0 := by
  intro x
  refine le_antisymm ?_ (hnonneg x)
  refine le_zero_of_forall_exp_mul_le (B := B) hc fun a ha => ?_
  have h := hcmp (a := a) (b := 0) (le_of_lt ha) le_rfl (hreg a ha) x
  simpa using h

theorem terminalReactionDefectVanishing_of_kLim_farPastComparison
    {kappa c B : ℝ} (hK : KLim (I := I) kappa F) (hc : 0 < c)
    (hcmp : FarPastReactionDefectComparison F c B)
    (hnonneg : ∀ x : F.M, 0 ≤ reactionDefectAtTime F 0 x) :
    TerminalReactionDefectVanishing (I := I) F := by
  intro x
  have h := reactionDefectAtTime_terminal_eq_zero_of_farPastComparison (I := I) F hc
    (fun a ha => by rw [hK.regular_eq]; exact ha) hcmp hnonneg x
  simpa only [TerminalReactionDefectVanishing, reactionDefectAtTime] using h

end ReactionDefectEvolution

section ReactionDefectTerminal

universe u₂ uE₂ uH₂

variable {E : Type uE₂} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H : Type uH₂} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {D : RealTimeInterval} (F : PointedFlowData.{u₂, uE₂, uH₂} (I := I) D)

local instance reactionDefectTerminalTopology : TopologicalSpace F.M := F.topology
local instance reactionDefectTerminalCharted : ChartedSpace H F.M := F.charted
local instance reactionDefectTerminalSmooth : IsManifold I ∞ F.M := F.smooth
local instance reactionDefectTerminalC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance reactionDefectTerminalC2 : IsManifold I 2 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance reactionDefectTerminalT2 : T2Space F.M := F.t2
local instance reactionDefectTerminalSigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem nullPlaneReactionDefectVanishing_of_kLim_farPastComparison
    {kappa c B : ℝ} (hK : KLim (I := I) kappa F) (hc : 0 < c)
    (hcmp : FarPastReactionDefectComparison (I := I) F c B)
    (hnonneg : ∀ x : F.M, 0 ≤ reactionDefectAtTime (I := I) F 0 x) :
    NullPlaneReactionDefectVanishing (I := I) F :=
  nullPlaneReactionDefectVanishing_of_terminalReactionDefectVanishing (I := I) F
    (terminalReactionDefectVanishing_of_kLim_farPastComparison (I := I) F hK hc hcmp hnonneg)

end ReactionDefectTerminal

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
