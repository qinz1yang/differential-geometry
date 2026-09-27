import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.FiniteDistanceCutoff
import DifferentialGeometry.Analysis.Parabolic.Energy.ClockSupportEstimate
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.EndpointRiemannNorm
import DifferentialGeometry.Geometry.Curvature.ScalarGradientNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.Evolution.SolutionHeatEquation
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.Analysis.Parabolic DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow

private def curvatureCutoffEnergyConstant (n : ℕ) : ℝ :=
  Real.exp (2 * rmTowerCost n 1) * (1 + 18 * finiteDistanceCutoffConstant n) *
    (1 + rmTowerCost n 0 + 5 * finiteDistanceCutoffConstant n)

private theorem curvatureCutoffEnergyConstant_pos (n : ℕ) :
    0 < curvatureCutoffEnergyConstant n := by
  have hcut := finiteDistanceCutoffConstant_pos n
  have hcost := rmTowerCost_nonneg n 0
  unfold curvatureCutoffEnergyConstant
  positivity

def fixedBallCurvatureGradientConstant (n : ℕ) : ℝ :=
  curvatureCutoffEnergyConstant n * (4 * Real.exp ((n : ℝ) ^ 2)) ^ 6

theorem fixedBallCurvatureGradientConstant_pos (n : ℕ) :
    0 < fixedBallCurvatureGradientConstant n := by
  have hc := curvatureCutoffEnergyConstant_pos n
  unfold fixedBallCurvatureGradientConstant
  positivity

def fixedBallScalarGradientConstant (n : ℕ) : ℝ :=
  (n : ℝ) ^ 3 * Real.sqrt (fixedBallCurvatureGradientConstant n)

theorem fixedBallScalarGradientConstant_nonneg (n : ℕ) :
    0 ≤ fixedBallScalarGradientConstant n := by
  unfold fixedBallScalarGradientConstant
  positivity

private theorem first_two_reactions_le
    {v u K c₀ c₁ : ℝ} (hv : 0 ≤ v) (hu : 0 ≤ u)
    (hK : 0 ≤ K) (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (hvK : v ≤ K ^ 2) :
    c₀ * Real.sqrt v * Real.sqrt v * Real.sqrt v ≤ c₀ * K ^ 3 ∧
      c₁ * Real.sqrt v * Real.sqrt u * Real.sqrt u +
        c₁ * Real.sqrt u * Real.sqrt v * Real.sqrt u ≤ 2 * c₁ * K * u := by
  have hroot : Real.sqrt v ≤ K :=
    (Real.sqrt_le_sqrt hvK).trans_eq (Real.sqrt_sq hK)
  constructor
  · calc
      _ = c₀ * v * Real.sqrt v := by rw [mul_assoc c₀, Real.mul_self_sqrt hv]
      _ ≤ c₀ * K ^ 2 * K :=
        mul_le_mul (mul_le_mul_of_nonneg_left hvK hc₀) hroot
          (Real.sqrt_nonneg _) (mul_nonneg hc₀ (sq_nonneg K))
      _ = _ := by ring
  · calc
      _ = 2 * c₁ * Real.sqrt v * (Real.sqrt u * Real.sqrt u) := by ring
      _ = 2 * c₁ * Real.sqrt v * u := by rw [Real.mul_self_sqrt hu]
      _ ≤ 2 * c₁ * K * u :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hroot (by positivity)) hu

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [NeZero (Module.finrank ℝ E)]
  {D : RealTimeInterval}

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [SigmaCompactSpace M] [NeZero (Module.finrank ℝ E)] in
private theorem curvature_norm_continuous_regular
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (L : ℝ) (hL : 0 < L) (hreg : Icc 0 L ⊆ D.regular) (k : ℕ) :
    ContinuousOn (fun p : ℝ × M => nablaKRm04NormSqIntrinsic S k p.1 p.2)
      (Icc 0 L ×ˢ (univ : Set M)) := by
  have hgram : ∀ (y₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (S.base.metric p.1) y₀ p.2 i j)
        (Icc 0 L ×ˢ (trivializationAt E (TangentSpace I) y₀).baseSet) := by
    intro y₀ i j
    let e := trivializationAt E (TangentSpace I : M → Type _) y₀
    let basis := DifferentialGeometry.Tensor.Coordinates.chartModelBasis E
    let frame : Fin (Module.finrank ℝ E) → ∀ y, TangentSpace I y := e.localFrame basis
    have hframe : IsLocalFrameOn I E ∞ frame e.baseSet := by
      simpa only [frame] using e.isLocalFrameOn_localFrame_baseSet I ∞ basis
    have hcomp := (hS.smoothMetric.frameCompSmooth frame hframe i j).mono
      (prod_mono hreg (Subset.refl _))
    refine hcomp.congr ?_
    intro p hp
    have hframe_eq (j : Fin (Module.finrank ℝ E)) :
        frame j p.2 = DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) y₀ j p.2 := by
      dsimp only [frame]
      rw [e.localFrame_apply_of_mem_baseSet basis hp.2]
      change (e.linearEquivAt ℝ p.2 hp.2).symm (basis j) =
        e.symmL ℝ p.2 ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)
      dsimp only [basis]
      rw [e.linearEquivAt_symm_apply, e.symmL_apply hp.2]
    simp only [DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply, SolutionOn.family_metric]
    rw [hframe_eq i, hframe_eq j]
  have hh := (covariantRiemannNormSq_contMDiffOn S.base.metric (Icc 0 L)
    (uniqueDiffOn_Icc hL) hgram k).continuousOn
  apply hh.congr
  intro p _
  dsimp only
  unfold nablaKRm04NormSqIntrinsic
  rw [nablaKRm_eq_iterCov]
  rfl

omit [SigmaCompactSpace M] in
private theorem curvature_energy_of_finite_cutoff
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (R : ℝ) (hR : 0 < R) (hreg : Icc 0 (R ^ 2) ⊆ D.regular)
    (χ : ℝ → M → ℝ) (Cpt : Set M) (hCpt : IsCompact Cpt)
    (hχcont : ContinuousOn (fun p : ℝ × M => χ p.1 p.2)
      (spacetimeSlab (M := M) (R ^ 2)))
    (hχrange : ∀ s ∈ Icc 0 (R ^ 2), ∀ x, χ s x ∈ Icc (0 : ℝ) 1)
    (hχout : ∀ s ∈ Icc 0 (R ^ 2), ∀ x ∉ Cpt, χ s x = 0)
    (hcut : ∀ s ∈ Icc 0 (R ^ 2), 0 < s → ∀ x, 0 < χ s x →
      Nonempty (ShiCutoffLowerSupportAt (I := I) (flowG S) (R ^ 2)
        (finiteDistanceCutoffConstant (Module.finrank ℝ E) / R ^ 2) χ s x))
    (hzero : ∀ s ∈ Icc 0 (R ^ 2), ∀ x, 0 < χ s x →
      nablaKRm04NormSqIntrinsic S 0 s x ≤ (1 / R ^ 2) ^ 2)
    (O : M) (hχone : χ (R ^ 2) O = 1) :
    nablaKRm04NormSqIntrinsic S 1 (R ^ 2) O ≤
      curvatureCutoffEnergyConstant (Module.finrank ℝ E) / R ^ 6 := by
  let n := Module.finrank ℝ E
  let L := R ^ 2
  let K := 1 / R ^ 2
  let ε := finiteDistanceCutoffConstant n / R ^ 2
  let a := 2 * rmTowerCost n 1 * K
  let b := rmTowerCost n 0 * K ^ 3
  let A := 1 + 18 * finiteDistanceCutoffConstant n
  let W := nablaKRm04NormSqIntrinsic S
  have hL : 0 < L := sq_pos_of_pos hR
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hε : 0 ≤ ε := by
    exact div_nonneg (finiteDistanceCutoffConstant_pos n).le (sq_nonneg R)
  have ha : 0 ≤ a := by
    exact mul_nonneg (mul_nonneg (by norm_num) (rmTowerCost_nonneg n 1)) hK
  have hb : 0 ≤ b := mul_nonneg (rmTowerCost_nonneg n 0) (pow_nonneg hK 3)
  have hA : 1 + 18 * ε * L ≤ A := by
    dsimp only [ε, L, A]
    field_simp [hR.ne']
    rfl
  have hslab : Icc 0 L ⊆ D.carrier := fun s hs => D.regular_subset (hreg hs)
  have hnonneg (j : ℕ) (s : ℝ) (x : M) : 0 ≤ W j s x :=
    nablaKRm04NormSqIntrinsic_nonneg S j s x
  have htime (j : ℕ) (s : ℝ) (hs : s ∈ Icc 0 L) (x : M) :
      DifferentiableWithinAt ℝ (fun t => W j t x) (Icc 0 L) s := by
    obtain ⟨d, hd, _⟩ := towerHeatBoundOn_of_solution S hS j ⟨s, hreg hs⟩ x
    exact (hd.mono hslab).differentiableWithinAt
  have hcont (j : ℕ) :
      ContinuousOn (fun p : ℝ × M => W j p.1 p.2) (Icc 0 L ×ˢ Cpt) :=
    (curvature_norm_continuous_regular S hS L hL hreg j).mono
      (prod_mono (Subset.refl _) (subset_univ _))
  have hspace (j : ℕ) (s : ℝ) (x : M) :
      ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (W j s) y :=
    Eventually.of_forall fun y =>
      (nablaKNorm_smooth S s j).contMDiffAt.mdifferentiableAt (by simp)
  have hgrad (j : ℕ) (s : ℝ) (x : M) :
      MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (T% (gradientFun (I := I) (S.base.metric s) (W j s))) x :=
    gradientFun_mdiffAt (S.base.metric s) (nablaKNorm_smooth S s j) x
  have hheat (j : ℕ) (s : ℝ) (hs : s ∈ Icc 0 L) (x : M) :
      parabolicOperatorWithDrift (flowG S) L (fun _ _ => 0) (W j) s x ≤
        -2 * W (j + 1) s x + towerReactionSum W (rmTowerCost n j) j s x := by
    obtain ⟨d, hd, hle⟩ := towerHeatBoundOn_of_solution S hS j ⟨s, hreg hs⟩ x
    have hderiv := (hd.mono hslab).derivWithin ((uniqueDiffOn_Icc hL) s hs)
    rw [parabolicOperatorWithDrift_eq, hderiv, heatOperatorWithDrift_zero_drift]
    change d - nablaKNormLap S j s x ≤ _
    exact sub_le_iff_le_add.mpr (by simpa only [add_comm] using hle)
  have hreaction (s : ℝ) (hs : s ∈ Icc 0 L) (x : M) (hx : 0 < χ s x) :
      towerReactionSum W (rmTowerCost n 0) 0 s x ≤ b ∧
        towerReactionSum W (rmTowerCost n 1) 1 s x ≤ a * W 1 s x := by
    have hr := first_two_reactions_le
      (hnonneg 0 s x) (hnonneg 1 s x) hK
      (rmTowerCost_nonneg n 0) (rmTowerCost_nonneg n 1) (hzero s hs x hx)
    simpa [towerReactionSum, Finset.sum_range_succ, a, b] using hr
  have hPu (s : ℝ) (hs : s ∈ Icc 0 L) (_ : 0 < s) (x : M) (hx : 0 < χ s x) :
      parabolicOperatorWithDrift (flowG S) L (fun _ _ => 0) (W 1) s x ≤
        -2 * W 2 s x + a * W 1 s x :=
    (hheat 1 s hs x).trans (add_le_add le_rfl (hreaction s hs x hx).2)
  have hPv (s : ℝ) (hs : s ∈ Icc 0 L) (_ : 0 < s) (x : M) (hx : 0 < χ s x) :
      parabolicOperatorWithDrift (flowG S) L (fun _ _ => 0) (W 0) s x ≤
        -2 * W 1 s x + b :=
    (hheat 0 s hs x).trans (add_le_add le_rfl (hreaction s hs x hx).1)
  have hbound := DifferentialGeometry.Analysis.upper_energy_bound_of_clock_cutoff
    (G := flowG S) (T := L) (K := K) (ε := ε) (a := a) (b := b) (A := A)
    (hT := hL) (hε := hε) (ha := ha) (hb := hb) (hA := hA)
    (χ := χ) (u := W 1) (v := W 0) (w := W 2) (Cpt := Cpt) (hCpt := hCpt)
    (hχcont := hχcont) (hχrange := hχrange) (hχout := hχout)
    (hucont := hcont 1) (hvcont := hcont 0)
    (hnonneg := fun s _ x _ => ⟨hnonneg 1 s x, hnonneg 0 s x⟩)
    (hvK := hzero) (hw := fun s _ _ x _ => hnonneg 2 s x) (hcut := hcut)
    (hu_time := fun s hs _ x _ => htime 1 s hs x)
    (hv_time := fun s hs _ x _ => htime 0 s hs x)
    (hu_space := fun s _ _ x _ => hspace 1 s x)
    (hv_space := fun s _ _ x _ => hspace 0 s x)
    (hu_grad := fun s _ _ x _ => hgrad 1 s x)
    (hv_grad := fun s _ _ x _ => hgrad 0 s x)
    (hgu := fun s _ _ x _ => towerNorm_grad_le S 1 s x)
    (hgv := fun s _ _ x _ => towerNorm_grad_le S 0 s x)
    (hPu := hPu) (hPv := hPv)
    L ⟨hL.le, le_rfl⟩ hL O hχone
  have haL : a * L = 2 * rmTowerCost n 1 := by
    dsimp only [a, K, L]
    field_simp [hR.ne']
  rw [haL] at hbound
  have hscale : Real.exp (2 * rmTowerCost n 1) *
        (A * K ^ 2 + (A * b + 5 * A * ε * K ^ 2) * L) / L =
      curvatureCutoffEnergyConstant n / R ^ 6 := by
    dsimp only [A, K, b, ε, L, curvatureCutoffEnergyConstant]
    field_simp [hR.ne']
    ring
  exact hbound.trans_eq hscale

variable [T2Space (TangentBundle I M)]

theorem fixed_ball_curvature_and_scalar_gradient_bound
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    {time : RealTimeInterval.FlowTime D} (B : FlowMetricBall S time)
    (hslab : Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ) ⊆ D.carrier)
    (hreg : Ioc ((time : ℝ) - B.radius ^ 2) (time : ℝ) ⊆ D.regular)
    (hRm : ∀ s ∈ Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ),
      ∀ x ∈ B.set, B.radius ^ 4 * FlowMetricBall.rmNormSq S s x ≤ 1)
    (hcomplete : ∀ s ∈ Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ),
      RiemannianMetricComplete (I := I) (S.base.metric s))
    (hqual : ∃ Kqual : ℝ, 0 ≤ Kqual ∧
      ∀ s ∈ Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ), ∀ x : M,
        normSq0S (I := I) (S.base.metric s) x 4 (S.base.rm04 s x) ≤ Kqual)
    (O : M)
    (hO : riemannianEDistOf (I := I) (S.base.metric (time : ℝ)) B.center O <
      ENNReal.ofReal (B.radius / 2))
    (b : RealTimeInterval.FlowTime D)
    (hb : (b : ℝ) ∈ Icc ((time : ℝ) - B.radius ^ 2 / 2) (time : ℝ)) :
    nablaKRm04NormSqIntrinsic S 1 (b : ℝ) O ≤
        fixedBallCurvatureGradientConstant (Module.finrank ℝ E) / B.radius ^ 6 ∧
      ∀ v : TangentSpace I O,
        |(S.base.metric (b : ℝ)).inner O
          (gradientFun (I := I) (S.base.metric (b : ℝ)) (S.scalar (b : ℝ)) O) v| ≤
          (fixedBallScalarGradientConstant (Module.finrank ℝ E) / B.radius ^ 3) *
            Real.sqrt ((S.base.metric (b : ℝ)).inner O v v) := by
  let n := Module.finrank ℝ E
  let R := B.radius / (4 * Real.exp ((n : ℝ) ^ 2))
  let a := (b : ℝ) - R ^ 2
  let S0 := S.timeShift a
  let χ := finiteDistanceCutoff S0 R O
  let Cpt : Set M := {x | riemannianEDistOf (I := I)
    (S.base.metric (time : ℝ)) B.center x ≤ ENNReal.ofReal B.radius}
  have hR : 0 < R := div_pos B.radius_pos (mul_pos (by norm_num) (Real.exp_pos _))
  have hRquarter : R ≤ B.radius / 4 := by
    have he : 1 ≤ Real.exp ((n : ℝ) ^ 2) := Real.one_le_exp (sq_nonneg _)
    apply (div_le_iff₀ (mul_pos (by norm_num) (Real.exp_pos _))).2
    nlinarith only [he, B.radius_pos]
  have hRr : R ≤ B.radius := hRquarter.trans (by linarith [B.radius_pos])
  have hwindow : Icc ((b : ℝ) - R ^ 2) (b : ℝ) ⊆
      Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ) := by
    have hsquare := pow_le_pow_left₀ hR.le hRquarter 2
    intro s hs
    refine ⟨?_, hs.2.trans hb.2⟩
    nlinarith only [hs.1, hb.1, hsquare, sq_nonneg B.radius]
  have hcutoff := fixed_ball_finite_distance_cutoff S hS B
    hslab hreg hRm hcomplete hqual O hO b hb
  change IsCompact Cpt ∧
    (∀ s ∈ Icc 0 (R ^ 2), ∀ x, χ s x ∈ Icc (0 : ℝ) 1) ∧
    (∀ s ∈ Icc 0 (R ^ 2), χ s O = 1) ∧
    ContinuousOn (fun p : ℝ × M => χ p.1 p.2) (spacetimeSlab (M := M) (R ^ 2)) ∧
    (∀ s ∈ Icc 0 (R ^ 2), ∀ x, x ∉ Cpt → χ s x = 0) ∧
    (∀ s ∈ Icc 0 (R ^ 2), ∀ x, 0 < χ s x → x ∈ B.set) ∧
    (∀ s ∈ Icc 0 (R ^ 2), 0 < s → ∀ x, 0 < χ s x →
      Nonempty (ShiCutoffLowerSupportAt (I := I) (flowG S0) (R ^ 2)
        (finiteDistanceCutoffConstant n / R ^ 2) χ s x)) ∧
    (∀ s x, χ s x = DifferentialGeometry.Analysis.CutoffProfile.evalue
      (ENNReal.ofReal ((8 / R) * Real.exp (((n : ℝ) ^ 2 / R ^ 2) * s)) *
        riemannianEDistOf (I := I) (S.base.metric (s + a)) O x)) ∧
    (∀ s ∈ Icc 0 (R ^ 2), s + a ∈ Icc ((b : ℝ) - R ^ 2) (b : ℝ) ∧
      s + a ∈ D.regular) at hcutoff
  obtain ⟨hCpt, hχrange, hχcenter, hχcont, hχout, hχset, hcut, _hformula, hclock⟩ := hcutoff
  have hreg0 : Icc 0 (R ^ 2) ⊆ (D.timeShift a).regular :=
    fun s hs => (hclock s hs).2
  have hzero (s : ℝ) (hs : s ∈ Icc 0 (R ^ 2)) (x : M) (hx : 0 < χ s x) :
      nablaKRm04NormSqIntrinsic S0 0 s x ≤ (1 / R ^ 2) ^ 2 := by
    have hraw := hRm (s + a) (hwindow (hclock s hs).1) x (hχset s hs x hx)
    have hn := nablaKRm04NormSqIntrinsic_nonneg S0 0 s x
    have heq : nablaKRm04NormSqIntrinsic S0 0 s x =
        FlowMetricBall.rmNormSq S (s + a) x := rfl
    rw [← heq] at hraw
    have hsmall : R ^ 4 * nablaKRm04NormSqIntrinsic S0 0 s x ≤ 1 :=
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hR.le hRr 4) hn).trans hraw
    have hh : nablaKRm04NormSqIntrinsic S0 0 s x ≤ 1 / R ^ 4 :=
      (le_div_iff₀ (pow_pos hR 4)).2 (by simpa only [mul_comm] using hsmall)
    convert hh using 1
    ring
  have henergy := curvature_energy_of_finite_cutoff S0 (isSolutionOn_timeShift hS a)
    R hR hreg0 χ Cpt hCpt hχcont hχrange hχout hcut hzero O
    (hχcenter (R ^ 2) ⟨(sq_pos_of_pos hR).le, le_rfl⟩)
  have htime : R ^ 2 + a = (b : ℝ) := by dsimp only [a]; ring
  have hsame : nablaKRm04NormSqIntrinsic S0 1 (R ^ 2) O =
      nablaKRm04NormSqIntrinsic S 1 (b : ℝ) O := by
    unfold nablaKRm04NormSqIntrinsic
    rw [nablaKRm_eq_iterCov, nablaKRm_eq_iterCov]
    change normSq0S (I := I) (S.base.metric (R ^ 2 + a)) O 5
      (iterCov (I := I) (S.base.metric (R ^ 2 + a)) 4
        (S.base.rm04 (R ^ 2 + a)) 1 O) = _
    rw [htime]
  rw [hsame] at henergy
  have hscale : curvatureCutoffEnergyConstant n / R ^ 6 =
      fixedBallCurvatureGradientConstant n / B.radius ^ 6 := by
    dsimp only [fixedBallCurvatureGradientConstant, R]
    rw [div_pow]
    field_simp [B.radius_pos.ne', (Real.exp_pos ((n : ℝ) ^ 2)).ne']
  have hderiv := henergy.trans_eq hscale
  refine ⟨hderiv, ?_⟩
  intro v
  have hpair := DifferentialGeometry.Geometry.Curvature.scalar_gradient_inner_le_nablaRm
    (S.base.metric (b : ℝ)) O v
  have hnorm : normSq0S (I := I) (S.base.metric (b : ℝ)) O 5
      (iterCov (I := I) (S.base.metric (b : ℝ)) 4
        (metricRm04 (I := I) (S.base.metric (b : ℝ))) 1 O) =
      nablaKRm04NormSqIntrinsic S 1 (b : ℝ) O := by
    unfold nablaKRm04NormSqIntrinsic
    rw [nablaKRm_eq_iterCov]
    rfl
  rw [hnorm] at hpair
  have hC := (fixedBallCurvatureGradientConstant_pos n).le
  have hroot : Real.sqrt (nablaKRm04NormSqIntrinsic S 1 (b : ℝ) O) ≤
      Real.sqrt (fixedBallCurvatureGradientConstant n) / B.radius ^ 3 := by
    have hs := Real.sqrt_le_sqrt hderiv
    have heq : fixedBallCurvatureGradientConstant n / B.radius ^ 6 =
        (Real.sqrt (fixedBallCurvatureGradientConstant n) / B.radius ^ 3) ^ 2 := by
      rw [div_pow, Real.sq_sqrt hC]
      ring
    rw [heq, Real.sqrt_sq
      (div_nonneg (Real.sqrt_nonneg _) (pow_nonneg B.radius_pos.le 3))] at hs
    exact hs
  calc
    _ ≤ (n : ℝ) ^ 3 * Real.sqrt (nablaKRm04NormSqIntrinsic S 1 (b : ℝ) O) *
        Real.sqrt ((S.base.metric (b : ℝ)).inner O v v) := hpair
    _ ≤ (n : ℝ) ^ 3 *
        (Real.sqrt (fixedBallCurvatureGradientConstant n) / B.radius ^ 3) *
          Real.sqrt ((S.base.metric (b : ℝ)).inner O v v) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hroot (by positivity))
        (Real.sqrt_nonneg _)
    _ = _ := by dsimp only [fixedBallScalarGradientConstant]; ring

end DifferentialGeometry.PDE.RicciFlow

end
