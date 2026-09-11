import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.FlowBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.LowerBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.DimensionZero
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.BallEstimate.SourceTailControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.FlowBall.VolumeComparison

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open scoped ContDiff ENNReal Manifold Topology

universe u uE uH

section DimensionZero

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [SigmaCompactSpace M]

private theorem redVolume_le_flowMetricBall_volume_of_finrank_eq_zero
    [ConnectedSpace M]
    (hdim : Module.finrank ℝ E = 0)
    {S : SolutionOn (I := I) (M := M) D}
    {time : RealTimeInterval.FlowTime D} (B : FlowMetricBall S time) (tau : ℝ) :
    redVolume S (time : ℝ) B.center tau ≤ B.volume := by
  let : Subsingleton E := Module.finrank_zero_iff.mp hdim
  let : Subsingleton H := I.injective.subsingleton
  let : DiscreteTopology M := ChartedSpace.discreteTopology H M
  let : Subsingleton M := subsingleton_of_preconnected_totallyDisconnected
  have hv (z : M) (v : TangentSpace I z) : v = 0 := by
    apply (tangentSpaceModelContinuousLinearEquiv (I := I) z).injective
    exact Subsingleton.elim _ _
  have hB : B.set = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    change riemannianEDistOf (S.base.metric (time : ℝ)) B.center x < ENNReal.ofReal B.radius
    rw [Subsingleton.elim x B.center, riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr B.radius_pos
  have hmeasure := volumeMeasure_le (I := I) (M := M)
    (S.base.metric (time : ℝ)) (S.base.metric ((time : ℝ) - tau))
    (Q := 1) zero_lt_one (fun x v => by rw [hv x v]; simp)
  rw [redVolume_eq_volume_of_finrank_eq_zero hdim]
  calc
    _ ≤ riemannianVolumeMeasure (I := I) (M := M)
        (S.base.metric (time : ℝ)) Set.univ := by
      simpa only [one_pow, Real.sqrt_one, ENNReal.ofReal_one, one_smul] using hmeasure Set.univ
    _ = B.volume := by
      simp only [FlowMetricBall.volume, volumeMeasureOn_eq_metric, SolutionOn.family_metric, hB]

end DimensionZero

section ReducedJacobian

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_pos_lintegral_lReducedJacobian_le_on_flowMetricBall :
    ∀ rho : Real, 0 < rho → ∃ eps₀ : Real, 0 < eps₀ ∧
        ∀ {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D},
          IsSolutionOn (I := I) S →
          ∀ {time : RealTimeInterval.FlowTime D} (B : FlowMetricBall S time),
            B.radius ≤ rho → B.IsRmControlled →
            Set.Ioc ((time : Real) - B.radius ^ 2) (time : Real) ⊆ D.regular →
            ∀ eps : Real, 0 < eps → eps ≤ eps₀ →
              let tau := eps * B.radius ^ 2
              let c := Real.exp
                ((Module.finrank Real E : Real) ^ 2 * eps / 3 -
                  ((Module.finrank Real E : Real) / 2) * Real.log tau -
                  ((Module.finrank Real E : Real) / 2) * Real.log (4 * Real.pi))
              let K : Set M := {y | riemannianEDistOf (I := I)
                (S.base.metric (time : Real)) B.center y ≤
                  ENNReal.ofReal (B.radius / 32)}
              (∫⁻ Z : E in
                  lInjDomain S (time : Real) B.center tau ∩
                    {Z | Real.sqrt
                      ((S.base.metric (time : Real)).inner B.center Z Z) ≤
                        1 / (128 * Real.sqrt eps)},
                  ENNReal.ofReal
                    (lReducedJacobian S (time : Real) B.center Z tau *
                      lSourceDensity S (time : Real) B.center)
                    ∂(modelHaar (E := E))) ≤
                ENNReal.ofReal c *
                  riemannianVolumeMeasure (I := I) (M := M)
                    (S.base.metric ((time : Real) - tau)) K := by
  obtain ⟨theta, htheta, hthetaOne, hrange⟩ :=
    exists_pos_lRegularizedCurve_mem_ball (E := E) (I := I) (M := M)
  intro rho hrho
  obtain ⟨epsR, hepsR, hrange'⟩ := hrange rho hrho
  let eps₀ : Real := min epsR 1
  have heps₀ : 0 < eps₀ := lt_min hepsR zero_lt_one
  refine ⟨eps₀, heps₀, ?_⟩
  intro D S hS time B hBrho hB hreg eps heps heps₀
  dsimp only
  have hepsR' : eps ≤ epsR := heps₀.trans (min_le_left epsR 1)
  have heps1 : eps ≤ 1 := heps₀.trans (min_le_right epsR 1)
  let tau : Real := eps * B.radius ^ 2
  let b : Real := Real.sqrt eps * B.radius
  let c : Real := Real.exp
    ((Module.finrank Real E : Real) ^ 2 * eps / 3 -
      ((Module.finrank Real E : Real) / 2) * Real.log tau -
      ((Module.finrank Real E : Real) / 2) * Real.log (4 * Real.pi))
  let U : Set E := lInjDomain S (time : Real) B.center tau
  let A : Set E := U ∩
    {Z | Real.sqrt ((S.base.metric (time : Real)).inner B.center Z Z) ≤
      1 / (128 * Real.sqrt eps)}
  let K : Set M := {y | riemannianEDistOf (I := I)
    (S.base.metric (time : Real)) B.center y ≤ ENNReal.ofReal (B.radius / 32)}
  have htau : 0 < tau := by
    dsimp only [tau]
    exact mul_pos heps (sq_pos_of_pos B.radius_pos)
  have hbpos : 0 < b := mul_pos (Real.sqrt_pos.2 heps) B.radius_pos
  have hb : Real.sqrt tau = b := by
    dsimp only [tau, b]
    rw [Real.sqrt_mul heps.le, Real.sqrt_sq_eq_abs, abs_of_pos B.radius_pos]
  have hcomplete : ∀ q ∈ Set.Icc
      ((time : Real) - theta * B.radius ^ 2) (time : Real),
      RiemannianMetricComplete (I := I) (S.base.metric q) := by
    intro q hq
    exact RiemannianMetricComplete.of_compact (I := I) (S.base.metric q)
  have hnormMeas : MeasurableSet
      {Z : E | Real.sqrt
        ((S.base.metric (time : Real)).inner B.center Z Z) ≤
          1 / (128 * Real.sqrt eps)} := by
    let F : E →L[ℝ] E →L[ℝ] ℝ := (S.base.metric (time : Real)).inner B.center
    have hc : Continuous (fun Z : E => F Z Z) := F.continuous.clm_apply continuous_id
    exact measurableSet_le (Real.continuous_sqrt.comp hc).measurable measurable_const
  have hAmeas : MeasurableSet A := by
    have hUopen : IsOpen U := by
      rw [show U = (lExpPartial S hS (time : Real) B.center tau htau).source from
        (lExpPartial_source S hS (time : Real) B.center tau htau).symm]
      exact (lExpPartial S hS (time : Real) B.center tau htau).open_source
    exact hUopen.measurableSet.inter hnormMeas
  have hAinj : A ⊆ lInjDomain S (time : Real) B.center tau := inter_subset_left
  have hrangeZ : ∀ Z ∈ A, ∀ s ∈ Set.Icc (0 : Real) b,
      s ∈ lRegularizedDomain S (time : Real) B.center Z ∧
        riemannianEDistOf (I := I) (S.base.metric (time : Real)) B.center
            (lRegularizedCurve S (time : Real) B.center Z s) <
          ENNReal.ofReal (B.radius / 32) ∧
        riemannianEDistOf (I := I)
            (S.base.metric ((time : Real) - s ^ 2)) B.center
            (lRegularizedCurve S (time : Real) B.center Z s) <
          ENNReal.ofReal (B.radius / 16) := by
    intro Z hZA
    simpa only [b] using
      hrange' hS B hBrho hB hreg hcomplete eps heps hepsR' Z hZA.2
  have hImage : ∀ Z ∈ A,
      lExp S (time : Real) B.center Z tau ∈ K := by
    intro Z hZA
    have h := (hrangeZ Z hZA b ⟨hbpos.le, le_rfl⟩).2.1
    change riemannianEDistOf (I := I) (S.base.metric (time : Real)) B.center
      (lExp S (time : Real) B.center Z tau) ≤ ENNReal.ofReal (B.radius / 32)
    change riemannianEDistOf (I := I) (S.base.metric (time : Real)) B.center
      (lRegularizedCurve S (time : Real) B.center Z (Real.sqrt tau)) ≤ _
    rw [hb]
    exact h.le
  have hden : ∀ Z ∈ A,
      redDensity S (time : Real) B.center
          (lExp S (time : Real) B.center Z tau) tau ≤ c := by
    intro Z hZA
    apply redDensity_le_of_redLength_ge (I := I) S (time : Real) B.center
      (lExp S (time : Real) B.center Z tau) tau
      ((Module.finrank Real E : Real) ^ 2 * eps / 3)
    apply redLength_lExp_ge_of_range_subset_flowMetricBall (J := I) S hS time heps heps1 B hB Z hZA.1
    dsimp only
    intro s hs
    have hsMove := (hrangeZ Z hZA s hs).2.2
    change riemannianEDistOf (I := I)
      (S.base.metric ((time : Real) - s ^ 2)) B.center
        (lRegularizedCurve S (time : Real) B.center Z s) < ENNReal.ofReal B.radius
    exact hsMove.trans ((ENNReal.ofReal_lt_ofReal_iff B.radius_pos).2 (by
      nlinarith only [B.radius_pos]))
  change (∫⁻ Z in A,
      ENNReal.ofReal
        (lReducedJacobian S (time : Real) B.center Z tau *
          lSourceDensity S (time : Real) B.center)
        ∂(modelHaar (E := E))) ≤ _
  simpa only [c] using
    lintegral_lReducedJacobian_mul_source_le (I := I) S hS (time : Real) B.center htau A K
      hAmeas hAinj c hImage hden

end ReducedJacobian

section ReducedVolume

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_pos_redVolume_le_on_flowMetricBall [ConnectedSpace M]
    {Q : ℝ} (hQ : 1 < Q) :
    ∀ rho : Real, 0 < rho → ∀ eta : ENNReal, 0 < eta →
      ∃ eps₀ : Real, 0 < eps₀ ∧
        ∀ {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D},
          IsSolutionOn (I := I) S →
          ∀ {time : RealTimeInterval.FlowTime D} (B : FlowMetricBall S time),
            B.radius ≤ rho → B.IsRmControlled →
            Set.Ioc ((time : Real) - B.radius ^ 2) (time : Real) ⊆ D.regular →
            ∀ eps : Real, 0 < eps → eps ≤ eps₀ →
              let tau := eps * B.radius ^ 2
              let c := Real.exp
                ((Module.finrank Real E : Real) ^ 2 * eps / 3 -
                  ((Module.finrank Real E : Real) / 2) * Real.log tau -
                  ((Module.finrank Real E : Real) / 2) * Real.log (4 * Real.pi))
              redVolume S (time : Real) B.center tau ≤
                ENNReal.ofReal c *
                    (ENNReal.ofReal
                        (Real.sqrt (Q ^ Module.finrank Real E)) *
                      B.volume) +
                  eta := by
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : PseudoMetricSpace M := TopologicalSpace.pseudoMetrizableSpacePseudoMetric M
  intro rho hrho eta heta
  by_cases hdim : Module.finrank ℝ E = 0
  · refine ⟨1, zero_lt_one, ?_⟩
    intro D S hS time B hBrho hB hreg eps heps heps₀
    dsimp only
    simpa only [hdim, Nat.cast_zero, zero_pow two_ne_zero, zero_mul,
      zero_div, sub_zero, zero_sub, neg_zero, Real.exp_zero,
      ENNReal.ofReal_one, pow_zero, Real.sqrt_one, one_mul] using
      (redVolume_le_flowMetricBall_volume_of_finrank_eq_zero hdim B (eps * B.radius ^ 2)).trans
        (le_add_of_nonneg_right heta.le)
  let : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
  have hsmall := exists_pos_lintegral_lReducedJacobian_le_on_flowMetricBall
    (E := E) (I := I) (M := M)
  obtain ⟨epsV, hepsV, hmove⟩ :=
    FlowMetricBall.exists_pos_volume_le_on_terminal_ball
      (E := E) (I := I) (M := M) hQ
  obtain ⟨epsJ, hepsJ, hsmall'⟩ := hsmall rho hrho
  obtain ⟨R, hR, htail⟩ :=
    lSourceGaussian_uniform_tail (E := E) (I := I) (M := M) eta heta
  let d : Real := 1 / (128 * (R + 1))
  have hRone : 0 < R + 1 := by linarith
  have hd : 0 < d := one_div_pos.mpr (mul_pos (by norm_num) hRone)
  let eps₀ : Real := min epsJ (min epsV (min (1 / 2) (d ^ 2)))
  have heps₀ : 0 < eps₀ :=
    lt_min hepsJ (lt_min hepsV (lt_min (by norm_num) (sq_pos_of_pos hd)))
  refine ⟨eps₀, heps₀, ?_⟩
  intro D S hS time B hBrho hB hreg eps heps heps₀
  dsimp only
  have hepsJ' : eps ≤ epsJ :=
    heps₀.trans (min_le_left epsJ (min epsV (min (1 / 2) (d ^ 2))))
  have hepsV' : eps ≤ epsV :=
    heps₀.trans ((min_le_right epsJ (min epsV (min (1 / 2) (d ^ 2)))).trans
      (min_le_left epsV (min (1 / 2) (d ^ 2))))
  have hepsHalf : eps ≤ (1 / 2 : Real) :=
    heps₀.trans ((min_le_right epsJ (min epsV (min (1 / 2) (d ^ 2)))).trans
      ((min_le_right epsV (min (1 / 2) (d ^ 2))).trans
        (min_le_left (1 / 2) (d ^ 2))))
  have hepsLt : eps < 1 := by linarith
  have hepsd : eps ≤ d ^ 2 :=
    heps₀.trans ((min_le_right epsJ (min epsV (min (1 / 2) (d ^ 2)))).trans
      ((min_le_right epsV (min (1 / 2) (d ^ 2))).trans
        (min_le_right (1 / 2) (d ^ 2))))
  have hsqrteps : 0 < Real.sqrt eps := Real.sqrt_pos.2 heps
  have hsqrtd : Real.sqrt eps ≤ d := by
    rw [Real.sqrt_le_iff]
    exact ⟨hd.le, hepsd⟩
  have hcut : R ≤ 1 / (128 * Real.sqrt eps) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hsqrteps)).2
    calc
      R * (128 * Real.sqrt eps) ≤ (R + 1) * (128 * Real.sqrt eps) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ (R + 1) * (128 * d) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsqrtd (by norm_num)) hRone.le
      _ = 1 := by
        dsimp only [d]
        field_simp [hRone.ne']
  let tau : Real := eps * B.radius ^ 2
  let c : Real := Real.exp
    ((Module.finrank Real E : Real) ^ 2 * eps / 3 -
      ((Module.finrank Real E : Real) / 2) * Real.log tau -
      ((Module.finrank Real E : Real) / 2) * Real.log (4 * Real.pi))
  let q : E → Real := fun Z ↦
    Real.sqrt ((S.base.metric (time : Real)).inner B.center Z Z)
  let U : Set E := lInjDomain S (time : Real) B.center tau
  let A : Set E := U ∩ {Z | q Z ≤ 1 / (128 * Real.sqrt eps)}
  let C : Set E := U ∩ {Z | 1 / (128 * Real.sqrt eps) < q Z}
  let f : E → ENNReal := fun Z ↦
    ENNReal.ofReal
      (lReducedJacobian S (time : Real) B.center Z tau *
        lSourceDensity S (time : Real) B.center)
  let K : Set M := {y | riemannianEDistOf (I := I)
    (S.base.metric (time : Real)) B.center y ≤ ENNReal.ofReal (B.radius / 32)}
  have htau : 0 < tau := by
    dsimp only [tau]
    exact mul_pos heps (sq_pos_of_pos B.radius_pos)
  have hCmeas : MeasurableSet C := by
    apply (lInj_isOpen S hS (time : Real) B.center tau).measurableSet.inter
    apply measurableSet_lt measurable_const
    let F : E →L[ℝ] E →L[ℝ] ℝ := (S.base.metric (time : Real)).inner B.center
    exact (Real.continuous_sqrt.comp (F.continuous.clm_apply continuous_id)).measurable
  have hunion : A ∪ C = U := by
    ext Z
    simp only [A, C, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro (hZ | hZ) <;> exact hZ.1
    · intro hZ
      exact (le_or_gt (q Z) (1 / (128 * Real.sqrt eps))).elim
        (fun h ↦ Or.inl ⟨hZ, h⟩) (fun h ↦ Or.inr ⟨hZ, h⟩)
  have hdisj : Disjoint A C := by
    rw [Set.disjoint_left]
    intro Z hZA hZC
    exact (not_lt_of_ge
      (show q Z ≤ 1 / (128 * Real.sqrt eps) from hZA.2))
      (show 1 / (128 * Real.sqrt eps) < q Z from hZC.2)
  have hsmallK : (∫⁻ Z in A, f Z ∂(modelHaar (E := E))) ≤
      ENNReal.ofReal c *
        riemannianVolumeMeasure (I := I) (M := M)
          (S.base.metric ((time : Real) - tau)) K := by
    simpa only [A, U, q, f, tau, c, K] using
      hsmall' hS B hBrho hB hreg eps heps hepsJ'
  have hmove' :
      riemannianVolumeMeasure (I := I) (M := M)
          (S.base.metric ((time : Real) - tau)) K ≤
        ENNReal.ofReal
            (Real.sqrt (Q ^ Module.finrank Real E)) *
          B.volume := by
    simpa only [tau, K] using hmove hS B hB
      (fun t ht => hreg ⟨ht.1, ht.2.le⟩)
      (RiemannianMetricComplete.of_compact (S.base.metric (time : Real))) eps heps hepsV'
  have hsmallFinal : (∫⁻ Z in A, f Z ∂(modelHaar (E := E))) ≤
      ENNReal.ofReal c *
        (ENNReal.ofReal
              (Real.sqrt (Q ^ Module.finrank Real E)) *
          B.volume) := by
    exact hsmallK.trans (by
      simpa only [mul_comm] using
        mul_le_mul_right hmove' (ENNReal.ofReal c))
  have htail' : (∫⁻ Z in C, f Z ∂(modelHaar (E := E))) ≤ eta := by
    calc
      (∫⁻ Z in C, f Z ∂(modelHaar (E := E))) ≤
          ∫⁻ Z : E in {Z | 1 / (128 * Real.sqrt eps) < q Z},
            ENNReal.ofReal (lSourceGaussian S (time : Real) B.center Z)
              ∂(modelHaar (E := E)) := by
        simpa only [C, U, q, f] using
          lReducedJacobian_tail_le S hS (time : Real) B.center tau
            (1 / (128 * Real.sqrt eps)) htau
      _ ≤ ∫⁻ Z : E in {Z | R < q Z},
          ENNReal.ofReal (lSourceGaussian S (time : Real) B.center Z)
            ∂(modelHaar (E := E)) := by
        apply MeasureTheory.lintegral_mono_set
        intro Z hZ
        exact lt_of_le_of_lt hcut hZ
      _ ≤ eta := by
        simpa only [q] using htail S (time : Real) B.center
  rw [redVolume_lint S hS (time : Real) B.center tau htau (by
    intro t ht
    apply hreg
    have htauLt : tau < B.radius ^ 2 := by
      dsimp only [tau]
      nlinarith [sq_pos_of_pos B.radius_pos, hepsLt]
    exact ⟨by linarith [ht.1], ht.2⟩)]
  change (∫⁻ Z in U, f Z ∂(modelHaar (E := E))) ≤ _
  calc
    (∫⁻ Z in U, f Z ∂(modelHaar (E := E))) =
        (∫⁻ Z in A, f Z ∂(modelHaar (E := E))) +
          ∫⁻ Z in C, f Z ∂(modelHaar (E := E)) := by
      rw [← hunion]
      exact MeasureTheory.lintegral_union hCmeas hdisj
    _ ≤ _ := add_le_add hsmallFinal htail'

end ReducedVolume

end DifferentialGeometry.PDE.RicciFlow.Perelman
