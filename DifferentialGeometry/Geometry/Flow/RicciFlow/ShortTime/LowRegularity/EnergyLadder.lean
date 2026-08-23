import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.FatouMass

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral hiding TensorEigenIdx
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral
  (eigenIdxFinset fatou_sq_mass galerkinEnergy tendsto_eigenIdxFinset_atTop)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

def HasGalerkinApproximationEnergyFiveBound (g₀ : SmoothRiemannianMetric I M)
    {δ Ctop B0 B1 D ρ P Rcap T : ℝ} {hT : 0 < T} {hT1 : T ≤ 1}
    (fLo : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hsol : IsLowRegularitySolutionAt (I := I) (M := M) (δ := δ) (Ctop := Ctop)
      (B0 := B0) (B1 := B1) (D := D) (ρ := ρ) (P := P)
      g₀ hT hT1 fLo Rcap)
    (fseq : ℕ → timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T) : Prop :=
  (∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2), ∀ t ∈ Set.Icc (0 : ℝ) T,
      Tendsto (fun N => galerkinSolutionMode (I := I) (M := M) g₀ fseq N t i) atTop
        (𝓝 (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
          (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t))) ∧
    (∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn
        (fun t => galerkinSolutionMode (I := I) (M := M) g₀ fseq N t i)
        (Set.Icc (0 : ℝ) T)) ∧
    (∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      HasDerivWithinAt
        (fun s => galerkinSolutionMode (I := I) (M := M) g₀ fseq N s i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) *
            galerkinSolutionMode (I := I) (M := M) g₀ fseq N t i +
          galTameForce (I := I) (M := M) g₀ 1
            (lowRegularityStateRadius_pos hsol.hCtop hsol.hB1 hsol.hρ hsol.hP).le
            (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hsol.hδ hsol.hCtop hsol.hB1
              hsol.hρ hsol.hP hsol.hreal)
            (eigenIdxFinset (I := I) (M := M) g₀ N)
            (galerkinSolutionMode (I := I) (M := M) g₀ fseq N t) i)
        (Set.Ici t) t) ∧
    (∀ N i, galerkinSolutionMode (I := I) (M := M) g₀ fseq N 0 i = 0) ∧
    ∃ Φ : ℝ, ∀ N : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g₀ N)
        (galerkinSolutionMode (I := I) (M := M) g₀ fseq N) 5 t ≤ Φ

theorem exists_galerkin_approximation_energy_five_bound
    (g₀ : SmoothRiemannianMetric I M)
    {δ Ctop B0 B1 D ρ P Rcap Ctop₂ Kr2 Kr1 Kcap T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (fLo : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hlo : IsAdaptedLowRegularitySolution (I := I) (M := M) (δ := δ) (Ctop := Ctop)
      (B0 := B0) (B1 := B1) (D := D) (ρ := ρ) (P := P)
      g₀ hT hT1 fLo Rcap Ctop₂ Kr2 Kr1 Kcap) :
    ∃ (fseq : ℕ → timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T),
      HasGalerkinApproximationEnergyFiveBound (I := I) (M := M) g₀ fLo hlo.toIsLowRegularitySolutionAt fseq := by
  classical
  have hsol := hlo.toIsLowRegularitySolutionAt
  obtain ⟨fseq, _hconv, hmode, hpack⟩ :=
    exists_galerkin_projected_forcing_sequence_with_mode_convergence (I := I) (M := M) g₀ hT hT1 fLo hsol
  obtain ⟨A, B, hgate, hA3, hB3, ε, hε, hbudget⟩ := hlo.exists_absorption_constants_and_margin
  have hstate : 0 ≤ lowRegularityStateRadius Ctop B1 ρ P :=
    (lowRegularityStateRadius_pos hsol.hCtop hsol.hB1 hsol.hρ hsol.hP).le
  have hdom3 := energyLadder_absorption_coefficient_le hA3 hB3 hsol.hδ0 hstate
  have habs3 :
      Ctop₂ * (Kcap * (δ / (1 - δ) ^ 2)) +
          Kr2 * lowRegularityStateRadius Ctop B1 ρ P +
          Kr1 * lowRegularityStateRadius Ctop B1 ρ P + ε < 1 := by
    linarith only [hdom3, hbudget]
  have hL2H3 (N : ℕ) := galerkin_energy_three_integral_bound (I := I) (M := M) g₀ hT N fseq _
    ((hpack N).2.2.1) ((hpack N).2.2.2.2.2)
  obtain ⟨Φ3, hE3⟩ := exists_uniform_galerkin_energy_three_bound_of_integral_bound (I := I) (M := M) g₀ hT
    hsol.hδ hsol.hδ0 hsol.hδ3 hsol.hCtop hsol.hB0 hsol.hB1 hsol.hρ hsol.hP
    hsol.hreal hsol.hcore hsol.htame fseq (fun N => (hpack N).2.1)
    (fun N => (hpack N).2.2.1) (Bd := ((1 + T) *
      (lowRegularityStateRadius Ctop B1 ρ P / 4)) ^ 2) hL2H3
    hlo.toHasGalerkinEnergyThreeBound hε habs3
  let R3 : ℝ := Real.sqrt (max Φ3 0)
  have hR3 : 0 ≤ R3 := by dsimp only [R3]; positivity
  have hE3cap : ∀ N : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Real.sqrt (galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g₀ N)
        (galerkinSolutionMode (I := I) (M := M) g₀ fseq N) 3 t) ≤ R3 := by
    intro N t ht
    dsimp only [R3]
    exact Real.sqrt_le_sqrt ((hE3 N t ht).trans (le_max_left _ _))
  let U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ :=
    galerkinSolutionMode (I := I) (M := M) g₀ fseq
  have hUcont : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T) :=
    fun N i _ => galerkinSolutionMode_continuous (I := I) (M := M) g₀ hT.le fseq N i
  have hUinit : ∀ N i, U N 0 i = 0 :=
    fun N i => lowRegularityProjMode_zero (I := I) (M := M) g₀ fseq N i
  have hUderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      HasDerivWithinAt (fun s => U N s i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
          galTameForce (I := I) (M := M) g₀ 1 hstate
            (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hsol.hδ hsol.hCtop hsol.hB1
              hsol.hρ hsol.hP hsol.hreal)
            (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) i)
        (Set.Ici t) t := by
    intro N t ht i _
    refine galerkinSolutionMode_hasDerivWithinAt (I := I) (M := M) g₀ hT hstate N fseq i ?_ ?_ ht
    · exact galerkinProjectedForce_mode_continuous (I := I) (M := M) g₀ g₀ hsol.hδ hsol.hCtop hsol.hB0
        hsol.hB1 hsol.hρ hsol.hP hsol.hreal hsol.htame N (U N)
        (fun j _ => hUcont N j (by assumption)) i
    · exact galerkinProjectedForce_mode_eq (I := I) (M := M) g₀ hstate hT N fseq
        ((hpack N).2.1) ((hpack N).2.2.1) i
  obtain ⟨C3, Kr24, Kr14, K3, hord4, hA4, hB4⟩ := hgate.2.2.2.1
  have hdom4 := energyLadder_absorption_coefficient_le hA4 hB4 hsol.hδ0 hstate
  have habs4 :
      C3 * (K3 * (δ / (1 - δ) ^ 2)) +
          Kr24 * lowRegularityStateRadius Ctop B1 ρ P +
          Kr14 * lowRegularityStateRadius Ctop B1 ρ P + ε < 1 := by
    linarith only [hdom4, hbudget]
  obtain ⟨Φ4, hE4⟩ := hord4.2.2.2.2
    (δ := δ) (Ctop := Ctop) (B1 := B1) (ρ := ρ) (P := P) (T := T) (R3 := R3)
    hsol.hδ hsol.hδ0 hsol.hδ3 hsol.hCtop hsol.hB1 hsol.hρ hsol.hP
    hsol.hreal hsol.hcore hUcont hUderiv hUinit hR3 hE3cap hε habs4
  let R4 : ℝ := Real.sqrt (max Φ4 0)
  have hR4 : 0 ≤ R4 := by dsimp only [R4]; positivity
  have hE4cap : ∀ N : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Real.sqrt (galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g₀ N)
        (galerkinSolutionMode (I := I) (M := M) g₀ fseq N) 4 t) ≤ R4 := by
    intro N t ht
    dsimp only [R4]
    exact Real.sqrt_le_sqrt ((hE4 N t ht).trans (le_max_left _ _))
  obtain ⟨C4, Kr25, Kr15, K4, hord5, hA5, hB5⟩ := hgate.2.2.2.2.1
  have hdom5 := energyLadder_absorption_coefficient_le hA5 hB5 hsol.hδ0 hstate
  have habs5 :
      C4 * (K4 * (δ / (1 - δ) ^ 2)) +
          Kr25 * lowRegularityStateRadius Ctop B1 ρ P +
          Kr15 * lowRegularityStateRadius Ctop B1 ρ P + ε < 1 := by
    linarith only [hdom5, hbudget]
  obtain ⟨Φ5, hE5⟩ := hord5.2.2.2.2
    (δ := δ) (Ctop := Ctop) (B1 := B1) (ρ := ρ) (P := P) (T := T)
    (R3 := R3) (R4 := R4) hsol.hδ hsol.hδ0 hsol.hδ3 hsol.hCtop hsol.hB1
    hsol.hρ hsol.hP hsol.hreal hsol.hcore hUcont hUderiv hUinit
    hR3 hE3cap hR4 hE4cap hε habs5
  refine ⟨fseq, ?_⟩
  exact ⟨hmode, hUcont, by simpa only [U] using hUderiv,
    by simpa only [U] using hUinit, Φ5, by simpa only [U] using hE5⟩

theorem exists_galerkin_approximation_converging_with_energy_five_bound
    (g₀ : SmoothRiemannianMetric I M)
    {δ Ctop B0 B1 D ρ P Rcap Ctop₂ Kr2 Kr1 Kcap T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (fLo : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hlo : IsAdaptedLowRegularitySolution (I := I) (M := M) (δ := δ) (Ctop := Ctop)
      (B0 := B0) (B1 := B1) (D := D) (ρ := ρ) (P := P)
      g₀ hT hT1 fLo Rcap Ctop₂ Kr2 Kr1 Kcap) :
    ∃ (fseq : ℕ → timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T),
      (∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2), ∀ t ∈ Set.Icc (0 : ℝ) T,
        Tendsto (fun N => galerkinSolutionMode (I := I) (M := M) g₀ fseq N t i) atTop
          (𝓝 (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t))) ∧
      ∃ Φ : ℝ, ∀ N : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T,
        galerkinEnergy (I := I) (M := M)
          (eigenIdxFinset (I := I) (M := M) g₀ N)
          (galerkinSolutionMode (I := I) (M := M) g₀ fseq N) 5 t ≤ Φ := by
  obtain ⟨fseq, hpath⟩ := exists_galerkin_approximation_energy_five_bound (I := I) (M := M)
    g₀ hT hT1 fLo hlo
  exact ⟨fseq, hpath.1, hpath.2.2.2.2⟩

theorem per_mode_limit_weighted_energy_five_bound
    (g₀ : SmoothRiemannianMetric I M)
    {δ Ctop B0 B1 D ρ P Rcap Ctop₂ Kr2 Kr1 Kcap T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (fLo : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hlo : IsAdaptedLowRegularitySolution (I := I) (M := M) (δ := δ) (Ctop := Ctop)
      (B0 := B0) (B1 := B1) (D := D) (ρ := ρ) (P := P)
      g₀ hT hT1 fLo Rcap Ctop₂ Kr2 Kr1 Kcap) :
    ∀ σ : ℝ, σ ≤ 5 → ∃ Cσ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t) ^ 2) ∧
        ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t) ^ 2 ≤
          Cσ := by
  classical
  obtain ⟨fseq, hconv, Φ, hΦ⟩ := exists_galerkin_approximation_converging_with_energy_five_bound (I := I) (M := M)
    g₀ hT hT1 fLo hlo
  intro σ hσ
  refine ⟨Φ, fun t ht => ?_⟩
  have hdom : ∀ i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
      tensorSobolevWeight (I := I) (M := M) i σ ≤
        tensorSobolevWeight (I := I) (M := M) i 5 := fun i =>
    Real.rpow_le_rpow_of_exponent_le (one_le_one_add_lambda (I := I) (M := M) i)
      hσ
  have hpartial : ∀ N : ℕ,
      ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
          tensorSobolevWeight (I := I) (M := M) i σ *
            (galerkinSolutionMode (I := I) (M := M) g₀ fseq N t i) ^ 2 ≤ Φ := by
    intro N
    refine le_trans (Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_right (hdom i) (sq_nonneg _))) ?_
    exact hΦ N t ht
  exact fatou_sq_mass (eigenIdxFinset (I := I) (M := M) g₀)
    (tendsto_eigenIdxFinset_atTop (I := I) (M := M) g₀)
    (fun i => tensorSobolevWeight (I := I) (M := M) i σ)
    (fun i => tensorSobolevWeight_nonneg (I := I) (M := M) i σ)
    (fun N i => galerkinSolutionMode (I := I) (M := M) g₀ fseq N t i)
    (fun i => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
      (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t)
    (fun i => hconv i t ht) Φ hpartial

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
