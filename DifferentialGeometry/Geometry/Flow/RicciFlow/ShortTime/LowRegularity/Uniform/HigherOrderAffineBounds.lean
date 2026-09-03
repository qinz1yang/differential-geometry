import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Background.HigherOrderEnergy
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.LowerScaleGalerkinAffineBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.FourthOrderDissipationLimit

set_option autoImplicit false

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
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic (zero_mem_lowerState)
open DifferentialGeometry.Analysis.Spectral
  (eigenIdxFinset galerkinEnergy galerkinEnergy_continuousOn galerkinEnergy_nonneg)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem exists_uniform_higher_order_affine_bounds_at_background
    (g gBase : SmoothRiemannianMetric I M)
    (K : LowRegularityBoundParameters)
    {T Rcap : ℝ} {hT : 0 < T} {hT1 : T ≤ 1}
    (u : MaxRegSolutionSpace (I := I) (M := M) (g := g) (r := 0) (s := 2)
      ((1 : ℕ) : ℝ) T)
    (gforce : timeL2
      (TensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
    (hsol : IsBackgroundLowRegularitySolutionAt (I := I) (M := M) g gBase K hT hT1
      u gforce Rcap)
    {fseq : ℕ → timeL2
      (TensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T}
    (hUcont : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g N,
      ContinuousOn
        (fun t => galerkinSolutionMode (I := I) (M := M) g fseq N t i)
        (Set.Icc (0 : ℝ) T))
    (hUderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      ∀ i ∈ eigenIdxFinset (I := I) (M := M) g N,
      HasDerivWithinAt
        (fun s => galerkinSolutionMode (I := I) (M := M) g fseq N s i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) *
            galerkinSolutionMode (I := I) (M := M) g fseq N t i +
          galTameForce (I := I) (M := M) g 1
            (lowRegularityStateRadius_pos K.top_nonneg K.slope_nonneg K.outer_pos K.realize_pos).le
            (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g gBase K.threshold_lt K.top_nonneg K.slope_nonneg
              K.outer_pos K.realize_pos hsol.hreal)
            (eigenIdxFinset (I := I) (M := M) g N)
            (galerkinSolutionMode (I := I) (M := M) g fseq N t) i)
        (Set.Ici t) t)
    (hUinit : ∀ N i, galerkinSolutionMode (I := I) (M := M) g fseq N 0 i = 0)
    {Φ4 Φ5 Karm : ℝ} {Ca2 : ℕ → ℝ} {Ca1 : ℝ → ℕ → ℝ}
    (hE4 : ∀ N : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g N)
        (galerkinSolutionMode (I := I) (M := M) g fseq N) 4 t ≤ Φ4)
    (hE5 : ∀ N : ℕ, ∫ t,
      galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g N)
        (galerkinSolutionMode (I := I) (M := M) g fseq N) 5 t
        ∂(timeMeasure T) ≤ Φ5)
    (hKarm : 0 ≤ Karm)
    (hmass : ∀
      (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
      (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ)
      {R4 : ℝ},
      Real.sqrt (∑ i ∈ F,
        tensorSobolevWeight (I := I) (M := M) i 4 * (c i) ^ 2) ≤ R4 →
      ∀ m : ℕ,
        Real.sqrt (∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
            ((galerkinActionVectorBackground (I := I) (M := M) g gBase
              (lowRegularityStateRadius_pos K.top_nonneg K.slope_nonneg K.outer_pos K.realize_pos).le
              K.threshold_lt
              (lowRegularityMetricRealization (I := I) (M := M) g
                (Ctop := K.top) (B1 := K.slope) (ρ := K.outer)
                K.realize_pos.le hsol.hreal) F c).coeff i) ^ 2) ≤
          Karm * (K.threshold / (1 - K.threshold) ^ 2 +
              lowRegularityStateRadius K.top K.slope K.outer K.realize) *
            Real.sqrt (∑ i ∈ F,
              tensorSobolevWeight (I := I) (M := M) i ((m : ℝ) + 2) *
                (c i) ^ 2) +
          (Ca1 R4 m + Ca2 m *
              (1 + Real.sqrt (∑ i ∈ F,
                tensorSobolevWeight (I := I) (M := M) i 5 * (c i) ^ 2))) *
            Real.sqrt (∑ i ∈ F,
              tensorSobolevWeight (I := I) (M := M) i ((m : ℝ) + 1) *
                (c i) ^ 2))
    (habs : Karm * (K.threshold / (1 - K.threshold) ^ 2 +
      lowRegularityStateRadius K.top K.slope K.outer K.realize) < 1 / 4) :
    ∀ k : ℕ, ∃ Φ : ℝ, ∀ N : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g N)
        (galerkinSolutionMode (I := I) (M := M) g fseq N)
        (5 + (k : ℝ)) t ≤ Φ := by
  classical
  let U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    galerkinSolutionMode (I := I) (M := M) g fseq
  let R4 : ℝ := Real.sqrt (max Φ4 0)
  have hE4cap : ∀ N : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Real.sqrt (galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g N) (U N) 4 t) ≤ R4 := by
    intro N t ht
    dsimp only [R4, U]
    exact Real.sqrt_le_sqrt ((hE4 N t ht).trans (le_max_left _ _))
  let EE5 : ℕ → ℝ → ℝ := fun N => Set.IccExtend hT.le
    (fun p : Set.Icc (0 : ℝ) T => galerkinEnergy (I := I) (M := M)
      (eigenIdxFinset (I := I) (M := M) g N) (U N) 5 p.1)
  have hEE5c : ∀ N, Continuous (EE5 N) := by
    intro N
    exact Continuous.Icc_extend'
      (galerkinEnergy_continuousOn (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g N) (U N) 5
        (by simpa only [U] using hUcont N)).domRestrict
  have hEE5nn : ∀ N, ∀ s : ℝ, 0 ≤ EE5 N s := fun N s =>
    galerkinEnergy_nonneg (I := I) (M := M) _ _ _ _
  have hEE5eq : ∀ N, ∀ s ∈ Set.Icc (0 : ℝ) T,
      EE5 N s = galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g N) (U N) 5 s :=
    fun N s hs => Set.IccExtend_of_mem hT.le _ hs
  let P5 : ℕ → ℝ → ℝ := fun N t => ∫ s in (0 : ℝ)..t, EE5 N s
  have hP5Has : ∀ N, ∀ t : ℝ, HasDerivAt (P5 N) (EE5 N t) t := by
    intro N t
    exact intervalIntegral.integral_hasDerivAt_right
      ((hEE5c N).intervalIntegrable 0 t)
      (hEE5c N).aestronglyMeasurable.stronglyMeasurableAtFilter
      (hEE5c N).continuousAt
  have hP50 : ∀ N, P5 N 0 = 0 := fun N => intervalIntegral.integral_same
  have hP5nn : ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ P5 N t := by
    intro N t ht
    exact intervalIntegral.integral_nonneg ht.1 (fun s _ => hEE5nn N s)
  have hP5cont : ∀ N, ContinuousOn (P5 N) (Set.Icc (0 : ℝ) T) := by
    intro N
    exact (continuous_iff_continuousAt.2
      (fun t => (hP5Has N t).continuousAt)).continuousOn
  have hP5deriv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (P5 N)
        (galerkinEnergy (I := I) (M := M)
          (eigenIdxFinset (I := I) (M := M) g N) (U N) 5 t)
        (Set.Ici t) t := by
    intro N t ht
    have h := hP5Has N t
    rw [hEE5eq N t ⟨ht.1, ht.2.le⟩] at h
    exact h.hasDerivWithinAt
  have hP5bd : ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T, P5 N t ≤ Φ5 := by
    intro N t ht
    have hTint : ∫ s in (0 : ℝ)..T, EE5 N s = ∫ s,
        galerkinEnergy (I := I) (M := M)
          (eigenIdxFinset (I := I) (M := M) g N) (U N) 5 s
          ∂(timeMeasure T) := by
      rw [intervalIntegral.integral_congr
        (g := fun s => galerkinEnergy (I := I) (M := M)
          (eigenIdxFinset (I := I) (M := M) g N) (U N) 5 s)
        (by rw [Set.uIcc_of_le hT.le]; exact fun s hs => hEE5eq N s hs),
        intervalIntegral.integral_of_le hT.le, timeMeasure,
        MeasureTheory.integral_Icc_eq_integral_Ioc]
    have hsplit : P5 N t + ∫ s in t..T, EE5 N s = ∫ s in (0 : ℝ)..T, EE5 N s :=
      intervalIntegral.integral_add_adjacent_intervals
        ((hEE5c N).intervalIntegrable 0 t) ((hEE5c N).intervalIntegrable t T)
    have hrest : 0 ≤ ∫ s in t..T, EE5 N s :=
      intervalIntegral.integral_nonneg ht.2 (fun s _ => hEE5nn N s)
    have hfin := hE5 N
    rw [← hTint] at hfin
    linarith
  have hRpos : 0 < lowRegularityStateRadius K.top K.slope K.outer K.realize :=
    lowRegularityStateRadius_pos K.top_nonneg K.slope_nonneg K.outer_pos K.realize_pos
  let hrealR := lowRegularityMetricRealization (I := I) (M := M) g
    (Ctop := K.top) (B1 := K.slope) (ρ := K.outer) K.realize_pos.le hsol.hreal
  obtain ⟨Cseed, hCseed, hseed⟩ := exists_zero_state_deTurck_remainder_spectral_bound (I := I) (M := M) g gBase
    hRpos K.threshold_lt hrealR hsol.hcore
  let α : ℝ := Karm * (K.threshold / (1 - K.threshold) ^ 2 +
    lowRegularityStateRadius K.top K.slope K.outer K.realize)
  have hα : 0 ≤ α := by
    dsimp only [α]
    exact mul_nonneg hKarm (add_nonneg
      (div_nonneg hsol.hδ0 (sq_nonneg _)) hRpos.le)
  intro k
  let m : ℕ := 4 + k
  let A : ℝ := Ca1 R4 m
  let B : ℝ := Ca2 m
  let Cmid : ℝ := 2 * A ^ 2
  let Crid : ℝ := 4 * B ^ 2
  have hCmid : 0 ≤ Cmid := mul_nonneg (by norm_num) (sq_nonneg A)
  have hCrid : 0 ≤ Crid := mul_nonneg (by norm_num) (sq_nonneg B)
  have hclosure : ∀ N : ℕ, ∀ t ∈ Set.Ico (0 : ℝ) T,
      2 * ∑ i ∈ eigenIdxFinset (I := I) (M := M) g N,
          tensorSobolevWeight (I := I) (M := M) i (5 + (k : ℝ)) *
            (U N t i * galTameForce (I := I) (M := M) g 1 hRpos.le
              (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g gBase K.threshold_lt K.top_nonneg K.slope_nonneg
                K.outer_pos K.realize_pos hsol.hreal)
              (eigenIdxFinset (I := I) (M := M) g N) (U N t) i) ≤
        (2 * α + 1) * galerkinEnergy (I := I) (M := M)
            (eigenIdxFinset (I := I) (M := M) g N) (U N)
            (5 + (k : ℝ) + 1) t +
          (Cmid + Crid * (1 + galerkinEnergy (I := I) (M := M)
              (eigenIdxFinset (I := I) (M := M) g N) (U N) 5 t)) *
            galerkinEnergy (I := I) (M := M)
              (eigenIdxFinset (I := I) (M := M) g N) (U N)
              (5 + (k : ℝ)) t +
          2 * Cseed (5 + k) * Real.sqrt (galerkinEnergy (I := I) (M := M)
            (eigenIdxFinset (I := I) (M := M) g N) (U N)
            (5 + (k : ℝ)) t) + 0 := by
    intro N t ht
    let F := eigenIdxFinset (I := I) (M := M) g N
    let arm := galerkinActionVectorBackground (I := I) (M := M) g gBase hRpos.le K.threshold_lt hrealR F (U N t)
    let seed := boundedDeTurckRemainderOnLowerState (I := I) (M := M) g gBase K.threshold_lt K.top_nonneg K.slope_nonneg
      K.outer_pos K.realize_pos hsol.hreal
      ⟨0, zero_mem_lowerState (I := I) (M := M) g 1 hRpos.le⟩
    let force := galTameForce (I := I) (M := M) g 1 hRpos.le
      (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g gBase K.threshold_lt K.top_nonneg K.slope_nonneg
        K.outer_pos K.realize_pos hsol.hreal) F (U N t)
    have hsplit : ∀ i ∈ F, force i = arm.coeff i + seed.coeff i := by
      intro i hi
      dsimp only [force, arm, seed]
      rw [galForceTermBackground (I := I) (M := M) g gBase K.threshold_lt hsol.hδ0 hsol.hδ3
        K.top_nonneg K.slope_nonneg K.outer_pos K.realize_pos hsol.hreal hsol.hcore F (U N t) i,
        if_pos hi]
      simp only [galerkinActionVectorBackground]
      module
    have hstatRaw := hseed (5 + k) F
    have hstat : ∑ i ∈ F,
        tensorSobolevWeight (I := I) (M := M) i (5 + (k : ℝ)) *
          (seed.coeff i) ^ 2 ≤ Cseed (5 + k) ^ 2 := by
      simpa only [seed, boundedDeTurckRemainderOnLowerState, Nat.cast_add,
        Nat.cast_ofNat] using hstatRaw
    let E5 : ℝ := galerkinEnergy (I := I) (M := M) F (U N) 5 t
    let q : ℝ := Real.sqrt E5
    let β : ℝ := A + B * (1 + q)
    have hE5nn : 0 ≤ E5 := galerkinEnergy_nonneg (I := I) (M := M) _ _ _ _
    have hq0 : 0 ≤ q := Real.sqrt_nonneg _
    have hq2 : q ^ 2 = E5 := Real.sq_sqrt hE5nn
    have hqbound : (1 + q) ^ 2 ≤ 2 * (1 + E5) := by
      nlinarith [sq_nonneg (q - 1)]
    have hβ : β ^ 2 ≤ Cmid + Crid * (1 + E5) := by
      have hy : (B * (1 + q)) ^ 2 ≤ B ^ 2 * (2 * (1 + E5)) := by
        nlinarith [mul_le_mul_of_nonneg_left hqbound (sq_nonneg B)]
      dsimp only [β, Cmid, Crid]
      nlinarith [sq_nonneg (A - B * (1 + q))]
    have hladder :
        Real.sqrt (∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i ((5 + (k : ℝ)) - 1) *
            (arm.coeff i) ^ 2) ≤
          α * Real.sqrt (∑ i ∈ F,
            tensorSobolevWeight (I := I) (M := M) i ((5 + (k : ℝ)) + 1) *
              (U N t i) ^ 2) +
          β * Real.sqrt (∑ i ∈ F,
            tensorSobolevWeight (I := I) (M := M) i (5 + (k : ℝ)) *
              (U N t i) ^ 2) := by
      have haction :
          galerkinActionVectorBackground (I := I) (M := M) g gBase
              (lowRegularityStateRadius_pos K.top_nonneg K.slope_nonneg
                K.outer_pos K.realize_pos).le K.threshold_lt
              (lowRegularityMetricRealization (I := I) (M := M) g
                (Ctop := K.top) (B1 := K.slope) (ρ := K.outer)
                K.realize_pos.le hsol.hreal) F (U N t) = arm := by
        rfl
      rw [← haction]
      have hm := hmass F (U N t) (hE4cap N t (Set.Ico_subset_Icc_self ht)) m
      dsimp only [α, β, A, B, E5, q, m, F] at hm ⊢
      rw [show (5 + (k : ℝ)) - 1 = ((4 + k : ℕ) : ℝ) by push_cast; ring,
        show (5 + (k : ℝ)) + 1 = ((4 + k : ℕ) : ℝ) + 2 by push_cast; ring,
        show (5 + (k : ℝ)) = ((4 + k : ℕ) : ℝ) + 1 by push_cast; ring]
      exact hm
    have hres := two_mul_sum_ladder_le (I := I) (M := M) F (5 + (k : ℝ))
      (U N t) (fun i => arm.coeff i) (fun i => seed.coeff i) force
      (hCseed (5 + k)) (by norm_num : (0 : ℝ) < 1) hsplit hladder hstat
    have hE : 0 ≤ galerkinEnergy (I := I) (M := M) F (U N) (5 + (k : ℝ)) t :=
      galerkinEnergy_nonneg (I := I) (M := M) _ _ _ _
    have hβmul := mul_le_mul_of_nonneg_right hβ hE
    dsimp only [F, force] at hres ⊢
    dsimp only [E5] at hβmul
    unfold galerkinEnergy at hβmul ⊢
    norm_num only [div_one] at hres
    exact hres.trans (by linarith)
  have hinit : ∀ N, galerkinEnergy (I := I) (M := M)
      (eigenIdxFinset (I := I) (M := M) g N) (U N) (5 + (k : ℝ)) 0 ≤ 0 := by
    intro N
    unfold galerkinEnergy
    have hz : ∑ i ∈ eigenIdxFinset (I := I) (M := M) g N,
        tensorSobolevWeight (I := I) (M := M) i (5 + (k : ℝ)) *
          U N 0 i ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      dsimp only [U]
      rw [hUinit N i]
      ring
    rw [hz]
  refine gal_rider_bound_at (I := I) (M := M) (g := g)
    (r := 0) (s₀ := 2) (U := U)
    (Fseq := fun N t => galTameForce (I := I) (M := M) g 1 hRpos.le
      (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g gBase K.threshold_lt K.top_nonneg K.slope_nonneg
        K.outer_pos K.realize_pos hsol.hreal)
      (eigenIdxFinset (I := I) (M := M) g N) (U N t))
    (sseq := fun N => eigenIdxFinset (I := I) (M := M) g N)
    (T := T) (σ := 5 + (k : ℝ)) (ρ := 5) (Cδ := 2 * α + 1)
    (Cmid := Cmid) (seed := 2 * Cseed (5 + k)) (B0 := 0) (c₀ := 0)
    (Crid := Crid) (B := Φ5) (P := P5)
    (by dsimp only [α] at habs ⊢; nlinarith) hCmid
    (mul_nonneg (by norm_num) (hCseed (5 + k))) le_rfl hCrid
    hP50 hP5nn hP5cont hP5deriv hP5bd
    (by simpa only [U] using hUcont) (by simpa only [U] using hUderiv)
    hclosure hinit

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
