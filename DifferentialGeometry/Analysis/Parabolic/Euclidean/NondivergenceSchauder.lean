import DifferentialGeometry.Analysis.Parabolic.Euclidean.BallInteriorLocalSource
import DifferentialGeometry.Analysis.Parabolic.Euclidean.NondivergenceLocalization

noncomputable section

open Matrix Real Set
open scoped NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

open DifferentialGeometry.Analysis.Schauder

private abbrev Euc (n : Type*) := EuclideanSpace Real n

variable {n F : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]

def parabolicNondivergenceRescaledInteriorSchauderConst
    (principal : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : (Matrix.of fun i j ↦ principal i j p0).PosDef)
    (alpha rho : NNReal) (Ka : n → n → NNReal)
    (Kb Bb : n → NNReal) (Kc Bc Ksource Ku Kdu Bsource Mu Mdu : NNReal) :
    NNReal :=
  let tau : Real := 3 / 8
  let outerRadius : Real := 1 / 2
  let principalExtension :=
    parabolicMatrixCoefficientRescaleExtension
      tau outerRadius rho p0 principal
  let hAExtension := parabolicMatrixCoefficientRescaleExtension_posDef
    tau outerRadius rho p0 principal hA
  let principalHolder : n → n → NNReal := fun i j ↦
    Ka i j * rho ^ (alpha : Real)
  let principalBound : n → n → NNReal := fun i j ↦
    ‖principal i j p0‖₊ + principalHolder i j
  let driftHolder : n → NNReal := fun i ↦
    Kb i * rho ^ (alpha : Real) * rho
  let driftBound : n → NNReal := fun i ↦ rho * Bb i
  let potentialHolder : NNReal := Kc * rho ^ (alpha : Real) * rho ^ 2
  let potentialBound : NNReal := rho ^ 2 * Bc
  let sourceHolder : NNReal := Ksource * rho ^ (alpha : Real) * rho ^ 2
  let sourceBound : NNReal := rho ^ 2 * Bsource
  let solutionHolder : NNReal := Ku * rho ^ (alpha : Real)
  let spatialDerivativeHolder : NNReal := Kdu * rho ^ (alpha : Real) * rho
  let spatialDerivativeBound : NNReal := rho * Mdu
  parabolicC2HolderRescaleConst 1 alpha
    (parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst
      principalExtension (parabolicPoint tau 0) hAExtension alpha
      (1 / 4) (5 / 16) (7 / 16) (1 / 2) 0
      (by norm_num : (0 : Real) ≤ 1 / 4)
      (by norm_num : (1 / 4 : Real) < 1 / 2)
      (sourceHolder + parabolicLowerOrderHolderConst
        driftHolder driftBound potentialHolder spatialDerivativeHolder
        solutionHolder spatialDerivativeBound potentialBound Mu)
      spatialDerivativeHolder solutionHolder
      (sourceBound + parabolicLowerOrderSupConst
        driftBound potentialBound spatialDerivativeBound Mu)
      spatialDerivativeBound Mu principalBound principalHolder
      principalHolder (5 / 8))

theorem parabolic_nondivergence_rescaled_interior_schauder_estimate
    {alpha Ksource Kc Ku KdtimeU Kdu Kd2u Bsource Bc
      Mu MdtimeU Mdu Md2u : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (principal : n → n → ParabolicPoint (Euc n) → Real)
    (drift : n → ParabolicPoint (Euc n) → Real)
    (potential : ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : (Matrix.of fun i j ↦ principal i j p0).PosDef)
    (Ka : n → n → NNReal) (Kb Bb : n → NNReal)
    (maxRadius : Real) (rho : NNReal)
    (hscale : IsParabolicNondivergenceSchauderScale
      principal drift potential p0 hA alpha Ka Kb Bb Kc Bc
        maxRadius (5 / 8) rho)
    (u dtimeU : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real → BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (huTime : ∀ s ∈ parabolicRescaleTimeInterval rho p0 (3 / 8),
      HasDerivAt u (dtimeU s) s)
    (hu : ∀ s ∈ parabolicRescaleTimeInterval rho p0 (3 / 8), ∀ x,
      HasFDerivAt (u s : Euc n → F) (du s x) x)
    (hdu : ∀ s ∈ parabolicRescaleTimeInterval rho p0 (3 / 8), ∀ x,
      HasFDerivAt (du s : Euc n → Euc n →L[Real] F) (d2u s x) x)
    (huCont : Continuous u)
    (hsourceHolder : HolderWith Ksource alpha
      ((Metric.ball p0 rho).restrict
        (parabolicNondivergenceOperator principal drift potential
          (fun t x ↦ u t x))))
    (hsourceNorm : ∀ p, p ∈ Metric.ball p0 rho →
      ‖parabolicNondivergenceOperator principal drift potential
        (fun t x ↦ u t x) p‖ ≤ Bsource)
    (huHolder : HolderWith Ku alpha
      ((parabolicCylinder (parabolicRescaleTimeInterval rho p0 (3 / 8))
        Set.univ).restrict (fun p ↦ u p.time p.space)))
    (hdtimeUHolder : HolderWith KdtimeU alpha
      ((parabolicCylinder (parabolicRescaleTimeInterval rho p0 (3 / 8))
        Set.univ).restrict (fun p ↦ dtimeU p.time p.space)))
    (hduHolder : HolderWith Kdu alpha
      ((parabolicCylinder (parabolicRescaleTimeInterval rho p0 (3 / 8))
        Set.univ).restrict (fun p ↦ du p.time p.space)))
    (hd2uHolder : HolderWith Kd2u alpha
      ((parabolicCylinder (parabolicRescaleTimeInterval rho p0 (3 / 8))
        Set.univ).restrict (fun p ↦ d2u p.time p.space)))
    (huNorm : ∀ p,
      p ∈ parabolicCylinder (parabolicRescaleTimeInterval rho p0 (3 / 8))
        Set.univ → ‖u p.time p.space‖ ≤ Mu)
    (hdtimeUNorm : ∀ p,
      p ∈ parabolicCylinder (parabolicRescaleTimeInterval rho p0 (3 / 8))
        Set.univ → ‖dtimeU p.time p.space‖ ≤ MdtimeU)
    (hduNorm : ∀ p,
      p ∈ parabolicCylinder (parabolicRescaleTimeInterval rho p0 (3 / 8))
        Set.univ → ‖du p.time p.space‖ ≤ Mdu)
    (hd2uNorm : ∀ p,
      p ∈ parabolicCylinder (parabolicRescaleTimeInterval rho p0 (3 / 8))
        Set.univ → ‖d2u p.time p.space‖ ≤ Md2u) :
    eParabolicC2HolderGaugeOn alpha
        (Metric.ball (parabolicPoint 0 0) (1 / 4))
        (fun t x ↦ BoundedContinuousFunction.parabolicRescaleAt
          rho p0 u t x) ≤
      parabolicNondivergenceRescaledInteriorSchauderConst
        principal p0 hA alpha rho Ka Kb Bb Kc Bc
        Ksource Ku Kdu Bsource Mu Mdu := by
  let tau : Real := 3 / 8
  let outerRadius : Real := 1 / 2
  let normalizedEnd : Real := 3 / 4
  let normalizedEstimateEnd : Real := 5 / 8
  let Q := parabolicCylinder (Set.Icc (0 : Real) normalizedEnd)
    (Set.univ : Set (Euc n))
  let Qsource := parabolicCylinder (Set.Icc (0 : Real) normalizedEnd)
    (Metric.ball (0 : Euc n) outerRadius)
  let P := parabolicCylinder (parabolicRescaleTimeInterval rho p0 tau)
    (Set.univ : Set (Euc n))
  let principalExtension := parabolicMatrixCoefficientRescaleExtension
    tau outerRadius rho p0 principal
  let driftExtension := parabolicDriftCoefficientRescaleExtension
    tau outerRadius rho p0 drift
  let potentialExtension := parabolicPotentialCoefficientRescaleExtension
    tau outerRadius rho p0 potential
  let v := BoundedContinuousFunction.parabolicTimeCenteredRescaleAt
    tau rho p0 u
  let dtimeV :=
    BoundedContinuousFunction.parabolicTimeCenteredTimeDerivativeRescaleAt
      tau rho p0 dtimeU
  let dv :=
    BoundedContinuousFunction.parabolicTimeCenteredSpatialDerivativeRescaleAt
      tau rho p0 du
  let d2v :=
    BoundedContinuousFunction.parabolicTimeCenteredSpatialSecondDerivativeRescaleAt
      tau rho p0 d2u
  have hrho : 0 < rho := hscale.1
  have htime : ∀ t ∈ Set.Icc (0 : Real) normalizedEnd,
      |t - tau| ^ (1 / 2 : Real) < 1 := by
    intro t ht
    apply Real.rpow_lt_one (abs_nonneg _) _ (by norm_num)
    rw [abs_lt]
    dsimp only [tau, normalizedEnd] at ht ⊢
    constructor <;> linarith [ht.1, ht.2]
  have hmap : MapsTo (parabolicTimeCenteredDilationAt tau rho p0) Q P := by
    simpa only [Q, P, tau, normalizedEnd,
      show (2 : Real) * (3 / 8) = 3 / 4 by norm_num] using
      parabolicTimeCenteredDilationAt_mapsTo_rescaleTimeCylinder
        (V := Euc n) (3 / 8) rho p0
  have hQsourceBall : Qsource ⊆
      Metric.ball (parabolicPoint tau (0 : Euc n)) 1 := by
    intro p hp
    rw [Metric.mem_ball, ← parabolicPoint_time_space p,
      dist_parabolicPoint]
    apply max_lt
    · exact htime p.time hp.1
    · exact (hp.2.trans (by norm_num : outerRadius < 1))
  have hmapSource : MapsTo
      (parabolicTimeCenteredDilationAt tau rho p0) Qsource
      (Metric.ball p0 rho) := by
    intro p hp
    have hball := parabolicTimeCenteredDilationAt_mapsTo_ball
      tau rho hrho 1 p0 (hQsourceBall hp)
    simpa only [mul_one, NNReal.smul_def] using hball
  have htimeMem : ∀ s ∈ Set.Icc (0 : Real) normalizedEnd,
      p0.time + (rho : Real) ^ 2 * (s - tau) ∈
        parabolicRescaleTimeInterval rho p0 tau := by
    intro s hs
    exact (hmap (x := parabolicPoint s (0 : Euc n))
      ⟨hs, Set.mem_univ _⟩).1
  have hspace : ∀ p, p ∈ Qsource → ContDiff Real 2
      (u (p0.time + (rho : Real) ^ 2 * (p.time - tau)) :
        Euc n → F) := by
    intro p hp
    exact contDiff_two_of_hasFDerivAt _ _ _
      (hu _ (htimeMem p.time hp.1)) (hdu _ (htimeMem p.time hp.1))
  obtain ⟨hAExtension, ha, homega, haNorm, hb, hbNorm,
      hc, hcNorm, hsmall⟩ :=
    exists_parabolicNondivergenceCoefficientRescaleExtension_schauder_bounds
      principal drift potential p0 hA alpha Ka Kb Bb Kc Bc
      maxRadius normalizedEstimateEnd rho hscale tau
      (J := Set.Icc (0 : Real) normalizedEnd)
      (R := outerRadius) (by norm_num) (by norm_num) htime
  have hQsourceQ : Qsource ⊆ Q := by
    intro p hp
    exact ⟨hp.1, Set.mem_univ _⟩
  have hbLocal : ∀ i, HolderWith
      (Kb i * rho ^ (alpha : Real) * rho) alpha
      (Qsource.restrict (driftExtension i)) := by
    intro i
    exact ((HolderWith.restrict_iff.mp (hb i)).mono hQsourceQ).holderWith
  have hcLocal : HolderWith
      (Kc * rho ^ (alpha : Real) * rho ^ 2) alpha
      (Qsource.restrict potentialExtension) :=
    ((HolderWith.restrict_iff.mp hc).mono hQsourceQ).holderWith
  have hbNormLocal : ∀ i p, p ∈ Qsource →
      ‖driftExtension i p‖ ≤ ((rho * Bb i : NNReal) : Real) := by
    intro i p hp
    exact hbNorm i p (hQsourceQ hp)
  have hcNormLocal : ∀ p, p ∈ Qsource →
      ‖potentialExtension p‖ ≤ ((rho ^ 2 * Bc : NNReal) : Real) := by
    intro p hp
    exact hcNorm p (hQsourceQ hp)
  have huTimeV : ∀ s ∈ Set.Icc (0 : Real) normalizedEnd,
      HasDerivAt v (dtimeV s) s := by
    intro s hs
    exact BoundedContinuousFunction.hasDerivAt_parabolicTimeCenteredRescaleAt
      tau rho p0 u dtimeU s (huTime _ (htimeMem s hs))
  have huV : ∀ s ∈ Set.Icc (0 : Real) normalizedEnd, ∀ x,
      HasFDerivAt (v s : Euc n → F) (dv s x) x := by
    intro s hs x
    exact BoundedContinuousFunction.hasFDerivAt_parabolicTimeCenteredRescaleAt
      tau rho p0 u du s x
        (hu _ (htimeMem s hs) (p0.space + (rho : Real) • x))
  have hduV : ∀ s ∈ Set.Icc (0 : Real) normalizedEnd, ∀ x,
      HasFDerivAt (dv s : Euc n → Euc n →L[Real] F) (d2v s x) x := by
    intro s hs x
    exact
      BoundedContinuousFunction.hasFDerivAt_parabolicTimeCenteredSpatialDerivativeRescaleAt
        tau rho p0 du d2u s x
          (hdu _ (htimeMem s hs) (p0.space + (rho : Real) • x))
  have huContV : Continuous v :=
    BoundedContinuousFunction.continuous_parabolicTimeCenteredRescaleAt
      tau rho p0 u huCont
  have hsourceHolderV :=
    parabolicNondivergenceOperator_timeCenteredRescaleExtension_holderWith
      (Q := Qsource) tau rho p0 principal drift potential u
      (fun p hp ↦ Metric.ball_subset_closedBall hp.2) hspace hmapSource
      hsourceHolder
  have hsourceNormV :=
    norm_parabolicNondivergenceOperator_timeCenteredRescaleExtension_le
      (Q := Qsource) tau rho p0 principal drift potential u Bsource
      (fun p hp ↦ Metric.ball_subset_closedBall hp.2) hspace hmapSource
      hsourceNorm
  have hsourceNormV' : ∀ p, p ∈ Qsource →
      ‖parabolicNondivergenceOperator principalExtension driftExtension
        potentialExtension (fun t x ↦ v t x) p‖ ≤
        ((rho ^ 2 * Bsource : NNReal) : Real) := by
    intro p hp
    simpa only [principalExtension, driftExtension, potentialExtension, v,
      NNReal.coe_mul, NNReal.coe_pow] using hsourceNormV p hp
  have huHolderV :=
    BoundedContinuousFunction.parabolicTimeCenteredRescaleAt_holderWith
      tau rho p0 u hmap huHolder
  have hdtimeUHolderV :=
    BoundedContinuousFunction.parabolicTimeCenteredTimeDerivativeRescaleAt_holderWith
      tau rho p0 dtimeU hmap hdtimeUHolder
  have hduHolderV :=
    BoundedContinuousFunction.parabolicTimeCenteredSpatialDerivativeRescaleAt_holderWith
      tau rho p0 du hmap hduHolder
  have hd2uHolderV :=
    BoundedContinuousFunction.parabolicTimeCenteredSpatialSecondDerivativeRescaleAt_holderWith
      tau rho p0 d2u hmap hd2uHolder
  have huNormV :=
    BoundedContinuousFunction.norm_parabolicTimeCenteredRescaleAt_le
      tau rho p0 u Mu hmap huNorm
  have hdtimeUNormV :=
    BoundedContinuousFunction.norm_parabolicTimeCenteredTimeDerivativeRescaleAt_le
      tau rho p0 dtimeU MdtimeU hmap hdtimeUNorm
  have hduNormV :=
    BoundedContinuousFunction.norm_parabolicTimeCenteredSpatialDerivativeRescaleAt_le
      tau rho p0 du Mdu hmap hduNorm
  have hd2uNormV :=
    BoundedContinuousFunction.norm_parabolicTimeCenteredSpatialSecondDerivativeRescaleAt_le
      tau rho p0 d2u Md2u hmap hd2uNorm
  have hdtimeUNormV' : ∀ p, p ∈ Q →
      ‖dtimeV p.time p.space‖ ≤
        ((rho ^ 2 * MdtimeU : NNReal) : Real) := by
    intro p hp
    simpa only [dtimeV, NNReal.coe_mul, NNReal.coe_pow] using
      hdtimeUNormV p hp
  have hduNormV' : ∀ p, p ∈ Q →
      ‖dv p.time p.space‖ ≤ ((rho * Mdu : NNReal) : Real) := by
    intro p hp
    simpa only [dv, NNReal.coe_mul] using hduNormV p hp
  have hd2uNormV' : ∀ p, p ∈ Q →
      ‖d2v p.time p.space‖ ≤ ((rho ^ 2 * Md2u : NNReal) : Real) := by
    intro p hp
    simpa only [d2v, NNReal.coe_mul, NNReal.coe_pow] using
      hd2uNormV p hp
  have hlocal :=
    parabolic_nondivergence_centered_ball_schauder_estimate_of_local_source_estimates_of_small_freeze_defect
      (alpha := alpha)
      (Ksource := Ksource * rho ^ (alpha : Real) * rho ^ 2)
      (Kc := Kc * rho ^ (alpha : Real) * rho ^ 2)
      (Ku := Ku * rho ^ (alpha : Real))
      (KdtimeU := KdtimeU * rho ^ (alpha : Real) * rho ^ 2)
      (Kdu := Kdu * rho ^ (alpha : Real) * rho)
      (Kd2u := Kd2u * rho ^ (alpha : Real) * rho ^ 2)
      (Bsource := rho ^ 2 * Bsource) (Bc := rho ^ 2 * Bc)
      (Mu := Mu) (MdtimeU := rho ^ 2 * MdtimeU)
      (Mdu := rho * Mdu) (Md2u := rho ^ 2 * Md2u)
      halpha0 halpha1
      (aTime := (1 / 4 : Real)) (t₀ := (5 / 16 : Real))
      (t₁ := (7 / 16 : Real)) (bTime := (1 / 2 : Real))
      (S := normalizedEnd) (T := normalizedEstimateEnd)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (0 : Euc n)
      (r := (1 / 4 : Real)) (R := outerRadius)
      (by norm_num) (by norm_num) (by norm_num)
      principalExtension (parabolicPoint tau 0) hAExtension
      driftExtension potentialExtension v dtimeV dv d2v
      huTimeV huV hduV huContV hsourceHolderV hsourceNormV'
      (fun i ↦ Kb i * rho ^ (alpha : Real) * rho)
      (fun i ↦ rho * Bb i)
      (fun i j ↦ ‖principal i j p0‖₊ +
        Ka i j * rho ^ (alpha : Real))
      (fun i j ↦ Ka i j * rho ^ (alpha : Real))
      (fun i j ↦ Ka i j * rho ^ (alpha : Real))
      hbLocal hcLocal hbNormLocal hcNormLocal ha homega haNorm
      huHolderV hdtimeUHolderV
      hduHolderV hd2uHolderV huNormV hdtimeUNormV' hduNormV'
      hd2uNormV' hsmall
  have hvShift : (fun t x ↦ v (((5 / 16 : Real) + 7 / 16) / 2 + t) x) =
      fun t x ↦ BoundedContinuousFunction.parabolicRescaleAt
        rho p0 u t x := by
    funext t x
    change u (p0.time + (rho : Real) ^ 2 *
        (((5 / 16 : Real) + 7 / 16) / 2 + t - tau))
        (p0.space + (rho : Real) • x) =
      u (p0.time + (rho : Real) ^ 2 * t)
        (p0.space + (rho : Real) • x)
    congr 1
    dsimp only [tau]
    ring_nf
  rw [← hvShift]
  convert hlocal using 1

theorem parabolic_nondivergence_rescaled_interior_schauder_estimate_of_subset
    {alpha Ksource Kc Ku KdtimeU Kdu Kd2u Bsource Bc
      Mu MdtimeU Mdu Md2u : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (principal : n → n → ParabolicPoint (Euc n) → Real)
    (drift : n → ParabolicPoint (Euc n) → Real)
    (potential : ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : (Matrix.of fun i j ↦ principal i j p0).PosDef)
    (Ka : n → n → NNReal) (Kb Bb : n → NNReal)
    (maxRadius : Real) (rho : NNReal)
    (hscale : IsParabolicNondivergenceSchauderScale
      principal drift potential p0 hA alpha Ka Kb Bb Kc Bc
        maxRadius (5 / 8) rho)
    (J : Set Real) (Qsource : Set (ParabolicPoint (Euc n)))
    (hball : Metric.ball p0 rho ⊆ Qsource)
    (htime : parabolicRescaleTimeInterval rho p0 (3 / 8) ⊆ J)
    (u dtimeU : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real → BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (huTime : ∀ s ∈ J, HasDerivAt u (dtimeU s) s)
    (hu : ∀ s ∈ J, ∀ x,
      HasFDerivAt (u s : Euc n → F) (du s x) x)
    (hdu : ∀ s ∈ J, ∀ x,
      HasFDerivAt (du s : Euc n → Euc n →L[Real] F) (d2u s x) x)
    (huCont : Continuous u)
    (hsourceHolder : HolderWith Ksource alpha
      (Qsource.restrict (parabolicNondivergenceOperator
        principal drift potential (fun t x ↦ u t x))))
    (hsourceNorm : ∀ p, p ∈ Qsource →
      ‖parabolicNondivergenceOperator principal drift potential
        (fun t x ↦ u t x) p‖ ≤ Bsource)
    (huHolder : HolderWith Ku alpha
      ((parabolicCylinder J Set.univ).restrict
        (fun p ↦ u p.time p.space)))
    (hdtimeUHolder : HolderWith KdtimeU alpha
      ((parabolicCylinder J Set.univ).restrict
        (fun p ↦ dtimeU p.time p.space)))
    (hduHolder : HolderWith Kdu alpha
      ((parabolicCylinder J Set.univ).restrict
        (fun p ↦ du p.time p.space)))
    (hd2uHolder : HolderWith Kd2u alpha
      ((parabolicCylinder J Set.univ).restrict
        (fun p ↦ d2u p.time p.space)))
    (huNorm : ∀ p, p ∈ parabolicCylinder J Set.univ →
      ‖u p.time p.space‖ ≤ Mu)
    (hdtimeUNorm : ∀ p, p ∈ parabolicCylinder J Set.univ →
      ‖dtimeU p.time p.space‖ ≤ MdtimeU)
    (hduNorm : ∀ p, p ∈ parabolicCylinder J Set.univ →
      ‖du p.time p.space‖ ≤ Mdu)
    (hd2uNorm : ∀ p, p ∈ parabolicCylinder J Set.univ →
      ‖d2u p.time p.space‖ ≤ Md2u) :
    eParabolicC2HolderGaugeOn alpha
        (Metric.ball (parabolicPoint 0 0) (1 / 4))
        (fun t x ↦ BoundedContinuousFunction.parabolicRescaleAt
          rho p0 u t x) ≤
      parabolicNondivergenceRescaledInteriorSchauderConst
        principal p0 hA alpha rho Ka Kb Bb Kc Bc
        Ksource Ku Kdu Bsource Mu Mdu := by
  let Qlocal := parabolicCylinder
    (parabolicRescaleTimeInterval rho p0 (3 / 8))
      (Set.univ : Set (Euc n))
  have hcylinder : Qlocal ⊆ parabolicCylinder J Set.univ := by
    intro p hp
    exact ⟨htime hp.1, Set.mem_univ _⟩
  have hsourceHolderLocal : HolderWith Ksource alpha
      ((Metric.ball p0 rho).restrict
        (parabolicNondivergenceOperator principal drift potential
          (fun t x ↦ u t x))) :=
    ((HolderWith.restrict_iff.mp hsourceHolder).mono hball).holderWith
  have huHolderLocal : HolderWith Ku alpha
      (Qlocal.restrict (fun p ↦ u p.time p.space)) :=
    ((HolderWith.restrict_iff.mp huHolder).mono hcylinder).holderWith
  have hdtimeUHolderLocal : HolderWith KdtimeU alpha
      (Qlocal.restrict (fun p ↦ dtimeU p.time p.space)) :=
    ((HolderWith.restrict_iff.mp hdtimeUHolder).mono hcylinder).holderWith
  have hduHolderLocal : HolderWith Kdu alpha
      (Qlocal.restrict (fun p ↦ du p.time p.space)) :=
    ((HolderWith.restrict_iff.mp hduHolder).mono hcylinder).holderWith
  have hd2uHolderLocal : HolderWith Kd2u alpha
      (Qlocal.restrict (fun p ↦ d2u p.time p.space)) :=
    ((HolderWith.restrict_iff.mp hd2uHolder).mono hcylinder).holderWith
  exact parabolic_nondivergence_rescaled_interior_schauder_estimate
    (alpha := alpha) (Ksource := Ksource) (Kc := Kc) (Ku := Ku)
    (KdtimeU := KdtimeU) (Kdu := Kdu) (Kd2u := Kd2u)
    (Bsource := Bsource) (Bc := Bc) (Mu := Mu)
    (MdtimeU := MdtimeU) (Mdu := Mdu) (Md2u := Md2u)
    halpha0 halpha1 principal drift potential p0 hA Ka Kb Bb
      maxRadius rho hscale u dtimeU du d2u
      (fun s hs ↦ huTime s (htime hs))
      (fun s hs ↦ hu s (htime hs))
      (fun s hs ↦ hdu s (htime hs)) huCont
      hsourceHolderLocal (fun p hp ↦ hsourceNorm p (hball hp))
      huHolderLocal hdtimeUHolderLocal hduHolderLocal hd2uHolderLocal
      (fun p hp ↦ huNorm p (hcylinder hp))
      (fun p hp ↦ hdtimeUNorm p (hcylinder hp))
      (fun p hp ↦ hduNorm p (hcylinder hp))
      (fun p hp ↦ hd2uNorm p (hcylinder hp))

theorem parabolic_nondivergence_rescaled_interior_schauder_estimates_on_parabolic_cylinder
    {alpha Ksource Kc Ku KdtimeU Kdu Kd2u Bsource Bc
      Mu MdtimeU Mdu Md2u : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (principal : n → n → ParabolicPoint (Euc n) → Real)
    (drift : n → ParabolicPoint (Euc n) → Real)
    (potential : ParabolicPoint (Euc n) → Real)
    {a t₀ t₁ b r R : Real}
    (hat₀ : a < t₀) (ht₁b : t₁ < b) (hrR : r < R)
    (center : Euc n)
    (hpos : ∀ p,
      p ∈ parabolicCylinder (Set.Icc t₀ t₁) (Metric.closedBall center r) →
        (Matrix.of fun i j ↦ principal i j p).PosDef)
    (Ka : n → n → NNReal) (Kb Bb : n → NNReal)
    (u dtimeU : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real → BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (huTime : ∀ s ∈ Set.Icc a b, HasDerivAt u (dtimeU s) s)
    (hu : ∀ s ∈ Set.Icc a b, ∀ x,
      HasFDerivAt (u s : Euc n → F) (du s x) x)
    (hdu : ∀ s ∈ Set.Icc a b, ∀ x,
      HasFDerivAt (du s : Euc n → Euc n →L[Real] F) (d2u s x) x)
    (huCont : Continuous u)
    (hsourceHolder : HolderWith Ksource alpha
      ((parabolicCylinder (Set.Icc a b) (Metric.closedBall center R)).restrict
        (parabolicNondivergenceOperator principal drift potential
          (fun t x ↦ u t x))))
    (hsourceNorm : ∀ p,
      p ∈ parabolicCylinder (Set.Icc a b) (Metric.closedBall center R) →
        ‖parabolicNondivergenceOperator principal drift potential
          (fun t x ↦ u t x) p‖ ≤ Bsource)
    (huHolder : HolderWith Ku alpha
      ((parabolicCylinder (Set.Icc a b) Set.univ).restrict
        (fun p ↦ u p.time p.space)))
    (hdtimeUHolder : HolderWith KdtimeU alpha
      ((parabolicCylinder (Set.Icc a b) Set.univ).restrict
        (fun p ↦ dtimeU p.time p.space)))
    (hduHolder : HolderWith Kdu alpha
      ((parabolicCylinder (Set.Icc a b) Set.univ).restrict
        (fun p ↦ du p.time p.space)))
    (hd2uHolder : HolderWith Kd2u alpha
      ((parabolicCylinder (Set.Icc a b) Set.univ).restrict
        (fun p ↦ d2u p.time p.space)))
    (huNorm : ∀ p, p ∈ parabolicCylinder (Set.Icc a b) Set.univ →
      ‖u p.time p.space‖ ≤ Mu)
    (hdtimeUNorm : ∀ p, p ∈ parabolicCylinder (Set.Icc a b) Set.univ →
      ‖dtimeU p.time p.space‖ ≤ MdtimeU)
    (hduNorm : ∀ p, p ∈ parabolicCylinder (Set.Icc a b) Set.univ →
      ‖du p.time p.space‖ ≤ Mdu)
    (hd2uNorm : ∀ p, p ∈ parabolicCylinder (Set.Icc a b) Set.univ →
      ‖d2u p.time p.space‖ ≤ Md2u) :
    (∀ p, p ∈ parabolicCylinder (Set.Icc a b) (Metric.closedBall center R) →
      ContDiff Real 2 (u p.time)) ∧
    ∀ p : ↥(parabolicCylinder (Set.Icc t₀ t₁)
        (Metric.closedBall center r)), ∀ rho : NNReal,
      IsParabolicNondivergenceSchauderScale principal drift potential p.1
        (hpos p.1 p.2) alpha Ka Kb Bb Kc Bc
          (parabolicInteriorRadius a t₀ t₁ b r R) (5 / 8) rho →
      eParabolicC2HolderGaugeOn alpha
          (Metric.ball (parabolicPoint 0 0) (1 / 4 : Real))
          (parabolicRescaleAt rho p.1 (fun t x ↦ u t x)) ≤
        parabolicNondivergenceRescaledInteriorSchauderConst
          principal p.1 (hpos p.1 p.2) alpha rho Ka Kb Bb Kc Bc
          Ksource Ku Kdu Bsource Mu Mdu := by
  constructor
  · intro p hp
    exact contDiff_two_of_hasFDerivAt (u p.time) (du p.time) (d2u p.time)
      (hu p.time hp.1) (hdu p.time hp.1)
  · intro p rho hscale
    let Qouter := parabolicCylinder (Set.Icc a b)
      (Metric.closedBall center R)
    have hball : Metric.ball p.1 rho ⊆ Qouter := by
      intro q hq
      apply ball_parabolicInteriorRadius_subset_parabolicCylinder
        hat₀ ht₁b hrR p.2
      exact Metric.ball_subset_ball hscale.2.2.1 hq
    have htime : parabolicRescaleTimeInterval rho p.1 (3 / 8) ⊆
        Set.Icc a b :=
      parabolicRescaleTimeInterval_subset_of_ball_subset
        rho hscale.1 (3 / 8) (by norm_num) hball
    change eParabolicC2HolderGaugeOn alpha
        (Metric.ball (parabolicPoint 0 0) (1 / 4 : Real))
        (fun t x ↦ BoundedContinuousFunction.parabolicRescaleAt
          rho p.1 u t x) ≤
      parabolicNondivergenceRescaledInteriorSchauderConst
        principal p.1 (hpos p.1 p.2) alpha rho Ka Kb Bb Kc Bc
        Ksource Ku Kdu Bsource Mu Mdu
    exact parabolic_nondivergence_rescaled_interior_schauder_estimate_of_subset
      (alpha := alpha) (Ksource := Ksource) (Kc := Kc) (Ku := Ku)
      (KdtimeU := KdtimeU) (Kdu := Kdu) (Kd2u := Kd2u)
      (Bsource := Bsource) (Bc := Bc) (Mu := Mu)
      (MdtimeU := MdtimeU) (Mdu := Mdu) (Md2u := Md2u)
      (halpha0 := halpha0) (halpha1 := halpha1)
      (principal := principal) (drift := drift) (potential := potential)
      (p0 := p.1) (hA := hpos p.1 p.2) (Ka := Ka) (Kb := Kb) (Bb := Bb)
      (maxRadius := parabolicInteriorRadius a t₀ t₁ b r R)
      (rho := rho) (hscale := hscale) (J := Set.Icc a b)
      (Qsource := Qouter) (hball := hball) (htime := htime)
      (u := u) (dtimeU := dtimeU) (du := du) (d2u := d2u)
      (huTime := huTime) (hu := hu) (hdu := hdu) (huCont := huCont)
      (hsourceHolder := hsourceHolder) (hsourceNorm := hsourceNorm)
      (huHolder := huHolder) (hdtimeUHolder := hdtimeUHolder)
      (hduHolder := hduHolder) (hd2uHolder := hd2uHolder)
      (huNorm := huNorm) (hdtimeUNorm := hdtimeUNorm)
      (hduNorm := hduNorm) (hd2uNorm := hd2uNorm)

theorem exists_parabolic_nondivergence_schauder_estimate
    {alpha Ksource Kc Ku KdtimeU Kdu Kd2u Bsource Bc
      Mu MdtimeU Mdu Md2u : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (principal : n → n → ParabolicPoint (Euc n) → Real)
    (drift : n → ParabolicPoint (Euc n) → Real)
    (potential : ParabolicPoint (Euc n) → Real)
    {a t₀ t₁ b r R : Real}
    (hat₀ : a < t₀) (ht₁b : t₁ < b) (hrR : r < R)
    (center : Euc n)
    (hpos : ∀ p,
      p ∈ parabolicCylinder (Set.Icc t₀ t₁) (Metric.closedBall center r) →
        (Matrix.of fun i j ↦ principal i j p).PosDef)
    (Ka : n → n → NNReal) (Kb Bb : n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Set.Icc a b) (Metric.closedBall center R)).restrict
        (principal i j)))
    (hb : ∀ i, HolderWith (Kb i) alpha
      ((parabolicCylinder (Set.Icc a b) (Metric.closedBall center R)).restrict
        (drift i)))
    (hc : HolderWith Kc alpha
      ((parabolicCylinder (Set.Icc a b) (Metric.closedBall center R)).restrict
        potential))
    (hbNorm : ∀ i p,
      p ∈ parabolicCylinder (Set.Icc a b) (Metric.closedBall center R) →
        ‖drift i p‖ ≤ Bb i)
    (hcNorm : ∀ p,
      p ∈ parabolicCylinder (Set.Icc a b) (Metric.closedBall center R) →
        ‖potential p‖ ≤ Bc)
    (u dtimeU : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real → BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (huTime : ∀ s ∈ Set.Icc a b, HasDerivAt u (dtimeU s) s)
    (hu : ∀ s ∈ Set.Icc a b, ∀ x,
      HasFDerivAt (u s : Euc n → F) (du s x) x)
    (hdu : ∀ s ∈ Set.Icc a b, ∀ x,
      HasFDerivAt (du s : Euc n → Euc n →L[Real] F) (d2u s x) x)
    (huCont : Continuous u)
    (hsourceHolder : HolderWith Ksource alpha
      ((parabolicCylinder (Set.Icc a b) (Metric.closedBall center R)).restrict
        (parabolicNondivergenceOperator principal drift potential
          (fun t x ↦ u t x))))
    (hsourceNorm : ∀ p,
      p ∈ parabolicCylinder (Set.Icc a b) (Metric.closedBall center R) →
        ‖parabolicNondivergenceOperator principal drift potential
          (fun t x ↦ u t x) p‖ ≤ Bsource)
    (huHolder : HolderWith Ku alpha
      ((parabolicCylinder (Set.Icc a b) Set.univ).restrict
        (fun p ↦ u p.time p.space)))
    (hdtimeUHolder : HolderWith KdtimeU alpha
      ((parabolicCylinder (Set.Icc a b) Set.univ).restrict
        (fun p ↦ dtimeU p.time p.space)))
    (hduHolder : HolderWith Kdu alpha
      ((parabolicCylinder (Set.Icc a b) Set.univ).restrict
        (fun p ↦ du p.time p.space)))
    (hd2uHolder : HolderWith Kd2u alpha
      ((parabolicCylinder (Set.Icc a b) Set.univ).restrict
        (fun p ↦ d2u p.time p.space)))
    (huNorm : ∀ p, p ∈ parabolicCylinder (Set.Icc a b) Set.univ →
      ‖u p.time p.space‖ ≤ Mu)
    (hdtimeUNorm : ∀ p, p ∈ parabolicCylinder (Set.Icc a b) Set.univ →
      ‖dtimeU p.time p.space‖ ≤ MdtimeU)
    (hduNorm : ∀ p, p ∈ parabolicCylinder (Set.Icc a b) Set.univ →
      ‖du p.time p.space‖ ≤ Mdu)
    (hd2uNorm : ∀ p, p ∈ parabolicCylinder (Set.Icc a b) Set.univ →
      ‖d2u p.time p.space‖ ≤ Md2u) :
    ∃ localScale : ∀ p : ↥(parabolicCylinder (Set.Icc t₀ t₁)
        (Metric.closedBall center r)),
      {rho : NNReal //
        IsParabolicNondivergenceSchauderScale principal drift potential p.1
          (hpos p.1 p.2) alpha Ka Kb Bb Kc Bc
          (parabolicInteriorRadius a t₀ t₁ b r R) (5 / 8) rho},
      ∃ s : Finset ↥(parabolicCylinder (Set.Icc t₀ t₁)
          (Metric.closedBall center r)),
        ∃ delta : NNReal, 0 < delta ∧
          (∀ p ∈ s, (delta : Real) ≤
            (((localScale p).1 : Real) * (1 / 4 : Real)) / 2) ∧
          parabolicCylinder (Set.Icc t₀ t₁) (Metric.closedBall center r) ⊆
            ⋃ p ∈ s, Metric.ball p.1
              ((((localScale p).1 : Real) * (1 / 4 : Real)) / 2) ∧
          eParabolicC2HolderGaugeOn alpha
              (parabolicCylinder (Set.Icc t₀ t₁)
                (Metric.closedBall center r)) (fun t x ↦ u t x) ≤
            bufferedParabolicC2HolderGaugeConst alpha
              (∑ p ∈ s, parabolicC2HolderRescaleConst
                (localScale p).1⁻¹ alpha
                (parabolicNondivergenceRescaledInteriorSchauderConst
                  principal p.1 (hpos p.1 p.2) alpha (localScale p).1
                  Ka Kb Bb Kc Bc Ksource Ku Kdu Bsource Mu Mdu))
              delta := by
  let Qouter := parabolicCylinder (Set.Icc a b)
    (Metric.closedBall center R)
  let localBound : ↥(parabolicCylinder (Set.Icc t₀ t₁)
      (Metric.closedBall center r)) → NNReal → NNReal := fun p rho ↦
    parabolicNondivergenceRescaledInteriorSchauderConst
      principal p.1 (hpos p.1 p.2) alpha rho Ka Kb Bb Kc Bc
        Ksource Ku Kdu Bsource Mu Mdu
  obtain ⟨hspace, hlocal⟩ :=
    parabolic_nondivergence_rescaled_interior_schauder_estimates_on_parabolic_cylinder
      (alpha := alpha) (Ksource := Ksource) (Kc := Kc) (Ku := Ku)
      (KdtimeU := KdtimeU) (Kdu := Kdu) (Kd2u := Kd2u)
      (Bsource := Bsource) (Bc := Bc) (Mu := Mu)
      (MdtimeU := MdtimeU) (Mdu := Mdu) (Md2u := Md2u)
      halpha0 halpha1 principal drift potential hat₀ ht₁b hrR center hpos
      Ka Kb Bb u dtimeU du d2u huTime hu hdu huCont hsourceHolder
      hsourceNorm huHolder hdtimeUHolder hduHolder hd2uHolder huNorm
      hdtimeUNorm hduNorm hd2uNorm
  exact exists_parabolicNondivergence_schauder_estimate_of_local_scaledBall_estimates
    principal drift potential hat₀ ht₁b hrR center hpos alpha halpha0
      Ka Kb Bb Kc Bc (5 / 8) ha hb hc hbNorm hcNorm (1 / 4) (by norm_num)
      (by exact (div_le_one (by norm_num : (0 : NNReal) < 4)).2 (by norm_num))
      (fun t x ↦ u t x) hspace localBound hlocal

theorem exists_parabolic_nondivergence_schauder_estimate_of_interpolation
    {alpha Ksource Kc Bsource Bc C M : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (epsilon : NNReal) (hepsilon : 0 < epsilon)
    (principal : n → n → ParabolicPoint (Euc n) → Real)
    (drift : n → ParabolicPoint (Euc n) → Real)
    (potential : ParabolicPoint (Euc n) → Real)
    {a t₀ t₁ b r R : Real}
    (hat₀ : a < t₀) (ht₁b : t₁ < b) (hrR : r < R)
    (center : Euc n)
    (hpos : ∀ p,
      p ∈ parabolicCylinder (Set.Icc t₀ t₁) (Metric.closedBall center r) →
        (Matrix.of fun i j ↦ principal i j p).PosDef)
    (Ka : n → n → NNReal) (Kb Bb : n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Set.Icc a b) (Metric.closedBall center R)).restrict
        (principal i j)))
    (hb : ∀ i, HolderWith (Kb i) alpha
      ((parabolicCylinder (Set.Icc a b) (Metric.closedBall center R)).restrict
        (drift i)))
    (hc : HolderWith Kc alpha
      ((parabolicCylinder (Set.Icc a b) (Metric.closedBall center R)).restrict
        potential))
    (hbNorm : ∀ i p,
      p ∈ parabolicCylinder (Set.Icc a b) (Metric.closedBall center R) →
        ‖drift i p‖ ≤ Bb i)
    (hcNorm : ∀ p,
      p ∈ parabolicCylinder (Set.Icc a b) (Metric.closedBall center R) →
        ‖potential p‖ ≤ Bc)
    (u dtimeU : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real → BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (huTime : ∀ s ∈ Set.Icc a b, HasDerivAt u (dtimeU s) s)
    (hu : ∀ s ∈ Set.Icc a b, ∀ x,
      HasFDerivAt (u s : Euc n → F) (du s x) x)
    (hdu : ∀ s ∈ Set.Icc a b, ∀ x,
      HasFDerivAt (du s : Euc n → Euc n →L[Real] F) (d2u s x) x)
    (huCont : Continuous u)
    (huC2 : IsParabolicC2On
      (parabolicCylinder (Set.Icc a b) Set.univ) (fun t x ↦ u t x))
    (hgauge : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Set.Icc a b) Set.univ)
      (fun t x ↦ u t x) ≤ C)
    (huNorm : ∀ p, p ∈ parabolicCylinder (Set.Icc a b) Set.univ →
      ‖u p.time p.space‖ ≤ M)
    (hsourceHolder : HolderWith Ksource alpha
      ((parabolicCylinder (Set.Icc a b) (Metric.closedBall center R)).restrict
        (parabolicNondivergenceOperator principal drift potential
          (fun t x ↦ u t x))))
    (hsourceNorm : ∀ p,
      p ∈ parabolicCylinder (Set.Icc a b) (Metric.closedBall center R) →
        ‖parabolicNondivergenceOperator principal drift potential
          (fun t x ↦ u t x) p‖ ≤ Bsource) :
    ∃ localScale : ∀ p : ↥(parabolicCylinder (Set.Icc t₀ t₁)
        (Metric.closedBall center r)),
      {rho : NNReal //
        IsParabolicNondivergenceSchauderScale principal drift potential p.1
          (hpos p.1 p.2) alpha Ka Kb Bb Kc Bc
          (parabolicInteriorRadius a t₀ t₁ b r R) (5 / 8) rho},
      ∃ s : Finset ↥(parabolicCylinder (Set.Icc t₀ t₁)
          (Metric.closedBall center r)),
        ∃ delta : NNReal, 0 < delta ∧
          (∀ p ∈ s, (delta : Real) ≤
            (((localScale p).1 : Real) * (1 / 4 : Real)) / 2) ∧
          parabolicCylinder (Set.Icc t₀ t₁) (Metric.closedBall center r) ⊆
            ⋃ p ∈ s, Metric.ball p.1
              ((((localScale p).1 : Real) * (1 / 4 : Real)) / 2) ∧
          eParabolicC2HolderGaugeOn alpha
              (parabolicCylinder (Set.Icc t₀ t₁)
                (Metric.closedBall center r)) (fun t x ↦ u t x) ≤
            bufferedParabolicC2HolderGaugeConst alpha
              (∑ p ∈ s, parabolicC2HolderRescaleConst
                (localScale p).1⁻¹ alpha
                (parabolicNondivergenceRescaledInteriorSchauderConst
                  principal p.1 (hpos p.1 p.2) alpha (localScale p).1
                  Ka Kb Bb Kc Bc Ksource
                  (parabolicValueInterpolationConst epsilon alpha C M)
                  (parabolicSpatialGradientInterpolationConst
                    epsilon alpha C M)
                  Bsource M (2 * M / epsilon + C * epsilon)))
              delta := by
  let Q := parabolicCylinder (Set.Icc a b) (Set.univ : Set (Euc n))
  let e1 := continuousMultilinearCurryFin1 Real (Euc n) F
  let e2 := hessianCurryEquiv (Euc n) F
  have hduEq : ∀ p ∈ Q,
      e1 (parabolicSpatialJet 1 (fun t x ↦ u t x) p) =
        du p.time p.space := by
    intro p hp
    ext v
    simp only [e1, parabolicSpatialJet,
      continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
    rw [(hu p.time hp.1 p.space).fderiv]
    rfl
  have hd2uEq : ∀ p ∈ Q,
      e2 (parabolicSpatialJet 2 (fun t x ↦ u t x) p) =
        d2u p.time p.space := by
    intro p hp
    simpa only [e2, parabolicPoint_time_space] using
      hessianCurryEquiv_parabolicSpatialJet_two_of_hasFDerivAt
        (fun t x ↦ u t x) (fun q ↦ du q.time q.space)
        (fun q ↦ d2u q.time q.space) p.time
        (hu p.time hp.1) (hdu p.time hp.1) p.space
  have hdtimeUEq : ∀ p ∈ Q,
      parabolicTimeDerivative (fun t x ↦ u t x) p =
        dtimeU p.time p.space := by
    intro p hp
    have hpoint : HasDerivAt (fun t ↦ u t p.space)
        (dtimeU p.time p.space) p.time := by
      simpa only [BoundedContinuousFunction.evalCLM_apply] using
        (BoundedContinuousFunction.evalCLM Real p.space).hasFDerivAt
          |>.comp_hasDerivAt p.time (huTime p.time hp.1)
    unfold parabolicTimeDerivative
    rw [hpoint.hasFDerivAt.fderiv]
    simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul]
  have huHolder : HolderWith
      (parabolicValueInterpolationConst epsilon alpha C M) alpha
      (Q.restrict (fun p ↦ u p.time p.space)) := by
    simpa only [Q] using
      parabolicValue_holderWith_restrict_of_interpolation
        (convex_Icc a b) convex_univ epsilon hepsilon halpha1.le
        huC2 hgauge huNorm
  have hjetHolder : HolderWith
      (parabolicSpatialGradientInterpolationConst epsilon alpha C M) alpha
      (Q.restrict (parabolicSpatialJet 1 (fun t x ↦ u t x))) := by
    simpa only [Q] using
      parabolicSpatialJet_one_holderWith_restrict_of_interpolation
        (convex_Icc a b) epsilon hepsilon halpha1.le huC2 hgauge huNorm
  have hduHolder : HolderWith
      (parabolicSpatialGradientInterpolationConst epsilon alpha C M) alpha
      (Q.restrict (fun p ↦ du p.time p.space)) := by
    have hcomp := e1.lipschitz.holderWith.comp hjetHolder
    have hfun : e1 ∘ Q.restrict
        (parabolicSpatialJet 1 (fun t x ↦ u t x)) =
          Q.restrict (fun p ↦ du p.time p.space) := by
      funext p
      exact hduEq p.1 p.2
    rw [hfun] at hcomp
    simpa only [NNReal.coe_one, NNReal.rpow_one, one_mul] using hcomp
  have hdtimeUHolder : HolderWith C alpha
      (Q.restrict (fun p ↦ dtimeU p.time p.space)) := by
    have hbase := parabolicTimeDerivative_holderWith_restrict hgauge
    have hfun : Q.restrict
        (parabolicTimeDerivative (fun t x ↦ u t x)) =
          Q.restrict (fun p ↦ dtimeU p.time p.space) := by
      funext p
      exact hdtimeUEq p.1 p.2
    rwa [hfun] at hbase
  have hd2uHolder : HolderWith C alpha
      (Q.restrict (fun p ↦ d2u p.time p.space)) := by
    have hbase := parabolicSpatialJet_holderWith_restrict hgauge
    have hcomp := e2.lipschitz.holderWith.comp hbase
    have hfun : e2 ∘ Q.restrict
        (parabolicSpatialJet 2 (fun t x ↦ u t x)) =
          Q.restrict (fun p ↦ d2u p.time p.space) := by
      funext p
      exact hd2uEq p.1 p.2
    rw [hfun] at hcomp
    simpa only [NNReal.coe_one, NNReal.rpow_one, one_mul] using hcomp
  have hdtimeUNorm : ∀ p, p ∈ Q → ‖dtimeU p.time p.space‖ ≤ C := by
    intro p hp
    rw [← hdtimeUEq p hp]
    exact parabolicTimeDerivative_norm_le hgauge hp
  have hduNorm : ∀ p, p ∈ Q →
      ‖du p.time p.space‖ ≤ 2 * M / epsilon + C * epsilon := by
    intro p hp
    rw [← hduEq p hp, LinearIsometryEquiv.norm_map]
    exact norm_parabolicSpatialJet_one_le_of_interpolation
      epsilon hepsilon huC2 hgauge huNorm p hp
  have hd2uNorm : ∀ p, p ∈ Q → ‖d2u p.time p.space‖ ≤ C := by
    intro p hp
    rw [← hd2uEq p hp, LinearIsometryEquiv.norm_map]
    exact parabolicSpatialJet_norm_le hgauge (j := 2) (by omega) hp
  simpa only [Q] using
    (exists_parabolic_nondivergence_schauder_estimate
      (alpha := alpha) (Ksource := Ksource) (Kc := Kc)
      (Ku := parabolicValueInterpolationConst epsilon alpha C M)
      (KdtimeU := C)
      (Kdu := parabolicSpatialGradientInterpolationConst epsilon alpha C M)
      (Kd2u := C) (Bsource := Bsource) (Bc := Bc) (Mu := M)
      (MdtimeU := C) (Mdu := 2 * M / epsilon + C * epsilon)
      (Md2u := C) halpha0 halpha1 principal drift potential hat₀ ht₁b hrR
      center hpos Ka Kb Bb ha hb hc hbNorm hcNorm u dtimeU du d2u
      huTime hu hdu huCont hsourceHolder hsourceNorm huHolder
      hdtimeUHolder hduHolder hd2uHolder huNorm hdtimeUNorm hduNorm
      hd2uNorm)

end DifferentialGeometry.Analysis.Parabolic.Euclidean

end
