import DifferentialGeometry.Analysis.Parabolic.Euclidean.NondivergenceSchauder
import DifferentialGeometry.Analysis.Parabolic.Euclidean.BoundedJetInterpolation
import DifferentialGeometry.Analysis.Schauder.ParabolicChartExtension

noncomputable section

open Matrix Real Set
open scoped NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Schauder

open DifferentialGeometry.Analysis.Parabolic.Euclidean

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
  {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners Real E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]

private abbrev EuclN (E : Type uE) [NormedAddCommGroup E]
    [NormedSpace Real E] [FiniteDimensional Real E] :=
  EuclideanSpace Real (Fin (Module.finrank Real E))

theorem parabolic_nondivergence_interior_schauder_estimate_in_euclideanChart_of_small_freeze_defect
    {alpha Ksource Kc Ku KdtimeU Kdu Kd2u Bsource Bc
      Mu MdtimeU Mdu Md2u : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {aTime t₀ t₁ bTime S T : Real}
    (haTime : 0 < aTime) (hat₀ : aTime < t₀) (ht₀t₁ : t₀ ≤ t₁)
    (ht₁b : t₁ < bTime) (hbT : bTime < T) (hTS : T < S)
    (center : EuclN E) {r R Rext : Real}
    (hr : 0 ≤ r) (hrR : r < R) (hRRext : R < Rext)
    (g : Real → SmoothRiemannianMetric I M) (V : Real → M → Real)
    (chartCenter : M) (intrinsicU : Real → M → Real)
    (p0 : ParabolicPoint (EuclN E))
    (u dtimeU : Real → BoundedContinuousFunction (EuclN E) Real)
    (du : Real →
      BoundedContinuousFunction (EuclN E) (EuclN E →L[Real] Real))
    (d2u : Real → BoundedContinuousFunction (EuclN E)
      (EuclN E →L[Real] EuclN E →L[Real] Real))
    (huTime : ∀ s ∈ Icc (0 : Real) S, HasDerivAt u (dtimeU s) s)
    (hu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (u s : EuclN E → Real) (du s x) x)
    (hdu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (du s : EuclN E → EuclN E →L[Real] Real)
        (d2u s x) x)
    (huCont : Continuous u)
    (hrealize : Set.EqOn (fun p ↦ u p.time p.space)
      (fun p ↦ parabolicEuclideanChartRepresentation
        I chartCenter intrinsicU p.time p.space)
      (parabolicCylinder Set.univ (Metric.ball center R)))
    (hsourceHolder : HolderWith Ksource alpha
      ((parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R)).restrict
        (parabolicNondivergenceOperatorInEuclideanChart (I := I)
          g V chartCenter intrinsicU)))
    (hsourceNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R) →
        ‖parabolicNondivergenceOperatorInEuclideanChart (I := I)
          g V chartCenter intrinsicU p‖ ≤ Bsource)
    (Kb Bb : Fin (Module.finrank Real E) → NNReal)
    (A Ka omega : Fin (Module.finrank Real E) →
      Fin (Module.finrank Real E) → NNReal)
    (hA : (Matrix.of fun i j : Fin (Module.finrank Real E) =>
      parabolicChartPrincipalCoefficientExtension (I := I)
        center R Rext g chartCenter p0 i j p0).PosDef)
    (hb : ∀ i, HolderWith (Kb i) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (parabolicChartDriftCoefficientExtension (I := I)
          center R Rext g chartCenter p0 i)))
    (hc : HolderWith Kc alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (parabolicChartPotentialCoefficientExtension (I := I)
          center R Rext V chartCenter p0)))
    (hbNorm : ∀ i p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖parabolicChartDriftCoefficientExtension (I := I)
          center R Rext g chartCenter p0 i p‖ ≤ Bb i)
    (hcNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖parabolicChartPotentialCoefficientExtension (I := I)
          center R Rext V chartCenter p0 p‖ ≤ Bc)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (parabolicChartPrincipalCoefficientExtension (I := I)
          center R Rext g chartCenter p0 i j)))
    (homega : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖parabolicChartPrincipalCoefficientExtension (I := I)
            center R Rext g chartCenter p0 i j p0 -
          parabolicChartPrincipalCoefficientExtension (I := I)
            center R Rext g chartCenter p0 i j p‖ ≤ omega i j)
    (haNorm : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖parabolicChartPrincipalCoefficientExtension (I := I)
          center R Rext g chartCenter p0 i j p‖ ≤ A i j)
    (huHolder : HolderWith Ku alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p ↦ u p.time p.space)))
    (hdtimeUHolder : HolderWith KdtimeU alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p ↦ dtimeU p.time p.space)))
    (hduHolder : HolderWith Kdu alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p ↦ du p.time p.space)))
    (hd2uHolder : HolderWith Kd2u alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p ↦ d2u p.time p.space)))
    (huNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖u p.time p.space‖ ≤ Mu)
    (hdtimeUNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖dtimeU p.time p.space‖ ≤ MdtimeU)
    (hduNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖du p.time p.space‖ ≤ Mdu)
    (hd2uNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖d2u p.time p.space‖ ≤ Md2u)
    (hsmall : spdParabolicSchauderDefectConst
      (fun i j ↦ parabolicChartPrincipalCoefficientExtension (I := I)
        center R Rext g chartCenter p0 i j p0)
      hA alpha Ka omega T < 1) :
    eParabolicC2HolderGaugeInEuclideanChartOn alpha I chartCenter
        (parabolicCylinder (Ioo t₀ t₁) (Metric.ball center r)) intrinsicU ≤
      parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst
        (parabolicChartPrincipalCoefficientExtension (I := I)
          center R Rext g chartCenter p0)
        p0 hA alpha aTime t₀ t₁ bTime center hr hrR
        (Ksource + parabolicLowerOrderHolderConst
          Kb Bb Kc Kdu Ku Mdu Bc Mu)
        Kdu Ku
        (Bsource + parabolicLowerOrderSupConst Bb Bc Mdu Mu)
        Mdu Mu A Ka omega T := by
  let aext := parabolicChartPrincipalCoefficientExtension (I := I)
    center R Rext g chartCenter p0
  let bext := parabolicChartDriftCoefficientExtension (I := I)
    center R Rext g chartCenter p0
  let cext := parabolicChartPotentialCoefficientExtension (I := I)
    center R Rext V chartCenter p0
  let chartU := parabolicEuclideanChartRepresentation I chartCenter intrinsicU
  let Qlocal := parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R)
  let Qglobal := parabolicCylinder (Icc (0 : Real) S) (Set.univ : Set (EuclN E))
  let Urealize := parabolicCylinder Set.univ (Metric.ball center R)
  have hR : 0 ≤ R := hr.trans hrR.le
  have hUrealize : IsOpen Urealize :=
    isOpen_parabolicCylinder isOpen_univ Metric.isOpen_ball
  have hQlocalQglobal : Qlocal ⊆ Qglobal := by
    intro p hp
    exact ⟨hp.1, Set.mem_univ p.space⟩
  have hsourceEq : Set.EqOn
      (parabolicNondivergenceOperator aext bext cext (fun t x ↦ u t x))
      (parabolicNondivergenceOperatorInEuclideanChart (I := I)
        g V chartCenter intrinsicU) Qlocal := by
    intro p hp
    have hpU : p ∈ Urealize := ⟨Set.mem_univ p.time, hp.2⟩
    calc
      parabolicNondivergenceOperator aext bext cext
          (fun t x ↦ u t x) p =
          parabolicNondivergenceOperator aext bext cext chartU p :=
        parabolicNondivergenceOperator_congr_of_eqOn_open
          hUrealize aext bext cext (fun t x ↦ u t x) chartU hpU
            (by simpa only [Urealize, chartU] using hrealize)
      _ = parabolicNondivergenceOperatorInEuclideanChart (I := I)
          g V chartCenter intrinsicU p := by
        exact parabolicNondivergenceOperator_coefficientExtension_eq
          (I := I) center hR hRRext g V chartCenter p0 chartU p
            (Metric.ball_subset_closedBall hp.2)
  have hsourceHolder' : HolderWith Ksource alpha
      (Qlocal.restrict
        (parabolicNondivergenceOperator aext bext cext
          (fun t x ↦ u t x))) := by
    have hfun : Qlocal.restrict
        (parabolicNondivergenceOperator aext bext cext
          (fun t x ↦ u t x)) =
        Qlocal.restrict
          (parabolicNondivergenceOperatorInEuclideanChart (I := I)
            g V chartCenter intrinsicU) := by
      funext p
      exact hsourceEq p.2
    rw [hfun]
    simpa only [Qlocal] using hsourceHolder
  have hsourceNorm' : ∀ p, p ∈ Qlocal →
      ‖parabolicNondivergenceOperator aext bext cext
        (fun t x ↦ u t x) p‖ ≤ Bsource := by
    intro p hp
    rw [hsourceEq hp]
    exact hsourceNorm p (by simpa only [Qlocal] using hp)
  have hbLocal : ∀ i, HolderWith (Kb i) alpha
      (Qlocal.restrict (bext i)) := by
    intro i
    exact ((HolderWith.restrict_iff.mp
      (by simpa only [Qglobal, bext] using hb i)).mono hQlocalQglobal).holderWith
  have hcLocal : HolderWith Kc alpha (Qlocal.restrict cext) :=
    ((HolderWith.restrict_iff.mp
      (by simpa only [Qglobal, cext] using hc)).mono hQlocalQglobal).holderWith
  have hbNormLocal : ∀ i p, p ∈ Qlocal → ‖bext i p‖ ≤ Bb i := by
    intro i p hp
    exact hbNorm i p (by simpa only [Qglobal] using hQlocalQglobal hp)
  have hcNormLocal : ∀ p, p ∈ Qlocal → ‖cext p‖ ≤ Bc := by
    intro p hp
    exact hcNorm p (by simpa only [Qglobal] using hQlocalQglobal hp)
  have hestimate :=
    parabolic_nondivergence_ball_interior_schauder_estimate_of_local_source_estimates_of_small_freeze_defect
      halpha0 halpha1 haTime hat₀ ht₀t₁ ht₁b hbT hTS center hr hrR
      aext p0 hA bext cext u dtimeU du d2u huTime hu hdu huCont
      (by simpa only [Qlocal] using hsourceHolder')
      (by simpa only [Qlocal] using hsourceNorm')
      Kb Bb A Ka omega
      (by simpa only [Qlocal] using hbLocal)
      (by simpa only [Qlocal] using hcLocal)
      (by simpa only [Qlocal] using hbNormLocal)
      (by simpa only [Qlocal] using hcNormLocal)
      (by simpa only [aext] using ha) (by simpa only [aext] using homega)
      (by simpa only [aext] using haNorm) huHolder hdtimeUHolder hduHolder
      hd2uHolder huNorm hdtimeUNorm hduNorm hd2uNorm
      (by simpa only [aext] using hsmall)
  let Qinner := parabolicCylinder (Ioo t₀ t₁) (Metric.ball center r)
  have hQinnerU : Qinner ⊆ Urealize := by
    intro p hp
    exact ⟨Set.mem_univ p.time, Metric.ball_subset_ball hrR.le hp.2⟩
  have hgauge : eParabolicC2HolderGaugeOn alpha Qinner
      (fun t x ↦ u t x) = eParabolicC2HolderGaugeOn alpha Qinner chartU :=
    eParabolicC2HolderGaugeOn_congr_of_eqOn_open
      hUrealize hQinnerU (by simpa only [Urealize, chartU] using hrealize) alpha
  unfold eParabolicC2HolderGaugeInEuclideanChartOn
  rw [← hgauge]
  simpa only [Qinner, aext, bext, cext] using hestimate

theorem exists_parabolic_nondivergence_schauder_estimate_in_euclideanChart
    {alpha Ksource Kc Ku KdtimeU Kdu Kd2u Bsource Bc
      Mu MdtimeU Mdu Md2u : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (g : Real → SmoothRiemannianMetric I M) (V : Real → M → Real)
    (chartCenter : M) (intrinsicU : Real → M → Real)
    {a t₀ t₁ b r R Rext : Real}
    (hat₀ : a < t₀) (ht₁b : t₁ < b) (hrR : r < R) (hRRext : R < Rext)
    (center : EuclN E)
    (hpos : ∀ p,
      p ∈ parabolicCylinder (Set.Icc t₀ t₁) (Metric.closedBall center r) →
        (Matrix.of fun i j : Fin (Module.finrank Real E) ↦
          parabolicChartPrincipalCoefficient (I := I) g chartCenter i j p).PosDef)
    (Ka : Fin (Module.finrank Real E) →
      Fin (Module.finrank Real E) → NNReal)
    (Kb Bb : Fin (Module.finrank Real E) → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Set.Icc a b) (Metric.closedBall center R)).restrict
        (parabolicChartPrincipalCoefficient (I := I) g chartCenter i j)))
    (hb : ∀ i, HolderWith (Kb i) alpha
      ((parabolicCylinder (Set.Icc a b) (Metric.closedBall center R)).restrict
        (parabolicChartDriftCoefficient (I := I) g chartCenter i)))
    (hc : HolderWith Kc alpha
      ((parabolicCylinder (Set.Icc a b) (Metric.closedBall center R)).restrict
        (parabolicChartPotentialCoefficient (I := I) V chartCenter)))
    (hbNorm : ∀ i p,
      p ∈ parabolicCylinder (Set.Icc a b) (Metric.closedBall center R) →
        ‖parabolicChartDriftCoefficient (I := I) g chartCenter i p‖ ≤ Bb i)
    (hcNorm : ∀ p,
      p ∈ parabolicCylinder (Set.Icc a b) (Metric.closedBall center R) →
        ‖parabolicChartPotentialCoefficient (I := I) V chartCenter p‖ ≤ Bc)
    (u dtimeU : Real → BoundedContinuousFunction (EuclN E) Real)
    (du : Real →
      BoundedContinuousFunction (EuclN E) (EuclN E →L[Real] Real))
    (d2u : Real → BoundedContinuousFunction (EuclN E)
      (EuclN E →L[Real] EuclN E →L[Real] Real))
    (huTime : ∀ s ∈ Set.Icc a b, HasDerivAt u (dtimeU s) s)
    (hu : ∀ s ∈ Set.Icc a b, ∀ x,
      HasFDerivAt (u s : EuclN E → Real) (du s x) x)
    (hdu : ∀ s ∈ Set.Icc a b, ∀ x,
      HasFDerivAt (du s : EuclN E → EuclN E →L[Real] Real)
        (d2u s x) x)
    (huCont : Continuous u)
    (hrealize : Set.EqOn (fun p ↦ u p.time p.space)
      (fun p ↦ parabolicEuclideanChartRepresentation
        I chartCenter intrinsicU p.time p.space)
      (parabolicCylinder Set.univ (Metric.ball center Rext)))
    (hsourceHolder : HolderWith Ksource alpha
      ((parabolicCylinder (Set.Icc a b) (Metric.closedBall center R)).restrict
        (parabolicNondivergenceOperatorInEuclideanChart (I := I)
          g V chartCenter intrinsicU)))
    (hsourceNorm : ∀ p,
      p ∈ parabolicCylinder (Set.Icc a b) (Metric.closedBall center R) →
        ‖parabolicNondivergenceOperatorInEuclideanChart (I := I)
          g V chartCenter intrinsicU p‖ ≤ Bsource)
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
        IsParabolicNondivergenceSchauderScale
          (parabolicChartPrincipalCoefficient (I := I) g chartCenter)
          (parabolicChartDriftCoefficient (I := I) g chartCenter)
          (parabolicChartPotentialCoefficient (I := I) V chartCenter)
          p.1 (hpos p.1 p.2) alpha Ka Kb Bb Kc Bc
          (parabolicInteriorRadius a t₀ t₁ b r R) (5 / 8) rho},
      ∃ s : Finset ↥(parabolicCylinder (Set.Icc t₀ t₁)
          (Metric.closedBall center r)),
        ∃ delta : NNReal, 0 < delta ∧
          (∀ p ∈ s, (delta : Real) ≤
            (((localScale p).1 : Real) * (1 / 4 : Real)) / 2) ∧
          parabolicCylinder (Set.Icc t₀ t₁) (Metric.closedBall center r) ⊆
            ⋃ p ∈ s, Metric.ball p.1
              ((((localScale p).1 : Real) * (1 / 4 : Real)) / 2) ∧
          eParabolicC2HolderGaugeInEuclideanChartOn alpha I chartCenter
              (parabolicCylinder (Set.Icc t₀ t₁)
                (Metric.closedBall center r)) intrinsicU ≤
            bufferedParabolicC2HolderGaugeConst alpha
              (∑ p ∈ s, parabolicC2HolderRescaleConst
                (localScale p).1⁻¹ alpha
                (parabolicNondivergenceRescaledInteriorSchauderConst
                  (parabolicChartPrincipalCoefficient (I := I) g chartCenter)
                  p.1 (hpos p.1 p.2) alpha (localScale p).1 Ka Kb Bb Kc Bc
                  Ksource Ku Kdu Bsource Mu Mdu)) delta := by
  let principal := parabolicChartPrincipalCoefficient (I := I) g chartCenter
  let drift := parabolicChartDriftCoefficient (I := I) g chartCenter
  let potential := parabolicChartPotentialCoefficient (I := I) V chartCenter
  let chartU := parabolicEuclideanChartRepresentation I chartCenter intrinsicU
  let Qouter := parabolicCylinder (Set.Icc a b) (Metric.closedBall center R)
  let Qinner := parabolicCylinder (Set.Icc t₀ t₁) (Metric.closedBall center r)
  let Urealize := parabolicCylinder Set.univ (Metric.ball center Rext)
  have hUrealize : IsOpen Urealize :=
    isOpen_parabolicCylinder isOpen_univ Metric.isOpen_ball
  have hQouterU : Qouter ⊆ Urealize := by
    intro p hp
    exact ⟨Set.mem_univ p.time, Metric.closedBall_subset_ball hRRext hp.2⟩
  have hQinnerU : Qinner ⊆ Urealize := by
    intro p hp
    exact ⟨Set.mem_univ p.time,
      Metric.closedBall_subset_ball (hrR.trans hRRext) hp.2⟩
  have hsourceEq : Set.EqOn
      (parabolicNondivergenceOperator principal drift potential
        (fun t x ↦ u t x))
      (parabolicNondivergenceOperatorInEuclideanChart (I := I)
        g V chartCenter intrinsicU) Qouter := by
    intro p hp
    exact parabolicNondivergenceOperator_congr_of_eqOn_open
      hUrealize principal drift potential (fun t x ↦ u t x) chartU
        (hQouterU hp) (by simpa only [Urealize, chartU] using hrealize)
  have hsourceHolder' : HolderWith Ksource alpha
      (Qouter.restrict
        (parabolicNondivergenceOperator principal drift potential
          (fun t x ↦ u t x))) := by
    have hfun : Qouter.restrict
        (parabolicNondivergenceOperator principal drift potential
          (fun t x ↦ u t x)) =
        Qouter.restrict
          (parabolicNondivergenceOperatorInEuclideanChart (I := I)
            g V chartCenter intrinsicU) := by
      funext p
      exact hsourceEq p.2
    rw [hfun]
    simpa only [Qouter] using hsourceHolder
  have hsourceNorm' : ∀ p, p ∈ Qouter →
      ‖parabolicNondivergenceOperator principal drift potential
        (fun t x ↦ u t x) p‖ ≤ Bsource := by
    intro p hp
    rw [hsourceEq hp]
    exact hsourceNorm p (by simpa only [Qouter] using hp)
  obtain ⟨localScale, s, delta, hdelta, hdeltaScale, hcover, hestimate⟩ :=
    exists_parabolic_nondivergence_schauder_estimate
      (alpha := alpha) (Ksource := Ksource) (Kc := Kc) (Ku := Ku)
      (KdtimeU := KdtimeU) (Kdu := Kdu) (Kd2u := Kd2u)
      (Bsource := Bsource) (Bc := Bc) (Mu := Mu)
      (MdtimeU := MdtimeU) (Mdu := Mdu) (Md2u := Md2u)
      halpha0 halpha1 principal drift potential hat₀ ht₁b hrR center hpos
      Ka Kb Bb (by simpa only [principal] using ha)
      (by simpa only [drift] using hb) (by simpa only [potential] using hc)
      (by simpa only [drift] using hbNorm)
      (by simpa only [potential] using hcNorm)
      u dtimeU du d2u huTime hu hdu huCont
      (by simpa only [Qouter] using hsourceHolder')
      (by simpa only [Qouter] using hsourceNorm') huHolder hdtimeUHolder
      hduHolder hd2uHolder huNorm hdtimeUNorm hduNorm hd2uNorm
  refine ⟨localScale, s, delta, hdelta, hdeltaScale, hcover, ?_⟩
  have hgauge : eParabolicC2HolderGaugeOn alpha Qinner
      (fun t x ↦ u t x) = eParabolicC2HolderGaugeOn alpha Qinner chartU :=
    eParabolicC2HolderGaugeOn_congr_of_eqOn_open
      hUrealize hQinnerU (by simpa only [Urealize, chartU] using hrealize) alpha
  unfold eParabolicC2HolderGaugeInEuclideanChartOn
  rw [← hgauge]
  simpa only [Qinner, principal, drift, potential] using hestimate

end DifferentialGeometry.Analysis.Schauder

namespace DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn

open DifferentialGeometry.Analysis.Schauder
open DifferentialGeometry.Analysis.Parabolic.Euclidean

universe v vE vH

variable {E : Type vE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
  {H : Type vH} [TopologicalSpace H]
  {I : ModelWithCorners Real E H}
  {M : Type v} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]

private abbrev EuclM (E : Type vE) [NormedAddCommGroup E]
    [NormedSpace Real E] [FiniteDimensional Real E] :=
  EuclideanSpace Real (Fin (Module.finrank Real E))

theorem eParabolicC2HolderGaugeInEuclideanChartOn_bounded_of_lower_jet_bounds
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {alpha Ksource Ku KdtimeU Kdu Kd2u Bsource
      Mu MdtimeU Mdu Md2u : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {a t₀ t₁ b r R Rext : Real}
    (hab : a < b) (habreg : Set.Icc a b ⊆ D.regular)
    (hat₀ : a < t₀) (ht₁b : t₁ < b) (hrR : r < R) (hRRext : R < Rext)
    (chartCenter : M) (center : EuclM E)
    (hchart : ((toEuclidean (E := E)).symm : EuclM E → E) ''
      Metric.closedBall center R ⊆ interior (extChartAt I chartCenter).target)
    (V : Real → M → Real)
    (hV : ContDiffOn Real 1
      (fun p : Real × E ↦ V p.1 ((extChartAt I chartCenter).symm p.2))
      (Set.Icc a b ×ˢ
        (((toEuclidean (E := E)).symm : EuclM E → E) ''
          Metric.closedBall center R)))
    (intrinsicU : Real → M → Real)
    (u dtimeU : Real → BoundedContinuousFunction (EuclM E) Real)
    (du : Real →
      BoundedContinuousFunction (EuclM E) (EuclM E →L[Real] Real))
    (d2u : Real → BoundedContinuousFunction (EuclM E)
      (EuclM E →L[Real] EuclM E →L[Real] Real))
    (huTime : ∀ s ∈ Set.Icc a b, HasDerivAt u (dtimeU s) s)
    (hu : ∀ s ∈ Set.Icc a b, ∀ x,
      HasFDerivAt (u s : EuclM E → Real) (du s x) x)
    (hdu : ∀ s ∈ Set.Icc a b, ∀ x,
      HasFDerivAt (du s : EuclM E → EuclM E →L[Real] Real)
        (d2u s x) x)
    (huCont : Continuous u)
    (hrealize : Set.EqOn (fun p ↦ u p.time p.space)
      (fun p ↦ parabolicEuclideanChartRepresentation
        I chartCenter intrinsicU p.time p.space)
      (parabolicCylinder Set.univ (Metric.ball center Rext)))
    (hsourceHolder : HolderWith Ksource alpha
      ((parabolicCylinder (Set.Icc a b) (Metric.closedBall center R)).restrict
        (parabolicNondivergenceOperatorInEuclideanChart (I := I)
          G.metric V chartCenter intrinsicU)))
    (hsourceNorm : ∀ p,
      p ∈ parabolicCylinder (Set.Icc a b) (Metric.closedBall center R) →
        ‖parabolicNondivergenceOperatorInEuclideanChart (I := I)
          G.metric V chartCenter intrinsicU p‖ ≤ Bsource)
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
    ∃ C : NNReal,
      eParabolicC2HolderGaugeInEuclideanChartOn alpha I chartCenter
        (parabolicCylinder (Set.Icc t₀ t₁) (Metric.closedBall center r))
        intrinsicU ≤ C := by
  obtain ⟨_Apr, Ka, Bb, Kb, Bc, Kc, _hAnorm, ha, hpos,
      hbNorm, hb, hcNorm, hc⟩ :=
    exists_parabolic_chart_nondivergence_operator_coefficient_schauder_bounds_on_closedBall
      hG hab habreg chartCenter center R hchart V hV halpha1.le
  have hposInner : ∀ p,
      p ∈ parabolicCylinder (Set.Icc t₀ t₁) (Metric.closedBall center r) →
        (Matrix.of fun i j : Fin (Module.finrank Real E) ↦
          parabolicChartPrincipalCoefficient (I := I)
            G.metric chartCenter i j p).PosDef := by
    intro p hp
    apply hpos p
    exact ⟨⟨hat₀.le.trans hp.1.1, hp.1.2.trans ht₁b.le⟩,
      Metric.closedBall_subset_closedBall hrR.le hp.2⟩
  obtain ⟨localScale, s, delta, _hdelta, _hdeltaScale, _hcover, hestimate⟩ :=
    exists_parabolic_nondivergence_schauder_estimate_in_euclideanChart
      (alpha := alpha) (Ksource := Ksource) (Kc := Kc) (Ku := Ku)
      (KdtimeU := KdtimeU) (Kdu := Kdu) (Kd2u := Kd2u)
      (Bsource := Bsource) (Bc := Bc) (Mu := Mu)
      (MdtimeU := MdtimeU) (Mdu := Mdu) (Md2u := Md2u)
      halpha0 halpha1 G.metric V chartCenter intrinsicU hat₀ ht₁b hrR hRRext
      center hposInner Ka Kb Bb ha hb hc hbNorm hcNorm
      u dtimeU du d2u huTime hu hdu huCont hrealize hsourceHolder hsourceNorm
      huHolder hdtimeUHolder hduHolder hd2uHolder
      huNorm hdtimeUNorm hduNorm hd2uNorm
  exact ⟨bufferedParabolicC2HolderGaugeConst alpha
    (∑ p ∈ s, parabolicC2HolderRescaleConst
      (localScale p).1⁻¹ alpha
      (parabolicNondivergenceRescaledInteriorSchauderConst
        (parabolicChartPrincipalCoefficient (I := I) G.metric chartCenter)
        p.1 (hposInner p.1 p.2) alpha (localScale p).1 Ka Kb Bb Kc Bc
        Ksource Ku Kdu Bsource Mu Mdu)) delta, hestimate⟩

theorem eParabolicC2HolderGaugeInEuclideanChartOn_bounded_of_lower_jet_bounds_of_interpolation
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {alpha Ksource Bsource C M0 : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (epsilon : NNReal) (hepsilon : 0 < epsilon)
    {a t₀ t₁ b r R Rext : Real}
    (hab : a < b) (habreg : Set.Icc a b ⊆ D.regular)
    (hat₀ : a < t₀) (ht₁b : t₁ < b) (hrR : r < R) (hRRext : R < Rext)
    (chartCenter : M) (center : EuclM E)
    (hchart : ((toEuclidean (E := E)).symm : EuclM E → E) ''
      Metric.closedBall center R ⊆ interior (extChartAt I chartCenter).target)
    (V : Real → M → Real)
    (hV : ContDiffOn Real 1
      (fun p : Real × E ↦ V p.1 ((extChartAt I chartCenter).symm p.2))
      (Set.Icc a b ×ˢ
        (((toEuclidean (E := E)).symm : EuclM E → E) ''
          Metric.closedBall center R)))
    (intrinsicU : Real → M → Real)
    (u dtimeU : Real → BoundedContinuousFunction (EuclM E) Real)
    (du : Real →
      BoundedContinuousFunction (EuclM E) (EuclM E →L[Real] Real))
    (d2u : Real → BoundedContinuousFunction (EuclM E)
      (EuclM E →L[Real] EuclM E →L[Real] Real))
    (huTime : ∀ s ∈ Set.Icc a b, HasDerivAt u (dtimeU s) s)
    (hu : ∀ s ∈ Set.Icc a b, ∀ x,
      HasFDerivAt (u s : EuclM E → Real) (du s x) x)
    (hdu : ∀ s ∈ Set.Icc a b, ∀ x,
      HasFDerivAt (du s : EuclM E → EuclM E →L[Real] Real)
        (d2u s x) x)
    (huCont : Continuous u)
    (hrealize : Set.EqOn (fun p ↦ u p.time p.space)
      (fun p ↦ parabolicEuclideanChartRepresentation
        I chartCenter intrinsicU p.time p.space)
      (parabolicCylinder Set.univ (Metric.ball center Rext)))
    (hsourceHolder : HolderWith Ksource alpha
      ((parabolicCylinder (Set.Icc a b) (Metric.closedBall center R)).restrict
        (parabolicNondivergenceOperatorInEuclideanChart (I := I)
          G.metric V chartCenter intrinsicU)))
    (hsourceNorm : ∀ p,
      p ∈ parabolicCylinder (Set.Icc a b) (Metric.closedBall center R) →
        ‖parabolicNondivergenceOperatorInEuclideanChart (I := I)
          G.metric V chartCenter intrinsicU p‖ ≤ Bsource)
    (hgauge : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Set.Icc a b) Set.univ)
      (fun t x ↦ u t x) ≤ C)
    (huNorm : ∀ p, p ∈ parabolicCylinder (Set.Icc a b) Set.univ →
      ‖u p.time p.space‖ ≤ M0) :
    ∃ Cresult : NNReal,
      eParabolicC2HolderGaugeInEuclideanChartOn alpha I chartCenter
        (parabolicCylinder (Set.Icc t₀ t₁) (Metric.closedBall center r))
        intrinsicU ≤ Cresult := by
  let J := Set.Icc a b
  have huC2 : IsParabolicC2On
      (parabolicCylinder J Set.univ) (fun t x ↦ u t x) := by
    constructor
    · intro p hp
      exact (contDiff_two_of_hasFDerivAt (u p.time) (du p.time) (d2u p.time)
        (hu p.time hp.1) (hdu p.time hp.1)).contDiffAt
    · intro p hp
      exact ((BoundedContinuousFunction.evalCLM Real p.space).hasFDerivAt
        |>.comp_hasDerivAt p.time (huTime p.time hp.1)).differentiableAt
  have huHolder := parabolicValue_holderWith_restrict_of_interpolation
    (convex_Icc a b) convex_univ epsilon hepsilon halpha1.le
    huC2 (by simpa only [J] using hgauge) (by simpa only [J] using huNorm)
  have hdtimeUHolder :=
    BoundedContinuousFunction.parabolicTimeDerivative_holderWith_restrict
      u dtimeU huTime hgauge
  have hduHolder :=
    BoundedContinuousFunction.parabolicSpatialDerivative_holderWith_restrict_of_interpolation
      (convex_Icc a b) epsilon hepsilon halpha1.le u du hu
      (by simpa only [J] using huC2) hgauge huNorm
  have hd2uHolder :=
    BoundedContinuousFunction.parabolicSpatialSecondDerivative_holderWith_restrict
      u du d2u hu hdu hgauge
  have hdtimeUNorm :=
    BoundedContinuousFunction.norm_parabolicTimeDerivative_le
      u dtimeU huTime hgauge
  have hduNorm :=
    BoundedContinuousFunction.norm_parabolicSpatialDerivative_le_of_interpolation
      epsilon hepsilon u du hu (by simpa only [J] using huC2) hgauge huNorm
  have hd2uNorm :=
    BoundedContinuousFunction.norm_parabolicSpatialSecondDerivative_le
      u du d2u hu hdu hgauge
  exact
    eParabolicC2HolderGaugeInEuclideanChartOn_bounded_of_lower_jet_bounds
      hG (alpha := alpha) (Ksource := Ksource)
      (Ku := parabolicValueInterpolationConst epsilon alpha C M0)
      (KdtimeU := C)
      (Kdu := parabolicSpatialGradientInterpolationConst epsilon alpha C M0)
      (Kd2u := C) (Bsource := Bsource) (Mu := M0)
      (MdtimeU := C) (Mdu := 2 * M0 / epsilon + C * epsilon)
      (Md2u := C) halpha0 halpha1 hab habreg hat₀ ht₁b hrR hRRext
      chartCenter center hchart V hV intrinsicU u dtimeU du d2u
      huTime hu hdu huCont hrealize hsourceHolder hsourceNorm
      (by simpa only [J] using huHolder) hdtimeUHolder hduHolder hd2uHolder
      huNorm hdtimeUNorm hduNorm hd2uNorm

theorem eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn_bounded_of_lower_jet_bounds
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {alpha Ksource Ku KdtimeU Kdu Kd2u Bsource
      Mu MdtimeU Mdu Md2u : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {a t₀ t₁ b r rBuffer R Rext : Real}
    (hab : a < b) (habreg : Set.Icc a b ⊆ D.regular)
    (hat₀ : a < t₀) (ht₁b : t₁ < b)
    (hrBuffer : r < rBuffer) (hrBufferR : rBuffer < R)
    (hRRext : R < Rext)
    (chartCenter : M) (center : EuclM E)
    (hchart : ((toEuclidean (E := E)).symm : EuclM E → E) ''
      Metric.closedBall center R ⊆ interior (extChartAt I chartCenter).target)
    (V : Real → M → Real)
    (hV : ContDiffOn Real 1
      (fun p : Real × E ↦ V p.1 ((extChartAt I chartCenter).symm p.2))
      (Set.Icc a b ×ˢ
        (((toEuclidean (E := E)).symm : EuclM E → E) ''
          Metric.closedBall center R)))
    (intrinsicU : Real → M → Real)
    (u dtimeU : Real → BoundedContinuousFunction (EuclM E) Real)
    (du : Real →
      BoundedContinuousFunction (EuclM E) (EuclM E →L[Real] Real))
    (d2u : Real → BoundedContinuousFunction (EuclM E)
      (EuclM E →L[Real] EuclM E →L[Real] Real))
    (huTime : ∀ s ∈ Set.Icc a b, HasDerivAt u (dtimeU s) s)
    (hu : ∀ s ∈ Set.Icc a b, ∀ x,
      HasFDerivAt (u s : EuclM E → Real) (du s x) x)
    (hdu : ∀ s ∈ Set.Icc a b, ∀ x,
      HasFDerivAt (du s : EuclM E → EuclM E →L[Real] Real)
        (d2u s x) x)
    (huCont : Continuous u)
    (hrealize : Set.EqOn (fun p ↦ u p.time p.space)
      (fun p ↦ parabolicEuclideanChartRepresentation
        I chartCenter intrinsicU p.time p.space)
      (parabolicCylinder Set.univ (Metric.ball center Rext)))
    (hsourceHolder : HolderWith Ksource alpha
      ((parabolicCylinder (Set.Icc a b) (Metric.closedBall center R)).restrict
        (parabolicNondivergenceOperatorInEuclideanChart (I := I)
          G.metric V chartCenter intrinsicU)))
    (hsourceNorm : ∀ p,
      p ∈ parabolicCylinder (Set.Icc a b) (Metric.closedBall center R) →
        ‖parabolicNondivergenceOperatorInEuclideanChart (I := I)
          G.metric V chartCenter intrinsicU p‖ ≤ Bsource)
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
    (hdtimeUNorm : ∀ p,
      p ∈ parabolicCylinder (Set.Icc a b) Set.univ →
        ‖dtimeU p.time p.space‖ ≤ MdtimeU)
    (hduNorm : ∀ p, p ∈ parabolicCylinder (Set.Icc a b) Set.univ →
      ‖du p.time p.space‖ ≤ Mdu)
    (hd2uNorm : ∀ p, p ∈ parabolicCylinder (Set.Icc a b) Set.univ →
      ‖d2u p.time p.space‖ ≤ Md2u) :
    ∃ C : NNReal,
      eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn alpha I chartCenter
        (parabolicCylinder (Set.Icc t₀ t₁) (Metric.closedBall center r))
        intrinsicU ≤ C := by
  obtain ⟨C, hC⟩ :=
    eParabolicC2HolderGaugeInEuclideanChartOn_bounded_of_lower_jet_bounds
      hG (halpha0 := halpha0) (halpha1 := halpha1)
      hab habreg hat₀ ht₁b hrBufferR hRRext chartCenter center hchart V hV
      intrinsicU u dtimeU du d2u huTime hu hdu huCont hrealize
      hsourceHolder hsourceNorm huHolder hdtimeUHolder hduHolder hd2uHolder
      huNorm hdtimeUNorm hduNorm hd2uNorm
  let J := Set.Icc t₀ t₁
  let Qbuffer := parabolicCylinder J (Metric.ball center rBuffer)
  let Urealize := parabolicCylinder Set.univ (Metric.ball center Rext)
  have hQbufferU : Qbuffer ⊆ Urealize := by
    intro p hp
    exact ⟨Set.mem_univ p.time,
      Metric.ball_subset_ball (hrBufferR.trans hRRext).le hp.2⟩
  have huC2 : IsParabolicC2On Qbuffer (fun t x ↦ u t x) := by
    constructor
    · intro p hp
      exact (contDiff_two_of_hasFDerivAt (u p.time) (du p.time) (d2u p.time)
        (hu p.time ⟨hat₀.le.trans hp.1.1, hp.1.2.trans ht₁b.le⟩)
        (hdu p.time ⟨hat₀.le.trans hp.1.1, hp.1.2.trans ht₁b.le⟩)).contDiffAt
    · intro p hp
      exact ((BoundedContinuousFunction.evalCLM Real p.space).hasFDerivAt
        |>.comp_hasDerivAt p.time
          (huTime p.time
            ⟨hat₀.le.trans hp.1.1, hp.1.2.trans ht₁b.le⟩)).differentiableAt
  have hchartC2 : IsParabolicC2On Qbuffer
      (parabolicEuclideanChartRepresentation I chartCenter intrinsicU) := by
    exact isParabolicC2On_congr_of_eqOn_open
      (isOpen_parabolicCylinder isOpen_univ Metric.isOpen_ball)
      hQbufferU hrealize huC2
  have hCball : eParabolicC2HolderGaugeInEuclideanChartOn alpha I chartCenter
      Qbuffer intrinsicU ≤ C := by
    exact (eParabolicC2HolderGaugeInEuclideanChartOn_mono
      (Q := Qbuffer)
      (R := parabolicCylinder J (Metric.closedBall center rBuffer))
      (fun p hp ↦ ⟨hp.1, Metric.ball_subset_closedBall hp.2⟩)
      alpha I chartCenter intrinsicU).trans (by simpa only [J] using hC)
  let Cresult := bufferedParabolicC2HolderGaugeWithLowerJetsFactor
    (Real.toNNReal (rBuffer - r)) * C
  refine ⟨Cresult, ?_⟩
  have hinterpolation :=
    eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn_le_mul_of_nested_balls
      (convex_Icc t₀ t₁) chartCenter center hrBuffer halpha1.le hchartC2
  exact hinterpolation.trans (by
    exact mul_le_mul_right hCball _)

theorem eParabolicC2HolderGaugeInEuclideanChartsOn_bounded_of_lower_jet_bounds_of_finite
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {Achart : Type*} [Finite Achart]
    {alpha : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {a t₀ t₁ b : Real}
    (hab : a < b) (habreg : Set.Icc a b ⊆ D.regular)
    (hat₀ : a < t₀) (ht₁b : t₁ < b)
    (chartCenter : Achart → M) (center : Achart → EuclM E)
    (r R Rext : Achart → Real)
    (hrR : ∀ i, r i < R i) (hRRext : ∀ i, R i < Rext i)
    (hchart : ∀ i,
      ((toEuclidean (E := E)).symm : EuclM E → E) ''
          Metric.closedBall (center i) (R i) ⊆
        interior (extChartAt I (chartCenter i)).target)
    (V : Real → M → Real)
    (hV : ∀ i, ContDiffOn Real 1
      (fun p : Real × E ↦ V p.1 ((extChartAt I (chartCenter i)).symm p.2))
      (Set.Icc a b ×ˢ
        (((toEuclidean (E := E)).symm : EuclM E → E) ''
          Metric.closedBall (center i) (R i))))
    (intrinsicU : Real → M → Real)
    (u dtimeU : Achart → Real → BoundedContinuousFunction (EuclM E) Real)
    (du : Achart → Real →
      BoundedContinuousFunction (EuclM E) (EuclM E →L[Real] Real))
    (d2u : Achart → Real → BoundedContinuousFunction (EuclM E)
      (EuclM E →L[Real] EuclM E →L[Real] Real))
    (huTime : ∀ i s, s ∈ Set.Icc a b → HasDerivAt (u i) (dtimeU i s) s)
    (hu : ∀ i s, s ∈ Set.Icc a b → ∀ x,
      HasFDerivAt (u i s : EuclM E → Real) (du i s x) x)
    (hdu : ∀ i s, s ∈ Set.Icc a b → ∀ x,
      HasFDerivAt (du i s : EuclM E → EuclM E →L[Real] Real)
        (d2u i s x) x)
    (huCont : ∀ i, Continuous (u i))
    (hrealize : ∀ i, Set.EqOn (fun p ↦ u i p.time p.space)
      (fun p ↦ parabolicEuclideanChartRepresentation
        I (chartCenter i) intrinsicU p.time p.space)
      (parabolicCylinder Set.univ (Metric.ball (center i) (Rext i))))
    (Ksource Ku KdtimeU Kdu Kd2u Bsource
      Mu MdtimeU Mdu Md2u : Achart → NNReal)
    (hsourceHolder : ∀ i, HolderWith (Ksource i) alpha
      ((parabolicCylinder (Set.Icc a b)
          (Metric.closedBall (center i) (R i))).restrict
        (parabolicNondivergenceOperatorInEuclideanChart (I := I)
          G.metric V (chartCenter i) intrinsicU)))
    (hsourceNorm : ∀ i p,
      p ∈ parabolicCylinder (Set.Icc a b)
          (Metric.closedBall (center i) (R i)) →
        ‖parabolicNondivergenceOperatorInEuclideanChart (I := I)
          G.metric V (chartCenter i) intrinsicU p‖ ≤ Bsource i)
    (huHolder : ∀ i, HolderWith (Ku i) alpha
      ((parabolicCylinder (Set.Icc a b) Set.univ).restrict
        (fun p ↦ u i p.time p.space)))
    (hdtimeUHolder : ∀ i, HolderWith (KdtimeU i) alpha
      ((parabolicCylinder (Set.Icc a b) Set.univ).restrict
        (fun p ↦ dtimeU i p.time p.space)))
    (hduHolder : ∀ i, HolderWith (Kdu i) alpha
      ((parabolicCylinder (Set.Icc a b) Set.univ).restrict
        (fun p ↦ du i p.time p.space)))
    (hd2uHolder : ∀ i, HolderWith (Kd2u i) alpha
      ((parabolicCylinder (Set.Icc a b) Set.univ).restrict
        (fun p ↦ d2u i p.time p.space)))
    (huNorm : ∀ i p, p ∈ parabolicCylinder (Set.Icc a b) Set.univ →
      ‖u i p.time p.space‖ ≤ Mu i)
    (hdtimeUNorm : ∀ i p,
      p ∈ parabolicCylinder (Set.Icc a b) Set.univ →
        ‖dtimeU i p.time p.space‖ ≤ MdtimeU i)
    (hduNorm : ∀ i p, p ∈ parabolicCylinder (Set.Icc a b) Set.univ →
      ‖du i p.time p.space‖ ≤ Mdu i)
    (hd2uNorm : ∀ i p, p ∈ parabolicCylinder (Set.Icc a b) Set.univ →
      ‖d2u i p.time p.space‖ ≤ Md2u i) :
    ∃ C : NNReal,
      eParabolicC2HolderGaugeInEuclideanChartsOn alpha I chartCenter
        (fun i ↦ parabolicCylinder (Set.Icc t₀ t₁)
          (Metric.closedBall (center i) (r i))) intrinsicU ≤ C := by
  classical
  letI := Fintype.ofFinite Achart
  have hlocal : ∀ i : Achart, ∃ C : NNReal,
      eParabolicC2HolderGaugeInEuclideanChartOn alpha I (chartCenter i)
        (parabolicCylinder (Set.Icc t₀ t₁)
          (Metric.closedBall (center i) (r i))) intrinsicU ≤ C := by
    intro i
    exact eParabolicC2HolderGaugeInEuclideanChartOn_bounded_of_lower_jet_bounds
      hG (halpha0 := halpha0) (halpha1 := halpha1)
      hab habreg hat₀ ht₁b (hrR i) (hRRext i) (chartCenter i) (center i)
      (hchart i) V (hV i) intrinsicU (u i) (dtimeU i) (du i) (d2u i)
      (huTime i) (hu i) (hdu i) (huCont i) (hrealize i)
      (hsourceHolder i) (hsourceNorm i) (huHolder i) (hdtimeUHolder i)
      (hduHolder i) (hd2uHolder i) (huNorm i) (hdtimeUNorm i)
      (hduNorm i) (hd2uNorm i)
  choose C hC using hlocal
  refine ⟨∑ i, C i, ?_⟩
  exact eParabolicC2HolderGaugeInEuclideanChartsOn_le_sum_of_finite
    alpha I chartCenter
      (fun i ↦ parabolicCylinder (Set.Icc t₀ t₁)
        (Metric.closedBall (center i) (r i))) intrinsicU C hC

theorem eParabolicC2HolderGaugeInEuclideanChartsOn_bounded_of_lower_jet_bounds_of_interpolation_of_finite
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {Achart : Type*} [Finite Achart]
    {alpha : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {a t₀ t₁ b : Real}
    (hab : a < b) (habreg : Set.Icc a b ⊆ D.regular)
    (hat₀ : a < t₀) (ht₁b : t₁ < b)
    (epsilon : Achart → NNReal) (hepsilon : ∀ i, 0 < epsilon i)
    (chartCenter : Achart → M) (center : Achart → EuclM E)
    (r R Rext : Achart → Real)
    (hrR : ∀ i, r i < R i) (hRRext : ∀ i, R i < Rext i)
    (hchart : ∀ i,
      ((toEuclidean (E := E)).symm : EuclM E → E) ''
          Metric.closedBall (center i) (R i) ⊆
        interior (extChartAt I (chartCenter i)).target)
    (V : Real → M → Real)
    (hV : ∀ i, ContDiffOn Real 1
      (fun p : Real × E ↦ V p.1 ((extChartAt I (chartCenter i)).symm p.2))
      (Set.Icc a b ×ˢ
        (((toEuclidean (E := E)).symm : EuclM E → E) ''
          Metric.closedBall (center i) (R i))))
    (intrinsicU : Real → M → Real)
    (u dtimeU : Achart → Real → BoundedContinuousFunction (EuclM E) Real)
    (du : Achart → Real →
      BoundedContinuousFunction (EuclM E) (EuclM E →L[Real] Real))
    (d2u : Achart → Real → BoundedContinuousFunction (EuclM E)
      (EuclM E →L[Real] EuclM E →L[Real] Real))
    (huTime : ∀ i s, s ∈ Set.Icc a b → HasDerivAt (u i) (dtimeU i s) s)
    (hu : ∀ i s, s ∈ Set.Icc a b → ∀ x,
      HasFDerivAt (u i s : EuclM E → Real) (du i s x) x)
    (hdu : ∀ i s, s ∈ Set.Icc a b → ∀ x,
      HasFDerivAt (du i s : EuclM E → EuclM E →L[Real] Real)
        (d2u i s x) x)
    (huCont : ∀ i, Continuous (u i))
    (hrealize : ∀ i, Set.EqOn (fun p ↦ u i p.time p.space)
      (fun p ↦ parabolicEuclideanChartRepresentation
        I (chartCenter i) intrinsicU p.time p.space)
      (parabolicCylinder Set.univ (Metric.ball (center i) (Rext i))))
    (Ksource Bsource C M0 : Achart → NNReal)
    (hsourceHolder : ∀ i, HolderWith (Ksource i) alpha
      ((parabolicCylinder (Set.Icc a b)
          (Metric.closedBall (center i) (R i))).restrict
        (parabolicNondivergenceOperatorInEuclideanChart (I := I)
          G.metric V (chartCenter i) intrinsicU)))
    (hsourceNorm : ∀ i p,
      p ∈ parabolicCylinder (Set.Icc a b)
          (Metric.closedBall (center i) (R i)) →
        ‖parabolicNondivergenceOperatorInEuclideanChart (I := I)
          G.metric V (chartCenter i) intrinsicU p‖ ≤ Bsource i)
    (hgauge : ∀ i, eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Set.Icc a b) Set.univ)
      (fun t x ↦ u i t x) ≤ C i)
    (huNorm : ∀ i p, p ∈ parabolicCylinder (Set.Icc a b) Set.univ →
      ‖u i p.time p.space‖ ≤ M0 i) :
    ∃ Cresult : NNReal,
      eParabolicC2HolderGaugeInEuclideanChartsOn alpha I chartCenter
        (fun i ↦ parabolicCylinder (Set.Icc t₀ t₁)
          (Metric.closedBall (center i) (r i))) intrinsicU ≤ Cresult := by
  classical
  letI := Fintype.ofFinite Achart
  have hlocal : ∀ i : Achart, ∃ Cresult : NNReal,
      eParabolicC2HolderGaugeInEuclideanChartOn alpha I (chartCenter i)
        (parabolicCylinder (Set.Icc t₀ t₁)
          (Metric.closedBall (center i) (r i))) intrinsicU ≤ Cresult := by
    intro i
    exact
      eParabolicC2HolderGaugeInEuclideanChartOn_bounded_of_lower_jet_bounds_of_interpolation
        hG (halpha0 := halpha0) (halpha1 := halpha1)
        (epsilon i) (hepsilon i) hab habreg hat₀ ht₁b (hrR i) (hRRext i)
        (chartCenter i) (center i) (hchart i) V (hV i) intrinsicU
        (u i) (dtimeU i) (du i) (d2u i) (huTime i) (hu i) (hdu i)
        (huCont i) (hrealize i) (hsourceHolder i) (hsourceNorm i)
        (hgauge i) (huNorm i)
  choose Cresult hCresult using hlocal
  refine ⟨∑ i, Cresult i, ?_⟩
  exact eParabolicC2HolderGaugeInEuclideanChartsOn_le_sum_of_finite
    alpha I chartCenter
      (fun i ↦ parabolicCylinder (Set.Icc t₀ t₁)
        (Metric.closedBall (center i) (r i))) intrinsicU Cresult hCresult

theorem eParabolicC2HolderGaugeInEuclideanChartsOn_bounded_of_lower_jet_bounds_of_uniform_interpolation_of_finite
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {Achart : Type*} [Finite Achart]
    {alpha : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {a t₀ t₁ b : Real}
    (hab : a < b) (habreg : Set.Icc a b ⊆ D.regular)
    (hat₀ : a < t₀) (ht₁b : t₁ < b)
    (epsilon : NNReal) (hepsilon : 0 < epsilon)
    (chartCenter : Achart → M) (center : Achart → EuclM E)
    (r R Rext : Achart → Real)
    (hrR : ∀ i, r i < R i) (hRRext : ∀ i, R i < Rext i)
    (hchart : ∀ i,
      ((toEuclidean (E := E)).symm : EuclM E → E) ''
          Metric.closedBall (center i) (R i) ⊆
        interior (extChartAt I (chartCenter i)).target)
    (V : Real → M → Real)
    (hV : ∀ i, ContDiffOn Real 1
      (fun p : Real × E ↦ V p.1 ((extChartAt I (chartCenter i)).symm p.2))
      (Set.Icc a b ×ˢ
        (((toEuclidean (E := E)).symm : EuclM E → E) ''
          Metric.closedBall (center i) (R i))))
    (intrinsicU : Real → M → Real)
    (u dtimeU : Achart → Real → BoundedContinuousFunction (EuclM E) Real)
    (du : Achart → Real →
      BoundedContinuousFunction (EuclM E) (EuclM E →L[Real] Real))
    (d2u : Achart → Real → BoundedContinuousFunction (EuclM E)
      (EuclM E →L[Real] EuclM E →L[Real] Real))
    (huTime : ∀ i s, s ∈ Set.Icc a b → HasDerivAt (u i) (dtimeU i s) s)
    (hu : ∀ i s, s ∈ Set.Icc a b → ∀ x,
      HasFDerivAt (u i s : EuclM E → Real) (du i s x) x)
    (hdu : ∀ i s, s ∈ Set.Icc a b → ∀ x,
      HasFDerivAt (du i s : EuclM E → EuclM E →L[Real] Real)
        (d2u i s x) x)
    (huCont : ∀ i, Continuous (u i))
    (hrealize : ∀ i, Set.EqOn (fun p ↦ u i p.time p.space)
      (fun p ↦ parabolicEuclideanChartRepresentation
        I (chartCenter i) intrinsicU p.time p.space)
      (parabolicCylinder Set.univ (Metric.ball (center i) (Rext i))))
    {Ksource Bsource C M0 : NNReal}
    (hsourceHolder : ∀ i, HolderWith Ksource alpha
      ((parabolicCylinder (Set.Icc a b)
          (Metric.closedBall (center i) (R i))).restrict
        (parabolicNondivergenceOperatorInEuclideanChart (I := I)
          G.metric V (chartCenter i) intrinsicU)))
    (hsourceNorm : ∀ i p,
      p ∈ parabolicCylinder (Set.Icc a b)
          (Metric.closedBall (center i) (R i)) →
        ‖parabolicNondivergenceOperatorInEuclideanChart (I := I)
          G.metric V (chartCenter i) intrinsicU p‖ ≤ Bsource)
    (hgauge : ∀ i, eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Set.Icc a b) Set.univ)
      (fun t x ↦ u i t x) ≤ C)
    (huNorm : ∀ i p, p ∈ parabolicCylinder (Set.Icc a b) Set.univ →
      ‖u i p.time p.space‖ ≤ M0) :
    ∃ Cresult : NNReal,
      eParabolicC2HolderGaugeInEuclideanChartsOn alpha I chartCenter
        (fun i ↦ parabolicCylinder (Set.Icc t₀ t₁)
          (Metric.closedBall (center i) (r i))) intrinsicU ≤ Cresult := by
  exact
    eParabolicC2HolderGaugeInEuclideanChartsOn_bounded_of_lower_jet_bounds_of_interpolation_of_finite
      hG halpha0 halpha1 hab habreg hat₀ ht₁b (fun _ ↦ epsilon)
      (fun _ ↦ hepsilon) chartCenter center r R Rext hrR hRRext hchart V hV
      intrinsicU u dtimeU du d2u huTime hu hdu huCont hrealize
      (fun _ ↦ Ksource) (fun _ ↦ Bsource) (fun _ ↦ C) (fun _ ↦ M0)
      hsourceHolder hsourceNorm hgauge huNorm

theorem eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartsOn_bounded_of_lower_jet_bounds_of_finite
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {Achart : Type*} [Finite Achart]
    {alpha : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {a t₀ t₁ b : Real}
    (hab : a < b) (habreg : Set.Icc a b ⊆ D.regular)
    (hat₀ : a < t₀) (ht₁b : t₁ < b)
    (chartCenter : Achart → M) (center : Achart → EuclM E)
    (r rBuffer R Rext : Achart → Real)
    (hrBuffer : ∀ i, r i < rBuffer i)
    (hrBufferR : ∀ i, rBuffer i < R i)
    (hRRext : ∀ i, R i < Rext i)
    (hchart : ∀ i,
      ((toEuclidean (E := E)).symm : EuclM E → E) ''
          Metric.closedBall (center i) (R i) ⊆
        interior (extChartAt I (chartCenter i)).target)
    (V : Real → M → Real)
    (hV : ∀ i, ContDiffOn Real 1
      (fun p : Real × E ↦ V p.1 ((extChartAt I (chartCenter i)).symm p.2))
      (Set.Icc a b ×ˢ
        (((toEuclidean (E := E)).symm : EuclM E → E) ''
          Metric.closedBall (center i) (R i))))
    (intrinsicU : Real → M → Real)
    (u dtimeU : Achart → Real → BoundedContinuousFunction (EuclM E) Real)
    (du : Achart → Real →
      BoundedContinuousFunction (EuclM E) (EuclM E →L[Real] Real))
    (d2u : Achart → Real → BoundedContinuousFunction (EuclM E)
      (EuclM E →L[Real] EuclM E →L[Real] Real))
    (huTime : ∀ i s, s ∈ Set.Icc a b → HasDerivAt (u i) (dtimeU i s) s)
    (hu : ∀ i s, s ∈ Set.Icc a b → ∀ x,
      HasFDerivAt (u i s : EuclM E → Real) (du i s x) x)
    (hdu : ∀ i s, s ∈ Set.Icc a b → ∀ x,
      HasFDerivAt (du i s : EuclM E → EuclM E →L[Real] Real)
        (d2u i s x) x)
    (huCont : ∀ i, Continuous (u i))
    (hrealize : ∀ i, Set.EqOn (fun p ↦ u i p.time p.space)
      (fun p ↦ parabolicEuclideanChartRepresentation
        I (chartCenter i) intrinsicU p.time p.space)
      (parabolicCylinder Set.univ (Metric.ball (center i) (Rext i))))
    (Ksource Ku KdtimeU Kdu Kd2u Bsource
      Mu MdtimeU Mdu Md2u : Achart → NNReal)
    (hsourceHolder : ∀ i, HolderWith (Ksource i) alpha
      ((parabolicCylinder (Set.Icc a b)
          (Metric.closedBall (center i) (R i))).restrict
        (parabolicNondivergenceOperatorInEuclideanChart (I := I)
          G.metric V (chartCenter i) intrinsicU)))
    (hsourceNorm : ∀ i p,
      p ∈ parabolicCylinder (Set.Icc a b)
          (Metric.closedBall (center i) (R i)) →
        ‖parabolicNondivergenceOperatorInEuclideanChart (I := I)
          G.metric V (chartCenter i) intrinsicU p‖ ≤ Bsource i)
    (huHolder : ∀ i, HolderWith (Ku i) alpha
      ((parabolicCylinder (Set.Icc a b) Set.univ).restrict
        (fun p ↦ u i p.time p.space)))
    (hdtimeUHolder : ∀ i, HolderWith (KdtimeU i) alpha
      ((parabolicCylinder (Set.Icc a b) Set.univ).restrict
        (fun p ↦ dtimeU i p.time p.space)))
    (hduHolder : ∀ i, HolderWith (Kdu i) alpha
      ((parabolicCylinder (Set.Icc a b) Set.univ).restrict
        (fun p ↦ du i p.time p.space)))
    (hd2uHolder : ∀ i, HolderWith (Kd2u i) alpha
      ((parabolicCylinder (Set.Icc a b) Set.univ).restrict
        (fun p ↦ d2u i p.time p.space)))
    (huNorm : ∀ i p, p ∈ parabolicCylinder (Set.Icc a b) Set.univ →
      ‖u i p.time p.space‖ ≤ Mu i)
    (hdtimeUNorm : ∀ i p,
      p ∈ parabolicCylinder (Set.Icc a b) Set.univ →
        ‖dtimeU i p.time p.space‖ ≤ MdtimeU i)
    (hduNorm : ∀ i p, p ∈ parabolicCylinder (Set.Icc a b) Set.univ →
      ‖du i p.time p.space‖ ≤ Mdu i)
    (hd2uNorm : ∀ i p, p ∈ parabolicCylinder (Set.Icc a b) Set.univ →
      ‖d2u i p.time p.space‖ ≤ Md2u i) :
    ∃ C : NNReal,
      eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartsOn
        alpha I chartCenter
        (fun i ↦ parabolicCylinder (Set.Icc t₀ t₁)
          (Metric.closedBall (center i) (r i))) intrinsicU ≤ C := by
  classical
  letI := Fintype.ofFinite Achart
  have hlocal : ∀ i : Achart, ∃ C : NNReal,
      eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn
        alpha I (chartCenter i)
        (parabolicCylinder (Set.Icc t₀ t₁)
          (Metric.closedBall (center i) (r i))) intrinsicU ≤ C := by
    intro i
    exact
      eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartOn_bounded_of_lower_jet_bounds
        hG (halpha0 := halpha0) (halpha1 := halpha1)
        hab habreg hat₀ ht₁b (hrBuffer i) (hrBufferR i) (hRRext i)
        (chartCenter i) (center i) (hchart i) V (hV i) intrinsicU
        (u i) (dtimeU i) (du i) (d2u i)
        (huTime i) (hu i) (hdu i) (huCont i) (hrealize i)
        (hsourceHolder i) (hsourceNorm i) (huHolder i) (hdtimeUHolder i)
        (hduHolder i) (hd2uHolder i) (huNorm i) (hdtimeUNorm i)
        (hduNorm i) (hd2uNorm i)
  choose C hC using hlocal
  refine ⟨∑ i, C i, ?_⟩
  exact eParabolicC2HolderGaugeWithLowerJetsInEuclideanChartsOn_le_sum_of_finite
    alpha I chartCenter
      (fun i ↦ parabolicCylinder (Set.Icc t₀ t₁)
        (Metric.closedBall (center i) (r i))) intrinsicU C hC

end DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn

end
