import DifferentialGeometry.Analysis.Parabolic.Euclidean.BallInteriorSchauder
import DifferentialGeometry.Analysis.Parabolic.Euclidean.CutoffLocalSource
import DifferentialGeometry.Analysis.Parabolic.Euclidean.LowerOrder

noncomputable section

open Filter Matrix Real Set
open scoped NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

open DifferentialGeometry.Analysis.Schauder

private abbrev Euc (n : Type*) := EuclideanSpace Real n

variable {n F : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]

theorem parabolic_variable_coefficient_ball_interior_schauder_estimate_of_local_cutoff_source_estimates
    {alpha Ksource Kcomm Bsource Bcomm X : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {aTime t₀ t₁ bTime S T : Real}
    (haTime : 0 ≤ aTime) (hat₀ : aTime < t₀) (ht₀t₁ : t₀ ≤ t₁)
    (ht₁b : t₁ < bTime) (ht₁T : t₁ ≤ T)
    (hT : 0 ≤ T) (hTS : T < S)
    (center : Euc n) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (u dtimeU : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (huTime : ∀ s ∈ Icc (0 : Real) S, HasDerivAt u (dtimeU s) s)
    (hu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (u s : Euc n → F) (du s x) x)
    (hdu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (du s : Euc n → Euc n →L[Real] F) (d2u s x) x)
    (huCont : Continuous u)
    (hsourceHolder : HolderWith Ksource alpha
      ((parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R)).restrict
        (parabolicVariableMatrixOperator a (fun t x ↦ u t x))))
    (hcommHolder : HolderWith Kcomm alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (parabolicCutoffOperatorCommutator a
          (fun p ↦ parabolicBallCutoffTimeDerivative
            aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
              p.time p.space)
          (fun p ↦ parabolicBallCutoffSpatialFDeriv
            aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
              p.time p.space)
          (fun p ↦ parabolicBallCutoffSpatialFDeriv2
            aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
              p.time p.space)
          (fun t x ↦ u t x) (fun p ↦ du p.time p.space))))
    (hsourceNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R) →
        ‖parabolicVariableMatrixOperator a (fun t x ↦ u t x) p‖ ≤ Bsource)
    (hcommNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖parabolicCutoffOperatorCommutator a
          (fun q ↦ parabolicBallCutoffTimeDerivative
            aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
              q.time q.space)
          (fun q ↦ parabolicBallCutoffSpatialFDeriv
            aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
              q.time q.space)
          (fun q ↦ parabolicBallCutoffSpatialFDeriv2
            aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
              q.time q.space)
          (fun t x ↦ u t x) (fun q ↦ du q.time q.space) p‖ ≤ Bcomm)
    (Ka omega : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict (a i j)))
    (homega : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p0 - a i j p‖ ≤ omega i j)
    (hcutoffGauge : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Icc (0 : Real) S) Set.univ)
      (fun t x ↦ parabolicBallCutoff
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR t x •
          u t x) ≤ X) :
    eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Ioo t₀ t₁) (Metric.ball center r))
        (fun t x ↦ u t x) ≤
      parabolicBallInteriorSchauderConst a p0 hA alpha
        aTime t₀ t₁ bTime r R Ksource Kcomm Bsource Bcomm X
        Ka omega T := by
  let chi := parabolicBallCutoff
    aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
  let dtimeChi := parabolicBallCutoffTimeDerivative
    aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
  let dchi := parabolicBallCutoffSpatialFDeriv
    aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
  let d2chi := parabolicBallCutoffSpatialFDeriv2
    aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
  let Q := parabolicCylinder (Icc (0 : Real) S) (Set.univ : Set (Euc n))
  let Qsource := parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R)
  let U := parabolicCylinder (Ioo t₀ t₁) (Metric.ball center r)
  let W : Real → Euc n → F := fun t x ↦ chi t x • u t x
  have hchiTime : ∀ s ∈ Icc (0 : Real) S,
      HasDerivAt chi (dtimeChi s) s := by
    intro s _hs
    exact parabolicBallCutoff_hasDerivAt
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR s
  have hchi : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (chi s : Euc n → Real) (dchi s x) x := by
    intro s _hs x
    exact parabolicBallCutoff_hasFDerivAt
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR s x
  have hdchi : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (dchi s : Euc n → Euc n →L[Real] Real)
        (d2chi s x) x := by
    intro s _hs x
    exact parabolicBallCutoffSpatialFDeriv_hasFDerivAt
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR s x
  have hchiCont : Continuous chi := by
    rw [continuous_iff_continuousAt]
    intro s
    exact (parabolicBallCutoff_hasDerivAt
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR s).continuousAt
  have hchi0 : chi 0 = 0 := by
    exact parabolicBallCutoff_eq_zero_of_time_not_mem
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        (fun hmem ↦ (not_lt_of_ge haTime) hmem.1)
  have hchiHolder : HolderWith
      (parabolicBallCutoffHolderConst aTime t₀ t₁ bTime r R) alpha
      (Q.restrict (fun p ↦ chi p.time p.space)) := by
    exact parabolicBallCutoff_holderWith_restrict
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        halpha1.le (Icc (0 : Real) S)
  have hchiNorm : ∀ p, p ∈ Q → ‖chi p.time p.space‖ ≤ (1 : NNReal) := by
    intro p _hp
    exact norm_parabolicBallCutoff_le_one
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        p.time p.space
  have hQsource : Q ∩ Qsource = Qsource := by
    apply Set.inter_eq_right.mpr
    intro p hp
    exact ⟨hp.1, Set.mem_univ p.space⟩
  have hchiZero : ∀ p, p ∈ Q → p ∉ Qsource →
      chi p.time p.space = 0 := by
    intro p hpQ hpSource
    have hspace : p.space ∉ Metric.ball center R := by
      intro hpball
      exact hpSource ⟨hpQ.1, hpball⟩
    change intervalCutoffBcf aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b p.time •
      ballCutoff center r R p.space = 0
    rw [ballCutoff_eq_zero_of_not_mem_ball hr hrR hspace, smul_zero]
  have hsourceHolder' : HolderWith Ksource alpha
      ((Q ∩ Qsource).restrict
        (parabolicVariableMatrixOperator a (fun t x ↦ u t x))) := by
    rw [hQsource]
    exact hsourceHolder
  have hraw : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Ioc (0 : Real) T) Set.univ) W ≤
        parabolicBallInteriorSchauderConst a p0 hA alpha
          aTime t₀ t₁ bTime r R Ksource Kcomm Bsource Bcomm X
          Ka omega T := by
    simpa only [Q, chi, dtimeChi, dchi, d2chi, W,
      parabolicBallInteriorSchauderConst] using
      (parabolic_variable_coefficient_schauder_estimate_of_local_cutoff_source_estimates
        (U := Qsource)
        halpha0 halpha1 hT hTS a p0 hA chi dtimeChi dchi d2chi
        u dtimeU du d2u hchiTime huTime hchi hdchi hu hdu hchiCont huCont
        hchi0 hchiHolder hsourceHolder'
        hcommHolder (fun p hp _ ↦ hchiNorm p hp)
        (fun p _ hp ↦ hsourceNorm p hp) hchiZero hcommNorm
        Ka omega ha homega hcutoffGauge)
  have hUOpen : IsOpen U :=
    isOpen_parabolicCylinder isOpen_Ioo Metric.isOpen_ball
  have hUOut : U ⊆ parabolicCylinder (Ioc (0 : Real) T) Set.univ := by
    intro p hp
    exact ⟨⟨lt_of_le_of_lt haTime (hat₀.trans hp.1.1),
      hp.1.2.le.trans ht₁T⟩, Set.mem_univ p.space⟩
  have heq : Set.EqOn (fun p ↦ u p.time p.space)
      (fun p ↦ W p.time p.space) U := by
    intro p hp
    change u p.time p.space = chi p.time p.space • u p.time p.space
    rw [show chi p.time p.space = 1 from
      parabolicBallCutoff_eq_one
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        ⟨hp.1.1.le, hp.1.2.le⟩ (Metric.ball_subset_closedBall hp.2), one_smul]
  calc
    eParabolicC2HolderGaugeOn alpha U (fun t x ↦ u t x) =
        eParabolicC2HolderGaugeOn alpha U W :=
      eParabolicC2HolderGaugeOn_congr_of_eqOn_open
        hUOpen Set.Subset.rfl heq alpha
    _ ≤ eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Ioc (0 : Real) T) Set.univ) W :=
      eParabolicC2HolderGaugeOn_mono hUOut alpha W
    _ ≤ parabolicBallInteriorSchauderConst a p0 hA alpha
        aTime t₀ t₁ bTime r R Ksource Kcomm Bsource Bcomm X
        Ka omega T := hraw

theorem parabolic_variable_coefficient_ball_interior_schauder_estimate_of_local_cutoff_source_estimates_of_small_freeze_defect
    {alpha Ksource Kcomm Bsource Bcomm : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {aTime t₀ t₁ bTime S T : Real}
    (haTime : 0 < aTime) (hat₀ : aTime < t₀) (ht₀t₁ : t₀ ≤ t₁)
    (ht₁b : t₁ < bTime) (hbT : bTime < T) (hTS : T < S)
    (center : Euc n) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (u dtimeU : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (huTime : ∀ s ∈ Icc (0 : Real) S, HasDerivAt u (dtimeU s) s)
    (hu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (u s : Euc n → F) (du s x) x)
    (hdu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (du s : Euc n → Euc n →L[Real] F) (d2u s x) x)
    (huCont : Continuous u)
    (hsourceHolder : HolderWith Ksource alpha
      ((parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R)).restrict
        (parabolicVariableMatrixOperator a (fun t x ↦ u t x))))
    (hcommHolder : HolderWith Kcomm alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (parabolicCutoffOperatorCommutator a
          (fun p ↦ parabolicBallCutoffTimeDerivative
            aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
              p.time p.space)
          (fun p ↦ parabolicBallCutoffSpatialFDeriv
            aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
              p.time p.space)
          (fun p ↦ parabolicBallCutoffSpatialFDeriv2
            aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
              p.time p.space)
          (fun t x ↦ u t x) (fun p ↦ du p.time p.space))))
    (hsourceNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R) →
        ‖parabolicVariableMatrixOperator a (fun t x ↦ u t x) p‖ ≤ Bsource)
    (hcommNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖parabolicCutoffOperatorCommutator a
          (fun q ↦ parabolicBallCutoffTimeDerivative
            aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
              q.time q.space)
          (fun q ↦ parabolicBallCutoffSpatialFDeriv
            aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
              q.time q.space)
          (fun q ↦ parabolicBallCutoffSpatialFDeriv2
            aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
              q.time q.space)
          (fun t x ↦ u t x) (fun q ↦ du q.time q.space) p‖ ≤ Bcomm)
    (Ka omega : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict (a i j)))
    (homega : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p0 - a i j p‖ ≤ omega i j)
    (hcutoffFinite : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Icc (0 : Real) S) Set.univ)
      (fun t x ↦ parabolicBallCutoff
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR t x •
          u t x) ≠ ⊤)
    (hsmall : spdParabolicSchauderDefectConst
      (fun i j ↦ a i j p0) hA alpha Ka omega T < 1) :
    eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Ioo t₀ t₁) (Metric.ball center r))
        (fun t x ↦ u t x) ≤
      parabolicBallInteriorAbsorbedSchauderConst a p0 hA alpha
        aTime t₀ t₁ bTime r R Ksource Kcomm Bsource Bcomm
        Ka omega T := by
  let chi := parabolicBallCutoff
    aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
  let dtimeChi := parabolicBallCutoffTimeDerivative
    aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
  let dchi := parabolicBallCutoffSpatialFDeriv
    aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
  let d2chi := parabolicBallCutoffSpatialFDeriv2
    aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
  let Q := parabolicCylinder (Icc (0 : Real) S) (Set.univ : Set (Euc n))
  let Qsource := parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R)
  let QT := parabolicCylinder (Ioc (0 : Real) T) (Set.univ : Set (Euc n))
  let U := parabolicCylinder (Ioo t₀ t₁) (Metric.ball center r)
  let W : Real → Euc n → F := fun t x ↦ chi t x • u t x
  have haTlt : aTime < T :=
    (hat₀.trans_le ht₀t₁).trans (ht₁b.trans hbT)
  have hT : 0 ≤ T := (haTime.trans haTlt).le
  have haT : aTime ≤ T := haTlt.le
  have hchiTime : ∀ s ∈ Icc (0 : Real) S,
      HasDerivAt chi (dtimeChi s) s := by
    intro s _hs
    exact parabolicBallCutoff_hasDerivAt
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR s
  have hchi : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (chi s : Euc n → Real) (dchi s x) x := by
    intro s _hs x
    exact parabolicBallCutoff_hasFDerivAt
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR s x
  have hdchi : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (dchi s : Euc n → Euc n →L[Real] Real)
        (d2chi s x) x := by
    intro s _hs x
    exact parabolicBallCutoffSpatialFDeriv_hasFDerivAt
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR s x
  have hchiCont : Continuous chi := by
    rw [continuous_iff_continuousAt]
    intro s
    exact (parabolicBallCutoff_hasDerivAt
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR s).continuousAt
  have hchi0 : chi 0 = 0 := by
    exact parabolicBallCutoff_eq_zero_of_time_not_mem
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        (fun hmem ↦ (not_lt_of_ge haTime.le) hmem.1)
  have hchiHolder : HolderWith
      (parabolicBallCutoffHolderConst aTime t₀ t₁ bTime r R) alpha
      (Q.restrict (fun p ↦ chi p.time p.space)) := by
    exact parabolicBallCutoff_holderWith_restrict
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        halpha1.le (Icc (0 : Real) S)
  have hchiNorm : ∀ p, p ∈ Q → ‖chi p.time p.space‖ ≤ (1 : NNReal) := by
    intro p _hp
    exact norm_parabolicBallCutoff_le_one
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        p.time p.space
  have hQsource : Q ∩ Qsource = Qsource := by
    apply Set.inter_eq_right.mpr
    intro p hp
    exact ⟨hp.1, Set.mem_univ p.space⟩
  have hchiZero : ∀ p, p ∈ Q → p ∉ Qsource →
      chi p.time p.space = 0 := by
    intro p hpQ hpSource
    have hspace : p.space ∉ Metric.ball center R := by
      intro hpball
      exact hpSource ⟨hpQ.1, hpball⟩
    change intervalCutoffBcf aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b p.time •
      ballCutoff center r R p.space = 0
    rw [ballCutoff_eq_zero_of_not_mem_ball hr hrR hspace, smul_zero]
  have hsourceHolder' : HolderWith Ksource alpha
      ((Q ∩ Qsource).restrict
        (parabolicVariableMatrixOperator a (fun t x ↦ u t x))) := by
    rw [hQsource]
    exact hsourceHolder
  have hspatialSupport : ∀ j < 3, ∀ p,
      p.time ∈ Icc (0 : Real) S → p.time ∉ Ioo aTime bTime →
        parabolicSpatialJet j W p = 0 := by
    intro j _hj p _hp hpmem
    have hchiZeroTime : chi p.time = 0 :=
      parabolicBallCutoff_eq_zero_of_time_not_mem
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR hpmem
    have hWZero : W p.time = 0 := by
      funext x
      change chi p.time x • u p.time x = 0
      rw [hchiZeroTime]
      exact zero_smul Real (u p.time x)
    unfold parabolicSpatialJet
    rw [hWZero]
    change iteratedFDeriv Real j (fun _ : Euc n ↦ (0 : F)) p.space = 0
    rw [iteratedFDeriv_fun_zero]
    rfl
  have htimeSupport : ∀ p,
      p.time ∈ Icc (0 : Real) S → p.time ∉ Ioo aTime bTime →
        parabolicTimeDerivative W p = 0 := by
    intro p hp hpmem
    have hchiZeroTime : chi p.time = 0 :=
      parabolicBallCutoff_eq_zero_of_time_not_mem
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR hpmem
    have hdtimeChiZero : dtimeChi p.time = 0 :=
      parabolicBallCutoffTimeDerivative_eq_zero_of_time_not_mem
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR hpmem
    have hchiTimePoint : HasDerivAt (fun t ↦ chi t p.space)
        (dtimeChi p.time p.space) p.time := by
      simpa only [BoundedContinuousFunction.evalCLM_apply] using
        (BoundedContinuousFunction.evalCLM Real p.space).hasFDerivAt
          |>.comp_hasDerivAt p.time (hchiTime p.time hp)
    have huTimePoint : HasDerivAt (fun t ↦ u t p.space)
        (dtimeU p.time p.space) p.time := by
      simpa only [BoundedContinuousFunction.evalCLM_apply] using
        (BoundedContinuousFunction.evalCLM Real p.space).hasFDerivAt
          |>.comp_hasDerivAt p.time (huTime p.time hp)
    have hproduct := parabolicTimeDerivative_cutoff
      (fun q ↦ chi q.time q.space) (fun q ↦ dtimeChi q.time q.space)
      (fun t x ↦ u t x) (fun q ↦ dtimeU q.time q.space) p
      (by simpa only [parabolicPoint_time, parabolicPoint_space,
        parabolicPoint_time_space] using hchiTimePoint)
      huTimePoint
    change parabolicTimeDerivative
      (parabolicCutoffValue (fun q ↦ chi q.time q.space)
        (fun t x ↦ u t x)) p = 0
    rw [hproduct]
    unfold parabolicCutoffTimeDerivative
    change chi p.time p.space • dtimeU p.time p.space +
      dtimeChi p.time p.space • u p.time p.space = 0
    rw [show chi p.time p.space = 0 by rw [hchiZeroTime]; rfl,
      show dtimeChi p.time p.space = 0 by rw [hdtimeChiZero]; rfl]
    simp only [zero_smul, zero_add]
  have hlocalize : eParabolicC2HolderGaugeOn alpha Q W ≤
      eParabolicC2HolderGaugeOn alpha QT W := by
    exact eParabolicC2HolderGaugeOn_Icc_le_Ioc_of_time_support
      haTime haT hbT hTS.le alpha W hspatialSupport htimeSupport
  have hQTQ : QT ⊆ Q := by
    intro p hp
    exact ⟨⟨hp.1.1.le, hp.1.2.trans hTS.le⟩, Set.mem_univ p.space⟩
  have hlocalFinite : eParabolicC2HolderGaugeOn alpha QT W ≠ ⊤ := by
    apply ne_of_lt
    exact (eParabolicC2HolderGaugeOn_mono hQTQ alpha W).trans_lt
      (lt_top_iff_ne_top.mpr (by simpa only [Q, W, chi] using hcutoffFinite))
  let X : NNReal :=
    (eParabolicC2HolderGaugeOn alpha QT W).toNNReal
  have hX : (X : ENNReal) = eParabolicC2HolderGaugeOn alpha QT W := by
    exact ENNReal.coe_toNNReal hlocalFinite
  have hcutoffGauge : eParabolicC2HolderGaugeOn alpha Q W ≤ X := by
    rw [hX]
    exact hlocalize
  have hraw : eParabolicC2HolderGaugeOn alpha QT W ≤
      spdHeatPotentialSchauderConst (fun i j ↦ a i j p0) hA alpha
        (parabolicCutoffSourceHolderConst
            (parabolicBallCutoffHolderConst aTime t₀ t₁ bTime r R)
            Ksource Kcomm 1 Bsource +
          X * parabolicMatrixFreezeHolderConst Ka omega)
        (parabolicCutoffSourceSupConst 1 Bsource Bcomm +
          X * parabolicMatrixFreezeSupConst omega) T := by
    simpa only [Q, QT, chi, dtimeChi, dchi, d2chi, W] using
      (parabolic_variable_coefficient_schauder_estimate_of_local_cutoff_source_estimates
        (U := Qsource)
        halpha0 halpha1 hT hTS a p0 hA chi dtimeChi dchi d2chi
        u dtimeU du d2u hchiTime huTime hchi hdchi hu hdu hchiCont huCont
        hchi0 hchiHolder hsourceHolder' hcommHolder
        (fun p hp _ ↦ hchiNorm p hp)
        (fun p _ hp ↦ hsourceNorm p hp) hchiZero hcommNorm
        Ka omega ha homega hcutoffGauge)
  have habsorb := parabolic_schauder_estimate_of_small_freeze_defect
    halpha1 hT (fun i j ↦ a i j p0) hA Ka omega W hraw hX.le hsmall
  have hUOpen : IsOpen U :=
    isOpen_parabolicCylinder isOpen_Ioo Metric.isOpen_ball
  have hUOut : U ⊆ QT := by
    intro p hp
    exact ⟨⟨haTime.trans (hat₀.trans hp.1.1),
      hp.1.2.le.trans (ht₁b.trans hbT).le⟩, Set.mem_univ p.space⟩
  have heq : Set.EqOn (fun p ↦ u p.time p.space)
      (fun p ↦ W p.time p.space) U := by
    intro p hp
    change u p.time p.space = chi p.time p.space • u p.time p.space
    rw [show chi p.time p.space = 1 from
      parabolicBallCutoff_eq_one
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        ⟨hp.1.1.le, hp.1.2.le⟩ (Metric.ball_subset_closedBall hp.2), one_smul]
  calc
    eParabolicC2HolderGaugeOn alpha U (fun t x ↦ u t x) =
        eParabolicC2HolderGaugeOn alpha U W :=
      eParabolicC2HolderGaugeOn_congr_of_eqOn_open
        hUOpen Set.Subset.rfl heq alpha
    _ ≤ eParabolicC2HolderGaugeOn alpha QT W :=
      eParabolicC2HolderGaugeOn_mono hUOut alpha W
    _ ≤ parabolicBallInteriorAbsorbedSchauderConst a p0 hA alpha
        aTime t₀ t₁ bTime r R Ksource Kcomm Bsource Bcomm
        Ka omega T := by
      simpa only [parabolicBallInteriorAbsorbedSchauderConst] using habsorb

theorem parabolic_variable_coefficient_ball_interior_schauder_estimate_of_local_source_estimates_of_small_freeze_defect
    {alpha Ksource Ku KdtimeU Kdu Kd2u Bsource Mu MdtimeU Mdu Md2u : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {aTime t₀ t₁ bTime S T : Real}
    (haTime : 0 < aTime) (hat₀ : aTime < t₀) (ht₀t₁ : t₀ ≤ t₁)
    (ht₁b : t₁ < bTime) (hbT : bTime < T) (hTS : T < S)
    (center : Euc n) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (u dtimeU : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (huTime : ∀ s ∈ Icc (0 : Real) S, HasDerivAt u (dtimeU s) s)
    (hu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (u s : Euc n → F) (du s x) x)
    (hdu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (du s : Euc n → Euc n →L[Real] F) (d2u s x) x)
    (huCont : Continuous u)
    (hsourceHolder : HolderWith Ksource alpha
      ((parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R)).restrict
        (parabolicVariableMatrixOperator a (fun t x ↦ u t x))))
    (hsourceNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R) →
        ‖parabolicVariableMatrixOperator a (fun t x ↦ u t x) p‖ ≤ Bsource)
    (A Ka omega : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict (a i j)))
    (homega : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p0 - a i j p‖ ≤ omega i j)
    (haNorm : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p‖ ≤ A i j)
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
      (fun i j ↦ a i j p0) hA alpha Ka omega T < 1) :
    eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Ioo t₀ t₁) (Metric.ball center r))
        (fun t x ↦ u t x) ≤
      parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst
        a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
        Ksource Kdu Ku Bsource Mdu Mu A Ka omega T := by
  let Q := parabolicCylinder (Icc (0 : Real) S) (Set.univ : Set (Euc n))
  let dtimeChi : ParabolicPoint (Euc n) → Real := fun q ↦
    parabolicBallCutoffTimeDerivative
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        q.time q.space
  let dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real := fun q ↦
    parabolicBallCutoffSpatialFDeriv
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        q.time q.space
  let d2chi : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] Real := fun q ↦
    parabolicBallCutoffSpatialFDeriv2
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        q.time q.space
  let Kcomm := parabolicBallCutoffOperatorCommutatorHolderConst
    aTime t₀ t₁ bTime center hr hrR A Ka Kdu Ku Mdu Mu
  let Bcomm := parabolicBallCutoffOperatorCommutatorSupConst
    aTime t₀ t₁ bTime r R A Mdu Mu
  have hcommHolder : HolderWith Kcomm alpha
      (Q.restrict
        (parabolicCutoffOperatorCommutator a dtimeChi dchi d2chi
          (fun t x ↦ u t x) (fun p ↦ du p.time p.space))) := by
    exact parabolicBallCutoffOperatorCommutator_holderWith_restrict
      halpha1.le aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
      a (fun t x ↦ u t x) (fun p ↦ du p.time p.space)
      A Ka Mdu Mu ha hduHolder huHolder haNorm hduNorm huNorm
  have hcommNorm : ∀ p, p ∈ Q →
      ‖parabolicCutoffOperatorCommutator a dtimeChi dchi d2chi
        (fun t x ↦ u t x) (fun q ↦ du q.time q.space) p‖ ≤ Bcomm := by
    intro p hp
    exact norm_parabolicBallCutoffOperatorCommutator_le
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
      a (fun t x ↦ u t x) (fun q ↦ du q.time q.space)
      A Mdu Mu haNorm hduNorm huNorm p hp
  have hcutoffBound : eParabolicC2HolderGaugeOn alpha Q
      (fun t x ↦ parabolicBallCutoff
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR t x •
          u t x) ≤
      parabolicBallCutoffC2HolderGaugeConst
        aTime t₀ t₁ bTime center hr hrR
        Ku KdtimeU Kdu Kd2u Mu MdtimeU Mdu Md2u := by
    exact eParabolicC2HolderGaugeOn_parabolicBallCutoff_le
      halpha1.le aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
      u dtimeU du d2u huTime hu hdu huHolder hdtimeUHolder
      hduHolder hd2uHolder huNorm hdtimeUNorm hduNorm hd2uNorm
  have hcutoffFinite : eParabolicC2HolderGaugeOn alpha Q
      (fun t x ↦ parabolicBallCutoff
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR t x •
          u t x) ≠ ⊤ := by
    exact ne_of_lt (hcutoffBound.trans_lt ENNReal.coe_lt_top)
  simpa only [Q, dtimeChi, dchi, d2chi, Kcomm, Bcomm,
      parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst] using
    (parabolic_variable_coefficient_ball_interior_schauder_estimate_of_local_cutoff_source_estimates_of_small_freeze_defect
      halpha0 halpha1 haTime hat₀ ht₀t₁ ht₁b hbT hTS center hr hrR
      a p0 hA u dtimeU du d2u huTime hu hdu huCont hsourceHolder
      hcommHolder hsourceNorm hcommNorm Ka omega ha homega
      hcutoffFinite hsmall)

theorem parabolic_variable_coefficient_ball_interior_schauder_estimate_of_local_source_and_solution_estimates_of_small_freeze_defect
    {alpha Ksource Ku KdtimeU Kdu Kd2u Bsource Mu MdtimeU Mdu Md2u : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {aTime t₀ t₁ bTime S T : Real}
    (haTime : 0 < aTime) (hat₀ : aTime < t₀) (ht₀t₁ : t₀ ≤ t₁)
    (ht₁b : t₁ < bTime) (hbT : bTime < T) (hTS : T < S)
    (center : Euc n) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (u dtimeU : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (huTime : ∀ s ∈ Icc (0 : Real) S, HasDerivAt u (dtimeU s) s)
    (hu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (u s : Euc n → F) (du s x) x)
    (hdu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (du s : Euc n → Euc n →L[Real] F) (d2u s x) x)
    (huCont : Continuous u)
    (hsourceHolder : HolderWith Ksource alpha
      ((parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R)).restrict
        (parabolicVariableMatrixOperator a (fun t x ↦ u t x))))
    (hsourceNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R) →
        ‖parabolicVariableMatrixOperator a (fun t x ↦ u t x) p‖ ≤ Bsource)
    (A Ka omega : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict (a i j)))
    (homega : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p0 - a i j p‖ ≤ omega i j)
    (haNorm : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p‖ ≤ A i j)
    (huHolder : HolderWith Ku alpha
      ((parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R)).restrict
        (fun p ↦ u p.time p.space)))
    (hdtimeUHolder : HolderWith KdtimeU alpha
      ((parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R)).restrict
        (fun p ↦ dtimeU p.time p.space)))
    (hduHolder : HolderWith Kdu alpha
      ((parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R)).restrict
        (fun p ↦ du p.time p.space)))
    (hd2uHolder : HolderWith Kd2u alpha
      ((parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R)).restrict
        (fun p ↦ d2u p.time p.space)))
    (huNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R) →
        ‖u p.time p.space‖ ≤ Mu)
    (hdtimeUNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R) →
        ‖dtimeU p.time p.space‖ ≤ MdtimeU)
    (hduNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R) →
        ‖du p.time p.space‖ ≤ Mdu)
    (hd2uNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R) →
        ‖d2u p.time p.space‖ ≤ Md2u)
    (hsmall : spdParabolicSchauderDefectConst
      (fun i j ↦ a i j p0) hA alpha Ka omega T < 1) :
    eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Ioo t₀ t₁) (Metric.ball center r))
        (fun t x ↦ u t x) ≤
      parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst
        a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
        Ksource Kdu Ku Bsource Mdu Mu A Ka omega T := by
  let Q := parabolicCylinder (Icc (0 : Real) S) (Set.univ : Set (Euc n))
  let dtimeChi : ParabolicPoint (Euc n) → Real := fun q ↦
    parabolicBallCutoffTimeDerivative
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR q.time q.space
  let dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real := fun q ↦
    parabolicBallCutoffSpatialFDeriv
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR q.time q.space
  let d2chi : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] Real := fun q ↦
    parabolicBallCutoffSpatialFDeriv2
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR q.time q.space
  let Kcomm := parabolicBallCutoffOperatorCommutatorHolderConst
    aTime t₀ t₁ bTime center hr hrR A Ka Kdu Ku Mdu Mu
  let Bcomm := parabolicBallCutoffOperatorCommutatorSupConst
    aTime t₀ t₁ bTime r R A Mdu Mu
  have hcommHolder : HolderWith Kcomm alpha
      (Q.restrict
        (parabolicCutoffOperatorCommutator a dtimeChi dchi d2chi
          (fun t x ↦ u t x) (fun p ↦ du p.time p.space))) := by
    exact parabolicBallCutoffOperatorCommutator_holderWith_restrict_of_local_solution
      halpha1.le aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
      a (fun t x ↦ u t x) (fun p ↦ du p.time p.space)
      A Ka Mdu Mu ha hduHolder huHolder haNorm hduNorm huNorm
  have hcommNorm : ∀ p, p ∈ Q →
      ‖parabolicCutoffOperatorCommutator a dtimeChi dchi d2chi
        (fun t x ↦ u t x) (fun q ↦ du q.time q.space) p‖ ≤ Bcomm := by
    intro p hp
    exact norm_parabolicBallCutoffOperatorCommutator_le_of_local_solution
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
      a (fun t x ↦ u t x) (fun q ↦ du q.time q.space)
      A Mdu Mu haNorm hduNorm huNorm p hp
  have hcutoffBound : eParabolicC2HolderGaugeOn alpha Q
      (fun t x ↦ parabolicBallCutoff
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR t x • u t x) ≤
      parabolicBallCutoffC2HolderGaugeConst
        aTime t₀ t₁ bTime center hr hrR
        Ku KdtimeU Kdu Kd2u Mu MdtimeU Mdu Md2u := by
    exact eParabolicC2HolderGaugeOn_parabolicBallCutoff_le_of_local_solution
      halpha1.le aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
      u dtimeU du d2u huTime hu hdu huHolder hdtimeUHolder
      hduHolder hd2uHolder huNorm hdtimeUNorm hduNorm hd2uNorm
  have hcutoffFinite : eParabolicC2HolderGaugeOn alpha Q
      (fun t x ↦ parabolicBallCutoff
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR t x • u t x) ≠ ⊤ := by
    exact ne_of_lt (hcutoffBound.trans_lt ENNReal.coe_lt_top)
  simpa only [Q, dtimeChi, dchi, d2chi, Kcomm, Bcomm,
      parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst] using
    (parabolic_variable_coefficient_ball_interior_schauder_estimate_of_local_cutoff_source_estimates_of_small_freeze_defect
      halpha0 halpha1 haTime hat₀ ht₀t₁ ht₁b hbT hTS center hr hrR
      a p0 hA u dtimeU du d2u huTime hu hdu huCont hsourceHolder
      hcommHolder hsourceNorm hcommNorm Ka omega ha homega hcutoffFinite hsmall)

theorem parabolic_variable_coefficient_ball_interior_schauder_estimate_of_buffered_interpolation_of_local_source_estimates_of_small_freeze_defect
    {alpha Ksource Bsource C M : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (epsilon delta : NNReal) (hepsilon : 0 < epsilon)
    (hepsilonDelta : epsilon < delta)
    {aTime t₀ t₁ bTime S T : Real}
    (haTime : 0 < aTime) (hat₀ : aTime < t₀) (ht₀t₁ : t₀ ≤ t₁)
    (ht₁b : t₁ < bTime) (hbT : bTime < T) (hTS : T < S)
    (center : Euc n) {r R Rout : Real}
    (hr : 0 ≤ r) (hrR : r < R) (hbuffer : R + delta ≤ Rout)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (u dtimeU : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (huTime : ∀ s ∈ Icc (0 : Real) S, HasDerivAt u (dtimeU s) s)
    (hu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (u s : Euc n → F) (du s x) x)
    (hdu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (du s : Euc n → Euc n →L[Real] F) (d2u s x) x)
    (huCont : Continuous u)
    (hsourceHolder : HolderWith Ksource alpha
      ((parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R)).restrict
        (parabolicVariableMatrixOperator a (fun t x ↦ u t x))))
    (hsourceNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R) →
        ‖parabolicVariableMatrixOperator a (fun t x ↦ u t x) p‖ ≤ Bsource)
    (A Ka omega : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict (a i j)))
    (homega : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p0 - a i j p‖ ≤ omega i j)
    (haNorm : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p‖ ≤ A i j)
    (hgauge : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Icc (0 : Real) S) (Metric.ball center Rout))
      (fun t x ↦ u t x) ≤ C)
    (huNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) (Metric.ball center Rout) →
        ‖u p.time p.space‖ ≤ M)
    (hsmall : spdParabolicSchauderDefectConst
      (fun i j ↦ a i j p0) hA alpha Ka omega T < 1) :
    eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Ioo t₀ t₁) (Metric.ball center r))
        (fun t x ↦ u t x) ≤
      parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst
        a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
        Ksource
        (bufferedParabolicSpatialGradientInterpolationConst
          epsilon delta alpha C M)
        (parabolicValueInterpolationConst epsilon alpha C M)
        Bsource (2 * M / epsilon + C * epsilon) M A Ka omega T := by
  let J := Icc (0 : Real) S
  let Qout := parabolicCylinder J (Metric.ball center Rout)
  let Q := parabolicCylinder J (Metric.ball center R)
  let Qclosed := parabolicCylinder J (Metric.closedBall center R)
  let e1 := continuousMultilinearCurryFin1 Real (Euc n) F
  let e2 := hessianCurryEquiv (Euc n) F
  have hdelta : 0 < delta := hepsilon.trans hepsilonDelta
  have hRRout : R < Rout := by
    calc
      R < R + (delta : Real) := lt_add_of_pos_right R (by exact_mod_cast hdelta)
      _ ≤ Rout := hbuffer
  have hQout : Q ⊆ Qout := by
    intro p hp
    exact ⟨hp.1, Metric.ball_subset_ball hRRout.le hp.2⟩
  have hQQclosed : Q ⊆ Qclosed := by
    intro p hp
    exact ⟨hp.1, Metric.ball_subset_closedBall hp.2⟩
  have huC2 : IsParabolicC2On Qout (fun t x ↦ u t x) := by
    constructor
    · intro p hp
      exact (contDiff_two_of_hasFDerivAt (u p.time) (du p.time) (d2u p.time)
        (hu p.time hp.1) (hdu p.time hp.1)).contDiffAt
    · intro p hp
      exact ((BoundedContinuousFunction.evalCLM Real p.space).hasFDerivAt
        |>.comp_hasDerivAt p.time (huTime p.time hp.1)).differentiableAt
  have huC2Q : IsParabolicC2On Q (fun t x ↦ u t x) :=
    ⟨fun p hp ↦ huC2.1 p (hQout hp), fun p hp ↦ huC2.2 p (hQout hp)⟩
  have hgaugeQ : eParabolicC2HolderGaugeOn alpha Q (fun t x ↦ u t x) ≤ C :=
    (eParabolicC2HolderGaugeOn_mono hQout alpha (fun t x ↦ u t x)).trans
      (by simpa only [Qout, J] using hgauge)
  have huNormQ : ∀ p, p ∈ Q → ‖u p.time p.space‖ ≤ M :=
    fun p hp ↦ huNorm p (by simpa only [Qout, J] using hQout hp)
  have hduEq : ∀ p ∈ Qclosed,
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
    exact parabolicValue_holderWith_restrict_of_interpolation
      (convex_Icc (0 : Real) S) (convex_ball center R) epsilon hepsilon
      halpha1.le huC2Q hgaugeQ huNormQ
  have hjetHolderClosed :=
    parabolicSpatialJet_one_holderWith_restrict_of_buffered_ball_interpolation
      (convex_Icc (0 : Real) S) center epsilon delta hepsilon hepsilonDelta
      hbuffer halpha1.le huC2 (by simpa only [Qout, J] using hgauge)
        (by simpa only [Qout, J] using huNorm)
  have hjetHolder : HolderWith
      (bufferedParabolicSpatialGradientInterpolationConst
        epsilon delta alpha C M) alpha
      (Q.restrict (parabolicSpatialJet 1 (fun t x ↦ u t x))) :=
    ((HolderWith.restrict_iff.mp hjetHolderClosed).mono hQQclosed).holderWith
  have hduHolder : HolderWith
      (bufferedParabolicSpatialGradientInterpolationConst
        epsilon delta alpha C M) alpha
      (Q.restrict (fun p ↦ du p.time p.space)) := by
    have hcomp := e1.lipschitz.holderWith.comp hjetHolder
    have hfun : e1 ∘ Q.restrict
        (parabolicSpatialJet 1 (fun t x ↦ u t x)) =
          Q.restrict (fun p ↦ du p.time p.space) := by
      funext p
      exact hduEq p.1 (hQQclosed p.2)
    rw [hfun] at hcomp
    simpa only [NNReal.coe_one, NNReal.rpow_one, one_mul] using hcomp
  have hdtimeUHolder : HolderWith C alpha
      (Q.restrict (fun p ↦ dtimeU p.time p.space)) := by
    have hbase := parabolicTimeDerivative_holderWith_restrict hgaugeQ
    have hfun : Q.restrict (parabolicTimeDerivative (fun t x ↦ u t x)) =
        Q.restrict (fun p ↦ dtimeU p.time p.space) := by
      funext p
      exact hdtimeUEq p.1 p.2
    rwa [hfun] at hbase
  have hd2uHolder : HolderWith C alpha
      (Q.restrict (fun p ↦ d2u p.time p.space)) := by
    have hbase := parabolicSpatialJet_holderWith_restrict hgaugeQ
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
    exact parabolicTimeDerivative_norm_le hgaugeQ hp
  have hduNorm : ∀ p, p ∈ Q →
      ‖du p.time p.space‖ ≤ 2 * M / epsilon + C * epsilon := by
    intro p hp
    rw [← hduEq p (hQQclosed hp), LinearIsometryEquiv.norm_map]
    exact norm_parabolicSpatialJet_one_le_of_buffered_ball
      center epsilon hepsilon (by
        calc
          R + (epsilon : Real) < R + (delta : Real) := by gcongr
          _ ≤ Rout := hbuffer)
      huC2 (by simpa only [Qout, J] using hgauge)
        (by simpa only [Qout, J] using huNorm) p (hQQclosed hp)
  have hd2uNorm : ∀ p, p ∈ Q → ‖d2u p.time p.space‖ ≤ C := by
    intro p hp
    rw [← hd2uEq p hp, LinearIsometryEquiv.norm_map]
    exact parabolicSpatialJet_norm_le hgaugeQ (j := 2) (by omega) hp
  simpa only [Q, J] using
    (parabolic_variable_coefficient_ball_interior_schauder_estimate_of_local_source_and_solution_estimates_of_small_freeze_defect
      (alpha := alpha) (Ksource := Ksource)
      (Ku := parabolicValueInterpolationConst epsilon alpha C M)
      (KdtimeU := C)
      (Kdu := bufferedParabolicSpatialGradientInterpolationConst
        epsilon delta alpha C M)
      (Kd2u := C) (Bsource := Bsource) (Mu := M)
      (MdtimeU := C) (Mdu := 2 * M / epsilon + C * epsilon)
      (Md2u := C) halpha0 halpha1 haTime hat₀ ht₀t₁ ht₁b hbT hTS
      center hr hrR a p0 hA u dtimeU du d2u huTime hu hdu huCont
      hsourceHolder hsourceNorm A Ka omega ha homega haNorm
      huHolder hdtimeUHolder hduHolder hd2uHolder
      huNormQ hdtimeUNorm hduNorm hd2uNorm hsmall)

theorem parabolic_variable_coefficient_ball_interior_schauder_estimate_of_local_source_and_solution_estimates
    {alpha Ksource Kdu Ku Bsource Mdu Mu X : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {aTime t₀ t₁ bTime S T : Real}
    (haTime : 0 ≤ aTime) (hat₀ : aTime < t₀) (ht₀t₁ : t₀ ≤ t₁)
    (ht₁b : t₁ < bTime) (ht₁T : t₁ ≤ T)
    (hT : 0 ≤ T) (hTS : T < S)
    (center : Euc n) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (u dtimeU : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (huTime : ∀ s ∈ Icc (0 : Real) S, HasDerivAt u (dtimeU s) s)
    (hu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (u s : Euc n → F) (du s x) x)
    (hdu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (du s : Euc n → Euc n →L[Real] F) (d2u s x) x)
    (huCont : Continuous u)
    (hsourceHolder : HolderWith Ksource alpha
      ((parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R)).restrict
        (parabolicVariableMatrixOperator a (fun t x ↦ u t x))))
    (hsourceNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R) →
        ‖parabolicVariableMatrixOperator a (fun t x ↦ u t x) p‖ ≤ Bsource)
    (A Ka omega : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict (a i j)))
    (homega : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p0 - a i j p‖ ≤ omega i j)
    (haNorm : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p‖ ≤ A i j)
    (hduHolder : HolderWith Kdu alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p ↦ du p.time p.space)))
    (huHolder : HolderWith Ku alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p ↦ u p.time p.space)))
    (hduNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖du p.time p.space‖ ≤ Mdu)
    (huNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖u p.time p.space‖ ≤ Mu)
    (hcutoffGauge : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Icc (0 : Real) S) Set.univ)
      (fun t x ↦ parabolicBallCutoff
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR t x •
          u t x) ≤ X) :
    eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Ioo t₀ t₁) (Metric.ball center r))
        (fun t x ↦ u t x) ≤
      parabolicBallInteriorSchauderConst a p0 hA alpha
        aTime t₀ t₁ bTime r R Ksource
        (parabolicBallCutoffOperatorCommutatorHolderConst
          aTime t₀ t₁ bTime center hr hrR A Ka Kdu Ku Mdu Mu)
        Bsource
        (parabolicBallCutoffOperatorCommutatorSupConst
          aTime t₀ t₁ bTime r R A Mdu Mu)
        X Ka omega T := by
  let Q := parabolicCylinder (Icc (0 : Real) S) (Set.univ : Set (Euc n))
  let dtimeChi : ParabolicPoint (Euc n) → Real := fun q ↦
    parabolicBallCutoffTimeDerivative
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        q.time q.space
  let dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real := fun q ↦
    parabolicBallCutoffSpatialFDeriv
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        q.time q.space
  let d2chi : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] Real := fun q ↦
    parabolicBallCutoffSpatialFDeriv2
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        q.time q.space
  have hcommHolder : HolderWith
      (parabolicBallCutoffOperatorCommutatorHolderConst
        aTime t₀ t₁ bTime center hr hrR A Ka Kdu Ku Mdu Mu)
      alpha (Q.restrict
        (parabolicCutoffOperatorCommutator a dtimeChi dchi d2chi
          (fun t x ↦ u t x) (fun p ↦ du p.time p.space))) := by
    exact parabolicBallCutoffOperatorCommutator_holderWith_restrict
      halpha1.le aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
      a (fun t x ↦ u t x) (fun p ↦ du p.time p.space)
      A Ka Mdu Mu ha hduHolder huHolder haNorm hduNorm huNorm
  have hcommNorm : ∀ p, p ∈ Q →
      ‖parabolicCutoffOperatorCommutator a dtimeChi dchi d2chi
        (fun t x ↦ u t x) (fun q ↦ du q.time q.space) p‖ ≤
          parabolicBallCutoffOperatorCommutatorSupConst
            aTime t₀ t₁ bTime r R A Mdu Mu := by
    intro p hp
    exact norm_parabolicBallCutoffOperatorCommutator_le
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
      a (fun t x ↦ u t x) (fun q ↦ du q.time q.space)
      A Mdu Mu haNorm hduNorm huNorm p hp
  exact
    parabolic_variable_coefficient_ball_interior_schauder_estimate_of_local_cutoff_source_estimates
      halpha0 halpha1 haTime hat₀ ht₀t₁ ht₁b ht₁T hT hTS center hr hrR
      a p0 hA u dtimeU du d2u huTime hu hdu huCont hsourceHolder
      (by simpa only [Q, dtimeChi, dchi, d2chi] using hcommHolder)
      hsourceNorm (by simpa only [Q, dtimeChi, dchi, d2chi] using hcommNorm)
      Ka omega ha homega hcutoffGauge

theorem parabolic_variable_coefficient_ball_interior_schauder_estimate_of_local_lower_order_source_estimates
    {alpha Ksource Klo Kdu Ku Bsource Blo Mdu Mu X : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {aTime t₀ t₁ bTime S T : Real}
    (haTime : 0 ≤ aTime) (hat₀ : aTime < t₀) (ht₀t₁ : t₀ ≤ t₁)
    (ht₁b : t₁ < bTime) (ht₁T : t₁ ≤ T)
    (hT : 0 ≤ T) (hTS : T < S)
    (center : Euc n) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (b : n → ParabolicPoint (Euc n) → Real)
    (c : ParabolicPoint (Euc n) → Real)
    (u dtimeU : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (huTime : ∀ s ∈ Icc (0 : Real) S, HasDerivAt u (dtimeU s) s)
    (hu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (u s : Euc n → F) (du s x) x)
    (hdu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (du s : Euc n → Euc n →L[Real] F) (d2u s x) x)
    (huCont : Continuous u)
    (hsourceHolder : HolderWith Ksource alpha
      ((parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R)).restrict
        (parabolicNondivergenceOperator a b c (fun t x ↦ u t x))))
    (hlowerHolder : HolderWith Klo alpha
      ((parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R)).restrict
        (parabolicLowerOrderTerm b c (fun t x ↦ u t x))))
    (hsourceNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R) →
        ‖parabolicNondivergenceOperator a b c (fun t x ↦ u t x) p‖ ≤
          Bsource)
    (hlowerNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R) →
        ‖parabolicLowerOrderTerm b c (fun t x ↦ u t x) p‖ ≤ Blo)
    (A Ka omega : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict (a i j)))
    (homega : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p0 - a i j p‖ ≤ omega i j)
    (haNorm : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p‖ ≤ A i j)
    (hduHolder : HolderWith Kdu alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p ↦ du p.time p.space)))
    (huHolder : HolderWith Ku alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p ↦ u p.time p.space)))
    (hduNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖du p.time p.space‖ ≤ Mdu)
    (huNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖u p.time p.space‖ ≤ Mu)
    (hcutoffGauge : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Icc (0 : Real) S) Set.univ)
      (fun t x ↦ parabolicBallCutoff
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR t x •
          u t x) ≤ X) :
    eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Ioo t₀ t₁) (Metric.ball center r))
        (fun t x ↦ u t x) ≤
      parabolicBallInteriorSchauderConst a p0 hA alpha
        aTime t₀ t₁ bTime r R (Ksource + Klo)
        (parabolicBallCutoffOperatorCommutatorHolderConst
          aTime t₀ t₁ bTime center hr hrR A Ka Kdu Ku Mdu Mu)
        (Bsource + Blo)
        (parabolicBallCutoffOperatorCommutatorSupConst
          aTime t₀ t₁ bTime r R A Mdu Mu)
        X Ka omega T := by
  apply
    parabolic_variable_coefficient_ball_interior_schauder_estimate_of_local_source_and_solution_estimates
      halpha0 halpha1 haTime hat₀ ht₀t₁ ht₁b ht₁T hT hTS center hr hrR
      a p0 hA u dtimeU du d2u huTime hu hdu huCont
  · rw [parabolicVariableMatrixOperator_eq_nondivergenceOperator_add_lowerOrderTerm]
    exact hsourceHolder.add hlowerHolder
  · intro p hp
    rw [parabolicVariableMatrixOperator_eq_nondivergenceOperator_add_lowerOrderTerm]
    exact (norm_add_le _ _).trans
      (add_le_add (hsourceNorm p hp) (hlowerNorm p hp))
  · exact ha
  · exact homega
  · exact haNorm
  · exact hduHolder
  · exact huHolder
  · exact hduNorm
  · exact huNorm
  · exact hcutoffGauge

theorem parabolic_nondivergence_ball_interior_schauder_estimate_of_local_source_estimates
    {alpha Ksource Kc Kdu Ku Bsource Bc Mdu Mu X : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {aTime t₀ t₁ bTime S T : Real}
    (haTime : 0 ≤ aTime) (hat₀ : aTime < t₀) (ht₀t₁ : t₀ ≤ t₁)
    (ht₁b : t₁ < bTime) (ht₁T : t₁ ≤ T)
    (hT : 0 ≤ T) (hTS : T < S)
    (center : Euc n) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (b : n → ParabolicPoint (Euc n) → Real)
    (c : ParabolicPoint (Euc n) → Real)
    (u dtimeU : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (huTime : ∀ s ∈ Icc (0 : Real) S, HasDerivAt u (dtimeU s) s)
    (hu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (u s : Euc n → F) (du s x) x)
    (hdu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (du s : Euc n → Euc n →L[Real] F) (d2u s x) x)
    (huCont : Continuous u)
    (hsourceHolder : HolderWith Ksource alpha
      ((parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R)).restrict
        (parabolicNondivergenceOperator a b c (fun t x ↦ u t x))))
    (hsourceNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R) →
        ‖parabolicNondivergenceOperator a b c (fun t x ↦ u t x) p‖ ≤
          Bsource)
    (Kb Bb : n → NNReal) (A Ka omega : n → n → NNReal)
    (hb : ∀ i, HolderWith (Kb i) alpha
      ((parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R)).restrict
        (b i)))
    (hc : HolderWith Kc alpha
      ((parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R)).restrict
        c))
    (hbNorm : ∀ i p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R) →
        ‖b i p‖ ≤ Bb i)
    (hcNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R) →
        ‖c p‖ ≤ Bc)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict (a i j)))
    (homega : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p0 - a i j p‖ ≤ omega i j)
    (haNorm : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p‖ ≤ A i j)
    (hduHolder : HolderWith Kdu alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p ↦ du p.time p.space)))
    (huHolder : HolderWith Ku alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p ↦ u p.time p.space)))
    (hduNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖du p.time p.space‖ ≤ Mdu)
    (huNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖u p.time p.space‖ ≤ Mu)
    (hcutoffGauge : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Icc (0 : Real) S) Set.univ)
      (fun t x ↦ parabolicBallCutoff
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR t x •
          u t x) ≤ X) :
    eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Ioo t₀ t₁) (Metric.ball center r))
        (fun t x ↦ u t x) ≤
      parabolicBallInteriorSchauderConst a p0 hA alpha
        aTime t₀ t₁ bTime r R
        (Ksource + parabolicLowerOrderHolderConst
          Kb Bb Kc Kdu Ku Mdu Bc Mu)
        (parabolicBallCutoffOperatorCommutatorHolderConst
          aTime t₀ t₁ bTime center hr hrR A Ka Kdu Ku Mdu Mu)
        (Bsource + parabolicLowerOrderSupConst Bb Bc Mdu Mu)
        (parabolicBallCutoffOperatorCommutatorSupConst
          aTime t₀ t₁ bTime r R A Mdu Mu)
        X Ka omega T := by
  let Q := parabolicCylinder (Icc (0 : Real) S) (Set.univ : Set (Euc n))
  let Qlocal := parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R)
  have hQlocalQ : Qlocal ⊆ Q := by
    intro p hp
    exact ⟨hp.1, Set.mem_univ p.space⟩
  let e := continuousMultilinearCurryFin1 Real (Euc n) F
  have heq : ∀ p ∈ Qlocal,
      e (parabolicSpatialJet 1 (fun t x ↦ u t x) p) =
        du p.time p.space := by
    intro p hp
    ext v
    simp only [e, parabolicSpatialJet,
      continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
    rw [(hu p.time hp.1 p.space).fderiv]
    rfl
  have hduHolderLocal : HolderWith Kdu alpha
      (Qlocal.restrict (fun p ↦ du p.time p.space)) :=
    ((HolderWith.restrict_iff.mp hduHolder).mono hQlocalQ).holderWith
  have huHolderLocal : HolderWith Ku alpha
      (Qlocal.restrict (fun p ↦ u p.time p.space)) :=
    ((HolderWith.restrict_iff.mp huHolder).mono hQlocalQ).holderWith
  have hjetHolder : HolderWith Kdu alpha
      (Qlocal.restrict (parabolicSpatialJet 1 (fun t x ↦ u t x))) := by
    have hcomp := e.symm.lipschitz.holderWith.comp hduHolderLocal
    have hfun : e.symm ∘ Qlocal.restrict (fun p ↦ du p.time p.space) =
        Qlocal.restrict (parabolicSpatialJet 1 (fun t x ↦ u t x)) := by
      funext p
      change e.symm (du p.1.time p.1.space) =
        parabolicSpatialJet 1 (fun t x ↦ u t x) p.1
      rw [← heq p.1 p.2, e.symm_apply_apply]
    rw [hfun] at hcomp
    simpa only [Qlocal, NNReal.coe_one, NNReal.rpow_one, one_mul] using hcomp
  have hjetNorm : ∀ p, p ∈ Qlocal →
      ‖parabolicSpatialJet 1 (fun t x ↦ u t x) p‖ ≤ Mdu := by
    intro p hp
    rw [← e.norm_map, heq p hp]
    exact hduNorm p (hQlocalQ hp)
  have huNormLocal : ∀ p, p ∈ Qlocal → ‖u p.time p.space‖ ≤ Mu := by
    intro p hp
    exact huNorm p (hQlocalQ hp)
  have hlowerHolder : HolderWith
      (parabolicLowerOrderHolderConst Kb Bb Kc Kdu Ku Mdu Bc Mu) alpha
      (Qlocal.restrict
        (parabolicLowerOrderTerm b c (fun t x ↦ u t x))) :=
    parabolicLowerOrderTerm_holderWith_restrict
      b c (fun t x ↦ u t x) Kb Bb Mdu Bc Mu hb hc hjetHolder
        huHolderLocal hbNorm hcNorm hjetNorm huNormLocal
  have hlowerNorm : ∀ p, p ∈ Qlocal →
      ‖parabolicLowerOrderTerm b c (fun t x ↦ u t x) p‖ ≤
        parabolicLowerOrderSupConst Bb Bc Mdu Mu := by
    intro p hp
    exact norm_parabolicLowerOrderTerm_le b c (fun t x ↦ u t x)
      Bb Bc Mdu Mu hbNorm hcNorm hjetNorm huNormLocal p hp
  exact
    parabolic_variable_coefficient_ball_interior_schauder_estimate_of_local_lower_order_source_estimates
      halpha0 halpha1 haTime hat₀ ht₀t₁ ht₁b ht₁T hT hTS center hr hrR
      a p0 hA b c u dtimeU du d2u huTime hu hdu huCont
      hsourceHolder (by simpa only [Qlocal] using hlowerHolder) hsourceNorm
      (by simpa only [Qlocal] using hlowerNorm) A Ka omega ha homega haNorm
      hduHolder huHolder hduNorm huNorm hcutoffGauge

theorem parabolic_variable_coefficient_ball_interior_schauder_estimate_of_local_lower_order_source_estimates_of_small_freeze_defect
    {alpha Ksource Klo Ku KdtimeU Kdu Kd2u Bsource Blo
      Mu MdtimeU Mdu Md2u : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {aTime t₀ t₁ bTime S T : Real}
    (haTime : 0 < aTime) (hat₀ : aTime < t₀) (ht₀t₁ : t₀ ≤ t₁)
    (ht₁b : t₁ < bTime) (hbT : bTime < T) (hTS : T < S)
    (center : Euc n) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (b : n → ParabolicPoint (Euc n) → Real)
    (c : ParabolicPoint (Euc n) → Real)
    (u dtimeU : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (huTime : ∀ s ∈ Icc (0 : Real) S, HasDerivAt u (dtimeU s) s)
    (hu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (u s : Euc n → F) (du s x) x)
    (hdu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (du s : Euc n → Euc n →L[Real] F) (d2u s x) x)
    (huCont : Continuous u)
    (hsourceHolder : HolderWith Ksource alpha
      ((parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R)).restrict
        (parabolicNondivergenceOperator a b c (fun t x ↦ u t x))))
    (hlowerHolder : HolderWith Klo alpha
      ((parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R)).restrict
        (parabolicLowerOrderTerm b c (fun t x ↦ u t x))))
    (hsourceNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R) →
        ‖parabolicNondivergenceOperator a b c (fun t x ↦ u t x) p‖ ≤
          Bsource)
    (hlowerNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R) →
        ‖parabolicLowerOrderTerm b c (fun t x ↦ u t x) p‖ ≤ Blo)
    (A Ka omega : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict (a i j)))
    (homega : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p0 - a i j p‖ ≤ omega i j)
    (haNorm : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p‖ ≤ A i j)
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
      (fun i j ↦ a i j p0) hA alpha Ka omega T < 1) :
    eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Ioo t₀ t₁) (Metric.ball center r))
        (fun t x ↦ u t x) ≤
      parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst
        a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
        (Ksource + Klo) Kdu Ku (Bsource + Blo) Mdu Mu A Ka omega T := by
  apply
    parabolic_variable_coefficient_ball_interior_schauder_estimate_of_local_source_estimates_of_small_freeze_defect
      halpha0 halpha1 haTime hat₀ ht₀t₁ ht₁b hbT hTS center hr hrR
      a p0 hA u dtimeU du d2u huTime hu hdu huCont
  · rw [parabolicVariableMatrixOperator_eq_nondivergenceOperator_add_lowerOrderTerm]
    exact hsourceHolder.add hlowerHolder
  · intro p hp
    rw [parabolicVariableMatrixOperator_eq_nondivergenceOperator_add_lowerOrderTerm]
    exact (norm_add_le _ _).trans
      (add_le_add (hsourceNorm p hp) (hlowerNorm p hp))
  · exact ha
  · exact homega
  · exact haNorm
  · exact huHolder
  · exact hdtimeUHolder
  · exact hduHolder
  · exact hd2uHolder
  · exact huNorm
  · exact hdtimeUNorm
  · exact hduNorm
  · exact hd2uNorm
  · exact hsmall

theorem parabolic_nondivergence_ball_interior_schauder_estimate_of_local_source_estimates_of_small_freeze_defect
    {alpha Ksource Kc Ku KdtimeU Kdu Kd2u Bsource Bc
      Mu MdtimeU Mdu Md2u : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {aTime t₀ t₁ bTime S T : Real}
    (haTime : 0 < aTime) (hat₀ : aTime < t₀) (ht₀t₁ : t₀ ≤ t₁)
    (ht₁b : t₁ < bTime) (hbT : bTime < T) (hTS : T < S)
    (center : Euc n) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (b : n → ParabolicPoint (Euc n) → Real)
    (c : ParabolicPoint (Euc n) → Real)
    (u dtimeU : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (huTime : ∀ s ∈ Icc (0 : Real) S, HasDerivAt u (dtimeU s) s)
    (hu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (u s : Euc n → F) (du s x) x)
    (hdu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (du s : Euc n → Euc n →L[Real] F) (d2u s x) x)
    (huCont : Continuous u)
    (hsourceHolder : HolderWith Ksource alpha
      ((parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R)).restrict
        (parabolicNondivergenceOperator a b c (fun t x ↦ u t x))))
    (hsourceNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R) →
        ‖parabolicNondivergenceOperator a b c (fun t x ↦ u t x) p‖ ≤
          Bsource)
    (Kb Bb : n → NNReal) (A Ka omega : n → n → NNReal)
    (hb : ∀ i, HolderWith (Kb i) alpha
      ((parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R)).restrict
        (b i)))
    (hc : HolderWith Kc alpha
      ((parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R)).restrict
        c))
    (hbNorm : ∀ i p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R) →
        ‖b i p‖ ≤ Bb i)
    (hcNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R) →
        ‖c p‖ ≤ Bc)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict (a i j)))
    (homega : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p0 - a i j p‖ ≤ omega i j)
    (haNorm : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p‖ ≤ A i j)
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
      (fun i j ↦ a i j p0) hA alpha Ka omega T < 1) :
    eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Ioo t₀ t₁) (Metric.ball center r))
        (fun t x ↦ u t x) ≤
      parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst
        a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
        (Ksource + parabolicLowerOrderHolderConst
          Kb Bb Kc Kdu Ku Mdu Bc Mu)
        Kdu Ku
        (Bsource + parabolicLowerOrderSupConst Bb Bc Mdu Mu)
        Mdu Mu A Ka omega T := by
  let Q := parabolicCylinder (Icc (0 : Real) S) (Set.univ : Set (Euc n))
  let Qlocal := parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R)
  have hQlocalQ : Qlocal ⊆ Q := by
    intro p hp
    exact ⟨hp.1, Set.mem_univ p.space⟩
  let e := continuousMultilinearCurryFin1 Real (Euc n) F
  have heq : ∀ p ∈ Qlocal,
      e (parabolicSpatialJet 1 (fun t x ↦ u t x) p) =
        du p.time p.space := by
    intro p hp
    ext v
    simp only [e, parabolicSpatialJet,
      continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
    rw [(hu p.time hp.1 p.space).fderiv]
    rfl
  have hduHolderLocal : HolderWith Kdu alpha
      (Qlocal.restrict (fun p ↦ du p.time p.space)) :=
    ((HolderWith.restrict_iff.mp hduHolder).mono hQlocalQ).holderWith
  have huHolderLocal : HolderWith Ku alpha
      (Qlocal.restrict (fun p ↦ u p.time p.space)) :=
    ((HolderWith.restrict_iff.mp huHolder).mono hQlocalQ).holderWith
  have hjetHolder : HolderWith Kdu alpha
      (Qlocal.restrict (parabolicSpatialJet 1 (fun t x ↦ u t x))) := by
    have hcomp := e.symm.lipschitz.holderWith.comp hduHolderLocal
    have hfun : e.symm ∘ Qlocal.restrict (fun p ↦ du p.time p.space) =
        Qlocal.restrict (parabolicSpatialJet 1 (fun t x ↦ u t x)) := by
      funext p
      change e.symm (du p.1.time p.1.space) =
        parabolicSpatialJet 1 (fun t x ↦ u t x) p.1
      rw [← heq p.1 p.2, e.symm_apply_apply]
    rw [hfun] at hcomp
    simpa only [Qlocal, NNReal.coe_one, NNReal.rpow_one, one_mul] using hcomp
  have hjetNorm : ∀ p, p ∈ Qlocal →
      ‖parabolicSpatialJet 1 (fun t x ↦ u t x) p‖ ≤ Mdu := by
    intro p hp
    rw [← e.norm_map, heq p hp]
    exact hduNorm p (hQlocalQ hp)
  have huNormLocal : ∀ p, p ∈ Qlocal → ‖u p.time p.space‖ ≤ Mu := by
    intro p hp
    exact huNorm p (hQlocalQ hp)
  have hlowerHolder : HolderWith
      (parabolicLowerOrderHolderConst Kb Bb Kc Kdu Ku Mdu Bc Mu) alpha
      (Qlocal.restrict
        (parabolicLowerOrderTerm b c (fun t x ↦ u t x))) :=
    parabolicLowerOrderTerm_holderWith_restrict
      b c (fun t x ↦ u t x) Kb Bb Mdu Bc Mu hb hc hjetHolder
        huHolderLocal hbNorm hcNorm hjetNorm huNormLocal
  have hlowerNorm : ∀ p, p ∈ Qlocal →
      ‖parabolicLowerOrderTerm b c (fun t x ↦ u t x) p‖ ≤
        parabolicLowerOrderSupConst Bb Bc Mdu Mu := by
    intro p hp
    exact norm_parabolicLowerOrderTerm_le b c (fun t x ↦ u t x)
      Bb Bc Mdu Mu hbNorm hcNorm hjetNorm huNormLocal p hp
  exact
    parabolic_variable_coefficient_ball_interior_schauder_estimate_of_local_lower_order_source_estimates_of_small_freeze_defect
      halpha0 halpha1 haTime hat₀ ht₀t₁ ht₁b hbT hTS center hr hrR
      a p0 hA b c u dtimeU du d2u huTime hu hdu huCont
      hsourceHolder (by simpa only [Qlocal] using hlowerHolder) hsourceNorm
      (by simpa only [Qlocal] using hlowerNorm) A Ka omega ha homega haNorm
      huHolder hdtimeUHolder hduHolder hd2uHolder huNorm hdtimeUNorm
      hduNorm hd2uNorm hsmall

def parabolicNondivergenceBufferedBallInteriorGaugeFactor
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (alpha : NNReal) (aTime t₀ t₁ bTime : Real) (center : Euc n)
    {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (Kb Bb : n → NNReal) (Kc Bc epsilon delta : NNReal)
    (A Ka omega : n → n → NNReal) (T : Real) : NNReal :=
  parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst
    a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
    (bufferedParabolicLowerOrderInterpolationHolderConst
      Kb Bb Kc Bc epsilon delta alpha 1 0)
    (bufferedParabolicSpatialGradientInterpolationConst
      epsilon delta alpha 1 0)
    (parabolicValueInterpolationConst epsilon alpha 1 0)
    (bufferedParabolicLowerOrderInterpolationSupConst Bb Bc epsilon 1 0)
    epsilon 0 A Ka omega T

def parabolicNondivergenceBufferedBallInteriorRpowGaugeFactor
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (alpha : NNReal) (aTime t₀ t₁ bTime : Real) (center : Euc n)
    {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (Kb Bb : n → NNReal) (Kc Bc delta : NNReal)
    (A Ka omega : n → n → NNReal) (T : Real) : NNReal :=
  parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst
    a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
    (parabolicLowerOrderHolderConst Kb Bb Kc
      (bufferedParabolicSpatialGradientConst 1 delta + 2) 2 0 Bc 0)
    (bufferedParabolicSpatialGradientConst 1 delta + 2) 2 0 0 0
    A Ka omega T

def parabolicNondivergenceBufferedBallInteriorLinearGaugeFactor
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (alpha : NNReal) (aTime t₀ t₁ bTime : Real) (center : Euc n)
    {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (Kb Bb : n → NNReal) (Kc Bc : NNReal)
    (A Ka omega : n → n → NNReal) (T : Real) : NNReal :=
  parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst
    a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
    (parabolicLowerOrderHolderConst Kb Bb Kc 0 0 1 Bc 0)
    0 0 (parabolicLowerOrderSupConst Bb Bc 1 0) 1 0 A Ka omega T

def parabolicNondivergenceBufferedBallInteriorDataConst
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (alpha : NNReal) (aTime t₀ t₁ bTime : Real) (center : Euc n)
    {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (Ksource : NNReal) (Kb Bb : n → NNReal)
    (Kc Bc epsilon delta Bsource M : NNReal)
    (A Ka omega : n → n → NNReal) (T : Real) : NNReal :=
  parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst
    a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
    (Ksource + bufferedParabolicLowerOrderInterpolationHolderConst
      Kb Bb Kc Bc epsilon delta alpha 0 M)
    (bufferedParabolicSpatialGradientInterpolationConst
      epsilon delta alpha 0 M)
    (parabolicValueInterpolationConst epsilon alpha 0 M)
    (Bsource + bufferedParabolicLowerOrderInterpolationSupConst
      Bb Bc epsilon 0 M)
    (2 * M / epsilon) M A Ka omega T

omit [Nonempty n] in
theorem parabolicNondivergenceBufferedBallInteriorConst_eq_data_add_gauge
    {alpha : NNReal} (halpha1 : alpha < 1)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (aTime t₀ t₁ bTime : Real) (center : Euc n)
    {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (Ksource : NNReal) (Kb Bb : n → NNReal)
    (Kc Bc epsilon delta Bsource C M : NNReal)
    (A Ka omega : n → n → NNReal) {T : Real} (hT : 0 ≤ T) :
    parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst
        a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
        (Ksource + bufferedParabolicLowerOrderInterpolationHolderConst
          Kb Bb Kc Bc epsilon delta alpha C M)
        (bufferedParabolicSpatialGradientInterpolationConst
          epsilon delta alpha C M)
        (parabolicValueInterpolationConst epsilon alpha C M)
        (Bsource + bufferedParabolicLowerOrderInterpolationSupConst
          Bb Bc epsilon C M)
        (2 * M / epsilon + C * epsilon) M A Ka omega T =
      parabolicNondivergenceBufferedBallInteriorDataConst
          a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
          Ksource Kb Bb Kc Bc epsilon delta Bsource M A Ka omega T +
        C * parabolicNondivergenceBufferedBallInteriorGaugeFactor
          a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
          Kb Bb Kc Bc epsilon delta A Ka omega T := by
  have hlo : bufferedParabolicLowerOrderInterpolationHolderConst
      Kb Bb Kc Bc epsilon delta alpha C M =
    bufferedParabolicLowerOrderInterpolationHolderConst
        Kb Bb Kc Bc epsilon delta alpha 0 M +
      C * bufferedParabolicLowerOrderInterpolationHolderConst
        Kb Bb Kc Bc epsilon delta alpha 1 0 := by
    calc
      _ = bufferedParabolicLowerOrderInterpolationHolderConst
          Kb Bb Kc Bc epsilon delta alpha (0 + C * 1) (M + C * 0) := by simp
      _ = bufferedParabolicLowerOrderInterpolationHolderConst
            Kb Bb Kc Bc epsilon delta alpha 0 M +
          bufferedParabolicLowerOrderInterpolationHolderConst
            Kb Bb Kc Bc epsilon delta alpha (C * 1) (C * 0) :=
        bufferedParabolicLowerOrderInterpolationHolderConst_add
          Kb Bb Kc Bc epsilon delta alpha 0 (C * 1) M (C * 0)
      _ = _ := by
        rw [bufferedParabolicLowerOrderInterpolationHolderConst_nnreal_mul]
  have hdu : bufferedParabolicSpatialGradientInterpolationConst
      epsilon delta alpha C M =
    bufferedParabolicSpatialGradientInterpolationConst
        epsilon delta alpha 0 M +
      C * bufferedParabolicSpatialGradientInterpolationConst
        epsilon delta alpha 1 0 := by
    calc
      _ = bufferedParabolicSpatialGradientInterpolationConst
          epsilon delta alpha (0 + C * 1) (M + C * 0) := by simp
      _ = bufferedParabolicSpatialGradientInterpolationConst
            epsilon delta alpha 0 M +
          bufferedParabolicSpatialGradientInterpolationConst
            epsilon delta alpha (C * 1) (C * 0) :=
        bufferedParabolicSpatialGradientInterpolationConst_add
          epsilon delta alpha 0 (C * 1) M (C * 0)
      _ = _ := by
        rw [bufferedParabolicSpatialGradientInterpolationConst_nnreal_mul]
  have hu : parabolicValueInterpolationConst epsilon alpha C M =
    parabolicValueInterpolationConst epsilon alpha 0 M +
      C * parabolicValueInterpolationConst epsilon alpha 1 0 := by
    calc
      _ = parabolicValueInterpolationConst epsilon alpha
          (0 + C * 1) (M + C * 0) := by simp
      _ = parabolicValueInterpolationConst epsilon alpha 0 M +
          parabolicValueInterpolationConst epsilon alpha (C * 1) (C * 0) :=
        parabolicValueInterpolationConst_add epsilon alpha 0 (C * 1) M (C * 0)
      _ = _ := by rw [parabolicValueInterpolationConst_nnreal_mul]
  have hlosup : bufferedParabolicLowerOrderInterpolationSupConst
      Bb Bc epsilon C M =
    bufferedParabolicLowerOrderInterpolationSupConst Bb Bc epsilon 0 M +
      C * bufferedParabolicLowerOrderInterpolationSupConst
        Bb Bc epsilon 1 0 := by
    calc
      _ = bufferedParabolicLowerOrderInterpolationSupConst Bb Bc epsilon
          (0 + C * 1) (M + C * 0) := by simp
      _ = bufferedParabolicLowerOrderInterpolationSupConst
            Bb Bc epsilon 0 M +
          bufferedParabolicLowerOrderInterpolationSupConst
            Bb Bc epsilon (C * 1) (C * 0) :=
        bufferedParabolicLowerOrderInterpolationSupConst_add
          Bb Bc epsilon 0 (C * 1) M (C * 0)
      _ = _ := by
        rw [bufferedParabolicLowerOrderInterpolationSupConst_nnreal_mul]
  have hsourceSplit : Ksource +
      bufferedParabolicLowerOrderInterpolationHolderConst
        Kb Bb Kc Bc epsilon delta alpha C M =
    (Ksource + bufferedParabolicLowerOrderInterpolationHolderConst
      Kb Bb Kc Bc epsilon delta alpha 0 M) +
      C * bufferedParabolicLowerOrderInterpolationHolderConst
        Kb Bb Kc Bc epsilon delta alpha 1 0 := by rw [hlo]; ring
  have hsupSplit : Bsource +
      bufferedParabolicLowerOrderInterpolationSupConst Bb Bc epsilon C M =
    (Bsource + bufferedParabolicLowerOrderInterpolationSupConst
      Bb Bc epsilon 0 M) +
      C * bufferedParabolicLowerOrderInterpolationSupConst
        Bb Bc epsilon 1 0 := by rw [hlosup]; ring
  calc
    _ = parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst
        a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
        ((Ksource + bufferedParabolicLowerOrderInterpolationHolderConst
            Kb Bb Kc Bc epsilon delta alpha 0 M) +
          C * bufferedParabolicLowerOrderInterpolationHolderConst
            Kb Bb Kc Bc epsilon delta alpha 1 0)
        (bufferedParabolicSpatialGradientInterpolationConst
            epsilon delta alpha 0 M +
          C * bufferedParabolicSpatialGradientInterpolationConst
            epsilon delta alpha 1 0)
        (parabolicValueInterpolationConst epsilon alpha 0 M +
          C * parabolicValueInterpolationConst epsilon alpha 1 0)
        ((Bsource + bufferedParabolicLowerOrderInterpolationSupConst
            Bb Bc epsilon 0 M) +
          C * bufferedParabolicLowerOrderInterpolationSupConst
            Bb Bc epsilon 1 0)
        ((2 * M / epsilon) + C * epsilon) (M + C * 0)
        A Ka omega T := by rw [hsourceSplit, hdu, hu, hsupSplit]; simp
    _ = parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst
          a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
          (Ksource + bufferedParabolicLowerOrderInterpolationHolderConst
            Kb Bb Kc Bc epsilon delta alpha 0 M)
          (bufferedParabolicSpatialGradientInterpolationConst
            epsilon delta alpha 0 M)
          (parabolicValueInterpolationConst epsilon alpha 0 M)
          (Bsource + bufferedParabolicLowerOrderInterpolationSupConst
            Bb Bc epsilon 0 M)
          (2 * M / epsilon) M A Ka omega T +
        parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst
          a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
          (C * bufferedParabolicLowerOrderInterpolationHolderConst
            Kb Bb Kc Bc epsilon delta alpha 1 0)
          (C * bufferedParabolicSpatialGradientInterpolationConst
            epsilon delta alpha 1 0)
          (C * parabolicValueInterpolationConst epsilon alpha 1 0)
          (C * bufferedParabolicLowerOrderInterpolationSupConst
            Bb Bc epsilon 1 0)
          (C * epsilon) (C * 0) A Ka omega T := by
      exact parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst_add
        halpha1 a p0 hA aTime t₀ t₁ bTime center hr hrR
        (Ksource + bufferedParabolicLowerOrderInterpolationHolderConst
          Kb Bb Kc Bc epsilon delta alpha 0 M)
        (C * bufferedParabolicLowerOrderInterpolationHolderConst
          Kb Bb Kc Bc epsilon delta alpha 1 0)
        (bufferedParabolicSpatialGradientInterpolationConst
          epsilon delta alpha 0 M)
        (C * bufferedParabolicSpatialGradientInterpolationConst
          epsilon delta alpha 1 0)
        (parabolicValueInterpolationConst epsilon alpha 0 M)
        (C * parabolicValueInterpolationConst epsilon alpha 1 0)
        (Bsource + bufferedParabolicLowerOrderInterpolationSupConst
          Bb Bc epsilon 0 M)
        (C * bufferedParabolicLowerOrderInterpolationSupConst
          Bb Bc epsilon 1 0)
        (2 * M / epsilon) (C * epsilon) M (C * 0) A Ka omega hT
    _ = _ := by
      rw [parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst_nnreal_mul]
      rfl

omit [Nonempty n] in
theorem parabolicNondivergenceBufferedBallInteriorGaugeFactor_eq_rpow_add_linear
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (alpha : NNReal) (aTime t₀ t₁ bTime : Real) (center : Euc n)
    {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (Kb Bb : n → NNReal) (Kc Bc epsilon delta : NNReal)
    (halpha1 : alpha < 1) (hepsilon : 0 < epsilon)
    (A Ka omega : n → n → NNReal) {T : Real} (hT : 0 ≤ T) :
    parabolicNondivergenceBufferedBallInteriorGaugeFactor
        a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
        Kb Bb Kc Bc epsilon delta A Ka omega T =
      epsilon ^ ((1 : NNReal) - alpha : Real) *
          parabolicNondivergenceBufferedBallInteriorRpowGaugeFactor
            a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
            Kb Bb Kc Bc delta A Ka omega T +
        epsilon * parabolicNondivergenceBufferedBallInteriorLinearGaugeFactor
          a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
          Kb Bb Kc Bc A Ka omega T := by
  let q := epsilon ^ ((1 : NNReal) - alpha : Real)
  let G := bufferedParabolicSpatialGradientConst 1 delta + 2
  have hdu : bufferedParabolicSpatialGradientInterpolationConst
      epsilon delta alpha 1 0 = q * G := by
    unfold bufferedParabolicSpatialGradientInterpolationConst
    simp only [mul_zero, zero_div, zero_add, one_mul]
    rw [show 2 * epsilon / epsilon ^ (alpha : Real) = 2 * q by
      calc
        _ = 2 * (epsilon / epsilon ^ (alpha : Real)) := by ring
        _ = _ := by rw [show epsilon / epsilon ^ (alpha : Real) = q by
          dsimp only [q]
          simpa only [NNReal.rpow_one] using
            (NNReal.rpow_sub hepsilon.ne' 1 (alpha : Real)).symm]]
    dsimp only [G, q]
    ring
  have hu : parabolicValueInterpolationConst epsilon alpha 1 0 = q * 2 := by
    unfold parabolicValueInterpolationConst
    dsimp only [q]
    simp
    ring
  have hlo : bufferedParabolicLowerOrderInterpolationHolderConst
      Kb Bb Kc Bc epsilon delta alpha 1 0 =
    q * parabolicLowerOrderHolderConst Kb Bb Kc G 2 0 Bc 0 +
      epsilon * parabolicLowerOrderHolderConst Kb Bb Kc 0 0 1 Bc 0 := by
    unfold bufferedParabolicLowerOrderInterpolationHolderConst
    rw [hdu, hu]
    simp only [mul_zero, zero_div, zero_add, one_mul]
    calc
      _ = parabolicLowerOrderHolderConst Kb Bb Kc
          (q * G + epsilon * 0) (q * 2 + epsilon * 0)
          (q * 0 + epsilon * 1) Bc (q * 0 + epsilon * 0) := by simp
      _ = parabolicLowerOrderHolderConst Kb Bb Kc
            (q * G) (q * 2) (q * 0) Bc (q * 0) +
          parabolicLowerOrderHolderConst Kb Bb Kc
            (epsilon * 0) (epsilon * 0) (epsilon * 1) Bc
              (epsilon * 0) :=
        parabolicLowerOrderHolderConst_add Kb Bb Kc Bc
          (q * G) (epsilon * 0) (q * 2) (epsilon * 0)
          (q * 0) (epsilon * 1) (q * 0) (epsilon * 0)
      _ = _ := by
        rw [parabolicLowerOrderHolderConst_nnreal_mul,
          parabolicLowerOrderHolderConst_nnreal_mul]
  have hsup : bufferedParabolicLowerOrderInterpolationSupConst
      Bb Bc epsilon 1 0 = epsilon * parabolicLowerOrderSupConst Bb Bc 1 0 := by
    unfold bufferedParabolicLowerOrderInterpolationSupConst
    simp only [mul_zero, zero_div, zero_add, one_mul]
    simpa using parabolicLowerOrderSupConst_nnreal_mul epsilon Bb Bc 1 0
  unfold parabolicNondivergenceBufferedBallInteriorGaugeFactor
  rw [hlo, hdu, hu, hsup]
  calc
    _ = parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst
        a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
        (q * parabolicLowerOrderHolderConst Kb Bb Kc G 2 0 Bc 0 +
          epsilon * parabolicLowerOrderHolderConst Kb Bb Kc 0 0 1 Bc 0)
        (q * G + epsilon * 0) (q * 2 + epsilon * 0)
        (q * 0 + epsilon * parabolicLowerOrderSupConst Bb Bc 1 0)
        (q * 0 + epsilon * 1) (q * 0 + epsilon * 0) A Ka omega T := by simp
    _ = parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst
          a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
          (q * parabolicLowerOrderHolderConst Kb Bb Kc G 2 0 Bc 0)
          (q * G) (q * 2) (q * 0) (q * 0) (q * 0) A Ka omega T +
        parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst
          a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
          (epsilon * parabolicLowerOrderHolderConst Kb Bb Kc 0 0 1 Bc 0)
          (epsilon * 0) (epsilon * 0)
          (epsilon * parabolicLowerOrderSupConst Bb Bc 1 0)
          (epsilon * 1) (epsilon * 0) A Ka omega T := by
      exact parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst_add
        halpha1 a p0 hA aTime t₀ t₁ bTime center hr hrR
        (q * parabolicLowerOrderHolderConst Kb Bb Kc G 2 0 Bc 0)
        (epsilon * parabolicLowerOrderHolderConst Kb Bb Kc 0 0 1 Bc 0)
        (q * G) (epsilon * 0) (q * 2) (epsilon * 0)
        (q * 0) (epsilon * parabolicLowerOrderSupConst Bb Bc 1 0)
        (q * 0) (epsilon * 1) (q * 0) (epsilon * 0) A Ka omega hT
    _ = _ := by
      rw [parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst_nnreal_mul,
        parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst_nnreal_mul]
      rfl

omit [Nonempty n] in
theorem tendsto_parabolicNondivergenceBufferedBallInteriorGaugeFactor_nhdsWithin_zero
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (alpha : NNReal) (halpha1 : alpha < 1)
    (aTime t₀ t₁ bTime : Real) (center : Euc n)
    {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (Kb Bb : n → NNReal) (Kc Bc delta : NNReal)
    (A Ka omega : n → n → NNReal) {T : Real} (hT : 0 ≤ T) :
    Tendsto (fun epsilon : NNReal ↦
      parabolicNondivergenceBufferedBallInteriorGaugeFactor
        a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
        Kb Bb Kc Bc epsilon delta A Ka omega T)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have halphaReal : (alpha : Real) < 1 := by exact_mod_cast halpha1
  have hbeta : 0 < (1 : Real) - alpha := by linarith
  have hq : Tendsto (fun epsilon : NNReal ↦
      epsilon ^ ((1 : NNReal) - alpha : Real)) (nhds 0) (nhds 0) := by
    simpa only [NNReal.zero_rpow hbeta.ne'] using
      (NNReal.continuousAt_rpow_const (x := (0 : NNReal))
        (y := (1 : Real) - alpha) (Or.inr hbeta.le)).tendsto
  have hmodel : Tendsto (fun epsilon : NNReal ↦
      epsilon ^ ((1 : NNReal) - alpha : Real) *
          parabolicNondivergenceBufferedBallInteriorRpowGaugeFactor
            a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
            Kb Bb Kc Bc delta A Ka omega T +
        epsilon * parabolicNondivergenceBufferedBallInteriorLinearGaugeFactor
          a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
          Kb Bb Kc Bc A Ka omega T)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using ((hq.mono_left inf_le_left).mul_const _).add
      ((tendsto_id.mono_left inf_le_left).mul_const _)
  apply hmodel.congr'
  filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
  exact
    (parabolicNondivergenceBufferedBallInteriorGaugeFactor_eq_rpow_add_linear
      a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
      Kb Bb Kc Bc epsilon delta halpha1 hepsilon A Ka omega hT).symm

omit [Nonempty n] in
theorem exists_parabolicNondivergenceBufferedBallInteriorGaugeFactor_lt
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (alpha : NNReal) (halpha1 : alpha < 1)
    (aTime t₀ t₁ bTime : Real) (center : Euc n)
    {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (Kb Bb : n → NNReal) (Kc Bc delta : NNReal) (hdelta : 0 < delta)
    (A Ka omega : n → n → NNReal) {T : Real} (hT : 0 ≤ T)
    (theta : NNReal) (htheta : 0 < theta) :
    ∃ epsilon : NNReal, 0 < epsilon ∧ epsilon < delta ∧
      parabolicNondivergenceBufferedBallInteriorGaugeFactor
        a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
        Kb Bb Kc Bc epsilon delta A Ka omega T < theta := by
  have ht :=
    tendsto_parabolicNondivergenceBufferedBallInteriorGaugeFactor_nhdsWithin_zero
      a p0 hA alpha halpha1 aTime t₀ t₁ bTime center hr hrR
      Kb Bb Kc Bc delta A Ka omega hT
  have hsmall := ht.eventually (Iio_mem_nhds htheta)
  have hlt : ∀ᶠ epsilon : NNReal in nhdsWithin 0 (Ioi 0), epsilon < delta :=
    (tendsto_id.mono_left inf_le_left).eventually (Iio_mem_nhds hdelta)
  have hpos : ∀ᶠ epsilon : NNReal in nhdsWithin 0 (Ioi 0),
      epsilon ∈ Ioi (0 : NNReal) := self_mem_nhdsWithin
  obtain ⟨epsilon, hepsilon, hepsdelta, hfactor⟩ :=
    (hpos.and (hlt.and hsmall)).exists
  exact ⟨epsilon, hepsilon, hepsdelta, hfactor⟩

omit [Nonempty n] in
theorem exists_parabolicNondivergenceBufferedBallInteriorGaugeFactor_mul_lt_one
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (alpha : NNReal) (halpha1 : alpha < 1)
    (aTime t₀ t₁ bTime : Real) (center : Euc n)
    {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (Kb Bb : n → NNReal) (Kc Bc delta : NNReal) (hdelta : 0 < delta)
    (A Ka omega : n → n → NNReal) {T : Real} (hT : 0 ≤ T)
    (B : NNReal) (hB : 0 < B) :
    ∃ epsilon : NNReal, 0 < epsilon ∧ epsilon < delta ∧
      parabolicNondivergenceBufferedBallInteriorGaugeFactor
          a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
          Kb Bb Kc Bc epsilon delta A Ka omega T * B < 1 := by
  obtain ⟨epsilon, hepsilon, hepsdelta, hfactor⟩ :=
    exists_parabolicNondivergenceBufferedBallInteriorGaugeFactor_lt
      a p0 hA alpha halpha1 aTime t₀ t₁ bTime center hr hrR
      Kb Bb Kc Bc delta hdelta A Ka omega hT B⁻¹ (inv_pos.mpr hB)
  refine ⟨epsilon, hepsilon, hepsdelta, ?_⟩
  calc
    parabolicNondivergenceBufferedBallInteriorGaugeFactor
          a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
          Kb Bb Kc Bc epsilon delta A Ka omega T * B < B⁻¹ * B :=
      mul_lt_mul_of_pos_right hfactor hB
    _ = 1 := inv_mul_cancel₀ hB.ne'

theorem parabolic_nondivergence_ball_interior_schauder_estimate_of_buffered_interpolation_of_local_source_estimates_of_small_freeze_defect
    {alpha Ksource Kc Bsource Bc C M : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (epsilon delta : NNReal) (hepsilon : 0 < epsilon)
    (hepsilonDelta : epsilon < delta)
    {aTime t₀ t₁ bTime S T : Real}
    (haTime : 0 < aTime) (hat₀ : aTime < t₀) (ht₀t₁ : t₀ ≤ t₁)
    (ht₁b : t₁ < bTime) (hbT : bTime < T) (hTS : T < S)
    (center : Euc n) {r R Rout : Real}
    (hr : 0 ≤ r) (hrR : r < R) (hbuffer : R + delta ≤ Rout)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (b : n → ParabolicPoint (Euc n) → Real)
    (c : ParabolicPoint (Euc n) → Real)
    (u dtimeU : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (huTime : ∀ s ∈ Icc (0 : Real) S, HasDerivAt u (dtimeU s) s)
    (hu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (u s : Euc n → F) (du s x) x)
    (hdu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (du s : Euc n → Euc n →L[Real] F) (d2u s x) x)
    (huCont : Continuous u)
    (hsourceHolder : HolderWith Ksource alpha
      ((parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R)).restrict
        (parabolicNondivergenceOperator a b c (fun t x ↦ u t x))))
    (hsourceNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R) →
        ‖parabolicNondivergenceOperator a b c (fun t x ↦ u t x) p‖ ≤
          Bsource)
    (Kb Bb : n → NNReal) (A Ka omega : n → n → NNReal)
    (hb : ∀ i, HolderWith (Kb i) alpha
      ((parabolicCylinder (Icc (0 : Real) S)
        (Metric.closedBall center R)).restrict (b i)))
    (hc : HolderWith Kc alpha
      ((parabolicCylinder (Icc (0 : Real) S)
        (Metric.closedBall center R)).restrict c))
    (hbNorm : ∀ i p,
      p ∈ parabolicCylinder (Icc (0 : Real) S)
        (Metric.closedBall center R) → ‖b i p‖ ≤ Bb i)
    (hcNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S)
        (Metric.closedBall center R) → ‖c p‖ ≤ Bc)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict (a i j)))
    (homega : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p0 - a i j p‖ ≤ omega i j)
    (haNorm : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p‖ ≤ A i j)
    (hgauge : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Icc (0 : Real) S) (Metric.ball center Rout))
      (fun t x ↦ u t x) ≤ C)
    (huNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) (Metric.ball center Rout) →
        ‖u p.time p.space‖ ≤ M)
    (hsmall : spdParabolicSchauderDefectConst
      (fun i j ↦ a i j p0) hA alpha Ka omega T < 1) :
    eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Ioo t₀ t₁) (Metric.ball center r))
        (fun t x ↦ u t x) ≤
      parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst
        a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
        (Ksource + bufferedParabolicLowerOrderInterpolationHolderConst
          Kb Bb Kc Bc epsilon delta alpha C M)
        (bufferedParabolicSpatialGradientInterpolationConst
          epsilon delta alpha C M)
        (parabolicValueInterpolationConst epsilon alpha C M)
        (Bsource + bufferedParabolicLowerOrderInterpolationSupConst
          Bb Bc epsilon C M)
        (2 * M / epsilon + C * epsilon) M A Ka omega T := by
  let J := Icc (0 : Real) S
  let Qout := parabolicCylinder J (Metric.ball center Rout)
  let Q := parabolicCylinder J (Metric.ball center R)
  let Qclosed := parabolicCylinder J (Metric.closedBall center R)
  have hQQclosed : Q ⊆ Qclosed := by
    intro p hp
    exact ⟨hp.1, Metric.ball_subset_closedBall hp.2⟩
  have huC2 : IsParabolicC2On Qout (fun t x ↦ u t x) := by
    constructor
    · intro p hp
      exact (contDiff_two_of_hasFDerivAt (u p.time) (du p.time) (d2u p.time)
        (hu p.time hp.1) (hdu p.time hp.1)).contDiffAt
    · intro p hp
      exact ((BoundedContinuousFunction.evalCLM Real p.space).hasFDerivAt
        |>.comp_hasDerivAt p.time (huTime p.time hp.1)).differentiableAt
  have hlowerHolderClosed : HolderWith
      (bufferedParabolicLowerOrderInterpolationHolderConst
        Kb Bb Kc Bc epsilon delta alpha C M) alpha
      (Qclosed.restrict
        (parabolicLowerOrderTerm b c (fun t x ↦ u t x))) := by
    exact parabolicLowerOrderTerm_holderWith_restrict_of_buffered_ball_interpolation
      (convex_Icc (0 : Real) S) center epsilon delta hepsilon
      hepsilonDelta hbuffer halpha1.le b c (fun t x ↦ u t x)
      Kb Bb Kc Bc huC2 (by simpa only [Qout, J] using hgauge)
      (by simpa only [Qout, J] using huNorm)
      (by simpa only [Qclosed, J] using hb)
      (by simpa only [Qclosed, J] using hc)
      (by simpa only [Qclosed, J] using hbNorm)
      (by simpa only [Qclosed, J] using hcNorm)
  have hlowerHolder : HolderWith
      (bufferedParabolicLowerOrderInterpolationHolderConst
        Kb Bb Kc Bc epsilon delta alpha C M) alpha
      (Q.restrict
        (parabolicLowerOrderTerm b c (fun t x ↦ u t x))) :=
    ((HolderWith.restrict_iff.mp hlowerHolderClosed).mono hQQclosed).holderWith
  have hlowerNorm : ∀ p, p ∈ Q →
      ‖parabolicLowerOrderTerm b c (fun t x ↦ u t x) p‖ ≤
        bufferedParabolicLowerOrderInterpolationSupConst
          Bb Bc epsilon C M := by
    intro p hp
    exact norm_parabolicLowerOrderTerm_le_of_buffered_ball_interpolation
      center epsilon hepsilon (by
        calc
          R + (epsilon : Real) < R + (delta : Real) := by gcongr
          _ ≤ Rout := hbuffer)
      b c (fun t x ↦ u t x) Bb Bc huC2
      (by simpa only [Qout, J] using hgauge)
      (by simpa only [Qout, J] using huNorm)
      (by simpa only [Qclosed, J] using hbNorm)
      (by simpa only [Qclosed, J] using hcNorm) p (hQQclosed hp)
  have hmatrixHolder : HolderWith
      (Ksource + bufferedParabolicLowerOrderInterpolationHolderConst
        Kb Bb Kc Bc epsilon delta alpha C M) alpha
      (Q.restrict
        (parabolicVariableMatrixOperator a (fun t x ↦ u t x))) := by
    rw [parabolicVariableMatrixOperator_eq_nondivergenceOperator_add_lowerOrderTerm
      a b c (fun t x ↦ u t x)]
    have hsourceHolderQ : HolderWith Ksource alpha
        (Q.restrict
          (parabolicNondivergenceOperator a b c (fun t x ↦ u t x))) := by
      simpa only [Q, J] using hsourceHolder
    exact hsourceHolderQ.add hlowerHolder
  have hmatrixNorm : ∀ p, p ∈ Q →
      ‖parabolicVariableMatrixOperator a (fun t x ↦ u t x) p‖ ≤
        Bsource + bufferedParabolicLowerOrderInterpolationSupConst
          Bb Bc epsilon C M := by
    intro p hp
    rw [parabolicVariableMatrixOperator_eq_nondivergenceOperator_add_lowerOrderTerm
      a b c (fun t x ↦ u t x)]
    exact (norm_add_le _ _).trans
      (add_le_add (hsourceNorm p (by simpa only [Q, J] using hp))
        (hlowerNorm p hp))
  simpa only [Q, J] using
    (parabolic_variable_coefficient_ball_interior_schauder_estimate_of_buffered_interpolation_of_local_source_estimates_of_small_freeze_defect
      (alpha := alpha)
      (Ksource := Ksource +
        bufferedParabolicLowerOrderInterpolationHolderConst
          Kb Bb Kc Bc epsilon delta alpha C M)
      (Bsource := Bsource +
        bufferedParabolicLowerOrderInterpolationSupConst
          Bb Bc epsilon C M)
      (C := C) (M := M) halpha0 halpha1 epsilon delta hepsilon
      hepsilonDelta haTime hat₀ ht₀t₁ ht₁b hbT hTS center hr hrR hbuffer
      a p0 hA u dtimeU du d2u huTime hu hdu huCont hmatrixHolder
      hmatrixNorm A Ka omega ha homega haNorm hgauge huNorm hsmall)

theorem parabolic_nondivergence_ball_interior_schauder_estimate_le_data_add_gauge_of_buffered_interpolation_of_local_source_estimates_of_small_freeze_defect
    {alpha Ksource Kc Bsource Bc C M : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (epsilon delta : NNReal) (hepsilon : 0 < epsilon)
    (hepsilonDelta : epsilon < delta)
    {aTime t₀ t₁ bTime S T : Real}
    (haTime : 0 < aTime) (hat₀ : aTime < t₀) (ht₀t₁ : t₀ ≤ t₁)
    (ht₁b : t₁ < bTime) (hbT : bTime < T) (hTS : T < S)
    (center : Euc n) {r R Rout : Real}
    (hr : 0 ≤ r) (hrR : r < R) (hbuffer : R + delta ≤ Rout)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (b : n → ParabolicPoint (Euc n) → Real)
    (c : ParabolicPoint (Euc n) → Real)
    (u dtimeU : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (huTime : ∀ s ∈ Icc (0 : Real) S, HasDerivAt u (dtimeU s) s)
    (hu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (u s : Euc n → F) (du s x) x)
    (hdu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (du s : Euc n → Euc n →L[Real] F) (d2u s x) x)
    (huCont : Continuous u)
    (hsourceHolder : HolderWith Ksource alpha
      ((parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R)).restrict
        (parabolicNondivergenceOperator a b c (fun t x ↦ u t x))))
    (hsourceNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R) →
        ‖parabolicNondivergenceOperator a b c (fun t x ↦ u t x) p‖ ≤
          Bsource)
    (Kb Bb : n → NNReal) (A Ka omega : n → n → NNReal)
    (hb : ∀ i, HolderWith (Kb i) alpha
      ((parabolicCylinder (Icc (0 : Real) S)
        (Metric.closedBall center R)).restrict (b i)))
    (hc : HolderWith Kc alpha
      ((parabolicCylinder (Icc (0 : Real) S)
        (Metric.closedBall center R)).restrict c))
    (hbNorm : ∀ i p,
      p ∈ parabolicCylinder (Icc (0 : Real) S)
        (Metric.closedBall center R) → ‖b i p‖ ≤ Bb i)
    (hcNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S)
        (Metric.closedBall center R) → ‖c p‖ ≤ Bc)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict (a i j)))
    (homega : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p0 - a i j p‖ ≤ omega i j)
    (haNorm : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p‖ ≤ A i j)
    (hgauge : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Icc (0 : Real) S) (Metric.ball center Rout))
      (fun t x ↦ u t x) ≤ C)
    (huNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) (Metric.ball center Rout) →
        ‖u p.time p.space‖ ≤ M)
    (hsmall : spdParabolicSchauderDefectConst
      (fun i j ↦ a i j p0) hA alpha Ka omega T < 1) :
    eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Ioo t₀ t₁) (Metric.ball center r))
        (fun t x ↦ u t x) ≤
      parabolicNondivergenceBufferedBallInteriorDataConst
          a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
          Ksource Kb Bb Kc Bc epsilon delta Bsource M A Ka omega T +
        C * parabolicNondivergenceBufferedBallInteriorGaugeFactor
          a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
          Kb Bb Kc Bc epsilon delta A Ka omega T := by
  have hT : 0 ≤ T := by linarith
  have heq :=
    parabolicNondivergenceBufferedBallInteriorConst_eq_data_add_gauge
      halpha1 a p0 hA aTime t₀ t₁ bTime center hr hrR Ksource Kb Bb
      Kc Bc epsilon delta Bsource C M A Ka omega hT
  calc
    eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Ioo t₀ t₁) (Metric.ball center r))
        (fun t x ↦ u t x) ≤
      parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst
        a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
        (Ksource + bufferedParabolicLowerOrderInterpolationHolderConst
          Kb Bb Kc Bc epsilon delta alpha C M)
        (bufferedParabolicSpatialGradientInterpolationConst
          epsilon delta alpha C M)
        (parabolicValueInterpolationConst epsilon alpha C M)
        (Bsource + bufferedParabolicLowerOrderInterpolationSupConst
          Bb Bc epsilon C M)
        (2 * M / epsilon + C * epsilon) M A Ka omega T :=
      parabolic_nondivergence_ball_interior_schauder_estimate_of_buffered_interpolation_of_local_source_estimates_of_small_freeze_defect
        halpha0 halpha1 epsilon delta hepsilon hepsilonDelta haTime hat₀
        ht₀t₁ ht₁b hbT hTS center hr hrR hbuffer a p0 hA b c u dtimeU
        du d2u huTime hu hdu huCont hsourceHolder hsourceNorm Kb Bb A Ka
        omega hb hc hbNorm hcNorm ha homega haNorm hgauge huNorm hsmall
    _ = (parabolicNondivergenceBufferedBallInteriorDataConst
          a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
          Ksource Kb Bb Kc Bc epsilon delta Bsource M A Ka omega T +
        C * parabolicNondivergenceBufferedBallInteriorGaugeFactor
          a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
          Kb Bb Kc Bc epsilon delta A Ka omega T : NNReal) := by
      exact_mod_cast heq
    _ = _ := by norm_cast

theorem parabolic_nondivergence_ball_interior_schauder_estimate_of_interpolation_of_local_source_estimates_of_small_freeze_defect
    {alpha Ksource Kc Bsource Bc C M : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (epsilon : NNReal) (hepsilon : 0 < epsilon)
    {aTime t₀ t₁ bTime S T : Real}
    (haTime : 0 < aTime) (hat₀ : aTime < t₀) (ht₀t₁ : t₀ ≤ t₁)
    (ht₁b : t₁ < bTime) (hbT : bTime < T) (hTS : T < S)
    (center : Euc n) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (b : n → ParabolicPoint (Euc n) → Real)
    (c : ParabolicPoint (Euc n) → Real)
    (u dtimeU : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (huTime : ∀ s ∈ Icc (0 : Real) S, HasDerivAt u (dtimeU s) s)
    (hu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (u s : Euc n → F) (du s x) x)
    (hdu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (du s : Euc n → Euc n →L[Real] F) (d2u s x) x)
    (huCont : Continuous u)
    (huC2 : IsParabolicC2On
      (parabolicCylinder (Icc (0 : Real) S) Set.univ)
      (fun t x ↦ u t x))
    (hgauge : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Icc (0 : Real) S) Set.univ)
      (fun t x ↦ u t x) ≤ C)
    (huNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖u p.time p.space‖ ≤ M)
    (hsourceHolder : HolderWith Ksource alpha
      ((parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R)).restrict
        (parabolicNondivergenceOperator a b c (fun t x ↦ u t x))))
    (hsourceNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R) →
        ‖parabolicNondivergenceOperator a b c (fun t x ↦ u t x) p‖ ≤
          Bsource)
    (Kb Bb : n → NNReal) (A Ka omega : n → n → NNReal)
    (hb : ∀ i, HolderWith (Kb i) alpha
      ((parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R)).restrict
        (b i)))
    (hc : HolderWith Kc alpha
      ((parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R)).restrict
        c))
    (hbNorm : ∀ i p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R) →
        ‖b i p‖ ≤ Bb i)
    (hcNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R) →
        ‖c p‖ ≤ Bc)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict (a i j)))
    (homega : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p0 - a i j p‖ ≤ omega i j)
    (haNorm : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p‖ ≤ A i j)
    (hsmall : spdParabolicSchauderDefectConst
      (fun i j ↦ a i j p0) hA alpha Ka omega T < 1) :
    eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Ioo t₀ t₁) (Metric.ball center r))
        (fun t x ↦ u t x) ≤
      parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst
        a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
        (Ksource + parabolicLowerOrderInterpolationHolderConst
          Kb Bb Kc Bc epsilon alpha C M)
        (parabolicSpatialGradientInterpolationConst epsilon alpha C M)
        (parabolicValueInterpolationConst epsilon alpha C M)
        (Bsource + parabolicLowerOrderInterpolationSupConst
          Bb Bc epsilon C M)
        (2 * M / epsilon + C * epsilon) M A Ka omega T := by
  let Q := parabolicCylinder (Icc (0 : Real) S) (Set.univ : Set (Euc n))
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
        (convex_Icc (0 : Real) S) convex_univ epsilon hepsilon
        halpha1.le huC2 hgauge huNorm
  have hjetHolder : HolderWith
      (parabolicSpatialGradientInterpolationConst epsilon alpha C M) alpha
      (Q.restrict (parabolicSpatialJet 1 (fun t x ↦ u t x))) := by
    simpa only [Q] using
      parabolicSpatialJet_one_holderWith_restrict_of_interpolation
        (convex_Icc (0 : Real) S) epsilon hepsilon halpha1.le
        huC2 hgauge huNorm
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
  simpa only [Q, parabolicLowerOrderInterpolationHolderConst,
    parabolicLowerOrderInterpolationSupConst] using
    (parabolic_nondivergence_ball_interior_schauder_estimate_of_local_source_estimates_of_small_freeze_defect
      (alpha := alpha) (Ksource := Ksource) (Kc := Kc)
      (Ku := parabolicValueInterpolationConst epsilon alpha C M)
      (KdtimeU := C)
      (Kdu := parabolicSpatialGradientInterpolationConst epsilon alpha C M)
      (Kd2u := C) (Bsource := Bsource) (Bc := Bc) (Mu := M)
      (MdtimeU := C) (Mdu := 2 * M / epsilon + C * epsilon)
      (Md2u := C) halpha0 halpha1 haTime hat₀ ht₀t₁ ht₁b hbT hTS
      center hr hrR a p0 hA b c u dtimeU du d2u huTime hu hdu huCont
      hsourceHolder hsourceNorm Kb Bb A Ka omega hb hc hbNorm hcNorm
      ha homega haNorm huHolder hdtimeUHolder hduHolder hd2uHolder
      huNorm hdtimeUNorm hduNorm hd2uNorm hsmall)

theorem parabolic_nondivergence_centered_ball_schauder_estimate_of_local_source_estimates_of_small_freeze_defect
    {alpha Ksource Kc Ku KdtimeU Kdu Kd2u Bsource Bc
      Mu MdtimeU Mdu Md2u : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {aTime t₀ t₁ bTime S T : Real}
    (haTime : 0 < aTime) (hat₀ : aTime < t₀) (ht₀t₁ : t₀ ≤ t₁)
    (ht₁b : t₁ < bTime) (hbT : bTime < T) (hTS : T < S)
    (center : Euc n) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (htimeRadius : t₁ - t₀ = 2 * r ^ 2)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (b : n → ParabolicPoint (Euc n) → Real)
    (c : ParabolicPoint (Euc n) → Real)
    (u dtimeU : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (huTime : ∀ s ∈ Icc (0 : Real) S, HasDerivAt u (dtimeU s) s)
    (hu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (u s : Euc n → F) (du s x) x)
    (hdu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (du s : Euc n → Euc n →L[Real] F) (d2u s x) x)
    (huCont : Continuous u)
    (hsourceHolder : HolderWith Ksource alpha
      ((parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R)).restrict
        (parabolicNondivergenceOperator a b c (fun t x ↦ u t x))))
    (hsourceNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R) →
        ‖parabolicNondivergenceOperator a b c (fun t x ↦ u t x) p‖ ≤
          Bsource)
    (Kb Bb : n → NNReal) (A Ka omega : n → n → NNReal)
    (hb : ∀ i, HolderWith (Kb i) alpha
      ((parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R)).restrict
        (b i)))
    (hc : HolderWith Kc alpha
      ((parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R)).restrict
        c))
    (hbNorm : ∀ i p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R) →
        ‖b i p‖ ≤ Bb i)
    (hcNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R) →
        ‖c p‖ ≤ Bc)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict (a i j)))
    (homega : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p0 - a i j p‖ ≤ omega i j)
    (haNorm : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p‖ ≤ A i j)
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
      (fun i j ↦ a i j p0) hA alpha Ka omega T < 1) :
    eParabolicC2HolderGaugeOn alpha
        (Metric.ball (parabolicPoint 0 center) r)
        (fun t x ↦ u ((t₀ + t₁) / 2 + t) x) ≤
      parabolicC2HolderRescaleConst 1 alpha
        (parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst
          a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
          (Ksource + parabolicLowerOrderHolderConst
            Kb Bb Kc Kdu Ku Mdu Bc Mu)
          Kdu Ku
          (Bsource + parabolicLowerOrderSupConst Bb Bc Mdu Mu)
          Mdu Mu A Ka omega T) := by
  apply eParabolicC2HolderGaugeOn_centered_ball_le_of_parabolicCylinder
    hr htimeRadius center alpha
    (parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst
      a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
      (Ksource + parabolicLowerOrderHolderConst
        Kb Bb Kc Kdu Ku Mdu Bc Mu)
      Kdu Ku
      (Bsource + parabolicLowerOrderSupConst Bb Bc Mdu Mu)
      Mdu Mu A Ka omega T)
    u du d2u
  · intro s hs
    exact hu s ⟨(haTime.trans (hat₀.trans hs.1)).le,
      hs.2.le.trans (ht₁b.trans (hbT.trans hTS)).le⟩
  · intro s hs
    exact hdu s ⟨(haTime.trans (hat₀.trans hs.1)).le,
      hs.2.le.trans (ht₁b.trans (hbT.trans hTS)).le⟩
  · exact
      parabolic_nondivergence_ball_interior_schauder_estimate_of_local_source_estimates_of_small_freeze_defect
        halpha0 halpha1 haTime hat₀ ht₀t₁ ht₁b hbT hTS center hr hrR
        a p0 hA b c u dtimeU du d2u huTime hu hdu huCont
        hsourceHolder hsourceNorm Kb Bb A Ka omega hb hc hbNorm hcNorm
        ha homega haNorm huHolder hdtimeUHolder hduHolder hd2uHolder
        huNorm hdtimeUNorm hduNorm hd2uNorm hsmall

end DifferentialGeometry.Analysis.Parabolic.Euclidean

end
