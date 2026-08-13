import DifferentialGeometry.Analysis.Parabolic.Euclidean.ClassicalSchauder
import DifferentialGeometry.Analysis.Parabolic.Euclidean.CutoffEstimate
import DifferentialGeometry.Analysis.Schauder.VariableCoefficient

noncomputable section

open Matrix Real Set
open scoped NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

open DifferentialGeometry.Analysis.Schauder

private abbrev Euc (n : Type*) := EuclideanSpace Real n

variable {n F : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]

def parabolicCutoffFrozenSource
    (A : Matrix n n Real)
    (chi dtimeChi : Real → BoundedContinuousFunction (Euc n) Real)
    (dchi : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] Real))
    (d2chi : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] Real))
    (u dtimeU : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F)) :
    Real → BoundedContinuousFunction (Euc n) F :=
  fun t ↦ cutoffTimeJet chi dtimeChi u dtimeU t -
    matrixLapBcf A (cutoffJet2 (chi t) (dchi t) (d2chi t)
      (u t) (du t) (d2u t))

omit [DecidableEq n] [Nonempty n] [CompleteSpace F] in
@[simp]
theorem parabolicCutoffFrozenSource_apply
    (A : Matrix n n Real)
    (chi dtimeChi : Real → BoundedContinuousFunction (Euc n) Real)
    (dchi : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] Real))
    (d2chi : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] Real))
    (u dtimeU : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (t : Real) (x : Euc n) :
    parabolicCutoffFrozenSource A chi dtimeChi dchi d2chi
        u dtimeU du d2u t x =
      cutoffTimeJet chi dtimeChi u dtimeU t x -
        matrixLap A (cutoffJet2 (chi t) (dchi t) (d2chi t)
          (u t) (du t) (d2u t) x) := by
  simp only [parabolicCutoffFrozenSource,
    BoundedContinuousFunction.sub_apply, matrixLapBcf_apply]

omit [DecidableEq n] [Nonempty n] [CompleteSpace F] in
theorem parabolicVariableMatrixOperator_cutoff_eqOn_of_bcf_jets
    {Q : Set (ParabolicPoint (Euc n))}
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (chi dtimeChi : Real → BoundedContinuousFunction (Euc n) Real)
    (dchi : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] Real))
    (d2chi : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] Real))
    (u dtimeU : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (hchiTime : ∀ p ∈ Q, HasDerivAt chi (dtimeChi p.time) p.time)
    (huTime : ∀ p ∈ Q, HasDerivAt u (dtimeU p.time) p.time)
    (hchi : ∀ p ∈ Q, ∀ x,
      HasFDerivAt (chi p.time : Euc n → Real) (dchi p.time x) x)
    (hdchi : ∀ p ∈ Q, ∀ x,
      HasFDerivAt (dchi p.time : Euc n → Euc n →L[Real] Real)
        (d2chi p.time x) x)
    (hu : ∀ p ∈ Q, ∀ x,
      HasFDerivAt (u p.time : Euc n → F) (du p.time x) x)
    (hdu : ∀ p ∈ Q, ∀ x,
      HasFDerivAt (du p.time : Euc n → Euc n →L[Real] F)
        (d2u p.time x) x) :
    Set.EqOn
      (parabolicVariableMatrixOperator a
        (fun t x ↦ cutoffValue (chi t) (u t) x))
      (fun p ↦ chi p.time p.space •
          parabolicVariableMatrixOperator a (fun t x ↦ u t x) p +
        parabolicCutoffOperatorCommutator a
          (fun p ↦ dtimeChi p.time p.space)
          (fun p ↦ dchi p.time p.space)
          (fun p ↦ d2chi p.time p.space)
          (fun t x ↦ u t x) (fun p ↦ du p.time p.space) p) Q := by
  intro p hp
  have hchiTimePoint : HasDerivAt (fun t ↦ chi t p.space)
      (dtimeChi p.time p.space) p.time := by
    simpa only [BoundedContinuousFunction.evalCLM_apply] using
      (BoundedContinuousFunction.evalCLM Real p.space).hasFDerivAt
        |>.comp_hasDerivAt p.time (hchiTime p hp)
  have huTimePoint : HasDerivAt (fun t ↦ u t p.space)
      (dtimeU p.time p.space) p.time := by
    simpa only [BoundedContinuousFunction.evalCLM_apply] using
      (BoundedContinuousFunction.evalCLM Real p.space).hasFDerivAt
        |>.comp_hasDerivAt p.time (huTime p hp)
  simpa only [parabolicCutoffValue_apply, parabolicPoint_time,
    parabolicPoint_space, parabolicPoint_time_space] using
    parabolicVariableMatrixOperator_cutoff a
      (fun q ↦ chi q.time q.space) (fun q ↦ dtimeChi q.time q.space)
      (fun q ↦ dchi q.time q.space) (fun q ↦ d2chi q.time q.space)
      (fun t x ↦ u t x) (fun q ↦ du q.time q.space)
      (fun q ↦ d2u q.time q.space) (fun q ↦ dtimeU q.time q.space)
      p (hchi p hp) (hdchi p hp) (hu p hp) (hdu p hp)
        hchiTimePoint huTimePoint

theorem parabolic_variable_coefficient_schauder_estimate_of_cutoff_classical_solution
    {alpha Kf Bf X : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {S T : Real} (hT : 0 ≤ T) (hTS : T < S)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (chi dtimeChi : Real → BoundedContinuousFunction (Euc n) Real)
    (dchi : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] Real))
    (d2chi : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] Real))
    (u dtimeU : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (hchiTime : ∀ s ∈ Icc (0 : Real) S,
      HasDerivAt chi (dtimeChi s) s)
    (huTime : ∀ s ∈ Icc (0 : Real) S,
      HasDerivAt u (dtimeU s) s)
    (hchi : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (chi s : Euc n → Real) (dchi s x) x)
    (hdchi : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (dchi s : Euc n → Euc n →L[Real] Real)
        (d2chi s x) x)
    (hu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (u s : Euc n → F) (du s x) x)
    (hdu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (du s : Euc n → Euc n →L[Real] F) (d2u s x) x)
    (hchiCont : Continuous chi) (huCont : Continuous u)
    (hchi0 : chi 0 = 0)
    (hsourceBound : eSupNormOn
      (parabolicCylinder (Icc (0 : Real) S) Set.univ)
      (parabolicVariableMatrixOperator a
        (fun t x ↦ cutoffValue (chi t) (u t) x)) ≤ Bf)
    (hsourceHolder : HolderWith Kf alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (parabolicVariableMatrixOperator a
          (fun t x ↦ cutoffValue (chi t) (u t) x))))
    (Ka omega : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict (a i j)))
    (homega : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p0 - a i j p‖ ≤ omega i j)
    (hcutoffGauge : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Icc (0 : Real) S) Set.univ)
      (fun t x ↦ cutoffValue (chi t) (u t) x) ≤ X) :
    eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Ioc (0 : Real) T) Set.univ)
        (fun t x ↦ cutoffValue (chi t) (u t) x) ≤
      spdHeatPotentialSchauderConst (fun i j ↦ a i j p0) hA alpha
        (Kf + X * parabolicMatrixFreezeHolderConst Ka omega)
        (Bf + X * parabolicMatrixFreezeSupConst omega) T := by
  let w : Real → BoundedContinuousFunction (Euc n) F :=
    fun t ↦ cutoffValue (chi t) (u t)
  let dtimeW : Real → BoundedContinuousFunction (Euc n) F :=
    cutoffTimeJet chi dtimeChi u dtimeU
  let dw : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] F) :=
    fun t ↦ cutoffJet1 (chi t) (dchi t) (u t) (du t)
  let d2w : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F) :=
    fun t ↦ cutoffJet2 (chi t) (dchi t) (d2chi t)
      (u t) (du t) (d2u t)
  let g := parabolicCutoffFrozenSource (fun i j ↦ a i j p0)
    chi dtimeChi dchi d2chi u dtimeU du d2u
  apply parabolic_variable_coefficient_schauder_estimate_of_classical_solution
    halpha0 halpha1 hT hTS a p0 hA w dtimeW g dw d2w
  · intro s hs
    exact cutoffValue_hasDerivAt chi dtimeChi u dtimeU s
      (hchiTime s hs) (huTime s hs)
  · intro s hs x
    exact cutoffValue_hasFDerivAt (chi s) (dchi s) (u s) (du s)
      (hchi s hs) (hu s hs) x
  · intro s hs x
    exact cutoffJet1_hasFDerivAt (chi s) (dchi s) (d2chi s)
      (u s) (du s) (d2u s) (hchi s hs) (hdchi s hs)
        (hu s hs) (hdu s hs) x
  · intro s x
    simp only [g, dtimeW, d2w, parabolicCutoffFrozenSource_apply]
  · exact hchiCont.smul huCont
  · ext x
    change chi 0 x • u 0 x = 0
    rw [hchi0]
    change (0 : Real) • u 0 x = (0 : F)
    exact zero_smul Real (u 0 x)
  · exact hsourceBound
  · exact hsourceHolder
  · exact ha
  · exact homega
  · exact hcutoffGauge

theorem parabolic_variable_coefficient_schauder_estimate_of_cutoff_source_estimates
    {alpha Kchi Ksource Kcomm Mchi Bsource Bcomm X : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {S T : Real} (hT : 0 ≤ T) (hTS : T < S)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (chi dtimeChi : Real → BoundedContinuousFunction (Euc n) Real)
    (dchi : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] Real))
    (d2chi : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] Real))
    (u dtimeU : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (hchiTime : ∀ s ∈ Icc (0 : Real) S,
      HasDerivAt chi (dtimeChi s) s)
    (huTime : ∀ s ∈ Icc (0 : Real) S,
      HasDerivAt u (dtimeU s) s)
    (hchi : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (chi s : Euc n → Real) (dchi s x) x)
    (hdchi : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (dchi s : Euc n → Euc n →L[Real] Real)
        (d2chi s x) x)
    (hu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (u s : Euc n → F) (du s x) x)
    (hdu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (du s : Euc n → Euc n →L[Real] F) (d2u s x) x)
    (hchiCont : Continuous chi) (huCont : Continuous u)
    (hchi0 : chi 0 = 0)
    (hchiHolder : HolderWith Kchi alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p ↦ chi p.time p.space)))
    (hsourceHolder : HolderWith Ksource alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (parabolicVariableMatrixOperator a (fun t x ↦ u t x))))
    (hcommHolder : HolderWith Kcomm alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (parabolicCutoffOperatorCommutator a
          (fun p ↦ dtimeChi p.time p.space)
          (fun p ↦ dchi p.time p.space)
          (fun p ↦ d2chi p.time p.space)
          (fun t x ↦ u t x) (fun p ↦ du p.time p.space))))
    (hchiNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖chi p.time p.space‖ ≤ Mchi)
    (hsourceNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖parabolicVariableMatrixOperator a (fun t x ↦ u t x) p‖ ≤ Bsource)
    (hcommNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖parabolicCutoffOperatorCommutator a
          (fun q ↦ dtimeChi q.time q.space)
          (fun q ↦ dchi q.time q.space)
          (fun q ↦ d2chi q.time q.space)
          (fun t x ↦ u t x) (fun q ↦ du q.time q.space) p‖ ≤ Bcomm)
    (Ka omega : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict (a i j)))
    (homega : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p0 - a i j p‖ ≤ omega i j)
    (hcutoffGauge : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Icc (0 : Real) S) Set.univ)
      (fun t x ↦ cutoffValue (chi t) (u t) x) ≤ X) :
    eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Ioc (0 : Real) T) Set.univ)
        (fun t x ↦ cutoffValue (chi t) (u t) x) ≤
      spdHeatPotentialSchauderConst (fun i j ↦ a i j p0) hA alpha
        (parabolicCutoffSourceHolderConst
          Kchi Ksource Kcomm Mchi Bsource +
            X * parabolicMatrixFreezeHolderConst Ka omega)
        (parabolicCutoffSourceSupConst Mchi Bsource Bcomm +
          X * parabolicMatrixFreezeSupConst omega) T := by
  let Q : Set (ParabolicPoint (Euc n)) :=
    parabolicCylinder (Icc (0 : Real) S) Set.univ
  let source := parabolicVariableMatrixOperator a (fun t x ↦ u t x)
  let comm := parabolicCutoffOperatorCommutator a
    (fun p ↦ dtimeChi p.time p.space)
    (fun p ↦ dchi p.time p.space)
    (fun p ↦ d2chi p.time p.space)
    (fun t x ↦ u t x) (fun p ↦ du p.time p.space)
  have hoperator : Set.EqOn
      (parabolicVariableMatrixOperator a
        (fun t x ↦ cutoffValue (chi t) (u t) x))
      (fun p ↦ chi p.time p.space • source p + comm p) Q := by
    apply parabolicVariableMatrixOperator_cutoff_eqOn_of_bcf_jets
      a chi dtimeChi dchi d2chi u dtimeU du d2u
    · intro p hp
      exact hchiTime p.time hp.1
    · intro p hp
      exact huTime p.time hp.1
    · intro p hp
      exact hchi p.time hp.1
    · intro p hp
      exact hdchi p.time hp.1
    · intro p hp
      exact hu p.time hp.1
    · intro p hp
      exact hdu p.time hp.1
  have hbound := eSupNormOn_parabolicCutoffSource_eqOn_le
    (parabolicVariableMatrixOperator a
      (fun t x ↦ cutoffValue (chi t) (u t) x))
    (fun p ↦ chi p.time p.space) source comm Mchi Bsource Bcomm
      hoperator hchiNorm hsourceNorm hcommNorm
  have hholder := parabolicCutoffSource_eqOn_holderWith_restrict
    (parabolicVariableMatrixOperator a
      (fun t x ↦ cutoffValue (chi t) (u t) x))
    (fun p ↦ chi p.time p.space) source comm Mchi Bsource
      hoperator hchiHolder hsourceHolder hcommHolder hchiNorm hsourceNorm
  exact parabolic_variable_coefficient_schauder_estimate_of_cutoff_classical_solution
    halpha0 halpha1 hT hTS a p0 hA chi dtimeChi dchi d2chi
      u dtimeU du d2u hchiTime huTime hchi hdchi hu hdu hchiCont huCont
      hchi0 hbound hholder Ka omega ha homega hcutoffGauge

end DifferentialGeometry.Analysis.Parabolic.Euclidean

end
