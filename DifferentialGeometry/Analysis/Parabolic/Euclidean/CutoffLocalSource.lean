import DifferentialGeometry.Analysis.Parabolic.Euclidean.CutoffClassicalSchauder

noncomputable section

open Matrix Real Set
open scoped NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

open DifferentialGeometry.Analysis.Schauder

private abbrev Euc (n : Type*) := EuclideanSpace Real n

variable {n F : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]

theorem parabolic_variable_coefficient_schauder_estimate_of_local_cutoff_source_estimates
    {alpha Kchi Ksource Kcomm Mchi Bsource Bcomm X : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {S T : Real} (hT : 0 ≤ T) (hTS : T < S)
    {U : Set (ParabolicPoint (Euc n))}
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
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ ∩ U).restrict
        (parabolicVariableMatrixOperator a (fun t x ↦ u t x))))
    (hcommHolder : HolderWith Kcomm alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (parabolicCutoffOperatorCommutator a
          (fun p ↦ dtimeChi p.time p.space)
          (fun p ↦ dchi p.time p.space)
          (fun p ↦ d2chi p.time p.space)
          (fun t x ↦ u t x) (fun p ↦ du p.time p.space))))
    (hchiNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ → p ∈ U →
        ‖chi p.time p.space‖ ≤ Mchi)
    (hsourceNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ → p ∈ U →
        ‖parabolicVariableMatrixOperator a (fun t x ↦ u t x) p‖ ≤ Bsource)
    (hchiZero : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ → p ∉ U →
        chi p.time p.space = 0)
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
  have hbound := eSupNormOn_parabolicCutoffSource_eqOn_le_of_eq_zero_outside
    (parabolicVariableMatrixOperator a
      (fun t x ↦ cutoffValue (chi t) (u t) x))
    (fun p ↦ chi p.time p.space) source comm Mchi Bsource Bcomm
      hoperator hchiNorm hsourceNorm hcommNorm hchiZero
  have hholder := parabolicCutoffSource_eqOn_holderWith_restrict_of_eq_zero_outside
    (parabolicVariableMatrixOperator a
      (fun t x ↦ cutoffValue (chi t) (u t) x))
    (fun p ↦ chi p.time p.space) source comm Mchi Bsource
      hoperator hchiHolder hsourceHolder hcommHolder hchiNorm hsourceNorm hchiZero
  exact parabolic_variable_coefficient_schauder_estimate_of_cutoff_classical_solution
    halpha0 halpha1 hT hTS a p0 hA chi dtimeChi dchi d2chi
      u dtimeU du d2u hchiTime huTime hchi hdchi hu hdu hchiCont huCont
      hchi0 hbound hholder Ka omega ha homega hcutoffGauge

end DifferentialGeometry.Analysis.Parabolic.Euclidean

end
