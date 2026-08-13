import DifferentialGeometry.Analysis.Parabolic.Euclidean.DuhamelRepresentation

noncomputable section

open Matrix Real Set
open scoped NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

open DifferentialGeometry.Analysis.Schauder

private abbrev Euc (n : Type*) := EuclideanSpace Real n

variable {n F : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]

omit [DecidableEq n] [Nonempty n] [CompleteSpace F] in
theorem parabolicFrozenMatrixOperator_eq_of_bcf_jets
    (A : Matrix n n Real)
    (u dtU : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (p : ParabolicPoint (Euc n))
    (huTime : HasDerivAt u (dtU p.time) p.time)
    (hu : ∀ x, HasFDerivAt (u p.time : Euc n → F) (du p.time x) x)
    (hdu : ∀ x, HasFDerivAt
      (du p.time : Euc n → Euc n →L[Real] F) (d2u p.time x) x) :
    parabolicFrozenMatrixOperator A (fun t x ↦ u t x) p =
      dtU p.time p.space - matrixLap A (d2u p.time p.space) := by
  have htime : HasDerivAt (fun t ↦ u t p.space)
      (dtU p.time p.space) p.time := by
    simpa only [BoundedContinuousFunction.evalCLM_apply] using
      (BoundedContinuousFunction.evalCLM Real p.space).hasFDerivAt
        |>.comp_hasDerivAt p.time huTime
  have hspace : hessianCurryEquiv (Euc n) F
      (parabolicSpatialJet 2 (fun t x ↦ u t x) p) =
        d2u p.time p.space := by
    unfold parabolicSpatialJet
    exact hessianCurryEquiv_iteratedFDeriv_two
      (u p.time) (du p.time) (d2u p.time) hu hdu p.space
  unfold parabolicFrozenMatrixOperator parabolicFrozenMatrixLap
    parabolicTimeDerivative
  rw [htime.hasFDerivAt.fderiv]
  simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul, hspace]

theorem parabolic_variable_coefficient_schauder_estimate_of_classical_solution
    {alpha Kf Bf X : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {S T : Real} (hT : 0 ≤ T) (hTS : T < S)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (u dtU g : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (huTime : ∀ s ∈ Icc (0 : Real) S, HasDerivAt u (dtU s) s)
    (hu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (u s : Euc n → F) (du s x) x)
    (hdu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (du s : Euc n → Euc n →L[Real] F) (d2u s x) x)
    (hg : ∀ s x, g s x = dtU s x -
      matrixLap (fun i j ↦ a i j p0) (d2u s x))
    (huCont : Continuous u) (hu0 : u 0 = 0)
    (hsourceBound : eSupNormOn
      (parabolicCylinder (Icc (0 : Real) S) Set.univ)
      (parabolicVariableMatrixOperator a (fun t x ↦ u t x)) ≤ Bf)
    (hsourceHolder : HolderWith Kf alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (parabolicVariableMatrixOperator a (fun t x ↦ u t x))))
    (Ka omega : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict (a i j)))
    (homega : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p0 - a i j p‖ ≤ omega i j)
    (huGauge : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Icc (0 : Real) S) Set.univ)
      (fun t x ↦ u t x) ≤ X) :
    eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Ioc (0 : Real) T) Set.univ)
        (fun t x ↦ u t x) ≤
      spdHeatPotentialSchauderConst (fun i j ↦ a i j p0) hA alpha
        (Kf + X * parabolicMatrixFreezeHolderConst Ka omega)
        (Bf + X * parabolicMatrixFreezeSupConst omega) T := by
  let Q : Set (ParabolicPoint (Euc n)) :=
    parabolicCylinder (Icc (0 : Real) S) Set.univ
  let A : Matrix n n Real := fun i j ↦ a i j p0
  let Kdefect := X * parabolicMatrixFreezeHolderConst Ka omega
  let Bdefect := X * parabolicMatrixFreezeSupConst omega
  have hgfrozen : Set.EqOn (fun p ↦ g p.time p.space)
      (parabolicFrozenMatrixOperator A (fun t x ↦ u t x)) Q := by
    intro p hp
    calc
      g p.time p.space = dtU p.time p.space -
          matrixLap A (d2u p.time p.space) := hg p.time p.space
      _ = parabolicFrozenMatrixOperator A (fun t x ↦ u t x) p :=
        (parabolicFrozenMatrixOperator_eq_of_bcf_jets
          A u dtU du d2u p (huTime p.time hp.1)
            (hu p.time hp.1) (hdu p.time hp.1)).symm
  have hfrozen := parabolicFrozenMatrixOperator_source_estimate
    a p0 (fun t x ↦ u t x) Ka omega hsourceBound hsourceHolder
      ha homega huGauge
  rw [parabolicMatrixFreezeHolderConst_mul,
    parabolicMatrixFreezeSupConst_mul] at hfrozen
  have hboundG : ∀ r ∈ Icc (0 : Real) S, ‖g r‖ ≤ Bf + Bdefect := by
    intro r hr
    rw [BoundedContinuousFunction.norm_le (by positivity)]
    intro x
    let p : ParabolicPoint (Euc n) := parabolicPoint r x
    have hp : p ∈ Q := ⟨hr, Set.mem_univ x⟩
    have heq := hgfrozen hp
    calc
      ‖g r x‖ = ‖parabolicFrozenMatrixOperator A
          (fun t x ↦ u t x) p‖ := congrArg norm heq
      _ ≤ Bf + Bdefect := by
        change ‖parabolicFrozenMatrixOperator A
          (fun t x ↦ u t x) p‖ ≤ ((Bf + Bdefect : NNReal) : Real)
        rw [← ENNReal.ofReal_le_coe]
        exact (norm_le_eSupNormOn Q
          (parabolicFrozenMatrixOperator A (fun t x ↦ u t x)) p hp).trans
            (by simpa only [ENNReal.coe_add] using hfrozen.1)
  have hholderG : HolderWith (Kf + Kdefect) alpha
      (Q.restrict (fun p ↦ g p.time p.space)) := by
    have heq : Q.restrict (fun p ↦ g p.time p.space) =
        Q.restrict (parabolicFrozenMatrixOperator A
          (fun t x ↦ u t x)) := by
      funext p
      exact hgfrozen p.2
    rw [heq]
    exact hfrozen.2
  have hrep := spdHeatDuh_eqOn_of_zero_initial_of_parabolic_holder
    (K := Kf + Kdefect) (B := Bf + Bdefect) halpha0 A hA
      u dtU g du d2u
      (fun s hs ↦ huTime s ⟨hs.1.le, hs.2.le⟩)
      (fun s hs ↦ hu s ⟨hs.1.le, hs.2.le⟩)
      (fun s hs ↦ hdu s ⟨hs.1.le, hs.2.le⟩)
      (by simpa only [A] using hg) huCont hu0 hboundG hholderG
  exact parabolic_variable_coefficient_schauder_estimate_of_frozen_representation_on
    halpha0 halpha1 hT hTS a p0 hA (fun t x ↦ u t x) g hrep.symm
      hgfrozen hsourceBound hsourceHolder Ka omega ha homega huGauge

end DifferentialGeometry.Analysis.Parabolic.Euclidean

end
