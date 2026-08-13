import DifferentialGeometry.Analysis.Parabolic.Euclidean.BallInteriorSchauder
import DifferentialGeometry.Analysis.Parabolic.Euclidean.LowerOrder

noncomputable section

open Matrix Real Set
open scoped NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

open DifferentialGeometry.Analysis.Schauder

private abbrev Euc (n : Type*) := EuclideanSpace Real n

variable {n F : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]

theorem parabolic_variable_coefficient_ball_interior_schauder_estimate_of_lower_order_source_estimates
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
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (parabolicNondivergenceOperator a b c (fun t x ↦ u t x))))
    (hlowerHolder : HolderWith Klo alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (parabolicLowerOrderTerm b c (fun t x ↦ u t x))))
    (hsourceNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖parabolicNondivergenceOperator a b c (fun t x ↦ u t x) p‖ ≤
          Bsource)
    (hlowerNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
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
  apply parabolic_variable_coefficient_ball_interior_schauder_estimate_of_source_and_solution_estimates
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

theorem parabolic_nondivergence_ball_interior_schauder_estimate
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
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (parabolicNondivergenceOperator a b c (fun t x ↦ u t x))))
    (hsourceNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖parabolicNondivergenceOperator a b c (fun t x ↦ u t x) p‖ ≤
          Bsource)
    (Kb Bb : n → NNReal) (A Ka omega : n → n → NNReal)
    (hb : ∀ i, HolderWith (Kb i) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict (b i)))
    (hc : HolderWith Kc alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict c))
    (hbNorm : ∀ i p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖b i p‖ ≤ Bb i)
    (hcNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ → ‖c p‖ ≤ Bc)
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
  let e := continuousMultilinearCurryFin1 Real (Euc n) F
  have heq : ∀ p ∈ Q,
      e (parabolicSpatialJet 1 (fun t x ↦ u t x) p) =
        du p.time p.space := by
    intro p hp
    ext v
    simp only [e, parabolicSpatialJet,
      continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
    rw [(hu p.time hp.1 p.space).fderiv]
    rfl
  have hjetHolder : HolderWith Kdu alpha
      (Q.restrict (parabolicSpatialJet 1 (fun t x ↦ u t x))) := by
    have hcomp := e.symm.lipschitz.holderWith.comp hduHolder
    have hfun : e.symm ∘ Q.restrict (fun p ↦ du p.time p.space) =
        Q.restrict (parabolicSpatialJet 1 (fun t x ↦ u t x)) := by
      funext p
      change e.symm (du p.1.time p.1.space) =
        parabolicSpatialJet 1 (fun t x ↦ u t x) p.1
      rw [← heq p.1 p.2, e.symm_apply_apply]
    rw [hfun] at hcomp
    simpa only [Q, NNReal.coe_one, NNReal.rpow_one, one_mul] using hcomp
  have hjetNorm : ∀ p, p ∈ Q →
      ‖parabolicSpatialJet 1 (fun t x ↦ u t x) p‖ ≤ Mdu := by
    intro p hp
    rw [← e.norm_map, heq p hp]
    exact hduNorm p hp
  have hlowerHolder : HolderWith
      (parabolicLowerOrderHolderConst Kb Bb Kc Kdu Ku Mdu Bc Mu) alpha
      (Q.restrict (parabolicLowerOrderTerm b c (fun t x ↦ u t x))) :=
    parabolicLowerOrderTerm_holderWith_restrict
      b c (fun t x ↦ u t x) Kb Bb Mdu Bc Mu hb hc hjetHolder huHolder
        hbNorm hcNorm hjetNorm huNorm
  have hlowerNorm : ∀ p, p ∈ Q →
      ‖parabolicLowerOrderTerm b c (fun t x ↦ u t x) p‖ ≤
        parabolicLowerOrderSupConst Bb Bc Mdu Mu := by
    intro p hp
    exact norm_parabolicLowerOrderTerm_le b c (fun t x ↦ u t x)
      Bb Bc Mdu Mu hbNorm hcNorm hjetNorm huNorm p hp
  exact parabolic_variable_coefficient_ball_interior_schauder_estimate_of_lower_order_source_estimates
    halpha0 halpha1 haTime hat₀ ht₀t₁ ht₁b ht₁T hT hTS center hr hrR
    a p0 hA b c u dtimeU du d2u huTime hu hdu huCont
    hsourceHolder (by simpa only [Q] using hlowerHolder) hsourceNorm
    (by simpa only [Q] using hlowerNorm) A Ka omega ha homega haNorm
    hduHolder huHolder hduNorm huNorm hcutoffGauge

end DifferentialGeometry.Analysis.Parabolic.Euclidean
