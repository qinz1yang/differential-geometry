import DifferentialGeometry.Analysis.Parabolic.Euclidean.Cutoff
import DifferentialGeometry.Analysis.Schauder.Interpolation

noncomputable section

open Real Set
open scoped NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

open DifferentialGeometry.Analysis.Schauder

private abbrev Euc (n : Type*) := EuclideanSpace Real n

namespace BoundedContinuousFunction

variable {n F : Type*} [Fintype n]
  [NormedAddCommGroup F] [NormedSpace Real F]

omit [Fintype n] in
theorem parabolicTimeDerivative_eq
    {J : Set Real}
    (u dtimeU : Real → BoundedContinuousFunction (Euc n) F)
    (huTime : ∀ s ∈ J, HasDerivAt u (dtimeU s) s)
    {p : ParabolicPoint (Euc n)}
    (hp : p ∈ parabolicCylinder J Set.univ) :
    parabolicTimeDerivative (fun t x ↦ u t x) p =
      dtimeU p.time p.space := by
  have hpoint : HasDerivAt (fun t ↦ u t p.space)
      (dtimeU p.time p.space) p.time := by
    simpa only [BoundedContinuousFunction.evalCLM_apply] using
      (BoundedContinuousFunction.evalCLM Real p.space).hasFDerivAt
        |>.comp_hasDerivAt p.time (huTime p.time hp.1)
  unfold parabolicTimeDerivative
  rw [hpoint.hasFDerivAt.fderiv]
  simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul]

theorem parabolicSpatialJet_one_eq
    {J : Set Real}
    (u : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real → BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (hu : ∀ s ∈ J, ∀ x,
      HasFDerivAt (u s : Euc n → F) (du s x) x)
    {p : ParabolicPoint (Euc n)}
    (hp : p ∈ parabolicCylinder J Set.univ) :
    continuousMultilinearCurryFin1 Real (Euc n) F
        (parabolicSpatialJet 1 (fun t x ↦ u t x) p) =
      du p.time p.space := by
  ext v
  simp only [parabolicSpatialJet, continuousMultilinearCurryFin1_apply,
    iteratedFDeriv_one_apply]
  rw [(hu p.time hp.1 p.space).fderiv]
  rfl

theorem hessianCurryEquiv_parabolicSpatialJet_two_eq
    {J : Set Real}
    (u : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real → BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (hu : ∀ s ∈ J, ∀ x,
      HasFDerivAt (u s : Euc n → F) (du s x) x)
    (hdu : ∀ s ∈ J, ∀ x,
      HasFDerivAt (du s : Euc n → Euc n →L[Real] F) (d2u s x) x)
    {p : ParabolicPoint (Euc n)}
    (hp : p ∈ parabolicCylinder J Set.univ) :
    hessianCurryEquiv (Euc n) F
        (parabolicSpatialJet 2 (fun t x ↦ u t x) p) =
      d2u p.time p.space := by
  simpa only [parabolicPoint_time_space] using
    hessianCurryEquiv_parabolicSpatialJet_two_of_hasFDerivAt
      (fun t x ↦ u t x) (fun q ↦ du q.time q.space)
      (fun q ↦ d2u q.time q.space) p.time
      (hu p.time hp.1) (hdu p.time hp.1) p.space

theorem parabolicTimeDerivative_holderWith_restrict
    {J : Set Real} {alpha C : NNReal}
    (u dtimeU : Real → BoundedContinuousFunction (Euc n) F)
    (huTime : ∀ s ∈ J, HasDerivAt u (dtimeU s) s)
    (hgauge : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder J Set.univ) (fun t x ↦ u t x) ≤ C) :
    HolderWith C alpha
      ((parabolicCylinder J Set.univ).restrict
        (fun p ↦ dtimeU p.time p.space)) := by
  have hbase :=
    DifferentialGeometry.Analysis.Schauder.parabolicTimeDerivative_holderWith_restrict
      hgauge
  have hfun : (parabolicCylinder J Set.univ).restrict
      (parabolicTimeDerivative (fun t x ↦ u t x)) =
        (parabolicCylinder J Set.univ).restrict
          (fun p ↦ dtimeU p.time p.space) := by
    funext p
    exact parabolicTimeDerivative_eq u dtimeU huTime p.2
  rwa [hfun] at hbase

theorem norm_parabolicTimeDerivative_le
    {J : Set Real} {alpha C : NNReal}
    (u dtimeU : Real → BoundedContinuousFunction (Euc n) F)
    (huTime : ∀ s ∈ J, HasDerivAt u (dtimeU s) s)
    (hgauge : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder J Set.univ) (fun t x ↦ u t x) ≤ C) :
    ∀ p, p ∈ parabolicCylinder J Set.univ →
      ‖dtimeU p.time p.space‖ ≤ C := by
  intro p hp
  rw [← parabolicTimeDerivative_eq u dtimeU huTime hp]
  exact parabolicTimeDerivative_norm_le hgauge hp

theorem parabolicSpatialDerivative_holderWith_restrict_of_interpolation
    {J : Set Real} (hJ : Convex Real J)
    (epsilon : NNReal) (hepsilon : 0 < epsilon)
    {alpha C M : NNReal} (halpha : alpha ≤ 1)
    (u : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real → BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (hu : ∀ s ∈ J, ∀ x,
      HasFDerivAt (u s : Euc n → F) (du s x) x)
    (huC2 : IsParabolicC2On
      (parabolicCylinder J Set.univ) (fun t x ↦ u t x))
    (hgauge : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder J Set.univ) (fun t x ↦ u t x) ≤ C)
    (huNorm : ∀ p, p ∈ parabolicCylinder J Set.univ →
      ‖u p.time p.space‖ ≤ M) :
    HolderWith
      (parabolicSpatialGradientInterpolationConst epsilon alpha C M) alpha
      ((parabolicCylinder J Set.univ).restrict
        (fun p ↦ du p.time p.space)) := by
  let e := continuousMultilinearCurryFin1 Real (Euc n) F
  have hjet := parabolicSpatialJet_one_holderWith_restrict_of_interpolation
    hJ epsilon hepsilon halpha huC2 hgauge huNorm
  have hcomp := e.lipschitz.holderWith.comp hjet
  have hfun : e ∘ (parabolicCylinder J Set.univ).restrict
      (parabolicSpatialJet 1 (fun t x ↦ u t x)) =
        (parabolicCylinder J Set.univ).restrict
          (fun p ↦ du p.time p.space) := by
    funext p
    exact parabolicSpatialJet_one_eq u du hu p.2
  rw [hfun] at hcomp
  simpa only [NNReal.coe_one, NNReal.rpow_one, one_mul] using hcomp

theorem norm_parabolicSpatialDerivative_le_of_interpolation
    {J : Set Real} (epsilon : NNReal) (hepsilon : 0 < epsilon)
    {alpha C M : NNReal}
    (u : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real → BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (hu : ∀ s ∈ J, ∀ x,
      HasFDerivAt (u s : Euc n → F) (du s x) x)
    (huC2 : IsParabolicC2On
      (parabolicCylinder J Set.univ) (fun t x ↦ u t x))
    (hgauge : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder J Set.univ) (fun t x ↦ u t x) ≤ C)
    (huNorm : ∀ p, p ∈ parabolicCylinder J Set.univ →
      ‖u p.time p.space‖ ≤ M) :
    ∀ p, p ∈ parabolicCylinder J Set.univ →
      ‖du p.time p.space‖ ≤ 2 * M / epsilon + C * epsilon := by
  intro p hp
  rw [← parabolicSpatialJet_one_eq u du hu hp,
    LinearIsometryEquiv.norm_map]
  exact norm_parabolicSpatialJet_one_le_of_interpolation
    epsilon hepsilon huC2 hgauge huNorm p hp

theorem parabolicSpatialSecondDerivative_holderWith_restrict
    {J : Set Real} {alpha C : NNReal}
    (u : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real → BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (hu : ∀ s ∈ J, ∀ x,
      HasFDerivAt (u s : Euc n → F) (du s x) x)
    (hdu : ∀ s ∈ J, ∀ x,
      HasFDerivAt (du s : Euc n → Euc n →L[Real] F) (d2u s x) x)
    (hgauge : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder J Set.univ) (fun t x ↦ u t x) ≤ C) :
    HolderWith C alpha
      ((parabolicCylinder J Set.univ).restrict
        (fun p ↦ d2u p.time p.space)) := by
  let e := hessianCurryEquiv (Euc n) F
  have hbase := parabolicSpatialJet_holderWith_restrict hgauge
  have hcomp := e.lipschitz.holderWith.comp hbase
  have hfun : e ∘ (parabolicCylinder J Set.univ).restrict
      (parabolicSpatialJet 2 (fun t x ↦ u t x)) =
        (parabolicCylinder J Set.univ).restrict
          (fun p ↦ d2u p.time p.space) := by
    funext p
    exact hessianCurryEquiv_parabolicSpatialJet_two_eq u du d2u hu hdu p.2
  rw [hfun] at hcomp
  simpa only [NNReal.coe_one, NNReal.rpow_one, one_mul] using hcomp

theorem norm_parabolicSpatialSecondDerivative_le
    {J : Set Real} {alpha C : NNReal}
    (u : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real → BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (hu : ∀ s ∈ J, ∀ x,
      HasFDerivAt (u s : Euc n → F) (du s x) x)
    (hdu : ∀ s ∈ J, ∀ x,
      HasFDerivAt (du s : Euc n → Euc n →L[Real] F) (d2u s x) x)
    (hgauge : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder J Set.univ) (fun t x ↦ u t x) ≤ C) :
    ∀ p, p ∈ parabolicCylinder J Set.univ →
      ‖d2u p.time p.space‖ ≤ C := by
  intro p hp
  rw [← hessianCurryEquiv_parabolicSpatialJet_two_eq
    u du d2u hu hdu hp, LinearIsometryEquiv.norm_map]
  exact parabolicSpatialJet_norm_le hgauge (j := 2) (by omega) hp

end BoundedContinuousFunction

end DifferentialGeometry.Analysis.Parabolic.Euclidean

end
