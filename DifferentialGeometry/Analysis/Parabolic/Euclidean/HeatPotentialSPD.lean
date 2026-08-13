import DifferentialGeometry.Analysis.Parabolic.Euclidean.FrozenDuhamelSPD
import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatPotentialEstimate
import DifferentialGeometry.Analysis.Schauder.Scaling

noncomputable section

open Matrix MeasureTheory Real Set
open scoped Interval NNReal RealInnerProductSpace Topology

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

open DifferentialGeometry.Analysis.Schauder

private abbrev Euc (n : Type*) := EuclideanSpace Real n

variable {n F : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]

def spdHeatSource (A : Matrix n n Real) (hA : A.PosDef)
    (f : Real → BoundedContinuousFunction (Euc n) F) :
    Real → BoundedContinuousFunction (Euc n) F :=
  fun t => linPullBcf (spdSqrtEquiv A hA) (f t)

def spdSourceHolderConst (A : Matrix n n Real) (hA : A.PosDef)
    (alpha K : NNReal) : NNReal :=
  K * (max 1 ‖(spdSqrtEquiv A hA : Euc n →L[Real] Euc n)‖₊) ^
    (alpha : Real)

def spdHeatDuh (A : Matrix n n Real) (hA : A.PosDef) (t : Real)
    (f : Real → BoundedContinuousFunction (Euc n) F) (x : Euc n) : F :=
  heatDuh t (spdHeatSource A hA f) ((spdSqrtEquiv A hA).symm x)

def spdHeatDuhGradient (A : Matrix n n Real) (hA : A.PosDef) (t : Real)
    (f : Real → BoundedContinuousFunction (Euc n) F) (x : Euc n) :
    Euc n →L[Real] F :=
  (heatDuhGradientMap t (spdHeatSource A hA f)
    ((spdSqrtEquiv A hA).symm x)).comp
      ((spdSqrtEquiv A hA).symm : Euc n →L[Real] Euc n)

def spdHeatDuhHessian (A : Matrix n n Real) (hA : A.PosDef) (t : Real)
    (f : Real → BoundedContinuousFunction (Euc n) F) (x : Euc n) :
    Euc n →L[Real] Euc n →L[Real] F :=
  pushHess (F := F) (spdSqrtEquiv A hA).symm
    (heatDuhHessian t (spdHeatSource A hA f)
      ((spdSqrtEquiv A hA).symm x))

def eSpdParabolicC2HolderGaugeOn
    (A : Matrix n n Real) (hA : A.PosDef) (alpha : NNReal)
    (Q : Set (ParabolicPoint (Euc n))) (u : Real → Euc n → F) : ENNReal :=
  eParabolicC2HolderGaugeOn alpha Q
    (fun t y => u t (spdSqrtEquiv A hA y))

def spdHeatPotentialSchauderConst
    (A : Matrix n n Real) (hA : A.PosDef)
    (alpha K B : NNReal) (T : Real) : NNReal :=
  parabolicC2HolderLinearEquivConst (spdSqrtEquiv A hA) alpha
    (heatPotentialSchauderConst (V := Euc n) alpha
      (spdSourceHolderConst A hA alpha K) B
      (spdSourceHolderConst A hA alpha K) T)

omit [Nonempty n] [NormedSpace Real F] [CompleteSpace F] in
theorem spdSourceHolderConst_add
    (A : Matrix n n Real) (hA : A.PosDef)
    (alpha K₁ K₂ : NNReal) :
    spdSourceHolderConst A hA alpha (K₁ + K₂) =
      spdSourceHolderConst A hA alpha K₁ +
        spdSourceHolderConst A hA alpha K₂ := by
  unfold spdSourceHolderConst
  ring

omit [Nonempty n] [NormedSpace Real F] [CompleteSpace F] in
theorem spdSourceHolderConst_nnreal_mul
    (A : Matrix n n Real) (hA : A.PosDef)
    (alpha c K : NNReal) :
    spdSourceHolderConst A hA alpha (c * K) =
      c * spdSourceHolderConst A hA alpha K := by
  unfold spdSourceHolderConst
  ring

omit [Nonempty n] [NormedSpace Real F] [CompleteSpace F] in
theorem spdHeatPotentialSchauderConst_add
    {alpha : NNReal} (halpha1 : alpha < 1)
    (A : Matrix n n Real) (hA : A.PosDef)
    (K₁ K₂ B₁ B₂ : NNReal) {T : Real} (hT : 0 ≤ T) :
    spdHeatPotentialSchauderConst A hA alpha (K₁ + K₂) (B₁ + B₂) T =
      spdHeatPotentialSchauderConst A hA alpha K₁ B₁ T +
        spdHeatPotentialSchauderConst A hA alpha K₂ B₂ T := by
  unfold spdHeatPotentialSchauderConst
  rw [spdSourceHolderConst_add,
    heatPotentialSchauderConst_add halpha1
      (spdSourceHolderConst A hA alpha K₁)
      (spdSourceHolderConst A hA alpha K₂) B₁ B₂
      (spdSourceHolderConst A hA alpha K₁)
      (spdSourceHolderConst A hA alpha K₂) hT,
    parabolicC2HolderLinearEquivConst_add]

omit [Nonempty n] [NormedSpace Real F] [CompleteSpace F] in
theorem spdHeatPotentialSchauderConst_nnreal_mul
    (A : Matrix n n Real) (hA : A.PosDef)
    (alpha c K B : NNReal) (T : Real) :
    spdHeatPotentialSchauderConst A hA alpha (c * K) (c * B) T =
      c * spdHeatPotentialSchauderConst A hA alpha K B T := by
  unfold spdHeatPotentialSchauderConst
  rw [spdSourceHolderConst_nnreal_mul,
    heatPotentialSchauderConst_nnreal_mul,
    parabolicC2HolderLinearEquivConst_nnreal_mul]

omit [Nonempty n] [NormedSpace Real F] [CompleteSpace F] in
theorem spdHeatSource_norm (A : Matrix n n Real) (hA : A.PosDef)
    (f : Real → BoundedContinuousFunction (Euc n) F) (t : Real) :
    ‖spdHeatSource A hA f t‖ = ‖f t‖ := by
  exact norm_linPullBcf (spdSqrtEquiv A hA) (f t)

omit [Nonempty n] [NormedSpace Real F] [CompleteSpace F] in
theorem spdHeatSource_parabolic_holder
    {alpha K : NNReal} {S : Real}
    (A : Matrix n n Real) (hA : A.PosDef)
    (f : Real → BoundedContinuousFunction (Euc n) F)
    (hsource : HolderWith K alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p => f p.time p.space))) :
    HolderWith (spdSourceHolderConst A hA alpha K) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p => spdHeatSource A hA f p.time p.space)) := by
  have h := parabolicHolder_linearMap
    (spdSqrtEquiv A hA : Euc n →L[Real] Euc n) hsource
  simpa only [spdSourceHolderConst,
    parabolicLinearPreimage_cylinder_univ, spdHeatSource,
    linPullBcf_apply, Function.comp_apply, parabolicLinearMap_time,
    parabolicLinearMap_space] using h

theorem spdHeatDuh_schauder_estimate
    {alpha K B : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {S T : Real} (hT : 0 ≤ T) (hTS : T < S)
    (A : Matrix n n Real) (hA : A.PosDef)
    (f : Real → BoundedContinuousFunction (Euc n) F)
    (hbound : ∀ r ∈ Icc (0 : Real) S, ‖f r‖ ≤ B)
    (hsource : HolderWith K alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p => f p.time p.space))) :
    eSpdParabolicC2HolderGaugeOn A hA alpha
      (parabolicCylinder (Ioc (0 : Real) T) Set.univ)
      (fun t x => spdHeatDuh A hA t f x) ≤
      heatPotentialSchauderConst (V := Euc n) alpha
        (spdSourceHolderConst A hA alpha K) B
        (spdSourceHolderConst A hA alpha K) T := by
  have hbound' : ∀ r ∈ Icc (0 : Real) S,
      ‖spdHeatSource A hA f r‖ ≤ B := by
    intro r hr
    rw [spdHeatSource_norm]
    exact hbound r hr
  have h := heatDuh_schauder_estimate_of_parabolic_holder
    halpha0 halpha1 hT hTS (spdHeatSource A hA f) hbound'
      (spdHeatSource_parabolic_holder A hA f hsource)
  unfold eSpdParabolicC2HolderGaugeOn spdHeatDuh
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using h

theorem spdHeatDuh_schauder_estimate_euclidean
    {alpha K B : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {S T : Real} (hT : 0 ≤ T) (hTS : T < S)
    (A : Matrix n n Real) (hA : A.PosDef)
    (f : Real → BoundedContinuousFunction (Euc n) F)
    (hbound : ∀ r ∈ Icc (0 : Real) S, ‖f r‖ ≤ B)
    (hsource : HolderWith K alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p => f p.time p.space))) :
    eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Ioc (0 : Real) T) Set.univ)
      (fun t x => spdHeatDuh A hA t f x) ≤
      spdHeatPotentialSchauderConst A hA alpha K B T := by
  apply eParabolicC2HolderGaugeOn_linearEquiv_le
    (spdSqrtEquiv A hA) alpha
    (heatPotentialSchauderConst (V := Euc n) alpha
      (spdSourceHolderConst A hA alpha K) B
      (spdSourceHolderConst A hA alpha K) T)
    (Ioc (0 : Real) T) (fun t x => spdHeatDuh A hA t f x)
  exact spdHeatDuh_schauder_estimate halpha0 halpha1 hT hTS
    A hA f hbound hsource

theorem spdHeatDuh_matrixLap
    {alpha K B : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {S t : Real} (ht : t ∈ Ioc (0 : Real) S)
    (A : Matrix n n Real) (hA : A.PosDef)
    (f : Real → BoundedContinuousFunction (Euc n) F)
    (hbound : ∀ r ∈ Icc (0 : Real) S, ‖f r‖ ≤ B)
    (hsource : HolderWith K alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p => f p.time p.space)))
    (x : Euc n) :
    matrixLap A (spdHeatDuhHessian A hA t f x) =
      heatLapDuh t (fun s y => spdHeatSource A hA f s y)
        ((spdSqrtEquiv A hA).symm x) := by
  let L := spdSqrtEquiv A hA
  let fp := spdHeatSource A hA f
  let H := heatDuhHessian t fp (L.symm x)
  have hbound' : ∀ s ∈ Icc (0 : Real) t, ‖fp s‖ ≤ B := by
    intro s hs
    change ‖spdHeatSource A hA f s‖ ≤ B
    rw [spdHeatSource_norm]
    exact hbound s ⟨hs.1, hs.2.trans ht.2⟩
  have hsource' := spdHeatSource_parabolic_holder A hA f hsource
  have hf : ∀ s ∈ Icc (0 : Real) t,
      HolderWith (spdSourceHolderConst A hA alpha K) alpha (fp s) := by
    intro s hs
    exact holderWith_slice_of_parabolicCylinder
      (f := fun r y => fp r y) hsource'
      ⟨hs.1, hs.2.trans ht.2⟩
  have hm1 : ∀ z : Euc n, AEStronglyMeasurable
      (fun s : Real => heatSupGradient (t - s) (fp s) z)
      (volume.restrict (uIoc (0 : Real) t)) := fun z =>
    heatSupGradient_timeSource_aestronglyMeasurable_of_parabolic_holder
      halpha0 ht fp hsource' z
  have hm2 : ∀ z : Euc n, AEStronglyMeasurable
      (fun s : Real => heatSupHessian (t - s) (fp s) z)
      (volume.restrict (uIoc (0 : Real) t)) := fun z =>
    heatSupHessian_timeSource_aestronglyMeasurable_of_parabolic_holder
      halpha0 ht fp hsource' z
  change matrixLap A (pushHess L.symm H) = _
  calc
    matrixLap A (pushHess L.symm H) = factorLap L (pushHess L.symm H) :=
      (spd_factorLap A hA _).symm
    _ = lapEval H := factorLap_pull L H
    _ = ∑ i : Fin (Module.finrank Real (Euc n)),
        H ((stdOrthonormalBasis Real (Euc n)) i)
          ((stdOrthonormalBasis Real (Euc n)) i) :=
      lapEval_basis (stdOrthonormalBasis Real (Euc n)) H
    _ = ∑ i : Fin (Module.finrank Real (Euc n)),
        heatD2Duh t ((stdOrthonormalBasis Real (Euc n)) i)
          ((stdOrthonormalBasis Real (Euc n)) i)
          (fun s y => fp s y) (L.symm x) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact heatDuhHessian_apply halpha0 halpha1 ht.1 fp hbound' hf hm1 hm2
        (L.symm x) _ _
    _ = heatLapDuh t (fun s y => fp s y) (L.symm x) := rfl

theorem spdHeatDuh_pde
    {alpha K B : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {S t : Real} (ht : t ∈ Ioo (0 : Real) S)
    (A : Matrix n n Real) (hA : A.PosDef)
    (f : Real → BoundedContinuousFunction (Euc n) F)
    (hbound : ∀ r ∈ Icc (0 : Real) S, ‖f r‖ ≤ B)
    (hsource : HolderWith K alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p => f p.time p.space)))
    (x : Euc n) :
    HasFDerivAt (spdHeatDuh A hA t f)
        (spdHeatDuhGradient A hA t f x) x ∧
      HasFDerivAt (spdHeatDuhGradient A hA t f)
        (spdHeatDuhHessian A hA t f x) x ∧
      HasDerivAt (fun q : Real => spdHeatDuh A hA q f x)
        (matrixLap A (spdHeatDuhHessian A hA t f x) + f t x) t := by
  let L := spdSqrtEquiv A hA
  let fp := spdHeatSource A hA f
  have ht' : t ∈ Ioc (0 : Real) S := ⟨ht.1, ht.2.le⟩
  have hbound' : ∀ s ∈ Icc (0 : Real) t, ‖fp s‖ ≤ B := by
    intro s hs
    change ‖spdHeatSource A hA f s‖ ≤ B
    rw [spdHeatSource_norm]
    exact hbound s ⟨hs.1, hs.2.trans ht.2.le⟩
  have hsource' := spdHeatSource_parabolic_holder A hA f hsource
  have hf : ∀ s ∈ Icc (0 : Real) S,
      HolderWith (spdSourceHolderConst A hA alpha K) alpha (fp s) := by
    intro s hs
    exact holderWith_slice_of_parabolicCylinder
      (f := fun r y => fp r y) hsource' hs
  have hf' : ∀ s ∈ Icc (0 : Real) t,
      HolderWith (spdSourceHolderConst A hA alpha K) alpha (fp s) := by
    intro s hs
    exact hf s ⟨hs.1, hs.2.trans ht.2.le⟩
  have hm0 : ∀ z : Euc n, AEStronglyMeasurable
      (fun s : Real => heatSup (t - s) (fp s) z)
      (volume.restrict (uIoc (0 : Real) t)) := fun z =>
    heatSup_timeSource_aestronglyMeasurable_of_parabolic_holder
      halpha0 ht' fp hsource' z
  have hm1 : ∀ z : Euc n, AEStronglyMeasurable
      (fun s : Real => heatSupGradient (t - s) (fp s) z)
      (volume.restrict (uIoc (0 : Real) t)) := fun z =>
    heatSupGradient_timeSource_aestronglyMeasurable_of_parabolic_holder
      halpha0 ht' fp hsource' z
  have hm2 : ∀ z : Euc n, AEStronglyMeasurable
      (fun s : Real => heatSupHessian (t - s) (fp s) z)
      (volume.restrict (uIoc (0 : Real) t)) := fun z =>
    heatSupHessian_timeSource_aestronglyMeasurable_of_parabolic_holder
      halpha0 ht' fp hsource' z
  have hv := (heatDuh_hasFDerivAt ht.1 fp hbound' hm0 hm1 (L.symm x)).comp
    x L.symm.hasFDerivAt
  have hg0 := heatDuhGradientMap_hasFDerivAt halpha0 halpha1.le ht.1 fp
    hbound' hf' hm1 hm2 (L.symm x)
  have hg1 := hg0.comp x L.symm.hasFDerivAt
  have hg := (precompJet (F := F) L.symm).hasFDerivAt.comp x hg1
  have hsourceOpen : HolderWith (spdSourceHolderConst A hA alpha K) alpha
      ((parabolicCylinder (Ioc (0 : Real) S) Set.univ).restrict
        (fun p => fp p.time p.space)) := by
    rw [HolderWith.restrict_iff] at hsource' ⊢
    exact hsource'.mono fun p hp => ⟨⟨hp.1.1.le, hp.1.2⟩, hp.2⟩
  have hm2all : ∀ q ∈ Ioc (0 : Real) S, ∀ z : Euc n,
      AEStronglyMeasurable
        (fun s : Real => heatSupHessian (q - s) (fp s) z)
        (volume.restrict (uIoc (0 : Real) q)) := fun q hq z =>
    heatSupHessian_timeSource_aestronglyMeasurable_of_parabolic_holder
      halpha0 hq fp (spdHeatSource_parabolic_holder A hA f hsource) z
  have htime := heatDuh_time halpha0 halpha1 ht fp hf hsourceOpen hm2all (L.symm x)
  have hlap := spdHeatDuh_matrixLap halpha0 halpha1.le ht' A hA f
    hbound hsource x
  refine ⟨?_, ?_, ?_⟩
  · simpa only [spdHeatDuh, spdHeatDuhGradient, L, Function.comp_apply,
      ContinuousLinearMap.comp_apply] using hv
  · simpa only [spdHeatDuhGradient, spdHeatDuhHessian, L,
      Function.comp_apply, ContinuousLinearMap.comp_apply] using hg
  · rw [hlap]
    simpa only [spdHeatDuh, fp, spdHeatSource, linPullBcf_apply,
      heatDuhTimeCandidateField, heatDuhTimeCandidate, parabolicPoint_time,
      parabolicPoint_space, L, ContinuousLinearEquiv.apply_symm_apply,
      add_comm] using htime

end DifferentialGeometry.Analysis.Parabolic.Euclidean

end
