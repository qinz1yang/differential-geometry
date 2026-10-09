import DifferentialGeometry.Analysis.Calculus.MapConvergence.Algebra
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.CenterOfMass.Average.Weights.Basic

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff Topology

namespace DifferentialGeometry
namespace CheegerGromovCompactness

universe uX

variable {E' : Type uX} [NormedAddCommGroup E'] [NormedSpace Real E']

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem normWeights_contDiffOn {U : Set E'} {num : ι → E' → Real}
    (hnum : ∀ i, ContDiffOn Real (∞ : WithTop ℕ∞) (num i) U)
    (hne : ∀ x ∈ U, (∑ j, num j x) ≠ 0) (i : ι) :
    ContDiffOn Real (∞ : WithTop ℕ∞) (normWeights num i) U :=
  (hnum i).div (ContDiffOn.sum fun j _ => hnum j) hne

omit [DecidableEq ι] in
theorem normWeightsConvergence {U : Set E'} (hU : IsOpen U)
    {num : Nat → ι → E' → Real} {numinf : ι → E' → Real}
    {δ : Real} (hδ : 0 < δ)
    (hconv : ∀ i, MapCInfConvergenceOnCompacts U (fun k => num k i) (numinf i))
    (hc : ∀ k i, ContDiffOn Real (∞ : WithTop ℕ∞) (num k i) U)
    (hcinf : ∀ i, ContDiffOn Real (∞ : WithTop ℕ∞) (numinf i) U)
    (hlow : ∀ k, ∀ z ∈ U, δ < ∑ j, num k j z)
    (hlowinf : ∀ z ∈ U, δ < ∑ j, numinf j z) (i : ι) :
    MapCInfConvergenceOnCompacts U (fun k => normWeights (num k) i) (normWeights numinf i) := by
  have hpi := mapCInfConvergence_pi hU hconv (fun i k => hc k i) hcinf
  set Lsum : (ι → Real) →L[Real] Real := ∑ j : ι, ContinuousLinearMap.proj j with hLsum
  have hpic : ∀ k, ContDiffOn Real (∞ : WithTop ℕ∞) (fun z (j : ι) => num k j z) U :=
    fun k => contDiffOn_pi.mpr fun j => hc k j
  have hpiinfc : ContDiffOn Real (∞ : WithTop ℕ∞) (fun z (j : ι) => numinf j z) U :=
    contDiffOn_pi.mpr fun j => hcinf j
  have hsum0 := mapCInfConvergence_clm hU Lsum hpi hpic hpiinfc
  have hLapp : ∀ v : ι → Real, Lsum v = ∑ j, v j := by
    intro v
    rw [hLsum, sum_apply]
    exact Finset.sum_congr rfl fun j _ => ContinuousLinearMap.proj_apply j v
  have hsum : MapCInfConvergenceOnCompacts U (fun k z => ∑ j, num k j z)
      (fun z => ∑ j, numinf j z) := by
    refine hsum0.congr hU (fun k z _ => ?_) (fun z _ => ?_)
    · exact (hLapp (fun j => num k j z)).symm
    · exact (hLapp (fun j => numinf j z)).symm
  have hsumc : ∀ k, ContDiffOn Real (∞ : WithTop ℕ∞) (fun z => ∑ j, num k j z) U :=
    fun k => ContDiffOn.sum fun j _ => hc k j
  have hsuminfc : ContDiffOn Real (∞ : WithTop ℕ∞) (fun z => ∑ j, numinf j z) U :=
    ContDiffOn.sum fun j _ => hcinf j
  have hinv := mapCInfConvergence_inv hU hδ hsum hsumc hsuminfc hlow hlowinf
  have hinvc : ∀ k, ContDiffOn Real (∞ : WithTop ℕ∞) (fun z => (∑ j, num k j z)⁻¹) U :=
    fun k => (hsumc k).inv (fun z hz => ne_of_gt (lt_trans hδ (hlow k z hz)))
  have hinvinfc : ContDiffOn Real (∞ : WithTop ℕ∞) (fun z => (∑ j, numinf j z)⁻¹) U :=
    hsuminfc.inv (fun z hz => ne_of_gt (lt_trans hδ (hlowinf z hz)))
  have hmul := mapCInfConvergence_mul hU (hconv i) hinv
    (fun k => hc k i) (hcinf i) hinvc hinvinfc
  refine hmul.congr hU (fun k z _ => ?_) (fun z _ => ?_) <;>
    simp [normWeights, div_eq_mul_inv]

variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace Real X]

omit [Fintype ι] in
theorem cutRaw_contDiffOn {U : Set X} {a : ι -> X -> Real}
    (ha : forall i, ContDiffOn Real (∞ : WithTop ℕ∞) (a i) U)
    (i0 i : ι) :
    ContDiffOn Real (∞ : WithTop ℕ∞) (cutRaw (a i0) a i0 i) U := by
  by_cases hi : i = i0
  · subst i
    have heq : cutRaw (a i0) a i0 i0 = a i0 := by
      funext x
      exact cutRaw_same (a i0) a i0 x
    rw [heq]
    exact ha i0
  · have hkill : ContDiffOn Real (∞ : WithTop ℕ∞)
        (fun x => (1 : Real) - a i0 x) U :=
      (contDiffOn_const (c := (1 : Real))).sub (ha i0)
    refine ContDiffOn.congr (hkill.mul (ha i)) ?_
    intro x _hx
    exact cutRaw_of_ne (a i0) a i0 i x hi

omit [Fintype ι] in
theorem cutRaw_convergence {U : Set X} (hU : IsOpen U)
    {a : Nat -> ι -> X -> Real} {ainf : ι -> X -> Real}
    (hconv : forall i, MapCInfConvergenceOnCompacts U (fun k => a k i) (ainf i))
    (hc : forall k i, ContDiffOn Real (∞ : WithTop ℕ∞) (a k i) U)
    (hcinf : forall i, ContDiffOn Real (∞ : WithTop ℕ∞) (ainf i) U)
    (i0 i : ι) :
    MapCInfConvergenceOnCompacts U
      (fun k => cutRaw (a k i0) (a k) i0 i)
      (cutRaw (ainf i0) ainf i0 i) := by
  by_cases hi : i = i0
  · subst i
    have hseq : (fun k => cutRaw (a k i0) (a k) i0 i0) =
        (fun k => a k i0) := by
      funext k x
      exact cutRaw_same (a k i0) (a k) i0 x
    have hinf : cutRaw (ainf i0) ainf i0 i0 = ainf i0 := by
      funext x
      exact cutRaw_same (ainf i0) ainf i0 x
    rw [hseq, hinf]
    exact hconv i0
  · let oneSub : Real -> Real := fun t => 1 - t
    have hone : ContDiff Real (∞ : WithTop ℕ∞) oneSub :=
      contDiff_const.sub contDiff_id
    have hkill := MapCInfConvergenceOnCompacts.comp_of_finiteDimensional
      hU isOpen_univ (hconv i0)
      (mapCInfConvergence_const (U := (Set.univ : Set Real)) oneSub)
      (fun k => hc k i0) (hcinf i0) (fun _ => hone.contDiffOn) hone.contDiffOn
      (Set.mapsTo_univ _ _) (fun _ => Set.mapsTo_univ _ _)
    have hmul := mapCInfConvergence_mul hU hkill (hconv i)
      (fun k => contDiffOn_const.sub (hc k i0)) (contDiffOn_const.sub (hcinf i0))
      (fun k => hc k i) (hcinf i)
    refine hmul.congr hU (fun k x _ => ?_) (fun x _ => ?_)
    · simp only [oneSub]
      exact cutRaw_of_ne (a k i0) (a k) i0 i x hi
    · simp only [oneSub]
      exact cutRaw_of_ne (ainf i0) ainf i0 i x hi

omit [DecidableEq ι] in
theorem rawWeights_convergence {U : Set X} (hU : IsOpen U)
    {num : Nat -> ι -> X -> Real} {numinf : ι -> X -> Real}
    {delta : Real} (hdelta : 0 < delta)
    (hconv : forall i, MapCInfConvergenceOnCompacts U (fun k => num k i) (numinf i))
    (hc : forall k i, ContDiffOn Real (∞ : WithTop ℕ∞) (num k i) U)
    (hcinf : forall i, ContDiffOn Real (∞ : WithTop ℕ∞) (numinf i) U)
    (hlow : forall k, forall z, z ∈ U -> delta < ∑ j, num k j z)
    (hlowinf : forall z, z ∈ U -> delta < ∑ j, numinf j z) (i : ι) :
    MapCInfConvergenceOnCompacts U
      (fun k z => rawWeights (num k) z i) (fun z => rawWeights numinf z i) := by
  change MapCInfConvergenceOnCompacts U
    (fun k => normWeights (num k) i) (normWeights numinf i)
  exact normWeightsConvergence hU hdelta hconv hc hcinf hlow hlowinf i

omit [NormedAddCommGroup X] [NormedSpace Real X] in
theorem cutRaw_sum_half {a : ι -> X -> Real} {i0 : ι} {x : X}
    (hbase : a i0 x ∈ Set.Icc (0 : Real) 1)
    (hnn : forall i, 0 <= a i x) (hcover : exists i, a i x = 1) :
    (1 / 2 : Real) <= ∑ i, cutRaw (a i0) a i0 i x := by
  have hrawnn : forall i, 0 <= cutRaw (a i0) a i0 i x :=
    fun i => cutRaw_nonneg hbase hnn i
  by_cases hhalf : (1 / 2 : Real) <= a i0 x
  · exact hhalf.trans (by
      simpa only [cutRaw_same] using
        (Finset.single_le_sum (fun j _ => hrawnn j) (Finset.mem_univ i0)))
  · obtain ⟨j, hj⟩ := hcover
    have hji : j ≠ i0 := by
      intro h
      subst j
      linarith
    have hjraw : (1 / 2 : Real) <= cutRaw (a i0) a i0 j x := by
      rw [cutRaw_of_ne (a i0) a i0 j x hji, hj, mul_one]
      linarith
    exact hjraw.trans
      (Finset.single_le_sum (fun q _ => hrawnn q) (Finset.mem_univ j))

theorem cutWeights_convergence {U : Set X} (hU : IsOpen U)
    {a : Nat -> ι -> X -> Real} {ainf : ι -> X -> Real}
    (hconv : forall i, MapCInfConvergenceOnCompacts U (fun k => a k i) (ainf i))
    (hc : forall k i, ContDiffOn Real (∞ : WithTop ℕ∞) (a k i) U)
    (hcinf : forall i, ContDiffOn Real (∞ : WithTop ℕ∞) (ainf i) U)
    (i0 : ι)
    (hbase : forall k z, z ∈ U -> a k i0 z ∈ Set.Icc (0 : Real) 1)
    (hnn : forall k z, z ∈ U -> forall i, 0 <= a k i z)
    (hcover : forall k z, z ∈ U -> exists i, a k i z = 1)
    (i : ι) :
    MapCInfConvergenceOnCompacts U
      (fun k z => rawWeights (cutRaw (a k i0) (a k) i0) z i)
      (fun z => rawWeights (cutRaw (ainf i0) ainf i0) z i) := by
  have hraw : forall j, MapCInfConvergenceOnCompacts U
      (fun k => cutRaw (a k i0) (a k) i0 j)
      (cutRaw (ainf i0) ainf i0 j) :=
    fun j => cutRaw_convergence hU hconv hc hcinf i0 j
  have hrawc : forall k j, ContDiffOn Real (∞ : WithTop ℕ∞)
      (cutRaw (a k i0) (a k) i0 j) U :=
    fun k j => cutRaw_contDiffOn (fun q => hc k q) i0 j
  have hrawcinf : forall j, ContDiffOn Real (∞ : WithTop ℕ∞)
      (cutRaw (ainf i0) ainf i0 j) U :=
    fun j => cutRaw_contDiffOn hcinf i0 j
  have hlow : forall k, forall z, z ∈ U ->
      (1 / 4 : Real) < ∑ j, cutRaw (a k i0) (a k) i0 j z := by
    intro k z hz
    have hhalf := cutRaw_sum_half (hbase k z hz) (hnn k z hz) (hcover k z hz)
    linarith
  have hlowinf : forall z, z ∈ U ->
      (1 / 4 : Real) < ∑ j, cutRaw (ainf i0) ainf i0 j z := by
    intro z hz
    have hsum : Filter.Tendsto
        (fun k => ∑ j, cutRaw (a k i0) (a k) i0 j z) Filter.atTop
        (nhds (∑ j, cutRaw (ainf i0) ainf i0 j z)) :=
      tendsto_finsetSum Finset.univ fun j _ => tendsto_of_cInf (hraw j) hz
    have hhalf : (1 / 2 : Real) <= ∑ j, cutRaw (ainf i0) ainf i0 j z :=
      ge_of_tendsto hsum (Filter.Eventually.of_forall fun k =>
        cutRaw_sum_half (hbase k z hz) (hnn k z hz) (hcover k z hz))
    linarith
  exact rawWeights_convergence hU (by norm_num : (0 : Real) < 1 / 4)
    hraw hrawc hrawcinf hlow hlowinf i


end CheegerGromovCompactness
end DifferentialGeometry
