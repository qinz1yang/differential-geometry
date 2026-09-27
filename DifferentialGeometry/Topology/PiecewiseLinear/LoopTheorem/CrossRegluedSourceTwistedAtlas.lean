/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceTwistedModel

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem locallyFinite_halfTurnGraph :
    LocallyFinite (fun n : ℤ =>
      {p : ((ℝ × ℝ) × ℝ) × ((ℝ × ℝ) × ℝ) | p.2 = halfTurnTranslation n p.1}) := by
  intro p
  let d : ℝ := p.2.1.1 - p.1.1.1
  obtain ⟨a, ha⟩ := exists_int_lt (d - 1)
  obtain ⟨b, hb⟩ := exists_int_gt (d + 1)
  let V : Set (((ℝ × ℝ) × ℝ) × ((ℝ × ℝ) × ℝ)) :=
    {q | q.2.1.1 - q.1.1.1 ∈ Ioo (d - 1) (d + 1)}
  have hV : IsOpen V := isOpen_Ioo.preimage (by fun_prop)
  refine ⟨V, hV.mem_nhds ⟨by dsimp [d]; linarith, by dsimp [d]; linarith⟩,
    (finite_Icc a b).subset ?_⟩
  rintro n ⟨q, hq, hqV⟩
  have hx := congrArg (fun z : (ℝ × ℝ) × ℝ => z.1.1) hq
  change q.2.1.1 = q.1.1.1 + (n : ℝ) at hx
  change d - 1 < q.2.1.1 - q.1.1.1 ∧ q.2.1.1 - q.1.1.1 < d + 1 at hqV
  constructor
  · have h : (a : ℝ) ≤ n := by linarith [hqV.1]
    exact_mod_cast h
  · have h : (n : ℝ) ≤ b := by linarith [hqV.2]
    exact_mod_cast h

instance : T2Space halfTurnQuotient := by
  apply (t2Space_iff_of_isOpenQuotientMap
    ⟨surjective_halfTurnProjection, continuous_halfTurnProjection,
      isOpenMap_halfTurnProjection⟩).mpr
  have heq : {p : ((ℝ × ℝ) × ℝ) × ((ℝ × ℝ) × ℝ) |
      halfTurnProjection p.1 = halfTurnProjection p.2} =
      ⋃ n : ℤ, {p | p.2 = halfTurnTranslation n p.1} := by
    ext p
    simp only [mem_ofPred_eq, mem_iUnion, halfTurnProjection_eq_iff]
  rw [heq]
  exact locallyFinite_halfTurnGraph.isClosed_iUnion fun n =>
    isClosed_eq continuous_snd ((continuous_halfTurnTranslation n).comp continuous_fst)

instance : SecondCountableTopology halfTurnQuotient :=
  TopologicalSpace.Quotient.secondCountableTopology isOpenMap_halfTurnProjection

noncomputable def halfTurnEuclideanProjection (p : EuclideanSpace ℝ (Fin 3)) :
    halfTurnQuotient := halfTurnProjection (spliceEmbedding.symm p)

theorem continuous_halfTurnEuclideanProjection : Continuous halfTurnEuclideanProjection :=
  continuous_halfTurnProjection.comp spliceEmbedding.symm.continuous

theorem surjective_halfTurnEuclideanProjection :
    Function.Surjective halfTurnEuclideanProjection :=
  surjective_halfTurnProjection.comp spliceEmbedding.symm.surjective

theorem isLocalHomeomorph_halfTurnEuclideanProjection :
    IsLocalHomeomorph halfTurnEuclideanProjection :=
  isLocalHomeomorph_halfTurnProjection.comp spliceEmbedding.symm.toHomeomorph.isLocalHomeomorph

noncomputable def halfTurnChart (p : EuclideanSpace ℝ (Fin 3)) :
    OpenPartialHomeomorph halfTurnQuotient (EuclideanSpace ℝ (Fin 3)) :=
  isLocalHomeomorph_halfTurnEuclideanProjection.localInverseAt p

theorem halfTurnChart_symm (p : EuclideanSpace ℝ (Fin 3)) :
    ⇑(halfTurnChart p).symm = halfTurnEuclideanProjection :=
  isLocalHomeomorph_halfTurnEuclideanProjection.localInverseAt_symm p

noncomputable instance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) halfTurnQuotient where
  atlas := range halfTurnChart
  chartAt q := halfTurnChart (spliceEmbedding q.out)
  mem_chart_source q := by
    have h := isLocalHomeomorph_halfTurnEuclideanProjection.apply_self_mem_localInverseAt_source
      (x := spliceEmbedding q.out)
    simpa only [halfTurnChart, halfTurnEuclideanProjection,
      ContinuousLinearEquiv.symm_apply_apply, halfTurnProjection, Quotient.out_eq] using h
  chart_mem_atlas q := mem_range_self _

private noncomputable def halfTurnAffine (n : ℤ) :
    ((ℝ × ℝ) × ℝ) →ᵃ[ℝ] ((ℝ × ℝ) × ℝ) :=
  let x := ((LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.fst ℝ (ℝ × ℝ) ℝ)).toAffineMap
  let y := ((LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.fst ℝ (ℝ × ℝ) ℝ)).toAffineMap
  let z := (LinearMap.snd ℝ (ℝ × ℝ) ℝ).toAffineMap
  ((x + AffineMap.const ℝ _ (n : ℝ)).prod (((-1 : ℝ) ^ n) • y)).prod
    (((-1 : ℝ) ^ n) • (z - AffineMap.const ℝ _ (1 / 2)) + AffineMap.const ℝ _ (1 / 2))

private theorem halfTurnAffine_apply (n : ℤ) (p : (ℝ × ℝ) × ℝ) :
    halfTurnAffine n p = halfTurnTranslation n p := rfl

private theorem halfTurn_change_isPiecewiseAffineOn
    {f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U) (hf : ContinuousOn f U)
    (hproj : ∀ p ∈ U, halfTurnEuclideanProjection p = halfTurnEuclideanProjection (f p)) :
    IsPiecewiseAffineOn f U := by
  apply isPiecewiseAffineOn_of_locally
  intro p hp
  obtain ⟨n, hn⟩ := halfTurnProjection_eq_iff.mp (hproj p hp)
  let d : EuclideanSpace ℝ (Fin 3) → ℝ :=
    fun q => (spliceEmbedding.symm (f q)).1.1 - (spliceEmbedding.symm q).1.1
  have hd : ContinuousOn d U :=
    (spliceEmbedding.symm.continuous.comp_continuousOn hf).fst.fst.sub
      spliceEmbedding.symm.continuous.fst.fst.continuousOn
  have hdn : d p = n := by
    have h := congrArg (fun z : (ℝ × ℝ) × ℝ => z.1.1) hn
    change (spliceEmbedding.symm (f p)).1.1 = (spliceEmbedding.symm p).1.1 + n at h
    dsimp [d]
    linarith
  let V := U ∩ d ⁻¹' Ioo ((n : ℝ) - 1 / 2) ((n : ℝ) + 1 / 2)
  have hV : IsOpen V := hd.isOpen_inter_preimage hU isOpen_Ioo
  have hpV : p ∈ V := ⟨hp, by change _ < d p ∧ d p < _; rw [hdn]; constructor <;> linarith⟩
  refine ⟨V, hV, hpV, ?_⟩
  let A := spliceEmbedding.toAffineEquiv.toAffineMap.comp
    ((halfTurnAffine n).comp spliceEmbedding.symm.toAffineEquiv.toAffineMap)
  apply (isPiecewiseAffineOn_of_affine A (hU.inter hV)).congr
  intro q hq
  obtain ⟨m, hm⟩ := halfTurnProjection_eq_iff.mp (hproj q hq.1)
  have hdm : d q = m := by
    have h := congrArg (fun z : (ℝ × ℝ) × ℝ => z.1.1) hm
    change (spliceEmbedding.symm (f q)).1.1 = (spliceEmbedding.symm q).1.1 + m at h
    dsimp [d]
    linarith
  have hmn : m = n := by
    have hlt := hq.2.2
    change (n : ℝ) - 1 / 2 < d q ∧ d q < (n : ℝ) + 1 / 2 at hlt
    rw [hdm] at hlt
    have hlo : n - 1 < m := by
      have h : ((n - 1 : ℤ) : ℝ) < m := by push_cast; linarith [hlt.1]
      exact_mod_cast h
    have hhi : m < n + 1 := by
      have h : (m : ℝ) < ((n + 1 : ℤ) : ℝ) := by push_cast; linarith [hlt.2]
      exact_mod_cast h
    omega
  rw [hmn] at hm
  apply spliceEmbedding.symm.injective
  change spliceEmbedding.symm (f q) = spliceEmbedding.symm
    (spliceEmbedding (halfTurnAffine n (spliceEmbedding.symm q)))
  simpa only [ContinuousLinearEquiv.symm_apply_apply, halfTurnAffine_apply] using hm

instance : HasGroupoid halfTurnQuotient (plGroupoid 3) where
  compatible := by
    rintro e e' ⟨p, rfl⟩ ⟨q, rfl⟩
    apply mem_plGroupoid_of_isPiecewiseAffineOn
    let k := (halfTurnChart p).symm.trans (halfTurnChart q)
    apply halfTurn_change_isPiecewiseAffineOn k.open_source k.continuousOn
    intro z hz
    change halfTurnEuclideanProjection z =
      halfTurnEuclideanProjection ((halfTurnChart q) ((halfTurnChart p).symm z))
    calc
      _ = (halfTurnChart p).symm z := congrFun (halfTurnChart_symm p).symm z
      _ = (halfTurnChart q).symm
          ((halfTurnChart q) ((halfTurnChart p).symm z)) :=
        ((halfTurnChart q).left_inv hz.2).symm
      _ = _ := congrFun (halfTurnChart_symm q) _

theorem isPL_halfTurnEuclideanProjection : IsPL 3 3 halfTurnEuclideanProjection := by
  intro p
  rw [ChartedSpace.liftPropAt_iff]
  refine ⟨continuous_halfTurnEuclideanProjection.continuousAt, ?_⟩
  let e := chartAt (EuclideanSpace ℝ (Fin 3)) (halfTurnEuclideanProjection p)
  let U := halfTurnEuclideanProjection ⁻¹' e.source
  have hU : IsOpen U := e.open_source.preimage continuous_halfTurnEuclideanProjection
  have hpU : p ∈ U := by
    change halfTurnEuclideanProjection p ∈
      (chartAt (EuclideanSpace ℝ (Fin 3)) (halfTurnEuclideanProjection p)).source
    exact mem_chart_source _ _
  have hesymm : ⇑e.symm = halfTurnEuclideanProjection := halfTurnChart_symm _
  have hpa : IsPiecewiseAffineOn (e ∘ halfTurnEuclideanProjection) U := by
    apply halfTurn_change_isPiecewiseAffineOn hU
      (e.continuousOn.comp continuous_halfTurnEuclideanProjection.continuousOn (fun _ h => h))
    intro q hq
    change halfTurnEuclideanProjection q = halfTurnEuclideanProjection
      (e (halfTurnEuclideanProjection q))
    calc
      _ = e.symm (e (halfTurnEuclideanProjection q)) := (e.left_inv hq).symm
      _ = _ := congrFun hesymm _
  have hpa' : IsPiecewiseAffineWithinAt (e ∘ halfTurnEuclideanProjection) (univ ∩ U) p := by
    simpa only [univ_inter] using hpa p hpU
  exact hpa'.of_inter_of_mem_nhds (hU.mem_nhds hpU)

end DifferentialGeometry.Topology.PiecewiseLinear
