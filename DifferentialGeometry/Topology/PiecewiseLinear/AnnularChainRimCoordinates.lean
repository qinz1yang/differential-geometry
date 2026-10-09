/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCell

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable section

private def rotatePoint (q : EuclideanSpace ℝ (Fin 3)) (c : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 3) :=
  EuclideanSpace.single 0 (q 0 * c 0) +
    EuclideanSpace.single 1 (q 1) +
      EuclideanSpace.single 2 (q 0 * c 1)

private theorem rotatePoint_apply_zero (q : EuclideanSpace ℝ (Fin 3))
    (c : EuclideanSpace ℝ (Fin 2)) : rotatePoint q c 0 = q 0 * c 0 := by
  simp [rotatePoint, PiLp.add_apply]

private theorem rotatePoint_apply_one (q : EuclideanSpace ℝ (Fin 3))
    (c : EuclideanSpace ℝ (Fin 2)) : rotatePoint q c 1 = q 1 := by
  simp [rotatePoint, PiLp.add_apply]

private theorem rotatePoint_apply_two (q : EuclideanSpace ℝ (Fin 3))
    (c : EuclideanSpace ℝ (Fin 2)) : rotatePoint q c 2 = q 0 * c 1 := by
  simp [rotatePoint, PiLp.add_apply]

private theorem continuous_rotatePoint :
    Continuous fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 2) =>
      rotatePoint z.1 z.2 := by
  have h : (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 2) =>
      rotatePoint z.1 z.2) =
      fun z => WithLp.toLp 2 (fun i : Fin 3 =>
        if i = 0 then z.1 0 * z.2 0 else if i = 1 then z.1 1 else z.1 0 * z.2 1) := by
    funext z
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [rotatePoint_apply_zero, rotatePoint_apply_one, rotatePoint_apply_two]
  rw [h]
  apply (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte]
    fun_prop
  · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte]
    fun_prop
  · simp only [Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte]
    fun_prop

private theorem circle_coord_sq_eq_one (c : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    (c : EuclideanSpace ℝ (Fin 2)) 0 ^ 2 + (c : EuclideanSpace ℝ (Fin 2)) 1 ^ 2 = 1 := by
  have hc : ‖(c : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using c.property
  have hsq : ‖(c : EuclideanSpace ℝ (Fin 2))‖ ^ 2 = 1 := by
    rw [hc]
    norm_num
  rw [EuclideanSpace.real_norm_sq_eq] at hsq
  simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, Finset.sum_empty, add_zero,
    Fin.succ_zero_eq_one] using hsq

private theorem rotatePoint_sq (q : EuclideanSpace ℝ (Fin 3))
    (c : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    rotatePoint q c 0 ^ 2 + rotatePoint q c 2 ^ 2 = q 0 ^ 2 := by
  rw [rotatePoint_apply_zero, rotatePoint_apply_two]
  have hc := circle_coord_sq_eq_one c
  calc
    (q 0 * (c : EuclideanSpace ℝ (Fin 2)) 0) ^ 2 +
        (q 0 * (c : EuclideanSpace ℝ (Fin 2)) 1) ^ 2 =
        q 0 ^ 2 * ((c : EuclideanSpace ℝ (Fin 2)) 0 ^ 2 +
          (c : EuclideanSpace ℝ (Fin 2)) 1 ^ 2) := by ring
    _ = q 0 ^ 2 := by rw [hc, mul_one]

private theorem mem_revolutionOf_rotatePoint {D : Set (EuclideanSpace ℝ (Fin 3))}
    (hhalf : ∀ q ∈ D, q 2 = 0 ∧ 0 < q 0) (q : D)
    (c : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    rotatePoint q c ∈ revolutionOf D := by
  refine ⟨q, q.property, (hhalf q q.property).1, (hhalf q q.property).2.le, ?_, ?_⟩
  · rw [rotatePoint_apply_one]
  · rw [← rotatePoint_sq]

private def rotationMap (D : Set (EuclideanSpace ℝ (Fin 3)))
    (hhalf : ∀ q ∈ D, q 2 = 0 ∧ 0 < q 0) :
    D × Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → revolutionOf D :=
  fun z => ⟨rotatePoint z.1 z.2, mem_revolutionOf_rotatePoint hhalf z.1 z.2⟩

private theorem continuous_rotationMap {D : Set (EuclideanSpace ℝ (Fin 3))}
    (hhalf : ∀ q ∈ D, q 2 = 0 ∧ 0 < q 0) :
    Continuous (rotationMap D hhalf) := by
  unfold rotationMap
  apply Continuous.subtype_mk
  have hf : Continuous (fun x : D × Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 =>
      ((x.1 : EuclideanSpace ℝ (Fin 3)), (x.2 : EuclideanSpace ℝ (Fin 2)))) :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  refine (continuous_rotatePoint.comp hf).congr ?_
  intro x
  rfl

private theorem rotationMap_injective {D : Set (EuclideanSpace ℝ (Fin 3))}
    (hhalf : ∀ q ∈ D, q 2 = 0 ∧ 0 < q 0) :
    Function.Injective (rotationMap D hhalf) := by
  rintro ⟨q, c⟩ ⟨q', c'⟩ h
  have hval : rotatePoint q c = rotatePoint q' c' := congrArg Subtype.val h
  have hzero : (q : EuclideanSpace ℝ (Fin 3)) 0 * (c : EuclideanSpace ℝ (Fin 2)) 0 =
      (q' : EuclideanSpace ℝ (Fin 3)) 0 * (c' : EuclideanSpace ℝ (Fin 2)) 0 := by
    simpa only [rotatePoint_apply_zero] using
      congrArg (fun x : EuclideanSpace ℝ (Fin 3) => x 0) hval
  have htwo : (q : EuclideanSpace ℝ (Fin 3)) 0 * (c : EuclideanSpace ℝ (Fin 2)) 1 =
      (q' : EuclideanSpace ℝ (Fin 3)) 0 * (c' : EuclideanSpace ℝ (Fin 2)) 1 := by
    simpa only [rotatePoint_apply_two] using
      congrArg (fun x : EuclideanSpace ℝ (Fin 3) => x 2) hval
  have hone : (q : EuclideanSpace ℝ (Fin 3)) 1 = (q' : EuclideanSpace ℝ (Fin 3)) 1 := by
    simpa only [rotatePoint_apply_one] using
      congrArg (fun x : EuclideanSpace ℝ (Fin 3) => x 1) hval
  have hqzero : (q : EuclideanSpace ℝ (Fin 3)) 2 =
      (q' : EuclideanSpace ℝ (Fin 3)) 2 := by
    rw [(hhalf q q.property).1, (hhalf q' q'.property).1]
  have hq0sq : (q : EuclideanSpace ℝ (Fin 3)) 0 ^ 2 =
      (q' : EuclideanSpace ℝ (Fin 3)) 0 ^ 2 := by
    calc
      (q : EuclideanSpace ℝ (Fin 3)) 0 ^ 2 =
          rotatePoint q c 0 ^ 2 + rotatePoint q c 2 ^ 2 := (rotatePoint_sq q c).symm
      _ = rotatePoint q' c' 0 ^ 2 + rotatePoint q' c' 2 ^ 2 := by rw [hval]
      _ = (q' : EuclideanSpace ℝ (Fin 3)) 0 ^ 2 := rotatePoint_sq q' c'
  have hq0pos : 0 < (q : EuclideanSpace ℝ (Fin 3)) 0 := (hhalf q q.property).2
  have hq'0pos : 0 < (q' : EuclideanSpace ℝ (Fin 3)) 0 := (hhalf q' q'.property).2
  have hqzero' : (q : EuclideanSpace ℝ (Fin 3)) 0 =
      (q' : EuclideanSpace ℝ (Fin 3)) 0 := by
    nlinarith [hq0sq]
  have hq : q = q' := by
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i
    · exact hqzero'
    · exact hone
    · exact hqzero
  subst q'
  have hc : c = c' := by
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i
    · exact mul_left_cancel₀ (ne_of_gt hq0pos) hzero
    · exact mul_left_cancel₀ (ne_of_gt hq0pos) htwo
  subst c'
  rfl

private def normalizedCirclePoint (z q : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 2) :=
  EuclideanSpace.single 0 (z 0 / q 0) + EuclideanSpace.single 1 (z 2 / q 0)

private theorem normalizedCirclePoint_apply_zero (z q : EuclideanSpace ℝ (Fin 3)) :
    normalizedCirclePoint z q 0 = z 0 / q 0 := by
  simp [normalizedCirclePoint, PiLp.add_apply]

private theorem normalizedCirclePoint_apply_one (z q : EuclideanSpace ℝ (Fin 3)) :
    normalizedCirclePoint z q 1 = z 2 / q 0 := by
  simp [normalizedCirclePoint, PiLp.add_apply]

private theorem normalizedCirclePoint_mem_sphere (z q : EuclideanSpace ℝ (Fin 3))
    (hq : 0 < q 0) (hsq : q 0 ^ 2 = z 0 ^ 2 + z 2 ^ 2) :
    normalizedCirclePoint z q ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  have hnormsq : ‖normalizedCirclePoint z q‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    rw [normalizedCirclePoint_apply_zero, normalizedCirclePoint_apply_one]
    field_simp [ne_of_gt hq]
    nlinarith [hsq]
  have hnorm : ‖normalizedCirclePoint z q‖ = 1 := by
    nlinarith [norm_nonneg (normalizedCirclePoint z q)]
  simpa only [mem_sphere, dist_zero_right] using hnorm

private theorem rotationMap_surjective {D : Set (EuclideanSpace ℝ (Fin 3))}
    (hhalf : ∀ q ∈ D, q 2 = 0 ∧ 0 < q 0) :
    Function.Surjective (rotationMap D hhalf) := by
  rintro ⟨z, hz⟩
  rcases hz with ⟨q, hq, -, -, hqone, hsq⟩
  have hqpos : 0 < q 0 := (hhalf q hq).2
  let c : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
    ⟨normalizedCirclePoint z q, normalizedCirclePoint_mem_sphere z q hqpos hsq⟩
  have hzero : rotatePoint q c 0 = z 0 := by
    rw [rotatePoint_apply_zero]
    change q 0 * normalizedCirclePoint z q 0 = z 0
    rw [normalizedCirclePoint_apply_zero]
    field_simp [ne_of_gt hqpos]
  have hone : rotatePoint q c 1 = z 1 := by
    rw [rotatePoint_apply_one]
    exact hqone
  have htwo : rotatePoint q c 2 = z 2 := by
    rw [rotatePoint_apply_two]
    change q 0 * normalizedCirclePoint z q 1 = z 2
    rw [normalizedCirclePoint_apply_one]
    field_simp [ne_of_gt hqpos]
  refine ⟨(⟨q, hq⟩, c), ?_⟩
  apply Subtype.ext
  change rotatePoint q c = z
  apply PiLp.ext
  intro i
  fin_cases i
  · exact hzero
  · exact hone
  · exact htwo

private theorem rotationMap_bijective {D : Set (EuclideanSpace ℝ (Fin 3))}
    (hhalf : ∀ q ∈ D, q 2 = 0 ∧ 0 < q 0) :
    Function.Bijective (rotationMap D hhalf) :=
  ⟨rotationMap_injective hhalf, rotationMap_surjective hhalf⟩
private theorem revolutionOf_singleton_eq_range_rotatePoint (q : EuclideanSpace ℝ (Fin 3))
    (hqtwo : q 2 = 0) (hqpos : 0 < q 0) :
    revolutionOf {q} = Set.range fun c : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 =>
      rotatePoint q c := by
  let hhalf : ∀ r ∈ ({q} : Set (EuclideanSpace ℝ (Fin 3))), r 2 = 0 ∧ 0 < r 0 := by
    intro r hr
    rw [mem_singleton_iff] at hr
    subst r
    exact ⟨hqtwo, hqpos⟩
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx⟩ := rotationMap_surjective hhalf ⟨z, hz⟩
    have hxq : (x.1 : EuclideanSpace ℝ (Fin 3)) = q := by
      simpa only [mem_singleton_iff] using x.1.property
    refine ⟨x.2, ?_⟩
    calc
      rotatePoint q x.2 = rotatePoint (x.1 : EuclideanSpace ℝ (Fin 3)) x.2 :=
        congrArg (fun r : EuclideanSpace ℝ (Fin 3) => rotatePoint r x.2) hxq.symm
      _ = z := congrArg Subtype.val hx
  · rintro ⟨c, rfl⟩
    exact mem_revolutionOf_rotatePoint hhalf ⟨q, by simp⟩ c

private theorem exists_revolution_segment_homeomorph
    {p q : EuclideanSpace ℝ (Fin 3)} (hpq : p ≠ q)
    (hhalf : ∀ r ∈ segment ℝ p q, r 2 = 0 ∧ 0 < r 0) :
    ∃ e : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × unitInterval) ≃ₜ
      revolutionOf (segment ℝ p q),
      range (fun c => (e (c, 0) : EuclideanSpace ℝ (Fin 3))) = revolutionOf {p} ∧
      range (fun c => (e (c, 1) : EuclideanSpace ℝ (Fin 3))) = revolutionOf {q} := by
  let es : unitInterval ≃ₜ segment ℝ p q :=
    ((Path.segment p q).continuous.isClosedEmbedding
      (Path.segment_injective_of_ne hpq)).isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr (Path.range_segment p q))
  have : CompactSpace (segment ℝ p q) := es.compactSpace
  let er : ((segment ℝ p q) × Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) ≃ₜ
      revolutionOf (segment ℝ p q) :=
    Continuous.homeoOfEquivCompactToT2
      (f := Equiv.ofBijective (rotationMap _ hhalf) (rotationMap_bijective hhalf))
      (continuous_rotationMap hhalf)
  let e := (Homeomorph.prodComm _ _).trans ((es.prodCongr (Homeomorph.refl _)).trans er)
  have he (c : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (t : unitInterval) :
      (e (c, t) : EuclideanSpace ℝ (Fin 3)) = rotatePoint (Path.segment p q t) c := rfl
  have hp := hhalf p (left_mem_segment ℝ p q)
  have hq := hhalf q (right_mem_segment ℝ p q)
  refine ⟨e, ?_, ?_⟩
  · rw [revolutionOf_singleton_eq_range_rotatePoint p hp.1 hp.2]
    apply congrArg range
    funext c
    rw [he, Path.source]
  · rw [revolutionOf_singleton_eq_range_rotatePoint q hq.1 hq.2]
    apply congrArg range
    funext c
    rw [he, Path.target]

theorem IsCanonicalConfiguration.exists_annulus_homeomorph
    {P : Fin 4 → EuclideanSpace ℝ (Fin 3)}
    {D Dint : Fin 3 → Set (EuclideanSpace ℝ (Fin 3))}
    {J : Fin 4 → Set (EuclideanSpace ℝ (Fin 3))}
    {A S T : Fin 3 → Set (EuclideanSpace ℝ (Fin 3))}
    {N : Set (EuclideanSpace ℝ (Fin 3))}
    {φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {S'' T'' : Fin 3 → Set (EuclideanSpace ℝ (Fin 3))}
    (hc : IsCanonicalConfiguration P D Dint J A S T N φ S'' T'') (j : Fin 3) :
    ∃ e : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × unitInterval) ≃ₜ (φ '' A j),
      range (fun c => (e (c, 0) : EuclideanSpace ℝ (Fin 3))) = φ '' J j.castSucc ∧
      range (fun c => (e (c, 1) : EuclideanSpace ℝ (Fin 3))) = φ '' J j.succ := by
  obtain ⟨e₀, h₀, h₁⟩ := exists_revolution_segment_homeomorph (hc.base.chain.consecutiveNe j)
    (fun p hp => hc.base.chain.halfPlane j p
      (hc.base.chain.interiorSubset j (hc.base.chain.segmentSubset j hp)))
  let e₁ := e₀.trans (Homeomorph.setCongr (hc.base.annulusEq j).symm)
  have hAN : A j ⊆ N := by
    rw [hc.unionEq]
    exact (hc.base.annulusSubset j).trans (interior_subset.trans (subset_iUnion S j))
  have hemb : IsEmbedding ((A j).domRestrict φ) :=
    hc.isEmbedding.comp (IsEmbedding.inclusion hAN)
  let e₂ := hemb.toHomeomorph.trans
    (Homeomorph.setCongr (Set.range_domRestrict φ (A j)))
  let e := e₁.trans e₂
  have he (c : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (t : unitInterval) :
      (e (c, t) : EuclideanSpace ℝ (Fin 3)) = φ (e₀ (c, t)) := rfl
  refine ⟨e, ?_, ?_⟩
  · simp_rw [he]
    change range (φ ∘ fun c => (e₀ (c, 0) : EuclideanSpace ℝ (Fin 3))) = _
    rw [range_comp, h₀, hc.base.circleEq]
  · simp_rw [he]
    change range (φ ∘ fun c => (e₀ (c, 1) : EuclideanSpace ℝ (Fin 3))) = _
    rw [range_comp, h₁, hc.base.circleEq]

theorem IsCanonicalTower.exists_annulus_homeomorph
    {φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {Pt : ℤ → EuclideanSpace ℝ (Fin 3)}
    {Dp Dpint J A S T S'' T'' : ℤ → Set (EuclideanSpace ℝ (Fin 3))}
    {Dimg Dbdimg W I : Set (EuclideanSpace ℝ (Fin 3))}
    {P' : EuclideanSpace ℝ (Fin 3)}
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ) :
    ∃ e : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × unitInterval) ≃ₜ (φ '' A i),
      range (fun c => (e (c, 0) : EuclideanSpace ℝ (Fin 3))) = φ '' J i ∧
      range (fun c => (e (c, 1) : EuclideanSpace ℝ (Fin 3))) = φ '' J (i + 1) := by
  have hh := (htw.config i).exists_annulus_homeomorph (0 : Fin 3)
  change ∃ e : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × unitInterval) ≃ₜ
      (φ '' A (i + 0)),
      range (fun c => (e (c, 0) : EuclideanSpace ℝ (Fin 3))) = φ '' J (i + 0) ∧
      range (fun c => (e (c, 1) : EuclideanSpace ℝ (Fin 3))) = φ '' J (i + 1) at hh
  rw [add_zero] at hh
  exact hh

end

end DifferentialGeometry.Topology.PiecewiseLinear
