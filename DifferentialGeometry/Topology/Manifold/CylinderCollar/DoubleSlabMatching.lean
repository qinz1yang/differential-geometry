import DifferentialGeometry.Topology.Manifold.CylinderCollar.SlabMatching

noncomputable section

open Set Filter Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

private def reverseCylinder : SphereCylinder ≃ₘ⟮SphereCylinderModel,SphereCylinderModel⟯ SphereCylinder :=
  Diffeomorph.fiberwiseAffine (fun _ => (1 : ℝ)) (fun _ => (-1:ℝ))
    contMDiff_const contMDiff_const (fun _ => by norm_num)

private theorem reverseCylinder_apply (q : SphereCylinder) : reverseCylinder q = (q.1,1-q.2) := by
  change (q.1,1 + -1*q.2) = _
  simp only [neg_one_mul,sub_eq_add_neg]

private theorem reverseCylinder_band :
    reverseCylinder '' (univ ×ˢ Icc (0 : ℝ) 1) = univ ×ˢ Icc (0 : ℝ) 1 := by
  ext q
  constructor
  · rintro ⟨p,hp,rfl⟩
    rw [reverseCylinder_apply]
    exact ⟨mem_univ _,by constructor <;> linarith [hp.2.1,hp.2.2]⟩
  · intro hq
    refine ⟨(q.1,1-q.2),⟨mem_univ _,by constructor <;> linarith [hq.2.1,hq.2.2]⟩,?_⟩
    rw [reverseCylinder_apply]
    simp only [sub_sub_cancel,Prod.mk.eta]

private theorem reverseCylinder_involutive (q : SphereCylinder) : reverseCylinder (reverseCylinder q) = q := by
  simp only [reverseCylinder_apply,sub_sub_cancel,Prod.mk.eta]

theorem exists_two_ended_slab_collar_matching
    (P₀ P₁ Q : PartialDiffeomorph SphereCylinderModel I SphereCylinder M ∞)
    (hP₀ : univ ×ˢ Icc (0 : ℝ) 1 ⊆ P₀.source)
    (hP₁ : univ ×ˢ Icc (0 : ℝ) 1 ⊆ P₁.source)
    (hQ : univ ×ˢ Icc (0 : ℝ) 1 ⊆ Q.source)
    (hzero : ∀ z : S2, Q (z,0) = P₀ (z,1))
    (hone : ∀ z : S2, Q (z,1) = P₁ (z,1))
    (hmeet₀ : P₀ '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ Q '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆
      P₀ '' (univ ×ˢ ({0} : Set ℝ)) ∪ P₀ '' (univ ×ˢ ({1} : Set ℝ)))
    (hmeet₁ : P₁ '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ Q '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆
      P₁ '' (univ ×ˢ ({0} : Set ℝ)) ∪ P₁ '' (univ ×ˢ ({1} : Set ℝ))) :
    ∃ G : SphereCylinder ≃ₘ⟮SphereCylinderModel,SphereCylinderModel⟯ SphereCylinder,
      G '' (univ ×ˢ Icc (0 : ℝ) 1) = univ ×ˢ Icc (0 : ℝ) 1 ∧
      (∀ z : S2, G (z,0) = (z,0)) ∧ (∀ z : S2, G (z,1) = (z,1)) ∧
      (∀ z : S2, (fun q => Q (G q)) =ᶠ[𝓝 (z,0)] (fun q => P₀ (q.1,1+q.2))) ∧
      ∀ z : S2, (fun q => Q (G q)) =ᶠ[𝓝 (z,1)] (fun q => P₁ (q.1,2-q.2)) := by
  let B : Set SphereCylinder := univ ×ˢ Icc (0 : ℝ) 1
  let R := reverseCylinder
  have hR : R '' B = B := reverseCylinder_band
  obtain ⟨r₀,hr₀,F₀,hF₀,hF₀zero,hF₀fix,hF₀band⟩ :=
    exists_slab_collar_matching_of_boundary_intersection P₀ Q hP₀ hQ hzero hmeet₀
  let Q₀ := F₀.toPartialDiffeomorph.trans Q
  have hQ₀ : B ⊆ Q₀.source := fun q hq =>
    ⟨mem_univ _,hQ (hF₀band ▸ mem_image_of_mem F₀ hq)⟩
  have hQ₀i : Q₀ '' B = Q '' B := by
    calc
      _ = Q '' (F₀ '' B) := by rw [image_image]; rfl
      _ = _ := by rw [hF₀band]
  let A := R.toPartialDiffeomorph.trans Q₀
  have hA : B ⊆ A.source := fun q hq =>
    ⟨mem_univ _,hQ₀ (hR ▸ mem_image_of_mem R hq)⟩
  have hAi : A '' B = Q '' B := by
    calc
      _ = Q₀ '' (R '' B) := by rw [image_image]; rfl
      _ = _ := by rw [hR,hQ₀i]
  have hA0 (z : S2) : A (z,0) = P₁ (z,1) := by
    change Q (F₀ (R (z,0))) = _
    rw [reverseCylinder_apply,sub_zero,hF₀fix _ (by norm_num),hone]
  obtain ⟨r₁,hr₁,F₁,hF₁,hF₁zero,hF₁fix,hF₁band⟩ :=
    exists_slab_collar_matching_of_boundary_intersection P₁ A hP₁ hA hA0 (by
      rw [hAi]
      exact hmeet₁)
  let U := (R.trans F₁).trans R
  let G := U.trans F₀
  have hUb : U '' B = B := by
    calc
      _ = R '' (F₁ '' (R '' B)) := by simp only [image_image]; rfl
      _ = _ := by rw [hR,hF₁band,hR]
  have hGb : G '' B = B := by
    calc
      _ = F₀ '' (U '' B) := by rw [image_image]; rfl
      _ = _ := by rw [hUb,hF₀band]
  have hUfix (q : SphereCylinder) (hq : q.2 ≤ 1/2) : U q = q := by
    change R (F₁ (R q)) = q
    rw [hF₁fix _ (by rw [reverseCylinder_apply]; change (1/2:ℝ) ≤ 1-q.2; linarith),reverseCylinder_involutive]
  refine ⟨G,hGb,?_,?_,?_,?_⟩
  · intro z
    change F₀ (U (z,0)) = _
    rw [hUfix _ (by norm_num),hF₀zero]
  · intro z
    change F₀ (R (F₁ (R (z,1)))) = _
    have hR1 : R (z,1) = (z,0) := by rw [reverseCylinder_apply,sub_self]
    rw [hR1,hF₁zero,reverseCylinder_apply,sub_zero,hF₀fix _ (by norm_num)]
  · intro z
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
      (Metric.ball_mem_nhds (0 : ℝ) (lt_min hr₀ (by norm_num : (0 : ℝ)<1/2)))] with q hq
    have ht : |q.2| < min r₀ (1/2:ℝ) := by simpa [Real.dist_eq] using hq
    change Q (F₀ (U q)) = _
    rw [hUfix q (by linarith [(abs_lt.mp ht).2,min_le_right r₀ (1/2:ℝ)])]
    exact (hF₀ q (ht.le.trans (min_le_left _ _))).2
  · intro z
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
      (Metric.ball_mem_nhds (1 : ℝ) hr₁)] with q hq
    have ht : |(R q).2| ≤ r₁ := by
      rw [reverseCylinder_apply]
      change |1-q.2| ≤ r₁
      rw [abs_sub_comm]
      exact (show |q.2-1| < r₁ by simpa [Real.dist_eq] using hq).le
    have hh := (hF₁ (R q) ht).2
    change Q (F₀ (R (F₁ (R q)))) = _
    change Q (F₀ (R (F₁ (R q)))) = P₁ ((R q).1,1+(R q).2) at hh
    have he : ((R q).1,1+(R q).2) = (q.1,2-q.2) := by
      rw [reverseCylinder_apply]
      apply Prod.ext
      · rfl
      · dsimp
        ring
    exact hh.trans (congrArg P₁ he)


theorem exists_double_slab_collar_matching
    (a c : PartialDiffeomorph SphereCylinderModel I SphereCylinder M ∞)
    (f : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2)
    (ha : univ ×ˢ Icc (0 : ℝ) 1 ⊆ a.source)
    (hc : univ ×ˢ Icc (0 : ℝ) 1 ⊆ c.source)
    (hzero : ∀ z : S2, a (z,0) = c (z,0))
    (hone : ∀ z : S2, a (z,1) = c (f.symm z,1))
    (hmeet : a '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ c '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆
      c '' (univ ×ˢ ({0} : Set ℝ)) ∪ c '' (univ ×ˢ ({1} : Set ℝ))) :
    ∃ G : SphereCylinder ≃ₘ⟮SphereCylinderModel,SphereCylinderModel⟯ SphereCylinder,
      G '' (univ ×ˢ Icc (0 : ℝ) 1) = univ ×ˢ Icc (0 : ℝ) 1 ∧
      (∀ z : S2, G (z,0) = (z,0)) ∧ (∀ z : S2, G (z,1) = (z,1)) ∧
      (∀ z : S2, (fun q => a (G q)) =ᶠ[𝓝 (z,0)] (fun q => c (q.1,-q.2))) ∧
      ∀ z : S2, (fun q => a (G q)) =ᶠ[𝓝 (z,1)] (fun q => c (f.symm q.1,2-q.2)) := by
  let B : Set SphereCylinder := univ ×ˢ Icc (0 : ℝ) 1
  let R := reverseCylinder
  let P := R.toPartialDiffeomorph.trans c
  have hR : R '' B = B := reverseCylinder_band
  have hP : B ⊆ P.source := by
    intro q hq
    refine ⟨mem_univ _,hc ?_⟩
    change R q ∈ B
    rw [← hR]
    exact mem_image_of_mem R hq
  have hPi : P '' B = c '' B := by
    calc
      _ = c '' (R '' B) := by rw [image_image]; rfl
      _ = _ := by rw [hR]
  have hPends : P '' (univ ×ˢ ({0} : Set ℝ)) ∪ P '' (univ ×ˢ ({1} : Set ℝ)) =
      c '' (univ ×ˢ ({0} : Set ℝ)) ∪ c '' (univ ×ˢ ({1} : Set ℝ)) := by
    have he (t : ℝ) : P '' (univ ×ˢ ({t}:Set ℝ)) = c '' (univ ×ˢ ({1-t}:Set ℝ)) := by
      ext y
      constructor
      · rintro ⟨q,hq,rfl⟩
        exact ⟨R q,⟨mem_univ _,by rw [reverseCylinder_apply]; change 1-q.2 = 1-t; rw [hq.2]⟩,rfl⟩
      · rintro ⟨q,hq,rfl⟩
        refine ⟨R q,⟨mem_univ _,by rw [reverseCylinder_apply]; change 1-q.2 = t; rw [hq.2]; ring⟩,?_⟩
        change c (R (R q)) = c q
        rw [reverseCylinder_involutive]
    rw [he,he]
    norm_num [union_comm]
  have hPzero (z:S2) : a (z,0) = P (z,1) := by
    change a (z,0) = c (R (z,1))
    rw [reverseCylinder_apply,sub_self,hzero]
  let D := f.symm.prodCongr (Diffeomorph.refl 𝓘(ℝ) ℝ ∞)
  let C := D.toPartialDiffeomorph.trans c
  have hDb : D '' B = B := by
    ext q
    constructor
    · rintro ⟨p,hp,rfl⟩
      exact ⟨mem_univ _,hp.2⟩
    · intro hq
      exact ⟨(f q.1,q.2),⟨mem_univ _,hq.2⟩,Prod.ext (f.symm_apply_apply _) rfl⟩
  have hC : B ⊆ C.source := by
    intro q hq
    refine ⟨mem_univ _,hc ?_⟩
    change D q ∈ B
    rw [← hDb]
    exact mem_image_of_mem D hq
  have hCi : C '' B = c '' B := by
    calc
      _ = c '' (D '' B) := by rw [image_image]; rfl
      _ = _ := by rw [hDb]
  have hCends : C '' (univ ×ˢ ({0} : Set ℝ)) ∪ C '' (univ ×ˢ ({1} : Set ℝ)) =
      c '' (univ ×ˢ ({0} : Set ℝ)) ∪ c '' (univ ×ˢ ({1} : Set ℝ)) := by
    have he (t : ℝ) : C '' (univ ×ˢ ({t}:Set ℝ)) = c '' (univ ×ˢ ({t}:Set ℝ)) := by
      ext y
      constructor
      · rintro ⟨q,hq,rfl⟩
        exact ⟨D q,⟨mem_univ _,hq.2⟩,rfl⟩
      · rintro ⟨q,hq,rfl⟩
        refine ⟨(f q.1,q.2),⟨mem_univ _,hq.2⟩,?_⟩
        change c (f.symm (f q.1),q.2) = c q
        rw [f.symm_apply_apply]
    rw [he,he]
  obtain ⟨G,hGb,hGzero,hGone,hGlo,hGhi⟩ :=
    exists_two_ended_slab_collar_matching P C a hP hC ha hPzero hone
      (by rw [hPi,hPends,inter_comm]; exact hmeet)
      (by rw [hCi,hCends,inter_comm]; exact hmeet)
  refine ⟨G,hGb,hGzero,hGone,?_,?_⟩
  · intro z
    filter_upwards [hGlo z] with q hq
    change a (G q) = c (R (q.1,1+q.2)) at hq
    rw [reverseCylinder_apply] at hq
    exact hq.trans (congrArg c (by congr 1; ring))
  · exact hGhi

end DifferentialGeometry.Topology.Manifold
