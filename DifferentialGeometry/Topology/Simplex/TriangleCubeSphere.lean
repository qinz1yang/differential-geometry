import DifferentialGeometry.Topology.Simplex.CubeParametrization
import DifferentialGeometry.Topology.Simplex.BoundaryRetraction
import DifferentialGeometry.Topology.Homotopy.CubeSphereProjection

noncomputable section

open scoped unitInterval

namespace DifferentialGeometry.Simplex

theorem triangleJoin_surjective : Function.Surjective triangleJoin := by
  intro p
  have hp0 := p.property.1 0
  have hp1 := p.property.1 1
  have hp2 := p.property.1 2
  have hsum : p.val 0 + p.val 1 + p.val 2 = 1 := by
    simpa [Fin.sum_univ_succ, add_assoc] using p.property.2
  by_cases hzero : p.val 1 + p.val 2 = 0
  · refine ⟨(0, 0), ?_⟩
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [triangleJoin] <;> linarith
  · have hpos : 0 < p.val 1 + p.val 2 := lt_of_le_of_ne (add_nonneg hp1 hp2) (Ne.symm hzero)
    let s : unitInterval := ⟨p.val 1 + p.val 2, add_nonneg hp1 hp2, by linarith⟩
    let t : unitInterval := ⟨p.val 2 / (p.val 1 + p.val 2), div_nonneg hp2 hpos.le,
      (div_le_one hpos).2 (by linarith)⟩
    refine ⟨(s, t), ?_⟩
    apply Subtype.ext
    funext i
    fin_cases i
    · simp [triangleJoin, s]
      linarith
    · change (p.val 1 + p.val 2) * (1 - p.val 2 / (p.val 1 + p.val 2)) = p.val 1
      field_simp
      ring
    · change (p.val 1 + p.val 2) * (p.val 2 / (p.val 1 + p.val 2)) = p.val 2
      field_simp

theorem triangleJoin_eq_iff (p q : unitInterval × unitInterval) :
    triangleJoin p = triangleJoin q ↔ p = q ∨ p.1 = 0 ∧ q.1 = 0 := by
  constructor
  · intro h
    have hfirst : (p.1 : ℝ) = q.1 := by
      have hh := congrArg (fun z : stdSimplex ℝ (Fin 3) => z.val 0) h
      simp only [triangleJoin, ContinuousMap.coe_mk, Matrix.cons_val_zero] at hh
      linarith
    have hs : p.1 = q.1 := Subtype.ext hfirst
    by_cases hp : p.1 = 0
    · exact Or.inr ⟨hp, hs ▸ hp⟩
    · left
      refine Prod.ext hs ?_
      apply Subtype.ext
      have hmul := congrArg (fun z : stdSimplex ℝ (Fin 3) => z.val 2) h
      simp only [triangleJoin, ContinuousMap.coe_mk, Matrix.cons_val_two, hfirst] at hmul
      exact (mul_left_cancel₀ (show (q.1 : ℝ) ≠ 0 from fun hh => hp (hs.trans (Subtype.ext hh)))) hmul
  · rintro (rfl | ⟨hp, hq⟩)
    · rfl
    · rcases p with ⟨s, t⟩
      rcases q with ⟨u, v⟩
      simp only at hp hq
      subst s
      subst u
      simp

theorem isQuotientMap_triangleJoin : _root_.Topology.IsQuotientMap triangleJoin :=
  .of_surjective_continuous triangleJoin_surjective triangleJoin.continuous

theorem triangleJoin_mem_boundary_iff (p : unitInterval × unitInterval) :
    triangleJoin p ∈ boundary (Fin 3) ↔ ![p.1, p.2] ∈ Cube.boundary (Fin 2) := by
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    · refine ⟨0, Or.inr ?_⟩
      change p.1 = 1
      apply Subtype.ext
      change 1 - (p.1 : ℝ) = 0 at hi
      change (p.1 : ℝ) = 1
      linarith
    · change (p.1 : ℝ) * (1 - (p.2 : ℝ)) = 0 at hi
      rcases mul_eq_zero.mp hi with hs | ht
      · exact ⟨0, Or.inl (Subtype.ext hs)⟩
      · refine ⟨1, Or.inr ?_⟩
        change p.2 = 1
        apply Subtype.ext
        change (p.2 : ℝ) = 1
        linarith
    · change (p.1 : ℝ) * (p.2 : ℝ) = 0 at hi
      rcases mul_eq_zero.mp hi with hs | ht
      · exact ⟨0, Or.inl (Subtype.ext hs)⟩
      · exact ⟨1, Or.inl (Subtype.ext ht)⟩
  · rintro ⟨i, hi⟩
    fin_cases i
    · change p.1 = 0 ∨ p.1 = 1 at hi
      rcases hi with hs | hs
      · exact ⟨2, by simp [triangleJoin, hs]⟩
      · exact ⟨0, by simp [triangleJoin, hs]⟩
    · change p.2 = 0 ∨ p.2 = 1 at hi
      rcases hi with ht | ht
      · exact ⟨2, by simp [triangleJoin, ht]⟩
      · exact ⟨1, by simp [triangleJoin, ht]⟩

private def squareSphereProjection :
    C(unitInterval × unitInterval, Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) where
  toFun p := Topology.cubeSphereProjection 1 ![p.1, p.2]
  continuous_toFun := by
    apply Continuous.comp (Topology.cubeSphereProjection 1).continuous
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop

private theorem squareSphereProjection_factors :
    Function.FactorsThrough squareSphereProjection triangleJoin := by
  intro p q h
  rcases (triangleJoin_eq_iff p q).mp h with heq | ⟨hp, hq⟩
  · rw [heq]
  · change Topology.cubeSphereProjection 1 ![p.1, p.2] =
        Topology.cubeSphereProjection 1 ![q.1, q.2]
    rw [Topology.cubeSphereProjection_boundary 1 _ ⟨0, Or.inl hp⟩,
      Topology.cubeSphereProjection_boundary 1 _ ⟨0, Or.inl hq⟩]

def triangleCubeSphereMap :
    C(stdSimplex ℝ (Fin 3), Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  isQuotientMap_triangleJoin.lift squareSphereProjection squareSphereProjection_factors

@[simp] theorem triangleCubeSphereMap_triangleJoin (p : unitInterval × unitInterval) :
    triangleCubeSphereMap (triangleJoin p) = Topology.cubeSphereProjection 1 ![p.1, p.2] := by
  exact congrArg (fun f : C(unitInterval × unitInterval,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) => f p)
    (isQuotientMap_triangleJoin.lift_comp squareSphereProjection squareSphereProjection_factors)

theorem triangleCubeSphereMap_boundary (p : stdSimplex ℝ (Fin 3))
    (hp : p ∈ boundary (Fin 3)) : triangleCubeSphereMap p = Topology.cubeSphereBasepoint 1 := by
  obtain ⟨q, rfl⟩ := triangleJoin_surjective p
  rw [triangleCubeSphereMap_triangleJoin]
  exact Topology.cubeSphereProjection_boundary 1 _ ((triangleJoin_mem_boundary_iff q).mp hp)

end DifferentialGeometry.Simplex
