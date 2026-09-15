import DifferentialGeometry.Topology.Simplex.CubeParametrization
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Separation.Hausdorff

noncomputable section

open scoped unitInterval

namespace DifferentialGeometry.Simplex

private def simplexPairRatio (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : unitInterval :=
  ⟨b / (a + b), div_nonneg hb (add_nonneg ha hb), by
    by_cases h : a + b = 0
    · simp [h]
    · exact (div_le_one (lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm h))).mpr (by linarith)⟩

private theorem simplexPairRatio_mul (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) * (simplexPairRatio a b ha hb : ℝ) = b := by
  by_cases h : a + b = 0
  · have hb0 : b = 0 := by linarith
    simp [simplexPairRatio, hb0]
  · exact mul_div_cancel₀ b h

private theorem simplexPairRatio_compl_mul (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) * (1 - (simplexPairRatio a b ha hb : ℝ)) = a := by
  rw [mul_sub, mul_one, simplexPairRatio_mul]
  ring

theorem tetrahedronJoin_surjective : Function.Surjective tetrahedronJoin := by
  intro p
  have hsum : p.val 0 + p.val 1 + p.val 2 + p.val 3 = 1 := by
    simpa only [Fin.sum_univ_four] using p.property.2
  let s : unitInterval := ⟨p.val 2 + p.val 3,
    add_nonneg (p.property.1 2) (p.property.1 3), by
      linarith [p.property.1 0, p.property.1 1]⟩
  let t := simplexPairRatio (p.val 0) (p.val 1) (p.property.1 0) (p.property.1 1)
  let u := simplexPairRatio (p.val 2) (p.val 3) (p.property.1 2) (p.property.1 3)
  have hs : 1 - (s : ℝ) = p.val 0 + p.val 1 := by dsimp [s]; linarith
  refine ⟨(s, t, u), ?_⟩
  apply Subtype.ext
  funext i
  fin_cases i
  · change (1 - (s : ℝ)) * (1 - (t : ℝ)) = _
    rw [hs]
    exact simplexPairRatio_compl_mul _ _ _ _
  · change (1 - (s : ℝ)) * (t : ℝ) = _
    rw [hs]
    exact simplexPairRatio_mul _ _ _ _
  · change (s : ℝ) * (1 - (u : ℝ)) = _
    exact simplexPairRatio_compl_mul _ _ _ _
  · change (s : ℝ) * (u : ℝ) = _
    exact simplexPairRatio_mul _ _ _ _

theorem tetrahedronJoin_isQuotientMap : Topology.IsQuotientMap tetrahedronJoin :=
  Topology.IsQuotientMap.of_surjective_continuous tetrahedronJoin_surjective
    tetrahedronJoin.continuous

variable {X : Type*} [TopologicalSpace X]

theorem tetrahedronJoin_factorsThrough (G : C(unitInterval × unitInterval × unitInterval, X))
    (hzero : ∀ t u v, G (0, t, u) = G (0, t, v))
    (hone : ∀ t u v, G (1, t, u) = G (1, v, u)) :
    Function.FactorsThrough G tetrahedronJoin := by
  rintro ⟨s, t, u⟩ ⟨r, v, w⟩ h
  have h2 := congrArg (fun p : stdSimplex ℝ (Fin 4) => p.val 2) h
  have h3 := congrArg (fun p : stdSimplex ℝ (Fin 4) => p.val 3) h
  change (s : ℝ) * (1 - (u : ℝ)) = (r : ℝ) * (1 - (w : ℝ)) at h2
  change (s : ℝ) * (u : ℝ) = (r : ℝ) * (w : ℝ) at h3
  have hsr : s = r := Subtype.ext (by nlinarith [h2, h3])
  subst r
  by_cases hs0 : s = 0
  · subst s
    have h1 := congrArg (fun p : stdSimplex ℝ (Fin 4) => p.val 1) h
    change (1 - (0 : ℝ)) * (t : ℝ) = (1 - (0 : ℝ)) * (v : ℝ) at h1
    have htv : t = v := Subtype.ext (by simpa using h1)
    subst v
    exact hzero t u w
  by_cases hs1 : s = 1
  · subst s
    have huw : u = w := Subtype.ext (by simpa using h3)
    subst w
    exact hone t u v
  have hs0' : (s : ℝ) ≠ 0 := fun h => hs0 (Subtype.ext h)
  have hs1' : 1 - (s : ℝ) ≠ 0 := by
    intro hzero'
    apply hs1
    apply Subtype.ext
    dsimp
    linarith
  have huw : u = w := Subtype.ext (mul_left_cancel₀ hs0' h3)
  have h1 := congrArg (fun p : stdSimplex ℝ (Fin 4) => p.val 1) h
  change (1 - (s : ℝ)) * (t : ℝ) = (1 - (s : ℝ)) * (v : ℝ) at h1
  have htv : t = v := Subtype.ext (mul_left_cancel₀ hs1' h1)
  subst v
  subst w
  rfl

def tetrahedronJoinDesc (G : C(unitInterval × unitInterval × unitInterval, X))
    (hzero : ∀ t u v, G (0, t, u) = G (0, t, v))
    (hone : ∀ t u v, G (1, t, u) = G (1, v, u)) :
    C(stdSimplex ℝ (Fin 4), X) :=
  tetrahedronJoin_isQuotientMap.lift G (tetrahedronJoin_factorsThrough G hzero hone)

@[simp] theorem tetrahedronJoinDesc_comp (G : C(unitInterval × unitInterval × unitInterval, X))
    (hzero : ∀ t u v, G (0, t, u) = G (0, t, v))
    (hone : ∀ t u v, G (1, t, u) = G (1, v, u)) :
    (tetrahedronJoinDesc G hzero hone).comp tetrahedronJoin = G :=
  tetrahedronJoin_isQuotientMap.lift_comp G (tetrahedronJoin_factorsThrough G hzero hone)

@[simp] theorem tetrahedronJoinDesc_apply (G : C(unitInterval × unitInterval × unitInterval, X))
    (hzero : ∀ t u v, G (0, t, u) = G (0, t, v))
    (hone : ∀ t u v, G (1, t, u) = G (1, v, u)) (p : unitInterval × unitInterval × unitInterval) :
    tetrahedronJoinDesc G hzero hone (tetrahedronJoin p) = G p :=
  congrArg (fun f => f p) (tetrahedronJoinDesc_comp G hzero hone)

end DifferentialGeometry.Simplex
