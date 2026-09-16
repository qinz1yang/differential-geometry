import DifferentialGeometry.Topology.PiecewiseLinear.HeightIndex

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_embedding_heightSingularPoints_of_sdiff_subset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S T : Set E} {f g : E → ℝ} {a b : E}
    (hb : b ∈ heightSingularPoints T g)
    (hsub : heightSingularPoints S f \ {a} ⊆ heightSingularPoints T g \ {b}) :
    ∃ e : heightSingularPoints S f ↪ heightSingularPoints T g,
      (∀ q : heightSingularPoints S f, (q : E) = a → (e q : E) = b) ∧
      ∀ q : heightSingularPoints S f, (q : E) ≠ a → (e q : E) = q := by
  classical
  let φ : heightSingularPoints S f → heightSingularPoints T g := fun q =>
    if hq : (q : E) = a then ⟨b, hb⟩
    else ⟨q, (hsub ⟨q.property, by simpa only [mem_singleton_iff] using hq⟩).1⟩
  have hφ : Function.Injective φ := by
    intro q r hqr
    apply Subtype.ext
    by_cases hq : (q : E) = a
    · by_cases hr : (r : E) = a
      · exact hq.trans hr.symm
      · have hrange := hsub
          ⟨r.property, by simpa only [mem_singleton_iff] using hr⟩
        have hv : b = (r : E) := calc
          b = (φ q : E) := by simp only [φ, dif_pos hq]
          _ = (φ r : E) := congrArg Subtype.val hqr
          _ = r := by simp only [φ, dif_neg hr]
        exfalso
        apply hrange.2
        rw [mem_singleton_iff]
        exact hv.symm
    · by_cases hr : (r : E) = a
      · have hqrange := hsub
          ⟨q.property, by simpa only [mem_singleton_iff] using hq⟩
        have hv : (q : E) = b := calc
          (q : E) = (φ q : E) := by simp only [φ, dif_neg hq]
          _ = (φ r : E) := congrArg Subtype.val hqr
          _ = b := by simp only [φ, dif_pos hr]
        exfalso
        apply hqrange.2
        rw [mem_singleton_iff]
        exact hv
      · calc
          (q : E) = (φ q : E) := by simp only [φ, dif_neg hq]
          _ = (φ r : E) := congrArg Subtype.val hqr
          _ = r := by simp only [φ, dif_neg hr]
  let e : heightSingularPoints S f ↪ heightSingularPoints T g := ⟨φ, hφ⟩
  refine ⟨e, ?_, ?_⟩
  · intro q hq
    change (φ q : E) = b
    simp only [φ, dif_pos hq]
  · intro q hq
    change (φ q : E) = q
    simp only [φ, dif_neg hq]

end DifferentialGeometry.Topology.PiecewiseLinear
