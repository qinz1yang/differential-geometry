import DifferentialGeometry.Topology.PiecewiseLinear.Pasting

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def upperPrismTriangle : Set (ℝ × ℝ) := {z | 0 ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ 1}

def lowerPrismTriangle : Set (ℝ × ℝ) := {z | 0 ≤ z.2 ∧ z.2 ≤ z.1 ∧ z.1 ≤ 1}

theorem upperPrismTriangle_subset : upperPrismTriangle ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
  rintro ⟨l, t⟩ ⟨h1, h2, h3⟩
  exact ⟨⟨h1, by linarith⟩, ⟨by linarith, h3⟩⟩

theorem lowerPrismTriangle_subset : lowerPrismTriangle ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
  rintro ⟨l, t⟩ ⟨h1, h2, h3⟩
  exact ⟨⟨by linarith, h3⟩, ⟨h1, by linarith⟩⟩

theorem isHPolytope_upperPrismTriangle : IsHPolytope upperPrismTriangle := by
  refine ⟨?_, Fin 3, inferInstance,
    ![-(LinearMap.fst ℝ ℝ ℝ), LinearMap.fst ℝ ℝ ℝ - LinearMap.snd ℝ ℝ ℝ, LinearMap.snd ℝ ℝ ℝ],
    ![0, 0, 1], ?_⟩
  · refine IsCompact.of_isClosed_subset ((isCompact_Icc).prod isCompact_Icc) ?_
      upperPrismTriangle_subset
    have : upperPrismTriangle = {z : ℝ × ℝ | 0 ≤ z.1} ∩ {z : ℝ × ℝ | z.1 ≤ z.2} ∩
        {z : ℝ × ℝ | z.2 ≤ 1} := by
      ext z; exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩
    rw [this]
    exact ((isClosed_le continuous_const continuous_fst).inter
      (isClosed_le continuous_fst continuous_snd)).inter
      (isClosed_le continuous_snd continuous_const)
  · ext z
    constructor
    · rintro ⟨h1, h2, h3⟩ i
      fin_cases i <;> simp <;> linarith
    · intro h
      have h0 := h 0
      have h1 := h 1
      have h2 := h 2
      simp at h0 h1 h2
      exact ⟨by linarith, by linarith, by linarith⟩

theorem isHPolytope_lowerPrismTriangle : IsHPolytope lowerPrismTriangle := by
  refine ⟨?_, Fin 3, inferInstance,
    ![-(LinearMap.snd ℝ ℝ ℝ), LinearMap.snd ℝ ℝ ℝ - LinearMap.fst ℝ ℝ ℝ, LinearMap.fst ℝ ℝ ℝ],
    ![0, 0, 1], ?_⟩
  · refine IsCompact.of_isClosed_subset ((isCompact_Icc).prod isCompact_Icc) ?_
      lowerPrismTriangle_subset
    have : lowerPrismTriangle = {z : ℝ × ℝ | 0 ≤ z.2} ∩ {z : ℝ × ℝ | z.2 ≤ z.1} ∩
        {z : ℝ × ℝ | z.1 ≤ 1} := by
      ext z; exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩
    rw [this]
    exact ((isClosed_le continuous_const continuous_snd).inter
      (isClosed_le continuous_snd continuous_fst)).inter
      (isClosed_le continuous_fst continuous_const)
  · ext z
    constructor
    · rintro ⟨h1, h2, h3⟩ i
      fin_cases i <;> simp <;> linarith
    · intro h
      have h0 := h 0
      have h1 := h 1
      have h2 := h 2
      simp at h0 h1 h2
      exact ⟨by linarith, by linarith, by linarith⟩

theorem union_prismTriangle :
    upperPrismTriangle ∪ lowerPrismTriangle = Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
  refine Subset.antisymm (union_subset upperPrismTriangle_subset lowerPrismTriangle_subset) ?_
  rintro ⟨l, t⟩ ⟨⟨hl0, hl1⟩, ht0, ht1⟩
  rcases le_total l t with h | h
  · exact Or.inl ⟨hl0, h, ht1⟩
  · exact Or.inr ⟨ht0, h, hl1⟩

theorem fst_eq_snd_of_mem_inter_prismTriangle {z : ℝ × ℝ}
    (hz : z ∈ upperPrismTriangle ∩ lowerPrismTriangle) : z.1 = z.2 :=
  le_antisymm hz.1.2.1 hz.2.2.1

noncomputable def upperPrismAffine (a c d : F) : (ℝ × ℝ) →ᵃ[ℝ] F :=
  AffineMap.const ℝ (ℝ × ℝ) a +
    ((LinearMap.snd ℝ ℝ ℝ).smulRight (c - a) +
      (LinearMap.fst ℝ ℝ ℝ).smulRight (d - c)).toAffineMap

noncomputable def lowerPrismAffine (a b d : F) : (ℝ × ℝ) →ᵃ[ℝ] F :=
  AffineMap.const ℝ (ℝ × ℝ) a +
    ((LinearMap.fst ℝ ℝ ℝ).smulRight (b - a) +
      (LinearMap.snd ℝ ℝ ℝ).smulRight (d - b)).toAffineMap

theorem upperPrismAffine_apply (a c d : F) (z : ℝ × ℝ) :
    upperPrismAffine a c d z = a + z.2 • (c - a) + z.1 • (d - c) := by
  simp [upperPrismAffine, add_assoc]

theorem lowerPrismAffine_apply (a b d : F) (z : ℝ × ℝ) :
    lowerPrismAffine a b d z = a + z.1 • (b - a) + z.2 • (d - b) := by
  simp [lowerPrismAffine, add_assoc]

open Classical in
noncomputable def prismSquareMap (a b c d : F) : ℝ × ℝ → F :=
  upperPrismTriangle.piecewise (upperPrismAffine a c d) (lowerPrismAffine a b d)

theorem isPiecewiseAffineOn_prismSquareMap (a b c d : F) :
    IsPiecewiseAffineOn (prismSquareMap a b c d) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
  classical
  rw [← union_prismTriangle]
  refine IsPiecewiseAffineOn.piecewise_of_isClosed
    (isPiecewiseAffineOn_of_affine_of_isHPolytope _ isHPolytope_upperPrismTriangle)
    (isPiecewiseAffineOn_of_affine_of_isHPolytope _ isHPolytope_lowerPrismTriangle)
    isHPolytope_upperPrismTriangle.isClosed isHPolytope_lowerPrismTriangle.isClosed ?_
  intro z hz
  have h := fst_eq_snd_of_mem_inter_prismTriangle hz
  rw [upperPrismAffine_apply, lowerPrismAffine_apply, h]
  module

theorem prismSquareMap_bottom (a b c d : F) (l : ℝ) :
    prismSquareMap a b c d (l, 0) = a + l • (b - a) := by
  classical
  by_cases h : ((l, (0 : ℝ)) : ℝ × ℝ) ∈ upperPrismTriangle
  · have hl0 : l = 0 := le_antisymm h.2.1 h.1
    rw [prismSquareMap, Set.piecewise_eq_of_mem _ _ _ h, upperPrismAffine_apply, hl0]
    simp
  · rw [prismSquareMap, Set.piecewise_eq_of_notMem _ _ _ h, lowerPrismAffine_apply]
    simp

theorem prismSquareMap_top (a b c d : F) {l : ℝ} (hl : l ∈ Icc (0 : ℝ) 1) :
    prismSquareMap a b c d (l, 1) = c + l • (d - c) := by
  classical
  have h : ((l, (1 : ℝ)) : ℝ × ℝ) ∈ upperPrismTriangle := ⟨hl.1, hl.2, le_rfl⟩
  rw [prismSquareMap, Set.piecewise_eq_of_mem _ _ _ h, upperPrismAffine_apply]
  simp

theorem prismSquareMap_left (a b c d : F) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    prismSquareMap a b c d (0, t) = a + t • (c - a) := by
  classical
  have h : (((0 : ℝ), t) : ℝ × ℝ) ∈ upperPrismTriangle := ⟨le_rfl, ht.1, ht.2⟩
  rw [prismSquareMap, Set.piecewise_eq_of_mem _ _ _ h, upperPrismAffine_apply]
  simp

theorem prismSquareMap_right (a b c d : F) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    prismSquareMap a b c d (1, t) = b + t • (d - b) := by
  classical
  by_cases h : (((1 : ℝ), t) : ℝ × ℝ) ∈ upperPrismTriangle
  · have ht1 : t = 1 := le_antisymm ht.2 h.2.1
    rw [prismSquareMap, Set.piecewise_eq_of_mem _ _ _ h, upperPrismAffine_apply, ht1]
    simp
  · rw [prismSquareMap, Set.piecewise_eq_of_notMem _ _ _ h, lowerPrismAffine_apply]
    simp

theorem prismSquareMap_mem_convexHull (a b c d : F) {z : ℝ × ℝ}
    (hz : z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :
    prismSquareMap a b c d z ∈ convexHull ℝ ({a, b, c, d} : Set F) := by
  classical
  by_cases h : z ∈ upperPrismTriangle
  · rw [prismSquareMap, Set.piecewise_eq_of_mem _ _ _ h, upperPrismAffine_apply]
    have key : a + z.2 • (c - a) + z.1 • (d - c)
        = ∑ i : Fin 3, ![1 - z.2, z.2 - z.1, z.1] i • ![a, c, d] i := by
      simp [Fin.sum_univ_three]
      module
    rw [key]
    refine (convex_convexHull ℝ _).sum_mem (fun i _ => ?_) ?_ (fun i _ => ?_)
    · fin_cases i <;> simp <;> linarith [h.1, h.2.1, h.2.2]
    · simp [Fin.sum_univ_three]
    · fin_cases i <;> exact subset_convexHull ℝ _ (by simp)
  · rw [prismSquareMap, Set.piecewise_eq_of_notMem _ _ _ h, lowerPrismAffine_apply]
    have hlow : z ∈ lowerPrismTriangle := by
      have := union_prismTriangle ▸ hz
      exact this.resolve_left h
    have key : a + z.1 • (b - a) + z.2 • (d - b)
        = ∑ i : Fin 3, ![1 - z.1, z.1 - z.2, z.2] i • ![a, b, d] i := by
      simp [Fin.sum_univ_three]
      module
    rw [key]
    refine (convex_convexHull ℝ _).sum_mem (fun i _ => ?_) ?_ (fun i _ => ?_)
    · fin_cases i <;> simp <;> linarith [hlow.1, hlow.2.1, hlow.2.2]
    · simp [Fin.sum_univ_three]
    · fin_cases i <;> exact subset_convexHull ℝ _ (by simp)

end DifferentialGeometry.Topology.PiecewiseLinear
