import DifferentialGeometry.Topology.PiecewiseLinear.BallPairSimplex

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem coneSet_empty (p : E) : coneSet p (∅ : Set E) = {p} := by
  ext x
  constructor
  · intro hx
    rcases mem_coneSet_iff.mp hx with rfl | ⟨z, hz, -⟩
    · rfl
    · exact absurd hz (notMem_empty z)
  · intro hx
    rw [mem_singleton_iff.mp hx]
    exact apex_mem_coneSet p ∅

theorem isPLBall_zero_singleton (z : E) : IsPLBall 0 ({z} : Set E) := by
  classical
  have h := isPLBall_convexHull_of_affineIndependent ({z} : Finset E)
    (affineIndependent_of_subsingleton ℝ _) (by simp : ({z} : Finset E).card = 0 + 1)
  rwa [Finset.coe_singleton, convexHull_singleton] at h

theorem isPLBallPair_convexHull_singleton_of_mem_openSimplex {n : ℕ} {T : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) (hcard : T.card = n + 2) {p : E}
    (hp : p ∈ openSimplex T) :
    IsPLBallPair n 0 (convexHull ℝ (T : Set E)) {p} := by
  classical
  have h2 : 2 ≤ T.card := by omega
  have hfin : Finite (simplexBoundary T hT).faces := (simplexBoundary_faces_finite T hT).to_subtype
  have hL : IsConeBase p (simplexBoundary T hT) := isConeBase_simplexBoundary hT h2 hp
  have hsph : IsPLSphere n (simplexBoundary T hT).space := by
    rw [simplexBoundary_space T hT h2]
    exact isPLSphere_biUnion_erase T hT hcard
  have hbotspace : (⊥ : Geometry.SimplicialComplex ℝ E).space = ∅ :=
    Geometry.SimplicialComplex.space_bot
  have hball : IsPLBall 0 (coneSet p (⊥ : Geometry.SimplicialComplex ℝ E).space) := by
    rw [hbotspace, coneSet_empty]
    exact isPLBall_zero_singleton p
  have hpair := isPLBallPair_coneSet hL bot_le hsph hball
  rwa [hbotspace, coneSet_empty, ← coneComplex_space_eq_coneSet hL,
    coneComplex_simplexBoundary_space hT h2 hp] at hpair

omit [FiniteDimensional ℝ E] in
theorem convexHull_insert_inter_hyperplane [DecidableEq E] {F : Finset E} {a : E} {r : ℝ}
    (ℓ : E →ₗ[ℝ] ℝ) (hF : ∀ v ∈ F, ℓ v = r) (ha : ℓ a ≠ r) :
    convexHull ℝ ((insert a F : Finset E) : Set E) ∩ {x : E | ℓ x = r} =
      convexHull ℝ (F : Set E) := by
  have haF : a ∉ F := fun h => ha (hF a h)
  have hFr : convexHull ℝ (F : Set E) ⊆ {x : E | ℓ x = r} :=
    convexHull_min (fun v hv => hF v hv) (convex_hyperplane ℓ.isLinear r)
  apply Subset.antisymm
  · rintro x ⟨hxa, hx0⟩
    simp only [Set.mem_ofPred_eq] at hx0
    rcases exists_combo_of_mem_convexHull_insert haF hxa with rfl | ⟨z, hz, s, hs, hs1, rfl⟩
    · exact absurd hx0 ha
    · have hz0 : ℓ z = r := hFr hz
      have hval : ℓ (a + s • (z - a)) = (1 - s) * ℓ a + s * r := by
        rw [map_add, map_smul, map_sub, hz0, smul_eq_mul]
        ring
      rw [hval] at hx0
      have hfac : (1 - s) * (ℓ a - r) = 0 := by linear_combination hx0
      rcases mul_eq_zero.mp hfac with h | h
      · have hs' : s = 1 := by linarith
        subst hs'
        rw [one_smul, add_sub_cancel]
        exact hz
      · exact absurd (by linarith : ℓ a = r) ha
  · exact subset_inter (convexHull_mono (Finset.coe_subset.mpr (Finset.subset_insert a F))) hFr

omit [FiniteDimensional ℝ E] in
theorem convexHull_insert_subset_halfSpace_le [DecidableEq E] {F : Finset E} {a : E} {r : ℝ}
    (ℓ : E →ₗ[ℝ] ℝ) (hF : ∀ v ∈ F, ℓ v = r) (ha : ℓ a ≤ r) :
    convexHull ℝ ((insert a F : Finset E) : Set E) ⊆ {x : E | ℓ x ≤ r} := by
  refine convexHull_min ?_ (convex_halfSpace_le ℓ.isLinear r)
  intro v hv
  rw [Finset.coe_insert, Set.mem_insert_iff] at hv
  rcases hv with rfl | hv
  · exact ha
  · exact (hF v hv).le

omit [FiniteDimensional ℝ E] in
theorem convexHull_insert_subset_halfSpace_ge [DecidableEq E] {F : Finset E} {b : E} {r : ℝ}
    (ℓ : E →ₗ[ℝ] ℝ) (hF : ∀ v ∈ F, ℓ v = r) (hb : r ≤ ℓ b) :
    convexHull ℝ ((insert b F : Finset E) : Set E) ⊆ {x : E | r ≤ ℓ x} := by
  refine convexHull_min ?_ (convex_halfSpace_ge ℓ.isLinear r)
  intro v hv
  rw [Finset.coe_insert, Set.mem_insert_iff] at hv
  rcases hv with rfl | hv
  · exact hb
  · exact (hF v hv).ge

omit [FiniteDimensional ℝ E] in
theorem convexHull_insert_inter_convexHull_insert_of_separating [DecidableEq E] {F : Finset E}
    {a b : E} {r : ℝ} (ℓ : E →ₗ[ℝ] ℝ) (hF : ∀ v ∈ F, ℓ v = r) (ha : ℓ a < r) (hb : r < ℓ b) :
    convexHull ℝ ((insert a F : Finset E) : Set E) ∩
        convexHull ℝ ((insert b F : Finset E) : Set E) = convexHull ℝ (F : Set E) := by
  apply Subset.antisymm
  · rintro x ⟨hxa, hxb⟩
    have hx0 : ℓ x = r :=
      le_antisymm (convexHull_insert_subset_halfSpace_le ℓ hF ha.le hxa)
        (convexHull_insert_subset_halfSpace_ge ℓ hF hb.le hxb)
    exact (convexHull_insert_inter_hyperplane ℓ hF (ne_of_lt ha)).subset ⟨hxa, hx0⟩
  · exact subset_inter (convexHull_mono (Finset.coe_subset.mpr (Finset.subset_insert a F)))
      (convexHull_mono (Finset.coe_subset.mpr (Finset.subset_insert b F)))

omit [FiniteDimensional ℝ E] in
theorem convexHull_insert_union_convexHull_insert_of_midpoint [DecidableEq E] {F : Finset E}
    {c d m : E} (hm : c + d = m + m) (hcF : c ∉ F) (hdF : d ∉ F) (hmF : m ∉ F) (hcm : c ≠ m)
    (hdm : d ≠ m) (hcd : c ≠ d) :
    convexHull ℝ ((insert c (insert m F) : Finset E) : Set E) ∪
        convexHull ℝ ((insert d (insert m F) : Finset E) : Set E) =
      convexHull ℝ ((insert c (insert d F) : Finset E) : Set E) := by
  have hhalf : (1 / 2 : ℝ) • c + (1 / 2 : ℝ) • d = m := by
    rw [← smul_add, hm, ← two_smul ℝ m, smul_smul]
    norm_num
  have hmseg : m ∈ convexHull ℝ ((insert c (insert d F) : Finset E) : Set E) := by
    rw [← hhalf]
    exact (convex_convexHull ℝ _) (subset_convexHull ℝ _ (by simp))
      (subset_convexHull ℝ _ (by simp)) (by norm_num) (by norm_num) (by norm_num)
  have h2 : ∀ t : ℝ, (2 * t) • m = t • c + t • d := by
    intro t
    rw [mul_comm, mul_smul, two_smul, ← hm, smul_add]
  have hside : ∀ e : E, e = c ∨ e = d →
      convexHull ℝ ((insert e (insert m F) : Finset E) : Set E) ⊆
        convexHull ℝ ((insert c (insert d F) : Finset E) : Set E) := by
    intro e he
    refine convexHull_min ?_ (convex_convexHull ℝ _)
    intro v hv
    rw [Finset.coe_insert, Finset.coe_insert, Set.mem_insert_iff, Set.mem_insert_iff] at hv
    rcases hv with rfl | rfl | hv
    · refine subset_convexHull ℝ _ ?_
      simp only [Finset.coe_insert, Set.mem_insert_iff]
      rcases he with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · exact hmseg
    · refine subset_convexHull ℝ _ ?_
      simp only [Finset.coe_insert, Set.mem_insert_iff]
      exact Or.inr (Or.inr hv)
  refine Subset.antisymm (union_subset (hside c (Or.inl rfl)) (hside d (Or.inr rfl))) ?_
  intro x hx
  obtain ⟨w, hw0, hw1, hwx⟩ := mem_convexHull_iff_exists_weights.mp hx
  have hcni : c ∉ insert d F := by simp [hcd, hcF]
  rw [Finset.sum_insert hcni, Finset.sum_insert hdF] at hw1 hwx
  have hcmi : c ∉ insert m F := by simp [hcm, hcF]
  have hdmi : d ∉ insert m F := by simp [hdm, hdF]
  have hwc : 0 ≤ w c := hw0 c (by simp)
  have hwd : 0 ≤ w d := hw0 d (by simp)
  have hwF : ∀ v ∈ F, 0 ≤ w v := fun v hv => hw0 v (by simp [hv])
  rcases le_total (w d) (w c) with h | h
  · have hcongr : ∀ v ∈ F,
        (if v = c then w c - w d else if v = m then 2 * w d else w v) = w v := by
      intro v hv
      rw [if_neg (fun hh : v = c => hcF (hh ▸ hv)), if_neg (fun hh : v = m => hmF (hh ▸ hv))]
    refine Or.inl (mem_convexHull_iff_exists_weights.mpr
      ⟨fun v => if v = c then w c - w d else if v = m then 2 * w d else w v, ?_, ?_, ?_⟩)
    · intro v hv
      dsimp only
      split_ifs with h1 h2
      · linarith
      · linarith
      · rw [Finset.mem_insert, Finset.mem_insert] at hv
        rcases hv with rfl | rfl | hv
        · exact absurd rfl h1
        · exact absurd rfl h2
        · exact hwF v hv
    · rw [Finset.sum_insert hcmi, Finset.sum_insert hmF, if_pos rfl, if_neg (Ne.symm hcm),
        if_pos rfl, Finset.sum_congr rfl hcongr]
      linarith
    · rw [Finset.sum_insert hcmi, Finset.sum_insert hmF]
      dsimp only
      rw [if_pos rfl, if_neg (Ne.symm hcm), if_pos rfl,
        Finset.sum_congr rfl (fun v hv => by rw [hcongr v hv]), h2 (w d), ← hwx]
      module
  · have hcongr : ∀ v ∈ F,
        (if v = d then w d - w c else if v = m then 2 * w c else w v) = w v := by
      intro v hv
      rw [if_neg (fun hh : v = d => hdF (hh ▸ hv)), if_neg (fun hh : v = m => hmF (hh ▸ hv))]
    refine Or.inr (mem_convexHull_iff_exists_weights.mpr
      ⟨fun v => if v = d then w d - w c else if v = m then 2 * w c else w v, ?_, ?_, ?_⟩)
    · intro v hv
      dsimp only
      split_ifs with h1 h2
      · linarith
      · linarith
      · rw [Finset.mem_insert, Finset.mem_insert] at hv
        rcases hv with rfl | rfl | hv
        · exact absurd rfl h1
        · exact absurd rfl h2
        · exact hwF v hv
    · rw [Finset.sum_insert hdmi, Finset.sum_insert hmF, if_pos rfl, if_neg (Ne.symm hdm),
        if_pos rfl, Finset.sum_congr rfl hcongr]
      linarith
    · rw [Finset.sum_insert hdmi, Finset.sum_insert hmF]
      dsimp only
      rw [if_pos rfl, if_neg (Ne.symm hdm), if_pos rfl,
        Finset.sum_congr rfl (fun v hv => by rw [hcongr v hv]), h2 (w c), ← hwx]
      module

end DifferentialGeometry.Topology.PiecewiseLinear
