import DifferentialGeometry.Topology.PiecewiseLinear.Gluing
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexComplex

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

section JoinData

variable (E F) in
def joinFst : E → E × F × ℝ := fun v => (v, 0, 0)

variable (E F) in
def joinSnd : F → E × F × ℝ := fun w => (0, w, 1)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem joinFst_injective : Function.Injective (joinFst E F) := fun _ _ h => congrArg Prod.fst h

omit [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem joinSnd_injective : Function.Injective (joinSnd E F) :=
  fun _ _ h => congrArg (fun z : E × F × ℝ => z.2.1) h

theorem glueHeight_joinFst (v : E) : glueHeight E F (joinFst E F v) = 0 := rfl

theorem glueHeight_joinSnd (w : F) : glueHeight E F (joinSnd E F w) = 1 := rfl

theorem glueFst_joinFst (v : E) : glueFst E F (joinFst E F v) = v := rfl

theorem glueSnd_joinSnd (w : F) : glueSnd E F (joinSnd E F w) = w := rfl

theorem joinFst_ne_joinSnd (v : E) (w : F) : joinFst E F v ≠ joinSnd E F w := fun h => by
  have h' := congrArg (glueHeight E F) h
  rw [glueHeight_joinFst, glueHeight_joinSnd] at h'
  exact zero_ne_one h'

theorem sum_smul_joinFst (σ : Finset E) (a : E → ℝ) :
    ∑ v ∈ σ, a v • joinFst E F v = (∑ v ∈ σ, a v • v, 0, 0) := by
  classical
  induction σ using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rfl
  | insert v σ hv ih =>
    rw [Finset.sum_insert hv, Finset.sum_insert hv, ih]
    simp [joinFst]

theorem sum_smul_joinSnd (τ : Finset F) (b : F → ℝ) :
    ∑ w ∈ τ, b w • joinSnd E F w = (0, ∑ w ∈ τ, b w • w, ∑ w ∈ τ, b w) := by
  classical
  induction τ using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rfl
  | insert w τ hw ih =>
    rw [Finset.sum_insert hw, Finset.sum_insert hw, Finset.sum_insert hw, ih]
    simp [joinSnd]

variable [DecidableEq E] [DecidableEq F]

theorem disjoint_image_joinFst_joinSnd (σ : Finset E) (τ : Finset F) :
    Disjoint (σ.image (joinFst E F)) (τ.image (joinSnd E F)) := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨w, -, hw⟩ := Finset.mem_image.mp hz'
  exact joinFst_ne_joinSnd v w hw.symm

theorem mem_convexHull_join_iff (σ : Finset E) (τ : Finset F) {z : E × F × ℝ} :
    z ∈ convexHull ℝ ((σ.image (joinFst E F) ∪ τ.image (joinSnd E F) :
      Finset (E × F × ℝ)) : Set (E × F × ℝ)) ↔
      ∃ (a : E → ℝ) (b : F → ℝ), (∀ v ∈ σ, 0 ≤ a v) ∧ (∀ w ∈ τ, 0 ≤ b w) ∧
        ∑ v ∈ σ, a v + ∑ w ∈ τ, b w = 1 ∧
        z = (∑ v ∈ σ, a v • v, ∑ w ∈ τ, b w • w, ∑ w ∈ τ, b w) := by
  rw [mem_convexHull_iff_exists_weights]
  constructor
  · rintro ⟨c, hc0, hc1, hcz⟩
    refine ⟨fun v => c (joinFst E F v), fun w => c (joinSnd E F w),
      fun v hv => hc0 _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hv)),
      fun w hw => hc0 _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hw)), ?_, ?_⟩
    · rw [← hc1, Finset.sum_union (disjoint_image_joinFst_joinSnd σ τ),
        Finset.sum_image fun _ _ _ _ h => joinFst_injective h,
        Finset.sum_image fun _ _ _ _ h => joinSnd_injective h]
    · rw [← hcz, Finset.sum_union (disjoint_image_joinFst_joinSnd σ τ),
        Finset.sum_image fun _ _ _ _ h => joinFst_injective h,
        Finset.sum_image fun _ _ _ _ h => joinSnd_injective h, sum_smul_joinFst,
        sum_smul_joinSnd]
      simp
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨fun z => if glueHeight E F z = 0 then a (glueFst E F z) else b (glueSnd E F z),
      ?_, ?_, ?_⟩
    · intro u hu
      dsimp only
      rcases Finset.mem_union.mp hu with h | h
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h
        rw [if_pos (glueHeight_joinFst v), glueFst_joinFst]
        exact ha v hv
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp h
        rw [if_neg (by rw [glueHeight_joinSnd]; exact one_ne_zero), glueSnd_joinSnd]
        exact hb w hw
    · rw [Finset.sum_union (disjoint_image_joinFst_joinSnd σ τ),
        Finset.sum_image fun _ _ _ _ h => joinFst_injective h,
        Finset.sum_image fun _ _ _ _ h => joinSnd_injective h, ← hab]
      congr 1
      · exact Finset.sum_congr rfl fun v _ => by
          rw [if_pos (glueHeight_joinFst v), glueFst_joinFst]
      · exact Finset.sum_congr rfl fun w _ => by
          rw [if_neg (by rw [glueHeight_joinSnd]; exact one_ne_zero), glueSnd_joinSnd]
    · rw [Finset.sum_union (disjoint_image_joinFst_joinSnd σ τ),
        Finset.sum_image fun _ _ _ _ h => joinFst_injective h,
        Finset.sum_image fun _ _ _ _ h => joinSnd_injective h]
      dsimp only
      have h1 : ∑ v ∈ σ, (if glueHeight E F (joinFst E F v) = 0 then a (glueFst E F (joinFst E F v))
          else b (glueSnd E F (joinFst E F v))) • joinFst E F v = ∑ v ∈ σ, a v • joinFst E F v :=
        Finset.sum_congr rfl fun v _ => by rw [if_pos (glueHeight_joinFst v), glueFst_joinFst]
      have h2 : ∑ w ∈ τ, (if glueHeight E F (joinSnd E F w) = 0 then a (glueFst E F (joinSnd E F w))
          else b (glueSnd E F (joinSnd E F w))) • joinSnd E F w = ∑ w ∈ τ, b w • joinSnd E F w :=
        Finset.sum_congr rfl fun w _ => by
          rw [if_neg (by rw [glueHeight_joinSnd]; exact one_ne_zero), glueSnd_joinSnd]
      rw [h1, h2, sum_smul_joinFst, sum_smul_joinSnd]
      simp

theorem mem_convexHull_join_of (σ : Finset E) (τ : Finset F) {x : E} {y : F}
    (hx : x ∈ convexHull ℝ (σ : Set E)) (hy : y ∈ convexHull ℝ (τ : Set F)) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((1 - t) • x, t • y, t) ∈ convexHull ℝ ((σ.image (joinFst E F) ∪ τ.image (joinSnd E F) :
      Finset (E × F × ℝ)) : Set (E × F × ℝ)) := by
  obtain ⟨a, ha0, ha1, hax⟩ := mem_convexHull_iff_exists_weights.mp hx
  obtain ⟨b, hb0, hb1, hby⟩ := mem_convexHull_iff_exists_weights.mp hy
  refine (mem_convexHull_join_iff σ τ).mpr ⟨fun v => (1 - t) * a v, fun w => t * b w,
    fun v hv => mul_nonneg (by linarith) (ha0 v hv), fun w hw => mul_nonneg ht0 (hb0 w hw), ?_, ?_⟩
  · rw [← Finset.mul_sum, ← Finset.mul_sum, ha1, hb1]
    ring
  · rw [← hax, ← hby, Finset.smul_sum, Finset.smul_sum, ← Finset.mul_sum, hb1, mul_one]
    congr 1
    · exact Finset.sum_congr rfl fun v _ => by rw [mul_smul]
    · congr 1
      exact Finset.sum_congr rfl fun w _ => by rw [mul_smul]

end JoinData

section JoinComplex

variable [DecidableEq E] [DecidableEq F] (K : Geometry.SimplicialComplex ℝ E)
  (L : Geometry.SimplicialComplex ℝ F)

def joinFaces : Set (Finset (E × F × ℝ)) :=
  {t | ∃ (σ : Finset E) (τ : Finset F), (σ = ∅ ∨ σ ∈ K.faces) ∧ (τ = ∅ ∨ τ ∈ L.faces) ∧
    (σ.Nonempty ∨ τ.Nonempty) ∧ t = σ.image (joinFst E F) ∪ τ.image (joinSnd E F)}

theorem joinFaces_isRelLowerSet : IsRelLowerSet (joinFaces K L) Finset.Nonempty := by
  rintro t ⟨σ, τ, hσ, hτ, hne, rfl⟩
  refine ⟨?_, fun g hgt hg => ?_⟩
  · rcases hne with hne | hne
    · exact (hne.image _).mono Finset.subset_union_left
    · exact (hne.image _).mono Finset.subset_union_right
  · refine ⟨σ.filter fun v => joinFst E F v ∈ g, τ.filter fun w => joinSnd E F w ∈ g, ?_, ?_, ?_,
      ?_⟩
    · rcases (σ.filter fun v => joinFst E F v ∈ g).eq_empty_or_nonempty with h | h
      · exact Or.inl h
      · rcases hσ with rfl | hσ
        · exact absurd h (by simp)
        · exact Or.inr (K.down_closed hσ (Finset.filter_subset _ _) h)
    · rcases (τ.filter fun w => joinSnd E F w ∈ g).eq_empty_or_nonempty with h | h
      · exact Or.inl h
      · rcases hτ with rfl | hτ
        · exact absurd h (by simp)
        · exact Or.inr (L.down_closed hτ (Finset.filter_subset _ _) h)
    · obtain ⟨z, hz⟩ := hg
      rcases Finset.mem_union.mp (hgt hz) with h | h
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h
        exact Or.inl ⟨v, Finset.mem_filter.mpr ⟨hv, hz⟩⟩
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp h
        exact Or.inr ⟨w, Finset.mem_filter.mpr ⟨hw, hz⟩⟩
    · ext z
      constructor
      · intro hz
        rcases Finset.mem_union.mp (hgt hz) with h | h
        · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h
          exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hv, hz⟩))
        · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp h
          exact Finset.mem_union_right _
            (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hw, hz⟩))
      · intro hz
        rcases Finset.mem_union.mp hz with h | h
        · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h
          exact (Finset.mem_filter.mp hv).2
        · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp h
          exact (Finset.mem_filter.mp hw).2

theorem joinFaces_indep {t : Finset (E × F × ℝ)} (ht : t ∈ joinFaces K L) :
    AffineIndependent ℝ ((↑) : t → E × F × ℝ) := by
  obtain ⟨σ, τ, hσ, hτ, -, rfl⟩ := ht
  have hσind : AffineIndependent ℝ ((↑) : σ → E) := by
    rcases hσ with rfl | hσ
    · exact affineIndependent_of_subsingleton ℝ _
    · exact K.indep hσ
  have hτind : AffineIndependent ℝ ((↑) : τ → F) := by
    rcases hτ with rfl | hτ
    · exact affineIndependent_of_subsingleton ℝ _
    · exact L.indep hτ
  refine affineIndependent_of_forall_eq_zero fun c hc0 hc1 => ?_
  rw [Finset.sum_union (disjoint_image_joinFst_joinSnd σ τ),
    Finset.sum_image fun _ _ _ _ h => joinFst_injective h,
    Finset.sum_image fun _ _ _ _ h => joinSnd_injective h] at hc0 hc1
  rw [sum_smul_joinFst, sum_smul_joinSnd, Prod.mk_add_mk, Prod.mk_add_mk, add_zero, zero_add,
    zero_add, Prod.mk_eq_zero, Prod.mk_eq_zero] at hc1
  obtain ⟨h1, h2, h3⟩ := hc1
  have hσ0 : ∑ v ∈ σ, c (joinFst E F v) = 0 := by linarith
  have hσz := eq_zero_of_sum_eq_zero_of_affineIndependent hσind hσ0 h1
  have hτz := eq_zero_of_sum_eq_zero_of_affineIndependent hτind h3 h2
  intro u hu
  rcases Finset.mem_union.mp hu with h | h
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h
    exact hσz v hv
  · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp h
    exact hτz w hw

theorem mem_convexHull_of_sum_smul_eq {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {σ : Finset G} {a : G → ℝ} (ha0 : ∀ v ∈ σ, 0 ≤ a v) {s : ℝ} (hs : 0 < s)
    (ha1 : ∑ v ∈ σ, a v = s) : s⁻¹ • ∑ v ∈ σ, a v • v ∈ convexHull ℝ (σ : Set G) := by
  refine mem_convexHull_iff_exists_weights.mpr ⟨fun v => s⁻¹ * a v,
    fun v hv => mul_nonneg (inv_nonneg.mpr hs.le) (ha0 v hv), ?_, ?_⟩
  · rw [← Finset.mul_sum, ha1, inv_mul_cancel₀ hs.ne']
  · rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun v _ => by rw [mul_smul]

theorem joinFaces_inter {t₁ t₂ : Finset (E × F × ℝ)} (h₁ : t₁ ∈ joinFaces K L)
    (h₂ : t₂ ∈ joinFaces K L) :
    convexHull ℝ (t₁ : Set (E × F × ℝ)) ∩ convexHull ℝ (t₂ : Set (E × F × ℝ)) ⊆
      convexHull ℝ ((t₁ : Set (E × F × ℝ)) ∩ (t₂ : Set (E × F × ℝ))) := by
  obtain ⟨σ₁, τ₁, hσ₁, hτ₁, -, rfl⟩ := h₁
  obtain ⟨σ₂, τ₂, hσ₂, hτ₂, -, rfl⟩ := h₂
  rintro z ⟨hz₁, hz₂⟩
  obtain ⟨a₁, b₁, ha₁, hb₁, hab₁, hz₁'⟩ := (mem_convexHull_join_iff σ₁ τ₁).mp hz₁
  obtain ⟨a₂, b₂, ha₂, hb₂, hab₂, hz₂'⟩ := (mem_convexHull_join_iff σ₂ τ₂).mp hz₂
  have hsub : (((σ₁ ∩ σ₂).image (joinFst E F) ∪ (τ₁ ∩ τ₂).image (joinSnd E F) :
      Finset (E × F × ℝ)) : Set (E × F × ℝ)) ⊆
      ((σ₁.image (joinFst E F) ∪ τ₁.image (joinSnd E F) : Finset (E × F × ℝ)) : Set (E × F × ℝ)) ∩
        ((σ₂.image (joinFst E F) ∪ τ₂.image (joinSnd E F) : Finset (E × F × ℝ)) :
          Set (E × F × ℝ)) := by
    intro u hu
    rcases Finset.mem_union.mp (Finset.mem_coe.mp hu) with h | h
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h
      exact ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_inter.mp hv).1),
        Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_inter.mp hv).2)⟩
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp h
      exact ⟨Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_inter.mp hw).1),
        Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_inter.mp hw).2)⟩
  refine convexHull_mono hsub ?_
  have hx : ∑ v ∈ σ₁, a₁ v • v = ∑ v ∈ σ₂, a₂ v • v := by
    have := congrArg Prod.fst (hz₁'.symm.trans hz₂')
    exact this
  have hy : ∑ w ∈ τ₁, b₁ w • w = ∑ w ∈ τ₂, b₂ w • w := by
    have := congrArg (fun p : E × F × ℝ => p.2.1) (hz₁'.symm.trans hz₂')
    exact this
  have hs : ∑ w ∈ τ₁, b₁ w = ∑ w ∈ τ₂, b₂ w := by
    have := congrArg (fun p : E × F × ℝ => p.2.2) (hz₁'.symm.trans hz₂')
    exact this
  set s : ℝ := ∑ w ∈ τ₁, b₁ w with hsdef
  have hs0 : 0 ≤ s := Finset.sum_nonneg hb₁
  have hs1 : s ≤ 1 := by linarith [Finset.sum_nonneg ha₁]
  have hσ₁sum : ∑ v ∈ σ₁, a₁ v = 1 - s := by linarith
  have hσ₂sum : ∑ v ∈ σ₂, a₂ v = 1 - s := by linarith
  have hσfaces : 1 - s ≠ 0 → σ₁ ∈ K.faces ∧ σ₂ ∈ K.faces := by
    intro hne
    constructor
    · rcases hσ₁ with rfl | h
      · exact absurd (by rw [Finset.sum_empty] at hσ₁sum; exact hσ₁sum.symm) hne
      · exact h
    · rcases hσ₂ with rfl | h
      · exact absurd (by rw [Finset.sum_empty] at hσ₂sum; exact hσ₂sum.symm) hne
      · exact h
  have hτfaces : s ≠ 0 → τ₁ ∈ L.faces ∧ τ₂ ∈ L.faces := by
    intro hne
    constructor
    · rcases hτ₁ with rfl | h
      · exact absurd (hsdef.trans Finset.sum_empty) hne
      · exact h
    · rcases hτ₂ with rfl | h
      · exact absurd (hs.trans Finset.sum_empty) hne
      · exact h
  have hxconv : 1 - s ≠ 0 → (1 - s)⁻¹ • ∑ v ∈ σ₁, a₁ v • v ∈
      convexHull ℝ (((σ₁ ∩ σ₂ : Finset E) : Set E)) := by
    intro hne
    have hpos : 0 < 1 - s := lt_of_le_of_ne (by linarith) (Ne.symm hne)
    rw [Finset.coe_inter]
    refine K.inter_subset_convexHull (hσfaces hne).1 (hσfaces hne).2
      ⟨mem_convexHull_of_sum_smul_eq ha₁ hpos hσ₁sum, ?_⟩
    rw [hx]
    exact mem_convexHull_of_sum_smul_eq ha₂ hpos hσ₂sum
  have hyconv : s ≠ 0 → s⁻¹ • ∑ w ∈ τ₁, b₁ w • w ∈
      convexHull ℝ (((τ₁ ∩ τ₂ : Finset F) : Set F)) := by
    intro hne
    have hpos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hne)
    rw [Finset.coe_inter]
    refine L.inter_subset_convexHull (hτfaces hne).1 (hτfaces hne).2
      ⟨mem_convexHull_of_sum_smul_eq hb₁ hpos rfl, ?_⟩
    rw [hy]
    exact mem_convexHull_of_sum_smul_eq hb₂ hpos hs.symm
  rw [hz₁']
  rcases eq_or_lt_of_le hs0 with hs0' | hspos
  · have hs0'' : s = 0 := hs0'.symm
    have hb₁zero : ∀ w ∈ τ₁, b₁ w = 0 := (Finset.sum_eq_zero_iff_of_nonneg hb₁).mp hs0''
    have hne : (1 : ℝ) - s ≠ 0 := by
      rw [hs0'']
      norm_num
    obtain ⟨c, hc0, hc1, hcx⟩ := mem_convexHull_iff_exists_weights.mp (hxconv hne)
    rw [hs0'', sub_zero, inv_one, one_smul] at hcx
    have hy0 : ∑ w ∈ τ₁, b₁ w • w = 0 :=
      Finset.sum_eq_zero fun w hw => by rw [hb₁zero w hw, zero_smul]
    refine (mem_convexHull_join_iff _ _).mpr ⟨c, fun _ => 0, hc0, fun _ _ => le_rfl, ?_, ?_⟩
    · rw [hc1, Finset.sum_const_zero, add_zero]
    · rw [hcx, hy0, hs0'']
      simp
  · rcases eq_or_lt_of_le hs1 with hs1' | hslt
    · have ha₁zero : ∀ v ∈ σ₁, a₁ v = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg ha₁).mp (by rw [hσ₁sum, hs1', sub_self])
      obtain ⟨d, hd0, hd1, hdy⟩ := mem_convexHull_iff_exists_weights.mp (hyconv hspos.ne')
      rw [hs1', inv_one, one_smul] at hdy
      have hx0 : ∑ v ∈ σ₁, a₁ v • v = 0 :=
        Finset.sum_eq_zero fun v hv => by rw [ha₁zero v hv, zero_smul]
      refine (mem_convexHull_join_iff _ _).mpr ⟨fun _ => 0, d, fun _ _ => le_rfl, hd0, ?_, ?_⟩
      · rw [hd1, Finset.sum_const_zero, zero_add]
      · rw [hx0, hdy, hd1, hs1']
        simp
    · have hne : (1 : ℝ) - s ≠ 0 := by linarith
      obtain ⟨c, hc0, hc1, hcx⟩ := mem_convexHull_iff_exists_weights.mp (hxconv hne)
      obtain ⟨d, hd0, hd1, hdy⟩ := mem_convexHull_iff_exists_weights.mp (hyconv hspos.ne')
      refine (mem_convexHull_join_iff _ _).mpr ⟨fun v => (1 - s) * c v, fun w => s * d w,
        fun v hv => mul_nonneg (by linarith) (hc0 v hv), fun w hw => mul_nonneg hs0 (hd0 w hw),
        ?_, ?_⟩
      · rw [← Finset.mul_sum, ← Finset.mul_sum, hc1, hd1]
        ring
      · have hx' : ∑ v ∈ σ₁ ∩ σ₂, ((1 - s) * c v) • v = ∑ v ∈ σ₁, a₁ v • v := by
          have hsm : ∑ v ∈ σ₁ ∩ σ₂, ((1 - s) * c v) • v = (1 - s) • ∑ v ∈ σ₁ ∩ σ₂, c v • v := by
            rw [Finset.smul_sum]
            exact Finset.sum_congr rfl fun v _ => by rw [mul_smul]
          rw [hsm, hcx, smul_smul, mul_inv_cancel₀ hne, one_smul]
        have hy' : ∑ w ∈ τ₁ ∩ τ₂, (s * d w) • w = ∑ w ∈ τ₁, b₁ w • w := by
          have hsm : ∑ w ∈ τ₁ ∩ τ₂, (s * d w) • w = s • ∑ w ∈ τ₁ ∩ τ₂, d w • w := by
            rw [Finset.smul_sum]
            exact Finset.sum_congr rfl fun w _ => by rw [mul_smul]
          rw [hsm, hdy, smul_smul, mul_inv_cancel₀ hspos.ne', one_smul]
        have hs' : ∑ w ∈ τ₁ ∩ τ₂, s * d w = s := by
          rw [← Finset.mul_sum, hd1, mul_one]
        rw [hx', hy', hs']

def joinComplex : Geometry.SimplicialComplex ℝ (E × F × ℝ) where
  faces := joinFaces K L
  isRelLowerSet_faces := joinFaces_isRelLowerSet K L
  indep := joinFaces_indep K L
  inter_subset_convexHull := joinFaces_inter K L

theorem mem_joinComplex_faces_iff {t : Finset (E × F × ℝ)} :
    t ∈ (joinComplex K L).faces ↔ ∃ (σ : Finset E) (τ : Finset F),
      (σ = ∅ ∨ σ ∈ K.faces) ∧ (τ = ∅ ∨ τ ∈ L.faces) ∧ (σ.Nonempty ∨ τ.Nonempty) ∧
        t = σ.image (joinFst E F) ∪ τ.image (joinSnd E F) := Iff.rfl

theorem joinComplex_faces_finite [Finite K.faces] [Finite L.faces] :
    (joinComplex K L).faces.Finite := by
  refine ((((Set.toFinite K.faces).insert ∅).prod ((Set.toFinite L.faces).insert ∅)).image
    fun p : Finset E × Finset F => p.1.image (joinFst E F) ∪ p.2.image (joinSnd E F)).subset ?_
  rintro t ⟨σ, τ, hσ, hτ, -, rfl⟩
  refine ⟨(σ, τ), ⟨?_, ?_⟩, rfl⟩
  · rcases hσ with rfl | h
    · exact mem_insert _ _
    · exact mem_insert_of_mem _ h
  · rcases hτ with rfl | h
    · exact mem_insert _ _
    · exact mem_insert_of_mem _ h

theorem union_image_mem_joinComplex {σ : Finset E} {τ : Finset F} (hσ : σ = ∅ ∨ σ ∈ K.faces)
    (hτ : τ = ∅ ∨ τ ∈ L.faces) (hne : σ.Nonempty ∨ τ.Nonempty) :
    σ.image (joinFst E F) ∪ τ.image (joinSnd E F) ∈ (joinComplex K L).faces :=
  ⟨σ, τ, hσ, hτ, hne, rfl⟩

theorem image_joinFst_mem_joinComplex {σ : Finset E} (hσ : σ ∈ K.faces) :
    σ.image (joinFst E F) ∈ (joinComplex K L).faces := by
  have := union_image_mem_joinComplex K L (Or.inr hσ) (Or.inl rfl)
    (Or.inl (K.nonempty_of_mem_faces hσ)) (τ := ∅)
  rwa [Finset.image_empty, Finset.union_empty] at this

theorem image_joinSnd_mem_joinComplex {τ : Finset F} (hτ : τ ∈ L.faces) :
    τ.image (joinSnd E F) ∈ (joinComplex K L).faces := by
  have := union_image_mem_joinComplex K L (Or.inl rfl) (Or.inr hτ)
    (Or.inr (L.nonempty_of_mem_faces hτ)) (σ := ∅)
  rwa [Finset.image_empty, Finset.empty_union] at this

theorem joinFst_mem_convexHull_image {σ : Finset E} {x : E} (hx : x ∈ convexHull ℝ (σ : Set E)) :
    joinFst E F x ∈ convexHull ℝ ((σ.image (joinFst E F) : Finset (E × F × ℝ)) : Set (E × F × ℝ)) := by
  obtain ⟨c, hc0, hc1, hcx⟩ := mem_convexHull_iff_exists_weights.mp hx
  have h := (mem_convexHull_join_iff σ (∅ : Finset F)).mpr ⟨c, fun _ => 0, hc0, fun _ _ => le_rfl,
    by rw [hc1, Finset.sum_empty, add_zero], by rw [hcx, Finset.sum_empty, Finset.sum_empty]⟩
  rwa [Finset.image_empty, Finset.union_empty] at h

theorem joinSnd_mem_convexHull_image {τ : Finset F} {y : F} (hy : y ∈ convexHull ℝ (τ : Set F)) :
    joinSnd E F y ∈ convexHull ℝ ((τ.image (joinSnd E F) : Finset (E × F × ℝ)) : Set (E × F × ℝ)) := by
  obtain ⟨d, hd0, hd1, hdy⟩ := mem_convexHull_iff_exists_weights.mp hy
  have h := (mem_convexHull_join_iff (∅ : Finset E) τ).mpr ⟨fun _ => 0, d, fun _ _ => le_rfl, hd0,
    by rw [hd1, Finset.sum_empty, zero_add], by rw [hdy, Finset.sum_empty, hd1]⟩
  rwa [Finset.image_empty, Finset.empty_union] at h

theorem geometricLink_joinComplex_joinFst {v : E} (hv : {v} ∈ K.faces) :
    SimplicialComplex.geometricLink (joinComplex K L) {joinFst E F v} =
      joinComplex (SimplicialComplex.geometricLink K {v}) L := by
  ext t
  rw [SimplicialComplex.mem_geometricLink_singleton, mem_joinComplex_faces_iff,
    mem_joinComplex_faces_iff]
  constructor
  · rintro ⟨htne, hvt, σ, τ, hσ, hτ, -, hins⟩
    have hvσ : v ∈ σ := by
      have hmem : joinFst E F v ∈ σ.image (joinFst E F) ∪ τ.image (joinSnd E F) :=
        hins ▸ Finset.mem_insert_self _ _
      rcases Finset.mem_union.mp hmem with h | h
      · obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp h
        rw [joinFst_injective huv] at hu
        exact hu
      · obtain ⟨w, -, hw⟩ := Finset.mem_image.mp h
        exact absurd hw.symm (joinFst_ne_joinSnd v w)
    have hσK : σ ∈ K.faces := by
      rcases hσ with rfl | h
      · exact absurd hvσ (Finset.notMem_empty v)
      · exact h
    refine ⟨σ.erase v, τ, ?_, hτ, ?_, ?_⟩
    · rcases (σ.erase v).eq_empty_or_nonempty with h | h
      · exact Or.inl h
      · refine Or.inr ((SimplicialComplex.mem_geometricLink_singleton K v _).mpr
          ⟨h, Finset.notMem_erase v σ, ?_⟩)
        rw [Finset.insert_erase hvσ]
        exact hσK
    · obtain ⟨z, hz⟩ := htne
      have hz' : z ∈ σ.image (joinFst E F) ∪ τ.image (joinSnd E F) :=
        hins ▸ Finset.mem_insert_of_mem hz
      rcases Finset.mem_union.mp hz' with h | h
      · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp h
        exact Or.inl ⟨u, Finset.mem_erase.mpr ⟨fun huv => hvt (huv ▸ hz), hu⟩⟩
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp h
        exact Or.inr ⟨w, hw⟩
    · have ht : t = (insert (joinFst E F v) t).erase (joinFst E F v) :=
        (Finset.erase_insert hvt).symm
      have hjv : joinFst E F v ∉ τ.image (joinSnd E F) := by
        intro h
        obtain ⟨w, -, hw⟩ := Finset.mem_image.mp h
        exact joinFst_ne_joinSnd v w hw.symm
      rw [ht, hins, Finset.erase_union_distrib, Finset.image_erase joinFst_injective,
        Finset.erase_eq_of_notMem hjv]
  · rintro ⟨σ', τ, hσ', hτ, hne, rfl⟩
    have hσ'v : v ∉ σ' := by
      rcases hσ' with rfl | h
      · exact Finset.notMem_empty v
      · exact ((SimplicialComplex.mem_geometricLink_singleton K v σ').mp h).2.1
    have hins : insert v σ' ∈ K.faces := by
      rcases hσ' with rfl | h
      · rw [Finset.insert_empty]
        exact hv
      · exact ((SimplicialComplex.mem_geometricLink_singleton K v σ').mp h).2.2
    refine ⟨?_, ?_, insert v σ', τ, Or.inr hins, hτ, Or.inl (Finset.insert_nonempty v σ'), ?_⟩
    · rcases hne with h | h
      · exact (h.image _).mono Finset.subset_union_left
      · exact (h.image _).mono Finset.subset_union_right
    · intro h
      rcases Finset.mem_union.mp h with h | h
      · obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp h
        exact hσ'v (joinFst_injective huv ▸ hu)
      · obtain ⟨w, -, hw⟩ := Finset.mem_image.mp h
        exact joinFst_ne_joinSnd v w hw.symm
    · rw [Finset.image_insert, Finset.insert_union]

def joinSpace (X : Set E) (Y : Set F) : Set (E × F × ℝ) :=
  joinFst E F '' X ∪ joinSnd E F '' Y ∪
    {z | ∃ x ∈ X, ∃ y ∈ Y, ∃ t ∈ Icc (0 : ℝ) 1, z = ((1 - t) • x, t • y, t)}

theorem joinComplex_space : (joinComplex K L).space = joinSpace K.space L.space := by
  apply Subset.antisymm
  · intro z hz
    obtain ⟨t, ⟨σ, τ, hσ, hτ, -, rfl⟩, hzt⟩ := (joinComplex K L).mem_space_iff.mp hz
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := (mem_convexHull_join_iff σ τ).mp hzt
    set s : ℝ := ∑ w ∈ τ, b w with hsdef
    have hs0 : 0 ≤ s := Finset.sum_nonneg hb
    have hs1 : s ≤ 1 := by linarith [Finset.sum_nonneg ha]
    have hσsum : ∑ v ∈ σ, a v = 1 - s := by linarith
    have hσK : 1 - s ≠ 0 → σ ∈ K.faces := by
      intro hne
      rcases hσ with rfl | h
      · exact absurd (by rw [Finset.sum_empty] at hσsum; exact hσsum.symm) hne
      · exact h
    have hτL : s ≠ 0 → τ ∈ L.faces := by
      intro hne
      rcases hτ with rfl | h
      · exact absurd (hsdef.trans Finset.sum_empty) hne
      · exact h
    rcases eq_or_lt_of_le hs0 with hs0' | hspos
    · have hs0'' : s = 0 := hs0'.symm
      have hbzero : ∀ w ∈ τ, b w = 0 := (Finset.sum_eq_zero_iff_of_nonneg hb).mp hs0''
      have hy0 : ∑ w ∈ τ, b w • w = 0 :=
        Finset.sum_eq_zero fun w hw => by rw [hbzero w hw, zero_smul]
      have hne : (1 : ℝ) - s ≠ 0 := by
        rw [hs0'']
        norm_num
      have hx : ∑ v ∈ σ, a v • v ∈ K.space := by
        refine K.convexHull_subset_space (hσK hne) ?_
        have := mem_convexHull_of_sum_smul_eq ha (by rw [hs0'']; norm_num : (0 : ℝ) < 1 - s) hσsum
        rwa [hs0'', sub_zero, inv_one, one_smul] at this
      exact Or.inl (Or.inl ⟨_, hx, Prod.ext rfl (Prod.ext hy0.symm hs0''.symm)⟩)
    · rcases eq_or_lt_of_le hs1 with hs1' | hslt
      · have hazero : ∀ v ∈ σ, a v = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg ha).mp (by rw [hσsum, hs1', sub_self])
        have hx0 : ∑ v ∈ σ, a v • v = 0 :=
          Finset.sum_eq_zero fun v hv => by rw [hazero v hv, zero_smul]
        have hy : ∑ w ∈ τ, b w • w ∈ L.space := by
          refine L.convexHull_subset_space (hτL hspos.ne') ?_
          have := mem_convexHull_of_sum_smul_eq hb hspos rfl
          rwa [hs1', inv_one, one_smul] at this
        exact Or.inl (Or.inr ⟨_, hy, Prod.ext hx0.symm (Prod.ext rfl hs1'.symm)⟩)
      · have hne : (1 : ℝ) - s ≠ 0 := by linarith
        refine Or.inr ⟨(1 - s)⁻¹ • ∑ v ∈ σ, a v • v, ?_, s⁻¹ • ∑ w ∈ τ, b w • w, ?_, s, ⟨hs0, hs1⟩,
          ?_⟩
        · exact K.convexHull_subset_space (hσK hne)
            (mem_convexHull_of_sum_smul_eq ha (by linarith) hσsum)
        · exact L.convexHull_subset_space (hτL hspos.ne') (mem_convexHull_of_sum_smul_eq hb hspos rfl)
        · rw [smul_smul, mul_inv_cancel₀ hne, one_smul, smul_smul, mul_inv_cancel₀ hspos.ne',
            one_smul]
  · rintro z ((⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩) | ⟨x, hx, y, hy, t, ht, rfl⟩)
    · obtain ⟨σ, hσ, hxσ⟩ := K.mem_space_iff.mp hx
      exact (joinComplex K L).convexHull_subset_space (image_joinFst_mem_joinComplex K L hσ)
        (joinFst_mem_convexHull_image hxσ)
    · obtain ⟨τ, hτ, hyτ⟩ := L.mem_space_iff.mp hy
      exact (joinComplex K L).convexHull_subset_space (image_joinSnd_mem_joinComplex K L hτ)
        (joinSnd_mem_convexHull_image hyτ)
    · obtain ⟨σ, hσ, hxσ⟩ := K.mem_space_iff.mp hx
      obtain ⟨τ, hτ, hyτ⟩ := L.mem_space_iff.mp hy
      exact (joinComplex K L).convexHull_subset_space
        (union_image_mem_joinComplex K L (Or.inr hσ) (Or.inr hτ)
          (Or.inl (K.nonempty_of_mem_faces hσ)))
        (mem_convexHull_join_of σ τ hxσ hyτ ht.1 ht.2)

theorem joinComplex_faces_subset_of_faces_subset {K' : Geometry.SimplicialComplex ℝ E}
    (hK' : K'.faces ⊆ K.faces) : (joinComplex K' L).faces ⊆ (joinComplex K L).faces := by
  rintro t ⟨σ, τ, hσ, hτ, hne, rfl⟩
  refine ⟨σ, τ, ?_, hτ, hne, rfl⟩
  rcases hσ with rfl | h
  · exact Or.inl rfl
  · exact Or.inr (hK' h)

theorem IsSubdivision.joinComplex_left {K' : Geometry.SimplicialComplex ℝ E}
    (h : IsSubdivision K' K) : IsSubdivision (joinComplex K' L) (joinComplex K L) := by
  refine ⟨by rw [joinComplex_space, joinComplex_space, h.space_eq], ?_⟩
  rintro t ⟨σ', τ, hσ', hτ, hne, rfl⟩
  rcases hσ' with rfl | hσ'
  · exact ⟨_, union_image_mem_joinComplex K L (Or.inl rfl) hτ hne, subset_rfl⟩
  obtain ⟨σ, hσ, hsub⟩ := h.exists_face_subset hσ'
  refine ⟨σ.image (joinFst E F) ∪ τ.image (joinSnd E F),
    union_image_mem_joinComplex K L (Or.inr hσ) hτ (Or.inl (K.nonempty_of_mem_faces hσ)), ?_⟩
  refine convexHull_min ?_ (convex_convexHull ℝ _)
  intro u hu
  rcases Finset.mem_union.mp (Finset.mem_coe.mp hu) with h' | h'
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h'
    exact convexHull_mono (Finset.coe_subset.mpr Finset.subset_union_left)
      (joinFst_mem_convexHull_image (hsub (subset_convexHull ℝ _ (Finset.mem_coe.mpr hv))))
  · exact subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_union_right _ h'))

end JoinComplex

end DifferentialGeometry.Topology.PiecewiseLinear
