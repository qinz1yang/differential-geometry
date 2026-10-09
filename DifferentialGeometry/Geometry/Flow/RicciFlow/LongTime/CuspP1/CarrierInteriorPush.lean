import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.VertexGroupInjective

/-!
# CP1-C2: inward push of a compact carrier off its collared boundary tori

For a compact carrier `C` whose boundary is exhausted by the images of finitely many collars
(`BoundaryTori C n`, `C.model.boundary C.Carrier = T.image`), the collar rescaling
`a ↦ a + τ·max 0 (1/2 − a)` is a homotopy from the identity to a map `r` with values in the
interior (`exists_inward_homotopy_CPC2`). This is the collar form of "the interior of a compact
manifold with collared boundary is homotopy equivalent to it".
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology ContinuousMap unitInterval

universe u

namespace GC.LongTime.CuspP1

/-- Height rescaling used to push a collar inward. -/
def pushHeight_CPC2 (τ a : ℝ) : ℝ := a + τ * max 0 (1 / 2 - a)

theorem continuous_pushHeight_CPC2 : Continuous fun p : ℝ × ℝ => pushHeight_CPC2 p.1 p.2 := by
  unfold pushHeight_CPC2
  fun_prop

/-- Continuous half-space point of height `max s 0`. -/
def halfPt_CPC2 (s : ℝ) : EuclideanHalfSpace 1 := halfPoint (max s 0) (le_max_right s 0)

theorem continuous_halfPt_CPC2 : Continuous halfPt_CPC2 :=
  Continuous.subtype_mk ((PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun _ => continuous_id.max continuous_const)) _

theorem halfPt_val_CPC2 (s : ℝ) : (halfPt_CPC2 s).val 0 = max s 0 := rfl

/-- The push on collar coordinates. -/
def pushColl_CPC2 (τ : ℝ) (q : Torus × EuclideanHalfSpace 1) : Torus × EuclideanHalfSpace 1 :=
  (q.1, halfPt_CPC2 (pushHeight_CPC2 τ (q.2.val 0)))

theorem continuous_pushColl_CPC2 :
    Continuous fun p : ℝ × (Torus × EuclideanHalfSpace 1) => pushColl_CPC2 p.1 p.2 := by
  unfold pushColl_CPC2
  refine continuous_snd.fst.prodMk (continuous_halfPt_CPC2.comp
    (continuous_pushHeight_CPC2.comp (continuous_fst.prodMk ?_)))
  exact (EuclideanSpace.proj (0 : Fin 1)).continuous.comp
    (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))

theorem pushColl_height_CPC2 {τ : ℝ} (q : Torus × EuclideanHalfSpace 1) :
    (pushColl_CPC2 τ q).2.val 0 = max (pushHeight_CPC2 τ (q.2.val 0)) 0 := rfl

theorem pushHeight_lt_CPC2 {τ a : ℝ} (hτ1 : τ ≤ 1) (ha : a < 1) :
    pushHeight_CPC2 τ a < 1 := by
  unfold pushHeight_CPC2
  rcases le_total a (1 / 2) with h | h
  · rw [max_eq_right (by linarith)]
    nlinarith
  · rw [max_eq_left (by linarith)]
    linarith

theorem pushHeight_zero_CPC2 (a : ℝ) : pushHeight_CPC2 0 a = a := by
  simp [pushHeight_CPC2]

theorem pushHeight_of_half_le_CPC2 {τ a : ℝ} (h : 1 / 2 ≤ a) : pushHeight_CPC2 τ a = a := by
  unfold pushHeight_CPC2
  rw [max_eq_left (by linarith)]
  ring

theorem pushHeight_one_CPC2 (a : ℝ) : pushHeight_CPC2 1 a = max a (1 / 2) := by
  unfold pushHeight_CPC2
  rcases le_total a (1 / 2) with h | h
  · rw [max_eq_right (by linarith), max_eq_right h]; ring
  · rw [max_eq_left (by linarith), max_eq_left h]; ring

theorem pushColl_zero_CPC2 (q : Torus × EuclideanHalfSpace 1) : pushColl_CPC2 0 q = q := by
  refine Prod.ext rfl ?_
  refine Subtype.ext (PiLp.ext fun j => ?_)
  rw [Subsingleton.elim j 0]
  change max (pushHeight_CPC2 0 (q.2.val 0)) 0 = q.2.val 0
  rw [pushHeight_zero_CPC2]
  exact max_eq_left q.2.property

theorem pushColl_of_half_le_CPC2 (τ : ℝ) {q : Torus × EuclideanHalfSpace 1}
    (h : 1 / 2 ≤ q.2.val 0) : pushColl_CPC2 τ q = q := by
  refine Prod.ext rfl ?_
  refine Subtype.ext (PiLp.ext fun j => ?_)
  rw [Subsingleton.elim j 0]
  change max (pushHeight_CPC2 τ (q.2.val 0)) 0 = q.2.val 0
  rw [pushHeight_of_half_le_CPC2 h]
  exact max_eq_left q.2.property

theorem pushColl_mem_source_CPC2 {τ : ℝ} (hτ1 : τ ≤ 1)
    {q : Torus × EuclideanHalfSpace 1} (hq : q ∈ halfCollarSource) :
    pushColl_CPC2 τ q ∈ halfCollarSource := by
  change (pushColl_CPC2 τ q).2.val 0 < 1
  rw [pushColl_height_CPC2]
  exact max_lt (pushHeight_lt_CPC2 hτ1 hq) one_pos


section Push
variable {C : CompactCarrier.{u}} {n : ℕ} (T : BoundaryTori C n)

open Classical in
/-- The push of `C` along its collars at time `τ`. -/
def pushMap_CPC2 (τ : ℝ) (p : C.Carrier) : C.Carrier :=
  if h : ∃ j, p ∈ (T.collar j).target then
    T.collar (Classical.choose h) (pushColl_CPC2 τ ((T.collar (Classical.choose h)).symm p))
  else p

theorem pushMap_of_mem_CPC2 (τ : ℝ) {j : Fin n} {p : C.Carrier} (hp : p ∈ (T.collar j).target) :
    pushMap_CPC2 T τ p = T.collar j (pushColl_CPC2 τ ((T.collar j).symm p)) := by
  classical
  have h : ∃ j, p ∈ (T.collar j).target := ⟨j, hp⟩
  rw [pushMap_CPC2, dite_eq_left h]
  have hj : Classical.choose h = j := by
    by_contra hne
    exact (T.disjoint hne).le_bot ⟨Classical.choose_spec h, hp⟩
  rw [hj]

theorem pushMap_of_not_mem_CPC2 (τ : ℝ) {p : C.Carrier} (hp : ∀ j, p ∉ (T.collar j).target) :
    pushMap_CPC2 T τ p = p := by
  rw [pushMap_CPC2, dite_eq_right (fun ⟨j, hj⟩ => hp j hj)]

/-- The closed shell `a ≤ 1/2` of a collar. -/
def shell_CPC2 (j : Fin n) : Set C.Carrier :=
  (T.collar j) '' ((fun p : Torus × ℝ => (p.1, halfPt_CPC2 p.2)) '' (Set.univ ×ˢ Set.Icc 0 (1 / 2)))

theorem shell_subset_source_CPC2 (j : Fin n) :
    ((fun p : Torus × ℝ => (p.1, halfPt_CPC2 p.2)) '' (Set.univ ×ˢ Set.Icc (0 : ℝ) (1 / 2))) ⊆
      (T.collar j).source := by
  rintro _ ⟨⟨t, s⟩, ⟨-, hs⟩, rfl⟩
  rw [T.source_eq]
  change (halfPt_CPC2 s).val 0 < 1
  rw [halfPt_val_CPC2, max_eq_left hs.1]
  linarith [hs.2]

theorem isCompact_shell_CPC2 (j : Fin n) : IsCompact (shell_CPC2 T j) := by
  refine IsCompact.image_of_continuousOn ?_ ((T.collar j).contMDiffOn.continuousOn.mono
    (shell_subset_source_CPC2 T j))
  exact (isCompact_univ.prod isCompact_Icc).image
    (continuous_fst.prodMk (continuous_halfPt_CPC2.comp continuous_snd))

theorem shell_subset_target_CPC2 (j : Fin n) : shell_CPC2 T j ⊆ (T.collar j).target := by
  rintro _ ⟨q, hq, rfl⟩
  exact (T.collar j).map_source' (shell_subset_source_CPC2 T j hq)

theorem half_lt_of_not_mem_shell_CPC2 {j : Fin n} {p : C.Carrier} (hp : p ∈ (T.collar j).target)
    (hnot : p ∉ shell_CPC2 T j) : 1 / 2 < ((T.collar j).symm p).2.val 0 := by
  by_contra hle
  push Not at hle
  apply hnot
  set q := (T.collar j).symm p with hq
  refine ⟨q, ⟨(q.1, (q.2.val 0)), ⟨Set.mem_univ _, q.2.property, hle⟩, ?_⟩, ?_⟩
  · refine Prod.ext rfl ?_
    change halfPt_CPC2 (q.2.val 0) = q.2
    rw [halfPt_CPC2]
    exact halfPoint_eq_self q.2 (le_max_right _ _) (max_eq_left q.2.property)
  · exact (T.collar j).right_inv' hp

theorem continuous_pushMap_CPC2 :
    Continuous fun x : I × C.Carrier => pushMap_CPC2 T (x.1 : ℝ) x.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨τ, p⟩
  by_cases hp : ∃ j, p ∈ (T.collar j).target
  · obtain ⟨j, hj⟩ := hp
    have hopen : IsOpen ((Set.univ : Set I) ×ˢ (T.collar j).target) :=
      isOpen_univ.prod (T.collar j).open_target
    have hcont : ContinuousOn (fun x : I × C.Carrier =>
        T.collar j (pushColl_CPC2 (x.1 : ℝ) ((T.collar j).symm x.2)))
        ((Set.univ : Set I) ×ˢ (T.collar j).target) := by
      refine ContinuousOn.comp (g := T.collar j) (T.collar j).contMDiffOn.continuousOn
        (continuous_pushColl_CPC2.comp_continuousOn
          ((continuous_subtype_val.comp continuous_fst).continuousOn.prodMk ?_)) ?_
      · exact ((T.collar j).toOpenPartialHomeomorph.continuousOn_symm).comp continuous_snd.continuousOn
          fun x hx => hx.2
      · intro x hx
        rw [T.source_eq j]
        exact pushColl_mem_source_CPC2 x.1.2.2 (by
          rw [← T.source_eq j]
          exact (T.collar j).map_target' hx.2)
    exact (hcont.congr fun x hx => pushMap_of_mem_CPC2 T (x.1 : ℝ) hx.2).continuousAt
      (hopen.mem_nhds ⟨Set.mem_univ _, hj⟩)
  · push Not at hp
    have hK : IsClosed (⋃ j, shell_CPC2 T j) :=
      isClosed_iUnion_of_finite fun j => (isCompact_shell_CPC2 T j).isClosed
    have hpK : p ∈ (⋃ j, shell_CPC2 T j)ᶜ := fun h =>
      let ⟨j, hj⟩ := Set.mem_iUnion.mp h
      hp j (shell_subset_target_CPC2 T j hj)
    have hopen : IsOpen ((Set.univ : Set I) ×ˢ (⋃ j, shell_CPC2 T j)ᶜ) :=
      isOpen_univ.prod hK.isOpen_compl
    have hcont : ContinuousOn (fun x : I × C.Carrier => x.2)
        ((Set.univ : Set I) ×ˢ (⋃ j, shell_CPC2 T j)ᶜ) := continuous_snd.continuousOn
    refine (hcont.congr fun x hx => ?_).continuousAt (hopen.mem_nhds ⟨Set.mem_univ _, hpK⟩)
    by_cases hx2 : ∃ j, x.2 ∈ (T.collar j).target
    · obtain ⟨j, hj⟩ := hx2
      have hn : x.2 ∉ shell_CPC2 T j := fun h => hx.2 (Set.mem_iUnion.mpr ⟨j, h⟩)
      rw [pushMap_of_mem_CPC2 T (x.1 : ℝ) hj, pushColl_of_half_le_CPC2 _
        (half_lt_of_not_mem_shell_CPC2 T hj hn).le]
      exact (T.collar j).right_inv' hj
    · push Not at hx2
      exact pushMap_of_not_mem_CPC2 T (x.1 : ℝ) hx2


theorem pushMap_zero_CPC2 (p : C.Carrier) : pushMap_CPC2 T 0 p = p := by
  by_cases hp : ∃ j, p ∈ (T.collar j).target
  · obtain ⟨j, hj⟩ := hp
    rw [pushMap_of_mem_CPC2 T 0 hj, pushColl_zero_CPC2]
    exact (T.collar j).right_inv' hj
  · push Not at hp
    exact pushMap_of_not_mem_CPC2 T 0 hp

/-- The push at time `1`. -/
def pushOne_CPC2 : C(C.Carrier, C.Carrier) :=
  ⟨fun p => pushMap_CPC2 T 1 p,
    (continuous_pushMap_CPC2 T).comp
      ((continuous_const : Continuous fun _ : C.Carrier => (1 : I)).prodMk continuous_id)⟩

/-- The push homotopy from the identity. -/
def pushHomotopy_CPC2 : (ContinuousMap.id C.Carrier).Homotopy (pushOne_CPC2 T) where
  toFun x := pushMap_CPC2 T (x.1 : ℝ) x.2
  continuous_toFun := continuous_pushMap_CPC2 T
  map_zero_left p := by
    change pushMap_CPC2 T 0 p = p
    exact pushMap_zero_CPC2 T p
  map_one_left p := rfl

theorem collar_zero_mem_target_CPC2 (j : Fin n) (t : Torus) :
    T.collar j (t, halfZero) ∈ (T.collar j).target :=
  (T.collar j).map_source' (by rw [T.source_eq]; exact zero_mem_halfCollarSource t)

theorem image_subset_targets_CPC2 {p : C.Carrier} (hp : p ∈ T.image) : ∃ j, p ∈ (T.collar j).target := by
  obtain ⟨j, t, rfl⟩ := Set.mem_iUnion.mp hp
  exact ⟨j, collar_zero_mem_target_CPC2 T j t⟩

theorem isInteriorPoint_pushOne_CPC2 (hbd : C.model.boundary C.Carrier = T.image) (p : C.Carrier) :
    C.model.IsInteriorPoint (pushOne_CPC2 T p) := by
  rw [ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint]
  intro hb
  have hb' : pushOne_CPC2 T p ∈ T.image := hbd ▸ hb
  by_cases hp : ∃ j, p ∈ (T.collar j).target
  · obtain ⟨j, hj⟩ := hp
    change pushMap_CPC2 T 1 p ∈ T.image at hb'
    rw [pushMap_of_mem_CPC2 T 1 hj] at hb'
    obtain ⟨j', t, ht⟩ := Set.mem_iUnion.mp hb'
    set q := (T.collar j).symm p
    have hq : q ∈ halfCollarSource := by
      rw [← T.source_eq j]; exact (T.collar j).map_target' hj
    have hq' := pushColl_mem_source_CPC2 (τ := 1) le_rfl hq
    have hz : (t, halfZero) ∈ halfCollarSource := zero_mem_halfCollarSource t
    have h1 : T.collar j (pushColl_CPC2 1 q) ∈ (T.collar j).target :=
      (T.collar j).map_source' (by rw [T.source_eq]; exact hq')
    have h2 : T.collar j' (t, halfZero) ∈ (T.collar j').target := collar_zero_mem_target_CPC2 T j' t
    have hjj : j' = j := by
      by_contra hne
      exact (T.disjoint hne).le_bot ⟨h2, by
        rw [show T.collar j' (t, halfZero) = T.collar j (pushColl_CPC2 1 q) from ht]
        exact h1⟩
    subst hjj
    have heq := (T.collar j').toOpenPartialHomeomorph.injOn
      (by change _ ∈ (T.collar j').source; rw [T.source_eq]; exact hz)
      (by change _ ∈ (T.collar j').source; rw [T.source_eq]; exact hq') ht
    have h0 : (pushColl_CPC2 1 q).2.val 0 = 0 := by rw [← heq]; rfl
    rw [pushColl_height_CPC2, pushHeight_one_CPC2] at h0
    have := le_max_left (q.2.val 0) (1 / 2)
    have := le_max_right (q.2.val 0) (1 / 2)
    have := le_max_left (max (q.2.val 0) (1 / 2)) 0
    linarith
  · push Not at hp
    change pushMap_CPC2 T 1 p ∈ T.image at hb'
    rw [pushMap_of_not_mem_CPC2 T 1 hp] at hb'
    obtain ⟨j, hj⟩ := image_subset_targets_CPC2 T hb'
    exact hp j hj

theorem exists_inward_homotopy_CPC2 (hbd : C.model.boundary C.Carrier = T.image) :
    ∃ r : C(C.Carrier, C.Carrier), (∀ p, C.model.IsInteriorPoint (r p)) ∧
      Nonempty ((ContinuousMap.id C.Carrier).Homotopy r) :=
  ⟨pushOne_CPC2 T, isInteriorPoint_pushOne_CPC2 T hbd, ⟨pushHomotopy_CPC2 T⟩⟩

end Push

end GC.LongTime.CuspP1
