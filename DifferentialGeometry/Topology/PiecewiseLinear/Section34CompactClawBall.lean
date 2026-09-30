/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallGluing
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactSourceIncidence
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTargetCells
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTetraSkeleton

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Gluing

theorem isPLBall_union_of_inter_eq_of_subset_frontier {B V S : Set E3} (hB : IsPLBall 3 B)
    (hV : IsPLBall 3 V) (hS : IsPLBall 2 S) (hBV : B ∩ V = S) (hSV : S ⊆ frontier V) :
    IsPLBall 3 (B ∪ V) := by
  have hSB : S ⊆ frontier B := by
    intro z hz
    have hzBV := hBV.symm.subset hz
    rw [hB.isPolyhedron.isClosed.frontier_eq]
    refine ⟨hzBV.1, fun hzi => ?_⟩
    have hzV : z ∈ closure (interior V) := by
      rw [IsPLBall.closure_interior (n := 2) hV]
      exact hzBV.2
    obtain ⟨y, hyB, hyV⟩ := mem_closure_iff.mp hzV (interior B) isOpen_interior hzi
    have hyS : y ∈ S := hBV.subset ⟨interior_subset hyB, interior_subset hyV⟩
    exact Set.disjoint_left.mp disjoint_interior_frontier hyV (hSV hyS)
  rw [← hBV] at hS hSB hSV
  exact isPLBall_union_of_inter_isPLBall_two hB hV hS hSB hSV

theorem isPLBall_union_biUnion_range_of_attach {B : Set E3} (hB : IsPLBall 3 B)
    {W S : ℕ → Set E3} (k : ℕ) (hW : ∀ i < k, IsPLBall 3 (W (i + 1)))
    (hS : ∀ i < k, IsPLBall 2 (S i)) (hSW : ∀ i < k, S i ⊆ frontier (W (i + 1)))
    (hmeet : ∀ i < k, (B ∪ ⋃ j ∈ Finset.range i, W (j + 1)) ∩ W (i + 1) = S i) :
    IsPLBall 3 (B ∪ ⋃ j ∈ Finset.range k, W (j + 1)) := by
  induction k with
  | zero => simpa using hB
  | succ k ih =>
    have h := ih (fun i hi => hW i (by omega)) (fun i hi => hS i (by omega))
      (fun i hi => hSW i (by omega)) (fun i hi => hmeet i (by omega))
    rw [Finset.range_add_one, Finset.set_biUnion_insert, union_comm (W (k + 1)), ← union_assoc]
    exact isPLBall_union_of_inter_eq_of_subset_frontier h (hW k (by omega)) (hS k (by omega))
      (hmeet k (by omega)) (hSW k (by omega))

end Gluing

section Claw

variable {C : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {f₁ : E3 → E3}

def section34CompactClawBall (V : Section34CompactVertexIndex K K' → Set E3)
    (x y x' y' : E3) : Set E3 :=
  ⋃ (w : Section34CompactVertexIndex K K') (_ : ∃ p, w.1 = {p} ∧ (p ∈ segment ℝ x y ∨
    (p ∈ segment ℝ x x' ∧ p ≠ x') ∨ (p ∈ segment ℝ y y' ∧ p ≠ y'))), V w

theorem Section34CompactCutFrame.splitDiskImage_subset_frontier
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    {e : Section34CompactEdgeIndex K K'} {w : Section34CompactVertexIndex K K'}
    (hwe : w.1 ⊆ e.1) :
    section34CompactSplitDiskImage src f₁ e ⊆
      frontier (section34CompactVertexBallImage src f₁ w) := by
  obtain ⟨-, -, -, -, -, -, hcell, hbd, -⟩ := id hcut
  have hG := isPLHomeomorphInto_of_isPLHomeomorphOn_of_subset hf₁
    (hcell (.vertexBall w)).isPolyhedron (subset_iUnion (fun v => src (.vertexBall v)) w)
  have hsub : src (.splitDisk e) ⊆ src (.vertexBall w) :=
    (hcut.splitDisk_subset_vertexBall_iff e w).mpr hwe
  have hbdv : src (.splitDisk e) ⊆ srcBd (.vertexBall w) := by
    intro x hx
    rw [hbd (.vertexBall w)]
    exact mem_iUnion₂.mpr ⟨.splitDisk e, ⟨hsub, by simp⟩, hx⟩
  change f₁ '' src (.splitDisk e) ⊆ frontier (f₁ '' src (.vertexBall w))
  rw [← ((hcell (.vertexBall w)).image_boundary_interior hG).1]
  exact image_mono hbdv

theorem Section34CompactCutFrame.vertexBallImage_inter_eq_splitDiskImage
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    {e : Section34CompactEdgeIndex K K'} {w w' : Section34CompactVertexIndex K K'}
    (hww : w ≠ w') (hw : w.1 ⊆ e.1) (hw' : w'.1 ⊆ e.1) :
    section34CompactVertexBallImage src f₁ w ∩ section34CompactVertexBallImage src f₁ w' =
      section34CompactSplitDiskImage src f₁ e := by
  obtain ⟨a, b, -, hab, hE⟩ := hcut.splitDiskImage_eq_inter hf₁ e
  rcases eq_or_eq_of_section34CompactVertexIndex_subset e hab hw with rfl | rfl <;>
    rcases eq_or_eq_of_section34CompactVertexIndex_subset e hab hw' with rfl | rfl
  · exact absurd rfl hww
  · exact hE.symm
  · rw [inter_comm]
    exact hE.symm
  · exact absurd rfl hww

theorem Section34CompactCutFrame.disjoint_vertexBallImage_of_forall_not_subset
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    {w w' : Section34CompactVertexIndex K K'} (hww : w ≠ w')
    (hnot : ∀ e : Section34CompactEdgeIndex K K', w.1 ⊆ e.1 → w'.1 ⊆ e.1 → False) :
    Disjoint (section34CompactVertexBallImage src f₁ w)
      (section34CompactVertexBallImage src f₁ w') := by
  refine Set.disjoint_left.mpr fun x hx hx' => ?_
  obtain ⟨e, hxe⟩ := hcut.exists_mem_splitDiskImage_of_ne hf₁ hww hx hx'
  exact hnot e (hcut.subset_of_mem_splitDiskImage hf₁ hxe hx)
    (hcut.subset_of_mem_splitDiskImage hf₁ hxe hx')

theorem Section34CompactCutFrame.exists_vertexIndex_path
    (hcut : Section34CompactCutFrame C K K' src srcBd) {u v : E3} (huv : u ≠ v)
    (huvK : ({u, v} : Finset E3) ∈ K.faces) :
    ∃ (n : ℕ) (w : ℕ → Section34CompactVertexIndex K K')
      (e : ℕ → Section34CompactEdgeIndex K K'),
      0 < n ∧ (w 0).1 = {u} ∧ (w n).1 = {v} ∧
      (∀ i ≤ n, ∃ p ∈ segment ℝ u v, (w i).1 = {p} ∧ (0 < i → i < n → p ≠ u ∧ p ≠ v)) ∧
      (∀ i < n, (e i).1 = (w i).1 ∪ (w (i + 1)).1) ∧
      (∀ i ≤ n, ∀ j ≤ n, w i = w j → i = j) ∧
      (∀ w' : Section34CompactVertexIndex K K', (∃ p ∈ segment ℝ u v, w'.1 = {p}) →
        ∃ i ≤ n, w' = w i) ∧
      ∀ i ≤ n, ∀ j ≤ n, i + 1 < j → ∀ e' : Section34CompactEdgeIndex K K',
        (w i).1 ⊆ e'.1 → (w j).1 ⊆ e'.1 → False := by
  classical
  obtain ⟨-, -, hK'fin, -, hsub, -⟩ := id hcut
  obtain ⟨n, c, hn, hc0, hcn, hmono, hvert, hedge, hsurj, hK'edge⟩ :=
    hsub.exists_path_of_edge hK'fin huv huvK
  set L := AffineMap.lineMap (k := ℝ) u v
  have hLinj : Function.Injective L := AffineMap.lineMap_injective ℝ huv
  have hseg : segment ℝ u v = L '' Icc 0 1 := segment_eq_image_lineMap ℝ u v
  have hcIcc : ∀ i ≤ n, c i ∈ Icc (0 : ℝ) 1 := by
    intro i hi
    have h0 := hmono.monotoneOn (show 0 ∈ Iic n from Nat.zero_le n) (show i ∈ Iic n from hi)
      (Nat.zero_le i)
    have h1 := hmono.monotoneOn (show i ∈ Iic n from hi)
      (show n ∈ Iic n from Set.mem_Iic.mpr le_rfl) hi
    rw [hc0] at h0
    rw [hcn] at h1
    exact ⟨h0, h1⟩
  have hpt : ∀ i ≤ n, L (c i) ∈ segment ℝ u v := fun i hi => hseg ▸ ⟨c i, hcIcc i hi, rfl⟩
  have hgraph := segment_subset_section34CompactGraphSkeleton huvK
  have hw : ∀ i ≤ n, ∃ w' : Section34CompactVertexIndex K K', w'.1 = {L (c i)} := fun i hi =>
    exists_section34CompactVertexIndex_eq_singleton (hvert i hi) (hgraph (hpt i hi))
  set w : ℕ → Section34CompactVertexIndex K K' := fun i =>
    if h : i ≤ n then Classical.choose (hw i h) else Classical.choose (hw 0 (Nat.zero_le n))
  have hwspec : ∀ i ≤ n, (w i).1 = {L (c i)} := fun i hi => by
    change (if h : i ≤ n then Classical.choose (hw i h)
      else Classical.choose (hw 0 (Nat.zero_le n))).1 = _
    rw [dite_eq_left hi]
    exact Classical.choose_spec (hw i hi)
  have hinj : ∀ i ≤ n, ∀ j ≤ n, c i = c j → i = j := fun i hi j hj h =>
    hmono.injOn (show i ∈ Iic n from hi) (show j ∈ Iic n from hj) h
  have hne : ∀ i < n, L (c i) ≠ L (c (i + 1)) := fun i hi h =>
    absurd (hinj i hi.le (i + 1) hi (hLinj h)) (by omega)
  have he : ∀ i < n, ∃ e' : Section34CompactEdgeIndex K K', e'.1 = {L (c i), L (c (i + 1))} :=
    fun i hi => exists_section34CompactEdgeIndex_eq_pair (hne i hi) (hedge i hi)
      (((convex_segment u v).segment_subset (hpt i hi.le) (hpt (i + 1) hi)).trans hgraph)
  set e : ℕ → Section34CompactEdgeIndex K K' := fun i =>
    if h : i < n then Classical.choose (he i h) else Classical.choose (he 0 hn)
  have hespec : ∀ i < n, (e i).1 = {L (c i), L (c (i + 1))} := fun i hi => by
    change (if h : i < n then Classical.choose (he i h) else Classical.choose (he 0 hn)).1 = _
    rw [dite_eq_left hi]
    exact Classical.choose_spec (he i hi)
  refine ⟨n, w, e, hn, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hwspec 0 (Nat.zero_le n), hc0, AffineMap.lineMap_apply_zero]
  · rw [hwspec n le_rfl, hcn, AffineMap.lineMap_apply_one]
  · intro i hi
    refine ⟨L (c i), hpt i hi, hwspec i hi, fun hi0 hin => ⟨fun h => ?_, fun h => ?_⟩⟩
    · rw [← AffineMap.lineMap_apply_zero (k := ℝ) u v, ← hc0] at h
      exact absurd (hinj i hi 0 (Nat.zero_le n) (hLinj h)) (by omega)
    · rw [← AffineMap.lineMap_apply_one (k := ℝ) u v, ← hcn] at h
      exact absurd (hinj i hi n le_rfl (hLinj h)) (by omega)
  · intro i hi
    rw [hespec i hi, hwspec i hi.le, hwspec (i + 1) hi, Finset.insert_eq]
  · intro i hi j hj h
    have h' := congrArg Subtype.val h
    rw [hwspec i hi, hwspec j hj] at h'
    exact hinj i hi j hj (hLinj (Finset.singleton_injective h'))
  · rintro w' ⟨p, hp, hw'⟩
    rw [hseg] at hp
    obtain ⟨t, ht, rfl⟩ := hp
    obtain ⟨i, hi, hct⟩ := hsurj t ht (hw' ▸ w'.2.1)
    exact ⟨i, hi, Subtype.ext (by rw [hw', hwspec i hi, hct])⟩
  · intro i hi j hj hij e' hie hje
    rw [hwspec i hi] at hie
    rw [hwspec j hj] at hje
    have hij' : L (c i) ≠ L (c j) := fun h => absurd (hinj i hi j hj (hLinj h)) (by omega)
    have hpair : ({L (c i), L (c j)} : Finset E3) = e'.1 := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact hie (Finset.mem_singleton_self _)
        · rw [Finset.mem_singleton.mp hz]
          exact hje (Finset.mem_singleton_self _)
      · rw [e'.2.2.1, Finset.card_pair hij']
    have hconv : convexHull ℝ (e'.1 : Set E3) ⊆ segment ℝ u v := by
      rw [← hpair, Finset.coe_pair, convexHull_pair]
      exact (convex_segment u v).segment_subset (hpt i hi) (hpt j hj)
    obtain ⟨m, hm, hme⟩ := hK'edge e'.1 e'.2.1 hconv e'.2.2.1
    rw [← hpair] at hme
    have hmem : L (c i) ∈ ({L (c m), L (c (m + 1))} : Finset E3) :=
      hme ▸ Finset.mem_insert_self _ _
    have hmem' : L (c j) ∈ ({L (c m), L (c (m + 1))} : Finset E3) :=
      hme ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    rcases Finset.mem_insert.mp hmem with h1 | h1 <;>
      rcases Finset.mem_insert.mp hmem' with h2 | h2
    · exact hij' (h1.trans h2.symm)
    · have e1 := hinj i hi m hm.le (hLinj h1)
      have e2 := hinj j hj (m + 1) hm (hLinj (Finset.mem_singleton.mp h2))
      omega
    · have e1 := hinj i hi (m + 1) hm (hLinj (Finset.mem_singleton.mp h1))
      have e2 := hinj j hj m hm.le (hLinj h2)
      omega
    · exact hij' ((Finset.mem_singleton.mp h1).trans (Finset.mem_singleton.mp h2).symm)

theorem mem_segment_of_mem_segment_of_ne_of_incident (hsub : IsSubdivision K' K)
    {t : Finset E3} (ht : t ∈ K.faces) {u v p q : E3} (hu : u ∈ t) (hv : v ∈ t)
    (hp : p ∈ segment ℝ u v) (hpu : p ≠ u) (hpv : p ≠ v) (e : Section34CompactEdgeIndex K K')
    (hpe : p ∈ e.1) (hqe : q ∈ e.1) (het : Section34Incident e.1 t) : q ∈ segment ℝ u v := by
  classical
  obtain ⟨u', hu', v', hv', -, hconv⟩ :=
    exists_segment_of_incident_section34CompactEdgeIndex hsub ht e het
  have hpseg : p ∈ segment ℝ u' v' := hconv (subset_convexHull ℝ _ hpe)
  have huv : u ≠ v := by
    rintro rfl
    rw [segment_same] at hp
    exact hpu hp
  have hface : ∀ {a b : E3}, a ∈ t → b ∈ t → ({a, b} : Finset E3) ∈ K.faces := fun ha hb =>
    K.down_closed ht (Finset.insert_subset ha (Finset.singleton_subset_iff.mpr hb))
      (Finset.insert_nonempty _ _)
  have hmeet := segment_inter_segment_subset_of_mem_faces (hface hu hv) (hface hu' hv')
    ⟨hp, hpseg⟩
  have hin : ∀ {a b : E3}, a ∉ ({u', v'} : Set E3) →
      ({a, b} : Set E3) ∩ {u', v'} ⊆ {b} := by
    intro a b ha z hz
    rcases hz.1 with rfl | rfl
    · exact absurd hz.2 ha
    · exact mem_singleton _
  have huin : u ∈ ({u', v'} : Set E3) := by
    by_contra h
    have := convexHull_mono (hin (b := v) h) hmeet
    rw [convexHull_singleton] at this
    exact hpv this
  have hvin : v ∈ ({u', v'} : Set E3) := by
    by_contra h
    have hmeet' : p ∈ convexHull ℝ (({v, u} : Set E3) ∩ {u', v'}) := by
      rw [pair_comm]
      exact hmeet
    have := convexHull_mono (hin (b := u) h) hmeet'
    rw [convexHull_singleton] at this
    exact hpu this
  simp only [mem_insert_iff, mem_singleton_iff] at huin hvin
  have hsegeq : segment ℝ u' v' = segment ℝ u v := by
    rcases huin with h1 | h1 <;> rcases hvin with h2 | h2
    · exact absurd (h1.trans h2.symm) huv
    · rw [h1, h2]
    · rw [h1, h2, segment_symm]
    · exact absurd (h1.trans h2.symm) huv
  exact hsegeq ▸ hconv (subset_convexHull ℝ _ hqe)

theorem Section34CompactCutFrame.path_attach_meet
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    {n k : ℕ} (hk : k ≤ n) {w : ℕ → Section34CompactVertexIndex K K'}
    {e : ℕ → Section34CompactEdgeIndex K K'}
    (he : ∀ i < n, (e i).1 = (w i).1 ∪ (w (i + 1)).1)
    (hinj : ∀ i ≤ n, ∀ j ≤ n, w i = w j → i = j)
    (hfar : ∀ i ≤ n, ∀ j ≤ n, i + 1 < j → ∀ e' : Section34CompactEdgeIndex K K',
      (w i).1 ⊆ e'.1 → (w j).1 ⊆ e'.1 → False)
    {B : Set E3} (hB : ∀ z ∈ B ∩ section34CompactVertexBallImage src f₁ (w 1),
      z ∈ section34CompactVertexBallImage src f₁ (w 0))
    (hB' : ∀ j, 0 < j → j < k →
      Disjoint B (section34CompactVertexBallImage src f₁ (w (j + 1))))
    (hB0 : section34CompactVertexBallImage src f₁ (w 0) ⊆ B) {j : ℕ} (hj : j < k) :
    (B ∪ ⋃ m ∈ Finset.range j, section34CompactVertexBallImage src f₁ (w (m + 1))) ∩
      section34CompactVertexBallImage src f₁ (w (j + 1)) =
        section34CompactSplitDiskImage src f₁ (e j) := by
  have hcons : ∀ i < n, section34CompactVertexBallImage src f₁ (w i) ∩
      section34CompactVertexBallImage src f₁ (w (i + 1)) =
        section34CompactSplitDiskImage src f₁ (e i) := by
    intro i hi
    refine hcut.vertexBallImage_inter_eq_splitDiskImage hf₁ (fun h => ?_) ?_ ?_
    · exact absurd (hinj i hi.le (i + 1) hi h) (by omega)
    · rw [he i hi]
      exact Finset.subset_union_left
    · rw [he i hi]
      exact Finset.subset_union_right
  have hdisj : ∀ i ≤ n, ∀ l ≤ n, i + 1 < l → Disjoint
      (section34CompactVertexBallImage src f₁ (w i))
      (section34CompactVertexBallImage src f₁ (w l)) :=
    fun i hi l hl hil => hcut.disjoint_vertexBallImage_of_forall_not_subset hf₁
      (fun h => absurd (hinj i hi l hl h) (by omega)) (hfar i hi l hl hil)
  apply Subset.antisymm
  · rintro z ⟨hz | hz, hzj⟩
    · by_cases hj0 : j = 0
      · subst hj0
        rw [← hcons 0 (by omega)]
        exact ⟨hB z ⟨hz, hzj⟩, hzj⟩
      · exact absurd hzj (Set.disjoint_left.mp (hB' j (Nat.pos_of_ne_zero hj0) hj) hz)
    · obtain ⟨m, hm, hzm⟩ := mem_iUnion₂.mp hz
      have hm' : m < j := Finset.mem_range.mp hm
      by_cases hmj : m + 1 = j
      · rw [← hcons j (by omega)]
        rw [hmj] at hzm
        exact ⟨hzm, hzj⟩
      · exact absurd hzj (Set.disjoint_left.mp (hdisj (m + 1) (by omega) (j + 1) (by omega)
          (by omega)) hzm)
  · rw [← hcons j (by omega)]
    rintro z ⟨hz, hzj⟩
    refine ⟨?_, hzj⟩
    by_cases hj0 : j = 0
    · subst hj0
      exact mem_union_left _ (hB0 hz)
    · refine mem_union_right _ (mem_iUnion₂.mpr ⟨j - 1, Finset.mem_range.mpr (by omega), ?_⟩)
      rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hj0)]
      exact hz

theorem Section34CompactCutFrame.isPLBall_section34CompactClawBall
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    {t : Finset E3} (ht : t ∈ K.faces) {x y x' y' : E3} (hx : x ∈ t) (hy : y ∈ t)
    (hx' : x' ∈ t) (hy' : y' ∈ t) (hxy : x ≠ y) (hxx' : x ≠ x') (hyy' : y ≠ y')
    (hxy' : x ≠ y') (hyx' : y ≠ x') (hx'y' : x' ≠ y') :
    IsPLBall 3 (section34CompactClawBall (section34CompactVertexBallImage src f₁) x y x' y') := by
  classical
  obtain ⟨-, -, -, -, hsub, -⟩ := id hcut
  have hface : ∀ {a b : E3}, a ∈ t → b ∈ t → ({a, b} : Finset E3) ∈ K.faces := fun ha hb =>
    K.down_closed ht (Finset.insert_subset ha (Finset.singleton_subset_iff.mpr hb))
      (Finset.insert_nonempty _ _)
  have hVball : ∀ w, IsPLBall 3 (section34CompactVertexBallImage src f₁ w) := fun w =>
    (hcut.isPLCellOn_vertexBallImage hf₁ w).isPLBall_three
  have hEball : ∀ e, IsPLBall 2 (section34CompactSplitDiskImage src f₁ e) := fun e => by
    obtain ⟨q, hq, -⟩ :=
      (hcut.isPLCellOn_splitDiskImage hf₁ e).exists_isPLHomeomorphOn_stdSimplex
    exact ⟨q, hq⟩
  have hsegt : ∀ {a b : E3}, a ∈ t → b ∈ t → segment ℝ a b ⊆ convexHull ℝ (t : Set E3) :=
    fun ha hb => (convex_convexHull ℝ _).segment_subset (subset_convexHull ℝ _ ha)
      (subset_convexHull ℝ _ hb)
  have hsing : ∀ {w : Section34CompactVertexIndex K K'} {p : E3}
      (e' : Section34CompactEdgeIndex K K'), w.1 = {p} → w.1 ⊆ e'.1 → p ∈ e'.1 :=
    fun _ hw hwe => hwe (by rw [hw]; exact Finset.mem_singleton_self _)
  have hinc : ∀ (e' : Section34CompactEdgeIndex K K') (p q : E3), p ≠ q → p ∈ e'.1 →
      q ∈ e'.1 → p ∈ convexHull ℝ (t : Set E3) → q ∈ convexHull ℝ (t : Set E3) →
      Section34Incident e'.1 t := by
    intro e' p q hpq hp hq hpt hqt z hz
    have hpair : ({p, q} : Finset E3) = e'.1 := Finset.eq_of_subset_of_card_le
      (Finset.insert_subset hp (Finset.singleton_subset_iff.mpr hq))
      (by rw [e'.2.2.1, Finset.card_pair hpq])
    rw [← hpair] at hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hpt
    · rw [Finset.mem_singleton.mp hz]
      exact hqt
  have hmeet2 : ∀ {a b c : E3}, a ∈ t → b ∈ t → c ∈ t → b ≠ c →
      segment ℝ a b ∩ segment ℝ a c ⊆ {a} := by
    intro a b c ha hb hc hbc z hz
    have h := segment_inter_segment_subset_of_mem_faces (hface ha hb) (hface ha hc) hz
    have hset : ({a, b} : Set E3) ∩ {a, c} ⊆ {a} := by
      rintro u ⟨hu1, hu2⟩
      rcases hu1 with hu1 | hu1
      · rw [hu1]
        exact mem_singleton _
      · rw [mem_singleton_iff.mp hu1] at hu2 ⊢
        rcases hu2 with h' | h'
        · rw [h']
          exact mem_singleton _
        · exact absurd (mem_singleton_iff.mp h') hbc
    have h' := convexHull_mono hset h
    rwa [convexHull_singleton] at h'
  have hmeet0 : ∀ {a b c d : E3}, a ∈ t → b ∈ t → c ∈ t → d ∈ t → a ≠ c → a ≠ d →
      b ≠ c → b ≠ d → Disjoint (segment ℝ a b) (segment ℝ c d) := by
    intro a b c d ha hb hc hd hac had hbc hbd
    refine Set.disjoint_left.mpr fun z hz hz' => ?_
    have h := segment_inter_segment_subset_of_mem_faces (hface ha hb) (hface hc hd) ⟨hz, hz'⟩
    have hset : ({a, b} : Set E3) ∩ {c, d} = ∅ := by
      refine eq_empty_of_forall_notMem fun u hu => ?_
      rcases hu.1 with hu1 | hu1 <;> rcases hu.2 with hu2 | hu2
      · exact hac (hu1.symm.trans hu2)
      · exact had (hu1.symm.trans (mem_singleton_iff.mp hu2))
      · exact hbc ((mem_singleton_iff.mp hu1).symm.trans hu2)
      · exact hbd ((mem_singleton_iff.mp hu1).symm.trans (mem_singleton_iff.mp hu2))
    rw [hset, convexHull_empty] at h
    exact h
  have hmemU : ∀ (B : Set E3) (W : ℕ → Set E3) (k : ℕ) (z : E3),
      z ∈ B ∪ ⋃ j ∈ Finset.range k, W (j + 1) ↔ z ∈ B ∨ ∃ j, 0 < j ∧ j ≤ k ∧ z ∈ W j := by
    intro B W k z
    simp only [mem_union, mem_iUnion, Finset.mem_range, exists_prop]
    constructor
    · rintro (h | ⟨j, hj, hz⟩)
      · exact Or.inl h
      · exact Or.inr ⟨j + 1, by omega, by omega, hz⟩
    · rintro (h | ⟨j, hj0, hjk, hz⟩)
      · exact Or.inl h
      · refine Or.inr ⟨j - 1, by omega, ?_⟩
        rw [Nat.sub_add_cancel hj0]
        exact hz
  obtain ⟨n₀, w₀, e₀, -, hw₀0, hw₀n, hw₀pt, he₀, hw₀inj, hw₀surj, hw₀far⟩ :=
    hcut.exists_vertexIndex_path hxy (hface hx hy)
  obtain ⟨n₁, w₁, e₁, -, hw₁0, hw₁n, hw₁pt, he₁, hw₁inj, hw₁surj, hw₁far⟩ :=
    hcut.exists_vertexIndex_path hxx' (hface hx hx')
  obtain ⟨n₂, w₂, e₂, -, hw₂0, hw₂n, hw₂pt, he₂, hw₂inj, hw₂surj, hw₂far⟩ :=
    hcut.exists_vertexIndex_path hyy' (hface hy hy')
  set V := section34CompactVertexBallImage src f₁
  have hfront : ∀ {e : Section34CompactEdgeIndex K K'} {w w' : Section34CompactVertexIndex K K'},
      e.1 = w.1 ∪ w'.1 → section34CompactSplitDiskImage src f₁ e ⊆ frontier (V w') :=
    fun h => hcut.splitDiskImage_subset_frontier hf₁ (by rw [h]; exact Finset.subset_union_right)
  have hw₁₀ : w₁ 0 = w₀ 0 := Subtype.ext (hw₁0.trans hw₀0.symm)
  have hw₂₀ : w₂ 0 = w₀ n₀ := Subtype.ext (hw₂0.trans hw₀n.symm)
  have hedge : ∀ {w w' : Section34CompactVertexIndex K K'}, w ≠ w' → ∀ z ∈ V w, z ∈ V w' →
      ∃ e' : Section34CompactEdgeIndex K K', w.1 ⊆ e'.1 ∧ w'.1 ⊆ e'.1 := by
    intro w w' hww z hz hz'
    obtain ⟨e', he'⟩ := hcut.exists_mem_splitDiskImage_of_ne hf₁ hww hz hz'
    exact ⟨e', hcut.subset_of_mem_splitDiskImage hf₁ he' hz,
      hcut.subset_of_mem_splitDiskImage hf₁ he' hz'⟩
  have hrigid : ∀ {u v : E3}, u ∈ t → v ∈ t → ∀ {w w' : Section34CompactVertexIndex K K'}
      {p q : E3}, w.1 = {p} → w'.1 = {q} → p ∈ segment ℝ u v → p ≠ u → p ≠ v →
      q ∈ convexHull ℝ (t : Set E3) → p ≠ q → ∀ e' : Section34CompactEdgeIndex K K',
      w.1 ⊆ e'.1 → w'.1 ⊆ e'.1 → q ∈ segment ℝ u v := by
    intro u v hu hv w w' p q hwp hwq hp hpu hpv hqt hpq e' hwe hwe'
    exact mem_segment_of_mem_segment_of_ne_of_incident hsub ht hu hv hp hpu hpv e'
      (hsing e' hwp hwe) (hsing e' hwq hwe')
      (hinc e' p q hpq (hsing e' hwp hwe) (hsing e' hwq hwe')
        (hsegt hu hv hp) hqt)
  have hne : ∀ {w w' : Section34CompactVertexIndex K K'} {p q : E3}, w.1 = {p} →
      w'.1 = {q} → p ≠ q → w ≠ w' := by
    intro w w' p q hwp hwq hpq h
    have h' := congrArg Subtype.val h
    rw [hwp, hwq] at h'
    exact hpq (Finset.singleton_injective h')
  obtain ⟨B₀, hB₀⟩ : ∃ B, B = V (w₀ 0) ∪ ⋃ j ∈ Finset.range n₀, V (w₀ (j + 1)) := ⟨_, rfl⟩
  have hB₀mem : ∀ z ∈ B₀, ∃ i ≤ n₀, z ∈ V (w₀ i) := by
    intro z hz
    rw [hB₀] at hz
    rcases (hmemU _ (fun i => V (w₀ i)) _ _).mp hz with hz | ⟨j, -, hj, hz⟩
    · exact ⟨0, Nat.zero_le _, hz⟩
    · exact ⟨j, hj, hz⟩
  have hB₀sub : ∀ i ≤ n₀, V (w₀ i) ⊆ B₀ := by
    intro i hi z hz
    rw [hB₀]
    refine (hmemU _ (fun i => V (w₀ i)) _ _).mpr ?_
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact Or.inl hz
    · exact Or.inr ⟨i, hi0, hi, hz⟩
  have hB₀ball : IsPLBall 3 B₀ := by
    rw [hB₀]
    refine isPLBall_union_biUnion_range_of_attach (W := fun i => V (w₀ i))
      (S := fun i => section34CompactSplitDiskImage src f₁ (e₀ i)) (hVball _) n₀
      (fun i _ => hVball _) (fun i _ => hEball (e₀ i))
      (fun i hi => hfront (he₀ i hi)) fun j hj => ?_
    refine hcut.path_attach_meet hf₁ le_rfl he₀ hw₀inj hw₀far (fun z hz => hz.1)
      (fun j' _ hj' => hcut.disjoint_vertexBallImage_of_forall_not_subset hf₁
        (fun h => absurd (hw₀inj 0 (Nat.zero_le _) (j' + 1) (by omega) h) (by omega))
        (hw₀far 0 (Nat.zero_le _) (j' + 1) (by omega) (by omega))) subset_rfl hj
  have hopen₁ : ∀ j, 0 < j → j < n₁ → ∀ i ≤ n₀, ∀ z ∈ V (w₀ i), z ∈ V (w₁ j) →
      i = 0 ∧ j = 1 := by
    intro j hj0 hjn i hi z hz hz'
    obtain ⟨q, hq, hwq, hqo⟩ := hw₁pt j hjn.le
    obtain ⟨hqx, hqx'⟩ := hqo hj0 hjn
    obtain ⟨p, hp, hwp, -⟩ := hw₀pt i hi
    have hpq : q ≠ p := by
      rintro rfl
      exact hqx (mem_singleton_iff.mp (hmeet2 hx hy hx' hyx' ⟨hp, hq⟩))
    obtain ⟨e', hje, hie⟩ := hedge (hne hwq hwp hpq) z hz' hz
    have hpseg := hrigid hx hx' hwq hwp hq hqx hqx' (hsegt hx hy hp) hpq e' hje hie
    have hpx : p = x := mem_singleton_iff.mp (hmeet2 hx hy hx' hyx' ⟨hp, hpseg⟩)
    have hi0 : w₀ i = w₀ 0 := Subtype.ext (by rw [hwp, hw₀0, hpx])
    refine ⟨hw₀inj i hi 0 (Nat.zero_le _) hi0, ?_⟩
    by_contra hj1
    rw [hi0, ← hw₁₀] at hie
    exact hw₁far 0 (Nat.zero_le _) j hjn.le (by omega) e' hie hje
  have hopen₂ : ∀ j, 0 < j → j < n₂ → ∀ i ≤ n₀, ∀ z ∈ V (w₀ i), z ∈ V (w₂ j) →
      i = n₀ ∧ j = 1 := by
    intro j hj0 hjn i hi z hz hz'
    obtain ⟨q, hq, hwq, hqo⟩ := hw₂pt j hjn.le
    obtain ⟨hqy, hqy'⟩ := hqo hj0 hjn
    obtain ⟨p, hp, hwp, -⟩ := hw₀pt i hi
    have hp' : p ∈ segment ℝ y x := by
      rw [segment_symm]
      exact hp
    have hpq : q ≠ p := by
      rintro rfl
      exact hqy (mem_singleton_iff.mp (hmeet2 hy hy' hx (Ne.symm hxy') ⟨hq, hp'⟩))
    obtain ⟨e', hje, hie⟩ := hedge (hne hwq hwp hpq) z hz' hz
    have hpseg := hrigid hy hy' hwq hwp hq hqy hqy' (hsegt hx hy hp) hpq e' hje hie
    have hpy : p = y := mem_singleton_iff.mp (hmeet2 hy hy' hx (Ne.symm hxy') ⟨hpseg, hp'⟩)
    have hin : w₀ i = w₀ n₀ := Subtype.ext (by rw [hwp, hw₀n, hpy])
    refine ⟨hw₀inj i hi n₀ le_rfl hin, ?_⟩
    by_contra hj1
    rw [hin, ← hw₂₀] at hie
    exact hw₂far 0 (Nat.zero_le _) j hjn.le (by omega) e' hie hje
  have hopen₁₂ : ∀ j, 0 < j → j < n₁ → ∀ l, 0 < l → l < n₂ →
      Disjoint (V (w₁ j)) (V (w₂ l)) := by
    intro j _ hjn l hl0 hln
    refine Set.disjoint_left.mpr fun z hz hz' => ?_
    obtain ⟨p, hp, hwp, -⟩ := hw₁pt j hjn.le
    obtain ⟨q, hq, hwq, hqo⟩ := hw₂pt l hln.le
    obtain ⟨hqy, hqy'⟩ := hqo hl0 hln
    have hdis := hmeet0 hx hx' hy hy' hxy hxy' hyx'.symm hx'y'
    have hpq : q ≠ p := by
      rintro rfl
      exact Set.disjoint_left.mp hdis hp hq
    obtain ⟨e', hle, hje⟩ := hedge (hne hwq hwp hpq) z hz' hz
    have hpseg := hrigid hy hy' hwq hwp hq hqy hqy' (hsegt hx hx' hp) hpq e' hle hje
    exact Set.disjoint_left.mp hdis hp hpseg
  obtain ⟨B₁, hB₁⟩ : ∃ B, B = B₀ ∪ ⋃ j ∈ Finset.range (n₁ - 1), V (w₁ (j + 1)) :=
    ⟨_, rfl⟩
  have hB₁mem : ∀ z ∈ B₁, (∃ i ≤ n₀, z ∈ V (w₀ i)) ∨
      ∃ j, 0 < j ∧ j < n₁ ∧ z ∈ V (w₁ j) := by
    intro z hz
    rw [hB₁] at hz
    rcases (hmemU _ (fun i => V (w₁ i)) _ _).mp hz with hz | ⟨j, hj0, hj, hz⟩
    · exact Or.inl (hB₀mem z hz)
    · exact Or.inr ⟨j, hj0, by omega, hz⟩
  have hB₁sub₀ : B₀ ⊆ B₁ := by
    rw [hB₁]
    exact subset_union_left
  have hB₁sub : ∀ j, 0 < j → j < n₁ → V (w₁ j) ⊆ B₁ := by
    intro j hj0 hjn z hz
    rw [hB₁]
    exact (hmemU _ (fun i => V (w₁ i)) _ _).mpr (Or.inr ⟨j, hj0, by omega, hz⟩)
  have hB₁ball : IsPLBall 3 B₁ := by
    rw [hB₁]
    refine isPLBall_union_biUnion_range_of_attach (W := fun i => V (w₁ i))
      (S := fun i => section34CompactSplitDiskImage src f₁ (e₁ i)) hB₀ball (n₁ - 1)
      (fun i _ => hVball _) (fun i _ => hEball (e₁ i))
      (fun i hi => hfront (he₁ i (by omega))) fun j hj => ?_
    refine hcut.path_attach_meet hf₁ (Nat.sub_le n₁ 1) he₁ hw₁inj hw₁far ?_ ?_ ?_ hj
    · rintro z ⟨hz, hz'⟩
      obtain ⟨i, hi, hzi⟩ := hB₀mem z hz
      obtain ⟨hi0, -⟩ := hopen₁ 1 one_pos (by omega) i hi z hzi hz'
      subst hi0
      rw [hw₁₀]
      exact hzi
    · intro j' hj'0 hj'
      refine Set.disjoint_left.mpr fun z hz hz' => ?_
      obtain ⟨i, hi, hzi⟩ := hB₀mem z hz
      obtain ⟨-, hj1⟩ := hopen₁ (j' + 1) (by omega) (by omega) i hi z hzi hz'
      omega
    · rw [hw₁₀]
      exact hB₀sub 0 (Nat.zero_le _)
  obtain ⟨B₂, hB₂⟩ : ∃ B, B = B₁ ∪ ⋃ j ∈ Finset.range (n₂ - 1), V (w₂ (j + 1)) :=
    ⟨_, rfl⟩
  have hB₂mem : ∀ z ∈ B₂, (∃ i ≤ n₀, z ∈ V (w₀ i)) ∨
      (∃ j, 0 < j ∧ j < n₁ ∧ z ∈ V (w₁ j)) ∨ ∃ j, 0 < j ∧ j < n₂ ∧ z ∈ V (w₂ j) := by
    intro z hz
    rw [hB₂] at hz
    rcases (hmemU _ (fun i => V (w₂ i)) _ _).mp hz with hz | ⟨j, hj0, hj, hz⟩
    · rcases hB₁mem z hz with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨j, hj0, by omega, hz⟩)
  have hB₂sub₁ : B₁ ⊆ B₂ := by
    rw [hB₂]
    exact subset_union_left
  have hB₂sub : ∀ j, 0 < j → j < n₂ → V (w₂ j) ⊆ B₂ := by
    intro j hj0 hjn z hz
    rw [hB₂]
    exact (hmemU _ (fun i => V (w₂ i)) _ _).mpr (Or.inr ⟨j, hj0, by omega, hz⟩)
  have hB₂ball : IsPLBall 3 B₂ := by
    rw [hB₂]
    refine isPLBall_union_biUnion_range_of_attach (W := fun i => V (w₂ i))
      (S := fun i => section34CompactSplitDiskImage src f₁ (e₂ i)) hB₁ball (n₂ - 1)
      (fun i _ => hVball _) (fun i _ => hEball (e₂ i))
      (fun i hi => hfront (he₂ i (by omega))) fun j hj => ?_
    refine hcut.path_attach_meet hf₁ (Nat.sub_le n₂ 1) he₂ hw₂inj hw₂far ?_ ?_ ?_ hj
    · rintro z ⟨hz, hz'⟩
      rcases hB₁mem z hz with ⟨i, hi, hzi⟩ | ⟨j', hj'0, hj'n, hzj'⟩
      · obtain ⟨hin, -⟩ := hopen₂ 1 one_pos (by omega) i hi z hzi hz'
        rw [hw₂₀, ← hin]
        exact hzi
      · exact absurd hz' (Set.disjoint_left.mp (hopen₁₂ j' hj'0 hj'n 1 one_pos (by omega)) hzj')
    · intro j' hj'0 hj'
      refine Set.disjoint_left.mpr fun z hz hz' => ?_
      rcases hB₁mem z hz with ⟨i, hi, hzi⟩ | ⟨j'', hj''0, hj''n, hzj''⟩
      · obtain ⟨-, hj1⟩ := hopen₂ (j' + 1) (by omega) (by omega) i hi z hzi hz'
        omega
      · exact Set.disjoint_left.mp (hopen₁₂ j'' hj''0 hj''n (j' + 1) (by omega) (by omega))
          hzj'' hz'
    · rw [hw₂₀]
      exact (hB₀sub n₀ le_rfl).trans hB₁sub₀
  have hclaw : section34CompactClawBall V x y x' y' = B₂ := by
    apply Subset.antisymm
    · intro z hz
      obtain ⟨w, ⟨p, hwp, hp⟩, hzw⟩ := mem_iUnion₂.mp hz
      rcases hp with hp | ⟨hp, hpx'⟩ | ⟨hp, hpy'⟩
      · obtain ⟨i, hi, rfl⟩ := hw₀surj w ⟨p, hp, hwp⟩
        exact hB₂sub₁ (hB₁sub₀ (hB₀sub i hi hzw))
      · obtain ⟨i, hi, rfl⟩ := hw₁surj w ⟨p, hp, hwp⟩
        rcases Nat.eq_zero_or_pos i with rfl | hi0
        · rw [hw₁₀] at hzw
          exact hB₂sub₁ (hB₁sub₀ (hB₀sub 0 (Nat.zero_le _) hzw))
        · have hin : i ≠ n₁ := by
            rintro rfl
            rw [hw₁n] at hwp
            exact hpx' (Finset.singleton_injective hwp).symm
          exact hB₂sub₁ (hB₁sub i hi0 (by omega) hzw)
      · obtain ⟨i, hi, rfl⟩ := hw₂surj w ⟨p, hp, hwp⟩
        rcases Nat.eq_zero_or_pos i with rfl | hi0
        · rw [hw₂₀] at hzw
          exact hB₂sub₁ (hB₁sub₀ (hB₀sub n₀ le_rfl hzw))
        · have hin : i ≠ n₂ := by
            rintro rfl
            rw [hw₂n] at hwp
            exact hpy' (Finset.singleton_injective hwp).symm
          exact hB₂sub i hi0 (by omega) hzw
    · have hsubclaw : ∀ (w : Section34CompactVertexIndex K K') (p : E3), w.1 = {p} →
          (p ∈ segment ℝ x y ∨ (p ∈ segment ℝ x x' ∧ p ≠ x') ∨
            (p ∈ segment ℝ y y' ∧ p ≠ y')) → V w ⊆ section34CompactClawBall V x y x' y' :=
        fun w p hwp hp z hz => mem_iUnion₂.mpr ⟨w, ⟨p, hwp, hp⟩, hz⟩
      intro z hz
      rcases hB₂mem z hz with ⟨i, hi, hzi⟩ | ⟨j, hj0, hjn, hzj⟩ | ⟨j, hj0, hjn, hzj⟩
      · obtain ⟨p, hp, hwp, -⟩ := hw₀pt i hi
        exact hsubclaw _ p hwp (Or.inl hp) hzi
      · obtain ⟨p, hp, hwp, hpo⟩ := hw₁pt j hjn.le
        exact hsubclaw _ p hwp (Or.inr (Or.inl ⟨hp, (hpo hj0 hjn).2⟩)) hzj
      · obtain ⟨p, hp, hwp, hpo⟩ := hw₂pt j hjn.le
        exact hsubclaw _ p hwp (Or.inr (Or.inr ⟨hp, (hpo hj0 hjn).2⟩)) hzj
  rw [hclaw]
  exact hB₂ball

end Claw

end DifferentialGeometry.Topology.PiecewiseLinear
