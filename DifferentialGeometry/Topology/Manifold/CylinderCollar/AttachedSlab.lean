import DifferentialGeometry.Topology.OpenPartialHomeomorph.GraphOrientation
import DifferentialGeometry.Topology.Manifold.ProductChartCollar
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens

set_option autoImplicit false
noncomputable section

open Set Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
    {M : Type*} [TopologicalSpace M] [ChartedSpace G M]

theorem exists_smoothTwoSidedCollar_of_attached_slab
    [CompactSpace N] [PreconnectedSpace N]
    (P : _root_.PartialDiffeomorph (I.prod 𝓘(ℝ)) J (N × ℝ) M ∞)
    (hsource : univ ×ˢ Icc (0 : ℝ) 1 ⊆ P.source) {K S : Set M}
    (hregular : closure (interior K) = K) (hS : IsClosed S)
    (hfront : frontier K = range (fun q : N => P (q, 0)) ∪ S)
    (hdisjoint : Disjoint (range (fun q : N => P (q, 0))) S)
    (hinter : P '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ K = range (fun q : N => P (q, 0))) :
    ∃ c : SmoothTwoSidedCollar I J (fun q => P (q, 0)),
      c.radius < 1 ∧
      (∀ q t, t ∈ Icc (-c.radius) c.radius → (q, t) ∈ P.source) ∧
      (∀ z : N × symmetricOpenInterval c.radius, c.toFun z = P (z.1, z.2.val)) ∧
      (∀ z : N × symmetricOpenInterval c.radius, c.toFun z ∈ K ↔ z.2.val ≤ 0) ∧
      ∀ z : N × symmetricOpenInterval c.radius,
        z.2.val < 0 → c.toFun z ∈ interior K := by
  classical
  have hzero (q : N) : (q, (0 : ℝ)) ∈ P.source :=
    hsource ⟨mem_univ _, le_rfl, zero_le_one⟩
  obtain ⟨r, hr, horient⟩ := exists_cylinder_orientation_of_frontier_eq_union
    P.toOpenPartialHomeomorph hzero hregular hS hfront hdisjoint
  have hout (q : N) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) : P (q, t) ∉ K := by
    intro hin
    have hmem : P (q, t) ∈ P '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ K :=
      ⟨⟨(q, t), ⟨mem_univ _, ht.1.le, ht.2⟩, rfl⟩, hin⟩
    obtain ⟨q', hq'⟩ := hinter ▸ hmem
    have heq := P.toOpenPartialHomeomorph.injOn (hzero q')
      (hsource ⟨mem_univ _, ht.1.le, ht.2⟩) hq'
    exact ht.1.ne (congrArg Prod.snd heq)
  have hside : ∀ q : N, ∀ t ∈ Ioo (0 : ℝ) r,
      P (q, t) ∉ K ∧ P (q, -t) ∈ interior K := by
    rcases horient with h | h
    · exact h
    · intro q t ht
      let a : ℝ := min r 1 / 2
      have ha : 0 < a := by dsimp [a]; positivity
      have har : a < r := by dsimp [a]; have := min_le_left r 1; linarith
      have haone : a ≤ 1 := by dsimp [a]; have := min_le_right r 1; linarith
      exact False.elim (hout q a ⟨ha, haone⟩ (interior_subset ((h q a ⟨ha, har⟩).2)))
  let O : TopologicalSpace.Opens (N × ℝ) := ⟨P.source, P.open_source⟩
  let Φ := DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo P
    (U := O) (Subset.rfl)
  obtain ⟨c, hcr, hstrip, hmap⟩ :=
    exists_smoothTwoSidedCollar_of_product_chart_graph O _ Φ (fun _ => 0)
      contMDiff_const hzero (lt_min hr zero_lt_one)
  change SmoothTwoSidedCollar I J (fun q => P (q, 0)) at c
  have hcmap (z : N × symmetricOpenInterval c.radius) : c.toFun z = P (z.1, z.2.val) := by
    obtain ⟨_, hz⟩ := hmap z
    change c.toFun z = P (z.1, 0 + z.2.val) at hz
    simpa only [zero_add] using hz
  refine ⟨c, hcr.trans_le (min_le_right _ _), ?_, hcmap, ?_, ?_⟩
  · intro q t ht
    have hs := hstrip q t ht
    change (q, 0 + t) ∈ P.source at hs
    simpa only [zero_add] using hs
  · intro z
    rw [hcmap]
    constructor
    · intro hz
      by_contra h
      have ht : z.2.val ∈ Ioo (0 : ℝ) r :=
        ⟨lt_of_not_ge h, z.2.property.2.trans (hcr.trans_le (min_le_left _ _))⟩
      exact (hside z.1 z.2.val ht).1 hz
    · intro ht
      rcases lt_or_eq_of_le ht with ht | ht
      · have hn : -z.2.val ∈ Ioo (0 : ℝ) r := by
          constructor
          · exact neg_pos.mpr ht
          · have := z.2.property.1
            have := hcr.trans_le (min_le_left _ _)
            linarith
        simpa only [neg_neg] using interior_subset ((hside z.1 (-z.2.val) hn).2)
      · rw [ht]
        have hK : IsClosed K := hregular ▸ isClosed_closure
        apply hK.frontier_subset
        rw [hfront]
        exact Or.inl (mem_range_self z.1)
  · intro z ht
    rw [hcmap]
    have hn : -z.2.val ∈ Ioo (0 : ℝ) r := by
      constructor
      · exact neg_pos.mpr ht
      · have := z.2.property.1
        have := hcr.trans_le (min_le_left _ _)
        linarith
    simpa only [neg_neg] using (hside z.1 (-z.2.val) hn).2


theorem exists_smoothTwoSidedCollar_of_half_cylinder_first_slab
    [CompactSpace N] [PreconnectedSpace N]
    (P : _root_.PartialDiffeomorph (I.prod 𝓘(ℝ)) J (N × ℝ) M ∞)
    (hsource : univ ×ˢ Icc (0 : ℝ) 1 ⊆ P.source)
    (Θ : N × ℝ → M) (hfirst : ∀ q t, t ∈ Icc (0 : ℝ) 1 → Θ (q, t) = P (q, t))
    {K S : Set M} (hregular : closure (interior K) = K) (hS : IsClosed S)
    (hfront : frontier K = range (fun q : N => Θ (q, 0)) ∪ S)
    (hdisjoint : Disjoint (range (fun q : N => Θ (q, 0))) S)
    (hinter : Θ '' (univ ×ˢ Ici (0 : ℝ)) ∩ K = range (fun q : N => Θ (q, 0))) :
    ∃ c : SmoothTwoSidedCollar I J (fun q => Θ (q, 0)),
      c.radius < 1 ∧
      (∀ q t, t ∈ Icc (-c.radius) c.radius → (q, t) ∈ P.source) ∧
      (∀ z : N × symmetricOpenInterval c.radius, c.toFun z = P (z.1, z.2.val)) ∧
      (∀ z : N × symmetricOpenInterval c.radius, c.toFun z ∈ K ↔ z.2.val ≤ 0) ∧
      (∀ z : N × symmetricOpenInterval c.radius,
        z.2.val < 0 → c.toFun z ∈ interior K) ∧
      ∀ z : N × symmetricOpenInterval c.radius,
        0 ≤ z.2.val → c.toFun z = Θ (z.1, z.2.val) := by
  have hzero (q : N) : Θ (q, 0) = P (q, 0) := hfirst q 0 ⟨le_rfl, zero_le_one⟩
  have hbase : (fun q => Θ (q, 0)) = (fun q => P (q, 0)) := funext hzero
  have hslab : P '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ K = range (fun q : N => P (q, 0)) := by
    ext x
    constructor
    · rintro ⟨⟨⟨q, t⟩, ht, rfl⟩, hxK⟩
      have hx : P (q, t) ∈ Θ '' (univ ×ˢ Ici (0 : ℝ)) ∩ K :=
        ⟨⟨(q, t), ⟨mem_univ _, ht.2.1⟩, hfirst q t ht.2⟩, hxK⟩
      rw [hinter, hbase] at hx
      exact hx
    · rintro ⟨q, rfl⟩
      refine ⟨⟨(q, 0), ⟨mem_univ _, le_rfl, zero_le_one⟩, rfl⟩, ?_⟩
      have hx : P (q, 0) ∈ range (fun q : N => Θ (q, 0)) := ⟨q, hzero q⟩
      rw [← hinter] at hx
      exact hx.2
  obtain ⟨c, hc, hs, hmap, hcore, hnegative⟩ :=
    exists_smoothTwoSidedCollar_of_attached_slab P hsource hregular hS
      (hbase ▸ hfront) (hbase ▸ hdisjoint) hslab
  rw [hbase]
  refine ⟨c, hc, hs, hmap, hcore, hnegative, ?_⟩
  intro z ht
  exact (hmap z).trans (hfirst z.1 z.2.val ⟨ht, (z.2.property.2.trans hc).le⟩).symm

end DifferentialGeometry.Topology
