import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchTubeDerivedCells
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryInvariance

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_interior_circle_cell_chain (R Γc : Geometry.SimplicialComplex ℝ E) [Finite R.faces]
    [Finite Γc.faces] (hR : IsCombinatorialManifoldWithBoundary 3 R)
    (hdim : Module.finrank ℝ E = 3) (hΓint : Γc.space ⊆ interior R.space)
    (hΓR : Γc.faces ⊆ R.faces)
    (hΓ : IsCombinatorialManifold 1 Γc) (hconn : IsConnected Γc.space) {s₀ : Finset E}
    (hs₀ : s₀ ∈ Γc.faces) :
    ∃ (m : ℕ) (s : ℕ → Finset E) (D₀ D₁ : ℕ → Set E) (q₀ q₁ : ℕ → (Fin 3 → ℝ) → E)
      (y₀ y₁ : ℕ → E), 2 ≤ m ∧ s 0 = s₀ ∧ (∀ k, s k ∈ Γc.faces) ∧
      (∀ k, (upperLink (barycentricSubdivision R) {(s k).centroid ℝ id}).faces.Finite) ∧
      (∀ k, IsConeBase ((s k).centroid ℝ id)
        (upperLink (barycentricSubdivision R) {(s k).centroid ℝ id})) ∧
      (∀ k, IsPLSphere 2 (upperLink (barycentricSubdivision R) {(s k).centroid ℝ id}).space) ∧
      (∀ k, IsPLHomeomorphOn (q₀ k) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D₀ k)) ∧
      (∀ k, IsPLHomeomorphOn (q₁ k) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D₁ k)) ∧
      (∀ k, D₀ k ⊆ (upperLink (barycentricSubdivision R) {(s k).centroid ℝ id}).space) ∧
      (∀ k, D₁ k ⊆ (upperLink (barycentricSubdivision R) {(s k).centroid ℝ id}).space) ∧
      (∀ k, Disjoint (D₀ k) (D₁ k)) ∧ (∀ k < m, D₁ k = D₀ (k + 1)) ∧ D₁ m = D₀ 0 ∧
      (∀ k < m, (derivedNeighborhoodCell R (s k)).space ∩
        (derivedNeighborhoodCell R (s (k + 1))).space = D₁ k) ∧
      (derivedNeighborhoodCell R (s m)).space ∩ (derivedNeighborhoodCell R (s 0)).space = D₀ 0 ∧
      (∀ j k, j + 1 < k → k ≤ m → (j ≠ 0 ∨ k ≠ m) →
        Disjoint (derivedNeighborhoodCell R (s j)).space (derivedNeighborhoodCell R (s k)).space) ∧
      (⋃ k ≤ m, (derivedNeighborhoodCell R (s k)).space) = (derivedNeighborhood R Γc).space ∧
      (∀ k, y₀ k ∈ D₀ k) ∧ (∀ k, y₁ k ∈ D₁ k) ∧
      (∀ k, Γc.space ∩ (upperLink (barycentricSubdivision R) {(s k).centroid ℝ id}).space =
        {y₀ k, y₁ k}) ∧
      (⋃ k ≤ m, coneSet ((s k).centroid ℝ id) {y₀ k, y₁ k}) = Γc.space ∧
      ∃ t : ℕ → Fin 2 → Finset E,
        (∀ k j, t k j ∈ Γc.faces) ∧ (∀ k j, s k ≠ t k j) ∧
        (∀ k j, s k ⊆ t k j ∨ t k j ⊆ s k) ∧
        (∀ k, D₀ k = (derivedNeighborhoodCell R (s k)).space ∩
          (derivedNeighborhoodCell R (t k 0)).space) ∧
        (∀ k, D₁ k = (derivedNeighborhoodCell R (s k)).space ∩
          (derivedNeighborhoodCell R (t k 1)).space) ∧
        (∀ k, y₀ k = ({(s k).centroid ℝ id, (t k 0).centroid ℝ id} : Finset E).centroid ℝ id) ∧
        ∀ k, y₁ k = ({(s k).centroid ℝ id, (t k 1).centroid ℝ id} : Finset E).centroid ℝ id := by
  obtain ⟨m, s, hm, hs0, hsΓ, hcons, hclose, hdist, hfarF, hsurj⟩ :=
    exists_faceChain_of_isCombinatorialManifold_one Γc hΓ hconn hs₀
  have hRb : IsCombinatorialManifoldWithBoundary (1 + 2) R := hR
  have hΓbd : Disjoint Γc.space (boundaryComplex 3 R).space := by
    rw [← frontier_space_eq_boundaryComplex_space_of_finrank hdim R hR]
    exact disjoint_interior_frontier.mono_left hΓint
  have hsB : ∀ f ∈ Γc.faces, f ∉ (boundaryComplex 3 R).faces := by
    intro f hf hfb
    obtain ⟨x, hx⟩ := Γc.nonempty_of_mem_faces hf
    exact disjoint_left.mp hΓbd (Γc.subset_space hf hx)
      ((boundaryComplex 3 R).subset_space hfb hx)
  have hcard : ∀ f ∈ Γc.faces, Finset.card f ≤ 2 := fun f hf => hΓ.card_le Γc hf
  let ν : ℕ → ℕ := fun k => if k ≤ m then k else 0
  let prv : ℕ → ℕ := fun k => if k = 0 then m else k - 1
  let nxt : ℕ → ℕ := fun k => if k = m then 0 else k + 1
  have hν : ∀ k ≤ m, ν k = k := fun k hk => ite_eq_left hk
  have hνle : ∀ k, ν k ≤ m := by
    intro k
    change (if k ≤ m then k else 0) ≤ m
    split_ifs with h
    · exact h
    · exact Nat.zero_le m
  have hprv0 : prv 0 = m := ite_eq_left rfl
  have hprvS : ∀ k, prv (k + 1) = k := fun k => by
    change (if k + 1 = 0 then m else k + 1 - 1) = k
    rw [ite_eq_right (Nat.succ_ne_zero k), Nat.add_sub_cancel]
  have hnxtm : nxt m = 0 := ite_eq_left rfl
  have hnxtlt : ∀ k < m, nxt k = k + 1 := fun k hk => ite_eq_right hk.ne
  have hprvle : ∀ a ≤ m, prv a ≤ m := by
    intro a ha
    rcases Nat.eq_zero_or_pos a with rfl | h
    · rw [hprv0]
    · obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      rw [hprvS]
      omega
  have hnxtle : ∀ a ≤ m, nxt a ≤ m := by
    intro a ha
    rcases eq_or_lt_of_le ha with rfl | h
    · rw [hnxtm]
      exact Nat.zero_le _
    · rw [hnxtlt a h]
      omega
  have hne : ∀ i j, i ≤ m → j ≤ m → i ≠ j → s i ≠ s j := by
    intro i j hi hj hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hdist i j h hj
    · exact (hdist j i h hi).symm
  have hcompP : ∀ a ≤ m, s (prv a) ≠ s a ∧ (s (prv a) ⊆ s a ∨ s a ⊆ s (prv a)) := by
    intro a ha
    rcases Nat.eq_zero_or_pos a with rfl | h
    · rw [hprv0]
      exact hclose
    · obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      rw [hprvS]
      exact hcons b (by omega)
  have hcompN : ∀ a ≤ m, s a ≠ s (nxt a) ∧ (s a ⊆ s (nxt a) ∨ s (nxt a) ⊆ s a) := by
    intro a ha
    rcases eq_or_lt_of_le ha with rfl | h
    · rw [hnxtm]
      exact ⟨hclose.1, hclose.2⟩
    · rw [hnxtlt a h]
      exact hcons a h
  have hPN : ∀ a ≤ m, s (prv a) ≠ s (nxt a) := by
    intro a ha
    apply hne _ _ (hprvle a ha) (hnxtle a ha)
    rcases Nat.eq_zero_or_pos a with rfl | h
    · rw [hprv0, hnxtlt 0 (by omega)]
      omega
    · obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      rw [hprvS]
      rcases eq_or_lt_of_le ha with h' | h'
      · rw [h', hnxtm]
        omega
      · rw [hnxtlt _ h']
        omega
  have hR' : ∀ k, s k ∈ R.faces := fun k => hΓR (hsΓ k)
  have hcellcone : ∀ f ∈ R.faces, (derivedNeighborhoodCell R f).space =
      coneSet (f.centroid ℝ id) (upperLink (barycentricSubdivision R) {f.centroid ℝ id}).space :=
    fun f hf => derivedNeighborhoodCell_space_eq_coneSet R hf
  have hball : ∀ i j, i ≤ m → j ≤ m → s i ≠ s j → (s i ⊆ s j ∨ s j ⊆ s i) →
      IsPLBall 2 ((derivedNeighborhoodCell R (s i)).space ∩
        (derivedNeighborhoodCell R (s j)).space) :=
    fun i j _ _ hij hc => hRb.isPLBall_derivedNeighborhoodCell_inter (hR' i) (hR' j) hij hc
  have hball₀ : ∀ k, IsPLBall 2 ((derivedNeighborhoodCell R (s (prv (ν k)))).space ∩
      (derivedNeighborhoodCell R (s (ν k))).space) := fun k =>
    hball _ _ (hprvle _ (hνle k)) (hνle k) (hcompP _ (hνle k)).1 (hcompP _ (hνle k)).2
  have hball₁ : ∀ k, IsPLBall 2 ((derivedNeighborhoodCell R (s (ν k))).space ∩
      (derivedNeighborhoodCell R (s (nxt (ν k)))).space) := fun k =>
    hball _ _ (hνle k) (hnxtle _ (hνle k)) (hcompN _ (hνle k)).1 (hcompN _ (hνle k)).2
  choose q₀ hq₀ using hball₀
  choose q₁ hq₁ using hball₁
  have hcapP : ∀ a ≤ m, (derivedNeighborhoodCell R (s (prv a))).space ∩
      (derivedNeighborhoodCell R (s a)).space =
        coneSet (({(s (prv a)).centroid ℝ id, (s a).centroid ℝ id} : Finset E).centroid ℝ id)
          (upperLink (barycentricSubdivision R)
            {(s (prv a)).centroid ℝ id, (s a).centroid ℝ id}).space :=
    fun a ha => derivedNeighborhoodCell_inter_eq_coneSet R (hR' _) (hR' _) (hcompP a ha).2
  have hcapN : ∀ a ≤ m, (derivedNeighborhoodCell R (s a)).space ∩
      (derivedNeighborhoodCell R (s (nxt a))).space =
        coneSet (({(s a).centroid ℝ id, (s (nxt a)).centroid ℝ id} : Finset E).centroid ℝ id)
          (upperLink (barycentricSubdivision R)
            {(s a).centroid ℝ id, (s (nxt a)).centroid ℝ id}).space :=
    fun a ha => derivedNeighborhoodCell_inter_eq_coneSet R (hR' _) (hR' _) (hcompN a ha).2
  have hD₀S' : ∀ a ≤ m, (derivedNeighborhoodCell R (s (prv a))).space ∩
      (derivedNeighborhoodCell R (s a)).space ⊆
        (upperLink (barycentricSubdivision R) {(s a).centroid ℝ id}).space := by
    intro a ha
    rw [hcapP a ha]
    exact coneSet_pair_centroid_subset_upperLink_right R (hR' _) (hR' _) (hcompP a ha).1
      (hcompP a ha).2
  have hD₁S' : ∀ a ≤ m, (derivedNeighborhoodCell R (s a)).space ∩
      (derivedNeighborhoodCell R (s (nxt a))).space ⊆
        (upperLink (barycentricSubdivision R) {(s a).centroid ℝ id}).space := by
    intro a ha
    rw [hcapN a ha]
    exact coneSet_pair_centroid_subset_upperLink R (hR' _) (hR' _) (hcompN a ha).1
      (hcompN a ha).2
  have hdis' : ∀ a ≤ m, Disjoint ((derivedNeighborhoodCell R (s (prv a))).space ∩
      (derivedNeighborhoodCell R (s a)).space) ((derivedNeighborhoodCell R (s a)).space ∩
        (derivedNeighborhoodCell R (s (nxt a))).space) := fun a ha =>
    (disjoint_derivedNeighborhoodCell_inter_of_card_le_two R Γc hΓR hcard (hsΓ _) (hsΓ _)
      (hsΓ _) (hcompP a ha).1 (hPN a ha) (hcompN a ha).1).mono_right inter_subset_right
  have hy₀' : ∀ a ≤ m,
      ({(s (prv a)).centroid ℝ id, (s a).centroid ℝ id} : Finset E).centroid ℝ id ∈
        (derivedNeighborhoodCell R (s (prv a))).space ∩ (derivedNeighborhoodCell R (s a)).space :=
    fun a ha => by
      rw [hcapP a ha]
      exact apex_mem_coneSet _ _
  have hy₁' : ∀ a ≤ m,
      ({(s a).centroid ℝ id, (s (nxt a)).centroid ℝ id} : Finset E).centroid ℝ id ∈
        (derivedNeighborhoodCell R (s a)).space ∩ (derivedNeighborhoodCell R (s (nxt a))).space :=
    fun a ha => by
      rw [hcapN a ha]
      exact apex_mem_coneSet _ _
  have hΓS : ∀ f ∈ Γc.faces, Γc.space ∩
      (upperLink (barycentricSubdivision R) {f.centroid ℝ id}).space =
        (upperLink (barycentricSubdivision Γc) {f.centroid ℝ id}).space := by
    intro f hf
    have hcone := coneSet_upperLink_inter_subcomplex R Γc hΓR hf
    have hYS := upperLink_space_subset_of_faces_subset hΓR {f.centroid ℝ id}
    have hK := isConeBase_centroid_upperLink R (hΓR hf)
    apply Subset.antisymm
    · rintro x ⟨hxΓ, hxS⟩
      have hx : x ∈ coneSet (f.centroid ℝ id)
          (upperLink (barycentricSubdivision Γc) {f.centroid ℝ id}).space ∩
            (upperLink (barycentricSubdivision R) {f.centroid ℝ id}).space := by
        rw [← hcone]
        exact ⟨⟨subset_coneSet _ _ hxS, hxΓ⟩, hxS⟩
      rw [coneSet_inter_of_isRadiallyInjective hK.radial hK.notMem_space hYS subset_rfl] at hx
      exact hx.1
    · intro x hx
      refine ⟨?_, hYS hx⟩
      have hx' : x ∈ coneSet (f.centroid ℝ id)
          (upperLink (barycentricSubdivision Γc) {f.centroid ℝ id}).space :=
        subset_coneSet _ _ hx
      rw [← hcone] at hx'
      exact hx'.2
  have hpoles : ∀ a ≤ m, Γc.space ∩
      (upperLink (barycentricSubdivision R) {(s a).centroid ℝ id}).space =
        {({(s (prv a)).centroid ℝ id, (s a).centroid ℝ id} : Finset E).centroid ℝ id,
          ({(s a).centroid ℝ id, (s (nxt a)).centroid ℝ id} : Finset E).centroid ℝ id} := by
    intro a ha
    have hY0 : IsPLSphere (0 - 0)
        (upperLink (barycentricSubdivision Γc) {(s a).centroid ℝ id}).space :=
      hΓ.barycentricSubdivision.isPLSphere_upperLink _
        (singleton_centroid_mem_barycentricSubdivision Γc (hsΓ a)) (k := 0)
        (Finset.card_singleton _) le_rfl
    obtain ⟨u, v, huv, hY⟩ := isPLSphere_zero_iff.mp hY0
    rw [hΓS _ (hsΓ a), hY]
    have hmem₀ : ({(s (prv a)).centroid ℝ id, (s a).centroid ℝ id} : Finset E).centroid ℝ id ∈
        ({u, v} : Set E) := by
      rw [← hY, ← hΓS _ (hsΓ a)]
      exact ⟨pair_centroid_mem_space_of_subset (hsΓ _) (hsΓ _) (hcompP a ha).2,
        hD₀S' a ha (hy₀' a ha)⟩
    have hmem₁ : ({(s a).centroid ℝ id, (s (nxt a)).centroid ℝ id} : Finset E).centroid ℝ id ∈
        ({u, v} : Set E) := by
      rw [← hY, ← hΓS _ (hsΓ a)]
      exact ⟨pair_centroid_mem_space_of_subset (hsΓ _) (hsΓ _) (hcompN a ha).2,
        hD₁S' a ha (hy₁' a ha)⟩
    have hne₀₁ : ({(s (prv a)).centroid ℝ id, (s a).centroid ℝ id} : Finset E).centroid ℝ id ≠
        ({(s a).centroid ℝ id, (s (nxt a)).centroid ℝ id} : Finset E).centroid ℝ id :=
      fun h => disjoint_left.mp (hdis' a ha) (hy₀' a ha) (h ▸ hy₁' a ha)
    rcases hmem₀ with h₀ | h₀ <;> rcases hmem₁ with h₁ | h₁
    · exact absurd (h₀.trans h₁.symm) hne₀₁
    · rw [h₀, h₁]
    · rw [h₀, h₁, pair_comm]
    · exact absurd (h₀.trans h₁.symm) hne₀₁
  refine ⟨m, fun k => s (ν k),
    fun k => (derivedNeighborhoodCell R (s (prv (ν k)))).space ∩
      (derivedNeighborhoodCell R (s (ν k))).space,
    fun k => (derivedNeighborhoodCell R (s (ν k))).space ∩
      (derivedNeighborhoodCell R (s (nxt (ν k)))).space, q₀, q₁,
    fun k => ({(s (prv (ν k))).centroid ℝ id, (s (ν k)).centroid ℝ id} : Finset E).centroid ℝ id,
    fun k => ({(s (ν k)).centroid ℝ id, (s (nxt (ν k))).centroid ℝ id} : Finset E).centroid ℝ id,
    hm, ?_, fun k => hsΓ _, fun k => upperLink_faces_finite _ _,
    fun k => isConeBase_centroid_upperLink R (hR' _),
    fun k => hR.isPLSphere_upperLink_centroid_of_not_mem_boundaryComplex
      (hR' _) (hsB _ (hsΓ _)), hq₀, hq₁,
    fun k => hD₀S' _ (hνle k), fun k => hD₁S' _ (hνle k), fun k => hdis' _ (hνle k), ?_, ?_, ?_,
    ?_, ?_, ?_, fun k => hy₀' _ (hνle k), fun k => hy₁' _ (hνle k),
    fun k => hpoles _ (hνle k), ?_, ?_⟩
  · change s (ν 0) = s₀
    rw [hν 0 (Nat.zero_le m), hs0]
  · intro k hk
    change (derivedNeighborhoodCell R (s (ν k))).space ∩
        (derivedNeighborhoodCell R (s (nxt (ν k)))).space =
      (derivedNeighborhoodCell R (s (prv (ν (k + 1))))).space ∩
        (derivedNeighborhoodCell R (s (ν (k + 1)))).space
    rw [hν k hk.le, hν (k + 1) hk, hnxtlt k hk, hprvS]
  · change (derivedNeighborhoodCell R (s (ν m))).space ∩
        (derivedNeighborhoodCell R (s (nxt (ν m)))).space =
      (derivedNeighborhoodCell R (s (prv (ν 0)))).space ∩
        (derivedNeighborhoodCell R (s (ν 0))).space
    rw [hν m le_rfl, hnxtm, hν 0 (Nat.zero_le m), hprv0]
  · intro k hk
    change (derivedNeighborhoodCell R (s (ν k))).space ∩
        (derivedNeighborhoodCell R (s (ν (k + 1)))).space =
      (derivedNeighborhoodCell R (s (ν k))).space ∩
        (derivedNeighborhoodCell R (s (nxt (ν k)))).space
    rw [hν k hk.le, hν (k + 1) hk, hnxtlt k hk]
  · change (derivedNeighborhoodCell R (s (ν m))).space ∩
        (derivedNeighborhoodCell R (s (ν 0))).space =
      (derivedNeighborhoodCell R (s (prv (ν 0)))).space ∩
        (derivedNeighborhoodCell R (s (ν 0))).space
    rw [hν m le_rfl, hν 0 (Nat.zero_le m), hprv0]
  · intro j k hjk hk hjm
    change Disjoint (derivedNeighborhoodCell R (s (ν j))).space
      (derivedNeighborhoodCell R (s (ν k))).space
    rw [hν j (by omega), hν k hk]
    rw [disjoint_iff_inter_eq_empty]
    by_contra hne'
    exact hfarF j k hjk hk hjm (subset_or_subset_of_nonempty_derivedNeighborhoodCell_inter R
      (hR' j) (hR' k) (nonempty_iff_ne_empty.mpr hne'))
  · rw [← iUnion_derivedNeighborhoodCell_space R Γc hΓR]
    apply Subset.antisymm
    · intro x hx
      obtain ⟨k, -, hxk⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion₂.mpr ⟨s (ν k), hsΓ _, hxk⟩
    · intro x hx
      obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hx
      obtain ⟨k, hk, rfl⟩ := hsurj f hf
      refine mem_iUnion₂.mpr ⟨k, hk, ?_⟩
      change x ∈ (derivedNeighborhoodCell R (s (ν k))).space
      rw [hν k hk]
      exact hxf
  · apply Subset.antisymm
    · intro x hx
      obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx
      change x ∈ coneSet ((s (ν k)).centroid ℝ id)
        {({(s (prv (ν k))).centroid ℝ id, (s (ν k)).centroid ℝ id} : Finset E).centroid ℝ id,
          ({(s (ν k)).centroid ℝ id, (s (nxt (ν k))).centroid ℝ id} : Finset E).centroid ℝ id}
        at hxk
      rw [← hpoles _ (hνle k), hΓS _ (hsΓ _), ← coneSet_upperLink_inter_subcomplex R Γc hΓR
        (hsΓ _)] at hxk
      exact hxk.2
    · intro x hx
      have hxN := subcomplex_space_subset_derivedNeighborhood hΓR hx
      rw [← iUnion_derivedNeighborhoodCell_space R Γc hΓR] at hxN
      obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hxN
      obtain ⟨k, hk, rfl⟩ := hsurj f hf
      refine mem_iUnion₂.mpr ⟨k, hk, ?_⟩
      change x ∈ coneSet ((s (ν k)).centroid ℝ id)
        {({(s (prv (ν k))).centroid ℝ id, (s (ν k)).centroid ℝ id} : Finset E).centroid ℝ id,
          ({(s (ν k)).centroid ℝ id, (s (nxt (ν k))).centroid ℝ id} : Finset E).centroid ℝ id}
      rw [← hpoles _ (hνle k), hΓS _ (hsΓ _), ← coneSet_upperLink_inter_subcomplex R Γc hΓR
        (hsΓ _), hν k hk, ← hcellcone _ (hR' k)]
      exact ⟨hxf, hx⟩
  · refine ⟨fun k j => if j = 0 then s (prv (ν k)) else s (nxt (ν k)),
      fun k j => ?_, fun k j => ?_, fun k j => ?_, fun k => ?_, fun k => ?_,
      fun k => ?_, fun k => ?_⟩
    · dsimp only
      split_ifs <;> exact hsΓ _
    · dsimp only
      split_ifs
      · exact (hcompP _ (hνle k)).1.symm
      · exact (hcompN _ (hνle k)).1
    · dsimp only
      split_ifs
      · exact (hcompP _ (hνle k)).2.symm
      · exact (hcompN _ (hνle k)).2
    · simp [inter_comm]
    · simp
    · simp [Finset.pair_comm]
    · simp

end DifferentialGeometry.Topology.PiecewiseLinear
