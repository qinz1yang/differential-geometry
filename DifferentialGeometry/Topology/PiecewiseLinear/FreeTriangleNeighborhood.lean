import DifferentialGeometry.Topology.PiecewiseLinear.FreeTriangleFaces
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexDerivedNeighborhood

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
open Classical in
theorem derivedNeighborhoodCell_inter_derivedNeighborhood_eq_subfaces
    (K L : Geometry.SimplicialComplex ℝ E) (hLK : L.faces ⊆ K.faces)
    {s : Finset E} (hsK : s ∈ K.faces) (hsL : s ∉ L.faces) :
    (derivedNeighborhoodCell K s).space ∩ (derivedNeighborhood K L).space =
      (derivedNeighborhoodCell K s).space ∩
        ⋃ r ∈ s.powerset.filter (fun r => r ∈ L.faces),
          (derivedNeighborhoodCell K r).space := by
  classical
  rw [← iUnion_derivedNeighborhoodCell_space K L hLK]
  apply Subset.antisymm
  · rintro x ⟨hxs, hxL⟩
    obtain ⟨r, hrL, hxr⟩ := mem_iUnion₂.mp hxL
    have hrK := hLK hrL
    rcases subset_or_subset_of_nonempty_derivedNeighborhoodCell_inter K hsK hrK
        ⟨x, hxs, hxr⟩ with hsr | hrs
    · exact (hsL (L.down_closed hrL hsr (K.nonempty_of_mem_faces hsK))).elim
    · exact ⟨hxs, mem_iUnion₂.mpr ⟨r,
        Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hrs, hrL⟩, hxr⟩⟩
  · rintro x ⟨hxs, hxL⟩
    obtain ⟨r, hr, hxr⟩ := mem_iUnion₂.mp hxL
    exact ⟨hxs, mem_iUnion₂.mpr ⟨r, (Finset.mem_filter.mp hr).2, hxr⟩⟩

open Classical in
private theorem face_subset_of_sdiff_subset_free_triangle
    (A : Geometry.SimplicialComplex ℝ E) [Finite A.faces] (hA : IsPLBall 2 A.space)
    {t s r : Finset E} (htcard : t.card = 3)
    (hst : s ⊆ t) (hscard : s.card = 1 ∨ s.card = 2)
    (hinter : ∀ u ∈ A.faces, u.card = 3 → ¬s ⊆ u →
      (u ∩ t).card ≤ 1 ∧ (s.card = 2 → u ∩ t ⊆ s))
    (hr : r ∈ A.faces) (hqr : t \ s ⊆ r) : r ⊆ t := by
  classical
  obtain ⟨u, hu, hru, hucard⟩ := exists_face_superset_card_eq_of_isPLBall A hA hr
  by_cases hsu : s ⊆ u
  · have htu : t ⊆ u := by
      intro v hv
      by_cases hvs : v ∈ s
      · exact hsu hvs
      · exact hru (hqr (Finset.mem_sdiff.mpr ⟨hv, hvs⟩))
    have heq : t = u := Finset.eq_of_subset_of_card_le htu (by omega)
    exact heq ▸ hru
  · have hi := hinter u hu hucard hsu
    have hqint : t \ s ⊆ u ∩ t := by
      intro v hv
      exact Finset.mem_inter.mpr ⟨hru (hqr hv), (Finset.mem_sdiff.mp hv).1⟩
    rcases hscard with hscard | hscard
    · have hc := Finset.card_le_card hqint
      rw [Finset.card_sdiff_of_subset hst, htcard, hscard] at hc
      omega
    · obtain ⟨v, hv⟩ : (t \ s).Nonempty := Finset.card_pos.mp (by
        rw [Finset.card_sdiff_of_subset hst, htcard, hscard]
        decide)
      exact ((Finset.mem_sdiff.mp hv).2 (hi.2 hscard (hqint hv))).elim

open Classical in
private theorem isPLBall_derivedNeighborhoodCell_inter_edge
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    {t s : Finset E} (ht : t ∈ (boundaryComplex 3 K).faces)
    (hs : s ∈ K.faces) (htcard : t.card = 3) (hscard : s.card = 2)
    (hst : s ⊆ t) :
    IsPLBall 2 ((derivedNeighborhoodCell K t).space ∩
      ((derivedNeighborhoodCell K s).space ∪
        ⋃ v ∈ s, (derivedNeighborhoodCell K {v}).space)) := by
  classical
  let C := fun r : Finset E => (derivedNeighborhoodCell K r).space
  let B := (derivedNeighborhoodCellBase K t).space
  let A := fun v : E => C t ∩ C {v}
  have htK := boundaryComplex_faces_subset 3 K ht
  have hts : t ≠ s := by
    intro heq
    have hc := congrArg Finset.card heq
    omega
  have hbase : IsPLBall 2 B := hK.isPLBall_derivedNeighborhoodCellBase ht
  have hcenter : IsPLBall 2 (C t ∩ C s) :=
    hK.isPLBall_derivedNeighborhoodCell_inter htK hs hts (Or.inr hst)
  have hcenterB : C t ∩ C s ⊆ B :=
    derivedNeighborhoodCell_inter_subset_base K htK hs hts
  have hvK (v : E) (hv : v ∈ s) : {v} ∈ K.faces :=
    K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  have hvt (v : E) (hv : v ∈ s) : v ∈ t := hst hv
  have htne (v : E) : t ≠ {v} := by
    intro heq
    have hc := congrArg Finset.card heq
    simp only [Finset.card_singleton, htcard] at hc
    omega
  have hsne (v : E) : s ≠ {v} := by
    intro heq
    have hc := congrArg Finset.card heq
    simp only [Finset.card_singleton, hscard] at hc
    omega
  have hA (v : E) (hv : v ∈ s) : IsPLBall 2 (A v) :=
    hK.isPLBall_derivedNeighborhoodCell_inter htK (hvK v hv)
      (htne v)
      (Or.inr (Finset.singleton_subset_iff.mpr (hvt v hv)))
  have hAB (v : E) (hv : v ∈ s) : A v ⊆ B :=
    derivedNeighborhoodCell_inter_subset_base K htK (hvK v hv)
      (htne v)
  have hI (v : E) (hv : v ∈ s) : IsPLBall 1 ((C t ∩ C s) ∩ A v) := by
    have heq : (C t ∩ C s) ∩ A v = C t ∩ C s ∩ C {v} := by
      ext x
      simp only [C, A, mem_inter_iff]
      tauto
    rw [heq]
    exact hK.isPLBall_derivedNeighborhoodCell_inter_inter htK hs (hvK v hv) hts
      (htne v) (hsne v)
      (Or.inr hst) (Or.inr (Finset.singleton_subset_iff.mpr (hvt v hv)))
      (Or.inr (Finset.singleton_subset_iff.mpr hv))
  have hdis (v : E) (hv : v ∈ s) (w : E) (hw : w ∈ s) (hvw : v ≠ w) :
      Disjoint (A v) (A w) :=
    (disjoint_derivedNeighborhoodCell_space K (hvK v hv) (hvK w hw)
      (by simpa only [Finset.singleton_subset_iff, Finset.mem_singleton] using hvw)
      (by simpa only [Finset.singleton_subset_iff, Finset.mem_singleton] using hvw.symm)).mono
        inter_subset_right inter_subset_right
  have hball := isPLBall_union_iUnion_of_pairwiseDisjoint_in_ball hbase hcenter hcenterB
    s A hA hAB hI hdis
  simpa only [C, A, inter_union_distrib_left, inter_iUnion] using hball

open Classical in
private theorem iUnion_eraseTriangleComplex_subfaces_eq_edge
    (A : Geometry.SimplicialComplex ℝ E) [Finite A.faces] (hA : IsPLBall 2 A.space)
    {t s : Finset E} (ht : t ∈ A.faces) (htcard : t.card = 3)
    (hst : s ⊆ t) (hscard : s.card = 2)
    (htrace : (boundaryComplex 2 A).space ∩ convexHull ℝ (t : Set E) =
      ⋃ v ∈ s, convexHull ℝ ((t.erase v : Finset E) : Set E))
    (hinter : ∀ u ∈ A.faces, u.card = 3 → ¬s ⊆ u →
      (u ∩ t).card ≤ 1 ∧ (s.card = 2 → u ∩ t ⊆ s))
    (C : Finset E → Set E) :
    (⋃ r ∈ t.powerset.filter (fun r => r ∈ (eraseTriangleComplex A t).faces), C r) =
      C s ∪ ⋃ v ∈ s, C {v} := by
  classical
  let q := t \ s
  have hqcard : q.card = 1 := by
    dsimp [q]
    rw [Finset.card_sdiff_of_subset hst, htcard, hscard]
  have hqne : q.Nonempty := Finset.card_pos.mp (by omega)
  have hsA : s ∈ A.faces := A.down_closed ht hst (Finset.card_pos.mp (by omega))
  have hfree (r : Finset E) : r ∈ (eraseTriangleComplex A t).faces ↔
      r ∈ A.faces ∧ ¬q ⊆ r :=
    mem_eraseTriangleComplex_iff_of_free_triangle A hA ht htcard hst
      (Or.inr hscard) htrace hinter
  have hqns : ¬q ⊆ s := by
    intro hqs
    obtain ⟨v, hv⟩ := hqne
    exact (Finset.mem_sdiff.mp hv).2 (hqs hv)
  apply Subset.antisymm
  · intro x hx
    obtain ⟨r, hr, hxr⟩ := mem_iUnion₂.mp hx
    have hrpow := (Finset.mem_filter.mp hr).1
    have hrErase := (Finset.mem_filter.mp hr).2
    have hrA := eraseTriangleComplex_faces_subset A t hrErase
    have hrnot : ¬q ⊆ r := ((hfree r).mp hrErase).2
    have hrs : r ⊆ s := by
      intro v hvr
      have hvt : v ∈ t := (Finset.mem_powerset.mp hrpow) hvr
      by_contra hvs
      have hvq : v ∈ q := Finset.mem_sdiff.mpr ⟨hvt, hvs⟩
      apply hrnot
      intro w hw
      have hwv : w = v := Finset.card_le_one.mp (by omega : q.card ≤ 1) w hw v hvq
      exact hwv ▸ hvr
    have hrpos := A.nonempty_of_mem_faces hrA
    have hrcard : r.card = 1 ∨ r.card = 2 := by
      have hpos : 0 < r.card := Finset.card_pos.mpr hrpos
      have hle := Finset.card_le_card hrs
      rw [hscard] at hle
      omega
    rcases hrcard with hrcard | hrcard
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hrcard
      exact Or.inr (mem_iUnion₂.mpr
        ⟨v, Finset.singleton_subset_iff.mp hrs, hxr⟩)
    · have hrsEq : r = s := Finset.eq_of_subset_of_card_le hrs (by omega)
      exact Or.inl (hrsEq ▸ hxr)
  · rintro x (hxs | hxv)
    · refine mem_iUnion₂.mpr ⟨s, Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr hst, (hfree s).mpr ⟨hsA, hqns⟩⟩, hxs⟩
    · obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hxv
      have hvA : {v} ∈ A.faces := A.down_closed hsA
        (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
      have hqn : ¬q ⊆ {v} := by
        intro hqv
        obtain ⟨w, hw⟩ := hqne
        have hwv : w = v := Finset.mem_singleton.mp (hqv hw)
        exact (Finset.mem_sdiff.mp hw).2 (hwv ▸ hv)
      exact mem_iUnion₂.mpr ⟨{v}, Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr ((Finset.singleton_subset_iff.mpr hv).trans hst),
          (hfree {v}).mpr ⟨hvA, hqn⟩⟩, hxv⟩

open Classical in
private theorem isPLBall_derivedNeighborhoodCell_inter_erase_of_s_card_two
    {K A : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite A.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hA : IsPLBall 2 A.space)
    (hAK : A.faces ⊆ (boundaryComplex 3 K).faces)
    {t s : Finset E} (ht : t ∈ A.faces) (htcard : t.card = 3)
    (hst : s ⊆ t) (hscard : s.card = 2)
    (htrace : (boundaryComplex 2 A).space ∩ convexHull ℝ (t : Set E) =
      ⋃ v ∈ s, convexHull ℝ ((t.erase v : Finset E) : Set E))
    (hinter : ∀ u ∈ A.faces, u.card = 3 → ¬s ⊆ u →
      (u ∩ t).card ≤ 1 ∧ (s.card = 2 → u ∩ t ⊆ s)) :
    IsPLBall 2 ((derivedNeighborhoodCell K t).space ∩
      (derivedNeighborhood K (eraseTriangleComplex A t)).space) := by
  classical
  let A' := eraseTriangleComplex A t
  have hA'K : A'.faces ⊆ K.faces :=
    (eraseTriangleComplex_faces_subset A t).trans (hAK.trans (boundaryComplex_faces_subset 3 K))
  have htK := boundaryComplex_faces_subset 3 K (hAK ht)
  have htA' : t ∉ A'.faces := by
    intro ht'
    exact ((mem_eraseTriangleComplex_triangle_iff A t
      (fun u hu => card_le_of_isPLBall A hA hu) htcard).mp ht').2 rfl
  have heq := derivedNeighborhoodCell_inter_derivedNeighborhood_eq_subfaces K A' hA'K htK htA'
  have hunion := iUnion_eraseTriangleComplex_subfaces_eq_edge A hA ht htcard hst hscard
    htrace hinter (fun r => (derivedNeighborhoodCell K r).space)
  rw [heq, hunion]
  exact isPLBall_derivedNeighborhoodCell_inter_edge hK (hAK ht)
    (boundaryComplex_faces_subset 3 K (hAK (A.down_closed ht hst
      (Finset.card_pos.mp (by omega))))) htcard hscard hst

open Classical in
private theorem iUnion_eraseTriangleComplex_subfaces_eq_vertex
    (A : Geometry.SimplicialComplex ℝ E) [Finite A.faces] (hA : IsPLBall 2 A.space)
    {t s : Finset E} (ht : t ∈ A.faces) (htcard : t.card = 3)
    (hst : s ⊆ t) (hscard : s.card = 1)
    (htrace : (boundaryComplex 2 A).space ∩ convexHull ℝ (t : Set E) =
      ⋃ v ∈ s, convexHull ℝ ((t.erase v : Finset E) : Set E))
    (hinter : ∀ u ∈ A.faces, u.card = 3 → ¬s ⊆ u →
      (u ∩ t).card ≤ 1 ∧ (s.card = 2 → u ∩ t ⊆ s))
    (C : Finset E → Set E) :
    let q := t \ s
    let edges := t.powersetCard 2 |>.filter (fun e => s ⊆ e)
    (⋃ r ∈ t.powerset.filter (fun r => r ∈ (eraseTriangleComplex A t).faces), C r) =
      (C s ∪ ⋃ e ∈ edges, C e) ∪ ⋃ v ∈ q, C {v} := by
  classical
  dsimp only
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hscard
  let q := t \ {a}
  let edges := t.powersetCard 2 |>.filter (fun e => ({a} : Finset E) ⊆ e)
  have hqcard : q.card = 2 := by
    dsimp [q]
    rw [Finset.card_sdiff_of_subset hst, htcard, hscard]
  have hsne : ({a} : Finset E).Nonempty := Finset.singleton_nonempty a
  have hsA : ({a} : Finset E) ∈ A.faces := A.down_closed ht hst hsne
  have hfree (r : Finset E) : r ∈ (eraseTriangleComplex A t).faces ↔
      r ∈ A.faces ∧ ¬q ⊆ r :=
    by simpa only [q] using
      (mem_eraseTriangleComplex_iff_of_free_triangle A hA ht htcard hst
        (Or.inl hscard) htrace hinter :
        r ∈ (eraseTriangleComplex A t).faces ↔ r ∈ A.faces ∧ ¬t \ {a} ⊆ r)
  have hqns : ¬q ⊆ ({a} : Finset E) := by
    intro hqs
    have hc := Finset.card_le_card hqs
    omega
  apply Subset.antisymm
  · intro x hx
    obtain ⟨r, hr, hxr⟩ := mem_iUnion₂.mp hx
    have hrpow := (Finset.mem_filter.mp hr).1
    have hrErase := (Finset.mem_filter.mp hr).2
    have hrA := eraseTriangleComplex_faces_subset A t hrErase
    have hrnot : ¬q ⊆ r := ((hfree r).mp hrErase).2
    have hrpos : 0 < r.card := Finset.card_pos.mpr (A.nonempty_of_mem_faces hrA)
    have hrle := Finset.card_le_card (Finset.mem_powerset.mp hrpow)
    rw [htcard] at hrle
    have hrcard : r.card = 1 ∨ r.card = 2 := by
      by_cases hrc : r.card = 3
      · have hrt : r = t := Finset.eq_of_subset_of_card_le (Finset.mem_powerset.mp hrpow)
          (by omega)
        exact (hrnot (hrt ▸ Finset.sdiff_subset)) |>.elim
      · omega
    rcases hrcard with hrcard | hrcard
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hrcard
      have hvt : v ∈ t := Finset.singleton_subset_iff.mp (Finset.mem_powerset.mp hrpow)
      by_cases hvs : v ∈ ({a} : Finset E)
      · have hva : v = a := Finset.mem_singleton.mp hvs
        subst v
        exact Or.inl (Or.inl hxr)
      · exact Or.inr (mem_iUnion₂.mpr
          ⟨v, Finset.mem_sdiff.mpr ⟨hvt, hvs⟩, hxr⟩)
    · have hrs : ({a} : Finset E) ⊆ r := by
        apply Finset.singleton_subset_iff.mpr
        by_contra har
        have hrq : r ⊆ q := by
          intro w hwr
          exact Finset.mem_sdiff.mpr ⟨(Finset.mem_powerset.mp hrpow) hwr,
            fun hwa => har (Finset.mem_singleton.mp hwa ▸ hwr)⟩
        have heq : r = q := Finset.eq_of_subset_of_card_le hrq (by omega)
        exact hrnot (heq ▸ Finset.Subset.rfl)
      exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨r, Finset.mem_filter.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨Finset.mem_powerset.mp hrpow, hrcard⟩, hrs⟩, hxr⟩))
  · rintro x ((hxs | hxe) | hxv)
    · exact mem_iUnion₂.mpr ⟨{a}, Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr hst, (hfree {a}).mpr ⟨hsA, hqns⟩⟩, hxs⟩
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hxe
      have hep := (Finset.mem_filter.mp he).1
      have hse := (Finset.mem_filter.mp he).2
      have het := (Finset.mem_powersetCard.mp hep).1
      have hecard := (Finset.mem_powersetCard.mp hep).2
      have heA := A.down_closed ht het (Finset.card_pos.mp (by omega))
      have hqne : ¬q ⊆ e := by
        intro hqe
        have heq : q = e := Finset.eq_of_subset_of_card_le hqe (by omega)
        obtain ⟨v, hv⟩ := hsne
        exact (Finset.mem_sdiff.mp (heq ▸ hse hv)).2 hv
      exact mem_iUnion₂.mpr ⟨e, Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr het, (hfree e).mpr ⟨heA, hqne⟩⟩, hxe⟩
    · obtain ⟨v, hvq, hxv⟩ := mem_iUnion₂.mp hxv
      have hvt := (Finset.mem_sdiff.mp hvq).1
      have hvA : {v} ∈ A.faces := A.down_closed ht
        (Finset.singleton_subset_iff.mpr hvt) (Finset.singleton_nonempty v)
      have hqn : ¬q ⊆ {v} := by
        intro hqv
        have hc := Finset.card_le_card hqv
        simp only [Finset.card_singleton, hqcard] at hc
        omega
      exact mem_iUnion₂.mpr ⟨{v}, Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hvt),
          (hfree {v}).mpr ⟨hvA, hqn⟩⟩, hxv⟩

open Classical in
private theorem isPLBall_derivedNeighborhoodCell_inter_vertex
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    {t s : Finset E} (ht : t ∈ (boundaryComplex 3 K).faces)
    (htcard : t.card = 3) (hscard : s.card = 1) (hst : s ⊆ t) :
    let q := t \ s
    let edges := t.powersetCard 2 |>.filter (fun e => s ⊆ e)
    IsPLBall 2 ((derivedNeighborhoodCell K t).space ∩
      (((derivedNeighborhoodCell K s).space ∪
        ⋃ e ∈ edges, (derivedNeighborhoodCell K e).space) ∪
          ⋃ v ∈ q, (derivedNeighborhoodCell K {v}).space)) := by
  classical
  dsimp only
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hscard
  let q := t \ {a}
  let edges := t.powersetCard 2 |>.filter (fun e => ({a} : Finset E) ⊆ e)
  let C := fun r : Finset E => (derivedNeighborhoodCell K r).space
  let B := (derivedNeighborhoodCellBase K t).space
  let D := C t ∩ (C {a} ∪ ⋃ e ∈ edges, C e)
  let A := fun v : E => C t ∩ C {v}
  have htK := boundaryComplex_faces_subset 3 K ht
  have hat : a ∈ t := Finset.singleton_subset_iff.mp hst
  have haK : {a} ∈ K.faces := K.down_closed htK hst (Finset.singleton_nonempty a)
  have htneA : t ≠ {a} := by
    intro heq
    have hc := congrArg Finset.card heq
    simp only [Finset.card_singleton, htcard] at hc
    omega
  have hbase : IsPLBall 2 B := hK.isPLBall_derivedNeighborhoodCellBase ht
  have hcenter : IsPLBall 2 (C t ∩ C {a}) :=
    hK.isPLBall_derivedNeighborhoodCell_inter htK haK htneA
      (Or.inr (Finset.singleton_subset_iff.mpr hat))
  have hcenterB : C t ∩ C {a} ⊆ B :=
    derivedNeighborhoodCell_inter_subset_base K htK haK htneA
  have hedge (e : Finset E) (he : e ∈ edges) : e ⊆ t ∧ e.card = 2 ∧ a ∈ e := by
    have hep := (Finset.mem_filter.mp he).1
    exact ⟨(Finset.mem_powersetCard.mp hep).1, (Finset.mem_powersetCard.mp hep).2,
      Finset.singleton_subset_iff.mp (Finset.mem_filter.mp he).2⟩
  have heK (e : Finset E) (he : e ∈ edges) : e ∈ K.faces :=
    K.down_closed htK (hedge e he).1 (Finset.card_pos.mp (by rw [(hedge e he).2.1]; decide))
  have hte (e : Finset E) (he : e ∈ edges) : t ≠ e := by
    intro heq
    have hc := congrArg Finset.card heq
    rw [htcard, (hedge e he).2.1] at hc
    omega
  let P := fun e : Finset E => C t ∩ C e
  have hP (e : Finset E) (he : e ∈ edges) : IsPLBall 2 (P e) :=
    hK.isPLBall_derivedNeighborhoodCell_inter htK (heK e he) (hte e he)
      (Or.inr (hedge e he).1)
  have hPB (e : Finset E) (he : e ∈ edges) : P e ⊆ B :=
    derivedNeighborhoodCell_inter_subset_base K htK (heK e he) (hte e he)
  have hPI (e : Finset E) (he : e ∈ edges) :
      IsPLBall 1 ((C t ∩ C {a}) ∩ P e) := by
    have heq : (C t ∩ C {a}) ∩ P e = C t ∩ C {a} ∩ C e := by
      ext x
      simp only [C, P, mem_inter_iff]
      tauto
    rw [heq]
    exact hK.isPLBall_derivedNeighborhoodCell_inter_inter htK haK (heK e he)
      htneA (hte e he) (by
        intro heq
        have hc := congrArg Finset.card heq
        simp only [Finset.card_singleton, (hedge e he).2.1] at hc
        omega)
      (Or.inr (Finset.singleton_subset_iff.mpr hat)) (Or.inr (hedge e he).1)
      (Or.inl (Finset.singleton_subset_iff.mpr (hedge e he).2.2))
  have hPdis (e : Finset E) (he : e ∈ edges) (f : Finset E) (hf : f ∈ edges)
      (hef : e ≠ f) : Disjoint (P e) (P f) :=
    (disjoint_derivedNeighborhoodCell_space K (heK e he) (heK f hf)
      (by intro h; exact hef (Finset.eq_of_subset_of_card_le h
        (by rw [(hedge e he).2.1, (hedge f hf).2.1])))
      (by intro h; exact hef (Finset.eq_of_subset_of_card_le h
        (by rw [(hedge f hf).2.1, (hedge e he).2.1])).symm)).mono
        inter_subset_right inter_subset_right
  have hD : IsPLBall 2 D := by
    have h := isPLBall_union_iUnion_of_pairwiseDisjoint_in_ball hbase hcenter hcenterB
      edges P hP hPB hPI hPdis
    simpa only [D, C, P, inter_union_distrib_left, inter_iUnion] using h
  have hDB : D ⊆ B := by
    rintro x ⟨hxt, hxa | hxe⟩
    · exact hcenterB ⟨hxt, hxa⟩
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hxe
      exact hPB e he ⟨hxt, hxe⟩
  have hqcard : q.card = 2 := by
    dsimp [q]
    rw [Finset.card_sdiff_of_subset hst, htcard, Finset.card_singleton]
  have hvK (v : E) (hv : v ∈ q) : {v} ∈ K.faces :=
    K.down_closed htK (Finset.singleton_subset_iff.mpr (Finset.mem_sdiff.mp hv).1)
      (Finset.singleton_nonempty v)
  have hvne (v : E) (hv : v ∈ q) : v ≠ a := by
    intro heq
    exact (Finset.mem_sdiff.mp hv).2 (heq ▸ Finset.mem_singleton_self a)
  have hA (v : E) (hv : v ∈ q) : IsPLBall 2 (A v) :=
    hK.isPLBall_derivedNeighborhoodCell_inter htK (hvK v hv)
      (by intro heq; have hc := congrArg Finset.card heq;
          simp only [Finset.card_singleton, htcard] at hc; omega)
      (Or.inr (Finset.singleton_subset_iff.mpr (Finset.mem_sdiff.mp hv).1))
  have hAB (v : E) (hv : v ∈ q) : A v ⊆ B :=
    derivedNeighborhoodCell_inter_subset_base K htK (hvK v hv)
      (by intro heq; have hc := congrArg Finset.card heq;
          simp only [Finset.card_singleton, htcard] at hc; omega)
  have hDI (v : E) (hv : v ∈ q) : IsPLBall 1 (D ∩ A v) := by
    let e : Finset E := {a, v}
    have hecard : e.card = 2 := Finset.card_pair (hvne v hv).symm
    have het : e ⊆ t := by
      intro w hw
      simp only [e, Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact hat
      · exact (Finset.mem_sdiff.mp hv).1
    have heEdges : e ∈ edges := Finset.mem_filter.mpr
      ⟨Finset.mem_powersetCard.mpr ⟨het, hecard⟩,
        Finset.singleton_subset_iff.mpr (Finset.mem_insert_self a {v})⟩
    have heK' := heK e heEdges
    have heq : D ∩ A v = C t ∩ C e ∩ C {v} := by
      apply Subset.antisymm
      · rintro x ⟨hxD, hxt, hxv⟩
        have hright : x ∈ C e := by
          rcases hxD.2 with hxa | hxe
          · have hdis := disjoint_derivedNeighborhoodCell_space K haK (hvK v hv)
                (by simpa only [Finset.singleton_subset_iff, Finset.mem_singleton] using (hvne v hv).symm)
                (by simpa only [Finset.singleton_subset_iff, Finset.mem_singleton] using hvne v hv)
            exact (hdis.le_bot ⟨hxa, hxv⟩).elim
          · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hxe
            rcases subset_or_subset_of_nonempty_derivedNeighborhoodCell_inter K
                (heK f hf) (hvK v hv) ⟨x, hxf, hxv⟩ with hfv | hvf
            · have hc := Finset.card_le_card hfv
              rw [(hedge f hf).2.1, Finset.card_singleton] at hc
              omega
            · have hvfmem : v ∈ f := Finset.singleton_subset_iff.mp hvf
              have hef : e = f := Finset.eq_of_subset_of_card_le (by
                intro w hw
                simp only [e, Finset.mem_insert, Finset.mem_singleton] at hw
                rcases hw with rfl | rfl
                · exact (hedge f hf).2.2
                · exact hvfmem) (by rw [hecard, (hedge f hf).2.1])
              exact hef ▸ hxf
        exact ⟨⟨hxt, hright⟩, hxv⟩
      · rintro x ⟨⟨hxt, hxe⟩, hxv⟩
        exact ⟨⟨hxt, Or.inr (mem_iUnion₂.mpr ⟨e, heEdges, hxe⟩)⟩, hxt, hxv⟩
    rw [heq]
    exact hK.isPLBall_derivedNeighborhoodCell_inter_inter htK heK' (hvK v hv)
      (by intro heq'; have hc := congrArg Finset.card heq'; rw [htcard, hecard] at hc; omega)
      (by intro heq'; have hc := congrArg Finset.card heq';
          simp only [Finset.card_singleton, htcard] at hc; omega)
      (by intro heq'; have hc := congrArg Finset.card heq';
          simp only [Finset.card_singleton, hecard] at hc; omega)
      (Or.inr het) (Or.inr (Finset.singleton_subset_iff.mpr (Finset.mem_sdiff.mp hv).1))
      (Or.inr (Finset.singleton_subset_iff.mpr (Finset.mem_insert_of_mem (Finset.mem_singleton_self v))))
  have hAdis (v : E) (hv : v ∈ q) (w : E) (hw : w ∈ q) (hvw : v ≠ w) :
      Disjoint (A v) (A w) :=
    (disjoint_derivedNeighborhoodCell_space K (hvK v hv) (hvK w hw)
      (by simpa only [Finset.singleton_subset_iff, Finset.mem_singleton] using hvw)
      (by simpa only [Finset.singleton_subset_iff, Finset.mem_singleton] using hvw.symm)).mono
        inter_subset_right inter_subset_right
  have hball := isPLBall_union_iUnion_of_pairwiseDisjoint_in_ball hbase hD hDB
    q A hA hAB hDI hAdis
  simpa only [D, C, A, inter_union_distrib_left, inter_iUnion, union_assoc] using hball

open Classical in
private theorem isPLBall_derivedNeighborhoodCell_inter_erase_of_s_card_one
    {K A : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite A.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hA : IsPLBall 2 A.space)
    (hAK : A.faces ⊆ (boundaryComplex 3 K).faces)
    {t s : Finset E} (ht : t ∈ A.faces) (htcard : t.card = 3)
    (hst : s ⊆ t) (hscard : s.card = 1)
    (htrace : (boundaryComplex 2 A).space ∩ convexHull ℝ (t : Set E) =
      ⋃ v ∈ s, convexHull ℝ ((t.erase v : Finset E) : Set E))
    (hinter : ∀ u ∈ A.faces, u.card = 3 → ¬s ⊆ u →
      (u ∩ t).card ≤ 1 ∧ (s.card = 2 → u ∩ t ⊆ s)) :
    IsPLBall 2 ((derivedNeighborhoodCell K t).space ∩
      (derivedNeighborhood K (eraseTriangleComplex A t)).space) := by
  classical
  let A' := eraseTriangleComplex A t
  have hA'K : A'.faces ⊆ K.faces :=
    (eraseTriangleComplex_faces_subset A t).trans (hAK.trans (boundaryComplex_faces_subset 3 K))
  have htK := boundaryComplex_faces_subset 3 K (hAK ht)
  have htA' : t ∉ A'.faces := by
    intro ht'
    exact ((mem_eraseTriangleComplex_triangle_iff A t
      (fun u hu => card_le_of_isPLBall A hA hu) htcard).mp ht').2 rfl
  have heq := derivedNeighborhoodCell_inter_derivedNeighborhood_eq_subfaces K A' hA'K htK htA'
  have hunion := iUnion_eraseTriangleComplex_subfaces_eq_vertex A hA ht htcard hst hscard
    htrace hinter (fun r => (derivedNeighborhoodCell K r).space)
  rw [heq, hunion]
  exact isPLBall_derivedNeighborhoodCell_inter_vertex hK (hAK ht) htcard hscard hst

open Classical in
private theorem iUnion_eraseTriangleComplex_subfaces_free_edge
    (A : Geometry.SimplicialComplex ℝ E) [Finite A.faces] (hA : IsPLBall 2 A.space)
    {t s : Finset E} (ht : t ∈ A.faces) (htcard : t.card = 3)
    (hst : s ⊆ t) (hscard : s.card = 1)
    (htrace : (boundaryComplex 2 A).space ∩ convexHull ℝ (t : Set E) =
      ⋃ v ∈ s, convexHull ℝ ((t.erase v : Finset E) : Set E))
    (hinter : ∀ u ∈ A.faces, u.card = 3 → ¬s ⊆ u →
      (u ∩ t).card ≤ 1 ∧ (s.card = 2 → u ∩ t ⊆ s))
    (C : Finset E → Set E) :
    let q := t \ s
    (⋃ r ∈ q.powerset.filter (fun r => r ∈ (eraseTriangleComplex A t).faces), C r) =
      ⋃ v ∈ q, C {v} := by
  classical
  dsimp only
  let q := t \ s
  have hqcard : q.card = 2 := by
    dsimp [q]
    rw [Finset.card_sdiff_of_subset hst, htcard, hscard]
  have hfree (r : Finset E) : r ∈ (eraseTriangleComplex A t).faces ↔
      r ∈ A.faces ∧ ¬q ⊆ r :=
    mem_eraseTriangleComplex_iff_of_free_triangle A hA ht htcard hst
      (Or.inl hscard) htrace hinter
  apply Subset.antisymm
  · intro x hx
    obtain ⟨r, hr, hxr⟩ := mem_iUnion₂.mp hx
    have hrq := Finset.mem_powerset.mp (Finset.mem_filter.mp hr).1
    have hrErase := (Finset.mem_filter.mp hr).2
    have hrA := eraseTriangleComplex_faces_subset A t hrErase
    have hrnot := ((hfree r).mp hrErase).2
    have hrpos : 0 < r.card := Finset.card_pos.mpr (A.nonempty_of_mem_faces hrA)
    have hrle := Finset.card_le_card hrq
    rw [hqcard] at hrle
    have hrcard : r.card = 1 := by
      by_contra hne
      have hrcard : r.card = 2 := by omega
      have heq : r = q := Finset.eq_of_subset_of_card_le hrq (by omega)
      exact hrnot (heq ▸ Finset.Subset.rfl)
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hrcard
    exact mem_iUnion₂.mpr ⟨v, Finset.singleton_subset_iff.mp hrq, hxr⟩
  · intro x hx
    obtain ⟨v, hvq, hxv⟩ := mem_iUnion₂.mp hx
    have hvt := (Finset.mem_sdiff.mp hvq).1
    have hvA : {v} ∈ A.faces := A.down_closed ht
      (Finset.singleton_subset_iff.mpr hvt) (Finset.singleton_nonempty v)
    have hqn : ¬q ⊆ {v} := by
      intro hqv
      have hc := Finset.card_le_card hqv
      simp only [Finset.card_singleton, hqcard] at hc
      omega
    exact mem_iUnion₂.mpr ⟨{v}, Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hvq),
        (hfree {v}).mpr ⟨hvA, hqn⟩⟩, hxv⟩

open Classical in
private theorem IsCombinatorialManifoldWithBoundary.isPLBall_derivedNeighborhood_of_free_triangle_one
    {K A : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite A.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hA : IsPLBall 2 A.space)
    (hAK : A.faces ⊆ (boundaryComplex 3 K).faces)
    {t s : Finset E} (ht : t ∈ A.faces) (htcard : t.card = 3)
    (hst : s ⊆ t) (hscard : s.card = 1)
    (htrace : (boundaryComplex 2 A).space ∩ convexHull ℝ (t : Set E) =
      ⋃ v ∈ s, convexHull ℝ ((t.erase v : Finset E) : Set E))
    (hinter : ∀ u ∈ A.faces, u.card = 3 → ¬s ⊆ u →
      (u ∩ t).card ≤ 1 ∧ (s.card = 2 → u ∩ t ⊆ s))
    (hprev : IsPLBall 3 (PiecewiseLinear.derivedNeighborhood K
      (eraseTriangleComplex A t)).space) :
    IsPLBall 3 (PiecewiseLinear.derivedNeighborhood K A).space := by
  classical
  let A' := eraseTriangleComplex A t
  let q := t \ s
  let C := fun r : Finset E => (derivedNeighborhoodCell K r).space
  let N := (PiecewiseLinear.derivedNeighborhood K A').space
  have hAKK : A.faces ⊆ K.faces := hAK.trans (boundaryComplex_faces_subset 3 K)
  have hA'K : A'.faces ⊆ K.faces := (eraseTriangleComplex_faces_subset A t).trans hAKK
  have htB := hAK ht
  have htK := boundaryComplex_faces_subset 3 K htB
  have htball : IsPLBall 3 (C t) := hK.isPLBall_derivedNeighborhoodCell htK
  have hD : IsPLBall 2 (C t ∩ N) :=
    isPLBall_derivedNeighborhoodCell_inter_erase_of_s_card_one hK hA hAK ht htcard
      hst hscard htrace hinter
  have hmeet₁ : N ∩ C t = C t ∩ N := inter_comm _ _
  have hI₁ : IsPLBall 2 (N ∩ C t) := hmeet₁ ▸ hD
  have hNK : N ⊆ K.space := derivedNeighborhood_space_subset K A'
  have htspaceK : C t ⊆ K.space := derivedNeighborhoodCell_space_subset K t
  have hfirst : IsPLBall 3 (N ∪ C t) :=
    hK.isPLBall_union_of_inter_isPLBall_two hprev htball hNK htspaceK hI₁
  have hqcard : q.card = 2 := by
    dsimp [q]
    rw [Finset.card_sdiff_of_subset hst, htcard, hscard]
  have hqne : q.Nonempty := Finset.card_pos.mp (by omega)
  have hqA : q ∈ A.faces := A.down_closed ht Finset.sdiff_subset hqne
  have hqB := hAK hqA
  have hqK := boundaryComplex_faces_subset 3 K hqB
  have hqball : IsPLBall 3 (C q) := hK.isPLBall_derivedNeighborhoodCell hqK
  have hfree (r : Finset E) : r ∈ A'.faces ↔ r ∈ A.faces ∧ ¬q ⊆ r :=
    mem_eraseTriangleComplex_iff_of_free_triangle A hA ht htcard hst
      (Or.inl hscard) htrace hinter
  have hqA' : q ∉ A'.faces := fun h => ((hfree q).mp h).2 Finset.Subset.rfl
  have hqold := derivedNeighborhoodCell_inter_derivedNeighborhood_eq_subfaces K A'
    hA'K hqK hqA'
  have hqsub := iUnion_eraseTriangleComplex_subfaces_free_edge A hA ht htcard hst hscard
    htrace hinter C
  rw [hqsub] at hqold
  have hmeet₂ : (N ∪ C t) ∩ C q = C q ∩ (C t ∪ ⋃ v ∈ q, C {v}) := by
    apply Subset.antisymm
    · rintro x ⟨hxN | hxt, hxq⟩
      · have hx : x ∈ C q ∩ N := ⟨hxq, hxN⟩
        rw [hqold] at hx
        exact ⟨hxq, Or.inr hx.2⟩
      · exact ⟨hxq, Or.inl hxt⟩
    · rintro x ⟨hxq, hxt | hxv⟩
      · exact ⟨Or.inr hxt, hxq⟩
      · have hxold : x ∈ C q ∩ N := by
          rw [hqold]
          exact ⟨hxq, hxv⟩
        exact ⟨Or.inl hxold.2, hxq⟩
  let d := q.image (fun v => ({v} : Finset E))
  have hdspace : (⋃ u ∈ d, C u) = ⋃ v ∈ q, C {v} := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
      exact mem_iUnion₂.mpr ⟨v, hv, hxu⟩
    · intro x hx
      obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion₂.mpr ⟨{v}, Finset.mem_image.mpr ⟨v, hv, rfl⟩, hxv⟩
  have hqt : q ≠ t := by
    intro heq
    have hc := congrArg Finset.card heq
    rw [hqcard, htcard] at hc
    omega
  have hd (u : Finset E) (hu : u ∈ d) : u ∈ K.faces := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    exact K.down_closed hqK (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  have hdne (u : Finset E) (hu : u ∈ d) : u ≠ q ∧ u ≠ t := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    constructor <;> intro heq <;> have hc := congrArg Finset.card heq
    · simp only [Finset.card_singleton, hqcard] at hc
      omega
    · simp only [Finset.card_singleton, htcard] at hc
      omega
  have hdcomp (u : Finset E) (hu : u ∈ d) :
      (q ⊆ u ∨ u ⊆ q) ∧ (t ⊆ u ∨ u ⊆ t) := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    exact ⟨Or.inr (Finset.singleton_subset_iff.mpr hv),
      Or.inr (Finset.singleton_subset_iff.mpr (Finset.sdiff_subset hv))⟩
  have hdincomp (u : Finset E) (hu : u ∈ d) (v : Finset E) (hv : v ∈ d)
      (huv : u ≠ v) : ¬u ⊆ v ∧ ¬v ⊆ u := by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
    simp only [Finset.singleton_subset_iff, Finset.mem_singleton]
    exact ⟨fun h => huv (h ▸ rfl), fun h => huv (h.symm ▸ rfl)⟩
  have hattach₀ := hK.isPLBall_derivedNeighborhoodCell_inter_union hqB htK hqt
    (Or.inl Finset.sdiff_subset) d hd hdne hdcomp hdincomp
  rw [hdspace] at hattach₀
  have hI₂ : IsPLBall 2 ((N ∪ C t) ∩ C q) := hmeet₂ ▸ hattach₀
  have hfirstK : N ∪ C t ⊆ K.space := union_subset hNK htspaceK
  have hqspaceK : C q ⊆ K.space := derivedNeighborhoodCell_space_subset K q
  have hfinal : IsPLBall 3 ((N ∪ C t) ∪ C q) :=
    hK.isPLBall_union_of_inter_isPLBall_two hfirst hqball hfirstK hqspaceK hI₂
  have hspace : (PiecewiseLinear.derivedNeighborhood K A).space = (N ∪ C t) ∪ C q := by
    dsimp only [N]
    rw [← iUnion_derivedNeighborhoodCell_space K A hAKK,
      ← iUnion_derivedNeighborhoodCell_space K A' hA'K]
    apply Subset.antisymm
    · intro x hx
      obtain ⟨r, hrA, hxr⟩ := mem_iUnion₂.mp hx
      by_cases hqr : q ⊆ r
      · have hrt := face_subset_of_sdiff_subset_free_triangle A hA htcard hst
          (Or.inl hscard) hinter hrA hqr
        have hqle := Finset.card_le_card hqr
        have hrtle := Finset.card_le_card hrt
        rw [hqcard] at hqle
        rw [htcard] at hrtle
        have hrcard : r.card = 2 ∨ r.card = 3 := by omega
        rcases hrcard with hrcard | hrcard
        · have heq : r = q := (Finset.eq_of_subset_of_card_le hqr (by omega)).symm
          exact Or.inr (heq ▸ hxr)
        · have heq : r = t := Finset.eq_of_subset_of_card_le hrt (by omega)
          exact Or.inl (Or.inr (heq ▸ hxr))
      · exact Or.inl (Or.inl (mem_iUnion₂.mpr ⟨r, (hfree r).mpr ⟨hrA, hqr⟩, hxr⟩))
    · rintro x ((hxN | hxt) | hxq)
      · obtain ⟨r, hr, hxr⟩ := mem_iUnion₂.mp hxN
        exact mem_iUnion₂.mpr ⟨r, eraseTriangleComplex_faces_subset A t hr, hxr⟩
      · exact mem_iUnion₂.mpr ⟨t, ht, hxt⟩
      · exact mem_iUnion₂.mpr ⟨q, hqA, hxq⟩
  exact hspace.symm ▸ hfinal

open Classical in
private theorem IsCombinatorialManifoldWithBoundary.isPLBall_derivedNeighborhood_of_free_triangle_two
    {K A : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite A.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hA : IsPLBall 2 A.space)
    (hAK : A.faces ⊆ (boundaryComplex 3 K).faces)
    {t s : Finset E} (ht : t ∈ A.faces) (htcard : t.card = 3)
    (hst : s ⊆ t) (hscard : s.card = 2)
    (htrace : (boundaryComplex 2 A).space ∩ convexHull ℝ (t : Set E) =
      ⋃ v ∈ s, convexHull ℝ ((t.erase v : Finset E) : Set E))
    (hinter : ∀ u ∈ A.faces, u.card = 3 → ¬s ⊆ u →
      (u ∩ t).card ≤ 1 ∧ (s.card = 2 → u ∩ t ⊆ s))
    (hprev : IsPLBall 3 (PiecewiseLinear.derivedNeighborhood K
      (eraseTriangleComplex A t)).space) :
    IsPLBall 3 (PiecewiseLinear.derivedNeighborhood K A).space := by
  classical
  have hqcard : (t \ s).card = 1 := by
    rw [Finset.card_sdiff_of_subset hst, htcard, hscard]
  obtain ⟨a, hqa⟩ := Finset.card_eq_one.mp hqcard
  have ha : a ∈ t ∧ a ∉ s := Finset.mem_sdiff.mp (hqa.symm ▸ Finset.mem_singleton_self a)
  let A' := eraseTriangleComplex A t
  let C := fun r : Finset E => (derivedNeighborhoodCell K r).space
  let N := (PiecewiseLinear.derivedNeighborhood K A').space
  let e := fun v : E => ({a, v} : Finset E)
  have hAKK : A.faces ⊆ K.faces := hAK.trans (boundaryComplex_faces_subset 3 K)
  have hA'K : A'.faces ⊆ K.faces := (eraseTriangleComplex_faces_subset A t).trans hAKK
  have hN : N = ⋃ r ∈ A'.faces, C r := (iUnion_derivedNeighborhoodCell_space K A' hA'K).symm
  have hfree (r : Finset E) : r ∈ A'.faces ↔ r ∈ A.faces ∧ a ∉ r := by
    simpa only [hqa, Finset.singleton_subset_iff] using
      (mem_eraseTriangleComplex_iff_of_free_triangle A hA ht htcard hst
        (Or.inr hscard) htrace hinter :
        r ∈ A'.faces ↔ r ∈ A.faces ∧ ¬t \ s ⊆ r)
  have htK := hAKK ht
  have htB := hAK ht
  have htball : IsPLBall 3 (C t) := hK.isPLBall_derivedNeighborhoodCell htK
  have hD : IsPLBall 2 (C t ∩ N) :=
    isPLBall_derivedNeighborhoodCell_inter_erase_of_s_card_two hK hA hAK ht htcard
      hst hscard htrace hinter
  have hNK : N ⊆ K.space := derivedNeighborhood_space_subset K A'
  have htspaceK : C t ⊆ K.space := derivedNeighborhoodCell_space_subset K t
  have hfirst : IsPLBall 3 (N ∪ C t) :=
    hK.isPLBall_union_of_inter_isPLBall_two hprev htball hNK htspaceK
      ((inter_comm _ _).symm ▸ hD)
  have hav (v : E) (hv : v ∈ s) : a ≠ v := fun h => ha.2 (h.symm ▸ hv)
  have hecard (v : E) (hv : v ∈ s) : (e v).card = 2 := Finset.card_pair (hav v hv)
  have het (v : E) (hv : v ∈ s) : e v ⊆ t := by
    intro w hw
    simp only [e, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact ha.1
    · exact hst hv
  have heA (v : E) (hv : v ∈ s) : e v ∈ A.faces :=
    A.down_closed ht (het v hv) (Finset.insert_nonempty _ _)
  have hvA (v : E) (hv : v ∈ s) : {v} ∈ A.faces :=
    A.down_closed ht (Finset.singleton_subset_iff.mpr (hst hv)) (Finset.singleton_nonempty v)
  have heK (v : E) (hv : v ∈ s) : e v ∈ K.faces := hAKK (heA v hv)
  have heB (v : E) (hv : v ∈ s) : e v ∈ (boundaryComplex 3 K).faces := hAK (heA v hv)
  have hetne (v : E) (hv : v ∈ s) : e v ≠ t := by
    intro h
    have hc := congrArg Finset.card h
    rw [hecard v hv, htcard] at hc
    omega
  have hold (v : E) (hv : v ∈ s) : C (e v) ∩ N = C (e v) ∩ C {v} := by
    apply Subset.antisymm
    · rintro x ⟨hxe, hxN⟩
      rw [hN] at hxN
      obtain ⟨r, hr, hxr⟩ := mem_iUnion₂.mp hxN
      have hra := ((hfree r).mp hr).2
      rcases subset_or_subset_of_nonempty_derivedNeighborhoodCell_inter K
          (heK v hv) (hA'K hr) ⟨x, hxe, hxr⟩ with her | hre
      · exact (hra (her (Finset.mem_insert_self a {v}))).elim
      · have hrv : r = {v} := by
          apply Finset.eq_of_subset_of_card_le
          · intro w hw
            have hwe := hre hw
            simp only [e, Finset.mem_insert, Finset.mem_singleton] at hwe ⊢
            exact hwe.resolve_left (fun h => hra (h ▸ hw))
          · have := Finset.card_pos.mpr (A'.nonempty_of_mem_faces hr)
            simp only [Finset.card_singleton]
            omega
        exact ⟨hxe, hrv ▸ hxr⟩
    · rintro x ⟨hxe, hxv⟩
      refine ⟨hxe, ?_⟩
      rw [hN]
      exact mem_iUnion₂.mpr ⟨{v}, (hfree {v}).mpr ⟨hvA v hv, by
        simpa only [Finset.mem_singleton] using hav v hv⟩, hxv⟩
  have hattach (v : E) (hv : v ∈ s) : IsPLBall 2 ((N ∪ C t) ∩ C (e v)) := by
    have hgroup := hK.isPLBall_derivedNeighborhoodCell_inter_union (heB v hv) htK
      (hetne v hv) (Or.inl (het v hv)) {{v}}
      (by intro u hu; simp only [Finset.mem_singleton] at hu; subst u; exact hAKK (hvA v hv))
      (by
        intro u hu
        simp only [Finset.mem_singleton] at hu
        subst u
        constructor <;> intro h <;> have hc := congrArg Finset.card h
        · simp only [Finset.card_singleton, hecard v hv] at hc
          omega
        · simp only [Finset.card_singleton, htcard] at hc
          omega)
      (by
        intro u hu
        simp only [Finset.mem_singleton] at hu
        subst u
        exact ⟨Or.inr (Finset.singleton_subset_iff.mpr (Finset.mem_insert_of_mem
          (Finset.mem_singleton_self v))), Or.inr (Finset.singleton_subset_iff.mpr (hst hv))⟩)
      (by
        intro u hu w hw hne
        simp only [Finset.mem_singleton] at hu hw
        exact (hne (hu.trans hw.symm)).elim)
    have hmeet : (N ∪ C t) ∩ C (e v) = C (e v) ∩ (C t ∪ C {v}) := by
      rw [inter_comm, inter_union_distrib_left, hold v hv]
      simp only [inter_union_distrib_left, union_comm]
    rw [hmeet]
    simpa only [Finset.set_biUnion_singleton] using hgroup
  have hedis (v : E) (hv : v ∈ s) (w : E) (hw : w ∈ s) (hvw : v ≠ w) :
      Disjoint (C (e v)) (C (e w)) := by
    have hneq : e v ≠ e w := by
      intro heq
      have hvw' : v ∈ e w := heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self v)
      simp only [e, Finset.mem_insert, Finset.mem_singleton] at hvw'
      exact hvw (hvw'.resolve_left (hav v hv).symm)
    exact disjoint_derivedNeighborhoodCell_space K (heK v hv) (heK w hw)
      (fun h => hneq (Finset.eq_of_subset_of_card_le h (by rw [hecard v hv, hecard w hw])))
      (fun h => hneq (Finset.eq_of_subset_of_card_le h (by rw [hecard w hw, hecard v hv])).symm)
  let P := (N ∪ C t) ∪ ⋃ v ∈ s, C (e v)
  have hP : IsPLBall 3 P := hK.isPLBall_union_iUnion_of_pairwiseDisjoint hfirst
    (union_subset hNK htspaceK) s (fun v => C (e v))
    (fun v hv => hK.isPLBall_derivedNeighborhoodCell (heK v hv))
    (fun v _ => derivedNeighborhoodCell_space_subset K (e v)) hattach hedis
  have hPK : P ⊆ K.space := union_subset (union_subset hNK htspaceK)
    (iUnion₂_subset fun v _ => derivedNeighborhoodCell_space_subset K (e v))
  have haA : {a} ∈ A.faces := A.down_closed ht (Finset.singleton_subset_iff.mpr ha.1)
    (Finset.singleton_nonempty a)
  have haK := hAKK haA
  have haB := hAK haA
  have haN : Disjoint (C {a}) N := by
    rw [Set.disjoint_left]
    intro x hxa hxN
    rw [hN] at hxN
    obtain ⟨r, hr, hxr⟩ := mem_iUnion₂.mp hxN
    have hra := ((hfree r).mp hr).2
    rcases subset_or_subset_of_nonempty_derivedNeighborhoodCell_inter K haK (hA'K hr)
        ⟨x, hxa, hxr⟩ with har | hra'
    · exact hra (Finset.singleton_subset_iff.mp har)
    · obtain ⟨v, hv⟩ := A'.nonempty_of_mem_faces hr
      exact hra (Finset.mem_singleton.mp (hra' hv) ▸ hv)
  let d := s.image e
  have hdspace : (⋃ u ∈ d, C u) = ⋃ v ∈ s, C (e v) := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
      exact mem_iUnion₂.mpr ⟨v, hv, hxu⟩
    · intro x hx
      obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion₂.mpr ⟨e v, Finset.mem_image.mpr ⟨v, hv, rfl⟩, hxv⟩
  have hatne : ({a} : Finset E) ≠ t := by
    intro h
    have hc := congrArg Finset.card h
    simp only [Finset.card_singleton, htcard] at hc
    omega
  have hgroup := hK.isPLBall_derivedNeighborhoodCell_inter_union haB htK hatne
    (Or.inl (Finset.singleton_subset_iff.mpr ha.1)) d
    (by intro u hu; obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu; exact heK v hv)
    (by
      intro u hu
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
      refine ⟨?_, hetne v hv⟩
      intro h
      have hc := congrArg Finset.card h
      simp only [Finset.card_singleton, hecard v hv] at hc
      omega)
    (by
      intro u hu
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
      exact ⟨Or.inl (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self a {v})),
        Or.inr (het v hv)⟩)
    (by
      intro u hu w hw huw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
      exact ⟨fun h => huw (Finset.eq_of_subset_of_card_le h (by rw [hecard v hv, hecard z hz])),
        fun h => huw (Finset.eq_of_subset_of_card_le h (by rw [hecard z hz, hecard v hv])).symm⟩)
  rw [hdspace] at hgroup
  have hmeet : P ∩ C {a} = C {a} ∩ (C t ∪ ⋃ v ∈ s, C (e v)) := by
    ext x
    simp only [P, mem_inter_iff, mem_union]
    constructor
    · rintro ⟨(hxN | hxt) | hxe, hxa⟩
      · exact (haN.le_bot ⟨hxa, hxN⟩).elim
      · exact ⟨hxa, Or.inl hxt⟩
      · exact ⟨hxa, Or.inr hxe⟩
    · rintro ⟨hxa, hxt | hxe⟩
      · exact ⟨Or.inl (Or.inr hxt), hxa⟩
      · exact ⟨Or.inr hxe, hxa⟩
  have hfinal : IsPLBall 3 (P ∪ C {a}) := hK.isPLBall_union_of_inter_isPLBall_two hP
    (hK.isPLBall_derivedNeighborhoodCell haK) hPK (derivedNeighborhoodCell_space_subset K {a})
    (hmeet.symm ▸ hgroup)
  have hspace : (PiecewiseLinear.derivedNeighborhood K A).space = P ∪ C {a} := by
    rw [← iUnion_derivedNeighborhoodCell_space K A hAKK]
    apply Subset.antisymm
    · intro x hx
      obtain ⟨r, hr, hxr⟩ := mem_iUnion₂.mp hx
      by_cases har : a ∈ r
      · have hqr : t \ s ⊆ r := hqa ▸ Finset.singleton_subset_iff.mpr har
        have hrt := face_subset_of_sdiff_subset_free_triangle A hA htcard hst
          (Or.inr hscard) hinter hr hqr
        have hpos := Finset.card_pos.mpr (A.nonempty_of_mem_faces hr)
        have hle := Finset.card_le_card hrt
        rw [htcard] at hle
        have hrcard : r.card = 1 ∨ r.card = 2 ∨ r.card = 3 := by omega
        rcases hrcard with hrcard | hrcard | hrcard
        · have heq : r = {a} := (Finset.eq_of_subset_of_card_le
            (Finset.singleton_subset_iff.mpr har) (by simp only [Finset.card_singleton]; omega)).symm
          exact Or.inr (heq ▸ hxr)
        · obtain ⟨v, hva, hrv⟩ := Finset.exists_eq_insert_iff.mpr
            ⟨Finset.singleton_subset_iff.mpr har, by simp only [Finset.card_singleton]; omega⟩
          have hvR : v ∈ r := hrv ▸ Finset.mem_insert_self v {a}
          have hvS : v ∈ s := by
            by_contra hvs
            have hvq : v ∈ t \ s := Finset.mem_sdiff.mpr ⟨hrt hvR, hvs⟩
            rw [hqa] at hvq
            exact hva hvq
          have hre : r = e v := hrv.symm.trans (by ext w; simp [e, or_comm])
          exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨v, hvS, hre ▸ hxr⟩))
        · have heq : r = t := Finset.eq_of_subset_of_card_le hrt (by omega)
          exact Or.inl (Or.inl (Or.inr (heq ▸ hxr)))
      · have hxN : x ∈ N := by
          rw [hN]
          exact mem_iUnion₂.mpr ⟨r, (hfree r).mpr ⟨hr, har⟩, hxr⟩
        exact Or.inl (Or.inl (Or.inl hxN))
    · rintro x (((hxN | hxt) | hxe) | hxa)
      · rw [hN] at hxN
        obtain ⟨r, hr, hxr⟩ := mem_iUnion₂.mp hxN
        exact mem_iUnion₂.mpr ⟨r, eraseTriangleComplex_faces_subset A t hr, hxr⟩
      · exact mem_iUnion₂.mpr ⟨t, ht, hxt⟩
      · obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hxe
        exact mem_iUnion₂.mpr ⟨e v, heA v hv, hxv⟩
      · exact mem_iUnion₂.mpr ⟨{a}, haA, hxa⟩
  exact hspace.symm ▸ hfinal

open Classical in
theorem IsCombinatorialManifoldWithBoundary.isPLBall_derivedNeighborhood_of_free_triangle
    {K A : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite A.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hA : IsPLBall 2 A.space)
    (hAK : A.faces ⊆ (boundaryComplex 3 K).faces)
    {t s : Finset E} (ht : t ∈ A.faces) (htcard : t.card = 3)
    (hst : s ⊆ t) (hscard : s.card = 1 ∨ s.card = 2)
    (htrace : (boundaryComplex 2 A).space ∩ convexHull ℝ (t : Set E) =
      ⋃ v ∈ s, convexHull ℝ ((t.erase v : Finset E) : Set E))
    (hinter : ∀ u ∈ A.faces, u.card = 3 → ¬s ⊆ u →
      (u ∩ t).card ≤ 1 ∧ (s.card = 2 → u ∩ t ⊆ s))
    (hprev : IsPLBall 3 (PiecewiseLinear.derivedNeighborhood K
      (eraseTriangleComplex A t)).space) :
    IsPLBall 3 (PiecewiseLinear.derivedNeighborhood K A).space := by
  rcases hscard with hscard | hscard
  · exact hK.isPLBall_derivedNeighborhood_of_free_triangle_one hA hAK ht htcard hst
      hscard htrace hinter hprev
  · exact hK.isPLBall_derivedNeighborhood_of_free_triangle_two hA hAK ht htcard hst
      hscard htrace hinter hprev
end DifferentialGeometry.Topology.PiecewiseLinear
