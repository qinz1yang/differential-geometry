import DifferentialGeometry.Topology.SimplicialComplex.Realization.StandardRealizationCoordinates
import DifferentialGeometry.Topology.SimplicialComplex.Barycentric.Coordinates.BarycentricChain
import Mathlib.Order.Interval.Finset.Nat

namespace DifferentialGeometry.Topology.Engulfing

set_option linter.unusedSectionVars false

open Set _root_.Geometry _root_.Topology
open scoped BigOperators

noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def abstractBarycentric (P : PreAbstractSimplicialComplex ι) :
    PreAbstractSimplicialComplex (Finset ι) where
  faces := {C | C.Nonempty ∧ isFaceChain C ∧ ∀ s ∈ C, s ∈ P.faces}
  isRelLowerSet_faces := by
    intro C hC
    refine ⟨hC.1, fun D hDC hD => ⟨hD, hC.2.1.mono hDC, ?_⟩⟩
    exact fun s hs => hC.2.2 s (hDC hs)

omit [DecidableEq ι] [Fintype ι] in
theorem abstractBarycentric_mono [Finite ι] {P Q : PreAbstractSimplicialComplex ι} (hPQ : P ≤ Q) :
    abstractBarycentric P ≤ abstractBarycentric Q := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  intro C hC
  exact ⟨hC.1, hC.2.1, fun s hs => hPQ (hC.2.2 s hs)⟩

omit [DecidableEq ι] [Fintype ι] [Fintype κ] in
theorem abstractBarycentric_map [Finite ι] [Finite κ] (P : PreAbstractSimplicialComplex ι) (q : ι → κ) :
    abstractBarycentric (P.map q) =
      (abstractBarycentric P).map (fun s : Finset ι => s.image q) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : Fintype κ := Fintype.ofFinite κ
  ext C
  constructor
  · intro hC
    obtain ⟨u, hu, hmax⟩ := hC.2.1.exists_largest hC.1
    obtain ⟨s, hs, hsu⟩ := hC.2.2 u hu
    change s.image q = u at hsu
    let pre : Finset κ → Finset ι := fun t => s.filter (fun i => q i ∈ t)
    have hpre : ∀ t ∈ C, (pre t).image q = t := by
      intro t ht
      ext j
      constructor
      · rintro hj
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
        exact (Finset.mem_filter.mp hi).2
      · intro hj
        have hju : j ∈ s.image q := by
          rw [hsu]
          exact hmax t ht hj
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hju
        exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hj⟩, rfl⟩
    have hpne : ∀ t ∈ C, (pre t).Nonempty := by
      intro t ht
      exact Finset.image_nonempty.mp (show ((pre t).image q).Nonempty by
        rw [hpre t ht]
        exact hC.2.1.1 t ht)
    refine ⟨C.image pre, ⟨Finset.image_nonempty.mpr hC.1, ⟨?_, ?_⟩, ?_⟩, ?_⟩
    · intro t ht
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ht
      exact hpne v hv
    · rintro t ht v hv
      obtain ⟨t0, ht0, rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨v0, hv0, rfl⟩ := Finset.mem_image.mp hv
      rcases hC.2.1.2 t0 ht0 v0 hv0 with htv | hvt
      · exact Or.inl (fun i hi => Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hi).1, htv (Finset.mem_filter.mp hi).2⟩)
      · exact Or.inr (fun i hi => Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hi).1, hvt (Finset.mem_filter.mp hi).2⟩)
    · intro t ht
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ht
      exact (P.isRelLowerSet_faces hs).2 (Finset.filter_subset _ _) (hpne v hv)
    · change (C.image pre).image (fun s : Finset ι => s.image q) = C
      ext t
      constructor
      · intro ht
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hs
        rwa [hpre v hv]
      · intro ht
        exact Finset.mem_image.mpr ⟨pre t, Finset.mem_image.mpr ⟨t, ht, rfl⟩, hpre t ht⟩
  · rintro ⟨C, hC, rfl⟩
    refine ⟨Finset.image_nonempty.mpr hC.1, ⟨?_, ?_⟩, ?_⟩
    · intro t ht
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
      exact Finset.image_nonempty.mpr (hC.2.1.1 s hs)
    · intro s hs t ht
      obtain ⟨s0, hs0, rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨t0, ht0, rfl⟩ := Finset.mem_image.mp ht
      exact (hC.2.1.2 s0 hs0 t0 ht0).imp Finset.image_subset_image Finset.image_subset_image
    · intro s hs
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
      exact ⟨t, hC.2.2 t ht, rfl⟩

def fullVertexSubcomplex (P : PreAbstractSimplicialComplex ι) (A : Set ι) :
    PreAbstractSimplicialComplex ι where
  faces := {s | s ∈ P.faces ∧ (s : Set ι) ⊆ A}
  isRelLowerSet_faces := by
    intro s hs
    exact ⟨(P.isRelLowerSet_faces hs.1).1, fun t hts ht =>
      ⟨(P.isRelLowerSet_faces hs.1).2 hts ht, fun _ hi => hs.2 (hts hi)⟩⟩

omit [DecidableEq ι] [Fintype ι] in
theorem abstractBarycentric_subcomplex_full [Finite ι]
    {P D : PreAbstractSimplicialComplex ι} (hDP : D ≤ P) :
    abstractBarycentric D = fullVertexSubcomplex (abstractBarycentric P) D.faces := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  ext C
  constructor
  · intro hC
    exact ⟨⟨hC.1, hC.2.1, fun s hs => hDP (hC.2.2 s hs)⟩, hC.2.2⟩
  · intro hC
    exact ⟨hC.1.1, hC.1.2.1, hC.2⟩

omit [DecidableEq ι] [Fintype ι] in
theorem abstractBarycentric_fullVertexSubcomplex [Finite ι]
    (P : PreAbstractSimplicialComplex ι) (A : Set ι) :
    abstractBarycentric (fullVertexSubcomplex P A) =
      fullVertexSubcomplex (abstractBarycentric P) {s | (s : Set ι) ⊆ A} := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  ext C
  change (C.Nonempty ∧ isFaceChain C ∧ ∀ s ∈ C, s ∈ P.faces ∧ (s : Set ι) ⊆ A) ↔
    (C.Nonempty ∧ isFaceChain C ∧ ∀ s ∈ C, s ∈ P.faces) ∧ ∀ s ∈ C, (s : Set ι) ⊆ A
  aesop

theorem mem_standardRealization_fullVertexSubcomplex_iff
    (P : PreAbstractSimplicialComplex ι) (A : Set ι) {x : ι → ℝ}
    (hx : x ∈ (standardRealization P).space) :
    x ∈ (standardRealization (fullVertexSubcomplex P A)).space ↔
      ∀ i ∉ A, x i = 0 := by
  classical
  constructor
  · intro h
    obtain ⟨s, hs, hxs⟩ := (standardRealization_mem_space _ _).mp h
    have hzero := (mem_standardFace_iff s x).mp hxs |>.2
    exact fun i hi => hzero i (fun his => hi (hs.2 his))
  · intro hzero
    obtain ⟨s, hs, hxs⟩ := (standardRealization_mem_space _ _).mp hx
    have hcoords := (mem_standardFace_iff s x).mp hxs
    let t := s.filter (fun i => i ∈ A)
    have htzero : ∀ i ∉ t, x i = 0 := by
      intro i hi
      by_cases his : i ∈ s
      · exact hzero i (fun hiA => hi (Finset.mem_filter.mpr ⟨his, hiA⟩))
      · exact hcoords.2 i his
    have htne : t.Nonempty := by
      by_contra hn
      have hte := Finset.not_nonempty_iff_eq_empty.mp hn
      have hall : ∀ i, x i = 0 := fun i => htzero i (by simp [hte])
      have hsum := hcoords.1.2
      simp [hall] at hsum
    apply (standardRealization_mem_space _ _).mpr
    refine ⟨t, ⟨(P.isRelLowerSet_faces hs).2 (Finset.filter_subset _ _) htne,
      fun i hi => (Finset.mem_filter.mp hi).2⟩, ?_⟩
    exact (mem_standardFace_iff t x).mpr ⟨hcoords.1, htzero⟩

def quotientFaceLabel (A : Set ι) (q : ι → κ) (s : Finset ι) :
    Finset κ ⊕ Finset ι := by
  classical
  exact if (s : Set ι) ⊆ A then Sum.inl (s.image q) else Sum.inr s

omit [DecidableEq ι] [Fintype ι] [Fintype κ] in
@[simp] theorem quotientFaceLabel_of_subset [Finite ι] [Finite κ] (A : Set ι) (q : ι → κ)
    {s : Finset ι} (hs : (s : Set ι) ⊆ A) :
    quotientFaceLabel A q s = Sum.inl (s.image q) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : Fintype κ := Fintype.ofFinite κ
  simp [quotientFaceLabel, hs]

omit [DecidableEq ι] [Fintype ι] [Fintype κ] in
@[simp] theorem quotientFaceLabel_of_not_subset [Finite ι] [Finite κ] (A : Set ι) (q : ι → κ)
    {s : Finset ι} (hs : ¬ (s : Set ι) ⊆ A) :
    quotientFaceLabel A q s = Sum.inr s := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : Fintype κ := Fintype.ofFinite κ
  simp [quotientFaceLabel, hs]

omit [DecidableEq ι] [Fintype ι] [Fintype κ] in
theorem quotientFaceLabel_eq_exterior_iff [Finite ι] [Finite κ] (A : Set ι) (q : ι → κ)
    {s t : Finset ι} (hs : ¬ (s : Set ι) ⊆ A) :
    quotientFaceLabel A q t = quotientFaceLabel A q s ↔ t = s := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : Fintype κ := Fintype.ofFinite κ
  by_cases ht : (t : Set ι) ⊆ A
  · have hne : t ≠ s := fun h => hs (h ▸ ht)
    simp [quotientFaceLabel, hs, ht, hne]
  · simp [quotientFaceLabel, hs, ht]

omit [DecidableEq ι] [Fintype ι] [Fintype κ] in
private theorem image_injective_on_subsets [Finite ι] [Finite κ] {q : ι → κ} {S : Set ι}
    (hq : S.InjOn q) {s t : Finset ι} (hs : (s : Set ι) ⊆ S)
    (ht : (t : Set ι) ⊆ S) (h : s.image q = t.image q) : s = t := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : Fintype κ := Fintype.ofFinite κ
  ext i
  constructor
  · intro hi
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp (h ▸ Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    exact hq (ht hj) (hs hi) hji ▸ hj
  · intro hi
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp (h.symm ▸ Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    exact hq (hs hj) (ht hi) hji ▸ hj

omit [DecidableEq ι] [Fintype ι] in
private theorem inside_chain_face_subset_exterior [Finite ι] {C : Finset (Finset ι)}
    (hC : isFaceChain C) {A : Set ι} {s u : Finset ι}
    (hs : s ∈ C) (hu : u ∈ C) (hsA : (s : Set ι) ⊆ A)
    (huA : ¬ (u : Set ι) ⊆ A) : s ⊆ u := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  rcases hC.2 s hs u hu with hsu | hus
  · exact hsu
  · exact (huA (fun i hi => hsA (hus hi))).elim

omit [DecidableEq ι] [Fintype ι] [Fintype κ] in
theorem quotientFaceLabel_injOn_chain [Finite ι] [Finite κ]
    (P : PreAbstractSimplicialComplex ι) (A : Set ι) (q : ι → κ)
    (hq : ∀ u ∈ P.faces, ((u : Set ι) ∩ A).InjOn q)
    {C : Finset (Finset ι)} (hC : C ∈ (abstractBarycentric P).faces) :
    (C : Set (Finset ι)).InjOn (quotientFaceLabel A q) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : Fintype κ := Fintype.ofFinite κ
  intro s hs t ht hst
  by_cases hsA : (s : Set ι) ⊆ A
  · by_cases htA : (t : Set ι) ⊆ A
    · have heq : s.image q = t.image q := by simpa [quotientFaceLabel, hsA, htA] using hst
      rcases hC.2.1.2 s hs t ht with hsub | hsub
      · exact image_injective_on_subsets (hq t (hC.2.2 t ht))
          (fun i hi => ⟨hsub hi, hsA hi⟩) (fun i hi => ⟨hi, htA hi⟩) heq
      · exact image_injective_on_subsets (hq s (hC.2.2 s hs))
          (fun i hi => ⟨hi, hsA hi⟩) (fun i hi => ⟨hsub hi, htA hi⟩) heq
    · simp [quotientFaceLabel, hsA, htA] at hst
  · exact ((quotientFaceLabel_eq_exterior_iff A q hsA).mp hst.symm).symm

omit [Fintype ι] [Fintype κ] in
theorem quotientFaceLabel_injOn_union_of_common_exterior [Finite ι] [Finite κ]
    (P : PreAbstractSimplicialComplex ι) (A : Set ι) (q : ι → κ)
    (hq : ∀ u ∈ P.faces, ((u : Set ι) ∩ A).InjOn q)
    {C D : Finset (Finset ι)} (hC : C ∈ (abstractBarycentric P).faces)
    (hD : D ∈ (abstractBarycentric P).faces)
    {u : Finset ι} (huC : u ∈ C) (huD : u ∈ D) (huA : ¬ (u : Set ι) ⊆ A) :
    ((C ∪ D : Finset (Finset ι)) : Set (Finset ι)).InjOn (quotientFaceLabel A q) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : Fintype κ := Fintype.ofFinite κ
  have hsub : ∀ s ∈ C ∪ D, (s : Set ι) ⊆ A → s ⊆ u := by
    intro s hs hsA
    rcases Finset.mem_union.mp hs with hs | hs
    · exact inside_chain_face_subset_exterior hC.2.1 hs huC hsA huA
    · exact inside_chain_face_subset_exterior hD.2.1 hs huD hsA huA
  intro s hs t ht hst
  by_cases hsA : (s : Set ι) ⊆ A
  · by_cases htA : (t : Set ι) ⊆ A
    · apply image_injective_on_subsets (hq u (hC.2.2 u huC))
        (fun i hi => ⟨hsub s hs hsA hi, hsA hi⟩)
        (fun i hi => ⟨hsub t ht htA hi, htA hi⟩)
      simpa [quotientFaceLabel, hsA, htA] using hst
    · simp [quotientFaceLabel, hsA, htA] at hst
  · exact ((quotientFaceLabel_eq_exterior_iff A q hsA).mp hst.symm).symm

omit [Fintype κ] in
theorem quotientFaceLabel_point_fiber_outside [Finite κ]
    (P : PreAbstractSimplicialComplex ι) (A : Set ι) (q : ι → κ)
    (hq : ∀ u ∈ P.faces, ((u : Set ι) ∩ A).InjOn q)
    {x y : Finset ι → ℝ}
    (hx : x ∈ (standardRealization (abstractBarycentric P)).space)
    (hy : y ∈ (standardRealization (abstractBarycentric P)).space)
    (hxA : x ∉ (standardRealization
      (abstractBarycentric (fullVertexSubcomplex P A))).space)
    (hxy : vertexPushforward (quotientFaceLabel A q) x =
      vertexPushforward (quotientFaceLabel A q) y) : x = y := by
  classical
  let : Fintype κ := Fintype.ofFinite κ
  obtain ⟨C, hC, hxC⟩ := (standardRealization_mem_space _ _).mp hx
  obtain ⟨D, hD, hyD⟩ := (standardRealization_mem_space _ _).mp hy
  have hxcoords := (mem_standardFace_iff C x).mp hxC
  have hycoords := (mem_standardFace_iff D y).mp hyD
  have hex : ∃ u : Finset ι, ¬ (u : Set ι) ⊆ A ∧ x u ≠ 0 := by
    by_contra h
    apply hxA
    rw [abstractBarycentric_fullVertexSubcomplex]
    apply (mem_standardRealization_fullVertexSubcomplex_iff _ _ hx).mpr
    intro u hu
    by_contra hxu
    exact h ⟨u, hu, hxu⟩
  obtain ⟨u, huA, hxu⟩ := hex
  have hunique : ∀ t, quotientFaceLabel A q t = quotientFaceLabel A q u → t = u :=
    fun _ h => (quotientFaceLabel_eq_exterior_iff A q huA).mp h
  have hcoord : x u = y u := by
    have he := congrFun hxy (quotientFaceLabel A q u)
    simpa only [vertexPushforward_apply_of_unique _ hunique] using he
  have huC : u ∈ C := by
    by_contra hu
    exact hxu (hxcoords.2 u hu)
  have huD : u ∈ D := by
    by_contra hu
    exact hxu (hcoord.trans (hycoords.2 u hu))
  apply vertexPushforward_injective_of_supported (quotientFaceLabel A q)
    (quotientFaceLabel_injOn_union_of_common_exterior P A q hq hC hD huC huD huA)
    (fun i hi => hxcoords.2 i (fun hiC => hi (Finset.mem_union_left _ hiC)))
    (fun i hi => hycoords.2 i (fun hiD => hi (Finset.mem_union_right _ hiD))) hxy

omit [Fintype κ] in
theorem quotientFaceLabel_nontrivial_fiber_inside [Finite κ]
    (P : PreAbstractSimplicialComplex ι) (A : Set ι) (q : ι → κ)
    (hq : ∀ u ∈ P.faces, ((u : Set ι) ∩ A).InjOn q)
    {x y : Finset ι → ℝ}
    (hx : x ∈ (standardRealization (abstractBarycentric P)).space)
    (hy : y ∈ (standardRealization (abstractBarycentric P)).space)
    (hne : x ≠ y)
    (hxy : vertexPushforward (quotientFaceLabel A q) x =
      vertexPushforward (quotientFaceLabel A q) y) :
    x ∈ (standardRealization (abstractBarycentric (fullVertexSubcomplex P A))).space ∧
      y ∈ (standardRealization (abstractBarycentric (fullVertexSubcomplex P A))).space := by
  classical
  let : Fintype κ := Fintype.ofFinite κ
  constructor
  · by_contra hxA
    exact hne (quotientFaceLabel_point_fiber_outside P A q hq hx hy hxA hxy)
  · by_contra hyA
    exact hne (quotientFaceLabel_point_fiber_outside P A q hq hy hx hyA hxy.symm).symm

theorem quotientFaceLabel_pushforward_inside
    (P : PreAbstractSimplicialComplex ι) (A : Set ι) (q : ι → κ)
    {x : Finset ι → ℝ}
    (hx : x ∈ (standardRealization
      (abstractBarycentric (fullVertexSubcomplex P A))).space) :
    vertexPushforward (quotientFaceLabel A q) x =
      vertexPushforward Sum.inl (vertexPushforward (fun s : Finset ι => s.image q) x) := by
  classical
  rw [abstractBarycentric_fullVertexSubcomplex] at hx
  obtain ⟨C, hC, hxC⟩ := (standardRealization_mem_space _ _).mp hx
  have hzero : ∀ s : Finset ι, ¬ (s : Set ι) ⊆ A → x s = 0 := by
    intro s hs
    exact ((mem_standardFace_iff C x).mp hxC).2 s (fun hsC => hs (hC.2 hsC))
  rw [vertexPushforward_comp_apply]
  change (∑ s, x s • Pi.single (quotientFaceLabel A q s) (1 : ℝ)) =
    ∑ s, x s • Pi.single (Sum.inl (s.image q)) (1 : ℝ)
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : (s : Set ι) ⊆ A
  · rw [quotientFaceLabel_of_subset A q hs]
  · rw [hzero s hs]
    simp

omit [Fintype κ] in
theorem quotientFaceLabel_fiber_iff [Finite κ]
    (P : PreAbstractSimplicialComplex ι) (A : Set ι) (q : ι → κ)
    (hq : ∀ u ∈ P.faces, ((u : Set ι) ∩ A).InjOn q)
    {x y : Finset ι → ℝ}
    (hx : x ∈ (standardRealization (abstractBarycentric P)).space)
    (hy : y ∈ (standardRealization (abstractBarycentric P)).space) :
    vertexPushforward (quotientFaceLabel A q) x = vertexPushforward (quotientFaceLabel A q) y ↔
      x = y ∨
        (x ∈ (standardRealization (abstractBarycentric (fullVertexSubcomplex P A))).space ∧
        y ∈ (standardRealization (abstractBarycentric (fullVertexSubcomplex P A))).space ∧
        vertexPushforward (fun s : Finset ι => s.image q) x =
          vertexPushforward (fun s : Finset ι => s.image q) y) := by
  classical
  let : Fintype κ := Fintype.ofFinite κ
  constructor
  · intro hxy
    by_cases heq : x = y
    · exact Or.inl heq
    · obtain ⟨hxA, hyA⟩ := quotientFaceLabel_nontrivial_fiber_inside P A q hq hx hy heq hxy
      refine Or.inr ⟨hxA, hyA, ?_⟩
      rw [quotientFaceLabel_pushforward_inside P A q hxA,
        quotientFaceLabel_pushforward_inside P A q hyA] at hxy
      exact vertexPushforward_injective (Sum.inl : Finset κ → Finset κ ⊕ Finset ι)
        Sum.inl_injective hxy
  · rintro (rfl | ⟨hxA, hyA, hxy⟩)
    · rfl
    · rw [quotientFaceLabel_pushforward_inside P A q hxA,
        quotientFaceLabel_pushforward_inside P A q hyA, hxy]

omit [DecidableEq ι] [Fintype ι] in
theorem abstractBarycentric_face_card_le [Finite ι] (P : PreAbstractSimplicialComplex ι) {n : ℕ}
    (hn : ∀ s ∈ P.faces, s.card ≤ n) :
    ∀ C ∈ (abstractBarycentric P).faces, C.card ≤ n := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  intro C hC
  obtain ⟨u, hu, hmax⟩ := hC.2.1.exists_largest hC.1
  have hinj : (C : Set (Finset ι)).InjOn Finset.card := by
    intro s hs t ht hcard
    rcases hC.2.1.2 s hs t ht with hsub | hsub
    · exact Finset.eq_of_subset_of_card_le hsub hcard.ge
    · exact (Finset.eq_of_subset_of_card_le hsub hcard.le).symm
  have hsub : C.image Finset.card ⊆ Finset.Icc 1 u.card := by
    intro k hk
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_Icc.mpr ⟨Finset.card_pos.mpr (hC.2.1.1 s hs),
      Finset.card_le_card (hmax s hs)⟩
  calc
    C.card = (C.image Finset.card).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.Icc 1 u.card).card := Finset.card_le_card hsub
    _ = u.card := by simp
    _ ≤ n := hn u (hC.2.2 u hu)

def polyhedralQuotientComplex (P : PreAbstractSimplicialComplex ι) (A : Set ι) (q : ι → κ) :
    SimplicialComplex ℝ ((Finset κ ⊕ Finset ι) → ℝ) :=
  standardRealization ((abstractBarycentric P).map (quotientFaceLabel A q))

theorem polyhedralQuotientComplex_finite_faces
    (P : PreAbstractSimplicialComplex ι) (A : Set ι) (q : ι → κ) :
    (polyhedralQuotientComplex P A q).faces.Finite := standardRealization_finite_faces _

theorem polyhedralQuotientComplex_face_card_le
    (P : PreAbstractSimplicialComplex ι) (A : Set ι) (q : ι → κ) {n : ℕ}
    (hn : ∀ s ∈ P.faces, s.card ≤ n) :
    ∀ s ∈ (polyhedralQuotientComplex P A q).faces, s.card ≤ n := by
  apply standardRealization_face_card_le
  rintro s ⟨C, hC, rfl⟩
  exact Finset.card_image_le.trans (abstractBarycentric_face_card_le P hn C hC)

def polyhedralQuotientMap (P : PreAbstractSimplicialComplex ι) (A : Set ι) (q : ι → κ) :
    (standardRealization (abstractBarycentric P)).space →
      (polyhedralQuotientComplex P A q).space :=
  standardVertexMap (abstractBarycentric P) (quotientFaceLabel A q)

theorem isQuotientMap_polyhedralQuotientMap
    (P : PreAbstractSimplicialComplex ι) (A : Set ι) (q : ι → κ) :
    IsQuotientMap (polyhedralQuotientMap P A q) := isQuotientMap_standardVertexMap _ _

def polyhedralQuotientHomeomorph (P : PreAbstractSimplicialComplex ι) (A : Set ι) (q : ι → κ) :
    Quotient (Setoid.ker (polyhedralQuotientMap P A q)) ≃ₜ
      (polyhedralQuotientComplex P A q).space :=
  standardVertexQuotientHomeomorph _ _

theorem polyhedralQuotient_inside_image
    (P : PreAbstractSimplicialComplex ι) (A : Set ι) (q : ι → κ) :
    vertexPushforward (quotientFaceLabel A q) ''
        (standardRealization (abstractBarycentric (fullVertexSubcomplex P A))).space =
      vertexPushforward (Sum.inl : Finset κ → Finset κ ⊕ Finset ι) ''
        (standardRealization (abstractBarycentric ((fullVertexSubcomplex P A).map q))).space := by
  calc
    _ = (vertexPushforward (Sum.inl : Finset κ → Finset κ ⊕ Finset ι) ∘
        vertexPushforward (fun s : Finset ι => s.image q)) ''
        (standardRealization (abstractBarycentric (fullVertexSubcomplex P A))).space :=
      Set.image_congr (fun _ hx => quotientFaceLabel_pushforward_inside P A q hx)
    _ = _ := by rw [Set.image_comp, vertexPushforward_image_space, ← abstractBarycentric_map]

def polyhedralQuotientInsideMap
    (P : PreAbstractSimplicialComplex ι) (A : Set ι) (q : ι → κ) :
    (standardRealization (abstractBarycentric ((fullVertexSubcomplex P A).map q))).space →
      (polyhedralQuotientComplex P A q).space := by
  intro y
  refine ⟨vertexPushforward Sum.inl y.val, ?_⟩
  have hy := (polyhedralQuotient_inside_image P A q).symm.subset
    (mem_image_of_mem (vertexPushforward (Sum.inl : Finset κ → Finset κ ⊕ Finset ι)) y.property)
  obtain ⟨x, hx, hxy⟩ := hy
  have hxP : x ∈ (standardRealization (abstractBarycentric P)).space :=
    standardRealization_mono (abstractBarycentric_mono
      (show fullVertexSubcomplex P A ≤ P from fun _ hs => hs.1)) hx
  exact hxy ▸ (vertexPushforward_image_space (abstractBarycentric P)
    (quotientFaceLabel A q)).subset (mem_image_of_mem _ hxP)

theorem isClosedEmbedding_polyhedralQuotientInsideMap
    (P : PreAbstractSimplicialComplex ι) (A : Set ι) (q : ι → κ) :
    IsClosedEmbedding (polyhedralQuotientInsideMap P A q) := by
  apply Continuous.isClosedEmbedding
  · exact ((vertexPushforward (Sum.inl : Finset κ → Finset κ ⊕ Finset ι)).continuous_of_finiteDimensional.comp
      continuous_subtype_val).subtype_mk _
  · intro x y hxy
    exact Subtype.ext (vertexPushforward_injective _ Sum.inl_injective (congrArg Subtype.val hxy))

theorem range_polyhedralQuotientInsideMap
    (P : PreAbstractSimplicialComplex ι) (A : Set ι) (q : ι → κ) :
    Set.range (polyhedralQuotientInsideMap P A q) =
      polyhedralQuotientMap P A q ''
        {x | x.val ∈ (standardRealization
          (abstractBarycentric (fullVertexSubcomplex P A))).space} := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    have hy := (polyhedralQuotient_inside_image P A q).symm.subset
      (mem_image_of_mem (vertexPushforward (Sum.inl : Finset κ → Finset κ ⊕ Finset ι)) y.property)
    obtain ⟨x, hx, hxy⟩ := hy
    have hxP : x ∈ (standardRealization (abstractBarycentric P)).space :=
      standardRealization_mono (abstractBarycentric_mono
        (show fullVertexSubcomplex P A ≤ P from fun _ hs => hs.1)) hx
    exact ⟨⟨x, hxP⟩, hx, Subtype.ext hxy⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := (polyhedralQuotient_inside_image P A q).subset
      (mem_image_of_mem (vertexPushforward (quotientFaceLabel A q)) hx)
    exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩

omit [DecidableEq ι] [Fintype ι] [Fintype κ] in
theorem faceImage_injOn_barycentric_subcomplex [Finite ι] [Finite κ]
    (P D : PreAbstractSimplicialComplex ι) (q : ι → κ)
    (hq : ∀ s ∈ D.faces, (s : Set ι).InjOn q) :
    ∀ C ∈ (abstractBarycentric P).faces,
      ((C : Set (Finset ι)) ∩ D.faces).InjOn (fun s : Finset ι => s.image q) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : Fintype κ := Fintype.ofFinite κ
  intro C hC s hs t ht heq
  rcases hC.2.1.2 s hs.1 t ht.1 with hsub | hsub
  · exact image_injective_on_subsets (hq t ht.2) hsub (fun _ hi => hi) heq
  · exact image_injective_on_subsets (hq s hs.2) (fun _ hi => hi) hsub heq

def subcomplexQuotientComplex (P D : PreAbstractSimplicialComplex ι) (q : ι → κ) :
    SimplicialComplex ℝ ((Finset (Finset κ) ⊕ Finset (Finset ι)) → ℝ) :=
  polyhedralQuotientComplex (abstractBarycentric P) D.faces (fun s : Finset ι => s.image q)

def subcomplexQuotientMap (P D : PreAbstractSimplicialComplex ι) (q : ι → κ) :
    (standardRealization (abstractBarycentric (abstractBarycentric P))).space →
      (subcomplexQuotientComplex P D q).space :=
  polyhedralQuotientMap (abstractBarycentric P) D.faces (fun s : Finset ι => s.image q)

theorem subcomplexQuotientMap_fiber_iff
    (P D : PreAbstractSimplicialComplex ι) (hDP : D ≤ P) (q : ι → κ)
    (hq : ∀ s ∈ D.faces, (s : Set ι).InjOn q)
    (x y : (standardRealization (abstractBarycentric (abstractBarycentric P))).space) :
    subcomplexQuotientMap P D q x = subcomplexQuotientMap P D q y ↔
      x = y ∨
        (x.val ∈ (standardRealization (abstractBarycentric (abstractBarycentric D))).space ∧
        y.val ∈ (standardRealization (abstractBarycentric (abstractBarycentric D))).space ∧
        vertexPushforward (fun C : Finset (Finset ι) => C.image (fun s => s.image q)) x.val =
          vertexPushforward (fun C : Finset (Finset ι) => C.image (fun s => s.image q)) y.val) := by
  rw [Subtype.ext_iff]
  change vertexPushforward (quotientFaceLabel D.faces (fun s : Finset ι => s.image q)) x.val =
      vertexPushforward (quotientFaceLabel D.faces (fun s : Finset ι => s.image q)) y.val ↔ _
  rw [quotientFaceLabel_fiber_iff (abstractBarycentric P) D.faces _
    (faceImage_injOn_barycentric_subcomplex P D q hq) x.property y.property,
    ← abstractBarycentric_subcomplex_full hDP]
  simp only [Subtype.ext_iff]

theorem subcomplexQuotientComplex_finite_faces
    (P D : PreAbstractSimplicialComplex ι) (q : ι → κ) :
    (subcomplexQuotientComplex P D q).faces.Finite := polyhedralQuotientComplex_finite_faces _ _ _

theorem subcomplexQuotientComplex_face_card_le
    (P D : PreAbstractSimplicialComplex ι) (q : ι → κ) {n : ℕ}
    (hn : ∀ s ∈ P.faces, s.card ≤ n) :
    ∀ s ∈ (subcomplexQuotientComplex P D q).faces, s.card ≤ n :=
  polyhedralQuotientComplex_face_card_le _ _ _ (abstractBarycentric_face_card_le P hn)

theorem isQuotientMap_subcomplexQuotientMap
    (P D : PreAbstractSimplicialComplex ι) (q : ι → κ) :
    IsQuotientMap (subcomplexQuotientMap P D q) := isQuotientMap_polyhedralQuotientMap _ _ _

def subcomplexQuotientHomeomorph
    (P D : PreAbstractSimplicialComplex ι) (q : ι → κ) :
    Quotient (Setoid.ker (subcomplexQuotientMap P D q)) ≃ₜ
      (subcomplexQuotientComplex P D q).space :=
  polyhedralQuotientHomeomorph _ _ _

end

end DifferentialGeometry.Topology.Engulfing
