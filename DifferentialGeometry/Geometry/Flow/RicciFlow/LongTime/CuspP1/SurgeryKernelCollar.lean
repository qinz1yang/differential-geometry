import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryKernelThin
import DifferentialGeometry.Topology.VanKampen.FreeFactors.SeparatedCollarGroups
import DifferentialGeometry.Topology.VanKampen.TwoSidedCollarCover
import Mathlib.Analysis.Convex.Contractible

set_option autoImplicit false

/-!
# CP1-D2 (G1b): a component of the complement of finitely many collared simply connected slices
injects on `π₁`.
-/

noncomputable section
open Set DifferentialGeometry.Topology DifferentialGeometry.Topology.VanKampen
open DifferentialGeometry.Topology.ThreeManifold GC.Topology

namespace GC.LongTime.CuspP1

universe u v w

section Collar

variable {S : Type v} [TopologicalSpace S] {X : Type u} [TopologicalSpace X]
  {ι : Type w} {e : ι → S → X} (c : ∀ i, TwoSidedCollar (e i))

/-- the two open halves of the `i`-th collar -/
def halfCollar_CPD2 (i : ι) (b : Bool) : Set X :=
  (c i).toFun '' (univ ×ˢ (if b then Ioi (0 : ℝ) else Iio (0 : ℝ)))

theorem isOpen_halfCollar_CPD2 (i : ι) (b : Bool) : IsOpen (halfCollar_CPD2 c i b) := by
  apply (c i).isOpenEmbedding_toFun.isOpenMap
  apply isOpen_univ.prod
  cases b <;> simp [isOpen_Ioi, isOpen_Iio]

theorem halfCollar_subset_range_CPD2 (i : ι) (b : Bool) :
    halfCollar_CPD2 c i b ⊆ (c i).range := by
  rintro _ ⟨p, _, rfl⟩
  exact ⟨p, rfl⟩

theorem isPreconnected_halfCollar_CPD2 [PreconnectedSpace S] (i : ι) (b : Bool) :
    IsPreconnected (halfCollar_CPD2 c i b) := by
  apply IsPreconnected.image _ _ (c i).isOpenEmbedding_toFun.continuous.continuousOn
  apply isPreconnected_univ.prod
  cases b
  · exact isPreconnected_Iio
  · exact isPreconnected_Ioi

theorem simplyConnected_halfCollar_CPD2 [SimplyConnectedSpace S] (i : ι) (b : Bool) :
    SimplyConnectedSpace (halfCollar_CPD2 c i b) := by
  cases b
  · let : ContractibleSpace (Iio (0 : ℝ)) := (convex_Iio 0).contractibleSpace ⟨-1, by norm_num⟩
    exact simplyConnectedSpace_collar_image (c i) (Iio 0)
  · let : ContractibleSpace (Ioi (0 : ℝ)) := (convex_Ioi 0).contractibleSpace ⟨1, by norm_num⟩
    exact simplyConnectedSpace_collar_image (c i) (Ioi 0)

theorem range_subset_range_CPD2 (i : ι) : Set.range (e i) ⊆ (c i).range := by
  rintro _ ⟨s, rfl⟩
  exact ⟨(s, 0), (c i).zero_eq s⟩

theorem halfCollar_disjoint_slices_CPD2 (hdisj : Pairwise fun i j => Disjoint (c i).range (c j).range)
    (i : ι) (b : Bool) (j : ι) : Disjoint (halfCollar_CPD2 c i b) (Set.range (e j)) := by
  rw [Set.disjoint_left]
  rintro _ ⟨⟨s, t⟩, ⟨-, ht⟩, rfl⟩ ⟨s', hs'⟩
  by_cases hij : i = j
  · subst hij
    have h1 : (c i).toFun (s', 0) = (c i).toFun (s, t) := by rw [(c i).zero_eq]; exact hs'
    have h2 := (c i).isOpenEmbedding_toFun.injective h1
    have h3 : t = 0 := (congrArg Prod.snd h2).symm
    cases b <;> simp_all
  · have hmem : e j s' ∈ (c j).range := range_subset_range_CPD2 c j ⟨s', rfl⟩
    exact (Set.disjoint_left.mp (hdisj hij)) ⟨(s, t), rfl⟩ (hs' ▸ hmem)

theorem halfCollar_disjoint_CPD2 (hdisj : Pairwise fun i j => Disjoint (c i).range (c j).range)
    {p q : ι × Bool} (hpq : p ≠ q) :
    Disjoint (halfCollar_CPD2 c p.1 p.2) (halfCollar_CPD2 c q.1 q.2) := by
  by_cases h : p.1 = q.1
  · have hb : p.2 ≠ q.2 := fun hb => hpq (Prod.ext h hb)
    rw [Set.disjoint_left]
    rintro _ ⟨⟨s, t⟩, ⟨-, ht⟩, rfl⟩ ⟨⟨s', t'⟩, ⟨-, ht'⟩, hy⟩
    have h1 : (c q.1).toFun (s', t') = (c p.1).toFun (s, t) := hy
    rw [← h] at h1
    have h2 := (c p.1).isOpenEmbedding_toFun.injective h1
    have h3 : t' = t := congrArg Prod.snd h2
    subst h3
    rcases p with ⟨_, bp⟩
    rcases q with ⟨_, bq⟩
    cases bp <;> cases bq <;> simp_all <;> linarith
  · exact (hdisj h).mono (halfCollar_subset_range_CPD2 c _ _) (halfCollar_subset_range_CPD2 c _ _)

end Collar

section Main

variable {S : Type v} [TopologicalSpace S] [CompactSpace S] [SimplyConnectedSpace S]
  {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyPathConnectedSpace X]
  {ι : Type w} [Finite ι] {e : ι → S → X} (c : ∀ i, TwoSidedCollar (e i))

/-- A path component of the complement of finitely many pairwise disjoint collared simply
connected slices includes `π₁`-injectively into the ambient space (gluing along simply connected
slices gives a free product with a free group). -/
theorem injective_component_compl_collars_CPD2
    (hdisj : Pairwise fun i j => Disjoint (c i).range (c j).range) (x : X)
    (hx : x ∈ (⋃ i, Set.range (e i))ᶜ) :
    Function.Injective (FundamentalGroup.map
      (subsetToAmbient (connectedComponentIn (⋃ i, Set.range (e i))ᶜ x))
      ⟨x, mem_connectedComponentIn hx⟩) := by
  classical
  set A : Set X := (⋃ i, Set.range (e i))ᶜ with hAdef
  have hAo : IsOpen A :=
    (isClosed_iUnion_of_finite
      (fun i => (isCompact_range (c i).continuous_e).isClosed)).isOpen_compl
  set K : Set X := connectedComponentIn A x with hKdef
  have hKo : IsOpen K := hAo.connectedComponentIn
  have hxK : x ∈ K := mem_connectedComponentIn hx
  have hKA : K ⊆ A := connectedComponentIn_subset A x
  have : LocallyPathConnectedSpace K := hKo.locallyPathConnectedSpace
  have : ConnectedSpace K :=
    isConnected_iff_connectedSpace.mp (isConnected_connectedComponentIn_iff.mpr hx)
  have : PathConnectedSpace K := PathConnectedSpace.of_locallyPathConnectedSpace
  -- the pieces of the overlap
  let J : Type _ := {p : ι × Bool // halfCollar_CPD2 c p.1 p.2 ⊆ K}
  let Vf : J → Set X := fun p => halfCollar_CPD2 c p.1.1 p.1.2
  have hVA : ∀ i b, halfCollar_CPD2 c i b ⊆ A := by
    intro i b y hy hyU
    obtain ⟨j, hj⟩ := mem_iUnion.mp hyU
    exact (Set.disjoint_left.mp (halfCollar_disjoint_slices_CPD2 c hdisj i b j)) hy hj
  have hAK : IsOpen (A \ K) := by
    rw [isOpen_iff_forall_mem_open]
    rintro y ⟨hyA, hyK⟩
    refine ⟨connectedComponentIn A y, ?_, hAo.connectedComponentIn,
      mem_connectedComponentIn hyA⟩
    intro z hz
    refine ⟨connectedComponentIn_subset A y hz, fun hzK => hyK ?_⟩
    have h1 := connectedComponentIn_eq hz
    have h2 := connectedComponentIn_eq hzK
    have : y ∈ connectedComponentIn A x := by
      rw [h2, ← h1]; exact mem_connectedComponentIn hyA
    exact this
  let W : Set X := (A \ K) ∪ ⋃ i, (c i).range
  have hWo : IsOpen W := hAK.union (isOpen_iUnion fun i => (c i).isOpenEmbedding_toFun.isOpen_range)
  have hcover : K ∪ W = univ := by
    apply eq_univ_of_forall
    intro y
    by_cases hyA : y ∈ A
    · by_cases hyK : y ∈ K
      · exact Or.inl hyK
      · exact Or.inr (Or.inl ⟨hyA, hyK⟩)
    · have : y ∈ ⋃ i, Set.range (e i) := by simpa [hAdef] using hyA
      obtain ⟨i, hi⟩ := mem_iUnion.mp this
      exact Or.inr (Or.inr (mem_iUnion.mpr ⟨i, range_subset_range_CPD2 c i hi⟩))
  have hUW : K ∩ W = ⋃ p : J, Vf p := by
    ext y
    constructor
    · rintro ⟨hyK, hyW⟩
      rcases hyW with hyW | hyW
      · exact absurd hyK hyW.2
      · obtain ⟨i, ⟨⟨s, t⟩, rfl⟩⟩ := mem_iUnion.mp hyW
        have ht : t ≠ 0 := by
          intro ht0
          subst ht0
          apply hKA hyK
          exact mem_iUnion.mpr ⟨i, ⟨s, (c i).zero_eq s ▸ rfl⟩⟩
        have hyKc : K = connectedComponentIn A ((c i).toFun (s, t)) := connectedComponentIn_eq hyK
        have key : ∀ b : Bool, (c i).toFun (s, t) ∈ halfCollar_CPD2 c i b →
            (c i).toFun (s, t) ∈ ⋃ p : J, Vf p := by
          intro b hb
          have hsub : halfCollar_CPD2 c i b ⊆ K := by
            rw [hyKc]
            exact (isPreconnected_halfCollar_CPD2 c i b).subset_connectedComponentIn hb (hVA i b)
          exact mem_iUnion.mpr ⟨⟨(i, b), hsub⟩, hb⟩
        rcases lt_or_gt_of_ne ht with h | h
        · exact key false ⟨(s, t), ⟨trivial, by simpa using h⟩, rfl⟩
        · exact key true ⟨(s, t), ⟨trivial, by simpa using h⟩, rfl⟩
    · intro hy
      obtain ⟨p, hp⟩ := mem_iUnion.mp hy
      exact ⟨p.2 hp, Or.inr (mem_iUnion.mpr ⟨p.1.1, halfCollar_subset_range_CPD2 c _ _ hp⟩)⟩
  have : ∀ p : J, SimplyConnectedSpace (Vf p) := fun p =>
    simplyConnected_halfCollar_CPD2 c p.1.1 p.1.2
  exact injective_of_thin_overlap_CPD2 K W hKo hWo hcover Vf
    (fun p => isOpen_halfCollar_CPD2 c _ _)
    (fun p q hpq => halfCollar_disjoint_CPD2 c hdisj (fun h => hpq (Subtype.ext h)))
    (fun p => inferInstance) hUW ⟨x, hxK⟩

end Main

end GC.LongTime.CuspP1
