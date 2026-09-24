import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutBandFrontier
import DifferentialGeometry.Topology.OpenPartialHomeomorph.CollarAdvance
import DifferentialGeometry.Topology.Diffeomorph.FiberwiseAffine
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphTrans

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]

def outwardCutCylinder (Φ : PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ThreeSpace) (Sphere 2 × ℝ) M ∞) (side : Bool) :
    PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ThreeSpace) (Sphere 2 × ℝ) M ∞ :=
  (Diffeomorph.fiberwiseAffine (fun _ : Sphere 2 => if side then (1 : ℝ) else -1)
    (fun _ => if side then (1 / 2 : ℝ) else -(1 / 2))
    contMDiff_const contMDiff_const (by intro; cases side <;> norm_num)).toPartialDiffeomorph.trans
      Φ

theorem outwardCutCylinder_apply (Φ : PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ThreeSpace) (Sphere 2 × ℝ) M ∞) (side : Bool)
    (z : Sphere 2) (t : ℝ) :
    outwardCutCylinder Φ side (z, t) = Φ (z, if side then 1 + t / 2 else -1 - t / 2) := by
  change Φ (z, (if side then 1 else -1) + (if side then 1 / 2 else -(1 / 2)) * t) = _
  congr 1
  refine Prod.ext rfl ?_
  cases side <;> simp only [Bool.false_eq_true, if_false, if_true] <;> ring

theorem outwardCutCylinder_source
    (Φ : PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ThreeSpace) (Sphere 2 × ℝ) M ∞)
    (hsource : univ ×ˢ Icc (-(3 / 2) : ℝ) (3 / 2) ⊆ Φ.source) (side : Bool) :
    univ ×ˢ Icc (0 : ℝ) 1 ⊆ (outwardCutCylinder Φ side).source := by
  rintro ⟨z, t⟩ ⟨_, ht⟩
  refine ⟨mem_univ _, hsource ?_⟩
  change (z, (if side then 1 else -1) + (if side then 1 / 2 else -(1 / 2)) * t) ∈
    univ ×ˢ Icc (-(3 / 2) : ℝ) (3 / 2)
  refine ⟨mem_univ _, ?_, ?_⟩ <;> cases side <;>
    simp only [Bool.false_eq_true, if_false, if_true] <;> linarith [ht.1, ht.2]

theorem outwardCutCylinder_upper (Φ : PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ThreeSpace) (Sphere 2 × ℝ) M ∞) (side : Bool)
    (z : Sphere 2) :
    outwardCutCylinder Φ side (z, 1) = Φ (z, if side then 3 / 2 else -(3 / 2)) := by
  rw [outwardCutCylinder_apply Φ]
  cases side <;> norm_num

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  (T : TubeSystem M)
  (Φ : PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ThreeSpace) (Sphere 2 × ℝ) M ∞)
  (b : T.Boundary)
  (hmap : ∀ q : TubeDomain, T.tube b.1 q = Φ (q.1, q.2.val))

include hmap

private theorem outwardCutCylinder_lower (z : Sphere 2) :
    outwardCutCylinder Φ b.2 (z, 0) = T.boundarySphere b z := by
  rw [outwardCutCylinder_apply Φ]
  change _ = T.tube b.1 (z, boundaryLevel b.2)
  rw [hmap]
  cases b.2 <;> simp [boundaryLevel]

private theorem outwardCutCylinder_image_subset_tube :
    outwardCutCylinder Φ b.2 '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆ range (T.tube b.1) := by
  rintro _ ⟨⟨z, t⟩, ⟨_, ht⟩, rfl⟩
  let s : ℝ := if b.2 then 1 + t / 2 else -1 - t / 2
  have hs : s ∈ Icc (-2 : ℝ) 2 := by
    cases hside : b.2 <;> simp only [s, hside, Bool.false_eq_true, if_false, if_true] <;>
      constructor <;> linarith [ht.1, ht.2]
  exact ⟨(z, ⟨s, hs⟩), (hmap _).trans (outwardCutCylinder_apply Φ b.2 z t).symm⟩

private theorem outwardCutCylinder_mem_closedBands_iff (z : Sphere 2) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    outwardCutCylinder Φ b.2 (z, t) ∈
        ⋃ a, T.tube a '' {q : TubeDomain | q.2.val ∈ Icc (-1 : ℝ) 1} ↔ t = 0 := by
  let s : ℝ := if b.2 then 1 + t / 2 else -1 - t / 2
  have hs : s ∈ Icc (-2 : ℝ) 2 := by
    cases hside : b.2 <;> simp only [s, hside, Bool.false_eq_true, if_false, if_true] <;>
      constructor <;> linarith [ht.1, ht.2]
  let q : TubeDomain := (z, ⟨s, hs⟩)
  have he : outwardCutCylinder Φ b.2 (z, t) = T.tube b.1 q :=
    (outwardCutCylinder_apply Φ b.2 z t).trans (hmap q).symm
  constructor
  · intro hm
    obtain ⟨a, r, hr, her⟩ := mem_iUnion.mp hm
    have ha : a = b.1 := by
      by_contra hn
      exact disjoint_left.mp (T.disjoint hn) (mem_range_self r)
        ⟨q, he.symm.trans her.symm⟩
    subst a
    have hq := (T.embedding b.1).injective (her.trans he)
    have hs' := congrArg (fun q : TubeDomain => q.2.val) hq
    change r.2.val = s at hs'
    have hb : s ∈ Icc (-1 : ℝ) 1 := hs' ▸ hr
    cases hside : b.2 <;> simp only [s, hside, Bool.false_eq_true, if_false, if_true] at hb <;>
      linarith [hb.1, hb.2, ht.1]
  · rintro rfl
    rw [T.outwardCutCylinder_lower Φ b hmap]
    exact mem_iUnion.mpr ⟨b.1, (z, boundaryLevel b.2),
      by cases b.2 <;> norm_num [boundaryLevel], rfl⟩

private theorem outwardCutCylinder_inter_closedBands :
    (outwardCutCylinder Φ b.2 '' (univ ×ˢ Icc (0 : ℝ) 1)) ∩
        (⋃ a, T.tube a '' {q : TubeDomain | q.2.val ∈ Icc (-1 : ℝ) 1}) =
      range (T.boundarySphere b) := by
  ext x
  constructor
  · rintro ⟨⟨⟨z, t⟩, ⟨_, ht⟩, rfl⟩, hx⟩
    have ht0 := (T.outwardCutCylinder_mem_closedBands_iff Φ b hmap z ht).mp hx
    change t = 0 at ht0
    subst t
    exact ⟨z, (T.outwardCutCylinder_lower Φ b hmap z).symm⟩
  · rintro ⟨z, rfl⟩
    have he := T.outwardCutCylinder_lower Φ b hmap z
    refine ⟨⟨(z, 0), ⟨mem_univ _, by norm_num⟩, he⟩, ?_⟩
    rw [← he]
    exact (T.outwardCutCylinder_mem_closedBands_iff Φ b hmap z (by norm_num)).mpr rfl

private theorem outwardCutCylinder_upper_disjoint_closedBands :
    Disjoint (range (fun z : Sphere 2 => outwardCutCylinder Φ b.2 (z, 1)))
      (⋃ a, T.tube a '' {q : TubeDomain | q.2.val ∈ Icc (-1 : ℝ) 1}) := by
  rw [disjoint_left]
  rintro x ⟨z, rfl⟩ hx
  have := (T.outwardCutCylinder_mem_closedBands_iff Φ b hmap z (by norm_num)).mp hx
  norm_num at this

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

universe u
private abbrev IC := (𝓡 2).prod 𝓘(ℝ, ℝ)
private abbrev I3 := 𝓡 3
private abbrev Cylinder := Sphere 2 × ℝ

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [T2Space M] (T : TubeSystem M)

private theorem closed_band_cylinder_advance
    (b : T.Boundary) (W : Set M) (hreg : closure (interior W) = W)
    (hfront : frontier W = ⋃ c : T.Boundary, range (T.boundarySphere c))
    (A : PartialDiffeomorph IC I3 Cylinder M ∞)
    (hA : univ ×ˢ Icc (0 : ℝ) 1 ⊆ A.source)
    (hlower : ∀ z : Sphere 2, A (z,0) = T.boundarySphere b z)
    (hinter : A '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ W = range (T.boundarySphere b)) :
    closure (interior (W ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1))) =
        W ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1) ∧
      frontier (W ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1)) =
        range (fun z : Sphere 2 => A (z,1)) ∪
          ⋃ c : {c : T.Boundary // c ≠ b}, range (T.boundarySphere c.val) := by
  let : PreconnectedSpace (Sphere 2) := isPreconnected_iff_preconnectedSpace.mp
    (isPreconnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) 1)
  let S := ⋃ c : {c : T.Boundary // c ≠ b}, range (T.boundarySphere c.val)
  have hSc : IsClosed S := isClosed_iUnion_of_finite fun c =>
    (isCompact_range (T.boundarySphere c.val).continuous).isClosed
  have hface (t : ℝ) : A '' (univ ×ˢ ({t} : Set ℝ)) = range (fun z : Sphere 2 => A (z,t)) := by
    ext y
    constructor
    · rintro ⟨⟨z,s⟩,⟨_,hs⟩,rfl⟩
      have hs' : s=t := hs
      exact ⟨z,by rw [hs']⟩
    · rintro ⟨z,rfl⟩
      exact ⟨(z,t),⟨mem_univ _,rfl⟩,rfl⟩
  have hlface : A '' (univ ×ˢ ({0} : Set ℝ)) = range (T.boundarySphere b) := by
    rw [hface]
    congr 1
    funext z
    exact hlower z
  have hsplit : frontier W = A '' (univ ×ˢ ({0} : Set ℝ)) ∪ S := by
    rw [hlface,hfront]
    ext y
    constructor
    · intro hy
      obtain ⟨c,hc⟩ := mem_iUnion.mp hy
      by_cases he : c=b
      · exact Or.inl (he ▸ hc)
      · exact Or.inr (mem_iUnion.mpr ⟨⟨c,he⟩,hc⟩)
    · rintro (hy | hy)
      · exact mem_iUnion.mpr ⟨b,hy⟩
      · obtain ⟨c,hc⟩ := mem_iUnion.mp hy
        exact mem_iUnion.mpr ⟨c.val,hc⟩
  have hWc : IsClosed W := hreg ▸ isClosed_closure
  have hSW : S ⊆ W := by
    intro y hy
    apply hWc.frontier_subset
    rw [hsplit]
    exact Or.inr hy
  have havoid : Disjoint S (A '' (univ ×ˢ Icc (0 : ℝ) 1)) := by
    rw [disjoint_left]
    intro y hyS hyA
    have hyb : y ∈ range (T.boundarySphere b) := hinter ▸ ⟨hyA,hSW hyS⟩
    obtain ⟨c,hc⟩ := mem_iUnion.mp hyS
    exact disjoint_left.mp (T.pairwise_disjoint_range_boundarySphere c.property) hc hyb
  let z : Sphere 2 := ⟨EuclideanSpace.single 0 1,by simp⟩
  have hseed : (A '' (univ ×ˢ Ioo (0 : ℝ) 1) ∩ Wᶜ).Nonempty := by
    refine ⟨A (z,1/2),⟨(z,1/2),⟨mem_univ _,by norm_num⟩,rfl⟩,?_⟩
    intro hw
    have hm : A (z,1/2) ∈ range (T.boundarySphere b) := by
      rw [← hinter]
      exact ⟨⟨(z,1/2),⟨mem_univ _,by norm_num⟩,rfl⟩,hw⟩
    obtain ⟨w,hw⟩ := hm
    have he : A (w,0) = A (z,1/2) := (hlower w).trans hw
    have heq := A.injOn (hA ⟨mem_univ _,by norm_num⟩) (hA ⟨mem_univ _,by norm_num⟩) he
    have ht := congrArg Prod.snd heq
    norm_num at ht
  obtain ⟨_,hr,hf⟩ := A.toOpenPartialHomeomorph.closed_cylinder_advance
    (by norm_num : (0 : ℝ)<1) hA hreg hSc hsplit havoid hseed
  change closure (interior (A '' (univ ×ˢ Icc (0 : ℝ) 1) ∪ W)) =
    A '' (univ ×ˢ Icc (0 : ℝ) 1) ∪ W at hr
  change frontier (A '' (univ ×ˢ Icc (0 : ℝ) 1) ∪ W) =
    S ∪ A '' (univ ×ˢ ({1} : Set ℝ)) at hf
  constructor
  · simpa only [union_comm] using hr
  · rw [hface 1] at hf
    simpa only [union_comm] using hf


theorem exists_outward_cut_cylinder_of_partialDiffeomorph
    (chart : T.Index → PartialDiffeomorph IC I3 Cylinder M ∞)
    (hsource : ∀ i, univ ×ˢ Icc (-(3 / 2) : ℝ) (3 / 2) ⊆ (chart i).source)
    (hmap : ∀ i (q : TubeDomain), T.tube i q = chart i (q.1, q.2.val))
    (b : T.Boundary) :
    let W := ⋃ i, T.tube i '' {q : TubeDomain | q.2.val ∈ Icc (-1 : ℝ) 1}
    IsCompact W ∧ closure (interior W) = W ∧
      frontier W = ⋃ c : T.Boundary, range (T.boundarySphere c) ∧
      ∃ A : PartialDiffeomorph IC I3 Cylinder M ∞,
        univ ×ˢ Icc (0 : ℝ) 1 ⊆ A.source ∧
        (∀ z : Sphere 2, ∀ t : ℝ,
          A (z,t) = chart b.1 (z,if b.2 then 1+t/2 else -1-t/2)) ∧
        (∀ z : Sphere 2, A (z,0) = T.boundarySphere b z) ∧
        (∀ z : Sphere 2, A (z,1) = chart b.1 (z,if b.2 then 3 / 2 else -(3 / 2))) ∧
        |(if b.2 then 3 / 2 else -(3 / 2) : ℝ)| ≤ 4 ∧
        A '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ W = range (T.boundarySphere b) ∧
        Disjoint (range (fun z : Sphere 2 => chart b.1
          (z,if b.2 then 3 / 2 else -(3 / 2)))) W ∧
        closure (interior (W ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1))) =
          W ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1) ∧
        frontier (W ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1)) =
          range (fun z : Sphere 2 => chart b.1 (z,if b.2 then 3 / 2 else -(3 / 2))) ∪
            ⋃ c : {c : T.Boundary // c ≠ b}, range (T.boundarySphere c.val) := by
  let W := ⋃ i, T.tube i '' {q : TubeDomain | q.2.val ∈ Icc (-1 : ℝ) 1}
  have hs (i : T.Index) : univ ×ˢ Icc (-1 : ℝ) 1 ⊆ (chart i).source := by
    intro q hq
    apply hsource i
    exact ⟨hq.1,by linarith [hq.2.1],by linarith [hq.2.2]⟩
  have hr : closure (interior W) = W :=
    T.closure_interior_iUnion_closedBand_of_openPartialHomeomorph
      (fun i => (chart i).toOpenPartialHomeomorph) hs (fun i q _ => hmap i q)
  have hf : frontier W = ⋃ c : T.Boundary, range (T.boundarySphere c) :=
    T.frontier_iUnion_closedBand_of_openPartialHomeomorph
      (fun i => (chart i).toOpenPartialHomeomorph) hs (fun i q _ => hmap i q)
  let A := outwardCutCylinder (chart b.1) b.2
  have hA := outwardCutCylinder_source (chart b.1) (hsource b.1) b.2
  have hl := T.outwardCutCylinder_lower (chart b.1) b (hmap b.1)
  have hu := outwardCutCylinder_upper (chart b.1) b.2
  have hinter := T.outwardCutCylinder_inter_closedBands (chart b.1) b (hmap b.1)
  have hout := T.outwardCutCylinder_upper_disjoint_closedBands (chart b.1) b (hmap b.1)
  obtain ⟨hreg,hfront⟩ := T.closed_band_cylinder_advance b W hr hf A hA hl hinter
  have hupper : (fun z : Sphere 2 => A (z,1)) =
      (fun z : Sphere 2 => chart b.1 (z,if b.2 then 3 / 2 else -(3 / 2))) := funext hu
  refine ⟨T.isCompact_iUnion_closedBand,hr,hf,A,hA,
    outwardCutCylinder_apply (chart b.1) b.2,hl,hu,?_,hinter,?_,hreg,?_⟩
  · cases b.2 <;> norm_num
  · change Disjoint (range (fun z : Sphere 2 => chart b.1
      (z,if b.2 then 3 / 2 else -(3 / 2)))) W
    rw [← hupper]
    exact hout
  · rw [hupper] at hfront
    exact hfront


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem
