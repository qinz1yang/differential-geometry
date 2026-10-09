import DifferentialGeometry.Topology.VanKampen.FreeFactors.ThinOverlapGroups
import DifferentialGeometry.Topology.VanKampen.TwoSidedCollarSeparation
import DifferentialGeometry.Topology.VanKampen.DisjointSimplyConnectedCover
import DifferentialGeometry.Topology.FundamentalGroup.SimplyConnectedComponents
import Mathlib.Analysis.Convex.Contractible
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
open scoped ContinuousMap
open DifferentialGeometry.Topology
open DifferentialGeometry.Topology.ThreeManifold
open DifferentialGeometry.Topology.VanKampen
namespace GC.Topology
universe u v

theorem puncturedReal_paths_thin (x y : ({0}ᶜ : Set ℝ)) :
    Subsingleton (Path.Homotopic.Quotient x y) := by
  let A : Bool → Set ℝ := fun b => if b then Ioi 0 else Iio 0
  have hA : ∀ b, IsOpen (A b) := by intro b; cases b <;> simp [A, isOpen_Iio, isOpen_Ioi]
  have hd : Pairwise fun i j => Disjoint (A i) (A j) := by
    intro i j hij
    cases i <;> cases j <;> simp_all [A, disjoint_left]
    all_goals exact fun _ h => h.le
  have hsc : ∀ b, SimplyConnectedSpace (A b) := by
    intro b; cases b
    · let : ContractibleSpace (Iio (0 : ℝ)) := (convex_Iio 0).contractibleSpace ⟨-1, by norm_num⟩
      exact inferInstanceAs (SimplyConnectedSpace (Iio (0 : ℝ)))
    · let : ContractibleSpace (Ioi (0 : ℝ)) := (convex_Ioi 0).contractibleSpace ⟨1, by norm_num⟩
      exact inferInstanceAs (SimplyConnectedSpace (Ioi (0 : ℝ)))
  have he : (⋃ b, A b) = ({0}ᶜ : Set ℝ) := by
    ext t
    simp only [mem_iUnion, Bool.exists_bool, A, Bool.false_eq_true, ↓reduceIte,
      mem_Iio, mem_Ioi, mem_compl_iff, mem_singleton_iff]
    exact ⟨fun h => h.elim ne_of_lt ne_of_gt, lt_or_gt_of_ne⟩
  exact subsingleton_pathHomotopicQuotient_of_homotopyEquiv
    (Homeomorph.setCongr he).symm.toHomotopyEquiv
    (subsingleton_pathHomotopicQuotient_iUnion_of_pairwise_disjoint A hA hd hsc) x y

variable {S : Type v} [TopologicalSpace S] {X : Type u} [TopologicalSpace X]
  {e : S → X} (c : TwoSidedCollar e)

theorem collar_overlap_image : c.complement ∩ c.range =
    c.toFun '' ((univ : Set S) ×ˢ ({0}ᶜ : Set ℝ)) := by
  ext x
  constructor
  · rintro ⟨hx, p, rfl⟩
    refine ⟨p, ⟨mem_univ _, ?_⟩, rfl⟩
    change p.2 ≠ 0
    intro ht
    apply hx
    exact ⟨p.1, (c.zero_eq p.1).symm.trans (congrArg c.toFun (Prod.ext rfl ht.symm))⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨c.toFun_mem_complement_of_ne_zero p.1 hp.2, ⟨p, rfl⟩⟩

noncomputable def collarOverlapHomeomorph :
    ↥(c.complement ∩ c.range) ≃ₜ S × ({0}ᶜ : Set ℝ) :=
  (Homeomorph.setCongr (collar_overlap_image c)).trans
    ((c.isOpenEmbedding_toFun.toIsEmbedding.homeomorphImage
      ((univ : Set S) ×ˢ ({0}ᶜ : Set ℝ))).symm.trans
      ((Homeomorph.Set.prod univ ({0}ᶜ : Set ℝ)).trans
        ((Homeomorph.Set.univ S).prodCongr (Homeomorph.refl _))))

theorem collar_overlap_paths_thin [SimplyConnectedSpace S]
    (x y : ↥(c.complement ∩ c.range)) :
    Subsingleton (Path.Homotopic.Quotient x y) :=
  subsingleton_pathHomotopicQuotient_of_homotopyEquiv
    (collarOverlapHomeomorph c).toHomotopyEquiv
    (subsingleton_pathHomotopicQuotient_prod (fun _ _ => inferInstance) puncturedReal_paths_thin) x y

theorem simplyConnectedSpace_collar_range [SimplyConnectedSpace S] :
    SimplyConnectedSpace c.range := by
  let e : S × ℝ ≃ₕ S :=
    ((ContinuousMap.HomotopyEquiv.refl S).prodCongr
      (ContractibleSpace.hequiv_unit ℝ).some).trans
        (Homeomorph.prodUnique S Unit).toHomotopyEquiv
  exact (c.homeomorphRange.symm.toHomotopyEquiv.trans e).simplyConnectedSpace

theorem isFreeFactor_collar_complement [CompactSpace S] [SimplyConnectedSpace S]
    [T2Space X] [PathConnectedSpace c.complement] (x : c.complement) :
    GC.Group.IsFreeFactor (FundamentalGroup c.complement x)
      (FundamentalGroup X x.val) := by
  let : SimplyConnectedSpace c.range := simplyConnectedSpace_collar_range c
  let s : S := Classical.choice inferInstance
  let z : ↥(c.complement ∩ c.range) :=
    ⟨c.toFun (s, -1), c.toFun_mem_complement_of_ne_zero s (by norm_num), ⟨(s, -1), rfl⟩⟩
  have h := isFreeFactor_fundamentalGroup_thinOverlap c.complement c.range z
    c.isOpen_complement c.isOpen_range c.complement_union_range (collar_overlap_paths_thin c)
  let p : Path (coreBase c.complement c.range z) x := PathConnectedSpace.somePath _ _
  exact h.congr (FundamentalGroup.fundamentalGroupMulEquivOfPath p)
    (FundamentalGroup.fundamentalGroupMulEquivOfPath (p.map continuous_subtype_val))

end GC.Topology
