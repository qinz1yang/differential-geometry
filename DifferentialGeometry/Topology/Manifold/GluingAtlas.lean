import Mathlib.Topology.Gluing
import Mathlib.Topology.OpenPartialHomeomorph.Composition
import DifferentialGeometry.Topology.Attachment.TransitionGluing
import DifferentialGeometry.Topology.Manifold.SmoothOpenCover

section

set_option autoImplicit false

noncomputable section

namespace TopCat.GlueData

universe u
variable (D : TopCat.GlueData.{u})

theorem gluing_transition_source (i j : D.J)
    [Nonempty (D.U i)] [Nonempty (D.U j)] :
    let e := (D.ι_isOpenEmbedding i).toOpenPartialHomeomorph (D.toGlueData.ι i)
    let f := (D.ι_isOpenEmbedding j).toOpenPartialHomeomorph (D.toGlueData.ι j)
    (e.trans f.symm).source = Set.range (D.f i j) := by
  dsimp only
  rw [OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.symm_source,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target,
    Set.univ_inter,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply]
  exact D.preimage_range j i

theorem gluing_transition_apply (i j : D.J)
    [Nonempty (D.U i)] [Nonempty (D.U j)] (x : D.V (i, j)) :
    let e := (D.ι_isOpenEmbedding i).toOpenPartialHomeomorph (D.toGlueData.ι i)
    let f := (D.ι_isOpenEmbedding j).toOpenPartialHomeomorph (D.toGlueData.ι j)
    (e.trans f.symm) (D.f i j x) = D.f j i (D.t i j x) := by
  dsimp only
  rw [OpenPartialHomeomorph.trans_apply,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply,
    ← D.glue_condition_apply i j x]
  exact (D.ι_isOpenEmbedding j).toOpenPartialHomeomorph_left_inv
    (D.toGlueData.ι j)

end TopCat.GlueData

end

end

section

noncomputable section
open scoped ContDiff
namespace TopCat.GlueData
open TopologicalSpace Topology
universe u
variable {ι E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Opens E) [Nonempty U] (near : ι → ι → Bool)
    (J : {a : ι × ι // near a.1 a.2 = true} → E → E)
    (hJ : ∀ a, ContinuousOn (J a) U)
    (hrefl : ∀ i, near i i = true)
    (hsymm : ∀ i j, near i j = true → near j i = true)
    (hself : ∀ i x, x ∈ U → J ⟨(i, i), hrefl i⟩ x = x)
    (hinv : ∀ i j (h : near i j = true) x, x ∈ U → J ⟨(i, j), h⟩ x ∈ U →
      J ⟨(j, i), hsymm i j h⟩ (J ⟨(i, j), h⟩ x) = x)
    (htrans : ∀ i j k (hij : near i j = true) (hjk : near j k = true) x,
      x ∈ U → J ⟨(i, j), hij⟩ x ∈ U → J ⟨(j, k), hjk⟩ (J ⟨(i, j), hij⟩ x) ∈ U →
      ∃ hik : near i k = true,
        J ⟨(i, k), hik⟩ x = J ⟨(j, k), hjk⟩ (J ⟨(i, j), hij⟩ x))

local notation "D" => ofTransitionMaps (U : Set E) U.isOpen near J hJ hrefl hsymm hself hinv htrans

private def gluingInclusion (i : ι) : OpenPartialHomeomorph U (D).toGlueData.glued :=
  ((D).ι_isOpenEmbedding i).toOpenPartialHomeomorph ((D).toGlueData.ι i)

omit [NormedSpace ℝ E] in
private theorem gluingInclusion_cover :
    ∀ q : (D).toGlueData.glued, ∃ i, q ∈
      (gluingInclusion U near J hJ hrefl hsymm hself hinv htrans i).target := by
  intro q
  obtain ⟨i, x, hx⟩ := (D).ι_jointly_surjective q
  exact ⟨i, ⟨x, Set.mem_univ _, hx⟩⟩

omit [Nonempty U] in
private theorem contMDiffOn_restrict_open {F : E → E}
    (hF : ContDiffOn ℝ ∞ F U) :
    ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) ∞ (fun v : U => F v) := by
  intro v
  apply contMDiffAt_subtype_iff.mpr
  exact (hF.contDiffAt (U.isOpen.mem_nhds v.property)).contMDiffAt

private theorem gluingInclusion_transition_contMDiff
    (hsmooth : ∀ a, ContDiffOn ℝ ∞ (J a) U) (i j : ι) :
    ContMDiffOn (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) ∞
      ((gluingInclusion U near J hJ hrefl hsymm hself hinv htrans i).trans
        (gluingInclusion U near J hJ hrefl hsymm hself hinv htrans j).symm)
      ((gluingInclusion U near J hJ hrefl hsymm hself hinv htrans i).trans
        (gluingInclusion U near J hJ hrefl hsymm hself hinv htrans j).symm).source := by
  intro x hx
  rw [← ContMDiffWithinAt.subtypeVal_comp_iff U]
  let : Nonempty ((D).U i) := ⟨(Classical.choice (show Nonempty U from inferInstance))⟩
  let : Nonempty ((D).U j) := ⟨(Classical.choice (show Nonempty U from inferInstance))⟩
  have hsource := (D).gluing_transition_source i j
  change ((gluingInclusion U near J hJ hrefl hsymm hself hinv htrans i).trans
    (gluingInclusion U near J hJ hrefl hsymm hself hinv htrans j).symm).source =
      Set.range ((D).f i j) at hsource
  rw [hsource] at hx
  obtain ⟨z, rfl⟩ := hx
  change (transitionOverlap (U : Set E) U.isOpen near J hJ i j) at z
  let hij : near i j = true := z.property.choose
  have hcomp := contMDiffOn_restrict_open U (hsmooth ⟨(i, j), hij⟩)
    (show U from z.val)
  apply hcomp.contMDiffWithinAt.congr
  · intro y hy
    rw [hsource] at hy
    obtain ⟨w, rfl⟩ := hy
    have heq := (D).gluing_transition_apply i j w
    exact congrArg Subtype.val heq
  · exact congrArg Subtype.val ((D).gluing_transition_apply i j z)

theorem exists_smooth_atlas_ofTransitionMaps
    (hsmooth : ∀ a, ContDiffOn ℝ ∞ (J a) U) :
    ∃ C : ChartedSpace E (D).toGlueData.glued, letI := C
      IsManifold (modelWithCornersSelf ℝ E) ∞ (D).toGlueData.glued ∧
      ∀ i : ι, IsLocalDiffeomorph (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) ∞
        (fun x : U => (D).toGlueData.ι i x) := by
  let e := gluingInclusion U near J hJ hrefl hsymm hself hinv htrans
  have hcover := gluingInclusion_cover U near J hJ hrefl hsymm hself hinv htrans
  have hinterior : ∀ i, (e i).source ⊆ (modelWithCornersSelf ℝ E).interior U := by
    intro i x hx
    exact BoundarylessManifold.isInteriorPoint
  have hcompat := gluingInclusion_transition_contMDiff U near J hJ hrefl hsymm hself hinv htrans hsmooth
  obtain ⟨C, hC, he⟩ := DifferentialGeometry.Topology.Manifold.exists_smoothAtlas_of_openCover
    e hcover hinterior (fun _ => ContinuousLinearEquiv.refl ℝ E) hcompat
  let := C
  let := hC
  refine ⟨C, hC, ?_⟩
  intro i x
  let p : PartialDiffeomorph (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E)
      U (D).toGlueData.glued ∞ :=
    { toPartialEquiv := (e i).toPartialEquiv
      open_source := (e i).open_source
      open_target := (e i).open_target
      contMDiffOn_toFun := (he i).1
      contMDiffOn_invFun := (he i).2 }
  exact ⟨p, Set.mem_univ x, fun _ _ => rfl⟩

end TopCat.GlueData

end

end
