import DifferentialGeometry.Topology.Manifold.OpenCoverAtlas
import DifferentialGeometry.Topology.Manifold.InteriorCoordinates
import Mathlib.Geometry.Manifold.LocalDiffeomorph

noncomputable section
open Set Filter Topology Manifold
open scoped ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {ι E Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace Q]
  {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
  {H : ι → Type*} [∀ i, TopologicalSpace (H i)]
  {M : ι → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace (H i) (M i)]
  {I : ∀ i, ModelWithCorners ℝ (F i) (H i)} [∀ i, IsManifold (I i) ∞ (M i)]

set_option backward.isDefEq.respectTransparency false in
theorem exists_smoothAtlas_of_openCover
    (e : ∀ i, OpenPartialHomeomorph (M i) Q)
    (hcover : ∀ q : Q, ∃ i, q ∈ (e i).target)
    (hinterior : ∀ i, (e i).source ⊆ (I i).interior (M i))
    (L : ∀ i, F i ≃L[ℝ] E)
    (hcompat : ∀ i j, ContMDiffOn (I i) (I j) ∞
      ((e i).trans (e j).symm) ((e i).trans (e j).symm).source) :
    ∃ C : ChartedSpace E Q, letI := C
      IsManifold 𝓘(ℝ, E) ∞ Q ∧ ∀ i,
        ContMDiffOn (I i) 𝓘(ℝ, E) ∞ (e i) (e i).source ∧
        ContMDiffOn 𝓘(ℝ, E) (I i) ∞ (e i).symm (e i).target := by
  classical
  let A := Σ i, (e i).source
  have hcoord (v : A) : ∃ d : PartialDiffeomorph (I v.1) 𝓘(ℝ, E) (M v.1) E ∞,
      v.2.1 ∈ d.source := by
    obtain ⟨p, hp, _, _, _⟩ := exists_interior_coordinates (hinterior v.1 v.2.2)
    let d := p.trans (L v.1).toDiffeomorph.toPartialDiffeomorph
    exact ⟨d, hp, mem_univ _⟩
  let p (v : A) := (hcoord v).choose
  have hp (v : A) : v.2.1 ∈ (p v).source := (hcoord v).choose_spec
  let c (v : A) := (e v.1).symm.trans (p v).toOpenPartialHomeomorph
  have hc : ∀ q : Q, ∃ v, q ∈ (c v).source := by
    intro q
    obtain ⟨i, hq⟩ := hcover q
    let v : A := ⟨i, (e i).symm q, (e i).map_target hq⟩
    exact ⟨v, hq, hp v⟩
  let C := chartedSpaceOfOpenCover c hc
  have hman : IsManifold 𝓘(ℝ, E) ∞ Q := by
    apply isManifold_chartedSpaceOfOpenCover c hc
    intro v w
    let t : PartialDiffeomorph (I v.1) (I w.1) (M v.1) (M w.1) ∞ :=
      { toPartialEquiv := ((e v.1).trans (e w.1).symm).toPartialEquiv
        open_source := ((e v.1).trans (e w.1).symm).open_source
        open_target := ((e v.1).trans (e w.1).symm).open_target
        contMDiffOn_toFun := hcompat v.1 w.1
        contMDiffOn_invFun := hcompat w.1 v.1 }
    have hh := (((p v).symm.trans t).trans (p w)).contMDiffOn.contDiffOn
    change ContDiffOn ℝ ∞
      (((p v).toOpenPartialHomeomorph.symm.trans ((e v.1).trans (e w.1).symm)).trans
        (p w).toOpenPartialHomeomorph)
      (((p v).toOpenPartialHomeomorph.symm.trans ((e v.1).trans (e w.1).symm)).trans
        (p w).toOpenPartialHomeomorph).source at hh
    simpa only [c, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.trans_assoc] using hh
  let := hman
  have hmem (v : A) : c v ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ Q :=
    IsManifold.subset_maximalAtlas ⟨v, rfl⟩
  refine ⟨C, hman, ?_⟩
  intro i
  constructor
  · intro x hx
    let v : A := ⟨i, x, hx⟩
    have hcx : e i x ∈ (c v).source := by
      refine ⟨(e i).map_source hx, ?_⟩
      change (e i).symm (e i x) ∈ (p v).source
      rw [(e i).left_inv hx]
      exact hp v
    have hct : p v x ∈ (c v).target := by
      have hh := (c v).map_source hcx
      change p v ((e i).symm (e i x)) ∈ (c v).target at hh
      rwa [(e i).left_inv hx] at hh
    have hs := (contMDiffAt_symm_of_mem_maximalAtlas (hmem v) hct).comp x
      ((p v).contMDiffOn.contMDiffAt ((p v).open_source.mem_nhds (hp v)))
    apply (hs.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [(p v).open_source.mem_nhds (hp v)] with y hy
    change e i y = e i ((p v).symm (p v y))
    exact congrArg (e i) ((p v).left_inv hy).symm
  · intro q hq
    let v : A := ⟨i, (e i).symm q, (e i).map_target hq⟩
    have hcs : q ∈ (c v).source := ⟨hq, hp v⟩
    have hpt : c v q ∈ (p v).target := (p v).map_source (hp v)
    have hs := ((p v).symm.contMDiffOn.contMDiffAt
      ((p v).open_target.mem_nhds hpt)).comp q
      (contMDiffAt_of_mem_maximalAtlas (hmem v) hcs)
    apply (hs.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [(c v).open_source.mem_nhds hcs] with y hy
    change (e i).symm y = (p v).symm (p v ((e i).symm y))
    exact ((p v).left_inv hy.2).symm

end DifferentialGeometry.Topology.Manifold
