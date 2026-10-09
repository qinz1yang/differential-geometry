import DifferentialGeometry.Topology.Manifold.SmoothOpenCover

/-!+# Installing a quotient atlas from actual smooth open patches

Actual local coordinates into an arbitrary target model install a smooth atlas on the covered
space. The original patch parametrizations and their inverses are smooth in that atlas. The
target model may have boundary, so this applies to both half-space and closed quotient atlases.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Manifold
open scoped ContDiff

namespace GC.Seifert

variable {ι E H Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace Q]
  {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
  {K : ι → Type*} [∀ i, TopologicalSpace (K i)]
  {M : ι → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace (K i) (M i)]
  {I : ∀ i, ModelWithCorners ℝ (F i) (K i)}

theorem exists_carrierSurgeryAtlas_of_openCover (J : ModelWithCorners ℝ E H)
    (e : ∀ i, OpenPartialHomeomorph (M i) Q)
    (hcover : ∀ q : Q, ∃ i, q ∈ (e i).target)
    (hcompat : ∀ i j, ContMDiffOn (I i) (I j) ∞
      ((e i).trans (e j).symm) ((e i).trans (e j).symm).source)
    (hcoord : ∀ i x, x ∈ (e i).source →
      ∃ d : PartialDiffeomorph (I i) J (M i) H ∞, x ∈ d.source) :
    ∃ C : ChartedSpace H Q, letI := C
      IsManifold J ∞ Q ∧ ∀ i,
        ContMDiffOn (I i) J ∞ (e i) (e i).source ∧
        ContMDiffOn J (I i) ∞ (e i).symm (e i).target := by
  classical
  let A := Σ i, (e i).source
  let p (v : A) := (hcoord v.1 v.2.1 v.2.2).choose
  have hp (v : A) : v.2.1 ∈ (p v).source :=
    (hcoord v.1 v.2.1 v.2.2).choose_spec
  let c (v : A) := (e v.1).symm.trans (p v).toOpenPartialHomeomorph
  have hc : ∀ q : Q, ∃ v, q ∈ (c v).source := by
    intro q
    obtain ⟨i, hq⟩ := hcover q
    let v : A := ⟨i, (e i).symm q, (e i).map_target hq⟩
    exact ⟨v, hq, hp v⟩
  let C : ChartedSpace H Q :=
    { atlas := range c
      chartAt q := c (hc q).choose
      mem_chart_source q := (hc q).choose_spec
      chart_mem_atlas q := mem_range_self ((hc q).choose) }
  let := C
  have hman : IsManifold J ∞ Q := by
    refine { compatible := ?_ }
    rintro f g ⟨v, rfl⟩ ⟨w, rfl⟩
    let t : PartialDiffeomorph (I v.1) (I w.1) (M v.1) (M w.1) ∞ :=
      { toPartialEquiv := ((e v.1).trans (e w.1).symm).toPartialEquiv
        open_source := ((e v.1).trans (e w.1).symm).open_source
        open_target := ((e v.1).trans (e w.1).symm).open_target
        contMDiffOn_toFun := hcompat v.1 w.1
        contMDiffOn_invFun := hcompat w.1 v.1 }
    let d := ((p v).symm.trans t).trans (p w)
    have hd : d.toOpenPartialHomeomorph =
        (((p v).toOpenPartialHomeomorph.symm.trans
          ((e v.1).trans (e w.1).symm)).trans (p w).toOpenPartialHomeomorph) := rfl
    have hr : OpenPartialHomeomorph.refl H ∈ IsManifold.maximalAtlas J ∞ H :=
      IsManifold.subset_maximalAtlas (chartedSpaceSelf_atlas.mpr rfl)
    have hh := symm_trans_trans_mem_contDiffGroupoid_of_contMDiffOn hr hr
      d.contMDiffOn d.symm.contMDiffOn
    change (OpenPartialHomeomorph.refl H).symm.trans
      (d.toOpenPartialHomeomorph.trans (OpenPartialHomeomorph.refl H)) ∈
        contDiffGroupoid ∞ J at hh
    rw [hd] at hh
    simpa only [OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_trans,
      OpenPartialHomeomorph.trans_refl, c,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.trans_assoc] using hh
  let := hman
  have hmem (v : A) : c v ∈ IsManifold.maximalAtlas J ∞ Q :=
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

end GC.Seifert
