import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Topology.Covering.Basic
import Mathlib.Geometry.Manifold.LocalDiffeomorph



noncomputable section
open Set Function Manifold
open scoped Manifold ContDiff
namespace DifferentialGeometry.Topology.Manifold

variable {E H M C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace C] {p : C → M} (hp : IsLocalHomeomorph p)


def coveringChart (x : C) : OpenPartialHomeomorph C H :=
  (hp.localInverseAt x).symm.trans (chartAt H (p x))


theorem coveringChart_apply (x y : C) : coveringChart (H := H) hp x y = chartAt H (p x) (p y) := by
  simp [coveringChart, OpenPartialHomeomorph.trans_apply]


theorem mem_coveringChart_source (x : C) : x ∈ (coveringChart (H := H) hp x).source := by
  simp [coveringChart]


theorem coveringChart_symm_projects (x : C) {y : H} (hy : y ∈ (coveringChart (H := H) hp x).target) :
    p ((coveringChart (H := H) hp x).symm y) = (chartAt H (p x)).symm y := by
  change p (hp.localInverseAt x ((chartAt H (p x)).symm y)) = _
  apply hp.apply_localInverseAt_of_mem
  exact hy.2


theorem coveringChart_transition_source (a b : C) :
    ((coveringChart (H := H) hp a).symm.trans (coveringChart (H := H) hp b)).source ⊆
      ((chartAt H (p a)).symm.trans (chartAt H (p b))).source := by
  intro y hy
  have ha : y ∈ (coveringChart (H := H) hp a).target := hy.1
  have hb : p ((coveringChart (H := H) hp a).symm y) ∈ (chartAt H (p b)).source := by
    have h := hy.2.2
    simpa only [OpenPartialHomeomorph.symm_symm, IsLocalHomeomorph.localInverseAt_symm, Set.mem_preimage] using h
  refine ⟨ha.1, ?_⟩
  change (chartAt H (p a)).symm y ∈ (chartAt H (p b)).source
  rw [← coveringChart_symm_projects (H := H) hp a ha]
  exact hb


theorem coveringChart_transition_eqOn (a b : C) :
    EqOn ((chartAt H (p a)).symm.trans (chartAt H (p b)))
      ((coveringChart (H := H) hp a).symm.trans (coveringChart (H := H) hp b))
      ((coveringChart (H := H) hp a).symm.trans (coveringChart (H := H) hp b)).source := by
  intro y hy
  change chartAt H (p b) ((chartAt H (p a)).symm y) =
    coveringChart (H := H) hp b ((coveringChart (H := H) hp a).symm y)
  rw [coveringChart_apply, coveringChart_symm_projects (H := H) hp a hy.1]


@[instance_reducible]
def coveringChartedSpace : ChartedSpace H C where
  atlas := range (coveringChart (H := H) hp)
  chartAt := coveringChart (H := H) hp
  mem_chart_source := mem_coveringChart_source (H := H) hp
  chart_mem_atlas x := mem_range_self x

variable (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]


theorem covering_isManifold :
    @IsManifold ℝ _ E _ _ H _ I ∞ C _ (coveringChartedSpace (H := H) hp) := by
  let := coveringChartedSpace (H := H) hp
  refine { compatible := ?_ }
  rintro e e' ⟨a, rfl⟩ ⟨b, rfl⟩
  have hbase := StructureGroupoid.compatible (contDiffGroupoid ∞ I)
    (chart_mem_atlas H (p a)) (chart_mem_atlas H (p b))
  have h := StructureGroupoid.restr_mem_of_eqOn hbase
    (((coveringChart (H := H) hp a).symm.trans (coveringChart (H := H) hp b)).open_source)
    (coveringChart_transition_eqOn (H := H) hp a b)
    (inter_self _ ▸ coveringChart_transition_source (H := H) hp a b)
  rwa [OpenPartialHomeomorph.restr_eq_of_source_subset
    (((coveringChart (H := H) hp a).symm.trans (coveringChart (H := H) hp b)).open_source.interior_eq ▸
      (Subset.refl _))] at h


theorem covering_projection_contMDiff :
    letI := coveringChartedSpace (H := H) hp
    ContMDiff I I ∞ p := by
  let := coveringChartedSpace (H := H) hp
  let := covering_isManifold hp I
  intro z
  have hc : ContMDiffAt I I ∞ (coveringChart (H := H) hp z) z :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas z) (mem_chart_source H z)
  have hb : ContMDiffAt I I ∞ (chartAt H (p z)).symm (coveringChart hp z z) := by
    rw [coveringChart_apply]
    exact contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (p z))
      ((chartAt H (p z)).map_source (mem_chart_source H (p z)))
  apply (hb.comp z hc).congr_of_eventuallyEq
  filter_upwards [((coveringChart (H := H) hp z).open_source.mem_nhds
    (mem_coveringChart_source hp z))] with w hw
  change p w = (chartAt H (p z)).symm (coveringChart hp z w)
  rw [coveringChart_apply]
  exact ((chartAt H (p z)).left_inv (by
    simpa only [OpenPartialHomeomorph.symm_symm, IsLocalHomeomorph.localInverseAt_symm,
      Set.mem_preimage] using hw.2)).symm


theorem covering_lift_contMDiffAt {A : Type*} [TopologicalSpace A] [ChartedSpace H A]
    {f : A → C} {x : A} (hf : ContinuousAt f x)
    (hpf : ContMDiffAt I I ∞ (p ∘ f) x) :
    letI := coveringChartedSpace (H := H) hp
    ContMDiffAt I I ∞ f x := by
  let := coveringChartedSpace (H := H) hp
  let := covering_isManifold hp I
  have hb : ContMDiffAt I I ∞ (chartAt H (p (f x))) (p (f x)) :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas _) (mem_chart_source H _)
  have hc : ContMDiffAt I I ∞ (coveringChart (H := H) hp (f x)).symm
      (chartAt H (p (f x)) (p (f x))) := by
    rw [← coveringChart_apply (H := H) hp (f x) (f x)]
    exact contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (f x))
      ((coveringChart hp (f x)).map_source (mem_coveringChart_source hp (f x)))
  apply (hc.comp x (hb.comp x hpf)).congr_of_eventuallyEq
  filter_upwards [hf ((coveringChart (H := H) hp (f x)).open_source.mem_nhds
    (mem_coveringChart_source hp (f x)))] with y hy
  change f y = (coveringChart hp (f x)).symm (chartAt H (p (f x)) (p (f y)))
  rw [← coveringChart_apply (H := H) hp (f x) (f y)]
  exact ((coveringChart hp (f x)).left_inv hy).symm


theorem covering_sheetInverse_contMDiff (e : OpenPartialHomeomorph C M)
    (he : EqOn p e e.source) :
    letI := coveringChartedSpace (H := H) hp
    ContMDiffOn I I ∞ e.symm e.target := by
  let := coveringChartedSpace (H := H) hp
  intro y hy
  apply ContMDiffAt.contMDiffWithinAt
  apply covering_lift_contMDiffAt hp I (e.symm.continuousAt hy)
  apply contMDiffAt_id.congr_of_eventuallyEq
  filter_upwards [e.open_target.mem_nhds hy] with z hz
  change p (e.symm z) = z
  rw [he (e.map_target hz), e.right_inv hz]


theorem covering_section_contMDiff (s : C(M, C)) (hs : Function.RightInverse s p) :
    letI := coveringChartedSpace (H := H) hp
    ContMDiff I I ∞ s := by
  let := coveringChartedSpace (H := H) hp
  intro x
  apply covering_lift_contMDiffAt hp I s.continuous.continuousAt
  exact contMDiffAt_id.congr_of_eventuallyEq (Filter.Eventually.of_forall hs)


theorem covering_section_locally_inverse (s : C(M, C)) (hs : Function.RightInverse s p) (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ U ⊆ (hp.localInverseAt (s x)).source ∧
      EqOn s (hp.localInverseAt (s x)) U := by
  let e := hp.localInverseAt (s x)
  refine ⟨s ⁻¹' e.target, e.open_target.preimage s.continuous,
    hp.self_mem_localInverseAt_target, ?_, ?_⟩
  · intro y hy
    have h := e.map_target hy
    simpa only [e, IsLocalHomeomorph.localInverseAt_symm, hs y] using h
  · intro y hy
    have h := e.right_inv hy
    simpa only [e, IsLocalHomeomorph.localInverseAt_symm, hs y] using h.symm

theorem covering_projection_isLocalDiffeomorph :
    letI := coveringChartedSpace (H := H) hp
    IsLocalDiffeomorph I I ∞ p := by
  let := coveringChartedSpace (H := H) hp
  intro x
  let e := (hp.localInverseAt x).symm
  have he : (e : C → M) = p := hp.localInverseAt_symm x
  refine ⟨{
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := by
      change ContMDiffOn I I ∞ (e : C → M) e.source
      rw [he]
      exact (covering_projection_contMDiff hp I).contMDiffOn
    contMDiffOn_invFun := covering_sheetInverse_contMDiff hp I e
      (fun y _ => (congrFun he y).symm)
  }, ?_, fun y _ => (congrFun he y).symm⟩
  exact hp.self_mem_localInverseAt_target

end DifferentialGeometry.Topology.Manifold
