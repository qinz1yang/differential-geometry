import Mathlib.Geometry.Manifold.ContMDiff.Atlas

open Set
open scoped Manifold ContDiff

variable {k E H N P : Type*} [NontriviallyNormedField k]
  [NormedAddCommGroup E] [NormedSpace k E] [TopologicalSpace H]
  {I : ModelWithCorners k E H} {n : ℕ∞ω}
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I n N]
  [TopologicalSpace P] [ChartedSpace N P]

theorem isManifold_of_contMDiffOn
    (h : ∀ e e' : OpenPartialHomeomorph P N, e ∈ atlas N P → e' ∈ atlas N P →
      ContMDiffOn I I n (e.symm ≫ₕ e') (e.symm ≫ₕ e').source) :
    letI := ChartedSpace.comp H N P
    IsManifold I n P := by
  have ht (e e' : OpenPartialHomeomorph P N) (he : e ∈ atlas N P)
      (he' : e' ∈ atlas N P) :
      ChartedSpace.LiftPropOn (contDiffGroupoid n I).IsLocalStructomorphWithinAt
        (e.symm ≫ₕ e') (e.symm ≫ₕ e').source := by
    rw [isLocalStructomorphOn_contDiffGroupoid_iff]
    refine ⟨h e e' he he', ?_⟩
    rw [← OpenPartialHomeomorph.symm_source]
    simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm] using h e' e he' he
  let := ChartedSpace.comp H N P
  refine { compatible := ?_ }
  rintro _ _ ⟨e, he, f, hf, rfl⟩ ⟨e', he', f', hf', rfl⟩
  apply (contDiffGroupoid n I).locality
  intro x hx
  simp only [mfld_simps] at hx
  have hxs : x ∈ f.symm ⁻¹' (e.symm ≫ₕ e').source := by simp only [hx, mfld_simps]
  have hxs' : x ∈ f.target ∩
      f.symm ⁻¹' ((e.symm ≫ₕ e').source ∩ e.symm ≫ₕ e' ⁻¹' f'.source) := by
    simp only [hx, mfld_simps]
  obtain ⟨φ, hφG, hφ, hφ_dom⟩ := StructureGroupoid.LocalInvariantProp.liftPropOn_indep_chart
    (StructureGroupoid.isLocalStructomorphWithinAt_localInvariantProp (contDiffGroupoid n I))
    ((contDiffGroupoid n I).subset_maximalAtlas hf)
    ((contDiffGroupoid n I).subset_maximalAtlas hf') (ht e e' he he') hxs' hxs
  simp_rw [← OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.trans_assoc] at hφ
  simp_rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.trans_assoc]
  have hs : IsOpen (f.symm ≫ₕ e.symm ≫ₕ e' ≫ₕ f').source :=
    (f.symm ≫ₕ e.symm ≫ₕ e' ≫ₕ f').open_source
  refine ⟨_, hs.inter φ.open_source, ?_, ?_⟩
  · simp only [hx, hφ_dom, mfld_simps]
  · refine (contDiffGroupoid n I).mem_of_eqOnSource
      (closedUnderRestriction' hφG hs) ?_
    rw [OpenPartialHomeomorph.restr_source_inter]
    refine OpenPartialHomeomorph.Set.EqOn.restr_eqOn_source (hφ.mono ?_)
    mfld_set_tac

namespace ChartedSpace

omit [IsManifold I n N] in
theorem contMDiffOn_of_mem_atlas_comp {e : OpenPartialHomeomorph P N} (he : e ∈ atlas N P)
    (hP : letI := ChartedSpace.comp H N P; IsManifold I n P) :
    letI := ChartedSpace.comp H N P
    ContMDiffOn I I n e e.source := by
  let := ChartedSpace.comp H N P
  let : IsManifold I n P := hP
  intro p hp
  rw [contMDiffWithinAt_iff_target]
  refine ⟨e.continuousOn.continuousWithinAt hp, ?_⟩
  have hec : e ≫ₕ chartAt H (e p) ∈ atlas H P :=
    ⟨e, he, chartAt H (e p), chart_mem_atlas H (e p), rfl⟩
  have hc : ContMDiffAt I I n (e ≫ₕ chartAt H (e p)) p :=
    contMDiffAt_of_mem_maximalAtlas
      ((contDiffGroupoid n I).subset_maximalAtlas hec)
      ⟨hp, mem_chart_source H (e p)⟩
  exact (ModelWithCorners.contMDiff I).contMDiffAt.comp_contMDiffWithinAt p
    hc.contMDiffWithinAt

theorem contMDiffOn_symm_of_mem_atlas_comp {e : OpenPartialHomeomorph P N}
    (he : e ∈ atlas N P)
    (hP : letI := ChartedSpace.comp H N P; IsManifold I n P) :
    letI := ChartedSpace.comp H N P
    ContMDiffOn I I n e.symm e.target := by
  let := ChartedSpace.comp H N P
  let : IsManifold I n P := hP
  intro y hy
  let f := chartAt H y
  have hec : e ≫ₕ f ∈ atlas H P := ⟨e, he, f, chart_mem_atlas H y, rfl⟩
  have ht : f y ∈ (e ≫ₕ f).target := by
    change f y ∈ f.target ∩ f.symm ⁻¹' e.target
    refine ⟨f.map_source (mem_chart_source H y), ?_⟩
    change f.symm (f y) ∈ e.target
    rwa [f.left_inv (mem_chart_source H y)]
  have hd : ContMDiffAt I I n (e ≫ₕ f).symm (f y) :=
    contMDiffAt_symm_of_mem_maximalAtlas ((contDiffGroupoid n I).subset_maximalAtlas hec) ht
  have hf : ContMDiffAt I I n f y :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas y)
      (mem_chart_source H y)
  have hc := hd.comp y hf
  have hg : ContMDiffAt I I n e.symm y := by
    apply hc.congr_of_eventuallyEq
    filter_upwards [f.open_source.mem_nhds (mem_chart_source H y)] with z hz
    change e.symm z = e.symm (f.symm (f z))
    rw [f.left_inv hz]
  exact hg.contMDiffWithinAt

end ChartedSpace
