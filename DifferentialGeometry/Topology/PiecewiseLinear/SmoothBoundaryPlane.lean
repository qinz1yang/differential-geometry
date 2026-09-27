/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Manifold.EuclideanBoundaryCoordinates
import DifferentialGeometry.Topology.Manifold.PartialChartEmbedding
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Atlas
import DifferentialGeometry.Topology.InvarianceOfDomainManifold
import Mathlib.Analysis.InnerProductSpace.Calculus

open Set Metric Topology Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_isSmoothEmbedding_plane_boundary_subset
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] {O : Set M} (hO : IsOpen O) {x : M}
    (hx : x ∈ (𝓡∂ 3).boundary M) (hxO : x ∈ O) :
    ∃ f : EuclideanSpace ℝ (Fin 2) → M, IsSmoothEmbedding (𝓡 2) (𝓡∂ 3) ∞ f ∧
      range f ⊆ (𝓡∂ 3).boundary M ∧ range f ⊆ O := by
  classical
  set ψ := chartAt (EuclideanHalfSpace 3) x with hψdef
  have hbd : ∀ y ∈ ψ.source, y ∈ (𝓡∂ 3).boundary M ↔ (ψ y).val 0 = 0 := by
    intro y hy
    have h := isBoundaryPoint_iff_any_chart_real (𝓡∂ 3) hy
    rw [frontier_range_modelWithCornersEuclideanHalfSpace] at h
    exact h.trans ⟨fun h' => h'.symm, fun h' => h'.symm⟩
  have hxs : x ∈ ψ.source := mem_chart_source _ x
  set c : EuclideanSpace ℝ (Fin 3) := (ψ x).val with hcdef
  have hc0 : c 0 = 0 := (hbd x hxs).mp hx
  set c' : EuclideanSpace ℝ (Fin 2) := ((normalFirstEquiv 2).symm c).1 with hc'def
  have hcc : normalFirstEquiv 2 (c', 0) = c := by
    have h2 : ((normalFirstEquiv 2).symm c).2 = 0 := by
      have h := normalFirstEquiv_zero 2 ((normalFirstEquiv 2).symm c)
      rw [ContinuousLinearEquiv.apply_symm_apply] at h
      rw [← h]
      exact hc0
    have hp : (c', (0 : ℝ)) = (normalFirstEquiv 2).symm c := Prod.ext rfl h2.symm
    rw [hp, ContinuousLinearEquiv.apply_symm_apply]
  let ι : EuclideanSpace ℝ (Fin 2) → EuclideanHalfSpace 3 := fun w =>
    ⟨normalFirstEquiv 2 (w, 0), by rw [normalFirstEquiv_zero]⟩
  have hιc : Continuous ι :=
    ((normalFirstEquiv 2).continuous.comp (continuous_id.prodMk continuous_const)).subtype_mk _
  have hιemb : IsEmbedding ι := by
    refine Function.LeftInverse.isEmbedding (f := fun y : EuclideanHalfSpace 3 =>
      ((normalFirstEquiv 2).symm y.val).1) (fun w => ?_)
      (continuous_fst.comp ((normalFirstEquiv 2).symm.continuous.comp continuous_subtype_val))
      hιc
    change ((normalFirstEquiv 2).symm (normalFirstEquiv 2 (w, 0))).1 = w
    rw [ContinuousLinearEquiv.symm_apply_apply]
  have hιx : ι c' = ψ x := Subtype.ext hcc
  let V : Set (EuclideanHalfSpace 3) := ψ.target ∩ ψ.symm ⁻¹' O
  have hV : IsOpen V := ψ.isOpen_inter_preimage_symm hO
  have hxV : ψ x ∈ V := ⟨ψ.map_source hxs, by
    change ψ.symm (ψ x) ∈ O
    rw [ψ.left_inv hxs]
    exact hxO⟩
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.mp (hV.preimage hιc) c' (by
    change ι c' ∈ V
    rw [hιx]
    exact hxV)
  let A : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2) :=
    (Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addLeft c')
  have hAs : ∀ y, A.symm y = r⁻¹ • (-c' + y) := by
    intro y
    rw [Homeomorph.symm_trans_apply, Homeomorph.smulOfNeZero_symm_apply]
    rfl
  let τ : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) :=
    OpenPartialHomeomorph.univUnitBall.trans A.toOpenPartialHomeomorph
  have hτs : τ.source = univ := by
    simp [τ, OpenPartialHomeomorph.univUnitBall_source]
  have hτapp : ∀ v, τ v = c' + r • OpenPartialHomeomorph.univUnitBall v := fun v => rfl
  have hτt : ∀ y ∈ τ.target, A.symm y ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    intro y hy
    have h2 : A.symm y ∈ OpenPartialHomeomorph.univUnitBall.target := hy.2
    rwa [OpenPartialHomeomorph.univUnitBall_target] at h2
  have hτball : ∀ v, τ v ∈ ball c' r := by
    intro v
    have hu : OpenPartialHomeomorph.univUnitBall v ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
      have h := OpenPartialHomeomorph.univUnitBall.map_source
        (x := v) (by rw [OpenPartialHomeomorph.univUnitBall_source]; exact mem_univ v)
      rwa [OpenPartialHomeomorph.univUnitBall_target] at h
    rw [mem_ball_zero_iff] at hu
    rw [hτapp, mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le]
    nlinarith [norm_nonneg (OpenPartialHomeomorph.univUnitBall v)]
  have hτc : ContDiffOn ℝ ∞ τ τ.source := by
    change ContDiffOn ℝ ∞ (fun v => c' + r • OpenPartialHomeomorph.univUnitBall v) τ.source
    exact (contDiff_const.add
      (OpenPartialHomeomorph.contDiff_univUnitBall.const_smul r)).contDiffOn
  have hτsc : ContDiffOn ℝ ∞ τ.symm τ.target := by
    have hAc : ContDiff ℝ ∞ (A.symm : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) := by
      rw [show (A.symm : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) =
        fun y => r⁻¹ • (-c' + y) from funext hAs]
      exact (contDiff_const.add contDiff_id).const_smul r⁻¹
    change ContDiffOn ℝ ∞ (fun y => OpenPartialHomeomorph.univUnitBall.symm (A.symm y)) τ.target
    exact OpenPartialHomeomorph.contDiffOn_univUnitBall_symm.comp hAc.contDiffOn hτt
  have hτmax : τ ∈ IsManifold.maximalAtlas (𝓡 2) ∞ (EuclideanSpace ℝ (Fin 2)) :=
    DifferentialGeometry.OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn τ
      (contMDiffOn_iff_contDiffOn.mpr hτc) (contMDiffOn_iff_contDiffOn.mpr hτsc)
  let g : EuclideanSpace ℝ (Fin 2) → EuclideanHalfSpace 3 := fun v => ι (τ v)
  have hgemb : IsEmbedding g := hιemb.comp (τ.isOpenEmbedding hτs).isEmbedding
  have hgimm : IsImmersion (𝓡 2) (𝓡∂ 3) ∞ g := by
    apply IsImmersionOfComplement.isImmersion (F := ℝ)
    intro v
    apply IsImmersionAtOfComplement.mk_of_charts (normalFirstEquiv 2) τ
      (chartAt (EuclideanHalfSpace 3) (g v)) (by rw [hτs]; exact mem_univ v)
      (mem_chart_source _ _) hτmax (IsManifold.chart_mem_maximalAtlas (g v))
    · intro w _
      rw [mem_preimage, chartAt_self_eq]
      exact mem_univ _
    · intro u hu
      have hu' : u ∈ τ.target := by
        simpa only [OpenPartialHomeomorph.extend_target, modelWithCornersSelf_coe_symm,
          preimage_id_eq, modelWithCornersSelf_coe, range_id, inter_univ, id_eq] using hu
      change ((ι (τ (τ.symm u))).val : EuclideanSpace ℝ (Fin 3)) = normalFirstEquiv 2 (u, 0)
      rw [τ.right_inv hu']
  have hgV : ∀ v, g v ∈ V := fun v => hrV (hτball v)
  let Ψ : PartialDiffeomorph (𝓡∂ 3) (𝓡∂ 3) (EuclideanHalfSpace 3) M ∞ :=
    { toPartialEquiv := ψ.symm.toPartialEquiv
      open_source := ψ.open_target
      open_target := ψ.open_source
      contMDiffOn_toFun := contMDiffOn_chart_symm (x := x)
      contMDiffOn_invFun := contMDiffOn_chart (x := x) }
  have hf := isSmoothEmbedding_comp_partialDiffeomorph Ψ ⟨hgimm, hgemb⟩ (by
    rintro _ ⟨v, rfl⟩
    exact (hgV v).1)
  refine ⟨Ψ ∘ g, hf, ?_, ?_⟩
  · rintro _ ⟨v, rfl⟩
    have hvt := (hgV v).1
    have hys : ψ.symm (g v) ∈ ψ.source := ψ.map_target hvt
    refine (hbd _ hys).mpr ?_
    rw [ψ.right_inv hvt]
    exact normalFirstEquiv_zero 2 (τ v, 0)
  · rintro _ ⟨v, rfl⟩
    exact (hgV v).2

end DifferentialGeometry.Topology.PiecewiseLinear
