/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusTamingSteps
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceAnnulusShrink
import DifferentialGeometry.Topology.PiecewiseLinear.SphereBandChart
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryIsotopyExtension
import DifferentialGeometry.Topology.Manifold.AnnulusCoreSmoothing
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.Instances.Sphere

open Set Topology Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

universe u

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_homeomorph_smooth_annulus_of_isClosedEmbedding
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] [T2Space M] [CompactSpace M]
    (ψ : {z : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 |
      z.val ∈ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1} → M)
    (hψ : IsClosedEmbedding ψ) (hψbd : range ψ ⊆ (𝓡∂ 3).boundary M) :
    ∃ θ : M ≃ₜ M, θ '' (𝓡∂ 3).boundary M = (𝓡∂ 3).boundary M ∧
      ∃ f : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × ℝ → M,
        IsSmoothEmbedding ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡∂ 3) ∞ f ∧
        range f ⊆ (𝓡∂ 3).boundary M ∧
        θ '' range ψ = f '' (univ ×ˢ Icc (0 : ℝ) 1) := by
  classical
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) (BoundaryManifold (𝓡∂ 3) M) :=
    BoundaryManifold.chartedSpace (I := 𝓡∂ 3)
  let _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ (BoundaryManifold (𝓡∂ 3) M) :=
    BoundaryManifold.isManifold (I := 𝓡∂ 3)
  obtain ⟨e, hec, hei, herange⟩ := exists_halfAnnulus_param_of_isClosedEmbedding ψ hψ hψbd
  obtain ⟨a, b, ha, hab, hb, Gs, hGsc, hGsi, hGs0, hGsimg⟩ :=
    exists_isotopy_shrink_halfAnnulus e hec hei
  obtain ⟨Φ, hΦs, hΦe⟩ := exists_openPartialHomeomorph_of_halfAnnulus_embedding e hec hei
  have hΦsub : {x : EuclideanSpace ℝ (Fin 2) | 1 < ‖x‖ ∧ ‖x‖ < 2} ⊆ Φ.source := by
    rw [hΦs]
  obtain ⟨Gc, hGcc, hGci, hGc0, δ, hδ, hδ2, c, hcs, hce, hcmax⟩ :=
    DifferentialGeometry.Manifold.exists_isotopy_smooth_annulus_core Φ hΦsub
  obtain ⟨j, hjs, hjt, hjsm, hjsi, κ, hκ, hκ1, hjimg⟩ :=
    exists_sphereProd_band_openPartialHomeomorph (ε := δ / 2) (by positivity) (by linarith)
  have hq2 : 3 / 2 + δ / 2 * κ < 2 := by nlinarith
  obtain ⟨J, hJc, hJi, hJ0, hJimg⟩ := exists_isotopy_radial_of_annulus_chart Φ hΦsub
    (r₁ := 2 * a) (r₂ := 2 * b) (q₁ := 3 / 2) (q₂ := 3 / 2 + δ / 2 * κ) (by linarith)
    (by linarith) (by linarith) (by norm_num) (by nlinarith) hq2
  let G : ℝ → BoundaryManifold (𝓡∂ 3) M ≃ₜ BoundaryManifold (𝓡∂ 3) M :=
    fun t => ((Gs t).trans (J t)).trans (Gc t)
  have hGc : Continuous (fun p : ℝ × BoundaryManifold (𝓡∂ 3) M => G p.1 p.2) :=
    hGcc.comp (continuous_fst.prodMk (hJc.comp (continuous_fst.prodMk hGsc)))
  have hGi : Continuous (fun p : ℝ × BoundaryManifold (𝓡∂ 3) M => (G p.1).symm p.2) :=
    hGsi.comp (continuous_fst.prodMk (hJi.comp (continuous_fst.prodMk hGci)))
  have hG0 : G 0 = Homeomorph.refl _ := by
    refine Homeomorph.ext fun y => ?_
    change Gc 0 (J 0 (Gs 0 y)) = y
    rw [hGs0, hJ0, hGc0]
    rfl
  obtain ⟨θ, hθbd, hθ⟩ := exists_homeomorph_of_boundary_isotopy G hGc hGi hG0
  have hjc : ∀ w ∈ j.target, w ∈ c.source := by
    intro w hw
    rw [hjt] at hw
    rw [hcs]
    change |‖w‖ - 3 / 2| < δ
    have : |‖w‖ - 3 / 2| < δ / 2 := hw
    linarith
  let Fm := j.trans c
  have hFs : Fm.source = univ := by
    rw [OpenPartialHomeomorph.trans_source, hjs, univ_inter]
    exact eq_univ_of_forall fun q => hjc _ (j.map_source (hjs ▸ mem_univ q))
  have hcsm : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ c
      c.source := by
    have := contMDiffOn_symm_of_mem_maximalAtlas hcmax
    rwa [OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.symm_target] at this
  have hcsi : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞
      c.symm c.target := contMDiffOn_of_mem_maximalAtlas hcmax
  have hF : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)) ∞
      Fm univ :=
    hcsm.comp hjsm fun q _ => hjc _ (j.map_source (hjs ▸ mem_univ q))
  have hFi : ContMDiffOn (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞
      Fm.symm Fm.target := by
    have hsub : Fm.target ⊆ c.target ∩ c.symm ⁻¹' j.target := by
      intro y hy
      rw [OpenPartialHomeomorph.trans_target] at hy
      exact hy
    exact hjsi.comp (hcsi.mono fun y hy => (hsub hy).1) fun y hy => (hsub hy).2
  refine ⟨θ, hθbd, fun x => (Fm x : M),
    isSmoothEmbedding_coe_of_boundary_openPartialHomeomorph Fm hFs hF hFi, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact (Fm x).2
  · have h1 : θ '' range ψ =
        (fun y : BoundaryManifold (𝓡∂ 3) M => (y : M)) '' (G 1 '' range e) := by
      rw [← herange, ← image_comp, ← image_comp]
      exact image_congr fun y _ => hθ y
    have h2 : G 1 '' range e = Gc 1 '' (J 1 '' (Gs 1 '' range e)) := by
      rw [← image_comp, ← image_comp]
      rfl
    have h3 : e '' {v | a ≤ ‖v.val‖ ∧ ‖v.val‖ ≤ b} =
        Φ '' {x : EuclideanSpace ℝ (Fin 2) | 2 * a ≤ ‖x‖ ∧ ‖x‖ ≤ 2 * b} := by
      ext y
      constructor
      · rintro ⟨v, hv, rfl⟩
        refine ⟨(2 : ℝ) • v.val, ?_, hΦe v (by linarith [hv.1]) (by linarith [hv.2])⟩
        change 2 * a ≤ ‖(2 : ℝ) • v.val‖ ∧ ‖(2 : ℝ) • v.val‖ ≤ 2 * b
        rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
        exact ⟨by linarith [hv.1], by linarith [hv.2]⟩
      · rintro ⟨x, hx, rfl⟩
        have hxn : ‖(1 / 2 : ℝ) • x‖ = ‖x‖ / 2 := by
          rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
          ring
        let v : {x : EuclideanSpace ℝ (Fin 2) // 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1} :=
          ⟨(1 / 2 : ℝ) • x, by rw [hxn]; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩⟩
        refine ⟨v, ?_, ?_⟩
        · change a ≤ ‖(1 / 2 : ℝ) • x‖ ∧ ‖(1 / 2 : ℝ) • x‖ ≤ b
          rw [hxn]
          exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
        · have h4 := hΦe v (by change 1 / 2 < ‖(1 / 2 : ℝ) • x‖; rw [hxn]; linarith [hx.1])
            (by change ‖(1 / 2 : ℝ) • x‖ < 1; rw [hxn]; linarith [hx.2])
          have h5 : (2 : ℝ) • v.val = x := by
            change (2 : ℝ) • (1 / 2 : ℝ) • x = x
            rw [smul_smul]
            norm_num
          rw [h5] at h4
          exact h4.symm
    have h6 : Gc 1 '' (Φ '' {x : EuclideanSpace ℝ (Fin 2) |
        3 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 3 / 2 + δ / 2 * κ}) = c '' {x : EuclideanSpace ℝ (Fin 2) |
          3 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 3 / 2 + δ / 2 * κ} := by
      rw [← image_comp]
      refine image_congr fun x hx => ?_
      have hxc : x ∈ c.source := by
        rw [hcs]
        change |‖x‖ - 3 / 2| < δ
        rw [abs_lt]
        constructor <;> nlinarith [hx.1, hx.2]
      exact (hce x hxc).symm
    have h7 : c '' {x : EuclideanSpace ℝ (Fin 2) | 3 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 3 / 2 + δ / 2 * κ} =
        Fm '' (univ ×ˢ Icc (0 : ℝ) 1) := by
      rw [← hjimg, ← image_comp]
      rfl
    rw [h1, h2, hGsimg, h3, hJimg, h6, h7, ← image_comp]
    rfl

end DifferentialGeometry.Topology.PiecewiseLinear
