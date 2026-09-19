/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Homeomorph.PlanarGermIsotopy
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! Relative smoothing of topological disk charts in a prescribed smooth surface. -/

open Set Metric Filter Topology Manifold Schoenflies
open scoped ContDiff Manifold

namespace DifferentialGeometry.Manifold

theorem exists_isotopy_smoothing_surface_chart
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace Plane M]
    [IsManifold 𝓘(ℝ, Plane) ∞ M] (e : OpenPartialHomeomorph Plane M)
    {U : Set Plane} (hU : IsOpen U) (hU0 : (0 : Plane) ∈ U) (hUs : U ⊆ e.source) :
    ∃ K : Set Plane, IsCompact K ∧ K ⊆ U ∧ IsCompact (e '' K) ∧
      ∃ a : ℝ → Plane ≃ₜ Plane,
        Continuous (fun p : ℝ × Plane => a p.1 p.2) ∧
        Continuous (fun p : ℝ × Plane => (a p.1).symm p.2) ∧
        a 0 = Homeomorph.refl Plane ∧ (∀ t, a t 0 = 0) ∧
        (∀ t, EqOn (a t) id Kᶜ ∧ EqOn (a t).symm id Kᶜ) ∧
        ∃ J : ℝ → M ≃ₜ M,
          Continuous (fun p : ℝ × M => J p.1 p.2) ∧
          Continuous (fun p : ℝ × M => (J p.1).symm p.2) ∧
          J 0 = Homeomorph.refl M ∧
          (∀ t, EqOn (J t) id (e '' K)ᶜ ∧ EqOn (J t).symm id (e '' K)ᶜ) ∧
          (∀ t q, q ∈ e.source →
            J t (e q) = e (a t q) ∧ (J t).symm (e q) = e ((a t).symm q)) ∧
          ∃ r > 0, ∃ c : OpenPartialHomeomorph Plane M,
            c.source = ball 0 r ∧ ball 0 r ⊆ U ∧
            (∀ q, c q = e (a 1 q)) ∧
            (∀ y, c.symm y = (a 1).symm (e.symm y)) ∧
            c.symm ∈ IsManifold.maximalAtlas 𝓘(ℝ, Plane) ∞ M ∧
            ∀ b : OpenPartialHomeomorph M Plane,
              b ∈ IsManifold.maximalAtlas 𝓘(ℝ, Plane) ∞ M →
              ContDiffOn ℝ ∞ (c.trans b) (c.trans b).source ∧
              ContDiffOn ℝ ∞ (c.trans b).symm (c.trans b).target := by
  let b := chartAt Plane (e 0)
  let d := b.trans (Homeomorph.subRight (b (e 0))).toOpenPartialHomeomorph
  have hds : d.source = b.source := by simp [d]
  have hde : e 0 ∈ d.source := by rw [hds]; exact mem_chart_source Plane (e 0)
  have hd0 : d (e 0) = 0 := by change b (e 0) - b (e 0) = 0; exact sub_self _
  have hd : ContMDiffOn 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ d d.source := by
    change ContMDiffOn 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞
      (fun x => b x - b (e 0)) d.source
    exact ((contDiff_id.sub contDiff_const).contMDiff).comp_contMDiffOn
      ((contMDiffOn_chart (I := 𝓘(ℝ, Plane))).mono (fun _ hx => hx.1))
  have hdi : ContMDiffOn 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ d.symm d.target := by
    change ContMDiffOn 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞
      (fun x => b.symm (x + b (e 0))) d.target
    exact (contMDiffOn_chart_symm (I := 𝓘(ℝ, Plane))).comp
      (contDiff_id.add contDiff_const).contMDiff.contMDiffOn (fun _ hx => hx.2)
  obtain ⟨η, hη, hηU⟩ := Metric.isOpen_iff.mp hU 0 hU0
  obtain ⟨L, _, K, hK, hKη, a, ha, hai, ha0, haz, hafix, hlinear⟩ :=
    (e.trans d).exists_isotopy_linearizing_germ_in_ball ⟨hUs hU0, hde⟩ hd0 hη
  have hKU : K ⊆ U := hKη.trans hηU
  have hKs : K ⊆ e.source := hKU.trans hUs
  have heK : IsCompact (e '' K) :=
    hK.image_of_continuousOn (e.continuousOn.mono hKs)
  obtain ⟨J, hJ, hJi, hJe, hJfix⟩ :=
    e.symm.exists_conjugate_homeomorph_family a ha hai hK hKs hafix
  have hJ0 : J 0 = Homeomorph.refl M := by
    apply Homeomorph.ext
    intro y
    rw [(hJe 0 y).1, ha0]
    by_cases hy : y ∈ e.target
    · rw [e.symm.conjugateMap_of_mem _ hy]
      exact e.right_inv hy
    · exact e.symm.conjugateMap_of_notMem _ hy
  have hframe (t : ℝ) (q : Plane) (hq : q ∈ e.source) :
      J t (e q) = e (a t q) ∧ (J t).symm (e q) = e ((a t).symm q) := by
    constructor
    · rw [(hJe t (e q)).1, e.symm.conjugateMap_of_mem _ (e.map_source hq)]
      change e (a t (e.symm (e q))) = _
      rw [e.left_inv hq]
    · rw [(hJe t (e q)).2, e.symm.conjugateMap_of_mem _ (e.map_source hq)]
      change e ((a t).symm (e.symm (e q))) = _
      rw [e.left_inv hq]
  let f := (a 1).toOpenPartialHomeomorph.trans e
  let g := f.trans d
  have hg0 : (0 : Plane) ∈ g.source := by
    change ((0 : Plane) ∈ univ ∧ a 1 0 ∈ e.source) ∧ e (a 1 0) ∈ d.source
    rw [haz]
    exact ⟨⟨mem_univ _, hUs hU0⟩, hde⟩
  have hn : (g.source ∩ {x | g x = L x} ∩ U) ∈ 𝓝 (0 : Plane) := by
    filter_upwards [g.open_source.mem_nhds hg0, hlinear, hU.mem_nhds hU0] with x hx he hu
    exact ⟨⟨hx, he⟩, hu⟩
  obtain ⟨r, hr, hrg⟩ := Metric.mem_nhds_iff.mp hn
  let c := f.restr (ball 0 r)
  have hcsource : c.source = ball 0 r := by
    rw [OpenPartialHomeomorph.restr_source, isOpen_ball.interior_eq]
    exact inter_eq_right.mpr (fun x hx => (hrg hx).1.1.1)
  have hcrU : ball (0 : Plane) r ⊆ U := fun _ hx => (hrg hx).2
  have hcds {x : Plane} (hx : x ∈ c.source) : c x ∈ d.source :=
    (hrg (hcsource ▸ hx)).1.1.2
  have hcoord {x : Plane} (hx : x ∈ c.source) : d (c x) = L x :=
    (hrg (hcsource ▸ hx)).1.2
  have hcf (x : Plane) (hx : x ∈ c.source) : c x = d.symm (L x) := by
    rw [← hcoord hx]
    exact (d.left_inv (hcds hx)).symm
  have hct {y : M} (hy : y ∈ c.target) : y ∈ d.source := by
    have h := hcds (c.map_target hy)
    rwa [c.right_inv hy] at h
  have hci (y : M) (hy : y ∈ c.target) : c.symm y = L.symm (d y) := by
    apply L.injective
    rw [L.apply_symm_apply]
    have h := hcoord (c.map_target hy)
    rw [c.right_inv hy] at h
    exact h.symm
  have hcsm : ContMDiffOn 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ c c.source := by
    have hLs : MapsTo L c.source d.target := by
      intro x hx
      rw [← hcoord hx]
      exact d.map_source (hcds hx)
    exact (hdi.comp L.toContinuousLinearEquiv.contDiff.contMDiff.contMDiffOn hLs).congr
      (fun x hx => hcf x hx)
  have hcsi : ContMDiffOn 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ c.symm c.target :=
    (L.symm.toContinuousLinearEquiv.contDiff.contMDiff.comp_contMDiffOn
      (hd.mono (fun _ hy => hct hy))).congr (fun y hy => hci y hy)
  refine ⟨K, hK, hKU, heK, a, ha, hai, ha0, haz, hafix, J, hJ, hJi,
    hJ0, hJfix, hframe, r, hr, c, hcsource, hcrU, fun _ => rfl, fun _ => rfl,
    c.symm.mem_maximalAtlas_of_contMDiffOn hcsi hcsm, ?_⟩
  intro b hb
  have hbsm := contMDiffOn_of_mem_maximalAtlas hb
  have hbsi := contMDiffOn_symm_of_mem_maximalAtlas hb
  constructor
  · exact (hbsm.comp (hcsm.mono inter_subset_left) (fun _ hx => hx.2)).contDiffOn
  · exact (hcsi.comp (hbsi.mono inter_subset_left) (fun _ hx => hx.2)).contDiffOn

end DifferentialGeometry.Manifold
