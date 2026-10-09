/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LocalLinePolyhedron
import DifferentialGeometry.Topology.PiecewiseLinear.PLModelCellRestriction

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Classical in
theorem IsPLHomeomorphInto.exists_model_circles_of_image_lineCharts
    {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
    {u : E3 → M} {P S : Set E3} (hu : IsPLHomeomorphInto 3 u P)
    (hS : IsPolyhedron S) (hSP : S ⊆ P)
    (hcharts : ∀ y ∈ u '' S, ∃ e : OpenPartialHomeomorph M (ℝ × ℝ × ℝ),
      y ∈ e.source ∧ e y = 0 ∧
        ∀ z ∈ e.source, z ∈ u '' S ↔ (e z).2 = 0) :
    ∃ (ι : Type) (_ : Finite ι) (J : ι → Set E3), (∀ i, IsPLSphere 1 (J i)) ∧
      (Pairwise fun i j => Disjoint (J i) (J j)) ∧ S = ⋃ i, J i := by
  apply exists_iUnion_isPLSphere_one_of_local_real_embeddings hS
  · intro x hx
    obtain ⟨e, hxe, -, hline⟩ := hcharts (u x) ⟨x, hx, rfl⟩
    have hpre : u ⁻¹' e.source ∈ 𝓝[P] x :=
      (hu.continuousOn x (hSP hx)).preimage_mem_nhdsWithin
        (e.open_source.mem_nhds hxe)
    obtain ⟨O, hO, hxO, hOsub⟩ := mem_nhdsWithin.mp hpre
    have hmap : MapsTo u (O ∩ S) e.source := fun z hz => hOsub ⟨hz.1, hSP hz.2⟩
    refine ⟨O, fun z => (e (u z)).1, hO, hxO, ?_, ?_⟩
    · exact (e.continuousOn.comp (hu.continuousOn.mono
        (inter_subset_right.trans hSP)) hmap).fst
    · intro z hz w hw hzw
      apply hu.injOn (hSP hz.2) (hSP hw.2)
      apply e.injOn (hmap hz) (hmap hw)
      apply Prod.ext hzw
      rw [(hline _ (hmap hz)).mp ⟨z, hz.2, rfl⟩,
        (hline _ (hmap hw)).mp ⟨w, hw.2, rfl⟩]
  · intro x hx
    obtain ⟨e, hxe, hex, hline⟩ := hcharts (u x) ⟨x, hx, rfl⟩
    let l : ℝ → ℝ × ℝ × ℝ := fun t => (t, 0, 0)
    have hl : Continuous l := by fun_prop
    have hzero : (0 : ℝ × ℝ × ℝ) ∈ e.target := hex ▸ e.map_source hxe
    have hnear : l ⁻¹' e.target ∈ 𝓝 (0 : ℝ) :=
      hl.continuousAt.preimage_mem_nhds (e.open_target.mem_nhds hzero)
    obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hnear
    have hltarget : MapsTo l (Ioo (-r) r) e.target := by
      intro t ht
      apply hrsub
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using abs_lt.mpr ht
    have himage : MapsTo (e.symm ∘ l) (Ioo (-r) r) (u '' S) := by
      intro t ht
      apply (hline _ (e.map_target (hltarget ht))).mpr
      rw [e.right_inv (hltarget ht)]
      rfl
    let g := Function.invFunOn u P
    let γ : ℝ → E3 := g ∘ e.symm ∘ l
    have hgleft : LeftInvOn g u P := hu.injOn.leftInvOn_invFunOn
    have hgright : RightInvOn g u (u '' P) := hu.injOn.bijOn_image.invOn_invFunOn.2
    have hγS : MapsTo γ (Ioo (-r) r) S := by
      intro t ht
      obtain ⟨z, hz, hzt⟩ := himage ht
      change u z = e.symm (l t) at hzt
      change g (e.symm (l t)) ∈ S
      rw [← hzt, hgleft (hSP hz)]
      exact hz
    have hγval : ∀ t ∈ Ioo (-r) r, e (u (γ t)) = l t := by
      intro t ht
      change e (u (g (e.symm (l t)))) = l t
      have htimage : e.symm (l t) ∈ u '' P := image_mono hSP (himage ht)
      rw [hgright htimage, e.right_inv (hltarget ht)]
    have hgcont : ContinuousOn g (u '' P) :=
      fun z hz => (hu.isPLOn_inverse hgleft z hz).continuousWithinAt
    refine ⟨r, hr, γ, ?_, ?_, hγS, ?_⟩
    · exact hgcont.comp
        (e.continuousOn_symm.comp hl.continuousOn hltarget)
        (fun t ht => image_mono hSP (himage ht))
    · intro t ht t' ht' htt'
      have heq := congrArg (fun z => (e (u z)).1) htt'
      simpa only [hγval t ht, hγval t' ht', l] using heq
    · change g (e.symm (l 0)) = x
      have hl0 : l 0 = e (u x) := hex.symm
      rw [hl0, e.left_inv hxe, hgleft (hSP hx)]

end DifferentialGeometry.Topology.PiecewiseLinear
