/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Manifold.SurfaceChartSmoothing
import DifferentialGeometry.Topology.Manifold.ChartPartialDiffeomorph
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph

open Set Metric Filter Topology Manifold
open scoped ContDiff Manifold

namespace Homeomorph

open Schoenflies (Plane)

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [T2Space M] [T2Space N] [ChartedSpace Plane M] [ChartedSpace Plane N]
  [IsManifold 𝓘(ℝ, Plane) ∞ M] [IsManifold 𝓘(ℝ, Plane) ∞ N]

omit [IsManifold 𝓘(ℝ, Plane) ∞ M] in
theorem exists_smooth_at_in_chart (h : M ≃ₜ N)
    (a : PartialDiffeomorph 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) M Plane ∞)
    {x : M} (hxa : x ∈ a.source) (hax : a x = 0)
    {U : Set M} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ K : Set M, IsCompact K ∧ K ⊆ U ∧ ∃ g : M ≃ₜ N,
      EqOn g h Kᶜ ∧ g x = h x ∧ IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ g x ∧
      ∀ y ∉ K, IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ h y →
        IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ g y := by
  have ha0 : a.symm 0 = x := by
    have ha : a.symm (a x) = x := a.left_inv hxa
    rwa [hax] at ha
  let e := a.symm.toOpenPartialHomeomorph.trans h.toOpenPartialHomeomorph
  let V := a.target ∩ a.symm ⁻¹' U
  have hV : IsOpen V := a.toOpenPartialHomeomorph.isOpen_inter_preimage_symm hU
  have h0V : (0 : Plane) ∈ V := by
    refine ⟨hax ▸ a.map_source hxa, ?_⟩
    change a.symm 0 ∈ U
    rwa [ha0]
  have hVs : V ⊆ e.source := fun _ hq => ⟨hq.1, trivial⟩
  obtain ⟨L, hL, hLV, heL, α, -, -, -, hα0, -, J, -, -, -, hJfix, hframe,
    r, hr, c, hcs, -, hceq, -, hcmax, -⟩ :=
    DifferentialGeometry.Manifold.exists_isotopy_smoothing_surface_chart e hV h0V hVs
  let K := h.symm '' (e '' L)
  have hK : IsCompact K := heL.image h.symm.continuous
  have hKU : K ⊆ U := by
    rintro y ⟨z, ⟨q, hq, rfl⟩, rfl⟩
    change h.symm (h (a.symm q)) ∈ U
    rw [h.symm_apply_apply]
    exact (hLV hq).2
  let g := h.trans (J 1)
  have hgout : EqOn g h Kᶜ := by
    intro y hy
    apply (hJfix 1).1
    intro hhy
    exact hy ⟨h y, hhy, h.symm_apply_apply y⟩
  have he0 : e 0 = h x := by
    change h (a.symm 0) = h x
    rw [ha0]
  have hgx : g x = h x := by
    change J 1 (h x) = h x
    rw [← he0, (hframe 1 0 (hVs h0V)).1, hα0 1]
  let C : PartialDiffeomorph 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) Plane N ∞ := {
    toPartialEquiv := c.toPartialEquiv
    open_source := c.open_source
    open_target := c.open_target
    contMDiffOn_toFun := contMDiffOn_symm_of_mem_maximalAtlas hcmax
    contMDiffOn_invFun := contMDiffOn_of_mem_maximalAtlas hcmax }
  have hg : IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ g x := by
    refine ⟨a.trans C, ⟨hxa, ?_⟩, ?_⟩
    · change a x ∈ c.source
      rw [hcs, hax]
      exact mem_ball_self hr
    · intro y hy
      change J 1 (h y) = c (a y)
      have hay : a.symm (a y) = y := a.left_inv hy.1
      have heay : e (a y) = h y := by
        change h (a.symm (a y)) = h y
        rw [hay]
      rw [← heay, (hframe 1 (a y) ⟨a.map_source hy.1, trivial⟩).1]
      exact (hceq (a y)).symm
  refine ⟨K, hK, hKU, g, hgout, hgx, hg, ?_⟩
  intro y hy hhy
  apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq (g := h) _ hhy
  filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hy] with z hz
  exact hgout hz

theorem exists_smooth_at (h : M ≃ₜ N) {x : M} {U : Set M}
    (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ K : Set M, IsCompact K ∧ K ⊆ U ∧ ∃ g : M ≃ₜ N,
      EqOn g h Kᶜ ∧ g x = h x ∧ IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ g x ∧
      ∀ y ∉ K, IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ h y →
        IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ g y := by
  let a₀ := extChartAtPartialDiffeomorph 𝓘(ℝ, Plane) ∞ x
  let T : Plane ≃ₘ[ℝ] Plane := {
    toEquiv := (Homeomorph.subRight (a₀ x)).toEquiv
    contMDiff_toFun := (contDiff_id.sub contDiff_const).contMDiff
    contMDiff_invFun := (contDiff_id.add contDiff_const).contMDiff }
  let a := a₀.trans T.toPartialDiffeomorph
  have hxa : x ∈ a.source := ⟨mem_extChartAt_source x, mem_univ _⟩
  have hax : a x = 0 := by
    change a₀ x - a₀ x = 0
    exact sub_self _
  exact h.exists_smooth_at_in_chart a hxa hax hU hxU

theorem exists_smooth_on_finset (h : M ≃ₜ N) (T : Finset M) {U : Set M}
    (hU : IsOpen U) (hTU : (T : Set M) ⊆ U) :
    ∃ K : Set M, IsCompact K ∧ K ⊆ U ∧ ∃ g : M ≃ₜ N,
      EqOn g h Kᶜ ∧ EqOn g h (T : Set M) ∧
      IsLocalDiffeomorphOn 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ g (T : Set M) := by
  classical
  have step : ∀ s : Finset M, s ⊆ T →
      ∃ K : Set M, IsCompact K ∧ K ⊆ U ∧ ∃ g : M ≃ₜ N,
        EqOn g h Kᶜ ∧ EqOn g h (T : Set M) ∧
        IsLocalDiffeomorphOn 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ g (s : Set M) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _
        refine ⟨∅, isCompact_empty, empty_subset _, h, fun _ _ => rfl, fun _ _ => rfl, ?_⟩
        intro y
        exact False.elim (by simpa using y.property)
    | @insert x s hxs ih =>
        intro hsub
        have hxT : x ∈ T := hsub (Finset.mem_insert_self _ _)
        have hsT : s ⊆ T := fun y hy => hsub (Finset.mem_insert_of_mem hy)
        obtain ⟨K, hK, hKU, g, hgout, hgfix, hgdiff⟩ := ih hsT
        let V := U ∩ (T.erase x : Set M)ᶜ
        have hV : IsOpen V := hU.inter (T.erase x).finite_toSet.isClosed.isOpen_compl
        have hxV : x ∈ V := ⟨hTU hxT, by simp⟩
        obtain ⟨L, hL, hLV, g', hg'out, hg'x, hg'diff, hg'preserve⟩ :=
          g.exists_smooth_at hV hxV
        have hout {y : M} (hyT : y ∈ T) (hyx : y ≠ x) : y ∉ L := by
          intro hyL
          exact (hLV hyL).2 (Finset.mem_erase.mpr ⟨hyx, hyT⟩)
        refine ⟨K ∪ L, hK.union hL, union_subset hKU (hLV.trans inter_subset_left),
          g', ?_, ?_, ?_⟩
        · intro y hy
          exact (hg'out (fun hyL => hy (Or.inr hyL))).trans
            (hgout (fun hyK => hy (Or.inl hyK)))
        · intro y hyT
          by_cases hyx : y = x
          · subst y
            exact hg'x.trans (hgfix hxT)
          · exact (hg'out (hout hyT hyx)).trans (hgfix hyT)
        · intro y
          rcases Finset.mem_insert.mp y.property with hyx | hys
          · simpa only [hyx] using hg'diff
          · have hyx : (y : M) ≠ x := by
              intro heq
              apply hxs
              simpa only [heq] using hys
            exact hg'preserve y (hout (hsT hys) hyx) (hgdiff ⟨y, hys⟩)
  exact step T (Finset.Subset.refl T)

end Homeomorph
