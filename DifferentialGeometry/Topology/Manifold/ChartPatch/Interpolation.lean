import Mathlib.Analysis.Convex.Basic
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Algebra.SMul

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Manifold

theorem exists_contMDiffOn_supported_chart_interpolation
    {E F H G M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace G]
    [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace H M] [ChartedSpace G N]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    {n : ℕ∞ω} {A W T : Set M}
    (hA : IsOpen A) (hW : IsOpen W) (hT : IsOpen T)
    {f : M → N} {q : M → F} {χ : M → ℝ}
    (hf : ContMDiffOn I J n f A)
    (hq : ContMDiffOn I 𝓘(ℝ, F) n q (W ∩ T))
    (hχ : ContMDiffOn I 𝓘(ℝ, ℝ) n χ W)
    (hχrange : MapsTo χ W (Icc 0 1))
    (hχA : W ∩ tsupport χ ⊆ A)
    (hχT : W ∩ tsupport (fun x ↦ 1 - χ x) ⊆ T)
    (e : OpenPartialHomeomorph F N)
    (he : ContMDiffOn 𝓘(ℝ, F) J n e e.source)
    (heinv : ContMDiffOn J 𝓘(ℝ, F) n e.symm e.target)
    {D : Set F} (hD : Convex ℝ D) (hDe : D ⊆ e.source)
    (hqD : MapsTo q (W ∩ T) D)
    (hfD : ∀ x ∈ W ∩ T ∩ tsupport χ,
      f x ∈ e.target ∧ e.symm (f x) ∈ D) :
    ∃ g : M → N,
      ContMDiffOn I J n g W ∧
      EqOn g f (W ∩ {x | χ x = 1}) ∧
      EqOn g (e ∘ q) (W ∩ {x | χ x = 0}) ∧
      MapsTo g (W ∩ T) e.target ∧
      (∀ x ∈ W ∩ T,
        g x = e (q x + χ x • (e.symm (f x) - q x))) ∧
      (∀ x ∈ W ∩ T,
        e.symm (g x) = q x + χ x • (e.symm (f x) - q x)) := by
  classical
  let c : M → F := fun x ↦
    if x ∈ W ∩ T ∩ tsupport χ then χ x • (e.symm (f x) - q x) else 0
  let v : M → F := fun x ↦ q x + c x
  let g : M → N := fun x ↦ if x ∈ W ∩ T then e (v x) else f x
  have hc (x : M) (hx : x ∈ W ∩ T) :
      c x = χ x • (e.symm (f x) - q x) := by
    by_cases hs : x ∈ tsupport χ
    · simp only [c, ite_eq_left (show x ∈ W ∩ T ∩ tsupport χ from ⟨hx, hs⟩)]
    · simp [c, hs, image_eq_zero_of_notMem_tsupport hs]
  have hv (x : M) (hx : x ∈ W ∩ T) : v x ∈ D := by
    by_cases hs : x ∈ tsupport χ
    · change q x + c x ∈ D
      rw [hc x hx]
      exact hD.add_smul_sub_mem (hqD hx) (hfD x ⟨hx, hs⟩).2 (hχrange hx.1)
    · simpa [v, c, hs] using hqD hx
  have hgold (x : M) (hx : x ∈ W) (hχx : χ x = 1) : g x = f x := by
    by_cases hxT : x ∈ T
    · have hs : x ∈ tsupport χ := subset_closure (by simp [Function.mem_support, hχx])
      have hfx := (hfD x ⟨⟨hx, hxT⟩, hs⟩).1
      simpa [g, hx, hxT, v, hc x ⟨hx, hxT⟩, hχx] using e.right_inv hfx
    · simp [g, hxT]
  have hnew (x : M) (hx : x ∈ W) (hχx : χ x = 0) : g x = e (q x) := by
    have hs : x ∈ tsupport (fun y ↦ 1 - χ y) :=
      subset_closure (by simp [Function.mem_support, hχx])
    have hxT := hχT ⟨hx, hs⟩
    simp [g, hx, hxT, v, hc x ⟨hx, hxT⟩, hχx]
  have hcv (x : M) (hx : x ∈ W ∩ T) : ContMDiffAt I 𝓘(ℝ, F) n v x := by
    have hqx := hq.contMDiffAt ((hW.inter hT).mem_nhds hx)
    apply hqx.add
    by_cases hs : x ∈ tsupport χ
    · have hfx := hf.contMDiffAt (hA.mem_nhds (hχA ⟨hx.1, hs⟩))
      have hex := heinv.contMDiffAt (e.open_target.mem_nhds (hfD x ⟨hx, hs⟩).1)
      have hcx := (hχ.contMDiffAt (hW.mem_nhds hx.1)).smul ((hex.comp x hfx).sub hqx)
      apply hcx.congr_of_eventuallyEq
      filter_upwards [(hW.inter hT).mem_nhds hx] with y hy
      exact hc y hy
    · apply (contMDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hs] with y hy
      have hys : y ∉ tsupport χ := hy
      simp [c, hys]
  refine ⟨g, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    by_cases hxT : x ∈ T
    · have hvx := hDe (hv x ⟨hx, hxT⟩)
      have hex := he.contMDiffAt (e.open_source.mem_nhds hvx)
      apply (hex.comp x (hcv x ⟨hx, hxT⟩)).contMDiffWithinAt.congr_of_eventuallyEq_of_mem
        _ hx
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds
        ((hW.inter hT).mem_nhds ⟨hx, hxT⟩)] with y hy
      simp [g, hy.1, hy.2]
    · have hs : x ∉ tsupport (fun y ↦ 1 - χ y) := fun hs ↦ hxT (hχT ⟨hx, hs⟩)
      have hχx : χ x = 1 := sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport (f := fun y : M ↦ 1 - χ y) hs) |>.symm
      have hxA : x ∈ A := hχA ⟨hx, subset_closure (by simp [Function.mem_support, hχx])⟩
      apply (hf.contMDiffAt (hA.mem_nhds hxA)).contMDiffWithinAt.congr_of_eventuallyEq_of_mem
        _ hx
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds
        (hW.mem_nhds hx), eventually_nhdsWithin_of_eventually_nhds
        ((isClosed_tsupport (fun y ↦ 1 - χ y)).isOpen_compl.mem_nhds hs)] with y hy hys
      exact hgold y hy ((sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport (f := fun z : M ↦ 1 - χ z) hys)).symm)
  · intro x hx
    exact hgold x hx.1 hx.2
  · intro x hx
    exact hnew x hx.1 hx.2
  · intro x hx
    simpa [g, hx.1, hx.2] using e.map_source (hDe (hv x hx))
  · intro x hx
    simp [g, hx.1, hx.2, v, hc x hx]
  · intro x hx
    simpa [g, hx.1, hx.2, v, hc x hx] using e.left_inv (hDe (hv x hx))

end DifferentialGeometry.Topology.Manifold
