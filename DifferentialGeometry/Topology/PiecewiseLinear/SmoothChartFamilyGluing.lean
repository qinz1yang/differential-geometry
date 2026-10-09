/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.InvarianceOfDomainManifold
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

open Set Topology Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_isManifold_of_isOpenEmbedding_of_charts
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] {X : Type} [TopologicalSpace X] {J : Type}
    (U : TopologicalSpace.Opens M) (ι : M → X) (hι : IsOpenEmbedding (fun p : U => ι p.val))
    (κ : J → OpenPartialHomeomorph X (EuclideanHalfSpace 3))
    (hcov : ∀ x, x ∈ ι '' U ∨ ∃ j, x ∈ (κ j).source)
    (hκκ : ∀ j k, ContMDiffOn (𝓡∂ 3) (𝓡∂ 3) ∞ ((κ j).symm.trans (κ k))
      ((κ j).symm.trans (κ k)).source)
    (hfwd : ∀ j, ∀ m ∈ U, ι m ∈ (κ j).source →
      ContMDiffAt (𝓡∂ 3) (𝓡∂ 3) ∞ (fun m => κ j (ι m)) m)
    (Θ : J → EuclideanHalfSpace 3 → M)
    (hbwd : ∀ j, ∀ y ∈ (κ j).target, (κ j).symm y ∈ ι '' U →
      Θ j y ∈ U ∧ (κ j).symm y = ι (Θ j y) ∧ ContMDiffAt (𝓡∂ 3) (𝓡∂ 3) ∞ (Θ j) y) :
    ∃ cs : ChartedSpace (EuclideanHalfSpace 3) X,
      letI := cs
      IsManifold (𝓡∂ 3) ∞ X ∧
        ∀ m ∈ U, ((𝓡∂ 3).IsBoundaryPoint (ι m) ↔ (𝓡∂ 3).IsBoundaryPoint m) := by
  classical
  have hιU : IsOpen (ι '' U) := by
    have h : range (fun p : U => ι p.val) = ι '' U := by
      ext x
      constructor
      · rintro ⟨p, rfl⟩
        exact ⟨p.val, p.2, rfl⟩
      · rintro ⟨m, hm, rfl⟩
        exact ⟨⟨m, hm⟩, rfl⟩
    rw [← h]
    exact hι.isOpen_range
  let chartL : U → OpenPartialHomeomorph X (EuclideanHalfSpace 3) :=
    fun p => (chartAt (EuclideanHalfSpace 3) p).lift_openEmbedding hι
  let chartFn : X → OpenPartialHomeomorph X (EuclideanHalfSpace 3) := fun x =>
    if hx : x ∈ ι '' U then chartL ⟨hx.choose, hx.choose_spec.1⟩
    else κ ((hcov x).resolve_left hx).choose
  let cs : ChartedSpace (EuclideanHalfSpace 3) X :=
    { atlas := range chartL ∪ range κ
      chartAt := chartFn
      mem_chart_source := fun x => by
        by_cases hx : x ∈ ι '' U
        · simp only [chartFn, dite_eq_left hx]
          exact ⟨_, mem_chart_source _ _, hx.choose_spec.2⟩
        · simp only [chartFn, dite_eq_right hx]
          exact ((hcov x).resolve_left hx).choose_spec
      chart_mem_atlas := fun x => by
        by_cases hx : x ∈ ι '' U
        · simp only [chartFn, dite_eq_left hx]
          exact Or.inl ⟨_, rfl⟩
        · simp only [chartFn, dite_eq_right hx]
          exact Or.inr ⟨_, rfl⟩ }
  refine ⟨cs, ?_, ?_⟩
  · apply isManifold_of_contDiffOn (𝓡∂ 3) ∞ X
    intro e e' he he'
    have hT : ContMDiffOn (𝓡∂ 3) (𝓡∂ 3) ∞ (e.symm.trans e') (e.symm.trans e').source := by
      change e ∈ range chartL ∪ range κ at he
      change e' ∈ range chartL ∪ range κ at he'
      rcases he with ⟨p, rfl⟩ | ⟨j, rfl⟩
      · rcases he' with ⟨q, rfl⟩ | ⟨k, rfl⟩
        · change ContMDiffOn (𝓡∂ 3) (𝓡∂ 3) ∞
            (((chartAt (EuclideanHalfSpace 3) p).lift_openEmbedding hι).symm.trans
              ((chartAt (EuclideanHalfSpace 3) q).lift_openEmbedding hι))
            (((chartAt (EuclideanHalfSpace 3) p).lift_openEmbedding hι).symm.trans
              ((chartAt (EuclideanHalfSpace 3) q).lift_openEmbedding hι)).source
          rw [OpenPartialHomeomorph.lift_openEmbedding_trans]
          exact (contMDiffOn_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas q)).comp
            ((contMDiffOn_symm_of_mem_maximalAtlas
              (IsManifold.chart_mem_maximalAtlas p)).mono fun z hz => hz.1)
            fun z hz => hz.2
        · intro y hy
          apply ContMDiffAt.contMDiffWithinAt
          have hy1 : y ∈ (chartAt (EuclideanHalfSpace 3) p).target := hy.1
          have hmS : ι ((chartAt (EuclideanHalfSpace 3) p).symm y).val ∈ (κ k).source := hy.2
          have h1 : ContMDiffAt (𝓡∂ 3) (𝓡∂ 3) ∞ (chartAt (EuclideanHalfSpace 3) p).symm y :=
            (contMDiffOn_symm_of_mem_maximalAtlas
              (IsManifold.chart_mem_maximalAtlas p)).contMDiffAt
              ((chartAt (EuclideanHalfSpace 3) p).open_target.mem_nhds hy1)
          have h2 : ContMDiffAt (𝓡∂ 3) (𝓡∂ 3) ∞ (Subtype.val : U → M)
              ((chartAt (EuclideanHalfSpace 3) p).symm y) :=
            contMDiff_subtype_val.contMDiffAt
          have h3 := hfwd k _ ((chartAt (EuclideanHalfSpace 3) p).symm y).2 hmS
          have hc := h3.comp y (h2.comp y h1)
          exact hc
      · rcases he' with ⟨q, rfl⟩ | ⟨k, rfl⟩
        · intro y hy
          apply ContMDiffAt.contMDiffWithinAt
          have key : ∀ y' ∈ ((κ j).symm.trans (chartL q)).source,
              y' ∈ (κ j).target ∧ (κ j).symm y' ∈ ι '' U := by
            intro y' hy'
            obtain ⟨p', -, hpe⟩ := hy'.2
            exact ⟨hy'.1, ⟨p'.val, p'.2, hpe⟩⟩
          let ΘU : EuclideanHalfSpace 3 → U := fun w =>
            if h : Θ j w ∈ U then ⟨Θ j w, h⟩ else q
          have heq : ∀ᶠ y' in 𝓝 y, ((κ j).symm.trans (chartL q)) y' =
              ((chartAt (EuclideanHalfSpace 3) q) ∘ ΘU) y' := by
            filter_upwards [((κ j).symm.trans (chartL q)).open_source.mem_nhds hy] with y' hy'
            obtain ⟨hvt, hvU⟩ := key y' hy'
            obtain ⟨hΘU, hκ, -⟩ := hbwd j _ hvt hvU
            have hk : ΘU y' = ⟨Θ j y', hΘU⟩ := dite_eq_left hΘU
            change (chartL q) ((κ j).symm y') = _
            rw [hκ, Function.comp_apply, hk]
            exact OpenPartialHomeomorph.lift_openEmbedding_apply (chartAt (EuclideanHalfSpace 3) q)
              hι (x := ⟨Θ j y', hΘU⟩)
          obtain ⟨hvt, hvU⟩ := key y hy
          obtain ⟨hΘU, hκ, hΘs⟩ := hbwd j _ hvt hvU
          have hnbhd : ∀ᶠ w in 𝓝 y, Θ j w ∈ U := by
            filter_upwards [((κ j).isOpen_inter_preimage_symm hιU).mem_nhds ⟨hvt, hvU⟩]
              with w hw
            exact (hbwd j w hw.1 hw.2).1
          have hΘUat : ContMDiffAt (𝓡∂ 3) (𝓡∂ 3) ∞ ΘU y := by
            refine (ContMDiffAt.subtypeVal_comp_iff U ΘU _).mp ?_
            apply hΘs.congr_of_eventuallyEq
            filter_upwards [hnbhd] with w hw
            simp only [Function.comp_apply, ΘU, dite_eq_left hw]
          have hq' : ΘU y ∈ (chartAt (EuclideanHalfSpace 3) q).source := by
            obtain ⟨p', hp', hpe⟩ := hy.2
            have hp'eq : p' = ΘU y := by
              rw [show ΘU y = ⟨Θ j y, hΘU⟩ from dite_eq_left hΘU]
              exact hι.injective (hpe.trans hκ)
            rw [← hp'eq]
            exact hp'
          have hT3 : ContMDiffAt (𝓡∂ 3) (𝓡∂ 3) ∞ (chartAt (EuclideanHalfSpace 3) q) (ΘU y) :=
            (contMDiffOn_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas q)).contMDiffAt
              ((chartAt (EuclideanHalfSpace 3) q).open_source.mem_nhds hq')
          exact (hT3.comp y hΘUat).congr_of_eventuallyEq heq
        · exact hκκ j k
    have hcoord := hT.comp ((𝓡∂ 3).contMDiffOn_symm.mono
      (inter_subset_right : (𝓡∂ 3).symm ⁻¹' (e.symm.trans e').source ∩ range (𝓡∂ 3) ⊆
        range (𝓡∂ 3))) (fun z hz => hz.1)
    exact ((𝓡∂ 3).contMDiff.comp_contMDiffOn hcoord).contDiffOn
  · intro m hm
    let p : U := ⟨m, hm⟩
    have hsrc : ι m ∈ (chartL p).source := ⟨p, mem_chart_source _ p, rfl⟩
    have h1 := isBoundaryPoint_iff_any_chart_real (𝓡∂ 3) hsrc
    have h2 := isBoundaryPoint_iff_any_chart_real (𝓡∂ 3)
      (mem_chart_source (EuclideanHalfSpace 3) m)
    have hval : (chartL p) (ι m) = chartAt (EuclideanHalfSpace 3) p p :=
      OpenPartialHomeomorph.lift_openEmbedding_apply (chartAt (EuclideanHalfSpace 3) p) hι
        (x := p)
    have hval2 : chartAt (EuclideanHalfSpace 3) p p = chartAt (EuclideanHalfSpace 3) m m := rfl
    rw [h1, hval, hval2, ← h2]

end DifferentialGeometry.Topology.PiecewiseLinear
