/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Attachment.Basic
import DifferentialGeometry.Topology.Handle.SmoothStage
import DifferentialGeometry.Topology.InvarianceOfDomainManifold
import DifferentialGeometry.Topology.Manifold.Attachment.AdjunctionSeparation
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

open Set Topology Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

open DifferentialGeometry.Topology.Manifold.Attachment (adjunctionLower_injective
  adjunctionCell_eq_lower_iff adjunction_inclusions_cover adjunction_t2Space
  isClosedEmbedding_adjunctionLower isClosedEmbedding_adjunctionCell)

noncomputable def halfSpaceShiftFun (s : ℝ) (v : EuclideanSpace ℝ (Fin 3)) :
    EuclideanHalfSpace 3 :=
  if h : 0 ≤ v 0 + s then ⟨v + EuclideanSpace.single 0 s, by simpa using h⟩
  else ⟨0, by simp⟩

theorem halfSpaceShiftFun_val {s : ℝ} {v : EuclideanSpace ℝ (Fin 3)} (h : 0 ≤ v 0 + s) :
    (halfSpaceShiftFun s v).val = v + EuclideanSpace.single 0 s := by
  simp only [halfSpaceShiftFun, dite_eq_left h]

noncomputable def halfSpaceShift (s : ℝ) :
    OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (EuclideanHalfSpace 3) where
  toFun := halfSpaceShiftFun s
  invFun y := y.val - EuclideanSpace.single 0 s
  source := {v | 0 < v 0 + s}
  target := {y | 0 < y.val 0}
  map_source' := by
    intro v hv
    have hv' : 0 < v 0 + s := hv
    change 0 < (halfSpaceShiftFun s v).val 0
    rw [halfSpaceShiftFun_val hv'.le]
    simpa using hv'
  map_target' := by
    intro y hy
    have hy' : 0 < y.val 0 := hy
    change 0 < (y.val - EuclideanSpace.single 0 s : EuclideanSpace ℝ (Fin 3)) 0 + s
    simpa using hy'
  left_inv' := by
    intro v hv
    have hv' : 0 < v 0 + s := hv
    change (halfSpaceShiftFun s v).val - EuclideanSpace.single 0 s = v
    rw [halfSpaceShiftFun_val hv'.le, add_sub_cancel_right]
  right_inv' := by
    intro y _
    have h : 0 ≤ (y.val - EuclideanSpace.single 0 s : EuclideanSpace ℝ (Fin 3)) 0 + s := by
      simpa using y.2
    apply Subtype.ext
    rw [halfSpaceShiftFun_val h, sub_add_cancel]
  open_source := isOpen_lt continuous_const
    ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0).add continuous_const)
  open_target := isOpen_lt continuous_const
    ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0).comp continuous_subtype_val)
  continuousOn_toFun := by
    have hc : Continuous (fun v : {v : EuclideanSpace ℝ (Fin 3) | 0 < v 0 + s} =>
        (⟨v.val + EuclideanSpace.single 0 s, by simpa using v.2.le⟩ : EuclideanHalfSpace 3)) :=
      (continuous_subtype_val.add continuous_const).subtype_mk _
    rw [continuousOn_iff_continuous_domRestrict]
    refine hc.congr fun v => ?_
    apply Subtype.ext
    exact (halfSpaceShiftFun_val v.2.le).symm
  continuousOn_invFun := (Continuous.sub (f := fun y : EuclideanHalfSpace 3 => y.val)
    (g := fun _ => EuclideanSpace.single 0 s) continuous_subtype_val continuous_const).continuousOn

theorem halfSpaceShift_val {s : ℝ} {v : EuclideanSpace ℝ (Fin 3)} (h : 0 < v 0 + s) :
    (halfSpaceShift s v).val = v + EuclideanSpace.single 0 s :=
  halfSpaceShiftFun_val h.le

theorem halfSpaceShift_contMDiffOn (s : ℝ) :
    ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡∂ 3) ∞ (halfSpaceShift s)
      (halfSpaceShift s).source := by
  intro v hv
  have hv' : 0 < v 0 + s := hv
  apply ContMDiffAt.contMDiffWithinAt
  rw [contMDiffAt_iff]
  refine ⟨(halfSpaceShift s).continuousOn.continuousAt
    ((halfSpaceShift s).open_source.mem_nhds hv), ?_⟩
  simp only [extChartAt_self_eq, extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
    PartialEquiv.refl_coe, Function.comp_id, modelWithCornersSelf_coe, range_id, id_eq]
  apply ContDiffAt.contDiffWithinAt
  have ha : ContDiff ℝ ∞ (fun w : EuclideanSpace ℝ (Fin 3) => w + EuclideanSpace.single 0 s) :=
    contDiff_id.add contDiff_const
  apply ha.contDiffAt.congr_of_eventuallyEq
  filter_upwards [(halfSpaceShift s).open_source.mem_nhds hv] with w hw
  exact halfSpaceShift_val hw

theorem halfSpaceShift_symm_contMDiff (s : ℝ) :
    ContMDiff (𝓡∂ 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ (halfSpaceShift s).symm := by
  have h : ContMDiff (𝓡∂ 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
      (fun y : EuclideanHalfSpace 3 => (𝓡∂ 3) y - EuclideanSpace.single 0 s) :=
    (𝓡∂ 3).contMDiff.sub contMDiff_const
  exact h

theorem exists_isManifold_of_isOpenEmbedding_of_ballChart
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] {X : Type} [TopologicalSpace X]
    (U : TopologicalSpace.Opens M) (ι : M → X) (hι : IsOpenEmbedding (fun p : U => ι p.val))
    (κ : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin 3))) {R : ℝ}
    (hκt : κ.target = Metric.ball 0 R) (hcov : ∀ x, x ∈ ι '' U ∨ x ∈ κ.source)
    (hfwd : ∀ m ∈ U, ι m ∈ κ.source →
      ContMDiffAt (𝓡∂ 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ (fun m => κ (ι m)) m)
    (Θ : EuclideanSpace ℝ (Fin 3) → M)
    (hbwd : ∀ v ∈ κ.target, κ.symm v ∈ ι '' U →
      Θ v ∈ U ∧ κ.symm v = ι (Θ v) ∧
        ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡∂ 3) ∞ Θ v) :
    ∃ cs : ChartedSpace (EuclideanHalfSpace 3) X,
      letI := cs
      IsManifold (𝓡∂ 3) ∞ X ∧ (𝓡∂ 3).boundary X = ι '' (U ∩ (𝓡∂ 3).boundary M) := by
  classical
  have hshift : ∀ x ∈ κ.source, 0 < (κ x) 0 + (R + 1) := by
    intro x hx
    have hb : κ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R := hκt ▸ κ.map_source hx
    have h1 := PiLp.norm_apply_le (κ x) 0
    rw [Real.norm_eq_abs] at h1
    have h2 := neg_abs_le ((κ x) 0)
    rw [mem_ball_zero_iff] at hb
    linarith
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
  let chartC : OpenPartialHomeomorph X (EuclideanHalfSpace 3) :=
    κ.trans (halfSpaceShift (R + 1))
  have hCsrc : ∀ x ∈ κ.source, x ∈ chartC.source := fun x hx => ⟨hx, hshift x hx⟩
  let chartFn : X → OpenPartialHomeomorph X (EuclideanHalfSpace 3) := fun x =>
    if hx : x ∈ ι '' U then chartL ⟨hx.choose, hx.choose_spec.1⟩ else chartC
  let cs : ChartedSpace (EuclideanHalfSpace 3) X :=
    { atlas := range chartL ∪ {chartC}
      chartAt := chartFn
      mem_chart_source := fun x => by
        by_cases hx : x ∈ ι '' U
        · simp only [chartFn, dite_eq_left hx]
          exact ⟨_, mem_chart_source _ _, hx.choose_spec.2⟩
        · simp only [chartFn, dite_eq_right hx]
          exact hCsrc x ((hcov x).resolve_left hx)
      chart_mem_atlas := fun x => by
        by_cases hx : x ∈ ι '' U
        · simp only [chartFn, dite_eq_left hx]
          exact Or.inl ⟨_, rfl⟩
        · simp only [chartFn, dite_eq_right hx]
          exact Or.inr rfl }
  refine ⟨cs, ?_, ?_⟩
  · apply isManifold_of_contDiffOn (𝓡∂ 3) ∞ X
    intro e e' he he'
    have hT : ContMDiffOn (𝓡∂ 3) (𝓡∂ 3) ∞ (e.symm.trans e') (e.symm.trans e').source := by
      change e ∈ range chartL ∪ {chartC} at he
      change e' ∈ range chartL ∪ {chartC} at he'
      rcases he with ⟨p, rfl⟩ | he
      · rcases he' with ⟨q, rfl⟩ | he'
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
        · rw [mem_singleton_iff] at he'
          subst he'
          intro y hy
          apply ContMDiffAt.contMDiffWithinAt
          have hy1 : y ∈ (chartAt (EuclideanHalfSpace 3) p).target := hy.1
          have hmS : ι ((chartAt (EuclideanHalfSpace 3) p).symm y).val ∈ κ.source := hy.2.1
          have h1 : ContMDiffAt (𝓡∂ 3) (𝓡∂ 3) ∞ (chartAt (EuclideanHalfSpace 3) p).symm y :=
            (contMDiffOn_symm_of_mem_maximalAtlas
              (IsManifold.chart_mem_maximalAtlas p)).contMDiffAt
              ((chartAt (EuclideanHalfSpace 3) p).open_target.mem_nhds hy1)
          have h2 : ContMDiffAt (𝓡∂ 3) (𝓡∂ 3) ∞ (Subtype.val : U → M)
              ((chartAt (EuclideanHalfSpace 3) p).symm y) :=
            contMDiff_subtype_val.contMDiffAt
          have h3 := hfwd _ ((chartAt (EuclideanHalfSpace 3) p).symm y).2 hmS
          have h4 : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡∂ 3) ∞
              (halfSpaceShift (R + 1)) (κ (ι ((chartAt (EuclideanHalfSpace 3) p).symm y).val)) :=
            (halfSpaceShift_contMDiffOn _).contMDiffAt
              ((halfSpaceShift (R + 1)).open_source.mem_nhds (hshift _ hmS))
          have hc := h4.comp y (h3.comp y (h2.comp y h1))
          exact hc
      · rw [mem_singleton_iff] at he
        subst he
        rcases he' with ⟨q, rfl⟩ | he'
        · intro y hy
          apply ContMDiffAt.contMDiffWithinAt
          have key : ∀ y' ∈ (chartC.symm.trans (chartL q)).source,
              (halfSpaceShift (R + 1)).symm y' ∈ κ.target ∧
                κ.symm ((halfSpaceShift (R + 1)).symm y') ∈ ι '' U := by
            intro y' hy'
            obtain ⟨p', -, hpe⟩ := hy'.2
            exact ⟨hy'.1.2, ⟨p'.val, p'.2, hpe⟩⟩
          let ΘU : EuclideanSpace ℝ (Fin 3) → U := fun w =>
            if h : Θ w ∈ U then ⟨Θ w, h⟩ else q
          have heq : ∀ᶠ y' in 𝓝 y, (chartC.symm.trans (chartL q)) y' =
              ((chartAt (EuclideanHalfSpace 3) q) ∘ ΘU ∘ (halfSpaceShift (R + 1)).symm) y' := by
            filter_upwards [(chartC.symm.trans (chartL q)).open_source.mem_nhds hy] with y' hy'
            obtain ⟨hvt, hvU⟩ := key y' hy'
            obtain ⟨hΘU, hκ, -⟩ := hbwd _ hvt hvU
            have hk : ΘU ((halfSpaceShift (R + 1)).symm y') =
                ⟨Θ ((halfSpaceShift (R + 1)).symm y'), hΘU⟩ := dite_eq_left hΘU
            change (chartL q) (κ.symm ((halfSpaceShift (R + 1)).symm y')) = _
            rw [hκ, Function.comp_apply, Function.comp_apply, hk]
            exact OpenPartialHomeomorph.lift_openEmbedding_apply (chartAt (EuclideanHalfSpace 3) q)
              hι (x := ⟨Θ ((halfSpaceShift (R + 1)).symm y'), hΘU⟩)
          obtain ⟨hvt, hvU⟩ := key y hy
          obtain ⟨hΘU, hκ, hΘs⟩ := hbwd _ hvt hvU
          have hnbhd : ∀ᶠ w in 𝓝 ((halfSpaceShift (R + 1)).symm y), Θ w ∈ U := by
            filter_upwards [(κ.isOpen_inter_preimage_symm hιU).mem_nhds ⟨hvt, hvU⟩] with w hw
            exact (hbwd w hw.1 hw.2).1
          have hΘUat : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡∂ 3) ∞ ΘU
              ((halfSpaceShift (R + 1)).symm y) := by
            refine (ContMDiffAt.subtypeVal_comp_iff U ΘU _).mp ?_
            apply hΘs.congr_of_eventuallyEq
            filter_upwards [hnbhd] with w hw
            simp only [Function.comp_apply, ΘU, dite_eq_left hw]
          have hq' : ΘU ((halfSpaceShift (R + 1)).symm y) ∈
              (chartAt (EuclideanHalfSpace 3) q).source := by
            obtain ⟨p', hp', hpe⟩ := hy.2
            have hp'eq : p' = ΘU ((halfSpaceShift (R + 1)).symm y) := by
              rw [show ΘU ((halfSpaceShift (R + 1)).symm y) =
                ⟨Θ ((halfSpaceShift (R + 1)).symm y), hΘU⟩ from dite_eq_left hΘU]
              exact hι.injective (hpe.trans hκ)
            rw [← hp'eq]
            exact hp'
          have hT3 : ContMDiffAt (𝓡∂ 3) (𝓡∂ 3) ∞ (chartAt (EuclideanHalfSpace 3) q)
              (ΘU ((halfSpaceShift (R + 1)).symm y)) :=
            (contMDiffOn_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas q)).contMDiffAt
              ((chartAt (EuclideanHalfSpace 3) q).open_source.mem_nhds hq')
          have hT1 : ContMDiffAt (𝓡∂ 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
              (halfSpaceShift (R + 1)).symm y := (halfSpaceShift_symm_contMDiff _).contMDiffAt
          exact (hT3.comp y (hΘUat.comp y hT1)).congr_of_eventuallyEq heq
        · rw [mem_singleton_iff] at he'
          subst he'
          exact contMDiffOn_id.congr fun y hy => chartC.right_inv hy.1
    have hcoord := hT.comp ((𝓡∂ 3).contMDiffOn_symm.mono
      (inter_subset_right : (𝓡∂ 3).symm ⁻¹' (e.symm.trans e').source ∩ range (𝓡∂ 3) ⊆
        range (𝓡∂ 3))) (fun z hz => hz.1)
    exact ((𝓡∂ 3).contMDiff.comp_contMDiffOn hcoord).contDiffOn
  · ext x
    by_cases hx : x ∈ ι '' U
    · obtain ⟨m, hm, rfl⟩ := hx
      let p : U := ⟨m, hm⟩
      have hsrc : ι m ∈ (chartL p).source := ⟨p, mem_chart_source _ p, rfl⟩
      have h1 := isBoundaryPoint_iff_any_chart_real (𝓡∂ 3) hsrc
      have h2 := isBoundaryPoint_iff_any_chart_real (𝓡∂ 3)
        (mem_chart_source (EuclideanHalfSpace 3) m)
      have hval : (chartL p) (ι m) = chartAt (EuclideanHalfSpace 3) p p :=
        OpenPartialHomeomorph.lift_openEmbedding_apply (chartAt (EuclideanHalfSpace 3) p) hι
          (x := p)
      have hval2 : chartAt (EuclideanHalfSpace 3) p p = chartAt (EuclideanHalfSpace 3) m m := rfl
      change (𝓡∂ 3).IsBoundaryPoint (ι m) ↔ _
      rw [h1, hval, hval2, ← h2]
      constructor
      · intro hb
        exact ⟨m, ⟨hm, hb⟩, rfl⟩
      · rintro ⟨m', ⟨hm', hb⟩, he⟩
        have hmm : m' = m := congrArg Subtype.val
          (hι.injective (show ι (⟨m', hm'⟩ : U).val = ι (⟨m, hm⟩ : U).val from he))
        rwa [← hmm]
    · have hxS : x ∈ κ.source := (hcov x).resolve_left hx
      constructor
      · intro hb
        exfalso
        have h1 := (isBoundaryPoint_iff_any_chart_real (𝓡∂ 3) (hCsrc x hxS)).mp hb
        rw [frontier_range_modelWithCornersEuclideanHalfSpace] at h1
        have h3 : (𝓡∂ 3) (chartC x) = κ x + EuclideanSpace.single 0 (R + 1) :=
          halfSpaceShift_val (hshift x hxS)
        have h5 : (0 : ℝ) = ((𝓡∂ 3) (chartC x)) 0 := h1
        have h6 : (κ x + EuclideanSpace.single 0 (R + 1) : EuclideanSpace ℝ (Fin 3)) 0 =
            κ x 0 + (R + 1) := by simp
        rw [h3, h6] at h5
        linarith [hshift x hxS]
      · rintro ⟨m, ⟨hm, -⟩, rfl⟩
        exact absurd ⟨m, hm, rfl⟩ hx

theorem exists_capChart_of_radialCollar
    {M : Type} [TopologicalSpace M] [T2Space M]
    {A P : Type} [TopologicalSpace A] [TopologicalSpace P] [CompactSpace A] [T2Space P]
    {i : A → P} (hi : IsClosedEmbedding i) {ψ : A → M}
    (hψ : IsClosedEmbedding ψ) (Ext : P ≃ₜ ClosedCell 3)
    (hExt : ∀ z, ‖(Ext z : EuclideanSpace ℝ (Fin 3))‖ = 1 ↔ z ∈ range i)
    {a : ℝ} {V : Set M} {θ : M → EuclideanSpace ℝ (Fin 3)}
    {Θ : EuclideanSpace ℝ (Fin 3) → M} (ha : 0 < a) (hV : IsOpen V)
    (hθV : ∀ m ∈ V, 1 ≤ ‖θ m‖ ∧ ‖θ m‖ < 1 + a)
    (hΘV : ∀ v, 1 ≤ ‖v‖ → ‖v‖ < 1 + a → Θ v ∈ V)
    (hΘθ : ∀ m ∈ V, Θ (θ m) = m) (hθΘ : ∀ v, 1 ≤ ‖v‖ → ‖v‖ < 1 + a → θ (Θ v) = v)
    (hΘi : ∀ z, Θ (Ext (i z)) = ψ z) (hθc : ContinuousOn θ V)
    (hΘc : ContinuousOn Θ {v | 1 ≤ ‖v‖ ∧ ‖v‖ < 1 + a}) :
    ∃ κ : OpenPartialHomeomorph (AdjunctionSpace i ψ) (EuclideanSpace ℝ (Fin 3)),
      κ.target = Metric.ball 0 (1 + a) ∧
      κ.source = range (adjunctionCell i ψ) ∪ adjunctionLower ψ '' V ∧
      (∀ m, κ (adjunctionLower ψ m) = θ m) ∧
      (∀ v, ‖v‖ ≤ 1 → κ.symm v ∈ range (adjunctionCell i ψ)) ∧
      ∀ v, 1 < ‖v‖ → κ.symm v = adjunctionLower ψ (Θ v) := by
  classical
  have hExti : ∀ z, ‖(Ext (i z) : EuclideanSpace ℝ (Fin 3))‖ = 1 :=
    fun z => (hExt _).mpr ⟨z, rfl⟩
  have hθψ : ∀ z, θ (ψ z) = Ext (i z) := by
    intro z
    rw [← hΘi z]
    exact hθΘ _ (hExti z).ge (by rw [hExti z]; linarith)
  have hψV : ∀ z, ψ z ∈ V := by
    intro z
    rw [← hΘi z]
    exact hΘV _ (hExti z).ge (by rw [hExti z]; linarith)
  have hlowCE : IsClosedEmbedding (adjunctionLower (i := i) ψ) :=
    isClosedEmbedding_adjunctionLower i ψ hi.injective hψ.injective hi.continuous hψ.continuous
  have hcellCE : IsClosedEmbedding (adjunctionCell i ψ) :=
    isClosedEmbedding_adjunctionCell i ψ hi.injective hψ.injective hi.continuous hψ.continuous
  have hlowinj : Function.Injective (adjunctionLower (i := i) ψ) :=
    adjunctionLower_injective i ψ hi.injective
  have hcl : ∀ b m, adjunctionCell i ψ b = adjunctionLower ψ m → ∃ z, i z = b ∧ ψ z = m :=
    fun b m h => (adjunctionCell_eq_lower_iff i ψ hi.injective b m).mp h
  let C : Set (AdjunctionSpace i ψ) := range (adjunctionCell i ψ) ∪ adjunctionLower ψ '' V
  have hClow : ∀ m, adjunctionLower (i := i) ψ m ∈ C ↔ m ∈ V := by
    intro m
    constructor
    · rintro (⟨b, hb⟩ | ⟨m', hm', he⟩)
      · obtain ⟨z, -, hz⟩ := hcl b m hb
        rw [← hz]
        exact hψV z
      · rwa [hlowinj he] at hm'
    · intro hm
      exact Or.inr ⟨m, hm, rfl⟩
  have hq := isQuotientMap_adjunctionMk i ψ
  have hCopen : IsOpen C := by
    rw [← hq.isOpen_preimage, isOpen_sum_iff]
    constructor
    · have h : Sum.inl ⁻¹' (adjunctionMk i ψ ⁻¹' C) = univ :=
        eq_univ_of_forall fun b => Or.inl ⟨b, rfl⟩
      rw [h]
      exact isOpen_univ
    · have h : Sum.inr ⁻¹' (adjunctionMk i ψ ⁻¹' C) = V := by
        ext m
        exact hClow m
      rw [h]
      exact hV
  let κ : AdjunctionSpace i ψ → EuclideanSpace ℝ (Fin 3) :=
    Quot.lift (Sum.elim (fun b => (Ext b : EuclideanSpace ℝ (Fin 3))) θ) (by
      rintro _ _ ⟨z, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact (hθψ z).symm
      · exact hθψ z)
  have hκc : ∀ b, κ (adjunctionCell i ψ b) = Ext b := fun b => rfl
  let projCB : EuclideanSpace ℝ (Fin 3) → ClosedCell 3 := fun v =>
    ⟨(max 1 ‖v‖)⁻¹ • v, by
      have hpos : 0 < max 1 ‖v‖ := lt_of_lt_of_le one_pos (le_max_left _ _)
      rw [norm_smul, norm_inv, Real.norm_of_nonneg hpos.le, inv_mul_le_iff₀ hpos, mul_one]
      exact le_max_right _ _⟩
  have hprojC : Continuous projCB :=
    (((continuous_const.max continuous_norm).inv₀ fun v =>
      (lt_of_lt_of_le one_pos (le_max_left _ _)).ne').smul continuous_id).subtype_mk _
  have hproj1 : ∀ v : EuclideanSpace ℝ (Fin 3), ‖v‖ ≤ 1 →
      (projCB v : EuclideanSpace ℝ (Fin 3)) = v := by
    intro v hv
    change (max 1 ‖v‖)⁻¹ • v = v
    rw [max_eq_left hv, inv_one, one_smul]
  let κinv : EuclideanSpace ℝ (Fin 3) → AdjunctionSpace i ψ := fun v =>
    if ‖v‖ ≤ 1 then adjunctionCell i ψ (Ext.symm (projCB v)) else adjunctionLower ψ (Θ v)
  have hseam : ∀ v : EuclideanSpace ℝ (Fin 3), ‖v‖ = 1 →
      adjunctionCell i ψ (Ext.symm (projCB v)) = adjunctionLower ψ (Θ v) := by
    intro v hv
    have hE : (Ext (Ext.symm (projCB v)) : EuclideanSpace ℝ (Fin 3)) = v := by
      rw [Homeomorph.apply_symm_apply, hproj1 v hv.le]
    obtain ⟨z, hz⟩ := (hExt _).mp (by rw [hE, hv])
    rw [← hz, adjunction_coherence i ψ z, ← hΘi z, hz, hE]
  have hK1 : ∀ x ∈ C, κ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (1 + a) := by
    rintro _ (⟨b, rfl⟩ | ⟨m, hm, rfl⟩)
    · rw [mem_ball_zero_iff]
      exact lt_of_le_of_lt (Ext b).2 (by linarith)
    · rw [mem_ball_zero_iff]
      exact (hθV m hm).2
  have hK2 : ∀ x ∈ C, κinv (κ x) = x := by
    rintro _ (⟨b, rfl⟩ | ⟨m, hm, rfl⟩)
    · have hle : ‖(Ext b : EuclideanSpace ℝ (Fin 3))‖ ≤ 1 := (Ext b).2
      dsimp only [κinv]
      rw [hκc, ite_eq_left hle]
      have hp : projCB (Ext b) = Ext b := Subtype.ext (hproj1 _ hle)
      rw [hp, Homeomorph.symm_apply_apply]
    · dsimp only [κinv]
      change (if ‖θ m‖ ≤ 1 then adjunctionCell i ψ (Ext.symm (projCB (θ m)))
        else adjunctionLower ψ (Θ (θ m))) = adjunctionLower ψ m
      split_ifs with h
      · rw [hseam _ (le_antisymm h (hθV m hm).1), hΘθ m hm]
      · rw [hΘθ m hm]
  have hK3 : ∀ v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (1 + a),
      κinv v ∈ C ∧ κ (κinv v) = v := by
    intro v hv
    rw [mem_ball_zero_iff] at hv
    dsimp only [κinv]
    split_ifs with h
    · refine ⟨Or.inl ⟨_, rfl⟩, ?_⟩
      rw [hκc, Homeomorph.apply_symm_apply, hproj1 v h]
    · have h1 : 1 ≤ ‖v‖ := (not_le.mp h).le
      exact ⟨(hClow _).mpr (hΘV v h1 hv), hθΘ v h1 hv⟩
  have hκcell : ContinuousOn κ (range (adjunctionCell i ψ)) := by
    rw [← image_univ]
    exact hcellCE.isInducing.continuousOn_image_iff.mpr
      (continuous_subtype_val.comp Ext.continuous).continuousOn
  have hκlow : ContinuousOn κ (adjunctionLower ψ '' V) :=
    hlowCE.isInducing.continuousOn_image_iff.mpr hθc
  have hK4 : ContinuousOn κ C := by
    intro x hx
    have h1 : ContinuousWithinAt κ (range (adjunctionCell i ψ)) x := by
      by_cases hxc : x ∈ range (adjunctionCell i ψ)
      · exact hκcell x hxc
      · exact continuousWithinAt_of_notMem_closure (by rwa [hcellCE.isClosed_range.closure_eq])
    have h2 : ContinuousWithinAt κ (adjunctionLower ψ '' V) x := by
      by_cases hxl : x ∈ adjunctionLower ψ '' V
      · exact hκlow x hxl
      · apply continuousWithinAt_of_notMem_closure
        intro hcl'
        have hxr : x ∈ range (adjunctionLower (i := i) ψ) :=
          hlowCE.isClosed_range.closure_subset (closure_mono (image_subset_range _ _) hcl')
        obtain ⟨m, rfl⟩ := hxr
        exact hxl ⟨m, (hClow m).mp hx, rfl⟩
    exact h1.union h2
  have hK5 : ContinuousOn κinv (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (1 + a)) := by
    have hset : {v : EuclideanSpace ℝ (Fin 3) | ‖v‖ ≤ 1} = Metric.closedBall 0 1 := by
      ext v
      simp
    refine ContinuousOn.if (p := fun v => ‖v‖ ≤ 1)
      (f := fun v => adjunctionCell i ψ (Ext.symm (projCB v)))
      (g := fun v => adjunctionLower ψ (Θ v)) ?_ ?_ ?_
    · intro v hv
      have hv2 := hv.2
      rw [hset, frontier_closedBall (0 : EuclideanSpace ℝ (Fin 3)) one_ne_zero] at hv2
      exact hseam v (mem_sphere_zero_iff_norm.mp hv2)
    · exact ((continuous_adjunctionCell i ψ).comp
        (Ext.symm.continuous.comp hprojC)).continuousOn
    · have hsub : Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (1 + a) ∩
          closure {v : EuclideanSpace ℝ (Fin 3) | ¬ ‖v‖ ≤ 1} ⊆
          {v | 1 ≤ ‖v‖ ∧ ‖v‖ < 1 + a} := by
        intro v hv
        have hcl' : closure {v : EuclideanSpace ℝ (Fin 3) | ¬ ‖v‖ ≤ 1} ⊆ {v | 1 ≤ ‖v‖} :=
          closure_minimal (fun w hw => (not_le.mp hw).le)
            (isClosed_le continuous_const continuous_norm)
        exact ⟨hcl' hv.2, mem_ball_zero_iff.mp hv.1⟩
      exact (continuous_adjunctionLower i ψ).comp_continuousOn (hΘc.mono hsub)
  refine ⟨{ toFun := κ
            invFun := κinv
            source := C
            target := Metric.ball 0 (1 + a)
            map_source' := hK1
            map_target' := fun v hv => (hK3 v hv).1
            left_inv' := hK2
            right_inv' := fun v hv => (hK3 v hv).2
            open_source := hCopen
            open_target := Metric.isOpen_ball
            continuousOn_toFun := hK4
            continuousOn_invFun := hK5 }, rfl, rfl, fun m => rfl, fun v hv => ?_,
    fun v hv => ?_⟩
  · change κinv v ∈ _
    dsimp only [κinv]
    rw [ite_eq_left hv]
    exact ⟨_, rfl⟩
  · change κinv v = _
    dsimp only [κinv]
    rw [ite_eq_right (not_le.mpr hv)]

theorem isSmoothHandleStage_adjunction_of_radialCollar
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] [T2Space M] [CompactSpace M]
    {A P : Type} [TopologicalSpace A] [TopologicalSpace P] [CompactSpace A] [CompactSpace P]
    [T2Space P] {i : A → P} (hi : IsClosedEmbedding i) {ψ : A → M}
    (hψ : IsClosedEmbedding ψ) (Ext : P ≃ₜ ClosedCell 3)
    (hExt : ∀ z, ‖(Ext z : EuclideanSpace ℝ (Fin 3))‖ = 1 ↔ z ∈ range i)
    {a : ℝ} {V : Set M} {θ : M → EuclideanSpace ℝ (Fin 3)}
    {Θ : EuclideanSpace ℝ (Fin 3) → M} (ha : 0 < a) (hV : IsOpen V)
    (hθV : ∀ m ∈ V, 1 ≤ ‖θ m‖ ∧ ‖θ m‖ < 1 + a)
    (hΘV : ∀ v, 1 ≤ ‖v‖ → ‖v‖ < 1 + a → Θ v ∈ V)
    (hΘθ : ∀ m ∈ V, Θ (θ m) = m) (hθΘ : ∀ v, 1 ≤ ‖v‖ → ‖v‖ < 1 + a → θ (Θ v) = v)
    (hΘi : ∀ z, Θ (Ext (i z)) = ψ z)
    (hθs : ContMDiffOn (𝓡∂ 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ θ V)
    (hΘs : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡∂ 3) ∞ Θ
      {v | 1 ≤ ‖v‖ ∧ ‖v‖ < 1 + a}) :
    IsSmoothHandleStage (AdjunctionSpace i ψ)
      (adjunctionLower ψ '' ((𝓡∂ 3).boundary M \ range ψ)) := by
  classical
  obtain ⟨κ, hκt, hκs, hκl, hκin, hκout⟩ := exists_capChart_of_radialCollar hi hψ Ext hExt
    ha hV hθV hΘV hΘθ hθΘ hΘi hθs.continuousOn hΘs.continuousOn
  have hExti : ∀ z, ‖(Ext (i z) : EuclideanSpace ℝ (Fin 3))‖ = 1 :=
    fun z => (hExt _).mpr ⟨z, rfl⟩
  have hθψ : ∀ z, θ (ψ z) = Ext (i z) := by
    intro z
    rw [← hΘi z]
    exact hθΘ _ (hExti z).ge (by rw [hExti z]; linarith)
  have hψV : ∀ z, ψ z ∈ V := by
    intro z
    rw [← hΘi z]
    exact hΘV _ (hExti z).ge (by rw [hExti z]; linarith)
  have hT2 : T2Space (AdjunctionSpace i ψ) :=
    adjunction_t2Space i ψ hi.injective hψ.injective hi.continuous hψ.continuous
  have hlowCE : IsClosedEmbedding (adjunctionLower (i := i) ψ) :=
    isClosedEmbedding_adjunctionLower i ψ hi.injective hψ.injective hi.continuous hψ.continuous
  have hlowinj : Function.Injective (adjunctionLower (i := i) ψ) :=
    adjunctionLower_injective i ψ hi.injective
  have hcl : ∀ b m, adjunctionCell i ψ b = adjunctionLower ψ m → ∃ z, i z = b ∧ ψ z = m :=
    fun b m h => (adjunctionCell_eq_lower_iff i ψ hi.injective b m).mp h
  have hcover : ∀ x : AdjunctionSpace i ψ,
      x ∈ range (adjunctionCell i ψ) ∨ x ∈ range (adjunctionLower (i := i) ψ) := by
    intro x
    have hx : x ∈ range (adjunctionCell i ψ) ∪ range (adjunctionLower (i := i) ψ) := by
      rw [adjunction_inclusions_cover i ψ]
      trivial
    exact hx
  let Mc : TopologicalSpace.Opens M := ⟨(range ψ)ᶜ, hψ.isClosed_range.isOpen_compl⟩
  have hLlow : ∀ m, adjunctionLower (i := i) ψ m ∈ adjunctionLower ψ '' (Mc : Set M) ↔
      m ∉ range ψ := by
    intro m
    constructor
    · rintro ⟨m', hm', he⟩
      rw [hlowinj he] at hm'
      exact hm'
    · intro hm
      exact ⟨m, hm, rfl⟩
  have hLcell : ∀ b, adjunctionCell i ψ b ∉ adjunctionLower ψ '' (Mc : Set M) := by
    rintro b ⟨m, hm, he⟩
    obtain ⟨z, -, hz⟩ := hcl b m he.symm
    exact hm ⟨z, hz⟩
  have hLopen : IsOpen (adjunctionLower (i := i) ψ '' (Mc : Set M)) := by
    rw [← (isQuotientMap_adjunctionMk i ψ).isOpen_preimage, isOpen_sum_iff]
    constructor
    · have h : Sum.inl ⁻¹' (adjunctionMk i ψ ⁻¹' (adjunctionLower ψ '' (Mc : Set M))) = ∅ :=
        eq_empty_of_forall_notMem fun b hb => hLcell b hb
      rw [h]
      exact isOpen_empty
    · have h : Sum.inr ⁻¹' (adjunctionMk i ψ ⁻¹' (adjunctionLower ψ '' (Mc : Set M))) =
          (range ψ)ᶜ := by
        ext m
        exact hLlow m
      rw [h]
      exact hψ.isClosed_range.isOpen_compl
  have hLE : IsOpenEmbedding (fun p : Mc => adjunctionLower (i := i) ψ p.val) := by
    refine ⟨hlowCE.isEmbedding.comp IsEmbedding.subtypeVal, ?_⟩
    have h : range (fun p : Mc => adjunctionLower (i := i) ψ p.val) =
        adjunctionLower ψ '' (Mc : Set M) := by
      ext x
      constructor
      · rintro ⟨p, rfl⟩
        exact ⟨p.val, p.2, rfl⟩
      · rintro ⟨m, hm, rfl⟩
        exact ⟨⟨m, hm⟩, rfl⟩
    rw [h]
    exact hLopen
  have hΘout : ∀ w : EuclideanSpace ℝ (Fin 3), 1 < ‖w‖ → ‖w‖ < 1 + a → Θ w ∉ range ψ := by
    rintro w h1 h2 ⟨z, hz⟩
    have h := hθΘ w h1.le h2
    rw [← hz, hθψ z] at h
    have hn := hExti z
    rw [h] at hn
    linarith
  have hcov : ∀ x, x ∈ adjunctionLower ψ '' (Mc : Set M) ∨ x ∈ κ.source := by
    intro x
    rw [hκs]
    rcases hcover x with ⟨b, rfl⟩ | ⟨m, rfl⟩
    · exact Or.inr (Or.inl ⟨b, rfl⟩)
    · by_cases hm : m ∈ range ψ
      · obtain ⟨z, rfl⟩ := hm
        exact Or.inr (Or.inr ⟨ψ z, hψV z, rfl⟩)
      · exact Or.inl ⟨m, hm, rfl⟩
  have hfwd : ∀ m ∈ Mc, adjunctionLower (i := i) ψ m ∈ κ.source →
      ContMDiffAt (𝓡∂ 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
        (fun m => κ (adjunctionLower ψ m)) m := by
    intro m _ hmS
    rw [hκs] at hmS
    have hmV : m ∈ V := by
      rcases hmS with ⟨b, hb⟩ | ⟨m', hm', he⟩
      · obtain ⟨z, -, hz⟩ := hcl b m hb
        rw [← hz]
        exact hψV z
      · rwa [hlowinj he] at hm'
    have hfun : (fun m => κ (adjunctionLower ψ m)) = θ := funext hκl
    rw [hfun]
    exact hθs.contMDiffAt (hV.mem_nhds hmV)
  have hshellopen : IsOpen {w : EuclideanSpace ℝ (Fin 3) | 1 < ‖w‖ ∧ ‖w‖ < 1 + a} :=
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  have hbwd : ∀ v ∈ κ.target, κ.symm v ∈ adjunctionLower ψ '' (Mc : Set M) →
      Θ v ∈ Mc ∧ κ.symm v = adjunctionLower ψ (Θ v) ∧
        ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡∂ 3) ∞ Θ v := by
    intro v hv hvU
    rw [hκt, mem_ball_zero_iff] at hv
    have hv1 : 1 < ‖v‖ := by
      by_contra hle
      obtain ⟨b, hb⟩ := hκin v (not_lt.mp hle)
      rw [← hb] at hvU
      exact hLcell b hvU
    refine ⟨hΘout v hv1 hv, hκout v hv1, ?_⟩
    exact hΘs.contMDiffAt (Filter.mem_of_superset (hshellopen.mem_nhds ⟨hv1, hv⟩)
      fun w hw => ⟨hw.1.le, hw.2⟩)
  obtain ⟨cs, hman, hbd⟩ := exists_isManifold_of_isOpenEmbedding_of_ballChart Mc
    (adjunctionLower ψ) hLE κ hκt hcov hfwd Θ hbwd
  refine ⟨AdjunctionSpace i ψ, inferInstance, cs, hman, hT2, inferInstance,
    Homeomorph.refl _, ?_⟩
  have himg : ∀ s : Set (AdjunctionSpace i ψ), (Homeomorph.refl (AdjunctionSpace i ψ)) '' s = s :=
    fun s => image_id s
  rw [hbd, himg]
  congr 1
  ext m
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h2, h1⟩

end DifferentialGeometry.Topology.PiecewiseLinear
