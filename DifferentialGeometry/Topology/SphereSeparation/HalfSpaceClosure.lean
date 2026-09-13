import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import DifferentialGeometry.Topology.SphereSeparation.LocalNormalForm
import DifferentialGeometry.Topology.SphereSeparation.SmoothClosure

set_option autoImplicit false

open Function Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.SphereSeparation

namespace SphereSides

variable {X : Type*} [TopologicalSpace X]
  {S U V O : Set X} {p : X}

theorem local_halves_opposite_at (d : SphereSides S)
    (hpS : p ∈ S) (hU : IsConnected U) (hV : IsConnected V)
    (hUS : U ⊆ Sᶜ) (hVS : V ⊆ Sᶜ)
    (hOopen : IsOpen O) (hpO : p ∈ O)
    (hO : O ⊆ (U ∪ S) ∪ V) :
    Xor (U ⊆ d.compactSide ∧ V ⊆ d.endSide)
      (U ⊆ d.endSide ∧ V ⊆ d.compactSide) := by
  have not_both_compact :
      ¬ (U ⊆ d.compactSide ∧ V ⊆ d.compactSide) := by
    rintro ⟨hUB, hVB⟩
    have hpClosure : p ∈ closure d.endSide := by
      apply frontier_subset_closure
      simpa only [d.frontier_endSide] using hpS
    obtain ⟨y, hyO, hyE⟩ :=
      mem_closure_iff.1 hpClosure O hOopen hpO
    rcases hO hyO with (hyU | hyS) | hyV
    · exact Set.disjoint_left.1 d.disjoint (hUB hyU) hyE
    · exact Set.disjoint_left.1 d.endSide_disjoint_sphere hyE hyS
    · exact Set.disjoint_left.1 d.disjoint (hVB hyV) hyE
  have not_both_end :
      ¬ (U ⊆ d.endSide ∧ V ⊆ d.endSide) := by
    rintro ⟨hUE, hVE⟩
    have hpClosure : p ∈ closure d.compactSide := by
      apply frontier_subset_closure
      simpa only [d.frontier_compactSide] using hpS
    obtain ⟨y, hyO, hyB⟩ :=
      mem_closure_iff.1 hpClosure O hOopen hpO
    rcases hO hyO with (hyU | hyS) | hyV
    · exact Set.disjoint_left.1 d.disjoint hyB (hUE hyU)
    · exact Set.disjoint_left.1 d.compactSide_disjoint_sphere hyB hyS
    · exact Set.disjoint_left.1 d.disjoint hyB (hVE hyV)
  rcases d.subset_compactSide_or_subset_endSide
      hU.isPreconnected hUS with hUB | hUE
  · rcases d.subset_compactSide_or_subset_endSide
        hV.isPreconnected hVS with hVB | hVE
    · exact False.elim (not_both_compact ⟨hUB, hVB⟩)
    · refine Or.inl ⟨⟨hUB, hVE⟩, ?_⟩
      rintro ⟨hUE', _⟩
      obtain ⟨y, hyU⟩ := hU.nonempty
      exact Set.disjoint_left.1 d.disjoint (hUB hyU) (hUE' hyU)
  · rcases d.subset_compactSide_or_subset_endSide
        hV.isPreconnected hVS with hVB | hVE
    · refine Or.inr ⟨⟨hUE, hVB⟩, ?_⟩
      rintro ⟨hUB', _⟩
      obtain ⟨y, hyU⟩ := hU.nonempty
      exact Set.disjoint_left.1 d.disjoint (hUB' hyU) (hUE hyU)
    · exact False.elim (not_both_end ⟨hUE, hVE⟩)

end SphereSides

variable {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
  {e : SphereTwo → N}

theorem exists_oriented_embeddedSphereNormalChart
    (he : Manifold.IsSmoothEmbedding (𝓡 2)
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e)
    (d : SphereSides (Set.range e)) (x : SphereTwo) :
    ∃ c : EmbeddedSphereNormalChart e x,
      Xor
        (c.positiveHalf ⊆ d.compactSide ∧
          c.negativeHalf ⊆ d.endSide)
        (c.positiveHalf ⊆ d.endSide ∧
          c.negativeHalf ⊆ d.compactSide) := by
  obtain ⟨c, hpos, hneg⟩ :=
    exists_embeddedSphereNormalChart_connected_halves he x
  refine ⟨c, d.local_halves_opposite_at
    (p := e x) (O := c.neighborhood) ?_ hpos hneg
    c.positiveHalf_subset_compl_range
    c.negativeHalf_subset_compl_range c.isOpen_neighborhood
    c.image_mem_neighborhood ?_⟩
  · exact ⟨x, rfl⟩
  · rw [c.neighborhood_eq_halves_union_sphere]
    intro y hy
    rcases hy with (hyPos | ⟨hyO, hyS⟩) | hyNeg
    · exact Or.inl (Or.inl hyPos)
    · exact Or.inl (Or.inr hyS)
    · exact Or.inr hyNeg


inductive NormalOrientation where
  | positive
  | negative
  deriving DecidableEq

namespace NormalOrientation


def orient : NormalOrientation → ℝ → ℝ
  | .positive, t => t
  | .negative, t => -t


def continuousLinearEquiv : NormalOrientation → ℝ ≃L[ℝ] ℝ
  | .positive => ContinuousLinearEquiv.refl ℝ ℝ
  | .negative => ContinuousLinearEquiv.neg ℝ

@[simp] theorem continuousLinearEquiv_apply
    (o : NormalOrientation) (t : ℝ) :
    o.continuousLinearEquiv t = o.orient t := by
  cases o <;> rfl

noncomputable def tangentNormalEquiv
    (o : NormalOrientation) :
    (EuclideanSpace ℝ (Fin 2) × ℝ) ≃L[ℝ] EuclideanThree :=
  (ContinuousLinearEquiv.prodCongr
      (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 2)))
      o.continuousLinearEquiv).trans
    ((ContinuousLinearEquiv.prodCongr
        (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 2)))
        (PiLp.equivOfUnique 2 ℝ
          (fun _ : Fin 1 ↦ ℝ)).symm).trans
      ((ContinuousLinearEquiv.prodComm ℝ
          (EuclideanSpace ℝ (Fin 2))
          (EuclideanSpace ℝ (Fin 1))).trans
        (EuclideanSpace.finAddEquivProd
          (n := 1) (m := 2)).symm))

@[simp] theorem tangentNormalEquiv_zero_apply
    (o : NormalOrientation)
    (z : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    (o.tangentNormalEquiv (z, t)) 0 = o.orient t := by
  cases o <;> rfl

end NormalOrientation

namespace InteriorHalfSpace


noncomputable def setFirst (z : EuclideanThree) (a : ℝ) : EuclideanThree :=
  WithLp.toLp 2 (Function.update z.ofLp 0 a)

@[simp] theorem setFirst_zero (z : EuclideanThree) (a : ℝ) :
    setFirst z a 0 = a := by
  rfl

@[simp] theorem setFirst_apply_ne (z : EuclideanThree) (a : ℝ)
    {i : Fin 3} (hi : i ≠ 0) : setFirst z a i = z i := by
  simp [setFirst, hi]

theorem contDiff_setFirst_exp : ContDiff ℝ ∞
    (fun z : EuclideanThree ↦ setFirst z (Real.exp (z 0))) := by
  apply PiLp.contDiff_toLp.comp
  rw [contDiff_pi]
  intro i
  by_cases hi : i = 0
  · subst i
    simp only [Function.update, ↓reduceDIte]
    fun_prop
  · simp only [Function.update, hi, ↓reduceDIte]
    fun_prop

theorem contDiffOn_setFirst_log : ContDiffOn ℝ ∞
    (fun z : EuclideanThree ↦ setFirst z (Real.log (z 0)))
    {z | 0 < z 0} := by
  apply PiLp.contDiff_toLp.comp_contDiffOn
  rw [contDiffOn_pi]
  intro i
  by_cases hi : i = 0
  · subst i
    simp only [Function.update, ↓reduceDIte]
    intro z hz
    have hz0 : z 0 ≠ 0 := hz.ne'
    fun_prop
  · simp only [Function.update, hi, ↓reduceDIte]
    fun_prop

noncomputable def chart :
    OpenPartialHomeomorph EuclideanThree (EuclideanHalfSpace 3) where
  toFun z := ⟨setFirst z (Real.exp (z 0)), Real.exp_pos _ |>.le⟩
  invFun z := setFirst z.1 (Real.log (z.1 0))
  source := Set.univ
  target := {z | 0 < z.1 0}
  map_source' := fun _ _ ↦ Real.exp_pos _
  map_target' := fun _ _ ↦ Set.mem_univ _
  left_inv' := by
    intro z _
    ext i
    by_cases hi : i = 0
    · subst i
      simp [Real.log_exp]
    · simp [setFirst_apply_ne, hi]
  right_inv' := by
    intro z hz
    apply EuclideanHalfSpace.ext
    ext i
    by_cases hi : i = 0
    · subst i
      simp [Real.exp_log hz]
    · simp [setFirst_apply_ne, hi]
  continuousOn_toFun := by
    have hset : Continuous (fun z : EuclideanThree ↦
        setFirst z (Real.exp (z 0))) := by
      exact PiLp.continuous_toLp 2 (fun _ : Fin 3 ↦ ℝ) |>.comp <|
        (PiLp.continuous_ofLp 2 (fun _ : Fin 3 ↦ ℝ)).update 0
          (Real.continuous_exp.comp (PiLp.continuous_apply 2 _ 0))
    exact (hset.subtype_mk _).continuousOn
  continuousOn_invFun := by
    have hlog : ContinuousOn (fun z : EuclideanHalfSpace 3 ↦
        Real.log (z.1 0)) {z | 0 < z.1 0} :=
      Real.continuousOn_log.comp
        (((PiLp.continuous_apply 2 _ 0).comp
          continuous_subtype_val).continuousOn) (by
            intro z hz
            exact hz.ne' )
    have hupdate : ContinuousOn (fun z : EuclideanHalfSpace 3 ↦
        Function.update z.1.ofLp 0 (Real.log (z.1 0)))
        {z | 0 < z.1 0} := by
      rw [continuousOn_pi]
      intro i
      by_cases hi : i = 0
      · subst i
        simpa using hlog
      · simp only [Function.update, hi, ↓reduceDIte]
        have hval : Continuous
            (Subtype.val : EuclideanHalfSpace 3 → EuclideanThree) :=
          continuous_subtype_val
        exact ((PiLp.continuous_apply 2
          (fun _ : Fin 3 ↦ ℝ) i).comp hval).continuousOn
    exact (PiLp.continuous_toLp 2
      (fun _ : Fin 3 ↦ ℝ)).comp_continuousOn hupdate
  open_source := isOpen_univ
  open_target := isOpen_lt continuous_const
    ((PiLp.continuous_apply 2 _ 0).comp continuous_subtype_val)

@[simp] theorem chart_source : chart.source = Set.univ := rfl

@[simp] theorem chart_target : chart.target =
    {z : EuclideanHalfSpace 3 | 0 < z.1 0} := rfl

noncomputable def ambientChart :
    OpenPartialHomeomorph EuclideanThree EuclideanThree where
  toFun z := setFirst z (Real.exp (z 0))
  invFun z := setFirst z (Real.log (z 0))
  source := Set.univ
  target := {z | 0 < z 0}
  map_source' := fun _ _ ↦ Real.exp_pos _
  map_target' := fun _ _ ↦ Set.mem_univ _
  left_inv' := by
    intro z _
    ext i
    by_cases hi : i = 0
    · subst i
      simp [Real.log_exp]
    · simp [setFirst_apply_ne, hi]
  right_inv' := by
    intro z hz
    ext i
    by_cases hi : i = 0
    · subst i
      simp [Real.exp_log hz]
    · simp [setFirst_apply_ne, hi]
  continuousOn_toFun := contDiff_setFirst_exp.continuous.continuousOn
  continuousOn_invFun := contDiffOn_setFirst_log.continuousOn
  open_source := isOpen_univ
  open_target := isOpen_lt continuous_const
    (PiLp.continuous_apply 2 _ 0)

theorem ambientChart_mem_contDiffGroupoid :
    ambientChart ∈ contDiffGroupoid ∞
      (modelWithCornersSelf ℝ EuclideanThree) := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  constructor
  · simp only [contDiffPregroupoid,
      modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id,
      preimage_id_eq, range_id, inter_univ, id_eq]
    apply contDiff_setFirst_exp.contDiffOn.congr
    intro z _
    rfl
  · simp only [contDiffPregroupoid,
      modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id,
      preimage_id_eq, range_id, inter_univ, id_eq]
    apply contDiffOn_setFirst_log.congr
    intro z _
    rfl

theorem trans_mem_maximalAtlas
    {X : Type*} [TopologicalSpace X] [ChartedSpace EuclideanThree X]
    (a : OpenPartialHomeomorph X EuclideanThree)
    (ha : a ∈ IsManifold.maximalAtlas
      (modelWithCornersSelf ℝ EuclideanThree) ∞ X)
    (f : OpenPartialHomeomorph EuclideanThree EuclideanThree)
    (hf : f ∈ contDiffGroupoid ∞
      (modelWithCornersSelf ℝ EuclideanThree)) :
    a.trans f ∈ IsManifold.maximalAtlas
      (modelWithCornersSelf ℝ EuclideanThree) ∞ X := by
  let G := contDiffGroupoid ∞
    (modelWithCornersSelf ℝ EuclideanThree)
  change a.trans f ∈ G.maximalAtlas X
  intro a' ha'
  have hleft := (ha a' ha').1
  have hright := (ha a' ha').2
  constructor
  · rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc]
    exact G.trans (G.symm hf) hleft
  · rw [← OpenPartialHomeomorph.trans_assoc]
    exact G.trans hright hf

theorem contDiffOn_interiorized_transition
    {X : Type*} [TopologicalSpace X]
    (a b : OpenPartialHomeomorph X EuclideanThree)
    (hm : ContDiffOn ℝ ∞ (a.symm.trans b) (a.symm.trans b).source) :
    let t := (a.trans chart).symm.trans (b.trans chart)
    ContDiffOn ℝ ∞ ((𝓡∂ 3) ∘ t ∘ (𝓡∂ 3).symm)
      ((𝓡∂ 3).symm ⁻¹' t.source ∩ Set.range (𝓡∂ 3)) := by
  intro t
  let F : EuclideanThree → EuclideanThree := fun z ↦
    setFirst z (Real.exp (z 0))
  let G : EuclideanThree → EuclideanThree := fun z ↦
    setFirst z (Real.log (z 0))
  let m := a.symm.trans b
  let D := (𝓡∂ 3).symm ⁻¹' t.source ∩ Set.range (𝓡∂ 3)
  have hpositive : D ⊆ {z : EuclideanThree | 0 < z 0} := by
    intro z hz
    have ht : (𝓡∂ 3).symm z ∈ t.source := hz.1
    change (𝓡∂ 3).symm z ∈
      ((a.trans chart).symm.trans (b.trans chart)).source at ht
    have hfirst : (𝓡∂ 3).symm z ∈ (a.trans chart).target := by
      rw [OpenPartialHomeomorph.trans_source] at ht
      exact ht.1
    rw [OpenPartialHomeomorph.trans_target] at hfirst
    have htarget : (𝓡∂ 3).symm z ∈ chart.target := hfirst.1
    have hval : ((𝓡∂ 3).symm z).1 = z :=
      (𝓡∂ 3).right_inv hz.2
    change 0 < ((𝓡∂ 3).symm z).1 0 at htarget
    rwa [hval] at htarget
  have hmaps : MapsTo G D m.source := by
    intro z hz
    have ht : (𝓡∂ 3).symm z ∈ t.source := hz.1
    change (𝓡∂ 3).symm z ∈
      ((a.trans chart).symm.trans (b.trans chart)).source at ht
    have hval : ((𝓡∂ 3).symm z).1 = z :=
      (𝓡∂ 3).right_inv hz.2
    rw [OpenPartialHomeomorph.trans_source] at ht
    have haTarget' : (𝓡∂ 3).symm z ∈ (a.trans chart).target := by
      exact ht.1
    rw [OpenPartialHomeomorph.trans_target] at haTarget'
    have haTarget : chart.symm ((𝓡∂ 3).symm z) ∈ a.target :=
      haTarget'.2
    have hbSource' :
        (a.trans chart).symm ((𝓡∂ 3).symm z) ∈
          (b.trans chart).source := ht.2
    rw [OpenPartialHomeomorph.trans_source] at hbSource'
    have hbSource :
        a.symm (chart.symm ((𝓡∂ 3).symm z)) ∈ b.source := by
      simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_apply] using hbSource'.1
    change setFirst ((𝓡∂ 3).symm z).1
      (Real.log (((𝓡∂ 3).symm z).1 0)) ∈ a.target at haTarget
    change a.symm (setFirst ((𝓡∂ 3).symm z).1
      (Real.log (((𝓡∂ 3).symm z).1 0))) ∈ b.source at hbSource
    rw [hval] at haTarget hbSource
    change G z ∈ a.target ∩ a.symm ⁻¹' b.source
    constructor
    · exact haTarget
    · exact hbSource
  have hcomp : ContDiffOn ℝ ∞ (F ∘ m ∘ G) D :=
    contDiff_setFirst_exp.comp_contDiffOn
      (hm.comp
        (contDiffOn_setFirst_log.mono hpositive) hmaps)
  apply hcomp.congr
  intro z hz
  have hval : ((𝓡∂ 3).symm z).1 = z :=
    (𝓡∂ 3).right_inv hz.2
  change (((𝓡∂ 3) ∘ t ∘ (𝓡∂ 3).symm) z) =
    ((F ∘ m ∘ G) z)
  simp only [Function.comp_apply]
  change ((𝓡∂ 3)
      (((a.trans chart).symm.trans (b.trans chart)) ((𝓡∂ 3).symm z))) =
    ((F ∘ m ∘ G) z)
  rw [OpenPartialHomeomorph.trans_apply,
    OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.trans_apply,
    OpenPartialHomeomorph.trans_apply]
  have hin : chart.symm ((𝓡∂ 3).symm z) = G z := by
    change setFirst ((𝓡∂ 3).symm z).1
      (Real.log (((𝓡∂ 3).symm z).1 0)) = G z
    simp only [G]
    rw [hval]
  rw [hin]
  rfl

theorem interiorized_transition_mem_contDiffGroupoid
    {X : Type*} [TopologicalSpace X]
    (a b : OpenPartialHomeomorph X EuclideanThree)
    (hab : ContDiffOn ℝ ∞ (a.symm.trans b) (a.symm.trans b).source)
    (hba : ContDiffOn ℝ ∞ (b.symm.trans a) (b.symm.trans a).source) :
    (a.trans chart).symm.trans (b.trans chart) ∈
      contDiffGroupoid ∞ (𝓡∂ 3) := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  constructor
  · exact contDiffOn_interiorized_transition a b hab
  · let t := (a.trans chart).symm.trans (b.trans chart)
    change ContDiffOn ℝ ∞ ((𝓡∂ 3) ∘ t.symm ∘ (𝓡∂ 3).symm)
      ((𝓡∂ 3).symm ⁻¹' t.target ∩ Set.range (𝓡∂ 3))
    rw [← OpenPartialHomeomorph.symm_source t,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm]
    exact contDiffOn_interiorized_transition b a hba

end InteriorHalfSpace

namespace SideInteriorChart

variable {B : Set N}


def inclusion : B → closure B :=
  Set.inclusion subset_closure

omit [ChartedSpace EuclideanThree N] in
theorem isOpenEmbedding_inclusion (hB : IsOpen B) :
    Topology.IsOpenEmbedding (inclusion : B → closure B) :=
  Topology.IsOpenEmbedding.inclusion subset_closure
    (hB.preimage continuous_subtype_val)


noncomputable def ambientChart (hB : IsOpen B)
    (p : closure B) (hp : p.1 ∈ B) :
    OpenPartialHomeomorph B EuclideanThree := by
  let U : TopologicalSpace.Opens N := ⟨B, hB⟩
  let pU : U := ⟨p.1, hp⟩
  exact (chartAt EuclideanThree p.1).subtypeRestr ⟨pU⟩

noncomputable def liftedChart (hB : IsOpen B)
    (p : closure B) (hp : p.1 ∈ B) :
    OpenPartialHomeomorph (closure B) EuclideanThree :=
  (ambientChart hB p hp).lift_openEmbedding
    (isOpenEmbedding_inclusion hB)

theorem mem_liftedChart_source_iff (hB : IsOpen B)
    (p y : closure B) (hp : p.1 ∈ B) :
    y ∈ (liftedChart hB p hp).source ↔
      y.1 ∈ B ∧ y.1 ∈ (chartAt EuclideanThree p.1).source := by
  rw [liftedChart, OpenPartialHomeomorph.lift_openEmbedding_source]
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u.2, ?_⟩
    simpa [ambientChart, inclusion,
      OpenPartialHomeomorph.subtypeRestr_source] using hu
  · rintro ⟨hyB, hyChart⟩
    let u : B := ⟨y.1, hyB⟩
    refine ⟨u, ?_, ?_⟩
    · simpa [ambientChart, inclusion,
        OpenPartialHomeomorph.subtypeRestr_source] using hyChart
    · exact Subtype.ext rfl

theorem liftedChart_apply (hB : IsOpen B)
    (p y : closure B) (hp : p.1 ∈ B) (hy : y.1 ∈ B) :
    liftedChart hB p hp y = chartAt EuclideanThree p.1 y.1 := by
  let u : B := ⟨y.1, hy⟩
  have huy : inclusion u = y := Subtype.ext rfl
  rw [← huy, liftedChart,
    OpenPartialHomeomorph.lift_openEmbedding_apply]
  rfl

theorem liftedChart_symm_coe (hB : IsOpen B)
    (p : closure B) (hp : p.1 ∈ B) {z : EuclideanThree}
    (hz : z ∈ (liftedChart hB p hp).target) :
    ((liftedChart hB p hp).symm z).1 =
      (chartAt EuclideanThree p.1).symm z := by
  let U : TopologicalSpace.Opens N := ⟨B, hB⟩
  let pU : U := ⟨p.1, hp⟩
  have hz' : z ∈ (ambientChart hB p hp).target := by
    simpa only [liftedChart,
      OpenPartialHomeomorph.lift_openEmbedding_target] using hz
  change ((ambientChart hB p hp).symm z).1 =
    (chartAt EuclideanThree p.1).symm z
  exact (chartAt EuclideanThree p.1).subtypeRestr_symm_apply
    ⟨pU⟩ (by simpa only [ambientChart] using hz')

theorem liftedChart_target_subset_chart_target (hB : IsOpen B)
    (p : closure B) (hp : p.1 ∈ B) :
    (liftedChart hB p hp).target ⊆
      (chartAt EuclideanThree p.1).target := by
  let U : TopologicalSpace.Opens N := ⟨B, hB⟩
  let pU : U := ⟨p.1, hp⟩
  intro z hz
  have hz' : z ∈ (ambientChart hB p hp).target := by
    simpa only [liftedChart,
      OpenPartialHomeomorph.lift_openEmbedding_target] using hz
  exact (chartAt EuclideanThree p.1).subtypeRestr_target_subset
    ⟨pU⟩ (by simpa only [ambientChart] using hz')

noncomputable def chart (hB : IsOpen B) (p : closure B) (hp : p.1 ∈ B) :
    OpenPartialHomeomorph (closure B) (EuclideanHalfSpace 3) :=
  (liftedChart hB p hp).trans InteriorHalfSpace.chart


theorem chart_transition_mem_contDiffGroupoid
    [IsManifold (modelWithCornersSelf ℝ EuclideanThree) ∞ N]
    (hB : IsOpen B) (p q : closure B)
    (hp : p.1 ∈ B) (hq : q.1 ∈ B) :
    (chart hB p hp).symm.trans (chart hB q hq) ∈
      contDiffGroupoid ∞ (𝓡∂ 3) := by
  let U : TopologicalSpace.Opens N := ⟨B, hB⟩
  let _ : ChartedSpace EuclideanThree B :=
    TopologicalSpace.Opens.instChartedSpace U
  let _ : HasGroupoid B
      (contDiffGroupoid ∞ (modelWithCornersSelf ℝ EuclideanThree)) :=
    TopologicalSpace.Opens.instHasGroupoid
      (contDiffGroupoid ∞ (modelWithCornersSelf ℝ EuclideanThree)) U
  let pU : U := ⟨p.1, hp⟩
  let qU : U := ⟨q.1, hq⟩
  let a := ambientChart hB p hp
  let b := ambientChart hB q hq
  have ha : a ∈ atlas EuclideanThree U := by
    simpa only [a, ambientChart,
      TopologicalSpace.Opens.chartAt_eq] using
        (chart_mem_atlas EuclideanThree pU)
  have hb : b ∈ atlas EuclideanThree U := by
    simpa only [b, ambientChart,
      TopologicalSpace.Opens.chartAt_eq] using
        (chart_mem_atlas EuclideanThree qU)
  have habG : a.symm.trans b ∈
      contDiffGroupoid ∞ (modelWithCornersSelf ℝ EuclideanThree) :=
    (contDiffGroupoid ∞
      (modelWithCornersSelf ℝ EuclideanThree)).compatible ha hb
  have hbaG : b.symm.trans a ∈
      contDiffGroupoid ∞ (modelWithCornersSelf ℝ EuclideanThree) :=
    (contDiffGroupoid ∞
      (modelWithCornersSelf ℝ EuclideanThree)).compatible hb ha
  have hab := (mem_groupoid_of_pregroupoid.mp habG).1
  have hba := (mem_groupoid_of_pregroupoid.mp hbaG).1
  have hab' : ContDiffOn ℝ ∞ (a.symm.trans b)
      (a.symm.trans b).source := by
    simpa only [contDiffPregroupoid, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id,
      preimage_id_eq, range_id, inter_univ, id_eq] using hab
  have hba' : ContDiffOn ℝ ∞ (b.symm.trans a)
      (b.symm.trans a).source := by
    simpa only [contDiffPregroupoid, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id,
      preimage_id_eq, range_id, inter_univ, id_eq] using hba
  change ((liftedChart hB p hp).trans InteriorHalfSpace.chart).symm.trans
      ((liftedChart hB q hq).trans InteriorHalfSpace.chart) ∈
    contDiffGroupoid ∞ (𝓡∂ 3)
  apply InteriorHalfSpace.interiorized_transition_mem_contDiffGroupoid
  · rw [liftedChart, liftedChart,
      OpenPartialHomeomorph.lift_openEmbedding_trans]
    exact hab'
  · rw [liftedChart, liftedChart,
      OpenPartialHomeomorph.lift_openEmbedding_trans]
    exact hba'

theorem mem_chart_source (hB : IsOpen B) (p : closure B) (hp : p.1 ∈ B) :
    p ∈ (chart hB p hp).source := by
  let U : TopologicalSpace.Opens N := ⟨B, hB⟩
  let pU : U := ⟨p.1, hp⟩
  let hU : Nonempty U := ⟨pU⟩
  let c : OpenPartialHomeomorph U EuclideanThree :=
    (chartAt EuclideanThree p.1).subtypeRestr hU
  have hpC : pU ∈ c.source := by
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact _root_.mem_chart_source EuclideanThree p.1
  change p ∈ ((c.lift_openEmbedding (f := inclusion)
    (isOpenEmbedding_inclusion hB)).trans InteriorHalfSpace.chart).source
  rw [OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.lift_openEmbedding_source]
  refine ⟨⟨pU, hpC, ?_⟩, ?_⟩
  · exact Subtype.ext rfl
  · exact Set.mem_univ _

theorem chart_apply_zero_pos (hB : IsOpen B) (p : closure B)
    (hp : p.1 ∈ B) :
    0 < ((chart hB p hp) p).1 0 := by
  have hout := (chart hB p hp).map_source (mem_chart_source hB p hp)
  rw [chart, OpenPartialHomeomorph.trans_target] at hout
  exact hout.1

end SideInteriorChart

structure EmbeddedSphereSideNormalChart
    (e : SphereTwo → N) (B : Set N) (x : SphereTwo) where
  base : EmbeddedSphereNormalChart e x
  orientation : NormalOrientation
  mem_side_iff_oriented_pos : ∀ {y : N}, y ∈ base.neighborhood →
    (y ∈ B ↔ 0 < orientation.orient (base.normalCoordinate y))
  mem_closure_iff_oriented_nonneg : ∀ {y : N}, y ∈ base.neighborhood →
    (y ∈ closure B ↔ 0 ≤ orientation.orient (base.normalCoordinate y))

namespace EmbeddedSphereSideNormalChart

private noncomputable def ofPositive
    {B C : Set N} {x : SphereTwo}
    (c : EmbeddedSphereNormalChart e x)
    (hBcompl : B ⊆ (Set.range e)ᶜ)
    (hPos : c.positiveHalf ⊆ B)
    (hNeg : c.negativeHalf ⊆ C)
    (hdisjoint : Disjoint B C)
    (hclosure : closure B = B ∪ Set.range e) :
    EmbeddedSphereSideNormalChart e B x where
  base := c
  orientation := .positive
  mem_side_iff_oriented_pos := by
    intro y hy
    change y ∈ B ↔ 0 < c.normalCoordinate y
    constructor
    · intro hyB
      have hyNotRange : y ∉ Set.range e := hBcompl hyB
      have hyDiff : y ∈ c.neighborhood \ Set.range e :=
        ⟨hy, hyNotRange⟩
      rw [c.neighborhood_diff_range_eq_halves] at hyDiff
      rcases hyDiff with hyPos | hyNeg
      · exact hyPos.2
      · exact False.elim
          (Set.disjoint_left.1 hdisjoint hyB (hNeg hyNeg))
    · intro hyPos
      exact hPos ⟨hy, hyPos⟩
  mem_closure_iff_oriented_nonneg := by
    intro y hy
    change y ∈ closure B ↔ 0 ≤ c.normalCoordinate y
    rw [hclosure]
    constructor
    · rintro (hyB | hyS)
      · have hyNotRange : y ∉ Set.range e := hBcompl hyB
        have hyDiff : y ∈ c.neighborhood \ Set.range e :=
          ⟨hy, hyNotRange⟩
        rw [c.neighborhood_diff_range_eq_halves] at hyDiff
        rcases hyDiff with hyPos | hyNeg
        · exact hyPos.2.le
        · exact False.elim
            (Set.disjoint_left.1 hdisjoint hyB (hNeg hyNeg))
      · exact (c.normalCoordinate_eq_zero_iff hy).2 hyS |>.ge
    · intro hnonneg
      rcases hnonneg.eq_or_lt with hzero | hpos
      · exact Or.inr ((c.normalCoordinate_eq_zero_iff hy).1 hzero.symm)
      · exact Or.inl (hPos ⟨hy, hpos⟩)

private noncomputable def ofNegative
    {B C : Set N} {x : SphereTwo}
    (c : EmbeddedSphereNormalChart e x)
    (hBcompl : B ⊆ (Set.range e)ᶜ)
    (hNeg : c.negativeHalf ⊆ B)
    (hPos : c.positiveHalf ⊆ C)
    (hdisjoint : Disjoint B C)
    (hclosure : closure B = B ∪ Set.range e) :
    EmbeddedSphereSideNormalChart e B x where
  base := c
  orientation := .negative
  mem_side_iff_oriented_pos := by
    intro y hy
    change y ∈ B ↔ 0 < -c.normalCoordinate y
    rw [neg_pos]
    constructor
    · intro hyB
      have hyNotRange : y ∉ Set.range e := hBcompl hyB
      have hyDiff : y ∈ c.neighborhood \ Set.range e :=
        ⟨hy, hyNotRange⟩
      rw [c.neighborhood_diff_range_eq_halves] at hyDiff
      rcases hyDiff with hyPos | hyNeg
      · exact False.elim
          (Set.disjoint_left.1 hdisjoint hyB (hPos hyPos))
      · exact hyNeg.2
    · intro hyNeg
      exact hNeg ⟨hy, hyNeg⟩
  mem_closure_iff_oriented_nonneg := by
    intro y hy
    change y ∈ closure B ↔ 0 ≤ -c.normalCoordinate y
    rw [hclosure, neg_nonneg]
    constructor
    · rintro (hyB | hyS)
      · have hyNotRange : y ∉ Set.range e := hBcompl hyB
        have hyDiff : y ∈ c.neighborhood \ Set.range e :=
          ⟨hy, hyNotRange⟩
        rw [c.neighborhood_diff_range_eq_halves] at hyDiff
        rcases hyDiff with hyPos | hyNeg
        · exact False.elim
            (Set.disjoint_left.1 hdisjoint hyB (hPos hyPos))
        · exact hyNeg.2.le
      · exact (c.normalCoordinate_eq_zero_iff hy).2 hyS |>.le
    · intro hnonpos
      rcases hnonpos.eq_or_lt with hzero | hneg
      · exact Or.inr ((c.normalCoordinate_eq_zero_iff hy).1 hzero)
      · exact Or.inl (hNeg ⟨hy, hneg⟩)

end EmbeddedSphereSideNormalChart

theorem compactSideNormalChart_nonempty
    (he : Manifold.IsSmoothEmbedding (𝓡 2)
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e)
    (d : SphereSides (Set.range e)) (x : SphereTwo) :
    Nonempty (EmbeddedSphereSideNormalChart e d.compactSide x) := by
  obtain ⟨c, hc⟩ := exists_oriented_embeddedSphereNormalChart he d x
  rcases hc with ⟨hc, _⟩ | ⟨hc, _⟩
  · exact ⟨EmbeddedSphereSideNormalChart.ofPositive c
      d.compactSide_subset_compl hc.1 hc.2 d.disjoint
      d.closure_compactSide⟩
  · exact ⟨EmbeddedSphereSideNormalChart.ofNegative c
      d.compactSide_subset_compl hc.2 hc.1 d.disjoint
      d.closure_compactSide⟩

theorem endSideNormalChart_nonempty
    (he : Manifold.IsSmoothEmbedding (𝓡 2)
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e)
    (d : SphereSides (Set.range e)) (x : SphereTwo) :
    Nonempty (EmbeddedSphereSideNormalChart e d.endSide x) := by
  obtain ⟨c, hc⟩ := exists_oriented_embeddedSphereNormalChart he d x
  rcases hc with ⟨hc, _⟩ | ⟨hc, _⟩
  · exact ⟨EmbeddedSphereSideNormalChart.ofNegative c
      d.endSide_subset_compl hc.2 hc.1 d.disjoint.symm
      d.closure_endSide⟩
  · exact ⟨EmbeddedSphereSideNormalChart.ofPositive c
      d.endSide_subset_compl hc.1 hc.2 d.disjoint.symm
      d.closure_endSide⟩

namespace EmbeddedSphereSideNormalChart

variable {B : Set N} {x : SphereTwo}

noncomputable def coordinate
    (c : EmbeddedSphereSideNormalChart e B x) (y : N) : EuclideanThree :=
  c.orientation.tangentNormalEquiv
    (c.base.normalForm.equiv.symm (c.base.normalForm.codChart y))

@[simp] theorem coordinate_zero_apply
    (c : EmbeddedSphereSideNormalChart e B x) (y : N) :
    c.coordinate y 0 =
      c.orientation.orient (c.base.normalCoordinate y) := by
  exact c.orientation.tangentNormalEquiv_zero_apply
    (c.base.normalForm.equiv.symm (c.base.normalForm.codChart y)).1
    (c.base.normalForm.equiv.symm (c.base.normalForm.codChart y)).2

noncomputable def coordinateTarget
    (c : EmbeddedSphereSideNormalChart e B x) : Set EuclideanThree :=
  c.coordinate '' c.base.neighborhood

theorem isOpen_coordinateTarget
    (c : EmbeddedSphereSideNormalChart e B x) :
    IsOpen c.coordinateTarget := by
  let h := c.base.normalForm
  have hchart : IsOpen (h.codChart '' c.base.neighborhood) :=
    h.codChart.isOpen_image_of_subset_source c.base.isOpen_neighborhood
      c.base.neighborhood_subset_codChart_source
  have heq : c.coordinateTarget =
      c.orientation.tangentNormalEquiv ''
        (h.equiv.symm '' (h.codChart '' c.base.neighborhood)) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨h.equiv.symm (h.codChart y),
        ⟨h.codChart y, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
    · rintro ⟨w, ⟨v, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
      exact ⟨y, hy, rfl⟩
  rw [heq]
  exact c.orientation.tangentNormalEquiv.toHomeomorph.isOpen_image.2
    (h.equiv.symm.toHomeomorph.isOpen_image.2 hchart)

theorem coordinate_mem_target
    (c : EmbeddedSphereSideNormalChart e B x) {y : N}
    (hy : y ∈ c.base.neighborhood) :
    c.coordinate y ∈ c.coordinateTarget :=
  ⟨y, hy, rfl⟩

theorem mem_closure_iff_coordinate_nonneg
    (c : EmbeddedSphereSideNormalChart e B x) {y : N}
    (hy : y ∈ c.base.neighborhood) :
    y ∈ closure B ↔ 0 ≤ c.coordinate y 0 := by
  rw [c.coordinate_zero_apply]
  exact c.mem_closure_iff_oriented_nonneg hy

theorem mem_side_iff_coordinate_pos
    (c : EmbeddedSphereSideNormalChart e B x) {y : N}
    (hy : y ∈ c.base.neighborhood) :
    y ∈ B ↔ 0 < c.coordinate y 0 := by
  rw [c.coordinate_zero_apply]
  exact c.mem_side_iff_oriented_pos hy


noncomputable def coordinateInv
    (c : EmbeddedSphereSideNormalChart e B x) (z : EuclideanThree) : N :=
  c.base.normalForm.codChart.symm
    (c.base.normalForm.equiv
      (c.orientation.tangentNormalEquiv.symm z))

theorem coordinateInv_coordinate
    (c : EmbeddedSphereSideNormalChart e B x) {y : N}
    (hy : y ∈ c.base.neighborhood) :
    c.coordinateInv (c.coordinate y) = y := by
  rw [coordinateInv, coordinate,
    c.orientation.tangentNormalEquiv.symm_apply_apply,
    c.base.normalForm.equiv.apply_symm_apply]
  exact c.base.normalForm.codChart.left_inv
    (c.base.neighborhood_subset_codChart_source hy)

theorem coordinate_coordinateInv
    (c : EmbeddedSphereSideNormalChart e B x) {z : EuclideanThree}
    (hz : z ∈ c.coordinateTarget) :
    c.coordinate (c.coordinateInv z) = z := by
  rcases hz with ⟨y, hy, rfl⟩
  rw [c.coordinateInv_coordinate hy]

theorem coordinateInv_mem_neighborhood
    (c : EmbeddedSphereSideNormalChart e B x) {z : EuclideanThree}
    (hz : z ∈ c.coordinateTarget) :
    c.coordinateInv z ∈ c.base.neighborhood := by
  rcases hz with ⟨y, hy, rfl⟩
  rwa [c.coordinateInv_coordinate hy]

theorem continuousOn_coordinate
    (c : EmbeddedSphereSideNormalChart e B x) :
    ContinuousOn c.coordinate c.base.neighborhood := by
  have hchart := c.base.normalForm.codChart.continuousOn.mono
    c.base.neighborhood_subset_codChart_source
  have hequiv := c.base.normalForm.equiv.symm.continuous.comp_continuousOn hchart
  have horient :=
    c.orientation.tangentNormalEquiv.continuous.comp_continuousOn hequiv
  change ContinuousOn
    (fun y ↦ c.orientation.tangentNormalEquiv
      (c.base.normalForm.equiv.symm
        (c.base.normalForm.codChart y))) c.base.neighborhood
  exact horient

theorem continuousOn_coordinateInv
    (c : EmbeddedSphereSideNormalChart e B x) :
    ContinuousOn c.coordinateInv c.coordinateTarget := by
  have hlinear : Continuous (fun z : EuclideanThree ↦
      c.base.normalForm.equiv
        (c.orientation.tangentNormalEquiv.symm z)) :=
    c.base.normalForm.equiv.continuous.comp
      c.orientation.tangentNormalEquiv.symm.continuous
  have hmaps : MapsTo
      (fun z : EuclideanThree ↦ c.base.normalForm.equiv
        (c.orientation.tangentNormalEquiv.symm z))
      c.coordinateTarget c.base.normalForm.codChart.target := by
    rintro z ⟨y, hy, rfl⟩
    change c.base.normalForm.equiv
      (c.orientation.tangentNormalEquiv.symm
        (c.orientation.tangentNormalEquiv
          (c.base.normalForm.equiv.symm
            (c.base.normalForm.codChart y)))) ∈
      c.base.normalForm.codChart.target
    rw [
      c.orientation.tangentNormalEquiv.symm_apply_apply,
      c.base.normalForm.equiv.apply_symm_apply]
    exact c.base.normalForm.codChart.map_source
      (c.base.neighborhood_subset_codChart_source hy)
  have hinv := c.base.normalForm.codChart.continuousOn_symm.comp
    hlinear.continuousOn hmaps
  change ContinuousOn
    (fun z ↦ c.base.normalForm.codChart.symm
      (c.base.normalForm.equiv
        (c.orientation.tangentNormalEquiv.symm z))) c.coordinateTarget
  exact hinv


noncomputable def closureSource
    (c : EmbeddedSphereSideNormalChart e B x) :
    TopologicalSpace.Opens (closure B) :=
  ⟨Subtype.val ⁻¹' c.base.neighborhood,
    c.base.isOpen_neighborhood.preimage continuous_subtype_val⟩


noncomputable def halfSpaceTarget
    (c : EmbeddedSphereSideNormalChart e B x) :
    TopologicalSpace.Opens (EuclideanHalfSpace 3) :=
  ⟨Subtype.val ⁻¹' c.coordinateTarget,
    c.isOpen_coordinateTarget.preimage continuous_subtype_val⟩

theorem closureSource_nonempty
    (c : EmbeddedSphereSideNormalChart e B x) :
    Nonempty c.closureSource := by
  have hxcl : e x ∈ closure B := by
    apply (c.mem_closure_iff_coordinate_nonneg
      c.base.image_mem_neighborhood).2
    rw [c.coordinate_zero_apply,
      (c.base.normalCoordinate_eq_zero_iff
        c.base.image_mem_neighborhood).2 ⟨x, rfl⟩]
    cases c.orientation <;> simp [NormalOrientation.orient]
  exact ⟨⟨⟨e x, hxcl⟩, c.base.image_mem_neighborhood⟩⟩

theorem halfSpaceTarget_nonempty
    (c : EmbeddedSphereSideNormalChart e B x) :
    Nonempty c.halfSpaceTarget := by
  have hnonneg : 0 ≤ c.coordinate (e x) 0 := by
    rw [c.coordinate_zero_apply,
      (c.base.normalCoordinate_eq_zero_iff
        c.base.image_mem_neighborhood).2 ⟨x, rfl⟩]
    cases c.orientation <;> simp [NormalOrientation.orient]
  exact ⟨⟨⟨c.coordinate (e x), hnonneg⟩,
    c.coordinate_mem_target c.base.image_mem_neighborhood⟩⟩

private noncomputable def closureBasePoint
    (c : EmbeddedSphereSideNormalChart e B x) : closure B := by
  have hxcl : e x ∈ closure B := by
    apply (c.mem_closure_iff_coordinate_nonneg
      c.base.image_mem_neighborhood).2
    rw [c.coordinate_zero_apply,
      (c.base.normalCoordinate_eq_zero_iff
        c.base.image_mem_neighborhood).2 ⟨x, rfl⟩]
    cases c.orientation <;> simp [NormalOrientation.orient]
  exact ⟨e x, hxcl⟩

private noncomputable def closureCoordinateInv
    (c : EmbeddedSphereSideNormalChart e B x)
    (z : EuclideanHalfSpace 3) : closure B := by
  classical
  exact if h : c.coordinateInv z.1 ∈ closure B then
    ⟨c.coordinateInv z.1, h⟩ else c.closureBasePoint

private theorem continuousOn_closureCoordinateInv
    (c : EmbeddedSphereSideNormalChart e B x) :
    ContinuousOn c.closureCoordinateInv
      (Subtype.val ⁻¹' c.coordinateTarget) := by
  apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
  have hc : ContinuousOn (fun z : EuclideanHalfSpace 3 ↦
      c.coordinateInv z.1) (Subtype.val ⁻¹' c.coordinateTarget) :=
    c.continuousOn_coordinateInv.comp
      continuous_subtype_val.continuousOn (fun _ hz ↦ hz)
  apply hc.congr
  intro z hz
  have hyNeigh : c.coordinateInv z.1 ∈ c.base.neighborhood :=
    c.coordinateInv_mem_neighborhood hz
  have hyClosure : c.coordinateInv z.1 ∈ closure B :=
    (c.mem_closure_iff_coordinate_nonneg hyNeigh).2 <| by
      rw [c.coordinate_coordinateInv hz]
      exact z.2
  simp [closureCoordinateInv, hyClosure]

noncomputable def closureHalfSpaceChart
    (c : EmbeddedSphereSideNormalChart e B x) :
    OpenPartialHomeomorph (closure B) (EuclideanHalfSpace 3) where
  toFun y := (𝓡∂ 3).symm (c.coordinate y.1)
  invFun := c.closureCoordinateInv
  source := Subtype.val ⁻¹' c.base.neighborhood
  target := Subtype.val ⁻¹' c.coordinateTarget
  map_source' := by
    intro y hy
    have hnonneg : 0 ≤ c.coordinate y.1 0 :=
      (c.mem_closure_iff_coordinate_nonneg hy).1 y.2
    have hrange : c.coordinate y.1 ∈ Set.range (𝓡∂ 3) := by
      rw [range_modelWithCornersEuclideanHalfSpace]
      exact hnonneg
    change ((𝓡∂ 3) ((𝓡∂ 3).symm (c.coordinate y.1))) ∈
      c.coordinateTarget
    rw [(𝓡∂ 3).right_inv hrange]
    exact c.coordinate_mem_target hy
  map_target' := by
    intro z hz
    have hyNeigh : c.coordinateInv z.1 ∈ c.base.neighborhood :=
      c.coordinateInv_mem_neighborhood hz
    have hyClosure : c.coordinateInv z.1 ∈ closure B :=
      (c.mem_closure_iff_coordinate_nonneg hyNeigh).2 <| by
        rw [c.coordinate_coordinateInv hz]
        exact z.2
    simpa [closureCoordinateInv, hyClosure] using hyNeigh
  left_inv' := by
    intro y hy
    have hnonneg : 0 ≤ c.coordinate y.1 0 :=
      (c.mem_closure_iff_coordinate_nonneg hy).1 y.2
    have hrange : c.coordinate y.1 ∈ Set.range (𝓡∂ 3) := by
      rw [range_modelWithCornersEuclideanHalfSpace]
      exact hnonneg
    have hval : ((𝓡∂ 3) ((𝓡∂ 3).symm (c.coordinate y.1))) =
        c.coordinate y.1 := (𝓡∂ 3).right_inv hrange
    have hinv : c.coordinateInv
        (((𝓡∂ 3).symm (c.coordinate y.1)).1) = y.1 := by
      change c.coordinateInv
        ((𝓡∂ 3) ((𝓡∂ 3).symm (c.coordinate y.1))) = y.1
      rw [hval]
      exact c.coordinateInv_coordinate hy
    have hcl : c.coordinateInv
        (((𝓡∂ 3).symm (c.coordinate y.1)).1) ∈ closure B := by
      rw [hinv]
      exact y.2
    simp only [closureCoordinateInv, hcl, dite_true]
    exact Subtype.ext hinv
  right_inv' := by
    intro z hz
    have hyNeigh : c.coordinateInv z.1 ∈ c.base.neighborhood :=
      c.coordinateInv_mem_neighborhood hz
    have hyClosure : c.coordinateInv z.1 ∈ closure B :=
      (c.mem_closure_iff_coordinate_nonneg hyNeigh).2 <| by
        rw [c.coordinate_coordinateInv hz]
        exact z.2
    simp only [closureCoordinateInv, hyClosure, dite_true]
    apply EuclideanHalfSpace.ext
    change ((𝓡∂ 3) ((𝓡∂ 3).symm
      (c.coordinate (c.coordinateInv z.1)))) = z.1
    rw [c.coordinate_coordinateInv hz]
    apply (𝓡∂ 3).right_inv
    rw [range_modelWithCornersEuclideanHalfSpace]
    exact z.2
  continuousOn_toFun := by
    have hcoord : ContinuousOn (fun y : closure B ↦ c.coordinate y.1)
        (Subtype.val ⁻¹' c.base.neighborhood) := by
      exact c.continuousOn_coordinate.comp
        continuous_subtype_val.continuousOn (fun _ hy ↦ hy)
    exact (𝓡∂ 3).continuous_invFun.comp_continuousOn hcoord
  continuousOn_invFun := by
    exact c.continuousOn_closureCoordinateInv
  open_source := c.closureSource.2
  open_target := c.halfSpaceTarget.2

theorem image_mem_closureHalfSpaceChart_source
    (c : EmbeddedSphereSideNormalChart e B x) :
    (⟨e x, by
      apply (c.mem_closure_iff_coordinate_nonneg
        c.base.image_mem_neighborhood).2
      rw [c.coordinate_zero_apply,
        (c.base.normalCoordinate_eq_zero_iff
          c.base.image_mem_neighborhood).2 ⟨x, rfl⟩]
      cases c.orientation <;> simp [NormalOrientation.orient]
    ⟩ : closure B) ∈ c.closureHalfSpaceChart.source :=
  c.base.image_mem_neighborhood

theorem closureHalfSpaceChart_toFun_coe
    (c : EmbeddedSphereSideNormalChart e B x) {y : closure B}
    (hy : y ∈ c.closureHalfSpaceChart.source) :
    (c.closureHalfSpaceChart y).1 = c.coordinate y.1 := by
  have hnonneg : 0 ≤ c.coordinate y.1 0 :=
    (c.mem_closure_iff_coordinate_nonneg hy).1 y.2
  have hrange : c.coordinate y.1 ∈ Set.range (𝓡∂ 3) := by
    rw [range_modelWithCornersEuclideanHalfSpace]
    exact hnonneg
  exact (𝓡∂ 3).right_inv hrange

theorem closureHalfSpaceChart_invFun_coe
    (c : EmbeddedSphereSideNormalChart e B x) {z : EuclideanHalfSpace 3}
    (hz : z ∈ c.closureHalfSpaceChart.target) :
    (c.closureHalfSpaceChart.symm z).1 = c.coordinateInv z.1 := by
  have hyNeigh : c.coordinateInv z.1 ∈ c.base.neighborhood :=
    c.coordinateInv_mem_neighborhood hz
  have hyClosure : c.coordinateInv z.1 ∈ closure B :=
    (c.mem_closure_iff_coordinate_nonneg hyNeigh).2 <| by
      rw [c.coordinate_coordinateInv hz]
      exact z.2
  change (c.closureCoordinateInv z).1 = c.coordinateInv z.1
  simp [closureCoordinateInv, hyClosure]

theorem closureHalfSpaceChart_image_zero
    (c : EmbeddedSphereSideNormalChart e B x) :
    let p : closure B := ⟨e x, by
      apply (c.mem_closure_iff_coordinate_nonneg
        c.base.image_mem_neighborhood).2
      rw [c.coordinate_zero_apply,
        (c.base.normalCoordinate_eq_zero_iff
          c.base.image_mem_neighborhood).2 ⟨x, rfl⟩]
      cases c.orientation <;> simp [NormalOrientation.orient]
    ⟩
    ((c.closureHalfSpaceChart p).1 0) = 0 := by
  intro p
  have hzero : c.coordinate (e x) 0 = 0 := by
    rw [c.coordinate_zero_apply,
      (c.base.normalCoordinate_eq_zero_iff
        c.base.image_mem_neighborhood).2 ⟨x, rfl⟩]
    cases c.orientation <;> simp [NormalOrientation.orient]
  have hrange : c.coordinate (e x) ∈ Set.range (𝓡∂ 3) := by
    rw [range_modelWithCornersEuclideanHalfSpace]
    exact hzero.ge
  have hval := (𝓡∂ 3).right_inv hrange
  change (((𝓡∂ 3).symm (c.coordinate (e x))).1 0) = 0
  exact (congrArg (fun z : EuclideanThree ↦ z 0) hval).trans hzero

theorem contDiffOn_coordinate_comp_coordinateInv
    {x' : SphereTwo}
    (c : EmbeddedSphereSideNormalChart e B x)
    (c' : EmbeddedSphereSideNormalChart e B x') :
    ContDiffOn ℝ ∞ (c'.coordinate ∘ c.coordinateInv)
      (c.coordinateTarget ∩
        c.coordinateInv ⁻¹' c'.base.neighborhood) := by
  let J := modelWithCornersSelf ℝ EuclideanThree
  let f : EuclideanThree → EuclideanThree := fun z ↦
    c.base.normalForm.equiv
      (c.orientation.tangentNormalEquiv.symm z)
  let g : EuclideanThree → EuclideanThree := fun z ↦
    c'.orientation.tangentNormalEquiv
      (c'.base.normalForm.equiv.symm z)
  have hf : ContDiff ℝ ∞ f :=
    c.base.normalForm.equiv.contDiff.comp
      c.orientation.tangentNormalEquiv.symm.contDiff
  have hg : ContDiff ℝ ∞ g :=
    c'.orientation.tangentNormalEquiv.contDiff.comp
      c'.base.normalForm.equiv.symm.contDiff
  let m := J.extendCoordChange c.base.normalForm.codChart
    c'.base.normalForm.codChart
  have hm : ContDiffOn ℝ ∞ m m.source :=
    J.contDiffOn_extendCoordChange
      c.base.normalForm.codChart_mem_maximalAtlas
      c'.base.normalForm.codChart_mem_maximalAtlas
  have hmaps : MapsTo f
      (c.coordinateTarget ∩
        c.coordinateInv ⁻¹' c'.base.neighborhood) m.source := by
    intro z hz
    rcases hz.1 with ⟨y, hy, rfl⟩
    have hySource : y ∈ c.base.normalForm.codChart.source :=
      c.base.neighborhood_subset_codChart_source hy
    have hyNeigh' : y ∈ c'.base.neighborhood := by
      have hzinv : c.coordinateInv (c.coordinate y) ∈
          c'.base.neighborhood := hz.2
      rwa [c.coordinateInv_coordinate hy] at hzinv
    have hySource' : y ∈ c'.base.normalForm.codChart.source :=
      c'.base.neighborhood_subset_codChart_source hyNeigh'
    change f (c.coordinate y) ∈ m.source
    simp only [f, coordinate,
      c.orientation.tangentNormalEquiv.symm_apply_apply,
      c.base.normalForm.equiv.apply_symm_apply]
    change c.base.normalForm.codChart y ∈
      (J.extendCoordChange c.base.normalForm.codChart
        c'.base.normalForm.codChart).source
    rw [ModelWithCorners.extendCoordChange_source]
    refine ⟨c.base.normalForm.codChart y, ?_, ?_⟩
    · change c.base.normalForm.codChart y ∈
        c.base.normalForm.codChart.target ∩
          c.base.normalForm.codChart.symm ⁻¹'
            c'.base.normalForm.codChart.source
      refine ⟨c.base.normalForm.codChart.map_source hySource, ?_⟩
      change c.base.normalForm.codChart.symm
        (c.base.normalForm.codChart y) ∈
          c'.base.normalForm.codChart.source
      rw [c.base.normalForm.codChart.left_inv hySource]
      exact hySource'
    · simp [J]
  have hcomp := hg.comp_contDiffOn (hm.comp hf.contDiffOn hmaps)
  apply hcomp.congr
  intro z hz
  rcases hz.1 with ⟨y, hy, rfl⟩
  have hySource : y ∈ c.base.normalForm.codChart.source :=
    c.base.neighborhood_subset_codChart_source hy
  change g (m (f (c.coordinate y))) = c'.coordinate (c.coordinateInv (c.coordinate y))
  rw [c.coordinateInv_coordinate hy]
  simp [m, f, g, J, coordinate, ModelWithCorners.extendCoordChange,
    hySource]

theorem contDiffOn_ambient_comp_coordinateInv
    (c : EmbeddedSphereSideNormalChart e B x)
    (a : OpenPartialHomeomorph N EuclideanThree)
    (ha : a ∈ IsManifold.maximalAtlas
      (modelWithCornersSelf ℝ EuclideanThree) ∞ N) :
    ContDiffOn ℝ ∞ (a ∘ c.coordinateInv)
      (c.coordinateTarget ∩ c.coordinateInv ⁻¹' a.source) := by
  let J := modelWithCornersSelf ℝ EuclideanThree
  let f : EuclideanThree → EuclideanThree := fun z ↦
    c.base.normalForm.equiv
      (c.orientation.tangentNormalEquiv.symm z)
  have hf : ContDiff ℝ ∞ f :=
    c.base.normalForm.equiv.contDiff.comp
      c.orientation.tangentNormalEquiv.symm.contDiff
  let m := J.extendCoordChange c.base.normalForm.codChart a
  have hm : ContDiffOn ℝ ∞ m m.source :=
    J.contDiffOn_extendCoordChange
      c.base.normalForm.codChart_mem_maximalAtlas ha
  have hmaps : MapsTo f
      (c.coordinateTarget ∩ c.coordinateInv ⁻¹' a.source) m.source := by
    intro z hz
    rcases hz.1 with ⟨y, hy, rfl⟩
    have hySource : y ∈ c.base.normalForm.codChart.source :=
      c.base.neighborhood_subset_codChart_source hy
    have hySource' : y ∈ a.source := by
      have hzinv : c.coordinateInv (c.coordinate y) ∈ a.source := hz.2
      rwa [c.coordinateInv_coordinate hy] at hzinv
    change f (c.coordinate y) ∈ m.source
    simp only [f, coordinate,
      c.orientation.tangentNormalEquiv.symm_apply_apply,
      c.base.normalForm.equiv.apply_symm_apply]
    change c.base.normalForm.codChart y ∈
      (J.extendCoordChange c.base.normalForm.codChart a).source
    rw [ModelWithCorners.extendCoordChange_source]
    refine ⟨c.base.normalForm.codChart y, ?_, ?_⟩
    · refine ⟨c.base.normalForm.codChart.map_source hySource, ?_⟩
      change c.base.normalForm.codChart.symm
        (c.base.normalForm.codChart y) ∈ a.source
      rwa [c.base.normalForm.codChart.left_inv hySource]
    · simp [J]
  have hcomp := hm.comp hf.contDiffOn hmaps
  apply hcomp.congr
  intro z hz
  rcases hz.1 with ⟨y, hy, rfl⟩
  have hySource : y ∈ c.base.normalForm.codChart.source :=
    c.base.neighborhood_subset_codChart_source hy
  change m (f (c.coordinate y)) = a (c.coordinateInv (c.coordinate y))
  rw [c.coordinateInv_coordinate hy]
  simp [m, f, J, coordinate, ModelWithCorners.extendCoordChange,
    hySource]

theorem contDiffOn_coordinate_comp_ambient_symm
    (c : EmbeddedSphereSideNormalChart e B x)
    (a : OpenPartialHomeomorph N EuclideanThree)
    (ha : a ∈ IsManifold.maximalAtlas
      (modelWithCornersSelf ℝ EuclideanThree) ∞ N) :
    ContDiffOn ℝ ∞ (c.coordinate ∘ a.symm)
      (a.target ∩ a.symm ⁻¹' c.base.neighborhood) := by
  let J := modelWithCornersSelf ℝ EuclideanThree
  let g : EuclideanThree → EuclideanThree := fun z ↦
    c.orientation.tangentNormalEquiv
      (c.base.normalForm.equiv.symm z)
  have hg : ContDiff ℝ ∞ g :=
    c.orientation.tangentNormalEquiv.contDiff.comp
      c.base.normalForm.equiv.symm.contDiff
  let m := J.extendCoordChange a c.base.normalForm.codChart
  have hm : ContDiffOn ℝ ∞ m m.source :=
    J.contDiffOn_extendCoordChange ha
      c.base.normalForm.codChart_mem_maximalAtlas
  have hsubset :
      a.target ∩ a.symm ⁻¹' c.base.neighborhood ⊆ m.source := by
    intro z hz
    have hySource : a.symm z ∈ c.base.normalForm.codChart.source :=
      c.base.neighborhood_subset_codChart_source hz.2
    change z ∈ (J.extendCoordChange a
      c.base.normalForm.codChart).source
    rw [ModelWithCorners.extendCoordChange_source]
    refine ⟨z, ?_, ?_⟩
    · exact ⟨hz.1, hySource⟩
    · simp [J]
  have hcomp := hg.comp_contDiffOn (hm.mono hsubset)
  apply hcomp.congr
  intro z hz
  change g (m z) = c.coordinate (a.symm z)
  simp [m, g, J, coordinate, ModelWithCorners.extendCoordChange]

theorem contDiffOn_closureHalfSpaceChart_transition
    {x' : SphereTwo}
    (c : EmbeddedSphereSideNormalChart e B x)
    (c' : EmbeddedSphereSideNormalChart e B x') :
    let t := c.closureHalfSpaceChart.symm.trans
      c'.closureHalfSpaceChart
    ContDiffOn ℝ ∞ ((𝓡∂ 3) ∘ t ∘ (𝓡∂ 3).symm)
      ((𝓡∂ 3).symm ⁻¹' t.source ∩ Set.range (𝓡∂ 3)) := by
  intro t
  have hsmooth := c.contDiffOn_coordinate_comp_coordinateInv c'
  apply hsmooth.congr_mono
  · intro z hz
    have hzRange : z ∈ Set.range (𝓡∂ 3) := hz.2
    have ht : (𝓡∂ 3).symm z ∈ t.source := hz.1
    have ht' : (𝓡∂ 3).symm z ∈
        c.closureHalfSpaceChart.target ∩
          c.closureHalfSpaceChart.symm ⁻¹'
            c'.closureHalfSpaceChart.source := by
      simpa only [t, OpenPartialHomeomorph.trans_source,
        OpenPartialHomeomorph.symm_source] using ht
    have hval : ((𝓡∂ 3).symm z).1 = z :=
      (𝓡∂ 3).right_inv hzRange
    change (c'.closureHalfSpaceChart
      (c.closureHalfSpaceChart.symm ((𝓡∂ 3).symm z))).1 =
        c'.coordinate (c.coordinateInv z)
    rw [c'.closureHalfSpaceChart_toFun_coe ht'.2,
      c.closureHalfSpaceChart_invFun_coe ht'.1, hval]
  · intro z hz
    have hzRange : z ∈ Set.range (𝓡∂ 3) := hz.2
    have ht : (𝓡∂ 3).symm z ∈ t.source := hz.1
    have ht' : (𝓡∂ 3).symm z ∈
        c.closureHalfSpaceChart.target ∩
          c.closureHalfSpaceChart.symm ⁻¹'
            c'.closureHalfSpaceChart.source := by
      simpa only [t, OpenPartialHomeomorph.trans_source,
        OpenPartialHomeomorph.symm_source] using ht
    have hval : ((𝓡∂ 3).symm z).1 = z :=
      (𝓡∂ 3).right_inv hzRange
    constructor
    · rw [← hval]
      exact ht'.1
    · have hsource' :
          (c.closureHalfSpaceChart.symm ((𝓡∂ 3).symm z)).1 ∈
            c'.base.neighborhood := ht'.2
      rw [c.closureHalfSpaceChart_invFun_coe ht'.1, hval] at hsource'
      exact hsource'

theorem closureHalfSpaceChart_transition_mem_contDiffGroupoid
    {x' : SphereTwo}
    (c : EmbeddedSphereSideNormalChart e B x)
    (c' : EmbeddedSphereSideNormalChart e B x') :
    c.closureHalfSpaceChart.symm.trans c'.closureHalfSpaceChart ∈
      contDiffGroupoid ∞ (𝓡∂ 3) := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  constructor
  · exact c.contDiffOn_closureHalfSpaceChart_transition c'
  · let t := c.closureHalfSpaceChart.symm.trans
      c'.closureHalfSpaceChart
    change ContDiffOn ℝ ∞ ((𝓡∂ 3) ∘ t.symm ∘ (𝓡∂ 3).symm)
      ((𝓡∂ 3).symm ⁻¹' t.target ∩ Set.range (𝓡∂ 3))
    rw [← OpenPartialHomeomorph.symm_source t,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm]
    exact c'.contDiffOn_closureHalfSpaceChart_transition c

theorem contDiffOn_closureHalfSpaceChart_sideInteriorChart_transition
    [IsManifold (modelWithCornersSelf ℝ EuclideanThree) ∞ N]
    (c : EmbeddedSphereSideNormalChart e B x)
    (hB : IsOpen B) (q : closure B) (hq : q.1 ∈ B) :
    let t := c.closureHalfSpaceChart.symm.trans
      (SideInteriorChart.chart hB q hq)
    ContDiffOn ℝ ∞ ((𝓡∂ 3) ∘ t ∘ (𝓡∂ 3).symm)
      ((𝓡∂ 3).symm ⁻¹' t.source ∩ Set.range (𝓡∂ 3)) := by
  intro t
  let a := chartAt EuclideanThree q.1
  let F : EuclideanThree → EuclideanThree := fun z ↦
    InteriorHalfSpace.setFirst z (Real.exp (z 0))
  have ha : a ∈ IsManifold.maximalAtlas
      (modelWithCornersSelf ℝ EuclideanThree) ∞ N :=
    IsManifold.chart_mem_maximalAtlas q.1
  have hsmooth := c.contDiffOn_ambient_comp_coordinateInv a ha
  have hcomp : ContDiffOn ℝ ∞ (F ∘ a ∘ c.coordinateInv)
      (c.coordinateTarget ∩ c.coordinateInv ⁻¹' a.source) :=
    InteriorHalfSpace.contDiff_setFirst_exp.comp_contDiffOn hsmooth
  apply hcomp.congr_mono
  · intro z hz
    have ht : (𝓡∂ 3).symm z ∈
        (c.closureHalfSpaceChart.symm.trans
          (SideInteriorChart.chart hB q hq)).source := hz.1
    rw [OpenPartialHomeomorph.trans_source] at ht
    have hcTarget : (𝓡∂ 3).symm z ∈
        c.closureHalfSpaceChart.target := ht.1
    have hval : ((𝓡∂ 3).symm z).1 = z :=
      (𝓡∂ 3).right_inv hz.2
    have hcinv := c.closureHalfSpaceChart_invFun_coe hcTarget
    rw [hval] at hcinv
    have hySource :
        c.closureHalfSpaceChart.symm ((𝓡∂ 3).symm z) ∈
          (SideInteriorChart.liftedChart hB q hq).source := by
      rw [SideInteriorChart.chart,
        OpenPartialHomeomorph.trans_source] at ht
      exact ht.2.1
    have hyFacts := (SideInteriorChart.mem_liftedChart_source_iff
      hB q _ hq).1 hySource
    rw [hcinv] at hyFacts
    change (((𝓡∂ 3) ∘ t ∘ (𝓡∂ 3).symm) z) =
      F (a (c.coordinateInv z))
    simp only [Function.comp_apply]
    change (SideInteriorChart.chart hB q hq
        (c.closureHalfSpaceChart.symm ((𝓡∂ 3).symm z))).1 =
      F (a (c.coordinateInv z))
    rw [SideInteriorChart.chart, OpenPartialHomeomorph.trans_apply,
      SideInteriorChart.liftedChart_apply hB q _ hq
        (hcinv.symm ▸ hyFacts.1),
      hcinv]
    rfl
  · intro z hz
    have ht : (𝓡∂ 3).symm z ∈
        (c.closureHalfSpaceChart.symm.trans
          (SideInteriorChart.chart hB q hq)).source := hz.1
    rw [OpenPartialHomeomorph.trans_source] at ht
    have hcTarget : (𝓡∂ 3).symm z ∈
        c.closureHalfSpaceChart.target := ht.1
    have hval : ((𝓡∂ 3).symm z).1 = z :=
      (𝓡∂ 3).right_inv hz.2
    have hcinv := c.closureHalfSpaceChart_invFun_coe hcTarget
    rw [hval] at hcinv
    have hySource :
        c.closureHalfSpaceChart.symm ((𝓡∂ 3).symm z) ∈
          (SideInteriorChart.liftedChart hB q hq).source := by
      rw [SideInteriorChart.chart,
        OpenPartialHomeomorph.trans_source] at ht
      exact ht.2.1
    have hyFacts := (SideInteriorChart.mem_liftedChart_source_iff
      hB q _ hq).1 hySource
    rw [hcinv] at hyFacts
    constructor
    · change ((𝓡∂ 3).symm z).1 ∈ c.coordinateTarget at hcTarget
      rwa [hval] at hcTarget
    · exact hyFacts.2

theorem contDiffOn_sideInteriorChart_closureHalfSpaceChart_transition
    [IsManifold (modelWithCornersSelf ℝ EuclideanThree) ∞ N]
    (c : EmbeddedSphereSideNormalChart e B x)
    (hB : IsOpen B) (q : closure B) (hq : q.1 ∈ B) :
    let t := (SideInteriorChart.chart hB q hq).symm.trans
      c.closureHalfSpaceChart
    ContDiffOn ℝ ∞ ((𝓡∂ 3) ∘ t ∘ (𝓡∂ 3).symm)
      ((𝓡∂ 3).symm ⁻¹' t.source ∩ Set.range (𝓡∂ 3)) := by
  intro t
  let a := chartAt EuclideanThree q.1
  let G : EuclideanThree → EuclideanThree := fun z ↦
    InteriorHalfSpace.setFirst z (Real.log (z 0))
  let D := (𝓡∂ 3).symm ⁻¹' t.source ∩ Set.range (𝓡∂ 3)
  have ha : a ∈ IsManifold.maximalAtlas
      (modelWithCornersSelf ℝ EuclideanThree) ∞ N :=
    IsManifold.chart_mem_maximalAtlas q.1
  have hsmooth := c.contDiffOn_coordinate_comp_ambient_symm a ha
  have hpositive : D ⊆ {z : EuclideanThree | 0 < z 0} := by
    intro z hz
    have ht : (𝓡∂ 3).symm z ∈
        ((SideInteriorChart.chart hB q hq).symm.trans
          c.closureHalfSpaceChart).source := hz.1
    rw [OpenPartialHomeomorph.trans_source] at ht
    have hInteriorTarget : (𝓡∂ 3).symm z ∈
        (SideInteriorChart.chart hB q hq).target := ht.1
    rw [SideInteriorChart.chart,
      OpenPartialHomeomorph.trans_target] at hInteriorTarget
    have hChartTarget : (𝓡∂ 3).symm z ∈
        InteriorHalfSpace.chart.target := hInteriorTarget.1
    have hval : ((𝓡∂ 3).symm z).1 = z :=
      (𝓡∂ 3).right_inv hz.2
    change 0 < ((𝓡∂ 3).symm z).1 0 at hChartTarget
    rwa [hval] at hChartTarget
  have hmaps : MapsTo G D
      (a.target ∩ a.symm ⁻¹' c.base.neighborhood) := by
    intro z hz
    have ht : (𝓡∂ 3).symm z ∈
        ((SideInteriorChart.chart hB q hq).symm.trans
          c.closureHalfSpaceChart).source := hz.1
    rw [OpenPartialHomeomorph.trans_source] at ht
    have hInteriorTarget : (𝓡∂ 3).symm z ∈
        (SideInteriorChart.chart hB q hq).target := ht.1
    have hClosureSource :
        (SideInteriorChart.chart hB q hq).symm ((𝓡∂ 3).symm z) ∈
          c.closureHalfSpaceChart.source := ht.2
    rw [SideInteriorChart.chart,
      OpenPartialHomeomorph.trans_target] at hInteriorTarget
    have hLiftTarget : InteriorHalfSpace.chart.symm ((𝓡∂ 3).symm z) ∈
        (SideInteriorChart.liftedChart hB q hq).target :=
      hInteriorTarget.2
    have hval : ((𝓡∂ 3).symm z).1 = z :=
      (𝓡∂ 3).right_inv hz.2
    have hG : InteriorHalfSpace.chart.symm ((𝓡∂ 3).symm z) = G z := by
      change InteriorHalfSpace.setFirst ((𝓡∂ 3).symm z).1
        (Real.log (((𝓡∂ 3).symm z).1 0)) = G z
      simp only [G]
      rw [hval]
    have hsideSymm :
        (SideInteriorChart.chart hB q hq).symm ((𝓡∂ 3).symm z) =
          (SideInteriorChart.liftedChart hB q hq).symm (G z) := by
      rw [SideInteriorChart.chart,
        OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_apply, hG]
    have hAmbientTarget := SideInteriorChart.liftedChart_target_subset_chart_target
      hB q hq hLiftTarget
    have hunder := SideInteriorChart.liftedChart_symm_coe
      hB q hq hLiftTarget
    rw [hG] at hAmbientTarget hunder
    have hneigh :
        ((SideInteriorChart.liftedChart hB q hq).symm (G z)).1 ∈
          c.base.neighborhood := by
      rw [← hsideSymm]
      exact hClosureSource
    rw [hunder] at hneigh
    exact ⟨hAmbientTarget, hneigh⟩
  have hcomp : ContDiffOn ℝ ∞
      (c.coordinate ∘ a.symm ∘ G) D :=
    hsmooth.comp (InteriorHalfSpace.contDiffOn_setFirst_log.mono hpositive) hmaps
  apply hcomp.congr
  intro z hz
  have ht : (𝓡∂ 3).symm z ∈
      ((SideInteriorChart.chart hB q hq).symm.trans
        c.closureHalfSpaceChart).source := hz.1
  rw [OpenPartialHomeomorph.trans_source] at ht
  have hInteriorTarget : (𝓡∂ 3).symm z ∈
      (SideInteriorChart.chart hB q hq).target := ht.1
  have hClosureSource :
      (SideInteriorChart.chart hB q hq).symm ((𝓡∂ 3).symm z) ∈
        c.closureHalfSpaceChart.source := ht.2
  rw [SideInteriorChart.chart,
    OpenPartialHomeomorph.trans_target] at hInteriorTarget
  have hLiftTarget : InteriorHalfSpace.chart.symm ((𝓡∂ 3).symm z) ∈
      (SideInteriorChart.liftedChart hB q hq).target :=
    hInteriorTarget.2
  have hval : ((𝓡∂ 3).symm z).1 = z :=
    (𝓡∂ 3).right_inv hz.2
  have hG : InteriorHalfSpace.chart.symm ((𝓡∂ 3).symm z) = G z := by
    change InteriorHalfSpace.setFirst ((𝓡∂ 3).symm z).1
      (Real.log (((𝓡∂ 3).symm z).1 0)) = G z
    simp only [G]
    rw [hval]
  have hsideSymm :
      (SideInteriorChart.chart hB q hq).symm ((𝓡∂ 3).symm z) =
        (SideInteriorChart.liftedChart hB q hq).symm (G z) := by
    rw [SideInteriorChart.chart,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_apply, hG]
  have hunder := SideInteriorChart.liftedChart_symm_coe
    hB q hq hLiftTarget
  rw [hG] at hunder
  have hclosureValue := c.closureHalfSpaceChart_toFun_coe hClosureSource
  change (((𝓡∂ 3) ∘ t ∘ (𝓡∂ 3).symm) z) =
    ((c.coordinate ∘ a.symm ∘ G) z)
  simp only [Function.comp_apply]
  change (c.closureHalfSpaceChart
      ((SideInteriorChart.chart hB q hq).symm ((𝓡∂ 3).symm z))).1 =
    c.coordinate (a.symm (G z))
  rw [hclosureValue]
  rw [hsideSymm]
  exact congrArg c.coordinate hunder

theorem closureHalfSpaceChart_sideInteriorChart_transition_mem_contDiffGroupoid
    [IsManifold (modelWithCornersSelf ℝ EuclideanThree) ∞ N]
    (c : EmbeddedSphereSideNormalChart e B x)
    (hB : IsOpen B) (q : closure B) (hq : q.1 ∈ B) :
    c.closureHalfSpaceChart.symm.trans
      (SideInteriorChart.chart hB q hq) ∈
        contDiffGroupoid ∞ (𝓡∂ 3) := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  constructor
  · exact c.contDiffOn_closureHalfSpaceChart_sideInteriorChart_transition
      hB q hq
  · let t := c.closureHalfSpaceChart.symm.trans
      (SideInteriorChart.chart hB q hq)
    change ContDiffOn ℝ ∞ ((𝓡∂ 3) ∘ t.symm ∘ (𝓡∂ 3).symm)
      ((𝓡∂ 3).symm ⁻¹' t.target ∩ Set.range (𝓡∂ 3))
    rw [← OpenPartialHomeomorph.symm_source t,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm]
    exact c.contDiffOn_sideInteriorChart_closureHalfSpaceChart_transition
      hB q hq

end EmbeddedSphereSideNormalChart

section ClosureAtlas

variable {B : Set N}

noncomputable def sideChartAt
    (hBopen : IsOpen B)
    (hclosure : closure B = B ∪ Set.range e)
    (normalChart : ∀ x : SphereTwo,
      Nonempty (EmbeddedSphereSideNormalChart e B x))
    (p : closure B) :
    OpenPartialHomeomorph (closure B) (EuclideanHalfSpace 3) := by
  classical
  by_cases hpB : p.1 ∈ B
  · exact SideInteriorChart.chart hBopen p hpB
  · have hpClosure : p.1 ∈ closure B := p.property
    have hpRange : p.1 ∈ Set.range e := by
      exact (hclosure.le hpClosure).resolve_left hpB
    let x : SphereTwo := Classical.choose hpRange
    let hx : e x = p.1 := Classical.choose_spec hpRange
    exact (Classical.choice (normalChart x)).closureHalfSpaceChart

theorem mem_sideChartAt_source
    (hBopen : IsOpen B)
    (hclosure : closure B = B ∪ Set.range e)
    (normalChart : ∀ x : SphereTwo,
      Nonempty (EmbeddedSphereSideNormalChart e B x))
    (p : closure B) :
    p ∈ (sideChartAt hBopen hclosure normalChart p).source := by
  classical
  by_cases hpB : p.1 ∈ B
  · simp only [sideChartAt, dif_pos hpB]
    exact SideInteriorChart.mem_chart_source hBopen p hpB
  · simp only [sideChartAt, dif_neg hpB]
    have hpClosure : p.1 ∈ closure B := p.property
    have hpRange : p.1 ∈ Set.range e := by
      exact (hclosure.le hpClosure).resolve_left hpB
    let x : SphereTwo := Classical.choose hpRange
    have hx : e x = p.1 := Classical.choose_spec hpRange
    let c : EmbeddedSphereSideNormalChart e B x :=
      Classical.choice (normalChart x)
    change p.1 ∈ c.base.neighborhood
    rw [← hx]
    exact c.base.image_mem_neighborhood

@[instance_reducible]
noncomputable def sideClosureChartedSpace
    (hBopen : IsOpen B)
    (hclosure : closure B = B ∪ Set.range e)
    (normalChart : ∀ x : SphereTwo,
      Nonempty (EmbeddedSphereSideNormalChart e B x)) :
    ChartedSpace (EuclideanHalfSpace 3) (closure B) where
  atlas := Set.range (sideChartAt hBopen hclosure normalChart)
  chartAt := sideChartAt hBopen hclosure normalChart
  mem_chart_source := mem_sideChartAt_source hBopen hclosure normalChart
  chart_mem_atlas := fun p ↦ ⟨p, rfl⟩

theorem sideChartAt_transition_mem_contDiffGroupoid
    [IsManifold (modelWithCornersSelf ℝ EuclideanThree) ∞ N]
    (hBopen : IsOpen B)
    (hclosure : closure B = B ∪ Set.range e)
    (normalChart : ∀ x : SphereTwo,
      Nonempty (EmbeddedSphereSideNormalChart e B x))
    (p q : closure B) :
    (sideChartAt hBopen hclosure normalChart p).symm.trans
      (sideChartAt hBopen hclosure normalChart q) ∈
        contDiffGroupoid ∞ (𝓡∂ 3) := by
  classical
  by_cases hpB : p.1 ∈ B
  · by_cases hqB : q.1 ∈ B
    · simp only [sideChartAt, dif_pos hpB, dif_pos hqB]
      exact SideInteriorChart.chart_transition_mem_contDiffGroupoid
        hBopen p q hpB hqB
    · simp only [sideChartAt, dif_pos hpB, dif_neg hqB]
      have hqRange : q.1 ∈ Set.range e :=
        (hclosure.le q.property).resolve_left hqB
      let x : SphereTwo := Classical.choose hqRange
      let c : EmbeddedSphereSideNormalChart e B x :=
        Classical.choice (normalChart x)
      have hmix :=
        c.closureHalfSpaceChart_sideInteriorChart_transition_mem_contDiffGroupoid
          hBopen p hpB
      exact (contDiffGroupoid ∞ (𝓡∂ 3)).symm hmix
  · by_cases hqB : q.1 ∈ B
    · simp only [sideChartAt, dif_neg hpB, dif_pos hqB]
      have hpRange : p.1 ∈ Set.range e :=
        (hclosure.le p.property).resolve_left hpB
      let x : SphereTwo := Classical.choose hpRange
      let c : EmbeddedSphereSideNormalChart e B x :=
        Classical.choice (normalChart x)
      exact
        c.closureHalfSpaceChart_sideInteriorChart_transition_mem_contDiffGroupoid
          hBopen q hqB
    · simp only [sideChartAt, dif_neg hpB, dif_neg hqB]
      have hpRange : p.1 ∈ Set.range e :=
        (hclosure.le p.property).resolve_left hpB
      have hqRange : q.1 ∈ Set.range e :=
        (hclosure.le q.property).resolve_left hqB
      let x : SphereTwo := Classical.choose hpRange
      let x' : SphereTwo := Classical.choose hqRange
      let c : EmbeddedSphereSideNormalChart e B x :=
        Classical.choice (normalChart x)
      let c' : EmbeddedSphereSideNormalChart e B x' :=
        Classical.choice (normalChart x')
      exact c.closureHalfSpaceChart_transition_mem_contDiffGroupoid c'

theorem sideClosureIsManifold
    [IsManifold (modelWithCornersSelf ℝ EuclideanThree) ∞ N]
    (hBopen : IsOpen B)
    (hclosure : closure B = B ∪ Set.range e)
    (normalChart : ∀ x : SphereTwo,
      Nonempty (EmbeddedSphereSideNormalChart e B x)) :
    let _ := sideClosureChartedSpace hBopen hclosure normalChart
    IsManifold (𝓡∂ 3) ∞ (closure B) := by
  dsimp only
  let _ := sideClosureChartedSpace hBopen hclosure normalChart
  exact {
    compatible := by
      rintro f g ⟨p, rfl⟩ ⟨q, rfl⟩
      exact sideChartAt_transition_mem_contDiffGroupoid
        hBopen hclosure normalChart p q
  }

theorem sideClosure_inclusion_isSmoothEmbedding
    [IsManifold (modelWithCornersSelf ℝ EuclideanThree) ∞ N]
    (hBopen : IsOpen B)
    (hclosure : closure B = B ∪ Set.range e)
    (normalChart : ∀ x : SphereTwo,
      Nonempty (EmbeddedSphereSideNormalChart e B x)) :
    let _ := sideClosureChartedSpace hBopen hclosure normalChart
    Manifold.IsSmoothEmbedding (𝓡∂ 3)
      (modelWithCornersSelf ℝ EuclideanThree) ∞
      (Subtype.val : closure B → N) := by
  dsimp only
  let _ := sideClosureChartedSpace hBopen hclosure normalChart
  let _ := sideClosureIsManifold hBopen hclosure normalChart
  refine ⟨?_, Topology.IsEmbedding.subtypeVal⟩
  apply Manifold.IsImmersionOfComplement.isImmersion
    (F := PUnit)
  intro p
  classical
  by_cases hpB : p.1 ∈ B
  · let a := chartAt EuclideanThree p.1
    let dom := SideInteriorChart.chart hBopen p hpB
    let cod := a.trans InteriorHalfSpace.ambientChart
    apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
      continuous_subtype_val.continuousAt
      (ContinuousLinearEquiv.prodUnique ℝ EuclideanThree PUnit)
      dom cod
    · exact SideInteriorChart.mem_chart_source hBopen p hpB
    · change p.1 ∈ (a.trans InteriorHalfSpace.ambientChart).source
      rw [OpenPartialHomeomorph.trans_source]
      exact ⟨mem_chart_source EuclideanThree p.1, Set.mem_univ _⟩
    · have hdom : sideChartAt hBopen hclosure normalChart p ∈
          IsManifold.maximalAtlas (𝓡∂ 3) ∞ (closure B) :=
        IsManifold.chart_mem_maximalAtlas p
      simpa only [sideChartAt, dif_pos hpB, dom] using hdom
    · apply InteriorHalfSpace.trans_mem_maximalAtlas
      · exact IsManifold.chart_mem_maximalAtlas p.1
      · exact InteriorHalfSpace.ambientChart_mem_contDiffGroupoid
    · intro z hz
      rw [dom.extend_target_eq_image_source] at hz
      rcases hz with ⟨y, hy, rfl⟩
      have hy' :
          (dom.extend (𝓡∂ 3)).symm ((dom.extend (𝓡∂ 3)) y) = y :=
        (dom.extend (𝓡∂ 3)).left_inv (by simpa using hy)
      have hyLift : y ∈ (SideInteriorChart.liftedChart
          hBopen p hpB).source := by
        change y ∈ (SideInteriorChart.chart hBopen p hpB).source at hy
        rw [SideInteriorChart.chart,
          OpenPartialHomeomorph.trans_source] at hy
        exact hy.1
      have hyFacts := (SideInteriorChart.mem_liftedChart_source_iff
        hBopen p y hpB).1 hyLift
      rw [Function.comp_apply, Function.comp_apply, hy']
      change (a.trans InteriorHalfSpace.ambientChart) y.1 =
        ((𝓡∂ 3) ((SideInteriorChart.liftedChart hBopen p hpB).trans
          InteriorHalfSpace.chart y))
      rw [OpenPartialHomeomorph.trans_apply,
        OpenPartialHomeomorph.trans_apply,
        SideInteriorChart.liftedChart_apply hBopen p y hpB hyFacts.1]
      rfl
  · have hpRange : p.1 ∈ Set.range e :=
      (hclosure.le p.property).resolve_left hpB
    let x : SphereTwo := Classical.choose hpRange
    have hx : e x = p.1 := Classical.choose_spec hpRange
    let c : EmbeddedSphereSideNormalChart e B x :=
      Classical.choice (normalChart x)
    let dom := c.closureHalfSpaceChart
    let cod := c.base.normalForm.codChart
    let L : EuclideanThree ≃L[ℝ] EuclideanThree :=
      c.orientation.tangentNormalEquiv.symm.trans
        c.base.normalForm.equiv
    let equiv : (EuclideanThree × PUnit.{1}) ≃L[ℝ] EuclideanThree :=
      (ContinuousLinearEquiv.prodUnique ℝ EuclideanThree PUnit.{1}).trans L
    apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
      continuous_subtype_val.continuousAt equiv dom cod
    · change p.1 ∈ c.base.neighborhood
      rw [← hx]
      exact c.base.image_mem_neighborhood
    · change p.1 ∈ c.base.normalForm.codChart.source
      rw [← hx]
      exact c.base.neighborhood_subset_codChart_source
        c.base.image_mem_neighborhood
    · have hdom : sideChartAt hBopen hclosure normalChart p ∈
          IsManifold.maximalAtlas (𝓡∂ 3) ∞ (closure B) :=
        IsManifold.chart_mem_maximalAtlas p
      simpa only [sideChartAt, dif_neg hpB, c, x] using hdom
    · exact c.base.normalForm.codChart_mem_maximalAtlas
    · intro z hz
      rw [dom.extend_target_eq_image_source] at hz
      rcases hz with ⟨y, hy, rfl⟩
      have hy' :
          (dom.extend (𝓡∂ 3)).symm ((dom.extend (𝓡∂ 3)) y) = y :=
        (dom.extend (𝓡∂ 3)).left_inv (by simpa using hy)
      have hcoord : (dom y).1 = c.coordinate y.1 := by
        exact c.closureHalfSpaceChart_toFun_coe hy
      rw [Function.comp_apply, Function.comp_apply, hy']
      simp only [equiv]
      change cod y.1 = L ((𝓡∂ 3) (dom y))
      rw [modelWithCornersEuclideanHalfSpace_toFun, hcoord]
      simp [cod, L, EmbeddedSphereSideNormalChart.coordinate]

theorem sideClosure_isInteriorPoint_iff
    (hBopen : IsOpen B)
    (hclosure : closure B = B ∪ Set.range e)
    (normalChart : ∀ x : SphereTwo,
      Nonempty (EmbeddedSphereSideNormalChart e B x))
    (p : closure B) :
    let _ := sideClosureChartedSpace hBopen hclosure normalChart
    (𝓡∂ 3).IsInteriorPoint p ↔ p.1 ∈ B := by
  dsimp only
  let _ := sideClosureChartedSpace hBopen hclosure normalChart
  rw [ModelWithCorners.IsInteriorPoint,
    interior_range_modelWithCornersEuclideanHalfSpace]
  change 0 < (extChartAt (𝓡∂ 3) p p) 0 ↔ p.1 ∈ B
  rw [extChartAt_coe]
  change 0 < ((sideChartAt hBopen hclosure normalChart p) p).1 0 ↔
    p.1 ∈ B
  classical
  by_cases hpB : p.1 ∈ B
  · constructor
    · intro _
      exact hpB
    · intro _
      simpa only [sideChartAt, dif_pos hpB] using
        SideInteriorChart.chart_apply_zero_pos hBopen p hpB
  · constructor
    · simp only [sideChartAt, dif_neg hpB]
      intro hpos
      have hpRange : p.1 ∈ Set.range e :=
        (hclosure.le p.property).resolve_left hpB
      let x : SphereTwo := Classical.choose hpRange
      have hx : e x = p.1 := Classical.choose_spec hpRange
      let c : EmbeddedSphereSideNormalChart e B x :=
        Classical.choice (normalChart x)
      have hzero := c.closureHalfSpaceChart_image_zero
      have hpEq : p = ⟨e x, by rw [hx]; exact p.2⟩ := by
        apply Subtype.ext
        exact hx.symm
      have hz : ((c.closureHalfSpaceChart p).1 0) = 0 := by
        simpa only [hpEq] using hzero
      rw [hz] at hpos
      exact False.elim (lt_irrefl 0 hpos)
    · intro hp
      exact False.elim (hpB hp)

theorem sideClosure_isBoundaryPoint_iff
    (hBopen : IsOpen B)
    (hclosure : closure B = B ∪ Set.range e)
    (normalChart : ∀ x : SphereTwo,
      Nonempty (EmbeddedSphereSideNormalChart e B x))
    (p : closure B) :
    let _ := sideClosureChartedSpace hBopen hclosure normalChart
    (𝓡∂ 3).IsBoundaryPoint p ↔ p.1 ∈ Set.range e := by
  dsimp only
  let _ := sideClosureChartedSpace hBopen hclosure normalChart
  have hi : (𝓡∂ 3).IsInteriorPoint p ↔ p.1 ∈ B := by
    simpa only using
      (sideClosure_isInteriorPoint_iff hBopen hclosure normalChart p)
  rw [(𝓡∂ 3).isBoundaryPoint_iff_not_isInteriorPoint, hi]
  constructor
  · intro hpNotB
    exact (hclosure.le p.property).resolve_left hpNotB
  · rintro ⟨x, hx⟩ hpB
    let c : EmbeddedSphereSideNormalChart e B x :=
      Classical.choice (normalChart x)
    have hpos := (c.mem_side_iff_coordinate_pos
      c.base.image_mem_neighborhood).1 (hx ▸ hpB)
    have hzero : c.coordinate (e x) 0 = 0 := by
      rw [c.coordinate_zero_apply,
        (c.base.normalCoordinate_eq_zero_iff
          c.base.image_mem_neighborhood).2 ⟨x, rfl⟩]
      cases c.orientation <;> simp [NormalOrientation.orient]
    rw [hzero] at hpos
    exact lt_irrefl 0 hpos

theorem sideClosure_interior_image
    (hBopen : IsOpen B)
    (hclosure : closure B = B ∪ Set.range e)
    (normalChart : ∀ x : SphereTwo,
      Nonempty (EmbeddedSphereSideNormalChart e B x)) :
    let _ := sideClosureChartedSpace hBopen hclosure normalChart
    Subtype.val '' (𝓡∂ 3).interior (closure B) = B := by
  dsimp only
  let _ := sideClosureChartedSpace hBopen hclosure normalChart
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (sideClosure_isInteriorPoint_iff
      hBopen hclosure normalChart p).1 hp
  · intro hyB
    let p : closure B := ⟨y, subset_closure hyB⟩
    refine ⟨p, ?_, rfl⟩
    exact (sideClosure_isInteriorPoint_iff
      hBopen hclosure normalChart p).2 hyB

theorem sideClosure_boundary_image
    (hBopen : IsOpen B)
    (hclosure : closure B = B ∪ Set.range e)
    (normalChart : ∀ x : SphereTwo,
      Nonempty (EmbeddedSphereSideNormalChart e B x)) :
    let _ := sideClosureChartedSpace hBopen hclosure normalChart
    Subtype.val '' (𝓡∂ 3).boundary (closure B) = Set.range e := by
  dsimp only
  let _ := sideClosureChartedSpace hBopen hclosure normalChart
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (sideClosure_isBoundaryPoint_iff
      hBopen hclosure normalChart p).1 hp
  · intro hyRange
    have hyClosure : y ∈ closure B := hclosure.symm.le (Or.inr hyRange)
    let p : closure B := ⟨y, hyClosure⟩
    refine ⟨p, ?_, rfl⟩
    exact (sideClosure_isBoundaryPoint_iff
      hBopen hclosure normalChart p).2 hyRange

noncomputable def smoothSideClosure
    [IsManifold (modelWithCornersSelf ℝ EuclideanThree) ∞ N]
    (hBopen : IsOpen B)
    (hclosure : closure B = B ∪ Set.range e)
    (normalChart : ∀ x : SphereTwo,
      Nonempty (EmbeddedSphereSideNormalChart e B x)) :
    SmoothSideClosure B (Set.range e) where
  chartedSpace := sideClosureChartedSpace hBopen hclosure normalChart
  isManifold := sideClosureIsManifold hBopen hclosure normalChart
  inclusion_isSmoothEmbedding :=
    sideClosure_inclusion_isSmoothEmbedding
      hBopen hclosure normalChart
  interior_image :=
    sideClosure_interior_image hBopen hclosure normalChart
  boundary_image :=
    sideClosure_boundary_image hBopen hclosure normalChart


@[instance_reducible]
noncomputable def compactClosureChartedSpace
    (he : Manifold.IsSmoothEmbedding (𝓡 2)
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e)
    (d : SphereSides (Set.range e)) :
    ChartedSpace (EuclideanHalfSpace 3) (closure d.compactSide) :=
  sideClosureChartedSpace d.isOpen_compactSide d.closure_compactSide
    (compactSideNormalChart_nonempty he d)


@[instance_reducible]
noncomputable def endClosureChartedSpace
    (he : Manifold.IsSmoothEmbedding (𝓡 2)
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e)
    (d : SphereSides (Set.range e)) :
    ChartedSpace (EuclideanHalfSpace 3) (closure d.endSide) :=
  sideClosureChartedSpace d.isOpen_endSide d.closure_endSide
    (endSideNormalChart_nonempty he d)

noncomputable def compactSmoothSideClosure
    [IsManifold (modelWithCornersSelf ℝ EuclideanThree) ∞ N]
    (he : Manifold.IsSmoothEmbedding (𝓡 2)
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e)
    (d : SphereSides (Set.range e)) :
    SmoothSideClosure d.compactSide (Set.range e) :=
  smoothSideClosure d.isOpen_compactSide d.closure_compactSide
    (compactSideNormalChart_nonempty he d)

noncomputable def endSmoothSideClosure
    [IsManifold (modelWithCornersSelf ℝ EuclideanThree) ∞ N]
    (he : Manifold.IsSmoothEmbedding (𝓡 2)
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e)
    (d : SphereSides (Set.range e)) :
    SmoothSideClosure d.endSide (Set.range e) :=
  smoothSideClosure d.isOpen_endSide d.closure_endSide
    (endSideNormalChart_nonempty he d)

theorem compactClosure_interior_image
    (he : Manifold.IsSmoothEmbedding (𝓡 2)
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e)
    (d : SphereSides (Set.range e)) :
    let _ := sideClosureChartedSpace d.isOpen_compactSide
      d.closure_compactSide (compactSideNormalChart_nonempty he d)
    Subtype.val '' (𝓡∂ 3).interior (closure d.compactSide) =
      d.compactSide := by
  exact
    sideClosure_interior_image d.isOpen_compactSide
      d.closure_compactSide (compactSideNormalChart_nonempty he d)

theorem compactClosure_boundary_image
    (he : Manifold.IsSmoothEmbedding (𝓡 2)
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e)
    (d : SphereSides (Set.range e)) :
    let _ := sideClosureChartedSpace d.isOpen_compactSide
      d.closure_compactSide (compactSideNormalChart_nonempty he d)
    Subtype.val '' (𝓡∂ 3).boundary (closure d.compactSide) =
      Set.range e := by
  exact
    sideClosure_boundary_image d.isOpen_compactSide
      d.closure_compactSide (compactSideNormalChart_nonempty he d)

theorem endClosure_interior_image
    (he : Manifold.IsSmoothEmbedding (𝓡 2)
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e)
    (d : SphereSides (Set.range e)) :
    let _ := sideClosureChartedSpace d.isOpen_endSide
      d.closure_endSide (endSideNormalChart_nonempty he d)
    Subtype.val '' (𝓡∂ 3).interior (closure d.endSide) =
      d.endSide := by
  exact
    sideClosure_interior_image d.isOpen_endSide d.closure_endSide
      (endSideNormalChart_nonempty he d)

theorem endClosure_boundary_image
    (he : Manifold.IsSmoothEmbedding (𝓡 2)
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e)
    (d : SphereSides (Set.range e)) :
    let _ := sideClosureChartedSpace d.isOpen_endSide
      d.closure_endSide (endSideNormalChart_nonempty he d)
    Subtype.val '' (𝓡∂ 3).boundary (closure d.endSide) =
      Set.range e := by
  exact
    sideClosure_boundary_image d.isOpen_endSide d.closure_endSide
      (endSideNormalChart_nonempty he d)

end ClosureAtlas

theorem exists_embeddedSphereSideNormalChart_of_isOpen_side
    (he : Manifold.IsSmoothEmbedding (𝓡 2)
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e)
    {B C : Set N} (hBopen : IsOpen B) (hCopen : IsOpen C)
    (hBcompl : B ⊆ (Set.range e)ᶜ)
    (hdisjoint : Disjoint B C) (hunion : B ∪ C = (Set.range e)ᶜ)
    (hBclosure : closure B = B ∪ Set.range e)
    (hCclosure : closure C = C ∪ Set.range e)
    (x : SphereTwo) :
    Nonempty (EmbeddedSphereSideNormalChart e B x) := by
  obtain ⟨c, hpos, hneg⟩ :=
    exists_embeddedSphereNormalChart_connected_halves he x
  have hCcompl : C ⊆ (Set.range e)ᶜ := by
    rw [← hunion]
    exact Set.subset_union_right
  have hposc : c.positiveHalf ⊆ B ∨ c.positiveHalf ⊆ C :=
    hpos.isPreconnected.subset_or_subset hBopen hCopen hdisjoint
      (fun y hy => by rw [hunion]; exact c.positiveHalf_subset_compl_range hy)
  have hnegc : c.negativeHalf ⊆ B ∨ c.negativeHalf ⊆ C :=
    hneg.isPreconnected.subset_or_subset hBopen hCopen hdisjoint
      (fun y hy => by rw [hunion]; exact c.negativeHalf_subset_compl_range hy)
  have hxC : e x ∈ closure C := by
    rw [hCclosure]
    exact Or.inr ⟨x, rfl⟩
  have hxB : e x ∈ closure B := by
    rw [hBclosure]
    exact Or.inr ⟨x, rfl⟩
  have hnotBothB : ¬ (c.positiveHalf ⊆ B ∧ c.negativeHalf ⊆ B) := by
    rintro ⟨hp, hn⟩
    have hdisjC : Disjoint C c.neighborhood := by
      rw [Set.disjoint_left]
      intro y hyC hyN
      have hyNotRange : y ∉ Set.range e := fun h => hCcompl hyC h
      have hyDiff : y ∈ c.neighborhood \ Set.range e := ⟨hyN, hyNotRange⟩
      rw [c.neighborhood_diff_range_eq_halves] at hyDiff
      rcases hyDiff with hyPos | hyNeg
      · exact Set.disjoint_left.mp hdisjoint (hp hyPos) hyC
      · exact Set.disjoint_left.mp hdisjoint (hn hyNeg) hyC
    have hsub : C ⊆ c.neighborhoodᶜ := fun y hy hyN => Set.disjoint_left.mp hdisjC hy hyN
    exact (closure_minimal hsub c.isOpen_neighborhood.isClosed_compl hxC)
      c.image_mem_neighborhood
  have hnotBothC : ¬ (c.positiveHalf ⊆ C ∧ c.negativeHalf ⊆ C) := by
    rintro ⟨hp, hn⟩
    have hdisjB : Disjoint B c.neighborhood := by
      rw [Set.disjoint_left]
      intro y hyB hyN
      have hyNotRange : y ∉ Set.range e := fun h => hBcompl hyB h
      have hyDiff : y ∈ c.neighborhood \ Set.range e := ⟨hyN, hyNotRange⟩
      rw [c.neighborhood_diff_range_eq_halves] at hyDiff
      rcases hyDiff with hyPos | hyNeg
      · exact Set.disjoint_left.mp hdisjoint hyB (hp hyPos)
      · exact Set.disjoint_left.mp hdisjoint hyB (hn hyNeg)
    have hsub : B ⊆ c.neighborhoodᶜ := fun y hy hyN => Set.disjoint_left.mp hdisjB hy hyN
    exact (closure_minimal hsub c.isOpen_neighborhood.isClosed_compl hxB)
      c.image_mem_neighborhood
  rcases hposc with hposB | hposC
  · rcases hnegc with hnegB | hnegC
    · exact absurd ⟨hposB, hnegB⟩ hnotBothB
    · refine ⟨c, .positive, ?_, ?_⟩
      · intro y hy
        change y ∈ B ↔ 0 < c.normalCoordinate y
        constructor
        · intro hyB
          have hyNotRange : y ∉ Set.range e := hBcompl hyB
          have hyDiff : y ∈ c.neighborhood \ Set.range e := ⟨hy, hyNotRange⟩
          rw [c.neighborhood_diff_range_eq_halves] at hyDiff
          rcases hyDiff with hyPos | hyNeg
          · exact hyPos.2
          · exact False.elim (Set.disjoint_left.1 hdisjoint hyB (hnegC hyNeg))
        · intro hyPos
          exact hposB ⟨hy, hyPos⟩
      · intro y hy
        change y ∈ closure B ↔ 0 ≤ c.normalCoordinate y
        rw [hBclosure]
        constructor
        · rintro (hyB | hyS)
          · have hyNotRange : y ∉ Set.range e := hBcompl hyB
            have hyDiff : y ∈ c.neighborhood \ Set.range e := ⟨hy, hyNotRange⟩
            rw [c.neighborhood_diff_range_eq_halves] at hyDiff
            rcases hyDiff with hyPos | hyNeg
            · exact hyPos.2.le
            · exact False.elim (Set.disjoint_left.1 hdisjoint hyB (hnegC hyNeg))
          · exact (c.normalCoordinate_eq_zero_iff hy).2 hyS |>.ge
        · intro hnonneg
          rcases hnonneg.eq_or_lt with hzero | hpositive
          · exact Or.inr ((c.normalCoordinate_eq_zero_iff hy).1 hzero.symm)
          · exact Or.inl (hposB ⟨hy, hpositive⟩)
  · rcases hnegc with hnegB | hnegC
    · refine ⟨c, .negative, ?_, ?_⟩
      · intro y hy
        change y ∈ B ↔ 0 < -c.normalCoordinate y
        rw [neg_pos]
        constructor
        · intro hyB
          have hyNotRange : y ∉ Set.range e := hBcompl hyB
          have hyDiff : y ∈ c.neighborhood \ Set.range e := ⟨hy, hyNotRange⟩
          rw [c.neighborhood_diff_range_eq_halves] at hyDiff
          rcases hyDiff with hyPos | hyNeg
          · exact False.elim (Set.disjoint_left.1 hdisjoint hyB (hposC hyPos))
          · exact hyNeg.2
        · intro hyNeg
          exact hnegB ⟨hy, hyNeg⟩
      · intro y hy
        change y ∈ closure B ↔ 0 ≤ -c.normalCoordinate y
        rw [hBclosure, neg_nonneg]
        constructor
        · rintro (hyB | hyS)
          · have hyNotRange : y ∉ Set.range e := hBcompl hyB
            have hyDiff : y ∈ c.neighborhood \ Set.range e := ⟨hy, hyNotRange⟩
            rw [c.neighborhood_diff_range_eq_halves] at hyDiff
            rcases hyDiff with hyPos | hyNeg
            · exact False.elim (Set.disjoint_left.1 hdisjoint hyB (hposC hyPos))
            · exact hyNeg.2.le
          · exact (c.normalCoordinate_eq_zero_iff hy).2 hyS |>.le
        · intro hnonpos
          rcases hnonpos.eq_or_lt with hzero | hnegative
          · exact Or.inr ((c.normalCoordinate_eq_zero_iff hy).1 hzero)
          · exact Or.inl (hnegB ⟨hy, hnegative⟩)
    · exact absurd ⟨hposC, hnegC⟩ hnotBothC

end DifferentialGeometry.Topology.SphereSeparation
