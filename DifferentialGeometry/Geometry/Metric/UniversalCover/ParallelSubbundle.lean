import DifferentialGeometry.Geometry.Metric.UniversalCover.Coordinates
import DifferentialGeometry.Bundle.SmoothSubbundle.Basic
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Subbundle
import DifferentialGeometry.Geometry.Connection.LeviCivita.CorrectionContraction

open Set Filter Bundle
open scoped Topology ContDiff Manifold

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [LocallyPathConnectedSpace M]
variable [SemilocallySimplyConnectedSpace M] [Inhabited M]

private theorem proj_mem_chart_source
    (a x : UniversalCover M) (hx : x ∈ (chartAt H a).source) :
    proj x ∈ (chartAt H (proj a)).source := by
  have hx' : x ∈ (localSection a).source ∩
      (localSection a) ⁻¹' (chartAt H (proj a)).source := by
    rw [← coverChartAt_source_eq a]
    exact hx
  have hproj : (localSection a) x = proj x := by
    have h := congrArg (fun f => f x) (proj_eq_localSection a)
    exact h.symm
  simpa only [Set.mem_preimage, hproj] using hx'.2

private theorem contMDiffAt_lift_tangent_section
    (s : ∀ x : M, TangentSpace I x)
    (a : UniversalCover M)
    (hs : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (s x)) (proj a)) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : UniversalCover M =>
        (TotalSpace.mk' E x (s (proj x)) :
          TotalSpace E (TangentSpace I : UniversalCover M → Type _))) a := by
  refine (Bundle.contMDiffAt_section
    (s := fun x : UniversalCover M =>
      (show TangentSpace I x from s (proj x))) a).2 ?_
  have hsBase := hs
  rw [Bundle.contMDiffAt_section] at hsBase
  have hcomp := hsBase.comp a
    (proj_contMDiff (I := I) (M := M)).contMDiffAt
  apply hcomp.congr_of_eventuallyEq
  have hnhds : (chartAt H a).source ∈ 𝓝 a :=
    (chartAt H a).open_source.mem_nhds (mem_chart_source H a)
  filter_upwards [hnhds] with x hx
  have hpx := proj_mem_chart_source a x hx
  have hUC := Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ)
    (trivializationAt E (TangentSpace I : UniversalCover M → Type _) a)
    hx (s (proj x))
  have hBase := Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ)
    (trivializationAt E (TangentSpace I : M → Type _) (proj a))
    hpx (s (proj x))
  have hcoords :
      (trivializationAt E (TangentSpace I : UniversalCover M → Type _) a).continuousLinearMapAt
          ℝ x =
        (trivializationAt E (TangentSpace I : M → Type _) (proj a)).continuousLinearMapAt
          ℝ (proj x) := by
    rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hx,
      TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hpx]
    exact uc_tangentBundleCore_coordChange_agree (I := I) x a
      ⟨mem_chart_source H x, hx⟩
  rw [Function.comp_apply]
  calc
    (trivializationAt E (TangentSpace I : UniversalCover M → Type _) a
          ⟨x, s (proj x)⟩).2 =
        (trivializationAt E (TangentSpace I : UniversalCover M → Type _) a).continuousLinearMapAt
          ℝ x (s (proj x)) := hUC.symm
    _ = (trivializationAt E (TangentSpace I : M → Type _) (proj a)).continuousLinearMapAt
          ℝ (proj x) (s (proj x)) :=
      congrArg (fun L : E →L[ℝ] E => L (s (proj x))) hcoords
    _ = (trivializationAt E (TangentSpace I : M → Type _) (proj a)
          ⟨proj x, s (proj x)⟩).2 := hBase

private theorem contMDiff_lift_tangent_section
    (s : ∀ x : M, TangentSpace I x)
    (hs : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (s x))) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : UniversalCover M =>
        (TotalSpace.mk' E x (s (proj x)) :
          TotalSpace E (TangentSpace I : UniversalCover M → Type _))) := by
  intro a
  exact contMDiffAt_lift_tangent_section (I := I) (M := M) s a (hs (proj a))

private theorem contMDiffOn_lift_tangent_section
    (s : ∀ x : M, TangentSpace I x) {U : Set M}
    (hs : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (s x)) U)
    (hU : IsOpen U) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : UniversalCover M =>
        (TotalSpace.mk' E x (s (proj x)) :
          TotalSpace E (TangentSpace I : UniversalCover M → Type _)))
      (proj ⁻¹' U) := by
  intro a ha
  exact (contMDiffAt_lift_tangent_section (I := I) (M := M) s a
    ((hs (proj a) ha).contMDiffAt (hU.mem_nhds ha))).contMDiffWithinAt

def liftTangentSection
    (s : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : UniversalCover M → Type _) where
  toFun x := s (proj x)
  contMDiff_toFun := contMDiff_lift_tangent_section (I := I) (M := M) s s.contMDiff

@[simp]
theorem liftTangentSection_apply
    (s : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) (x : UniversalCover M) :
    liftTangentSection (I := I) (M := M) s x = s (proj x) :=
  rfl

def liftTangentSubbundle
    (S : ContMDiffVectorSubbundle
      (I := I) (F := E) (V := (TangentSpace I : M → Type _))
      (n := (∞ : WithTop ℕ∞))) :
    ContMDiffVectorSubbundle
      (I := I) (F := E)
      (V := (TangentSpace I : UniversalCover M → Type _))
      (n := (∞ : WithTop ℕ∞)) where
  fiber x := S.fiber (proj x)
  rank := S.rank
  exists_isSubbundleFrameOn x := by
    obtain ⟨U, s, hU, hx, hs⟩ := S.exists_frame (proj x)
    refine ⟨proj ⁻¹' U, fun i y => s i (proj y),
      hU.preimage (proj_contMDiff (I := I) (M := M)).continuous, hx, ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · intro y hy
      exact hs.linearIndependent hy
    · intro y hy
      exact hs.spans hy
    · intro i
      exact contMDiffOn_lift_tangent_section (I := I) (M := M) (s i)
        (hs.contMDiffOn i) hU

@[simp]
theorem liftTangentSubbundle_fiber
    (S : ContMDiffVectorSubbundle
      (I := I) (F := E) (V := (TangentSpace I : M → Type _))
      (n := (∞ : WithTop ℕ∞)))
    (x : UniversalCover M) :
    (liftTangentSubbundle (I := I) (M := M) S).fiber x = S.fiber (proj x) :=
  rfl

@[simp]
theorem liftTangentSubbundle_rank
    (S : ContMDiffVectorSubbundle
      (I := I) (F := E) (V := (TangentSpace I : M → Type _))
      (n := (∞ : WithTop ℕ∞))) :
    (liftTangentSubbundle (I := I) (M := M) S).rank = S.rank :=
  rfl

private theorem trivToE_lifted_apply
    (a x : UniversalCover M) (hx : x ∈ (chartAt H a).source) (v : E) :
    DifferentialGeometry.Geometry.Connection.trivToE (I := I) a x v =
      DifferentialGeometry.Geometry.Connection.trivToE (I := I) (proj a) (proj x) v := by
  have hpx := proj_mem_chart_source a x hx
  have hcoords :
      (trivializationAt E (TangentSpace I : UniversalCover M → Type _) a).continuousLinearMapAt
          ℝ x =
        (trivializationAt E (TangentSpace I : M → Type _) (proj a)).continuousLinearMapAt
          ℝ (proj x) := by
    rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hx,
      TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hpx]
    exact uc_tangentBundleCore_coordChange_agree (I := I) x a
      ⟨mem_chart_source H x, hx⟩
  exact congrArg (fun L : E →L[ℝ] E => L v) hcoords

private theorem trivFromE_lifted_apply
    (a x : UniversalCover M) (hx : x ∈ (chartAt H a).source) (v : E) :
    DifferentialGeometry.Geometry.Connection.trivFromE (I := I) a x v =
      DifferentialGeometry.Geometry.Connection.trivFromE (I := I) (proj a) (proj x) v := by
  have hpx := proj_mem_chart_source a x hx
  have hcoords :
      (trivializationAt E (TangentSpace I : UniversalCover M → Type _) a).symmL ℝ x =
        (trivializationAt E (TangentSpace I : M → Type _) (proj a)).symmL ℝ (proj x) := by
    rw [TangentBundle.symmL_trivializationAt_eq_core hx,
      TangentBundle.symmL_trivializationAt_eq_core hpx]
    exact uc_tangentBundleCore_coordChange_agree (I := I) a x
      ⟨hx, mem_chart_source H x⟩
  exact congrArg (fun L : E →L[ℝ] E => L v) hcoords

omit [IsManifold I ∞ M] in
private theorem proj_extChartAt_symm
    (a : UniversalCover M) {y : E} (hy : y ∈ (extChartAt I a).target) :
    proj ((extChartAt I a).symm y) =
      (extChartAt I (proj a)).symm y := by
  let x : UniversalCover M := (extChartAt I a).symm y
  have hxExt : x ∈ (extChartAt I a).source :=
    (extChartAt I a).map_target hy
  have hx : x ∈ (chartAt H a).source := by
    simpa only [extChartAt_source] using hxExt
  have hpx := proj_mem_chart_source a x hx
  have hpxExt : proj x ∈ (extChartAt I (proj a)).source := by
    simpa only [extChartAt_source] using hpx
  calc
    proj x = (extChartAt I (proj a)).symm
        (extChartAt I (proj a) (proj x)) :=
      ((extChartAt I (proj a)).left_inv hpxExt).symm
    _ = (extChartAt I (proj a)).symm (extChartAt I a x) := by
      rw [extChartAt_proj_eq (I := I) (M := M) a x]
    _ = (extChartAt I (proj a)).symm y := by
      rw [(extChartAt I a).right_inv hy]

open DifferentialGeometry.Geometry.Connection

variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [ConnectedSpace M] in
theorem leviCivita_lift_tangent_section
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (s : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : UniversalCover M) (v : TangentSpace I x) :
    (LeviCivita (I := I) (liftedMetric (I := I) g))
        (liftTangentSection (I := I) (M := M) s) x v =
      (LeviCivita (I := I) g) s (proj x) v := by
  let vBase : TangentSpace I (proj x) := v
  change (LeviCivita (I := I) (liftedMetric (I := I) g))
      (liftTangentSection (I := I) (M := M) s) x v =
    (LeviCivita (I := I) g) s (proj x) vBase
  have hgoodLift : x ∈ chartLeviCivitaGoodSet (I := I) x :=
    self_mem_chartLeviCivitaGoodSet (I := I) x
  have hgoodBase : proj x ∈ chartLeviCivitaGoodSet (I := I) (proj x) :=
    self_mem_chartLeviCivitaGoodSet (I := I) (proj x)
  have hsLiftMD :=
    (liftTangentSection (I := I) (M := M) s).mdifferentiableAt (x := x)
  have hsMD := s.mdifferentiableAt (x := proj x)
  rw [LeviCivita_chart_apply (I := I) (liftedMetric (I := I) g) x hgoodLift hsLiftMD v,
    LeviCivita_chart_apply (I := I) g (proj x) hgoodBase hsMD vBase]
  rw [chartLeviCivita_apply (I := I) (liftedMetric (I := I) g) x
      (liftTangentSection (I := I) (M := M) s) hgoodLift v,
    chartLeviCivita_apply (I := I) g (proj x) s hgoodBase vBase]
  have hchart : x ∈ (chartAt H x).source := mem_chart_source H x
  have hvalue :
      chartESectionRepr (I := I) x
          (liftTangentSection (I := I) (M := M) s) x =
        chartESectionRepr (I := I) (proj x) s (proj x) := by
    change trivToE (I := I) x x (s (proj x)) =
      trivToE (I := I) (proj x) (proj x) (s (proj x))
    exact trivToE_lifted_apply (I := I) (M := M) x x hchart (s (proj x))
  have hrep :
      (chartESectionRepr (I := I) x
          (liftTangentSection (I := I) (M := M) s) ∘
          (extChartAt I x).symm) =ᶠ[𝓝 (extChartAt I x x)]
        (chartESectionRepr (I := I) (proj x) s ∘
          (extChartAt I (proj x)).symm) := by
    have htarget : (extChartAt I x).target ∈ 𝓝 (extChartAt I x x) :=
      (isOpen_extChartAt_target (I := I) x).mem_nhds
        ((extChartAt I x).map_source (mem_extChartAt_source x))
    filter_upwards [htarget] with y hy
    let z : UniversalCover M := (extChartAt I x).symm y
    have hzExt : z ∈ (extChartAt I x).source := (extChartAt I x).map_target hy
    have hz : z ∈ (chartAt H x).source := by
      simpa only [extChartAt_source] using hzExt
    have hproj := proj_extChartAt_symm (I := I) (M := M) x hy
    have htriv := trivToE_lifted_apply (I := I) (M := M) x z hz (s (proj z))
    change trivToE (I := I) x z (s (proj z)) =
      trivToE (I := I) (proj x) ((extChartAt I (proj x)).symm y)
        (s ((extChartAt I (proj x)).symm y))
    rw [← hproj]
    exact htriv
  have hderiv :
      fderiv ℝ
          (chartESectionRepr (I := I) x
            (liftTangentSection (I := I) (M := M) s) ∘
            (extChartAt I x).symm)
          (extChartAt I x x) =
        fderiv ℝ
          (chartESectionRepr (I := I) (proj x) s ∘
            (extChartAt I (proj x)).symm)
          (extChartAt I (proj x) (proj x)) := by
    rw [← extChartAt_proj_eq (I := I) (M := M) x x]
    exact Filter.EventuallyEq.fderiv_eq hrep
  have hcorrection :
      christoffelCorrection (I := I) (liftedMetric (I := I) g) x x
          (chartESectionRepr (I := I) (proj x) s (proj x)) v =
        christoffelCorrection (I := I) g (proj x) (proj x)
          (chartESectionRepr (I := I) (proj x) s (proj x)) vBase := by
    rw [correction_eq_contr, correction_eq_contr]
    rw [trivToE_lifted_apply (I := I) (M := M) x x hchart v]
    exact chartChristoffelContraction_lifted (I := I) (M := M) g x x hchart
      (trivToE (I := I) (proj x) (proj x) vBase)
      (chartESectionRepr (I := I) (proj x) s (proj x))
  rw [trivToE_lifted_apply (I := I) (M := M) x x hchart v,
    hvalue, hderiv, hcorrection]
  exact trivFromE_lifted_apply (I := I) (M := M) x x hchart _

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [ConnectedSpace M] in
private theorem exists_local_parallel_unit_section_liftTangentSubbundle
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (S : ContMDiffVectorSubbundle
      (I := I) (F := E) (V := (TangentSpace I : M → Type _))
      (n := (∞ : WithTop ℕ∞)))
    (hSrank : S.rank = 1)
    (hS : DifferentialGeometry.Geometry.Connection.IsParallelSubmoduleFamily g S.fiber)
    (x : UniversalCover M) :
    ∃ (U : Set (UniversalCover M))
      (s : ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : UniversalCover M → Type _)),
      IsOpen U ∧ x ∈ U ∧
      (∀ y ∈ U, s y ∈
        (liftTangentSubbundle (I := I) (M := M) S).fiber y) ∧
      (∀ y ∈ U,
        (liftedMetric (I := I) g).inner y (s y) (s y) = 1) ∧
      (∀ y ∈ U, ∀ v : TangentSpace I y,
        (LeviCivita (I := I) (liftedMetric (I := I) g)) s y v = 0) := by
  obtain ⟨U, s, hU, hx, hs_mem, hs_unit, hs_parallel⟩ :=
    DifferentialGeometry.Geometry.Connection.ContMDiffVectorSubbundle.exists_local_parallel_unit_section_of_rank_eq_one
      g S hSrank hS (proj x)
  let s' := liftTangentSection (I := I) (M := M) s
  refine ⟨proj ⁻¹' U, s',
    hU.preimage (proj_contMDiff (I := I) (M := M)).continuous, hx, ?_, ?_, ?_⟩
  · intro y hy
    exact hs_mem (proj y) hy
  · intro y hy
    exact hs_unit (proj y) hy
  · intro y hy v
    rw [leviCivita_lift_tangent_section (I := I) (M := M)]
    exact hs_parallel (proj y) hy v

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [ConnectedSpace M] in
private theorem liftTangentSubbundle_isCovariantlyInvariant_of_rank_eq_one
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (S : ContMDiffVectorSubbundle
      (I := I) (F := E) (V := (TangentSpace I : M → Type _))
      (n := (∞ : WithTop ℕ∞)))
    (hSrank : S.rank = 1)
    (hS : DifferentialGeometry.Geometry.Connection.IsParallelSubmoduleFamily g S.fiber) :
    DifferentialGeometry.Geometry.Connection.IsCovariantlyInvariantSubmoduleFamily
      (LeviCivita (I := I) (liftedMetric (I := I) g))
      (liftTangentSubbundle (I := I) (M := M) S).fiber := by
  intro sigma U hU hsigma x hx v
  let S' := liftTangentSubbundle (I := I) (M := M) S
  let g' := liftedMetric (I := I) g
  obtain ⟨W, e, hW, hxW, he_mem, he_unit, he_parallel⟩ :=
    exists_local_parallel_unit_section_liftTangentSubbundle
      (I := I) (M := M) g S hSrank hS x
  let f : UniversalCover M → ℝ := fun z => g'.inner z (sigma z) (e z)
  have hf : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f x :=
    DifferentialGeometry.Geometry.Curvature.CovariantDerivative.metric_inner_contMDiffAt
      (I := I) g' sigma.contMDiff.contMDiffAt e.contMDiff.contMDiffAt le_rfl
  have hfe : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun z : UniversalCover M =>
        TotalSpace.mk' E z (f z • e z)) x :=
    (hf.mdifferentiableAt (by simp)).smul_section
      (e.contMDiff.mdifferentiableAt (by simp))
  have heq : (fun z => sigma z) =ᶠ[𝓝 x] fun z => f z • e z := by
    filter_upwards [hU.mem_nhds hx, hW.mem_nhds hxW] with z hzU hzW
    have he_ne : e z ≠ 0 := by
      intro he0
      have := he_unit z hzW
      rw [he0] at this
      simp at this
    have hfin : Module.finrank ℝ (S'.fiber z) = 1 := by
      rw [S'.finrank_fiber]
      exact hSrank
    have hspan : S'.fiber z = ℝ ∙ e z :=
      eq_span_singleton_of_mem_of_finrank_eq_one
        hfin (he_mem z hzW) he_ne
    have hsigma_mem := hsigma z hzU
    change sigma z ∈ S'.fiber z at hsigma_mem
    rw [hspan, Submodule.mem_span_singleton] at hsigma_mem
    obtain ⟨a, ha⟩ := hsigma_mem
    have hfa : f z = a := by
      simp only [f, g']
      rw [← ha, map_smul, smul_apply, smul_eq_mul, he_unit z hzW, mul_one]
    change sigma z = f z • e z
    rw [hfa]
    exact ha.symm
  have hcov :=
    (LeviCivita (I := I) g').isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      sigma.mdifferentiableAt hfe (Filter.univ_mem : Set.univ ∈ 𝓝 x) heq
  have hleibniz :=
    (LeviCivita (I := I) g').isCovariantDerivativeOnUniv.leibniz
      (e.contMDiff.mdifferentiableAt (by simp))
      (hf.mdifferentiableAt (by simp))
  have hcovv := congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L v)
    hcov
  have hleibnizv := congrArg
    (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L v) hleibniz
  have he_ne : e x ≠ 0 := by
    intro he0
    have := he_unit x hxW
    rw [he0] at this
    simp at this
  have hfin : Module.finrank ℝ (S'.fiber x) = 1 := by
    rw [S'.finrank_fiber]
    exact hSrank
  have hspan : S'.fiber x = ℝ ∙ e x :=
    eq_span_singleton_of_mem_of_finrank_eq_one
      hfin (he_mem x hxW) he_ne
  have he_parallel' : (LeviCivita (I := I) g') e x v = 0 :=
    he_parallel x hxW v
  change (LeviCivita (I := I) g') sigma x v ∈ S'.fiber x
  rw [hcovv]
  change (LeviCivita (I := I) g') (f • fun z => e z) x v ∈ S'.fiber x
  rw [hleibnizv]
  simp only [add_apply, smul_apply,
    he_parallel', smul_zero, zero_add]
  rw [hspan]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton (e x)))

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [ConnectedSpace M] in
theorem liftTangentSubbundle_isParallel_of_rank_eq_one
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (S : ContMDiffVectorSubbundle
      (I := I) (F := E) (V := (TangentSpace I : M → Type _))
      (n := (∞ : WithTop ℕ∞)))
    (hSrank : S.rank = 1)
    (hS : DifferentialGeometry.Geometry.Connection.IsParallelSubmoduleFamily g S.fiber) :
    DifferentialGeometry.Geometry.Connection.IsParallelSubmoduleFamily
      (liftedMetric (I := I) g)
      (liftTangentSubbundle (I := I) (M := M) S).fiber := by
  apply DifferentialGeometry.Geometry.Connection.ContMDiffVectorSubbundle.isParallelSubmoduleFamily_of_rank_eq_one
    (I := I) (liftedMetric (I := I) g)
      (liftTangentSubbundle (I := I) (M := M) S)
  · simpa using hSrank
  · exact liftTangentSubbundle_isCovariantlyInvariant_of_rank_eq_one
      (I := I) (M := M) g S hSrank hS

end DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover
