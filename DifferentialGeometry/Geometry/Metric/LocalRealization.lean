import DifferentialGeometry.Analysis.FiniteDimensional.BilinearPositivity
import DifferentialGeometry.Geometry.Metric.Construction.SmoothMetricFromCoefficients
import DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.OpenSubtype
import DifferentialGeometry.Bundle.ContinuousLinearMapSection.Basic

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Geometry
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Geometry.Metric
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [T2Space M] in
private theorem eventually_pos_bilinear_section
    (b : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (hb : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun y : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) y (b y)))
    (x : M) (hpos : ∀ v : TangentSpace I x, v ≠ 0 → 0 < b x v v) :
    ∀ᶠ y in 𝓝 x, ∀ v : TangentSpace I y, v ≠ 0 → 0 < b y v v := by
  let e := trivializationAt E (TangentSpace I) x
  let C : M → E →L[ℝ] E →L[ℝ] ℝ := fun y =>
    (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
      (fun z => TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ) x ⟨y, b y⟩).2
  have hC : ContinuousAt C x := (FiberBundle.continuousAt_section _ x).mp hb.continuous.continuousAt
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x
  have hCx : ∀ v : E, v ≠ 0 → 0 < C x v v := by
    intro v hv
    rw [metricCoeffInModel_apply x hx]
    apply hpos
    intro heq
    have hv0 := congrArg (e.continuousLinearMapAt ℝ x) heq
    rw [e.continuousLinearMapAt_symmL hx, map_zero] at hv0
    exact hv hv0
  have hcone : ∀ᶠ y in 𝓝 x, ∀ v : E, v ≠ 0 → 0 < C y v v :=
    hC (DifferentialGeometry.Analysis.isOpen_pos_diagonal.mem_nhds hCx)
  filter_upwards [hcone, e.open_baseSet.mem_nhds hx] with y hy hbase
  intro v hv
  let w := e.continuousLinearMapAt ℝ y v
  have hw : w ≠ 0 := by
    intro heq
    have hv0 := congrArg (e.symmL ℝ y) heq
    rw [e.symmL_continuousLinearMapAt hbase, map_zero] at hv0
    exact hv hv0
  have hval := hy w hw
  rw [metricCoeffInModel_apply x hbase] at hval
  change 0 < b y (e.symmL ℝ y (e.continuousLinearMapAt ℝ y v))
    (e.symmL ℝ y (e.continuousLinearMapAt ℝ y v)) at hval
  rwa [e.symmL_continuousLinearMapAt hbase] at hval

theorem contMDiff_bilinear_restrictOpen
    (b : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (U : TopologicalSpace.Opens M)
    (hb : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun y : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) y (b y)) (U : Set M)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun y : U => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun z : U => TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ)
        y (b (y : M))) := by
  apply contMDiff_continuousLinearMap_section_of_apply
    (V₂ := fun y : U => TangentSpace I y →L[ℝ] ℝ)
    (φ := fun y : U => b (y : M))
  intro Y
  apply contMDiff_continuousLinearMap_section_of_apply
    (V₂ := fun _ : U => ℝ) (φ := fun y : U => b (y : M) (Y y))
  intro W
  let incl : U → M := Subtype.val
  have hTan : ContMDiff I.tangent I.tangent ∞ (tangentMap I I incl) :=
    (contMDiff_subtype_val (I := I) (U := U)).contMDiff_tangentMap (le_refl _)
  have hY : ContMDiff I I.tangent ∞
      (fun y : U => (⟨(y : M), mfderiv I I incl y (Y y)⟩ : TangentBundle I M)) :=
    hTan.comp Y.contMDiff
  have hW : ContMDiff I I.tangent ∞
      (fun y : U => (⟨(y : M), mfderiv I I incl y (W y)⟩ : TangentBundle I M)) :=
    hTan.comp W.contMDiff
  have hcomp : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun y : U => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ)
        (y : M) (b (y : M))) :=
    hb.comp_contMDiff (contMDiff_subtype_val (I := I) (U := U)) (fun y => y.2)
  have htotal := ContMDiff.clm_bundle_apply₂
    (E₁ := fun z : M => TangentSpace I z)
    (E₂ := fun z : M => TangentSpace I z) (E₃ := fun _ : M => ℝ)
    (b := fun y : U => (y : M)) (ψ := fun y : U => b (y : M))
    (v := fun y : U => mfderiv I I incl y (Y y))
    (w := fun y : U => mfderiv I I incl y (W y)) hcomp hY hW
  have hscalar : ContMDiff I 𝓘(ℝ) ∞ (fun y : U => b (y : M) (Y y) (W y)) := by
    have hscalar' : ContMDiff I 𝓘(ℝ) ∞
        (fun y : U => b (y : M) (mfderiv I I incl y (Y y))
          (mfderiv I I incl y (W y))) := by
      intro y
      have hat := htotal y
      rw [contMDiffAt_totalSpace] at hat
      simpa using hat.2
    simpa only [incl, mfderiv_subtype_val_apply] using hscalar'
  intro y
  rw [contMDiffAt_section]
  refine hscalar.contMDiffAt.congr_of_eventuallyEq ?_
  filter_upwards with z
  rfl

theorem exists_local_metric_of_bilinear_section
    (b : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (hb : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun y : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) y (b y)))
    (hsymm : ∀ (y : M) (v w : TangentSpace I y), b y v w = b y w v)
    (x : M) (hpos : ∀ v : TangentSpace I x, v ≠ 0 → 0 < b x v v) :
    ∃ V : TopologicalSpace.Opens M, x ∈ V ∧
      ∃ g : SmoothRiemannianMetric I V,
        ∀ (y : V) (v w : TangentSpace I y), g.inner y v w = b (y : M) v w := by
  obtain ⟨s, hs, hopen, hx⟩ := mem_nhds_iff.mp (eventually_pos_bilinear_section b hb x hpos)
  let V : TopologicalSpace.Opens M := ⟨s, hopen⟩
  refine ⟨V, hx, ?_⟩
  refine ⟨{
    inner := fun y : V => b (y : M)
    symm := fun y v w => hsymm (y : M) v w
    pos := fun y v hv => hs y.2 v hv
    isVonNBounded := fun y => posDef_isVonNBounded (E := E) (b (y : M)) (hs y.2)
    contMDiff := contMDiff_bilinear_restrictOpen b V hb.contMDiffOn }, ?_⟩
  intro y v w
  rfl

end DifferentialGeometry.Geometry.Metric
