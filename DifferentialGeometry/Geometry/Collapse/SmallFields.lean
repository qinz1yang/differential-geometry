import DifferentialGeometry.Geometry.Collapse.SmallGeometry
import DifferentialGeometry.Geometry.Operator.Pullback
import DifferentialGeometry.Geometry.Metric.PullbackScaling
import DifferentialGeometry.Geometry.Metric.Approximation.ConvergenceIsometry
import DifferentialGeometry.Geometry.Metric.Scaling.RescaleIsometry

/-!
Functions, cone maps and partial smooth charts return along the same outer small model.
The gradient identities preserve the actual metric and every quantitative scalar test.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Manifold Set
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓡 3

variable {M : Type u} [mM : MetricSpace M] [i1 : ChartedSpace E3 M] [i2 : IsManifold I3 ∞ M]
  (S : SmallManifoldModel (I := I3) M)

def smallModel_backFunction {Y : Type*} (f : S.Carrier → Y) : M → Y :=
  f ∘ S.diffeo.symm

omit [IsManifold I3 ∞ M] in
theorem smallModel_backFunction_square {Y : Type*} (f : S.Carrier → Y) (x : S.Carrier) :
    smallModel_backFunction S f (S.diffeo x) = f x := by
  simp only [smallModel_backFunction, Function.comp_apply, Diffeomorph.symm_apply_apply]

omit [IsManifold I3 ∞ M] in
theorem smallModel_backFunction_smoothOn (f : S.Carrier → ℝ) (U : Set S.Carrier)
    (hf : ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ f U) :
    ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ (smallModel_backFunction S f) (S.diffeo '' U) := by
  apply hf.comp S.diffeo.symm.contMDiff.contMDiffOn
  rintro x ⟨y, hy, rfl⟩
  simpa only [mem_preimage, Diffeomorph.symm_apply_apply] using hy

omit [IsManifold I3 ∞ M] in
theorem smallModel_backFunction_smooth (f : S.Carrier → ℝ)
    (hf : ContMDiff I3 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff I3 𝓘(ℝ, ℝ) ∞ (smallModel_backFunction S f) :=
  hf.comp S.diffeo.symm.contMDiff

theorem smallModel_backFunction_gradientNorm (g : SmoothRiemannianMetric I3 M)
    (f : S.Carrier → ℝ) (x : M)
    (hf : MDifferentiableAt I3 𝓘(ℝ, ℝ) f (S.diffeo.symm x)) :
    g.inner x (gradFun g (smallModel_backFunction S f) x)
      (gradFun g (smallModel_backFunction S f) x) =
    (S.metric g).inner (S.diffeo.symm x)
      (gradFun (S.metric g) f (S.diffeo.symm x))
      (gradFun (S.metric g) f (S.diffeo.symm x)) := by
  have heq : Diffeomorph.pullbackMetricCross (S.metric g) S.diffeo.symm = g := by
    rw [SmallManifoldModel.metric, Diffeomorph.pullbackMetricCross_trans,
      Diffeomorph.symm_trans_self, Diffeomorph.pullbackMetricCross_refl]
  conv_lhs => rw [← heq]
  rw [show gradFun (Diffeomorph.pullbackMetricCross (S.metric g) S.diffeo.symm)
      (smallModel_backFunction S f) x =
      (S.diffeo.symm.mfderivToContinuousLinearEquiv (by simp) x).symm
        (gradFun (S.metric g) f (S.diffeo.symm x)) from
    gradientFun_pullbackCross (S.metric g) S.diffeo.symm f x hf]
  rw [Diffeomorph.pullbackMetricCross_inner]
  rw [← S.diffeo.symm.mfderivToContinuousLinearEquiv_coe (by simp)]
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]

theorem smallModel_backFunction_gradientNonzero (g : SmoothRiemannianMetric I3 M)
    (f : S.Carrier → ℝ) (x : M)
    (hf : MDifferentiableAt I3 𝓘(ℝ, ℝ) f (S.diffeo.symm x))
    (hg : gradFun (S.metric g) f (S.diffeo.symm x) ≠ 0) :
    gradFun g (smallModel_backFunction S f) x ≠ 0 := by
  intro hzero
  have hn := smallModel_backFunction_gradientNorm S g f x hf
  rw [hzero] at hn
  have hpos := (S.metric g).pos (S.diffeo.symm x) _ hg
  simp only [map_zero] at hn
  exact (ne_of_gt hpos) hn.symm

variable {N : Type*} [i3 : TopologicalSpace N] [i4 : ChartedSpace E3 N]

def smallModel_backPartial (P : PartialDiffeomorph I3 I3 S.Carrier N ∞) :
    PartialDiffeomorph I3 I3 M N ∞ := S.diffeo.symm.toPartialDiffeomorph.trans P

omit [IsManifold I3 ∞ M] in
theorem smallModel_backPartial_apply (P : PartialDiffeomorph I3 I3 S.Carrier N ∞)
    (x : M) : smallModel_backPartial S P x = P (S.diffeo.symm x) := rfl

omit [IsManifold I3 ∞ M] in
theorem smallModel_backPartial_source (P : PartialDiffeomorph I3 I3 S.Carrier N ∞) :
    (smallModel_backPartial S P).source = S.diffeo '' P.source := by
  ext x
  change x ∈ univ ∩ S.diffeo.symm ⁻¹' P.source ↔ x ∈ S.diffeo '' P.source
  simp only [mem_inter_iff, mem_univ, true_and, mem_preimage]
  constructor
  · intro hx
    exact ⟨S.diffeo.symm x, hx, S.diffeo.apply_symm_apply x⟩
  · rintro ⟨y, hy, rfl⟩
    simpa only [Diffeomorph.symm_apply_apply] using hy

omit [IsManifold I3 ∞ M] in
theorem smallModel_backPartial_target (P : PartialDiffeomorph I3 I3 S.Carrier N ∞) :
    (smallModel_backPartial S P).target = P.target := by
  ext x
  change x ∈ P.target ∩ P.symm ⁻¹' univ ↔ x ∈ P.target
  simp

omit [IsManifold I3 ∞ M] in
theorem smallModel_backPartial_ball_source
    (P : PartialDiffeomorph I3 I3 S.Carrier N ∞) (p : S.Carrier) (r : ℝ)
    (hP : letI _smallMetric := S.metricSpace
      P.source = Metric.ball p r) :
    (smallModel_backPartial S P).source = Metric.ball (S.diffeo p) r := by
  let smallMetric := S.metricSpace
  rw [smallModel_backPartial_source, hP]
  ext x
  simp only [mem_image, Metric.mem_ball]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ((S.isometryEquiv.dist_eq y p).trans_lt hy)
  · intro hx
    refine ⟨S.diffeo.symm x, ?_, S.diffeo.apply_symm_apply x⟩
    have hdist := S.isometryEquiv.symm.dist_eq x (S.diffeo p)
    change dist (S.diffeo.symm x) (S.diffeo.symm (S.diffeo p)) =
      dist x (S.diffeo p) at hdist
    rw [S.diffeo.symm_apply_apply] at hdist
    rwa [hdist]

omit [IsManifold I3 ∞ M] [TopologicalSpace N] [ChartedSpace E3 N] in
def smallModel_sublevel_homeomorph (f : S.Carrier → ℝ) (t : ℝ) :
    {x : S.Carrier // f x ≤ t} ≃ₜ {x : M // smallModel_backFunction S f x ≤ t} := by
  apply (S.diffeo.toHomeomorph.image {x : S.Carrier | f x ≤ t}).trans
  apply Homeomorph.setCongr
  ext x
  simp only [mem_image, mem_ofPred_eq]
  constructor
  · rintro ⟨y, hy, rfl⟩
    change smallModel_backFunction S f (S.diffeo y) ≤ t
    rw [smallModel_backFunction_square]
    exact hy
  · intro hx
    exact ⟨S.diffeo.symm x, hx, S.diffeo.apply_symm_apply x⟩

section MetricFields

variable [mN : MetricSpace N]

variable (p : S.Carrier) (c : ℝ) (hc : 0 < c)

@[instance_reducible] def smallModel_rescaledIsometry :
    letI smallMetric := S.metricSpace
    letI _smallRescaled := smallMetric.rescale c hc
    letI _sourceRescaled := mM.rescale c hc
    S.Carrier ≃ᵢ M := by
  letI smallMetric := S.metricSpace
  exact S.isometryEquiv.rescale c hc

def smallModel_backCone {q : N} {δ : ℝ}
    (P : letI _smallRescaled := S.metricSpace.rescale c hc
      GC.MetricGeometry.KleinerLottApprox p q δ) :
    letI _sourceRescaled := mM.rescale c hc
    GC.MetricGeometry.KleinerLottApprox (S.diffeo p) q δ := by
  exact @GC.MetricGeometry.KleinerLottApprox.comapSourceIsometryAt
    S.Carrier N M (S.metricSpace.rescale c hc) mN (mM.rescale c hc) p q δ P
    (@IsometryEquiv.symm S.Carrier M
      (S.metricSpace.rescale c hc).toPseudoEMetricSpace (mM.rescale c hc).toPseudoEMetricSpace
      (smallModel_rescaledIsometry (mM := mM) S c hc))
    (S.diffeo p) (S.diffeo.symm_apply_apply p)

omit [IsManifold I3 ∞ M] [TopologicalSpace N] [ChartedSpace E3 N] in
theorem smallModel_backCone_apply {q : N} {δ : ℝ}
    (P : letI _smallRescaled := S.metricSpace.rescale c hc
      GC.MetricGeometry.KleinerLottApprox p q δ) (x : M) :
    letI _smallRescaled := S.metricSpace.rescale c hc
    letI _sourceRescaled := mM.rescale c hc
    (smallModel_backCone (mM := mM) S p c hc P).toFun x = P.toFun (S.diffeo.symm x) := rfl

end MetricFields

end DifferentialGeometry.Geometry.Collapse
