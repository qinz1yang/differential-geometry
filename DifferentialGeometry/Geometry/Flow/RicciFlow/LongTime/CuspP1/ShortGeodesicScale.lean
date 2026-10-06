import DifferentialGeometry.Geometry.Hyperbolic.Truncation
import DifferentialGeometry.Geometry.Geodesic.Equation.Basic
import DifferentialGeometry.Topology.LoopSpace.CircleDegree
import DifferentialGeometry.Geometry.Metric.Scaling
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import DifferentialGeometry.Geometry.Collapse.SublevelCore.ScaledMinimizingDirections

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry.Hyperbolic
open GC.Endpoint Bundle Set
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

section Speed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Speed-squared of a curve is continuous when the velocity is continuous in the tangent bundle. -/
theorem continuous_speed_CPA (g : SmoothRiemannianMetric I M) (c : ℝ → M)
    (v : ∀ s, TangentSpace I (c s))
    (hv : Continuous fun s => (⟨c s, v s⟩ : TangentBundle I M)) :
    Continuous fun s => g.inner (c s) (v s) (v s) := by
  let _ : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have _ : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  exact Continuous.inner_bundle hv hv

/-- Velocity of a smooth curve `ℝ → M` is continuous in the tangent bundle. -/
theorem continuous_velocity_CPA (f : ℝ → M) (hf : ContMDiff 𝓘(ℝ, ℝ) I ∞ f) :
    Continuous fun s : ℝ => (⟨f s, mfderiv 𝓘(ℝ, ℝ) I f s 1⟩ : TangentBundle I M) := by
  have h1 : Continuous (tangentMap 𝓘(ℝ, ℝ) I f) := hf.continuous_tangentMap (by simp)
  have h2 : Continuous fun s : ℝ => (⟨s, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ) :=
    (tangentBundleModelSpaceHomeomorph (𝓘(ℝ, ℝ))).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  exact h1.comp h2

/-- A smooth `1`-periodic curve has a bounded speed. -/
theorem exists_speed_bound_CPA (g : SmoothRiemannianMetric I M) (f : ℝ → M)
    (hf : ContMDiff 𝓘(ℝ, ℝ) I ∞ f) (hper : ∀ s, f (s + 1) = f s) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℝ,
      g.inner (f s) (mfderiv 𝓘(ℝ, ℝ) I f s 1) (mfderiv 𝓘(ℝ, ℝ) I f s 1) ≤ B := by
  let sp : ℝ → ℝ := fun s =>
    g.inner (f s) (mfderiv 𝓘(ℝ, ℝ) I f s 1) (mfderiv 𝓘(ℝ, ℝ) I f s 1)
  have hcont : Continuous sp :=
    continuous_speed_CPA g f (fun s => mfderiv 𝓘(ℝ, ℝ) I f s 1) (continuous_velocity_CPA f hf)
  have hd : ∀ y : ℝ, mfderiv 𝓘(ℝ, ℝ) I f (y + 1) = mfderiv 𝓘(ℝ, ℝ) I f y := by
    intro y
    have htr : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun z : ℝ => z + 1) y = ContinuousLinearMap.id ℝ ℝ := by
      rw [mfderiv_eq_fderiv]
      exact ((hasFDerivAt_id y).add_const 1).fderiv
    have hcomp := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) (I'' := I)
      (f := fun z : ℝ => z + 1) (g := f) y
      (hf.mdifferentiable (by simp) (y + 1))
      ((contDiff_id.add contDiff_const : ContDiff ℝ 1 (fun z : ℝ => z + 1)).contMDiff.mdifferentiable
        (by simp) y)
    have hfun : (f ∘ fun z : ℝ => z + 1) = f := funext hper
    rw [hfun, htr] at hcomp
    exact hcomp.symm
  have hsub : ∀ (a b : M), a = b → ∀ u : E, g.inner a u u = g.inner b u u := by
    intro a b hab u; subst hab; rfl
  have hp : Function.Periodic sp 1 := by
    intro s
    have h1 : (mfderiv 𝓘(ℝ, ℝ) I f (s + 1) 1 : E) = (mfderiv 𝓘(ℝ, ℝ) I f s 1 : E) := by
      exact congrArg (fun L => (L 1 : E)) (hd s)
    show g.inner (f (s + 1)) (mfderiv 𝓘(ℝ, ℝ) I f (s + 1) 1) (mfderiv 𝓘(ℝ, ℝ) I f (s + 1) 1) =
      g.inner (f s) (mfderiv 𝓘(ℝ, ℝ) I f s 1) (mfderiv 𝓘(ℝ, ℝ) I f s 1)
    rw [h1]
    exact hsub _ _ (hper s) _
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).bddAbove_image hcont.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun s => ?_⟩
  obtain ⟨t, ht, hst⟩ := hp.exists_mem_Ico₀ one_pos s
  have : sp s ≤ B := by
    rw [hst]; exact hB ⟨t, ⟨ht.1, ht.2.le⟩, rfl⟩
  exact this.trans (le_max_left _ _)

end Speed

section Scaling

/-- Scaling a flat torus metric by a positive constant keeps it flat (`Rm₀₄` scales by `c`). -/
theorem torus_flat_scale_CPA (g : SmoothRiemannianMetric torusModel Torus) {c : ℝ} (hc : 0 < c)
    (hflat : ∀ (p : Torus) (v w : TangentSpace torusModel p),
      DifferentialGeometry.Geometry.Curvature.metricRm04StandardAt g p v w w v = 0) :
    ∀ (p : Torus) (v w : TangentSpace torusModel p),
      DifferentialGeometry.Geometry.Curvature.metricRm04StandardAt
        (scaleMetric c hc g) p v w w v = 0 := by
  intro p v w
  rw [DifferentialGeometry.Geometry.Curvature.metricRmStandard_scale, hflat, mul_zero]

/-- The cusp with cross-section metric `g` (flat) and metric `dz² + e^{-z} g`. -/
def cuspOfFlat_CPA (g : SmoothRiemannianMetric torusModel Torus)
    (hflat : ∀ (p : Torus) (v w : TangentSpace torusModel p),
      DifferentialGeometry.Geometry.Curvature.metricRm04StandardAt g p v w w v = 0) :
    HyperbolicCusp where
  torusMetric := g
  torus_flat := hflat
  metric := g.exponentialWarpedEnd (1 / 2)
  metric_formula p v w := by
    rw [SmoothRiemannianMetric.exponentialWarpedEnd_inner]
    congr 2
    ring_nf

/-- The cusp cross-section at depth `b` of a cusp with flat cross-section `g`: `e^{-b} g`. -/
def deepCusp_CPA (H : HyperbolicCusp) (b : ℝ) : HyperbolicCusp :=
  cuspOfFlat_CPA (scaleMetric (Real.exp (-b)) (Real.exp_pos _) H.torusMetric)
    (torus_flat_scale_CPA H.torusMetric (Real.exp_pos _) H.torus_flat)

theorem deepCusp_torusMetric_inner_CPA (H : HyperbolicCusp) (b : ℝ) (p : Torus)
    (v w : TangentSpace torusModel p) :
    (deepCusp_CPA H b).torusMetric.inner p v w = Real.exp (-b) * H.torusMetric.inner p v w :=
  scaleMetric_inner (Real.exp (-b)) (Real.exp_pos _) H.torusMetric p v w

/-- A smooth periodic curve that is a geodesic of `g` is a geodesic of every positive multiple,
and its speed in `c • g` is `< 1/4` once `c` is small: the **short** field after rescaling. -/
theorem exists_scale_short_geodesic_CPA (g : SmoothRiemannianMetric torusModel Torus)
    (γ : freeLoop Torus) (hsm : ContMDiff 𝓘(ℝ, ℝ) torusModel ∞ (loopLift γ))
    (hgeo : DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesic g (loopLift γ)) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (c : ℝ) (hc : 0 < c), c ≤ c₀ →
      DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesic
        (scaleMetric c hc g) (loopLift γ) ∧
      ∃ L : ℝ, 0 < L ∧ L < 1 ∧ ∀ s : ℝ,
        let v := mfderiv 𝓘(ℝ, ℝ) torusModel (loopLift γ) s 1;
        (scaleMetric c hc g).inner (loopLift γ s) v v ≤ L ^ 2 := by
  obtain ⟨B, hB0, hB⟩ := exists_speed_bound_CPA g (loopLift γ) hsm
    (fun s => by simpa using loopLift_add_intCast γ s 1)
  refine ⟨1 / (4 * (B + 1)), by positivity, fun c hc hcle => ⟨?_, 1 / 2, by norm_num, by norm_num, ?_⟩⟩
  · exact (DifferentialGeometry.Geometry.Collapse.isGeodesic_scaleMetric_iff c hc).mpr hgeo
  · intro s
    show (scaleMetric c hc g).inner (loopLift γ s) _ _ ≤ _
    rw [scaleMetric_inner]
    have h1 := hB s
    have h2 : c * (B + 1) ≤ 1 / 4 := by
      calc c * (B + 1) ≤ 1 / (4 * (B + 1)) * (B + 1) :=
            mul_le_mul_of_nonneg_right hcle (by positivity)
        _ = 1 / 4 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left h1 hc.le]

end Scaling

end GC.LongTime.CuspP1
