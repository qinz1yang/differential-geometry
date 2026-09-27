import DifferentialGeometry.Geometry.Neck.NormalizedDatum
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCross

set_option autoImplicit false
noncomputable section
open Set Function Manifold DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.Geometry.Neck.normalizedDatum
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Fact (Module.finrank ℝ E = 3)]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [Fact (Module.finrank ℝ F = 3)]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}

omit [Fact (Module.finrank ℝ E = 3)] [Fact (Module.finrank ℝ F = 3)] in
private theorem transported_scalar (D : M ≃ₘ⟮I, J⟯ N) (x : M) :
    metricScalarAt (Diffeomorph.pullbackMetricCross g D.symm) (D x) = metricScalarAt g x := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : CompleteSpace F := FiniteDimensional.complete ℝ F
  rw [metricScalar_cross, D.symm_apply_apply]

omit [Fact (Module.finrank ℝ F = 3)] [J.Boundaryless] in
private theorem transported_tensor (d : normalizedDatum g x₀ δ k)
    (D : M ≃ₘ⟮I, J⟯ N) (q : bufferedCylinder δ) (v w : TangentSpace IC q) :
    (Diffeomorph.pullbackMetricCross g D.symm).inner ((D ∘ d.map) q)
      (mfderiv IC J (D ∘ d.map) q v) (mfderiv IC J (D ∘ d.map) q w) =
      g.inner (d.map q) (mfderiv IC I d.map q v) (mfderiv IC I d.map q w) := by
  have hcomp : (D.symm ∘ (D ∘ d.map) : bufferedCylinder δ → M) = d.map := by
    funext p; exact D.symm_apply_apply (d.map p)
  have hd := mfderiv_comp q
    (D.symm.contMDiff.mdifferentiable (by decide : (∞ : WithTop ℕ∞) ≠ 0) ((D ∘ d.map) q))
    ((D.contMDiff.comp d.smooth).mdifferentiable (by decide : (∞ : WithTop ℕ∞) ≠ 0) q)
  rw [hcomp] at hd
  rw [Diffeomorph.pullbackMetricCross_inner]
  have hv := congrArg (fun A => A v) hd
  have hw := congrArg (fun A => A w) hd
  exact (congrArg₂ (fun a b => g.inner (D.symm (D (d.map q))) a b) hv.symm hw.symm).trans
    (by rw [D.symm_apply_apply])

def transported (d : normalizedDatum g x₀ δ k) (D : M ≃ₘ⟮I, J⟯ N) :
    normalizedDatum (Diffeomorph.pullbackMetricCross g D.symm) (D x₀) δ k := by
  let φ : bufferedCylinder δ → N := D ∘ d.map
  have hs : ContMDiff IC J ∞ φ := D.contMDiff.comp d.smooth
  have hi : Injective φ := D.injective.comp d.injective
  have hm : ∀ q, Injective (mfderiv IC J φ q) := by
    intro q
    rw [show φ = D ∘ d.map from rfl,
      mfderiv_comp q (D.contMDiff.mdifferentiable (by decide : (∞ : WithTop ℕ∞) ≠ 0) (d.map q))
        (d.smooth.mdifferentiable (by decide : (∞ : WithTop ℕ∞) ≠ 0) q)]
    exact (D.mfderivToContinuousLinearEquiv (by simp) (d.map q)).injective.comp (d.immersion q)
  have hp : 0 < metricScalarAt (Diffeomorph.pullbackMetricCross g D.symm) (D x₀) := by
    rw [transported_scalar]; exact d.scalar_pos
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = Module.finrank ℝ F := by
    rw [show Module.finrank ℝ F = 3 from Fact.out]; simp
  let hloc := isLocalDiffeomorph_of_injective_mfderiv φ hs hm hdim
  have he : pullbackMetricOfInjectiveLocalDiffeomorph
      (scaleMetric _ hp (Diffeomorph.pullbackMetricCross g D.symm)) φ hloc hi = d.normalizedMetric := by
    apply SmoothRiemannianMetric.ext_inner
    intro q v w
    rw [pullbackMetricOfInjectiveLocalDiffeomorph_inner, scaleMetric_inner,
      normalizedMetric_inner, transported_scalar]
    exact congrArg (fun t => metricScalarAt g x₀ * t) (transported_tensor d D q v w)
  refine
    { precision_pos := d.precision_pos
      precision_lt_one := d.precision_lt_one
      map := φ
      smooth := hs
      injective := hi
      immersion := hm
      center_eq := congrArg D d.center_eq
      scalar_pos := hp
      retainedSide := d.retainedSide
      error_lt := ?_ }
  change metricDerivENormSupOn (controlledCylinder δ) k
    (pullbackMetricOfInjectiveLocalDiffeomorph
      (scaleMetric _ hp (Diffeomorph.pullbackMetricCross g D.symm)) φ hloc hi)
      (referenceMetric δ) (referenceMetric δ) < _
  rw [he]
  exact d.error_lt

theorem transported_map (d : normalizedDatum g x₀ δ k) (D : M ≃ₘ⟮I, J⟯ N) :
    (d.transported D).map = D ∘ d.map := rfl

theorem transported_retainedSide (d : normalizedDatum g x₀ δ k) (D : M ≃ₘ⟮I, J⟯ N) :
    (d.transported D).retainedSide = d.retainedSide := rfl

theorem transported_normalizedMetric (d : normalizedDatum g x₀ δ k) (D : M ≃ₘ⟮I, J⟯ N) :
    (d.transported D).normalizedMetric = d.normalizedMetric := by
  apply SmoothRiemannianMetric.ext_inner
  intro q v w
  rw [normalizedMetric_inner, normalizedMetric_inner, transported_map, transported_scalar]
  exact congrArg (fun t => metricScalarAt g x₀ * t) (transported_tensor d D q v w)
end DifferentialGeometry.Geometry.Neck.normalizedDatum
