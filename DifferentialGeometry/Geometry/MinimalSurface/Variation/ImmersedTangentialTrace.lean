import DifferentialGeometry.Geometry.Connection.SourceSectionPairing
import DifferentialGeometry.Geometry.Metric.SourceTangent
import DifferentialGeometry.Geometry.Submanifold.SecondFundamentalForm.Pointwise
import DifferentialGeometry.Geometry.Metric.Pullback.Immersion
import DifferentialGeometry.Geometry.Operator.Gradient.MetricSharpSmoothness
import DifferentialGeometry.Geometry.Connection.DivergenceCovariantTrace
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.Expansion
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Global.IntegrationByParts
import DifferentialGeometry.Geometry.Comparison.Variation.Covariant.ChainRule
import DifferentialGeometry.Topology.Manifold.CurveExtension
import DifferentialGeometry.Topology.Manifold.OpenSubtype

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff _root_.Topology BigOperators

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

private local instance (N : TopologicalSpace.Opens ℂ) : MeasurableSpace N := borel N
private local instance (N : TopologicalSpace.Opens ℂ) : BorelSpace N := ⟨rfl⟩
private local instance (N : TopologicalSpace.Opens ℂ) : LocallyCompactSpace N :=
  N.isOpen.locallyCompactSpace
private local instance (N : TopologicalSpace.Opens ℂ) : SigmaCompactSpace N := by infer_instance

private def tangentialProjection
    (N : TopologicalSpace.Opens ℂ) (gN : SmoothRiemannianMetric 𝓘(ℝ, ℂ) N)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (f : N → M)
    (Y : ∀ x : M, TangentSpace 𝓘(ℝ, E) x) (q : N) :
    TangentSpace 𝓘(ℝ, ℂ) q :=
  metricSharp gN q
    (((g.inner (f q) (Y (f q))).comp (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) f q)).toLinearMap)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [T2Space M] in
private theorem tangentialProjection_inner
    (N : TopologicalSpace.Opens ℂ) (gN : SmoothRiemannianMetric 𝓘(ℝ, ℂ) N)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (f : N → M)
    (Y : ∀ x : M, TangentSpace 𝓘(ℝ, E) x) (q : N) (v : ℂ) :
    gN.inner q (tangentialProjection N gN g f Y q) v =
      g.inner (f q) (Y (f q)) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) f q v) :=
  inner_metricSharp gN q _ v

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [T2Space M] in
private theorem tangentialProjection_contMDiff
    (N : TopologicalSpace.Opens ℂ) (gN : SmoothRiemannianMetric 𝓘(ℝ, ℂ) N)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (f : N → M)
    (hf : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ f)
    (Y : ∀ x : M, TangentSpace 𝓘(ℝ, E) x)
    (hY : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun x => (⟨x, Y x⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ∞
      (fun q => (⟨q, tangentialProjection N gN g f Y q⟩ :
        TangentBundle 𝓘(ℝ, ℂ) N)) := by
  apply metricSharp_contMDiff_total
  intro α j
  have hB := DifferentialGeometry.Tensor.Coordinates.chartBasisVec_contMDiffOn
    (I := 𝓘(ℝ, ℂ)) α j
  rw [trivializationAt_baseSet_eq_chartAt_source] at hB
  have hdf : ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q : N => (⟨f q, mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) f q
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber
          (I := 𝓘(ℝ, ℂ)) α j q)⟩ : TangentBundle 𝓘(ℝ, E) M))
      (chartAt ℂ α).source :=
    (hf.contMDiff_tangentMap le_rfl).comp_contMDiffOn hB
  have hpair := ContMDiffOn.clm_bundle_apply₂
    (E₁ := fun x : M => TangentSpace 𝓘(ℝ, E) x)
    (E₂ := fun x : M => TangentSpace 𝓘(ℝ, E) x)
    (E₃ := fun _ : M => ℝ)
    (b := f) (ψ := fun q => g.inner (f q))
    (v := fun q => Y (f q))
    (w := fun q => mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) f q
      (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber
        (I := 𝓘(ℝ, ℂ)) α j q))
    (g.contMDiff.comp hf).contMDiffOn (hY.comp hf).contMDiffOn hdf
  intro q hq
  exact (contMDiffWithinAt_totalSpace.mp (hpair q hq)).2

omit [NeZero (Module.finrank ℝ E)] in
/-- Differentiating the defining pairing of the projection along a curve gives
exactly the Gauss defect, with the ambient-minus-source convention for II. -/
private theorem projection_covariant_pairing
    (N : TopologicalSpace.Opens ℂ) (gN : SmoothRiemannianMetric 𝓘(ℝ, ℂ) N)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (f : N → M)
    (hf : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ f)
    (Y : ∀ x : M, TangentSpace 𝓘(ℝ, E) x)
    (hY : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun x => (⟨x, Y x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (Z : ∀ q : N, TangentSpace 𝓘(ℝ, ℂ) q)
    (hZ : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ∞
      (fun q => (⟨q, Z q⟩ : TangentBundle 𝓘(ℝ, ℂ) N)))
    (hpair : ∀ (q : N) (v : ℂ), gN.inner q (Z q) v =
      g.inner (f q) (Y (f q)) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) f q v))
    (q : N) (v : ℂ) :
    gN.inner q ((LeviCivita gN).toFun Z q v) v =
      g.inner (f q)
        ((LeviCivita g).toFun Y (f q) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) f q v))
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) f q v) +
      g.inner (f q) (Y (f q)) (secondFundamentalFormAmbientAt gN g f q v v) := by
  obtain ⟨γ, hγ, _, hvelocity⟩ := exists_contMDiff_curve_with_velocity_range_subset
    (I := 𝓘(ℝ, ℂ)) BoundarylessManifold.isInteriorPoint v
    (Filter.univ_mem : Set.univ ∈ 𝓝 q)
  have hγ0 : γ 0 = q := congrArg (fun p : TangentBundle 𝓘(ℝ, ℂ) N => p.1) hvelocity
  have hv : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ 0 (1 : ℝ) : ℂ) = v :=
    congrArg (fun p : TangentBundle 𝓘(ℝ, ℂ) N => (p.2 : ℂ)) hvelocity
  let η : ℝ → M := fun t => f (γ t)
  have hη : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ η := hf.comp hγ
  have hdη (t : ℝ) :
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) η t (1 : ℝ) : E) =
        mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) f (γ t)
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ t (1 : ℝ)) := by
    exact mfderiv_comp_apply t (hf.mdifferentiableAt (by simp))
      (hγ.mdifferentiableAt (by simp)) (1 : ℝ)
  have hZrep : DifferentiableAt ℝ
      (chartRepAt γ (fun t => Z (γ t)) 0) 0 :=
    (contDiffAt_chartRepAt_of_section (hZ.comp hγ).contMDiffAt).differentiableAt (by simp)
  have hYrep : DifferentiableAt ℝ
      (chartRepAt η (fun t => Y (η t)) 0) 0 :=
    (contDiffAt_chartRepAt_of_section (hY.comp hη).contMDiffAt).differentiableAt (by simp)
  have hγrep : DifferentiableAt ℝ
      (chartRepAt γ (fun t => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ t (1 : ℝ)) 0) 0 :=
    MFDerivAlongCurve.velocity_coord_diff γ 0 (hγ.contMDiffAt.of_le (by simp))
  have hηrep : DifferentiableAt ℝ
      (chartRepAt η (fun t => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) η t (1 : ℝ)) 0) 0 :=
    MFDerivAlongCurve.velocity_coord_diff η 0 (hη.contMDiffAt.of_le (by simp))
  have hS := inner_deriv_at (by simp : (1 : WithTop ℕ∞) ≤ ∞) gN γ
    (fun t => Z (γ t)) (fun t => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ t (1 : ℝ)) 0
    hγ.contMDiffAt hZrep hγrep
  have hT := inner_deriv_at (by simp : (1 : WithTop ℕ∞) ≤ ∞) g η
    (fun t => Y (η t)) (fun t => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) η t (1 : ℝ)) 0
    hη.contMDiffAt hYrep hηrep
  have hZcov := covDerivAlong_eq_leviCivita_of_eventuallyEq gN γ 0
    (hγ.contMDiffAt.of_le (by simp)) (hZ.mdifferentiableAt (by simp))
    (Filter.EventuallyEq.rfl : (fun t => Z (γ t)) =ᶠ[𝓝 (0 : ℝ)] (fun t => Z (γ t)))
  have hYcov := covDerivAlong_eq_leviCivita_of_eventuallyEq g η 0
    (hη.contMDiffAt.of_le (by simp)) (hY.mdifferentiableAt (by simp))
    (Filter.EventuallyEq.rfl : (fun t => Y (η t)) =ᶠ[𝓝 (0 : ℝ)] (fun t => Y (η t)))
  have hscalar :
      (fun t => gN.inner (γ t) (Z (γ t)) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ t (1 : ℝ))) =
      (fun t => g.inner (η t) (Y (η t)) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) η t (1 : ℝ))) := by
    funext t
    rw [hdη t]
    exact hpair (γ t) _
  rw [hscalar] at hS
  have hder := hS.unique hT
  rw [hZcov, hYcov, hdη 0] at hder
  have hII := secondFundamentalFormAmbientAt_diagonal_along_curve gN g hf γ hγ 0
  change secondFundamentalFormAmbientAt gN g f (γ 0)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ 0 (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ 0 (1 : ℝ)) =
    covariantAcceleration g η 0 -
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) f (γ 0) (covariantAcceleration gN γ 0) at hII
  have hcurved :
      gN.inner (γ 0)
          ((LeviCivita gN).toFun Z (γ 0)
            (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ 0 (1 : ℝ)))
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ 0 (1 : ℝ)) =
        g.inner (f (γ 0))
          ((LeviCivita g).toFun Y (f (γ 0))
            (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) f (γ 0)
              (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ 0 (1 : ℝ))))
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) f (γ 0)
            (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ 0 (1 : ℝ))) +
        g.inner (f (γ 0)) (Y (f (γ 0)))
          (secondFundamentalFormAmbientAt gN g f (γ 0)
            (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ 0 (1 : ℝ))
            (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ 0 (1 : ℝ))) := by
    rw [hII, map_sub]
    have hsource := hpair (γ 0) (covariantAcceleration gN γ 0)
    change gN.inner (γ 0)
        ((LeviCivita gN).toFun Z (γ 0)
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ 0 (1 : ℝ)))
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ 0 (1 : ℝ)) +
      gN.inner (γ 0) (Z (γ 0)) (covariantAcceleration gN γ 0) =
      g.inner (f (γ 0))
        ((LeviCivita g).toFun Y (f (γ 0))
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) f (γ 0)
            (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ 0 (1 : ℝ))))
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) f (γ 0)
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ 0 (1 : ℝ))) +
      g.inner (f (γ 0)) (Y (f (γ 0))) (covariantAcceleration g η 0) at hder
    rw [hsource] at hder
    linarith
  rw [hv, hγ0] at hcurved
  exact hcurved

omit [NeZero (Module.finrank ℝ E)] in
private theorem sourceDerivative_restrict_ambient_field
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M)
    (Y : ∀ x : M, TangentSpace 𝓘(ℝ, E) x)
    (hY : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun x => (⟨x, Y x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (z v : ℂ) (hU : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U z) :
    sourceSectionCovariantDerivative g U (fun p => Y (U p)) z v =
      (LeviCivita g).toFun Y (U z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z v) := by
  let γ : ℝ → M := fun t => U (z + t • v)
  have hline : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ (fun t : ℝ => z + t • v) :=
    (contDiff_const.add (contDiff_id.smul contDiff_const)).contMDiff
  have hγ : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ 0 := by
    apply ContMDiffAt.comp 0 _ hline.contMDiffAt
    simpa only [zero_smul, add_zero] using hU
  have hγ0 : γ 0 = U z := by simp only [γ, zero_smul, add_zero]
  have hvel : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ 0 (1 : ℝ) : E) =
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z v :=
    source_mfderiv_line (r := U) (z := z) (hU.mdifferentiableAt (by simp)) v
  let L : M → E →L[ℝ] E := fun x => (LeviCivita g).toFun Y x
  have hcov : (covDerivAlong g γ (fun t => Y (γ t)) 0 : E) =
      L (γ 0) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ 0 (1 : ℝ)) :=
    covDerivAlong_eq_leviCivita_of_eventuallyEq (I := 𝓘(ℝ, E)) g γ 0
      (hγ.of_le (by simp)) (X := Y) (hY.mdifferentiableAt (by simp))
      (Filter.EventuallyEq.rfl :
        (fun t => Y (γ t)) =ᶠ[𝓝 (0 : ℝ)] (fun t => Y (γ t)))
  have hvector : L (γ 0) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ 0 (1 : ℝ)) =
      L (γ 0) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z v) :=
    congrArg (fun w : E => L (γ 0) w) hvel
  have hbase : L (γ 0) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z v) =
      L (U z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z v) :=
    congrArg (fun x : M => L x (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z v : E)) hγ0
  exact hcov.trans (hvector.trans hbase)

omit [NeZero (Module.finrank ℝ E)] in
/-- For the actual induced metric, zero vector mean curvature and compact
source support cancel the integrated tangential derivative of the ambient field.
The orthonormal basis may vary arbitrarily: the integrand equals smooth divergence. -/
theorem integral_tangential_trace_eq_zero_of_zero_mean_curvature
    (N : TopologicalSpace.Opens ℂ) (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M)
    (hU : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (hi : ∀ q : N, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q))
    (hmean :
      let gN := g.pullback (fun q : N => U q) hU hi
      ∀ (q : N) (b : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) q)),
        (∀ i j, gN.inner q (b i) (b j) = if i = j then 1 else 0) →
        (∑ i : Fin 2, secondFundamentalFormAmbientAt gN g
          (fun p : N => U p) q (b i) (b i)) = 0)
    (Y : ∀ x : M, TangentSpace 𝓘(ℝ, E) x)
    (hY : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun x => (⟨x, Y x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hYsource : HasCompactSupport (fun q : N => (Y (U q) : E)))
    (b : ∀ q : N, Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) q))
    (hb : ∀ (q : N) (i j : Fin 2),
      (g.pullback (fun p : N => U p) hU hi).inner q (b q i) (b q j) =
        if i = j then 1 else 0) :
    let gN := g.pullback (fun q : N => U q) hU hi
    let μ := riemannianVolumeMeasure (I := 𝓘(ℝ, ℂ)) (M := N) gN
    let T : N → ℝ := fun q => ∑ i : Fin 2,
      g.inner (U q)
        (sourceSectionCovariantDerivative g U (fun p => Y (U p)) q (b q i))
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U q (b q i))
    Integrable T μ ∧ (∫ q, T q ∂μ) = 0 := by
  classical
  let f : N → M := fun q => U q
  let gN := g.pullback f hU hi
  let μ := riemannianVolumeMeasure (I := 𝓘(ℝ, ℂ)) (M := N) gN
  let T : N → ℝ := fun q => ∑ i : Fin 2,
    g.inner (U q)
      (sourceSectionCovariantDerivative g U (fun p => Y (U p)) q (b q i))
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U q (b q i))
  let Z : Cₛ^∞⟮𝓘(ℝ, ℂ); ℂ, (TangentSpace 𝓘(ℝ, ℂ) : N → Type _)⟯ :=
    ⟨tangentialProjection N gN g f Y,
      tangentialProjection_contMDiff N gN g f hU Y hY⟩
  change Integrable T μ ∧ (∫ q, T q ∂μ) = 0
  have hZc : HasCompactSupport Z := by
    apply hYsource.of_isClosed_subset (isClosed_tsupport _)
    apply closure_mono
    intro q hq hYq
    change Y (U q) = 0 at hYq
    apply hq
    have hα : ((g.inner (f q) (Y (f q))).comp
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) f q)).toLinearMap = 0 := by
      ext v
      change g.inner (U q) (Y (U q)) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) f q v) = 0
      rw [hYq, map_zero, zero_apply]
    change metricSharp gN q _ = 0
    rw [hα, metricSharp_def, map_zero]
  have hdiv (q : N) : divergenceG gN Z q = T q := by
    have hinv : MetricInverseInBasis gN q (b q)
        (fun i j => if i = j then (1 : ℝ) else 0) := by
      intro i j
      constructor
      · rw [Finset.sum_eq_single i]
        · simpa only [ite_true, one_mul] using hb q i j
        · intro k _ hk
          simp only [ite_eq_right (Ne.symm hk), zero_mul]
        · intro h
          exact (h (Finset.mem_univ i)).elim
      · rw [Finset.sum_eq_single j]
        · simpa only [ite_true, mul_one] using hb q i j
        · intro k _ hk
          simp only [ite_eq_right hk, mul_zero]
        · intro h
          exact (h (Finset.mem_univ j)).elim
    have htrace : divergenceG gN Z q =
        ∑ i : Fin 2, gN.inner q ((LeviCivita gN).toFun Z.toFun q (b q i)) (b q i) := by
      rw [divergence_g_eq_leviCivita_divergence_of_isInteriorPoint gN Z
        (BoundarylessManifold.isInteriorPoint : q ∈ (𝓘(ℝ, ℂ)).interior N),
        ← LeviCivita_eq_leviCivitaConnectionOfMetric, divergence_eq]
      have ht := linearMap_trace_eq_sum_inv_inner_apply gN q (b q)
        (fun i j => if i = j then (1 : ℝ) else 0) hinv
        ((LeviCivita gN).toFun Z.toFun q).toLinearMap
      refine ht.trans ?_
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · simpa only [ite_true, one_mul] using
          (show gN.inner q
              (((LeviCivita gN).toFun Z.toFun q).toLinearMap (b q i)) (b q i) =
            gN.inner q ((LeviCivita gN).toFun Z.toFun q (b q i)) (b q i) from rfl)
      · intro j _ hji
        simp only [ite_eq_right (Ne.symm hji), zero_mul]
      · intro h
        exact (h (Finset.mem_univ i)).elim
    rw [htrace]
    have hUq : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U (q : ℂ) :=
      contMDiffAt_subtype_iff.mp (hU.contMDiffAt (x := q))
    have hdf : (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) f q : ℂ →L[ℝ] E) =
        mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U q :=
      DifferentialGeometry.mfderiv_restrict_open U N q
    have hpoint (v : TangentSpace 𝓘(ℝ, ℂ) q) :
        gN.inner q ((LeviCivita gN).toFun Z.toFun q v) v =
          g.inner (U q) (sourceSectionCovariantDerivative g U (fun p => Y (U p)) q v)
            (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U q v) +
          g.inner (U q) (Y (U q)) (secondFundamentalFormAmbientAt gN g f q v v) := by
      have hp := projection_covariant_pairing N gN g f hU Y hY Z.toFun Z.contMDiff
        (tangentialProjection_inner N gN g f Y) q v
      let df : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) f q
      let dU : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (q : ℂ)
      let B : E →L[ℝ] E →L[ℝ] ℝ := g.inner (U q)
      let L : E →L[ℝ] E := (LeviCivita g).toFun Y (U q)
      let a : E := sourceSectionCovariantDerivative g U (fun p => Y (U p)) q v
      let remainder : ℝ :=
        g.inner (U q) (Y (U q)) (secondFundamentalFormAmbientAt gN g f q v v)
      have hpModel : gN.inner q ((LeviCivita gN).toFun Z.toFun q v) v =
          B (L (df (v : ℂ))) (df (v : ℂ)) + remainder := hp
      have hdfModel : df = dU := hdf
      have hpairModel : B (L (df (v : ℂ))) (df (v : ℂ)) + remainder =
          B (L (dU (v : ℂ))) (dU (v : ℂ)) + remainder :=
        congrArg (fun D : ℂ →L[ℝ] E => B (L (D (v : ℂ))) (D (v : ℂ)) + remainder)
          hdfModel
      have hder : a = L (dU (v : ℂ)) :=
        sourceDerivative_restrict_ambient_field g U Y hY q v hUq
      have hambient : B (L (dU (v : ℂ))) (dU (v : ℂ)) + remainder =
          B a (dU (v : ℂ)) + remainder :=
        congrArg (fun w : E => B w (dU (v : ℂ)) + remainder) hder.symm
      exact hpModel.trans (hpairModel.trans hambient)
    calc
      (∑ i : Fin 2, gN.inner q ((LeviCivita gN).toFun Z.toFun q (b q i)) (b q i)) =
          ∑ i : Fin 2,
            (g.inner (U q)
                (sourceSectionCovariantDerivative g U (fun p => Y (U p)) q (b q i))
                (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U q (b q i)) +
              g.inner (U q) (Y (U q))
                (secondFundamentalFormAmbientAt gN g f q (b q i) (b q i))) :=
        Finset.sum_congr rfl (fun i _ => hpoint (b q i))
      _ = T q + g.inner (U q) (Y (U q))
          (∑ i : Fin 2, secondFundamentalFormAmbientAt gN g f q (b q i) (b q i)) := by
        rw [Finset.sum_add_distrib, map_sum]
      _ = T q := by rw [hmean q (b q) (hb q), map_zero, add_zero]
  have hfun : divergenceG gN Z = T := funext hdiv
  constructor
  · rw [← hfun]
    exact Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure gN
      (divergence_g_contMDiff gN Z).continuous (hasCompactSupport_divergence_g gN hZc)
  · rw [← hfun]
    exact integral_divergence_eq_zero_of_hasCompactSupport gN Z hZc

end DifferentialGeometry.Geometry
