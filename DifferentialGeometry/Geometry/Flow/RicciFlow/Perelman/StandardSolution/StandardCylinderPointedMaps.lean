import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CylinderReferenceInitialCharts
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardInitialCylinderCharts
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardClosedReferenceBounds
import DifferentialGeometry.Topology.Exhaustion

set_option autoImplicit false
noncomputable section
open Set Filter Function Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.PDE.RicciFlow.StandardCap
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev Q := cylinderReferenceCopy.Q
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private theorem copied_chart_subtype_deriv
    (Ψ : PartialDiffeomorph (𝓡 3) (𝓡 3) Q E3 ∞)
    (U : TopologicalSpace.Opens Q) (q : U) (hq : q.val ∈ Ψ.source) (u : E3) :
    mfderiv (𝓡 3) (𝓡 3) (fun y : U => Ψ y.val) q u =
      mfderiv (𝓡 3) (𝓡 3) Ψ q.val u := by
  have hh := mfderiv_comp_apply (I := 𝓡 3) (I' := 𝓡 3) (I'' := 𝓡 3)
    (f := (Subtype.val : U → Q)) (g := Ψ) q
    (Ψ.mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0) hq)
    ((hasMFDerivAt_subtype_val (I := 𝓡 3) U q).mdifferentiableAt) u
  exact hh.trans (congrArg (mfderiv (𝓡 3) (𝓡 3) Ψ q.val)
    (mfderiv_subtype_val_apply (I := 𝓡 3) U q u))

private local instance : TopologicalSpace cylinderPointedReference.M := cylinderPointedReference.topology
private local instance : ChartedSpace E3 cylinderPointedReference.M := cylinderPointedReference.charted
private local instance : T2Space cylinderPointedReference.M := cylinderPointedReference.t2
private local instance : IsManifold (𝓡 3) ∞ cylinderPointedReference.M := cylinderPointedReference.smooth
private local instance : SigmaCompactSpace cylinderPointedReference.M := cylinderPointedReference.sigmaCompact

def standardCylinderPointedMaps (τ : ℝ) (hτ : 0 < τ)
    (hlt : ENNReal.ofReal τ < uniformStandardLifetime)
    (S : ℕ → StandardSolution) (x : ℕ → E3) (φ : ℕ → ℕ)
    (hfit : ∀ k : ℕ, transitionEnd + ((k : ℝ) + 1) ≤ ‖x (φ k)‖) :
    PointedCGHMaps (standardClosedPointedFlowSequence τ hτ hlt S x)
      cylinderPointedReference φ where
  partialDiffeomorph k := cylinderReferenceInitialMap
    (pointedInitialRotation (x (φ k))) ‖x (φ k)‖ ((k : ℝ) + 1) (hfit k)
  source_exhausts := by
    change @ExhaustsByOpen Q cylinderReferenceCopy.topos
      (fun k : ℕ => (cylinderReferenceInitialMap
        (pointedInitialRotation (x (φ k))) ‖x (φ k)‖ ((k : ℝ) + 1) (hfit k)).source)
    simpa only [cylinderReferenceInitialMap_source] using
      cylinderReferenceOpenCylinder_exhausts
  base_mem := by
    intro k
    rw [cylinderReferenceInitialMap_source]
    exact cylinderReferenceOpenCylinder_basepoint_mem (by positivity)
  basepoint_map := by
    intro k
    change cylinderReferenceInitialMap (pointedInitialRotation (x (φ k)))
      ‖x (φ k)‖ ((k : ℝ) + 1) (hfit k) (cylinderReferenceCopy.equiv (spherePoint, 0)) = x (φ k)
    rw [cylinderReferenceInitialMap_apply]
    change initialPolarDiffeomorph (pointedInitialRotation (x (φ k))) ‖x (φ k)‖
      (cylinderReferenceCopy.equiv.symm (cylinderReferenceCopy.equiv (spherePoint, 0))) = x (φ k)
    rw [cylinderReferenceCopy.equiv.symm_apply_apply]
    exact pointedInitialRotation_center (x (φ k))

section Maps

variable (τ : ℝ) (hτ : 0 < τ)
  (hlt : ENNReal.ofReal τ < uniformStandardLifetime)
  (S : ℕ → StandardSolution) (x : ℕ → E3) (φ : ℕ → ℕ)
  (hfit : ∀ k : ℕ, transitionEnd + ((k : ℝ) + 1) ≤ ‖x (φ k)‖)

theorem standardCylinderPointedMaps_source (k : ℕ) :
    (standardCylinderPointedMaps τ hτ hlt S x φ hfit).source k =
      (cylinderReferenceOpenCylinder ((k : ℝ) + 1) : Set Q) :=
  cylinderReferenceInitialMap_source _ _ _ _

theorem standardCylinderPointedMaps_target (k : ℕ) :
    (standardCylinderPointedMaps τ hτ hlt S x φ hfit).target k =
      {y : E3 | ‖x (φ k)‖ - ((k : ℝ) + 1) < ‖y‖ ∧
        ‖y‖ < ‖x (φ k)‖ + ((k : ℝ) + 1)} :=
  cylinderReferenceInitialMap_target_shell _ _ _ _

private local instance (k : ℕ) :
    TopologicalSpace (SourceDomain (standardCylinderPointedMaps τ hτ hlt S x φ hfit) k) :=
  sourceDomTop (standardCylinderPointedMaps τ hτ hlt S x φ hfit) k
private local instance (k : ℕ) :
    ChartedSpace E3 (SourceDomain (standardCylinderPointedMaps τ hτ hlt S x φ hfit) k) :=
  sourceDomCharted (standardCylinderPointedMaps τ hτ hlt S x φ hfit) k
private local instance (k : ℕ) :
    T2Space (SourceDomain (standardCylinderPointedMaps τ hτ hlt S x φ hfit) k) :=
  sourceDomT2 (standardCylinderPointedMaps τ hτ hlt S x φ hfit) k
private local instance (k : ℕ) :
    IsManifold (𝓡 3) ∞ (SourceDomain (standardCylinderPointedMaps τ hτ hlt S x φ hfit) k) :=
  sourceDomSmooth (standardCylinderPointedMaps τ hτ hlt S x φ hfit) k

variable
  (hsrc : SourceIsSigmaCompact (standardCylinderPointedMaps τ hτ hlt S x φ hfit))
  (htgt : TargetIsSigmaCompact (standardCylinderPointedMaps τ hτ hlt S x φ hfit))

private local instance (k : ℕ) :
    SigmaCompactSpace (SourceDomain (standardCylinderPointedMaps τ hτ hlt S x φ hfit) k) :=
  sourceDomSigmaOf (standardCylinderPointedMaps τ hτ hlt S x φ hfit) k
    (standardClosedPointedMaps_sourceSigma
      (standardCylinderPointedMaps τ hτ hlt S x φ hfit) k)

theorem standardCylinderPointedMaps_initial (k : ℕ) :
    sourceMetric (standardCylinderPointedMaps τ hτ hlt S x φ hfit) hsrc htgt k 0 =
      sourceMetricRestriction (standardCylinderPointedMaps τ hτ hlt S x φ hfit) cylinderReferenceMetric k := by
  apply SmoothRiemannianMetric.ext_inner
  intro q v w
  let Φ := standardCylinderPointedMaps τ hτ hlt S x φ hfit
  let Ψ := cylinderReferenceInitialMap (pointedInitialRotation (x (φ k)))
    ‖x (φ k)‖ ((k : ℝ) + 1) (hfit k)
  let data := SourceDomainMetricData.ofRestrictPullback
    (Φ := Φ) (k := k) (hsrc k)
    (fun _ => cylinderReferenceMetric.restrictOpen (sourceOpen Φ k))
    (fun _ => cylinderReferenceMetric)
  let : TopologicalSpace (SourceDomain Φ k) := data.topology
  let : ChartedSpace E3 (SourceDomain Φ k) := data.charted
  let : T2Space (SourceDomain Φ k) := data.t2
  let : IsManifold (𝓡 3) ∞ (SourceDomain Φ k) := data.smooth
  let : SigmaCompactSpace (SourceDomain Φ k) := data.sigmaCompact
  change (data.pullbackMetric 0).inner q v w = cylinderReferenceMetric.inner q.val v w
  dsimp only [TangentSpace] at v w ⊢
  erw [data.pullback_inner]
  have hqsrc : q.val ∈ Ψ.source := q.property
  have hd (u : E3) :
      mfderiv (𝓡 3) (𝓡 3) (fun y : SourceDomain Φ k => Φ.map k y.val) q u =
        mfderiv (𝓡 3) (𝓡 3) Ψ q.val u :=
    copied_chart_subtype_deriv Ψ (sourceOpen Φ k) q hqsrc u
  simp only [hd]
  change ((S (φ k)).val.metric 0).inner (Ψ q.val)
    (mfderiv (𝓡 3) (𝓡 3) Ψ q.val v) (mfderiv (𝓡 3) (𝓡 3) Ψ q.val w) = _
  rw [(S (φ k)).val.initial]
  have hq : q.val ∈ cylinderReferenceOpenCylinder ((k : ℝ) + 1) := by
    change q.val ∈ (cylinderReferenceInitialMap (pointedInitialRotation (x (φ k)))
      ‖x (φ k)‖ ((k : ℝ) + 1) (hfit k)).source at hqsrc
    rwa [cylinderReferenceInitialMap_source] at hqsrc
  exact cylinderReferenceInitialMap_metric_inner _ _ _ _ q.val hq v w

end Maps

theorem exists_standard_cylinder_pointed_maps (τ : ℝ) (hτ : 0 < τ)
    (hlt : ENNReal.ofReal τ < uniformStandardLifetime)
    (S : ℕ → StandardSolution) (x : ℕ → E3)
    (hescape : Tendsto
      (fun i => (riemannianEDistOf ((S i).val.metric 0) 0 (x i)).toReal) atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ Φ : PointedCGHMaps (standardClosedPointedFlowSequence τ hτ hlt S x)
          cylinderPointedReference φ,
        (∀ k : ℕ, ∃ hfit : transitionEnd + ((k : ℝ) + 1) ≤ ‖x (φ k)‖,
          Φ.partialDiffeomorph k = cylinderReferenceInitialMap
            (pointedInitialRotation (x (φ k))) ‖x (φ k)‖ ((k : ℝ) + 1) hfit) ∧
        (∀ k : ℕ, sourceMetric Φ (standardClosedPointedMaps_sourceSigma Φ)
          (standardClosedPointedMaps_targetSigma Φ) k 0 =
            sourceMetricRestriction Φ cylinderReferenceMetric k) := by
  classical
  obtain ⟨φ, hφ, hcharts⟩ := escaping_initial_centers_growing_subsequence S x hescape
  have hfit : ∀ k : ℕ, transitionEnd + ((k : ℝ) + 1) ≤ ‖x (φ k)‖ :=
    fun k => (hcharts k).choose
  let Φ := standardCylinderPointedMaps τ hτ hlt S x φ hfit
  refine ⟨φ, hφ, Φ, ?_, ?_⟩
  · intro k
    exact ⟨hfit k, rfl⟩
  · intro k
    exact standardCylinderPointedMaps_initial τ hτ hlt S x φ hfit
      (standardClosedPointedMaps_sourceSigma Φ) (standardClosedPointedMaps_targetSigma Φ) k

end DifferentialGeometry.PDE.RicciFlow

end
