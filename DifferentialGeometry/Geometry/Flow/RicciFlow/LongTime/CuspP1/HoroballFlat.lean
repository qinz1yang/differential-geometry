import DifferentialGeometry.Geometry.Exponential.Flat.ExpCovering
import DifferentialGeometry.Geometry.Exponential.Flat.MetricDeckIsometries
import DifferentialGeometry.Geometry.Hyperbolic.Cusp
import DifferentialGeometry.Geometry.Curvature.Coordinates.RiemannTensorBridge
import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Geometry.Thurston.ConstantCurvatureAtlas

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set Function
open scoped Manifold ContDiff Topology
namespace GC.LongTime.CuspP1

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.Exponential
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection

section Generic

variable {E : Type*} [instE : NormedAddCommGroup E] [instER : NormedSpace ℝ E]
  [instFD : FiniteDimensional ℝ E] [instDim : NeZero (Module.finrank ℝ E)]
  {H : Type*} [instH : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [instBoundary : I.Boundaryless] {M : Type*} [instM : TopologicalSpace M]
  [instCM : ChartedSpace H M] [instMF : IsManifold I ∞ M]
  [instSigma : SigmaCompactSpace M] [instT2 : T2Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [instR : RiemannianBundle (fun x : M => TangentSpace I x)]
  [instEM : PseudoEMetricSpace M] [instRM : IsRiemannianManifold I M]
  [instComplete : CompleteSpace M]
  [instContinuous : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [instConn : ConnectedSpace M]

/-- A complete flat connected Riemannian manifold of dimension `n` is covered by `ℝⁿ` through a
local isometry. -/
theorem exists_flat_cover_metric_CPF3 {n : ℕ} (hn : Module.finrank ℝ E = n)
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hR : ∀ x (X Y Z : TangentSpace I x), riemannOp (LeviCivita (I := I) g) x X Y Z = 0) :
    ∃ p : EuclideanSpace ℝ (Fin n) → M,
      IsLocalDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ p ∧ IsCoveringMap p ∧
      Function.Surjective p ∧
      ∀ (x v w : EuclideanSpace ℝ (Fin n)), g.inner (p x) (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I p x v)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I p x w) = inner ℝ v w := by
  classical
  obtain ⟨a⟩ := (inferInstance : Nonempty M)
  let F : E → M := fun x => expMapIntrinsic g hEnorm a (show TangentSpace I a from x)
  obtain ⟨hF, hmetricF, hcovF, hsurjF⟩ :=
    flat_expMapIntrinsic_isLocalIsometry_isCoveringMap g hEnorm hR a
  let o := ((stdOrthonormalBasis ℝ (TangentSpace I a)).reindex (finCongr hn)).repr
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin n) := o.toLinearEquiv.toContinuousLinearEquiv
  let p : EuclideanSpace ℝ (Fin n) → M := F ∘ e.symm
  have hl : IsLocalDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ p := by
    intro x
    exact (e.symm.toDiffeomorph.isLocalDiffeomorph x).comp I M (hF (e.symm x))
  have hmetric : ∀ (x v w : EuclideanSpace ℝ (Fin n)), g.inner (p x)
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I p x v)
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I p x w) = inner ℝ v w := by
    intro x v w
    have hD (z : EuclideanSpace ℝ (Fin n)) :
        mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I p x z =
        mfderiv 𝓘(ℝ, E) I F (e.symm x) (e.symm z) := by
      have hc := mfderiv_comp x ((hF.contMDiff (e.symm x)).mdifferentiableAt (by simp))
        ((e.symm.toDiffeomorph.contMDiff x).mdifferentiableAt (by simp))
      rw [e.symm.mfderiv_eq] at hc
      exact congrArg (fun D => D z) hc
    change g.inner (F (e.symm x)) (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I p x v)
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I p x w) = inner ℝ v w
    rw [hD v, hD w, hmetricF]
    exact o.symm.inner_map_map v w
  exact ⟨p, hl, hcovF.comp_homeomorph e.symm.toHomeomorph,
    hsurjF.comp e.symm.surjective, hmetric⟩

end Generic


open DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint

local notation "E2" => EuclideanSpace ℝ (Fin 2)

private instance finrankTorusModelNeZero : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) :=
  ⟨by simp⟩

theorem torus_riemannOp_eq_zero_CPF3 (C : HyperbolicCusp) (x : Torus)
    (X Y Z : TangentSpace torusModel x) :
    riemannOp (LeviCivita (I := torusModel) C.torusMetric) x X Y Z = 0 := by
  have hsec : GC.Geometry.HasConstantSectionalCurvature C.torusMetric (0 : ℝ) := by
    intro p v w _
    rw [sectionalCurvature_eq_metricRm04StandardAt_div, C.torus_flat p v w, zero_div]
  rw [GC.Geometry.riemannOp_eq_smul_of_hasConstantSectionalCurvature hsec x X Y Z, zero_smul]

/-- The torus without its product metric structure (so that a Riemannian metric structure can be
attached). -/
def TorusSyn : Type := Torus

instance : TopologicalSpace TorusSyn := inferInstanceAs (TopologicalSpace Torus)
instance : ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))) TorusSyn :=
  inferInstanceAs (ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))) Torus)
instance : IsManifold torusModel ∞ TorusSyn := inferInstanceAs (IsManifold torusModel ∞ Torus)
instance : T2Space TorusSyn := inferInstanceAs (T2Space Torus)
instance : CompactSpace TorusSyn := inferInstanceAs (CompactSpace Torus)
instance : ConnectedSpace TorusSyn := inferInstanceAs (ConnectedSpace Torus)
instance : SigmaCompactSpace TorusSyn := inferInstanceAs (SigmaCompactSpace Torus)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- **Flat developing cover of the cusp cross-section.**  The flat metric `C.torusMetric` on
`Circle × Circle` is covered by the Euclidean plane through a surjective covering map which is a
local isometry. -/
theorem exists_flat_cover_torus_CPF3 (C : HyperbolicCusp) :
    ∃ cov : E2 → Torus, IsLocalDiffeomorph 𝓘(ℝ, E2) torusModel ∞ cov ∧ IsCoveringMap cov ∧
      Function.Surjective cov ∧
      ∀ (x v w : E2), C.torusMetric.inner (cov x) (mfderiv 𝓘(ℝ, E2) torusModel cov x v)
        (mfderiv 𝓘(ℝ, E2) torusModel cov x w) = inner ℝ v w := by
  let h : SmoothRiemannianMetric torusModel TorusSyn := C.torusMetric
  let : IsManifold torusModel 1 TorusSyn :=
    IsManifold.of_le (I := torusModel) (M := TorusSyn) (n := (∞ : WithTop ℕ∞)) (by decide)
  let : TopologicalSpace.MetrizableSpace TorusSyn := Manifold.metrizableSpace torusModel TorusSyn
  let : T3Space TorusSyn := inferInstance
  let : RiemannianBundle (fun x : TorusSyn => TangentSpace torusModel x) := ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
      (fun x : TorusSyn => TangentSpace torusModel x) :=
    ⟨⟨h.inner, h.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace TorusSyn := EMetricSpace.ofRiemannianMetric torusModel TorusSyn
  let : CompleteSpace TorusSyn := (RiemannianMetricComplete.of_compact h).complete
  have hEg : IsMetricNorm (I := torusModel) (M := TorusSyn) h := fun z v =>
    tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := torusModel) h z v
  exact exists_flat_cover_metric_CPF3 (I := torusModel) (M := TorusSyn) (n := 2)
    (by simp) h hEg (torus_riemannOp_eq_zero_CPF3 C)

end GC.LongTime.CuspP1
