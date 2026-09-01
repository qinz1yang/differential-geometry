import DifferentialGeometry.Geometry.Connection.Realization.SmoothSectionsLocal
import DifferentialGeometry.Geometry.Curvature.OpenSubtypeNaturality
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNormArity
import DifferentialGeometry.Geometry.Metric.Convergence.IteratedCovariantComponents
import DifferentialGeometry.Geometry.Metric.TensorInner.ComponentBounds
import DifferentialGeometry.Geometry.Metric.TensorInner.MetricGeodesicSpray
import Mathlib.Geometry.Manifold.Riemannian.Basic

set_option autoImplicit false

noncomputable section

universe uE

namespace DifferentialGeometry
namespace HCGCompactness

open Set
open Bundle Manifold
open scoped ContDiff Manifold BigOperators

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]

local instance euclideanDualNormedAddCommGroup : NormedAddCommGroup (E →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance euclideanDualNormedSpace : NormedSpace Real (E →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace

local instance euclideanBilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance euclideanBilinearNormedSpace :
    NormedSpace Real (E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace

noncomputable def constantModelVectorFieldSection (v : E) :
    ContMDiffSection 𝓘(Real, E) E (∞ : WithTop ℕ∞)
      (TangentSpace 𝓘(Real, E) : E → Type _) where
  toFun := fun x : E => (show TangentSpace 𝓘(Real, E) x from v)
  contMDiff_toFun := contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const

omit [NeZero (Module.finrank Real E)] [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem constantModelVectorFieldSection_apply (v x : E) :
    constantModelVectorFieldSection v x = constantModelVectorField v x := by
  exact (tangentSpaceModelContinuousLinearEquiv_symm_apply
    (I := 𝓘(Real, E)) x v).symm

omit [NeZero (Module.finrank Real E)] [FiniteDimensional ℝ E] in
theorem constantBasis_isLocalFrameOn
    {Idx : Type*}
    (U : TopologicalSpace.Opens E)
    (e : Module.Basis Idx Real E) :
    IsLocalFrameOn 𝓘(Real, E) E (1 : WithTop ℕ∞)
      (fun i (x : U) => (show TangentSpace 𝓘(Real, E) x from e i)) Set.univ := by
  constructor
  · intro _x _hx
    change LinearIndependent Real e
    exact e.linearIndependent
  · intro _x _hx
    change ⊤ ≤ Submodule.span Real (Set.range e)
    rw [e.span_eq]
  · intro i
    have hsmooth : ContMDiff 𝓘(Real, E)
        (𝓘(Real, E).prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (T% (fun y : U => (DifferentialGeometry.Geometry.Curvature.restrictOpenTangentSection
          (I := 𝓘(Real, E)) U (constantModelVectorFieldSection (E := E) (e i))) y)) :=
      (DifferentialGeometry.Geometry.Curvature.restrictOpenTangentSection
        (I := 𝓘(Real, E)) U (constantModelVectorFieldSection (E := E) (e i))).contMDiff.of_le
          (by simp : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
    have hsec : ContMDiffOn 𝓘(Real, E)
        (𝓘(Real, E).prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (T% (fun y : U => (DifferentialGeometry.Geometry.Curvature.restrictOpenTangentSection
          (I := 𝓘(Real, E)) U (constantModelVectorFieldSection (E := E) (e i))) y))
        Set.univ := hsmooth.contMDiffOn
    refine hsec.congr ?_
    intro y _hy
    refine TotalSpace.ext rfl ?_
    apply heq_of_eq
    rw [DifferentialGeometry.Geometry.Curvature.restrictOpenTangentSection_apply]
    with_unfolding_all
      rfl

private noncomputable def flatModelMetric :
    SmoothRiemannianMetric 𝓘(Real, E) E where
  inner := (riemannianMetricVectorSpace E).inner
  symm := (riemannianMetricVectorSpace E).symm
  pos := (riemannianMetricVectorSpace E).pos
  isVonNBounded := (riemannianMetricVectorSpace E).isVonNBounded
  contMDiff := (riemannianMetricVectorSpace E).contMDiff.of_le le_top

omit [NeZero (Module.finrank Real E)] in
theorem metricDerivNorm_le_of_iterCovComp_le
    (V : TopologicalSpace.Opens E) [T2Space V]
    (G g : SmoothRiemannianMetric 𝓘(Real, E) V) (a : Nat) (z : V)
    {B : Real} (hB : 0 ≤ B)
    (hequiv : ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤ g.inner z v v ∧
        g.inner z v v ≤ 2 * ‖v‖ ^ 2)
    (hcomp : ∀ slots : Fin (2 + a) → Fin (Module.finrank Real E),
      |iterCovComp (I := 𝓘(Real, E)) (M := V)
          (fun i _ ↦ (stdOrthonormalBasis Real E).toBasis i)
          (fun y ↦ Tensor.Coordinates.christoffelSymbolInFrame
            (Geometry.Connection.leviCivitaConnectionOfMetric
              (I := 𝓘(Real, E)) g)
            (fun i (_ : V) ↦ (stdOrthonormalBasis Real E).toBasis i)
            (constantBasis_isLocalFrameOn V
              (stdOrthonormalBasis Real E).toBasis) y)
          (frameComp0S (I := 𝓘(Real, E))
            (Tensor0SBundle.metricTensorField (I := 𝓘(Real, E)) G -
              Tensor0SBundle.metricTensorField (I := 𝓘(Real, E)) g)
            (fun i (_ : V) ↦ (stdOrthonormalBasis Real E).toBasis i))
          a z slots| ≤ B) :
    metricDerivNorm (I := 𝓘(Real, E)) a G g g z ≤
      Real.sqrt (2 ^ (2 + a)) *
        (Real.sqrt
          (Fintype.card
            (Fin (2 + a) → Fin (Module.finrank Real E)) : Real) * B) := by
  classical
  let e : Module.Basis (Fin (Module.finrank Real E)) Real E :=
    (stdOrthonormalBasis Real E).toBasis
  let frame : Fin (Module.finrank Real E) →
      (y : V) → TangentSpace 𝓘(Real, E) y := fun i _ ↦ e i
  let hframe : IsLocalFrameOn 𝓘(Real, E) E (1 : WithTop ℕ∞)
      frame Set.univ := constantBasis_isLocalFrameOn V e
  let g0 := (flatModelMetric (E := E)).restrictOpen (I := 𝓘(Real, E)) V
  have hON0 : ∀ i j : Fin (Module.finrank Real E),
      g0.inner z (e i) (e j) = if i = j then (1 : Real) else 0 := by
    intro i j
    have h := (stdOrthonormalBasis Real E).inner_eq_ite i j
    with_unfolding_all
      exact h
  have hinv0 : Tensor0SBundle.MetricInverseInBasisGen
      (I := 𝓘(Real, E)) g0 z e
      (Tensor0SBundle.identityInvMetric
        (Idx := Fin (Module.finrank Real E))) := by
    have h := DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal
      (I := 𝓘(Real, E)) g0 e hON0
    with_unfolding_all
      change Tensor0SBundle.MetricInverseInBasisGen
        (I := modelWithCornersSelf Real E) g0 z e
          (fun i j => if i = j then 1 else 0)
    exact h
  have hequiv' : ∀ v : TangentSpace 𝓘(Real, E) z,
      (2 : Real)⁻¹ * g0.inner z v v ≤ g.inner z v v ∧
        g.inner z v v ≤ 2 * g0.inner z v v := by
    intro v
    change E at v
    have hg0 : g0.inner z v v = ‖v‖ ^ 2 := by
      have h := real_inner_self_eq_norm_sq v
      with_unfolding_all
        exact h
    rw [hg0]
    simpa only [one_div] using hequiv v
  obtain ⟨b, hbON⟩ :=
    DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis
      (I := 𝓘(Real, E)) g z
  have hbinv : Tensor0SBundle.MetricInverseInBasisGen
      (I := 𝓘(Real, E)) g z b
      (Tensor0SBundle.identityInvMetric
        (Idx := Fin (Module.finrank Real (TangentSpace 𝓘(Real, E) z)))) := by
    have h := DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal
      (I := 𝓘(Real, E)) g b hbON
    with_unfolding_all
      change Tensor0SBundle.MetricInverseInBasisGen
        (I := modelWithCornersSelf Real E) g z b
          (fun i j => if i = j then 1 else 0)
    exact h
  rw [metricDerivNorm_eq_iterCov (I := 𝓘(Real, E)) G g g a b hbinv]
  apply Tensor0SBundle.sqrt_normSq0S_le_of_metric_equiv_of_component_bound
    (I := 𝓘(Real, E)) g0 g z (2 + a) e hinv0
      (C := 2) (B := B) (by norm_num) hequiv' _ hB
  intro slots
  with_unfolding_all
    change
      |iterCov (I := modelWithCornersSelf Real E) g 2
        (Tensor0SBundle.metricTensorField (I := modelWithCornersSelf Real E) G -
          Tensor0SBundle.metricTensorField (I := modelWithCornersSelf Real E) g)
        a z (fun q ↦ e (slots q))| ≤ B
  have ht := iterCovComp_eq_iterCov (I := 𝓘(Real, E)) g
    (Tensor0SBundle.metricTensorField (I := 𝓘(Real, E)) G -
      Tensor0SBundle.metricTensorField (I := 𝓘(Real, E)) g)
    frame hframe isOpen_univ a (Set.mem_univ z) slots
  have ht' :
      iterCovComp (I := 𝓘(Real, E)) frame
          (fun y ↦ Tensor.Coordinates.christoffelSymbolInFrame
            (Geometry.Connection.leviCivitaConnectionOfMetric
              (I := 𝓘(Real, E)) g) frame hframe y)
          (frameComp0S (I := 𝓘(Real, E))
            (Tensor0SBundle.metricTensorField (I := 𝓘(Real, E)) G -
              Tensor0SBundle.metricTensorField (I := 𝓘(Real, E)) g) frame)
          a z slots =
        iterCov (I := 𝓘(Real, E)) g 2
          (Tensor0SBundle.metricTensorField (I := 𝓘(Real, E)) G -
            Tensor0SBundle.metricTensorField (I := 𝓘(Real, E)) g)
          a z (fun q ↦ e (slots q)) := by
    have htuple : frameTuple (I := modelWithCornersSelf Real E) frame z slots =
        fun q ↦ e (slots q) := by
      funext q
      with_unfolding_all
        rfl
    rw [htuple] at ht
    exact ht
  calc
    |iterCov (I := 𝓘(Real, E)) g 2
        (Tensor0SBundle.metricTensorField (I := 𝓘(Real, E)) G -
          Tensor0SBundle.metricTensorField (I := 𝓘(Real, E)) g)
        a z (fun q ↦ e (slots q))| =
        |iterCovComp (I := 𝓘(Real, E)) frame
          (fun y ↦ Tensor.Coordinates.christoffelSymbolInFrame
            (Geometry.Connection.leviCivitaConnectionOfMetric
              (I := 𝓘(Real, E)) g) frame hframe y)
          (frameComp0S (I := 𝓘(Real, E))
            (Tensor0SBundle.metricTensorField (I := 𝓘(Real, E)) G -
              Tensor0SBundle.metricTensorField (I := 𝓘(Real, E)) g) frame)
          a z slots| := congrArg abs ht'.symm
    _ ≤ B := by simpa only [e, frame, hframe] using hcomp slots

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] in
theorem metric_iterCovComp_mdifferentiableAt
    (V : TopologicalSpace.Opens E)
    (e : Module.Basis (Fin (Module.finrank Real E)) Real E)
    (B Q : E → (E →L[Real] E →L[Real] Real))
    (hBcd : ContDiffOn Real (∞ : WithTop ℕ∞) B V)
    (hQcd : ContDiffOn Real (∞ : WithTop ℕ∞) Q V)
    (hBco : ∀ z : E, z ∈ V → IsCoercive (B z)) :
    let Gamma := fun z i j m ↦ e.coord m
      (MetricKoszul.raisedKoszulOp (B z) (fderiv Real B z)
        (e i) (e j))
    let base := fun z (slots : Fin 2 → Fin (Module.finrank Real E)) ↦
      (Q z - B z) (e (slots 0)) (e (slots 1))
    ∀ q : Nat, ∀ z : V,
      ∀ slots : Fin (2 + q) → Fin (Module.finrank Real E),
        MDifferentiableAt 𝓘(Real, E) 𝓘(Real, Real)
          (fun y : E ↦ iterCovComp (I := 𝓘(Real, E))
            (fun i _ ↦ e i) Gamma base q y slots) (z : E) := by
  dsimp only
  let : NormedAddCommGroup (E →L[Real] E →L[Real] E) :=
    MetricKoszul.sprayVecBilinNormedGroup
  let : NormedSpace Real (E →L[Real] E →L[Real] E) :=
    MetricKoszul.sprayVecBilinNormedSpace
  let raised : E → E →L[Real] E →L[Real] E := fun z =>
    MetricKoszul.raisedKoszulOp (B z) (fderiv Real B z)
  have hraised : ContDiffOn Real (∞ : WithTop ℕ∞) raised V := by
    have hraw := MetricKoszul.raisedOp_smooth V.2 hBcd hBco
    with_unfolding_all
      exact hraw
  have hchr : ∀ d i j : Fin (Module.finrank Real E),
      ContMDiffOn 𝓘(Real, E) 𝓘(Real, Real) ∞
        (fun z => e.coord j (raised z (e d) (e i))) V := by
    intro d i j
    rw [contMDiffOn_iff_contDiffOn]
    exact (e.coord j).toContinuousLinearMap.contDiff.comp_contDiffOn
      ((hraised.clm_apply contDiffOn_const).clm_apply contDiffOn_const)
  have hbase : ∀ slots : Fin 2 → Fin (Module.finrank Real E),
      ContMDiffOn 𝓘(Real, E) 𝓘(Real, Real) ∞
        (fun z => (Q z - B z) (e (slots 0)) (e (slots 1))) V := by
    intro slots
    rw [contMDiffOn_iff_contDiffOn]
    exact ((hQcd.sub hBcd).clm_apply contDiffOn_const).clm_apply contDiffOn_const
  have hframe : ∀ d : Fin (Module.finrank Real E),
      ContMDiffOn 𝓘(Real, E) (𝓘(Real, E).prod 𝓘(Real, E)) ∞
        (fun (y : E) => TotalSpace.mk' E (E := TangentSpace 𝓘(Real, E)) y
          (show TangentSpace 𝓘(Real, E) y from e d)) V := by
    intro d
    simpa only [constantModelVectorFieldSection] using
      (constantModelVectorFieldSection (E := E) (e d)).contMDiff_toFun.contMDiffOn
  intro q z slots
  exact DifferentialGeometry.PDE.RicciFlow.iterCovComp_mdiffAt V.2
    (fun i (_ : E) ↦ e i)
    (fun z i j m => e.coord m (raised z (e i) (e j)))
    (fun z s => (Q z - B z) (e (s 0)) (e (s 1)))
    hframe hchr hbase z.2 q slots

end HCGCompactness
end DifferentialGeometry
