import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.Bounds
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.ChartFamily
import DifferentialGeometry.Analysis.Calculus.Inverse.ContinuousLinearMapNeumann

import DifferentialGeometry.Bundle.Frame
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.CenterOfMass.NormalCoordinates.InverseDistance
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.DiagonalInverse.BranchScale
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.LocalGeometry
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.CenterOfMass.Smoothness
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.CenterOfMass.NormalCoordinates.ChartEquation

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Bundle Manifold Set TopologicalSpace
open scoped BigOperators ContDiff Manifold NNReal Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

open DifferentialGeometry.Integral.DivergenceTheorem

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

private local instance : NormedAddCommGroup (E →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace Real (E →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace
private local instance : NormedAddCommGroup (E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace Real (E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace

noncomputable def normalPhaseRead
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (z : E × E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    E := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  exact (trivializationAt E (TangentSpace I) x
    (normalTanHome (I := I) Y x z)).2

noncomputable def normalReadCLM
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (u : E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    E →L[Real] E := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  exact (trivializationAt E (TangentSpace I) x).continuousLinearMapAt Real
    (expMapDiffeo (I := I) Y.metric x u) |>.comp
      (mfderiv 𝓘(Real, E) I
        (fun v : E ↦ expMapDiffeo (I := I) Y.metric x v) u)

omit [NeZero (Module.finrank ℝ E)] in
theorem normalPhaseRead_eq
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    {u v : E} (hu : u ∈ normalBall (I := I) Y x) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    expMapDiffeo (I := I) Y.metric x u ∈
      (trivializationAt E (TangentSpace I) x).baseSet →
    normalPhaseRead (I := I) Y x (u, v) = normalReadCLM (I := I) Y x u v := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  intro hbase
  rw [normalPhaseRead, normalTanHome_apply (I := I) Y x (u, v) hu]
  unfold normalReadCLM normalTangent
  with_unfolding_all
    change (trivializationAt E (TangentSpace I) x
        ⟨expMapDiffeo (I := I) Y.metric x u,
          mfderiv 𝓘(Real, E) I
            (fun w : E ↦ expMapDiffeo (I := I) Y.metric x w) u v⟩).2 =
      (trivializationAt E (TangentSpace I) x).continuousLinearMapAt Real
        (expMapDiffeo (I := I) Y.metric x u)
          (mfderiv 𝓘(Real, E) I
            (fun w : E ↦ expMapDiffeo (I := I) Y.metric x w) u v)
  rw [show ⇑((trivializationAt E (TangentSpace I) x).continuousLinearMapAt Real
      (expMapDiffeo (I := I) Y.metric x u)) =
        ⇑((trivializationAt E (TangentSpace I) x).linearMapAt Real
          (expMapDiffeo (I := I) Y.metric x u)) from rfl,
    (trivializationAt E (TangentSpace I) x).coe_linearMapAt_of_mem hbase]

noncomputable def normalReadCLE
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    {u : E} (hu : u ∈ normalBall (I := I) Y x) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    expMapDiffeo (I := I) Y.metric x u ∈
      (trivializationAt E (TangentSpace I) x).baseSet →
    E ≃L[Real] E := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  intro hbase
  exact ((PartialDiffeomorph.isLocalDiffeomorphAt
      (I := 𝓘(Real, E)) (J := I) (n := ∞)
      (normalExpPD (I := I) Y x) (by
        with_unfolding_all
          exact hu)).mfderivToContinuousLinearEquiv
        (by simp)).trans
    ((trivializationAt E (TangentSpace I) x).continuousLinearEquivAt
      Real (expMapDiffeo (I := I) Y.metric x u) hbase)

omit [NeZero (Module.finrank ℝ E)] in
theorem normalReadCLE_coe
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    {u : E} (hu : u ∈ normalBall (I := I) Y x) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ∀ hbase : expMapDiffeo (I := I) Y.metric x u ∈
        (trivializationAt E (TangentSpace I) x).baseSet,
    (normalReadCLE (I := I) Y x hu hbase : E →L[Real] E) =
      normalReadCLM (I := I) Y x u := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  intro hbase
  let hloc : IsLocalDiffeomorphAt 𝓘(Real, E) I ∞
      (normalExpPD (I := I) Y x) u :=
    PartialDiffeomorph.isLocalDiffeomorphAt
      (I := 𝓘(Real, E)) (J := I) (n := ∞)
      (normalExpPD (I := I) Y x) (by
        with_unfolding_all
          exact hu)
  unfold normalReadCLE normalReadCLM
  ext v
  change
    ((trivializationAt E (TangentSpace I) x).continuousLinearEquivAt
        Real (expMapDiffeo (I := I) Y.metric x u) hbase
      ((hloc.mfderivToContinuousLinearEquiv (by simp)) v)) =
      (trivializationAt E (TangentSpace I) x).continuousLinearMapAt Real
        (expMapDiffeo (I := I) Y.metric x u)
          (mfderiv 𝓘(Real, E) I
            (fun w : E ↦ expMapDiffeo (I := I) Y.metric x w) u v)
  rw [Bundle.Trivialization.coe_continuousLinearEquivAt_eq _ hbase]
  apply congrArg ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt
    Real (expMapDiffeo (I := I) Y.metric x u))
  exact congrArg (fun A : E →L[Real] TangentSpace I
      (expMapDiffeo (I := I) Y.metric x u) => A v)
    (hloc.mfderivToContinuousLinearEquiv_coe (by simp))

omit [NeZero (Module.finrank ℝ E)] in
theorem normalPhaseRead_cd
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    {u v : E} (hu : u ∈ normalBall (I := I) Y x) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    expMapDiffeo (I := I) Y.metric x u ∈
      (trivializationAt E (TangentSpace I) x).baseSet →
    ContDiffAt Real ∞ (normalPhaseRead (I := I) Y x) (u, v) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  intro hbase
  have hzSource : (u, v) ∈ (normalTanHome (I := I) Y x).source := by
    rw [normalTanHome_source]
    exact hu
  have htan : ContMDiffAt 𝓘(Real, E × E) I.tangent ∞
      (normalTanHome (I := I) Y x) (u, v) :=
    ((normalTanHome_contMDiffOn (I := I) Y x) (u, v) hzSource).contMDiffAt
      ((normalTanHome (I := I) Y x).open_source.mem_nhds hzSource)
  have hzTriv : normalTanHome (I := I) Y x (u, v) ∈
      (trivializationAt E (TangentSpace I) x).source := by
    apply (trivializationAt E (TangentSpace I) x).mem_source.mpr
    rw [normalTanHome_apply (I := I) Y x (u, v) hu]
    exact hbase
  have hread :=
    (((trivializationAt E (TangentSpace I) x).contMDiffAt_iff hzTriv).mp htan).2
  exact contMDiffAt_iff_contDiffAt.mp hread

omit [NeZero (Module.finrank ℝ E)] in
theorem normalReadCLM_cd
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    {u : E} (hu : u ∈ normalBall (I := I) Y x) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    expMapDiffeo (I := I) Y.metric x u ∈
      (trivializationAt E (TangentSpace I) x).baseSet →
    ContDiffAt Real ∞ (normalReadCLM (I := I) Y x) u := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  intro hbase
  rw [← contMDiffAt_iff_contDiffAt]
  apply contMDiffAt_clm_of_pointwise (IB := 𝓘(Real, E)) (X := E)
  intro v
  have hpair : ContDiffAt Real ∞ (fun a : E => (a, v)) u := by
    fun_prop
  have hphase : ContMDiffAt 𝓘(Real, E) 𝓘(Real, E) ∞
      (fun a : E => normalPhaseRead (I := I) Y x (a, v)) u :=
    ((normalPhaseRead_cd (I := I) Y x (u := u) (v := v) hu hbase).comp u
      hpair).contMDiffAt
  refine hphase.congr_of_eventuallyEq ?_
  have huSource : u ∈ (normalExpPD (I := I) Y x).source := by
    with_unfolding_all
      exact hu
  have hExp : ContinuousAt
      (fun a : E => expMapDiffeo (I := I) Y.metric x a) u := by
    exact (((normalExpPD (I := I) Y x).contMDiffOn_toFun u huSource).contMDiffAt
      ((normalExpPD (I := I) Y x).open_source.mem_nhds huSource)).continuousAt
  have hnormal : (↑(normalBall (I := I) Y x) : Set E) ∈ nhds u :=
    (normalBall (I := I) Y x).isOpen.mem_nhds hu
  have hbaseNhd :
      (fun a : E => expMapDiffeo (I := I) Y.metric x a) ⁻¹'
          (trivializationAt E (TangentSpace I) x).baseSet ∈ nhds u :=
    hExp.preimage_mem_nhds
      ((trivializationAt E (TangentSpace I) x).open_baseSet.mem_nhds hbase)
  filter_upwards [hnormal, hbaseNhd] with a ha hb
  exact (normalPhaseRead_eq (I := I) Y x (u := a) (v := v) ha hb).symm

noncomputable def invVelocitySum {ι : Type*} [Fintype ι]
    (e : OpenPartialHomeomorph (E × E) (E × E))
    (mu : ι → Real) (xi : ι → E) (z : E) : E :=
  ∑ i, mu i • (e.symm (z, xi i)).2

omit [FiniteDimensional Real E] [CompleteSpace E]
    [NeZero (Module.finrank Real E)] in
theorem invVelocitySum_congr_ne {ι : Type*} [Fintype ι]
    (e : OpenPartialHomeomorph (E × E) (E × E))
    (mu : ι → Real) (xi xi' : ι → E) (z : E)
    (hxi : ∀ i, mu i ≠ 0 → xi i = xi' i) :
    invVelocitySum e mu xi z = invVelocitySum e mu xi' z := by
  classical
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hi : mu i = 0
  · simp only [hi, zero_smul]
  · rw [hxi i hi]

omit [FiniteDimensional Real E] [CompleteSpace E]
    [NeZero (Module.finrank Real E)] in
theorem invVelocitySum_congr_br {ι : Type*} [Fintype ι]
    (e e' : OpenPartialHomeomorph (E × E) (E × E))
    (mu : ι → Real) (xi : ι → E) (z : E) (heq : e ≈ e')
    (htgt : ∀ i, mu i ≠ 0 → (z, xi i) ∈ e.target) :
    invVelocitySum e mu xi z = invVelocitySum e' mu xi z := by
  classical
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hmu : mu i = 0
  · simp only [hmu, zero_smul]
  · rw [heq.symm_eqOn_target (htgt i hmu)]

omit [FiniteDimensional Real E] [CompleteSpace E]
    [NeZero (Module.finrank Real E)] in
theorem invVelocitySum_fderiv {ι : Type*} [Fintype ι]
    (e : OpenPartialHomeomorph (E × E) (E × E))
    (mu : ι → Real) (xi : ι → E) {z : E}
    (hinv : ContDiffOn Real ∞ (e.symm : E × E → E × E) e.target)
    (htgt : ∀ i, (z, xi i) ∈ e.target) :
    HasFDerivAt (invVelocitySum e mu xi)
      (∑ i, mu i • fderiv Real (fun u : E => (e.symm (u, xi i)).2) z) z := by
  classical
  have hvel : ∀ i, DifferentiableAt Real
      (fun u : E => (e.symm (u, xi i)).2) z := by
    intro i
    have hInvAt : ContDiffAt Real ∞ (e.symm : E × E → E × E) (z, xi i) :=
      (hinv (z, xi i) (htgt i)).contDiffAt
        (e.open_target.mem_nhds (htgt i))
    have hpair : DifferentiableAt Real (fun u : E => (u, xi i)) z := by
      fun_prop
    exact ((hInvAt.differentiableAt (by simp)).comp z hpair).snd
  with_unfolding_all
    exact HasFDerivAt.fun_sum (u := Finset.univ) fun i _ =>
      (hvel i).hasFDerivAt.const_smul (mu i)

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] in
theorem invVelocitySum_inv {ι : Type*} [Fintype ι]
    (e : OpenPartialHomeomorph (E × E) (E × E))
    (mu : ι → Real) (xi : ι → E) {z : E} {eta : NNReal}
    (hinv : ContDiffOn Real ∞ (e.symm : E × E → E × E) e.target)
    (htgt : ∀ i, (z, xi i) ∈ e.target)
    (happrox : ApproximatesLinearOn (e.symm : E × E → E × E)
      ((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E)) e.target eta)
    (hmu : ∀ i, 0 ≤ mu i) (hsum : ∑ i, mu i = 1) (heta : eta < 1) :
    ∃ L : E ≃L[Real] E,
      HasFDerivAt (invVelocitySum e mu xi) (L : E →L[Real] E) z := by
  classical
  let A : ι → E →L[Real] E := fun i =>
    fderiv Real (fun u : E => (e.symm (u, xi i)).2) z
  have hInvDiff : ∀ i,
      DifferentiableAt Real (e.symm : E × E → E × E) (z, xi i) := by
    intro i
    exact ((hinv (z, xi i) (htgt i)).contDiffAt
      (e.open_target.mem_nhds (htgt i))).differentiableAt (by simp)
  have hA : ∀ i, ‖A i + ContinuousLinearMap.id Real E‖ ≤ (eta : Real) := by
    intro i
    exact PhaseFlow.invVelocity_fderiv_le happrox
      (e.open_target.mem_nhds (htgt i)) (hInvDiff i)
  have hetaReal : (eta : Real) < 1 := by exact_mod_cast heta
  obtain ⟨L, hL⟩ := ContinuousLinearMap.sum_near_neg_inv
    mu A (eta : Real) hmu hsum hA hetaReal
  refine ⟨L, ?_⟩
  have hderiv : HasFDerivAt (invVelocitySum e mu xi)
      (∑ i, mu i • A i) z := by
    simpa only [A] using invVelocitySum_fderiv e mu xi hinv htgt
  rw [hL]
  exact hderiv

omit [NeZero (Module.finrank ℝ E)] in
theorem normalComp_inv {ι : Type*} [Fintype ι]
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (e : OpenPartialHomeomorph (E × E) (E × E))
    (mu : ι → Real) (xi : ι → E) {z : E} {eta : NNReal}
    (hu : z ∈ normalBall (I := I) Y x)
    (hinv : ContDiffOn Real ∞ (e.symm : E × E → E × E) e.target)
    (htgt : ∀ i, (z, xi i) ∈ e.target)
    (happrox : ApproximatesLinearOn (e.symm : E × E → E × E)
      ((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E)) e.target eta)
    (hmu : ∀ i, 0 ≤ mu i) (hsum : ∑ i, mu i = 1) (heta : eta < 1)
    (hzero : invVelocitySum e mu xi z = 0) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    expMapDiffeo (I := I) Y.metric x z ∈
      (trivializationAt E (TangentSpace I) x).baseSet →
    ∃ L : E ≃L[Real] E,
      HasFDerivAt
        (fun u : E => normalReadCLM (I := I) Y x u (invVelocitySum e mu xi u))
        (L : E →L[Real] E) z := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  intro hbase
  obtain ⟨LS, hLS⟩ := invVelocitySum_inv e mu xi hinv htgt happrox hmu hsum heta
  have hK : HasFDerivAt (normalReadCLM (I := I) Y x)
      (fderiv Real (normalReadCLM (I := I) Y x) z) z :=
    ((normalReadCLM_cd (I := I) Y x hu hbase).differentiableAt
      (by simp)).hasFDerivAt
  have happ : HasFDerivAt
      (fun u : E => normalReadCLM (I := I) Y x u (invVelocitySum e mu xi u))
      ((normalReadCLM (I := I) Y x z).comp (LS : E →L[Real] E)) z := by
    simpa only [hzero, map_zero, add_zero] using hK.clm_apply hLS
  let KR : E ≃L[Real] E := normalReadCLE (I := I) Y x hu hbase
  let L : E ≃L[Real] E := LS.trans KR
  have hL : (L : E →L[Real] E) =
      (normalReadCLM (I := I) Y x z).comp (LS : E →L[Real] E) := by
    ext v
    change normalReadCLE (I := I) Y x hu hbase (LS v) =
      normalReadCLM (I := I) Y x z (LS v)
    exact congrArg (fun A : E →L[Real] E => A (LS v))
      (normalReadCLE_coe (I := I) Y x hu hbase)
  refine ⟨L, ?_⟩
  rw [hL]
  exact happ

namespace IsNormalDiag

theorem diagonalInverseCoordinates_normalPair_eq
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) {q : NNReal} {delta : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q) (he : IsNormalDiag (I := I) Y hcomplete hconn x q delta e)
    (hf : NormalDiagFence (I := I) Y x q e) {w : E × E} (hw : w ∈ e.target) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : ConnectedSpace Y.M := hconn
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M :=
      Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
      (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    (toBranch (I := I) Y hcomplete hconn x hq he).diagonalInverseCoordinates
        (normalPair (I := I) Y x w) =
      normalReadCLM (I := I) Y x w.1 (e.symm w).2 := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : ConnectedSpace Y.M := hconn
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
    (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  have heData := he
  change e.source = Metric.ball (0 : E × E) q ∧
    e 0 = 0 ∧
    ContDiffOn Real ∞ (e : E × E → E × E) e.source ∧
    Metric.closedBall (0 : E × E) delta ⊆ e.target ∧
    ContDiffOn Real ∞ e.symm e.target ∧
    ∀ z ∈ Metric.closedBall (0 : E × E) q,
      normalPair (I := I) Y x (e z) =
        diagExp (I := I) Y.metric (normal_enorm (I := I) Y)
          (normalTangent (I := I) Y x z) at heData
  have hzBall : e.symm w ∈ Metric.ball (0 : E × E) q := by
    rw [← heData.1]
    exact e.map_target hw
  have hfence := hf
  change ∀ z ∈ Metric.closedBall (0 : E × E) q,
    z.1 ∈ normalBall (I := I) Y x ∧
    (e z).1 ∈ normalBall (I := I) Y x ∧
    (e z).2 ∈ normalBall (I := I) Y x at hfence
  have hzNormal : (e.symm w).1 ∈ normalBall (I := I) Y x :=
    (hfence (e.symm w) (Metric.ball_subset_closedBall hzBall)).1
  have hzNormLt : ‖(e.symm w).1‖ <
      expMapC2Radius (I := I) Y.metric x := by
    have hzNormal' := hzNormal
    change (e.symm w).1 ∈
      Metric.ball (0 : E) (expMapC2Radius (I := I) Y.metric x) at hzNormal'
    rwa [Metric.mem_ball, dist_zero_right] at hzNormal'
  have hzExpSource : (e.symm w).1 ∈
      (expMapDiffeo (I := I) Y.metric x).source :=
    mem_expMapDiffeo_source_of_norm_lt_radius (I := I) Y.metric x hzNormLt
  have hbase : expMapDiffeo (I := I) Y.metric x (e.symm w).1 ∈
      (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact NormalCoordinates.exp_target_sub_chart (I := I) Y.metric x
      ((expMapDiffeo (I := I) Y.metric x).map_source hzExpSource)
  have htransport := branch_coordinate_transport (I := I) Y hcomplete hconn x hq he hf
  unfold DiagonalInverseBranch.diagonalInverseCoordinates
  rw [htransport.2.2 w hw,
    ← normalTanHome_apply (I := I) Y x (e.symm w) hzNormal]
  change normalPhaseRead (I := I) Y x (e.symm w) = _
  rw [normalPhaseRead_eq (I := I) Y x hzNormal hbase,
    symm_fst_eq (I := I) Y hcomplete hconn x he hf hw]

theorem inv_cov_coord
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) {q : NNReal} {delta : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q) (he : IsNormalDiag (I := I) Y hcomplete hconn x q delta e)
    (hf : NormalDiagFence (I := I) Y x q e)
    {z xi : E} (hw : (z, xi) ∈ e.target)
    (hzQ : z ∈ normalQuarter (I := I) Y x) (v : E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : ConnectedSpace Y.M := hconn
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M :=
      Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
      (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    let B := toBranch (I := I) Y hcomplete hconn x hq he
    mfderiv 𝓘(Real, E) I
        (fun u : E => expMapDiffeo (I := I) Y.metric x u) z
        (((DifferentialGeometry.Geometry.Curvature.metricCov (I := 𝓘(Real, E)) (M := E)
          (normalTotal (I := I) Y x)).toFun
          (fun u : E => (e.symm (u, xi)).2) z) v) =
      ((DifferentialGeometry.Geometry.Curvature.metricCov (I := I) (M := Y.M) Y.metric).toFun
        (fun y : Y.M => (B.inv
          (y, expMapDiffeo (I := I) Y.metric x xi)).snd)
        (expMapDiffeo (I := I) Y.metric x z))
        (mfderiv 𝓘(Real, E) I
          (fun u : E => expMapDiffeo (I := I) Y.metric x u) z v) := by
  classical
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : ConnectedSpace Y.M := hconn
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
    (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  dsimp only
  let B := toBranch (I := I) Y hcomplete hconn x hq he
  let pt : Y.M := expMapDiffeo (I := I) Y.metric x xi
  let y0 : Y.M := expMapDiffeo (I := I) Y.metric x z
  let Vloc : E → E := fun u => (e.symm (u, xi)).2
  let VTan : (u : E) → TangentSpace 𝓘(Real, E) u := fun u => Vloc u
  let Zloc : (y : Y.M) → TangentSpace I y := fun y =>
    show TangentSpace I y from (B.inv (y, pt)).snd
  let Umod : Set E := (fun u : E => (u, xi)) ⁻¹' e.target
  have hUopen : IsOpen Umod := by
    exact e.open_target.preimage (continuous_id.prodMk continuous_const)
  have hzU : z ∈ Umod := hw
  have heData := he
  change e.source = Metric.ball (0 : E × E) q ∧
    e 0 = 0 ∧
    ContDiffOn Real ∞ (e : E × E → E × E) e.source ∧
    Metric.closedBall (0 : E × E) delta ⊆ e.target ∧
    ContDiffOn Real ∞ e.symm e.target ∧
    ∀ a ∈ Metric.closedBall (0 : E × E) q,
      normalPair (I := I) Y x (e a) =
        diagExp (I := I) Y.metric (normal_enorm (I := I) Y)
          (normalTangent (I := I) Y x a) at heData
  have hpair : ContDiffOn Real ∞ (fun u : E => (u, xi)) Umod :=
    (contDiff_id.prodMk contDiff_const).contDiffOn
  have hsymm : ContDiffOn Real ∞ (fun u : E => e.symm (u, xi)) Umod :=
    heData.2.2.2.2.1.comp hpair (by
      intro u hu
      exact hu)
  have hVfun : ContDiffOn Real ∞ Vloc Umod := by
    simpa only [Vloc] using hsymm.snd
  have hVsec : ContMDiffOn 𝓘(Real, E)
      (𝓘(Real, E).prod 𝓘(Real, E)) ∞
      (T% VTan) Umod := by
    exact contMDiffOn_vectorSpace_iff_contDiffOn.mpr (by simpa only [VTan] using hVfun)
  obtain ⟨Vexts, hVexts⟩ := exists_contMDiffSection_eqOn_nhd
    (I := 𝓘(Real, E)) (F := E) (V := TangentSpace 𝓘(Real, E))
    (n := (⊤ : ℕ∞)) (s := fun _ : Unit => VTan)
    (u := Umod) (p := z) (fun _ => hVsec) hUopen hzU
  let Vext : Cₛ^∞⟮𝓘(Real, E); E,
      (TangentSpace 𝓘(Real, E) : E → Type _)⟯ := Vexts ()
  have hVext : (fun u : E => Vext u) =ᶠ[nhds z] Vloc := by
    filter_upwards [hVexts] with u hu using hu ()
  let S : Set Y.M := (fun y : Y.M => (y, pt)) ⁻¹' B.dom
  have hSopen : IsOpen S := by
    change IsOpen ((fun y : Y.M => (y, pt)) ⁻¹' B.hom.target)
    exact B.hom.open_target.preimage (continuous_id.prodMk continuous_const)
  have htransport := branch_coordinate_transport (I := I) Y hcomplete hconn x hq he hf
  have hpairDom : normalPair (I := I) Y x (z, xi) ∈ B.dom := by
    rw [← htransport.2.1]
    refine ⟨(z, xi), hw, ?_⟩
    exact normalPairHome_apply (I := I) Y x (z, xi)
  have hyS : y0 ∈ S := by
    with_unfolding_all
      exact hpairDom
  have hdom : ∀ y ∈ S, (y, pt) ∈ B.dom := by
    intro y hy
    exact hy
  have hZsec : ContMDiffOn I I.tangent ∞
      (T% Zloc) S :=
    B.inv_vector_contMDiffOn_at_fixed_target hdom
  obtain ⟨Zexts, hZexts⟩ := exists_contMDiffSection_eqOn_nhd
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
    (s := fun _ : Unit => Zloc)
    (u := S) (p := y0) (fun _ => hZsec) hSopen hyS
  let Zext : Cₛ^∞⟮I; E, (TangentSpace I : Y.M → Type _)⟯ := Zexts ()
  have hZext : (fun y : Y.M => Zext y) =ᶠ[nhds y0]
      Zloc := by
    filter_upwards [hZexts] with y hy using hy ()
  let UQ := normalQuarter (I := I) Y x
  let WQ := normalQuarterImage (I := I) Y x
  let : SigmaCompactSpace UQ := normalQuarterSigma (I := I) Y x
  let : SigmaCompactSpace WQ := normalQuarterImageSigma (I := I) Y x
  let zQ : UQ := ⟨z, hzQ⟩
  let Phi := normalQuarterDiffeo (I := I) Y x
  have hback : Filter.Tendsto (fun a : WQ => ((Phi.symm a : UQ) : E))
      (nhds (Phi zQ)) (nhds z) := by
    have hc : ContinuousAt (fun a : WQ => ((Phi.symm a : UQ) : E))
        (Phi zQ) :=
      (continuous_subtype_val.comp Phi.symm.continuous).continuousAt
    have hz : ((Phi.symm (Phi zQ) : UQ) : E) = z := by
      simpa only [zQ] using congrArg Subtype.val (Phi.symm_apply_apply zQ)
    rw [← hz]
    exact hc
  have hfront : Filter.Tendsto (fun a : WQ => (a : Y.M))
      (nhds (Phi zQ)) (nhds y0) := by
    have hc : ContinuousAt (fun a : WQ => (a : Y.M)) (Phi zQ) :=
      continuous_subtype_val.continuousAt
    with_unfolding_all
      exact hc
  have hEq :
      (fun a : WQ =>
        DifferentialGeometry.Geometry.Curvature.restrictOpenTangentSection (I := I) WQ Zext a) =ᶠ[
        nhds (Phi zQ)]
      (fun a : WQ =>
        DifferentialGeometry.Geometry.Curvature.pushFwdSectionCross
          (I := 𝓘(Real, E)) (J := I) Phi
          (DifferentialGeometry.Geometry.Curvature.restrictOpenTangentSection
            (I := 𝓘(Real, E)) UQ Vext) a) := by
    filter_upwards [hfront.eventually hZext, hback.eventually hVext,
      hback.eventually (hUopen.mem_nhds hzU)] with a haZ haV haU
    let u : UQ := Phi.symm a
    have hau : Phi u = a := Phi.apply_symm_apply a
    rw [← hau] at haZ ⊢
    simp only [DifferentialGeometry.Geometry.Curvature.restrictOpenTangentSection_apply,
      DifferentialGeometry.Geometry.Curvature.pushFwdSectionCross_apply_at_image]
    rw [haZ, haV]
    have hInv := htransport.2.2 (((u : E), xi)) haU
    have hfst := symm_fst_eq (I := I) Y hcomplete hconn x he hf haU
    have hInv' : B.inv (normalPair (I := I) Y x ((u : E), xi)) =
        normalTangent (I := I) Y x ((u : E), (e.symm ((u : E), xi)).2) := by
      rw [hInv]
      congr 1
      exact Prod.ext hfst rfl
    change (B.inv (normalPair (I := I) Y x ((u : E), xi))).snd =
      mfderiv 𝓘(Real, E) I (Phi : UQ → WQ) u (Vloc (u : E))
    rw [hInv']
    change mfderiv 𝓘(Real, E) I
        (fun a : E => expMapDiffeo (I := I) Y.metric x a) (u : E)
        (Vloc (u : E)) = _
    exact (quarterDiffeo_mfd (I := I) Y x u (Vloc (u : E))).symm
  have hmap := normal_cov_map (I := I) Y x Vext Zext zQ v hEq
  have hVlocAt : MDifferentiableAt 𝓘(Real, E)
      (𝓘(Real, E).prod 𝓘(Real, E)) (T% VTan) z :=
    (hVsec.contMDiffAt (hUopen.mem_nhds hzU)).mdifferentiableAt (by simp)
  have hVextAt : MDifferentiableAt 𝓘(Real, E)
      (𝓘(Real, E).prod 𝓘(Real, E))
      (T% fun u : E => Vext u) z :=
    Vext.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hsrc := DifferentialGeometry.Geometry.Curvature.metricCov_congr_nhds
    (I := 𝓘(Real, E)) (M := E) (normalTotal (I := I) Y x)
    hVextAt hVlocAt hVext
  have hZlocAt : MDifferentiableAt I I.tangent
      (T% Zloc) y0 :=
    (hZsec.contMDiffAt (hSopen.mem_nhds hyS)).mdifferentiableAt (by simp)
  have hZextAt : MDifferentiableAt I I.tangent
      (T% fun y : Y.M => Zext y) y0 :=
    Zext.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have htgt := DifferentialGeometry.Geometry.Curvature.metricCov_congr_nhds
    (I := I) (M := Y.M) Y.metric hZextAt hZlocAt hZext
  rw [hsrc, htgt] at hmap
  with_unfolding_all
    exact hmap

theorem hess_inv_coord
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hb : NormalCoordMetricBounds (I := I) X) (k : Nat)
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (hconn : letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (x : (X.obj k).M) {q : NNReal} {δ ρ : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q)
    (he : IsNormalDiag (I := I) (X.obj k) hcomplete hconn x q δ e)
    (hf : NormalDiagFence (I := I) (X.obj k) x q e)
    {z xi : E} (hw : (z, xi) ∈ e.target)
    (hzQ : z ∈ normalQuarter (I := I) (X.obj k) x)
    (v w : E) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : IsManifold I 1 (X.obj k).M := IsManifold.of_le
      (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : ConnectedSpace (X.obj k).M := hconn
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
      Manifold.metrizableSpace I (X.obj k).M
    letI : T3Space (X.obj k).M := inferInstance
    letI : RiemannianBundle
        (fun y : (X.obj k).M => TangentSpace I y) :=
      (X.obj k).riemBundle (I := I)
    letI : (y : (X.obj k).M) → InnerProductSpace Real (TangentSpace I y) :=
      (X.obj k).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : (X.obj k).M => TangentSpace I y) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
    letI : CompleteSpace (X.obj k).M :=
      MetricComplete.complete (I := I) (X.obj k) hcomplete
    letI : MetricSpace (X.obj k).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj k).M)
    let dExp := mfderiv 𝓘(Real, E) I
      (fun u : E => expMapDiffeo (I := I) (X.obj k).metric x u) z
    0 < ρ →
    2 * ρ < (q : Real) →
    ρ ≤ hb.radius k x →
    ρ / 2 ≤ metricCoerciveExpRadius (I := I) (X.obj k).metric x →
    max
      (riemannianEDist I x
        (expMapDiffeo (I := I) (X.obj k).metric x z))
      (riemannianEDist I x
        (expMapDiffeo (I := I) (X.obj k).metric x xi)) <
        ENNReal.ofReal (ρ / 2) →
    hessFun (I := I) (X.obj k).metric
        (CenterOfMass.halfSqDist
          (expMapDiffeo (I := I) (X.obj k).metric x xi))
        (expMapDiffeo (I := I) (X.obj k).metric x z)
        (dExp v) (dExp w) =
      -normalCoordMetric (I := I) (X.obj k) x z
        ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z)
          (((DifferentialGeometry.Geometry.Curvature.metricCov
            (I := 𝓘(Real, E)) (M := E)
            (normalTotal (I := I) (X.obj k) x)).toFun
            (fun u : E => (tangentSpaceModelContinuousLinearEquiv
              (I := 𝓘(Real, E)) u).symm (e.symm (u, xi)).2) z)
            ((tangentSpaceModelContinuousLinearEquiv
              (I := 𝓘(Real, E)) z).symm v))) w := by
  classical
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : IsManifold I 1 (X.obj k).M := IsManifold.of_le
    (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  let : T2Space (X.obj k).M := (X.obj k).t2
  let : ConnectedSpace (X.obj k).M := hconn
  let : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  let : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  let : T3Space (X.obj k).M := inferInstance
  let : RiemannianBundle
      (fun y : (X.obj k).M => TangentSpace I y) :=
    (X.obj k).riemBundle (I := I)
  let : (y : (X.obj k).M) → InnerProductSpace Real (TangentSpace I y) :=
    (X.obj k).riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : (X.obj k).M => TangentSpace I y) :=
    (X.obj k).riemBundle_cont (I := I)
  let : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
  let : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) hcomplete
  let : MetricSpace (X.obj k).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj k).M)
  dsimp only
  intro hρ hρq hρmetric hρexp hpairs
  let B := toBranch (I := I) (X.obj k) hcomplete hconn x hq he
  let pt : (X.obj k).M :=
    expMapDiffeo (I := I) (X.obj k).metric x xi
  let y0 : (X.obj k).M :=
    expMapDiffeo (I := I) (X.obj k).metric x z
  let dExp := mfderiv 𝓘(Real, E) I
    (fun u : E => expMapDiffeo (I := I) (X.obj k).metric x u) z
  let Vloc : (u : E) → TangentSpace 𝓘(Real, E) u := fun u =>
    show TangentSpace 𝓘(Real, E) u from (e.symm (u, xi)).2
  let K : E :=
    ((DifferentialGeometry.Geometry.Curvature.metricCov
      (I := 𝓘(Real, E)) (M := E)
      (normalTotal (I := I) (X.obj k) x)).toFun Vloc z) v
  let Z : (y : (X.obj k).M) → TangentSpace I y := fun y =>
    show TangentSpace I y from (B.inv (y, pt)).snd
  let S : Set (X.obj k).M :=
    {y | max (riemannianEDist I x y) (riemannianEDist I x pt) <
      ENNReal.ofReal (ρ / 2)}
  have hSopen : IsOpen S := by
    dsimp only [S]
    exact isOpen_lt
      ((continuous_riemannianEDist (I := I) (X.obj k).metric x).max
        continuous_const) continuous_const
  have hyS : y0 ∈ S := by
    with_unfolding_all
      exact hpairs
  have hdom : ∀ y ∈ S, (y, pt) ∈ B.dom := by
    intro y hy
    exact (inv_is_min (I := I) hb k hcomplete hconn x hq he hf
      hρ hρq hρmetric hρexp (by
        with_unfolding_all
          exact hy)).choose_spec.1
  have hZat : MDifferentiableAt I I.tangent (T% Z) y0 :=
    ((B.inv_vector_contMDiffOn_at_fixed_target hdom).contMDiffAt (hSopen.mem_nhds hyS)).mdifferentiableAt
      (by simp)
  have hneg :
      (LeviCivita (I := I) (X.obj k).metric).toFun
          (fun y => -Z y) y0 (dExp v) =
        -(LeviCivita (I := I) (X.obj k).metric).toFun Z y0 (dExp v) := by
    have hsmul :=
      (LeviCivita (I := I) (X.obj k).metric).isCovariantDerivativeOnUniv.smul_const
        (-1 : Real) hZat
    have happ := congrArg (fun A => A (dExp v)) hsmul
    have hZneg : (-1 : Real) • Z = fun y => -Z y := by
      funext y
      simp
    rw [← hZneg]
    simpa using happ
  have hhess := hess_half_inv (I := I) hb k hcomplete hconn x hq he hf
    (dExp v) (dExp w) hρ hρq hρmetric hρexp hpairs
  have hcov := inv_cov_coord (I := I) (X.obj k) hcomplete hconn x
    hq he hf hw hzQ v
  have hcov' :
      (LeviCivita (I := I) (X.obj k).metric).toFun Z y0 (dExp v) =
        dExp K := by
    with_unfolding_all
      exact hcov.symm
  have hmain :
    hessFun (I := I) (X.obj k).metric
        (CenterOfMass.halfSqDist pt) y0 (dExp v) (dExp w) =
      -normalCoordMetric (I := I) (X.obj k) x z K w := by
    calc
      hessFun (I := I) (X.obj k).metric
          (CenterOfMass.halfSqDist pt) y0 (dExp v) (dExp w) =
        (X.obj k).metric.inner y0
          ((LeviCivita (I := I) (X.obj k).metric).toFun
            (fun y => -Z y) y0 (dExp v)) (dExp w) := by
              simpa only [B, Z, y0, pt] using hhess
      _ = (X.obj k).metric.inner y0
          (-(LeviCivita (I := I) (X.obj k).metric).toFun
            Z y0 (dExp v)) (dExp w) := by rw [hneg]
      _ = -((X.obj k).metric.inner y0
          ((LeviCivita (I := I) (X.obj k).metric).toFun
            Z y0 (dExp v)) (dExp w)) := by
              rw [ContinuousLinearMap.map_neg, neg_apply]
      _ = -((X.obj k).metric.inner y0 (dExp K) (dExp w)) := by
              rw [hcov']
      _ = -normalCoordMetric (I := I) (X.obj k) x z K w := by
              rw [normal_coord_metric_apply (I := I)]
  with_unfolding_all
    exact hmain

theorem inv_cov_expand
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hb : NormalCoordMetricBounds (I := I) X) (k : Nat)
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (hconn : letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (x : (X.obj k).M) {q : NNReal} {δ : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (he : IsNormalDiag (I := I) (X.obj k) hcomplete hconn x q δ e)
    {z xi : E} (hw : (z, xi) ∈ e.target)
    (hzQ : z ∈ normalQuarter (I := I) (X.obj k) x)
    (hzMetric : z ∈ Metric.ball (0 : E) (hb.radius k x)) (v : E) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z)
        (((DifferentialGeometry.Geometry.Curvature.metricCov
          (I := 𝓘(Real, E)) (M := E)
          (normalTotal (I := I) (X.obj k) x)).toFun
          (fun u : E => (tangentSpaceModelContinuousLinearEquiv
            (I := 𝓘(Real, E)) u).symm (e.symm (u, xi)).2) z)
          ((tangentSpaceModelContinuousLinearEquiv
            (I := 𝓘(Real, E)) z).symm v)) =
      fderiv Real (fun u : E => (e.symm (u, xi)).2) z v +
        MetricKoszul.koszulVec
          ((hb.metric_equiv k x).coercive hzMetric)
          (fderiv Real (normalCoordMetric (I := I) (X.obj k) x) z)
          v (e.symm (z, xi)).2 := by
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  let : T2Space (X.obj k).M := (X.obj k).t2
  let : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  let : RiemannianBundle
      (fun y : (X.obj k).M => TangentSpace I y) :=
    (X.obj k).riemBundle (I := I)
  let : (y : (X.obj k).M) → InnerProductSpace Real (TangentSpace I y) :=
    (X.obj k).riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : (X.obj k).M => TangentSpace I y) :=
    (X.obj k).riemBundle_cont (I := I)
  let : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
  let : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) hcomplete
  let V : E → E := fun u => (e.symm (u, xi)).2
  let VTan : (u : E) → TangentSpace 𝓘(Real, E) u := fun u => V u
  have heData := he
  change e.source = Metric.ball (0 : E × E) q ∧
    e 0 = 0 ∧
    ContDiffOn Real ∞ (e : E × E → E × E) e.source ∧
    Metric.closedBall (0 : E × E) δ ⊆ e.target ∧
    ContDiffOn Real ∞ e.symm e.target ∧
    ∀ a ∈ Metric.closedBall (0 : E × E) q,
      normalPair (I := I) (X.obj k) x (e a) =
        diagExp (I := I) (X.obj k).metric
          (normal_enorm (I := I) (X.obj k))
          (normalTangent (I := I) (X.obj k) x a) at heData
  have hInvAt : ContDiffAt Real ∞ (e.symm : E × E → E × E) (z, xi) :=
    (heData.2.2.2.2.1 (z, xi) hw).contDiffAt
      (e.open_target.mem_nhds hw)
  have hpair : ContDiffAt Real ∞ (fun u : E => (u, xi)) z :=
    (contDiff_id.prodMk contDiff_const).contDiffAt
  have hVcd : ContDiffAt Real ∞ V z := by
    with_unfolding_all
      exact (hInvAt.comp z hpair).snd
  have hVmd : MDifferentiableAt 𝓘(Real, E)
      (𝓘(Real, E).prod 𝓘(Real, E)) (T% VTan) z :=
    (contMDiffAt_vectorSpace_iff_contDiffAt.mpr
      (by simpa only [VTan] using hVcd)).mdifferentiableAt (by simp)
  have hzQuarter : z ∈ Metric.ball (0 : E)
      (expMapC2Radius (I := I) (X.obj k).metric x / 4) := by
    exact hzQ
  have hcov := normal_cov_eq_fderiv (I := I) (X.obj k) x z hzQuarter
    ((hb.metric_equiv k x).coercive hzMetric) V hVmd v
  simpa only [V, VTan, DifferentialGeometry.Geometry.Curvature.metricCov] using hcov

theorem hess_inv_lower
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hb : NormalCoordMetricBounds (I := I) X) (k : Nat)
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (hconn : letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (x : (X.obj k).M) {q eta : NNReal} {δ ρ : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q)
    (he : IsNormalDiag (I := I) (X.obj k) hcomplete hconn x q δ e)
    (hf : NormalDiagFence (I := I) (X.obj k) x q e)
    (happrox : ApproximatesLinearOn (e.symm : E × E → E × E)
      ((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E)) e.target eta)
    {z xi : E} (hw : (z, xi) ∈ e.target)
    (hzQ : z ∈ normalQuarter (I := I) (X.obj k) x)
    (hzMetric : z ∈ Metric.ball (0 : E) (hb.radius k x)) (v : E) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : IsManifold I 1 (X.obj k).M := IsManifold.of_le
      (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : ConnectedSpace (X.obj k).M := hconn
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
      Manifold.metrizableSpace I (X.obj k).M
    letI : T3Space (X.obj k).M := inferInstance
    letI : RiemannianBundle
        (fun y : (X.obj k).M ↦ TangentSpace I y) :=
      (X.obj k).riemBundle (I := I)
    letI : (y : (X.obj k).M) → InnerProductSpace Real (TangentSpace I y) :=
      (X.obj k).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : (X.obj k).M ↦ TangentSpace I y) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
    letI : CompleteSpace (X.obj k).M :=
      MetricComplete.complete (I := I) (X.obj k) hcomplete
    letI : MetricSpace (X.obj k).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj k).M)
    let dExp := mfderiv 𝓘(Real, E) I
      (fun u : E ↦ expMapDiffeo (I := I) (X.obj k).metric x u) z
    0 < ρ →
    2 * ρ < (q : Real) →
    ρ ≤ hb.radius k x →
    ρ / 2 ≤ metricCoerciveExpRadius (I := I) (X.obj k).metric x →
    max
      (riemannianEDist I x
        (expMapDiffeo (I := I) (X.obj k).metric x z))
      (riemannianEDist I x
        (expMapDiffeo (I := I) (X.obj k).metric x xi)) <
        ENNReal.ofReal (ρ / 2) →
    (1 - 4 * (eta : Real) -
        12 * hb.metricC 1 * (q : Real)) *
        normalCoordMetric (I := I) (X.obj k) x z v v ≤
      hessFun (I := I) (X.obj k).metric
        (CenterOfMass.halfSqDist
          (expMapDiffeo (I := I) (X.obj k).metric x xi))
        (expMapDiffeo (I := I) (X.obj k).metric x z)
        (dExp v) (dExp v) := by
  classical
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : IsManifold I 1 (X.obj k).M := IsManifold.of_le
    (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  let : T2Space (X.obj k).M := (X.obj k).t2
  let : ConnectedSpace (X.obj k).M := hconn
  let : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  let : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  let : T3Space (X.obj k).M := inferInstance
  let : RiemannianBundle
      (fun y : (X.obj k).M ↦ TangentSpace I y) :=
    (X.obj k).riemBundle (I := I)
  let : (y : (X.obj k).M) → InnerProductSpace Real (TangentSpace I y) :=
    (X.obj k).riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : (X.obj k).M ↦ TangentSpace I y) :=
    (X.obj k).riemBundle_cont (I := I)
  let : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
  let : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) hcomplete
  let : MetricSpace (X.obj k).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj k).M)
  dsimp only
  intro hρ hρq hρmetric hρexp hpairs
  let V : E → E := fun u ↦ (e.symm (u, xi)).2
  let A : E →L[Real] E := fderiv Real V z
  let K : E := MetricKoszul.koszulVec
    ((hb.metric_equiv k x).coercive hzMetric)
    (fderiv Real (normalCoordMetric (I := I) (X.obj k) x) z)
    v (e.symm (z, xi)).2
  let g : E →L[Real] E →L[Real] Real :=
    normalCoordMetric (I := I) (X.obj k) x z
  have heData := he
  change e.source = Metric.ball (0 : E × E) q ∧
    e 0 = 0 ∧
    ContDiffOn Real ∞ (e : E × E → E × E) e.source ∧
    Metric.closedBall (0 : E × E) δ ⊆ e.target ∧
    ContDiffOn Real ∞ e.symm e.target ∧
    ∀ a ∈ Metric.closedBall (0 : E × E) q,
      normalPair (I := I) (X.obj k) x (e a) =
        diagExp (I := I) (X.obj k).metric
          (normal_enorm (I := I) (X.obj k))
          (normalTangent (I := I) (X.obj k) x a) at heData
  have hInvDiff : DifferentiableAt Real
      (e.symm : E × E → E × E) (z, xi) :=
    ((heData.2.2.2.2.1 (z, xi) hw).contDiffAt
      (e.open_target.mem_nhds hw)).differentiableAt (by simp)
  have hAop : ‖A + ContinuousLinearMap.id Real E‖ ≤ (eta : Real) := by
    simpa only [A, V] using PhaseFlow.invVelocity_fderiv_le happrox
      (e.open_target.mem_nhds hw) hInvDiff
  have hAeval :
      ‖(A + ContinuousLinearMap.id Real E) v‖ ≤ (eta : Real) * ‖v‖ :=
    (A + ContinuousLinearMap.id Real E).le_opNorm v |>.trans
      (mul_le_mul_of_nonneg_right hAop (norm_nonneg v))
  have hpre : e.symm (z, xi) ∈ Metric.ball (0 : E × E) q := by
    rw [← heData.1]
    exact e.map_target hw
  have hpreNorm : ‖e.symm (z, xi)‖ < (q : Real) := by
    simpa only [Metric.mem_ball, dist_zero_right] using hpre
  have hVnorm : ‖(e.symm (z, xi)).2‖ ≤ (q : Real) :=
    (norm_snd_le (e.symm (z, xi))).trans hpreNorm.le
  have hKnorm : ‖K‖ ≤ 3 * hb.metricC 1 * ‖v‖ * (q : Real) := by
    with_unfolding_all
      refine (hb.koszul_vec_norm_le k x hzMetric v
        (e.symm (z, xi)).2).trans ?_
    exact mul_le_mul_of_nonneg_left hVnorm
      (mul_nonneg
        (mul_nonneg (by norm_num) (hb.metricC_nonneg 1)) (norm_nonneg v))
  have hquad := hb.metric_equiv k x z hzMetric v
  have hg0 : 0 ≤ g v v := by
    dsimp only [g]
    exact (mul_nonneg (by norm_num) (sq_nonneg ‖v‖)).trans hquad.1
  have hvSq : ‖v‖ ^ 2 ≤ 2 * g v v := by
    dsimp only [g]
    nlinarith [hquad.1]
  have hAabs :
      |g ((A + ContinuousLinearMap.id Real E) v) v| ≤
        4 * (eta : Real) * g v v := by
    calc
      |g ((A + ContinuousLinearMap.id Real E) v) v| ≤
          2 * ‖(A + ContinuousLinearMap.id Real E) v‖ * ‖v‖ := by
            dsimp only [g]
            exact NormalCoordMetricEquivOn.abs_apply_le
              (hb.metric_equiv k x) hzMetric _ _
      _ ≤ 2 * ((eta : Real) * ‖v‖) * ‖v‖ := by
        gcongr
      _ ≤ 4 * (eta : Real) * g v v := by
        have heta0 : 0 ≤ (eta : Real) := NNReal.coe_nonneg eta
        nlinarith
  have hKabs : |g K v| ≤ 12 * hb.metricC 1 * (q : Real) * g v v := by
    calc
      |g K v| ≤ 2 * ‖K‖ * ‖v‖ := by
        dsimp only [g]
        exact NormalCoordMetricEquivOn.abs_apply_le
          (hb.metric_equiv k x) hzMetric _ _
      _ ≤ 2 * (3 * hb.metricC 1 * ‖v‖ * (q : Real)) * ‖v‖ := by
        gcongr
      _ ≤ 12 * hb.metricC 1 * (q : Real) * g v v := by
        have hC0 := hb.metricC_nonneg 1
        have hq0 : 0 ≤ (q : Real) := NNReal.coe_nonneg q
        calc
          2 * (3 * hb.metricC 1 * ‖v‖ * (q : Real)) * ‖v‖ =
              6 * hb.metricC 1 * (q : Real) * ‖v‖ ^ 2 := by ring
          _ ≤ 6 * hb.metricC 1 * (q : Real) * (2 * g v v) := by
            gcongr
          _ = 12 * hb.metricC 1 * (q : Real) * g v v := by ring
  have hdecomp :
      -g (A v + K) v =
        g v v - g ((A + ContinuousLinearMap.id Real E) v) v - g K v := by
    have hAg : g (A v) v =
        g ((A + ContinuousLinearMap.id Real E) v) v - g v v := by
      have hsum : (A + ContinuousLinearMap.id Real E) v = A v + v := by
        simp only [add_apply, ContinuousLinearMap.id_apply]
      rw [hsum, map_add, add_apply]
      ring
    calc
      -g (A v + K) v = -(g (A v) v + g K v) := by
        rw [map_add, add_apply]
      _ = -(g ((A + ContinuousLinearMap.id Real E) v) v -
          g v v + g K v) := by rw [hAg]
      _ = g v v - g ((A + ContinuousLinearMap.id Real E) v) v -
          g K v := by ring
  have hhess := hess_inv_coord (I := I) hb k hcomplete hconn x hq he hf
    hw hzQ v v hρ hρq hρmetric hρexp hpairs
  have hcov := inv_cov_expand (I := I) hb k hcomplete hconn x he hw hzQ
    hzMetric v
  have hhess' :
      hessFun (I := I) (X.obj k).metric
          (CenterOfMass.halfSqDist
            (expMapDiffeo (I := I) (X.obj k).metric x xi))
          (expMapDiffeo (I := I) (X.obj k).metric x z)
          (mfderiv 𝓘(Real, E) I
            (fun u : E ↦ expMapDiffeo (I := I) (X.obj k).metric x u) z v)
          (mfderiv 𝓘(Real, E) I
            (fun u : E ↦ expMapDiffeo (I := I) (X.obj k).metric x u) z v) =
        -g (A v + K) v := by
    rw [hhess, hcov]
  rw [hhess', hdecomp]
  have hAupper : g ((A + ContinuousLinearMap.id Real E) v) v ≤
      4 * (eta : Real) * g v v := (le_abs_self _).trans hAabs
  have hKupper : g K v ≤
      12 * hb.metricC 1 * (q : Real) * g v v :=
    (le_abs_self _).trans hKabs
  nlinarith

theorem hess_inv_sixth
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hb : NormalCoordMetricBounds (I := I) X) (k : Nat)
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (hconn : letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (x : (X.obj k).M) {q eta : NNReal} {δ ρ : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q)
    (he : IsNormalDiag (I := I) (X.obj k) hcomplete hconn x q δ e)
    (hf : NormalDiagFence (I := I) (X.obj k) x q e)
    (happrox : ApproximatesLinearOn (e.symm : E × E → E × E)
      ((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E)) e.target eta)
    (heta : eta < (1 / 24 : NNReal))
    (hqAcc : 3 * hb.metricC 1 * (2 * (q : Real)) ^ 2 ≤
      (2 / 3 : Real) * (q : Real))
    {z xi : E} (hw : (z, xi) ∈ e.target)
    (hzQ : z ∈ normalQuarter (I := I) (X.obj k) x)
    (hzMetric : z ∈ Metric.ball (0 : E) (hb.radius k x)) (v : E) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : IsManifold I 1 (X.obj k).M := IsManifold.of_le
      (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : ConnectedSpace (X.obj k).M := hconn
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
      Manifold.metrizableSpace I (X.obj k).M
    letI : T3Space (X.obj k).M := inferInstance
    letI : RiemannianBundle
        (fun y : (X.obj k).M ↦ TangentSpace I y) :=
      (X.obj k).riemBundle (I := I)
    letI : (y : (X.obj k).M) → InnerProductSpace Real (TangentSpace I y) :=
      (X.obj k).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : (X.obj k).M ↦ TangentSpace I y) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
    letI : CompleteSpace (X.obj k).M :=
      MetricComplete.complete (I := I) (X.obj k) hcomplete
    letI : MetricSpace (X.obj k).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj k).M)
    let dExp := mfderiv 𝓘(Real, E) I
      (fun u : E ↦ expMapDiffeo (I := I) (X.obj k).metric x u) z
    0 < ρ →
    2 * ρ < (q : Real) →
    ρ ≤ hb.radius k x →
    ρ / 2 ≤ metricCoerciveExpRadius (I := I) (X.obj k).metric x →
    max
      (riemannianEDist I x
        (expMapDiffeo (I := I) (X.obj k).metric x z))
      (riemannianEDist I x
        (expMapDiffeo (I := I) (X.obj k).metric x xi)) <
        ENNReal.ofReal (ρ / 2) →
    (1 / 6 : Real) *
        normalCoordMetric (I := I) (X.obj k) x z v v ≤
      hessFun (I := I) (X.obj k).metric
        (CenterOfMass.halfSqDist
          (expMapDiffeo (I := I) (X.obj k).metric x xi))
        (expMapDiffeo (I := I) (X.obj k).metric x z)
        (dExp v) (dExp v) := by
  classical
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : IsManifold I 1 (X.obj k).M := IsManifold.of_le
    (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  let : T2Space (X.obj k).M := (X.obj k).t2
  let : ConnectedSpace (X.obj k).M := hconn
  let : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  let : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  let : T3Space (X.obj k).M := inferInstance
  let : RiemannianBundle
      (fun y : (X.obj k).M ↦ TangentSpace I y) :=
    (X.obj k).riemBundle (I := I)
  let : (y : (X.obj k).M) → InnerProductSpace Real (TangentSpace I y) :=
    (X.obj k).riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : (X.obj k).M ↦ TangentSpace I y) :=
    (X.obj k).riemBundle_cont (I := I)
  let : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
  let : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) hcomplete
  let : MetricSpace (X.obj k).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj k).M)
  dsimp only
  intro hρ hρq hρmetric hρexp hpairs
  have hlower := hess_inv_lower (I := I) hb k hcomplete hconn x hq he hf
    happrox hw hzQ hzMetric v hρ hρq hρmetric hρexp hpairs
  have hqReal : 0 < (q : Real) := by exact_mod_cast hq
  have hqCoef : 12 * hb.metricC 1 * (q : Real) ≤ (2 / 3 : Real) := by
    refine le_of_mul_le_mul_right ?_ hqReal
    nlinarith [hqAcc]
  have hetaReal : (eta : Real) < (1 / 24 : Real) := by
    exact_mod_cast heta
  have hcoef : (1 / 6 : Real) ≤
      1 - 4 * (eta : Real) - 12 * hb.metricC 1 * (q : Real) := by
    nlinarith
  have hquad := hb.metric_equiv k x z hzMetric v
  have hg0 : 0 ≤ normalCoordMetric (I := I) (X.obj k) x z v v :=
    (mul_nonneg (by norm_num) (sq_nonneg ‖v‖)).trans hquad.1
  exact (mul_le_mul_of_nonneg_right hcoef hg0).trans hlower

omit [CompleteSpace E] in
theorem chartCenterOfMassEquation_factor
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) {c : NormalChartAt (I := I) Y x}
    {q : NNReal} {delta : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q)
    (he : IsNormalDiag (I := I) Y hcomplete hconn x q delta e (c := c))
    (hf : NormalDiagFence (I := I) Y x q e (c := c))
    {ι : Type} [Fintype ι] (z : E) (mu : ι → Real) (xi : ι → E)
    (htgt : ∀ i, (z, xi i) ∈ e.target) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : ConnectedSpace Y.M := hconn
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M :=
      Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
      (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    chartCenterOfMassEquation (I := I) Y.metric (normal_enorm (I := I) Y) x c
        (IsNormalDiag.toBranch (I := I) Y hcomplete hconn x hq he)
        z (mu, xi) =
      invVelocitySum e mu xi z := by
  classical
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : ConnectedSpace Y.M := hconn
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
    (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  unfold chartCenterOfMassEquation invVelocitySum
  apply Finset.sum_congr rfl
  intro i _hi
  congr 1
  change
    (IsNormalDiag.toBranch (I := I) Y hcomplete hconn x hq he).chartDiagonalInverseCoordinates c
        (normalPair (I := I) Y x (z, xi i) (c := c)) =
      (e.symm (z, xi i)).2
  exact IsNormalDiag.chartDiagonalInverseCoordinates_normalPair (I := I) Y hcomplete hconn x
    hq he hf (htgt i)

omit [CompleteSpace E] in
theorem chartCenterOfMassEquation_zero_iff
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) {c : NormalChartAt (I := I) Y x}
    {q : NNReal} {delta : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q)
    (he : IsNormalDiag (I := I) Y hcomplete hconn x q delta e (c := c))
    (hf : NormalDiagFence (I := I) Y x q e (c := c))
    {ι : Type} [Fintype ι] (z : E) (mu : ι → Real) (xi : ι → E)
    (htgt : ∀ i, (z, xi i) ∈ e.target) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : ConnectedSpace Y.M := hconn
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M :=
      Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
      (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    (chartCenterOfMassEquation (I := I) Y.metric (normal_enorm (I := I) Y) x c
        (IsNormalDiag.toBranch (I := I) Y hcomplete hconn x hq he)
        z (mu, xi) = 0 ↔
      invVelocitySum e mu xi z = 0) := by
  rw [chartCenterOfMassEquation_factor (I := I) Y hcomplete hconn x
    hq he hf z mu xi htgt]

omit [CompleteSpace E] in
theorem HasCenterOfMassChartSolution.target_mem
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) {c : NormalChartAt (I := I) Y x}
    {q : NNReal} {delta : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q)
    (he : IsNormalDiag (I := I) Y hcomplete hconn x q delta e (c := c))
    {ι : Type} [Fintype ι] (z : E) (mu : ι → Real) (xi : ι → E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : ConnectedSpace Y.M := hconn
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M :=
      Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : Y.M ↦ TangentSpace I y) :=
      Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    HasCenterOfMassChartSolution (I := I) Y.metric (normal_enorm (I := I) Y) x c
        (IsNormalDiag.toBranch (I := I) Y hcomplete hconn x hq he)
        z (mu, xi) →
      ∀ i, (z, xi i) ∈ e.target := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : ConnectedSpace Y.M := hconn
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : Y.M ↦ TangentSpace I y) :=
    Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  intro hsol
  rcases hsol with ⟨hzBall, hxiBall, hdom, _hzero, _hstrict⟩
  have hzTarget : c.hom z ∈ c.restrictBall.target := by
    have hmap := c.restrictBall.map_source hzBall
    change c.hom z ∈ c.restrictBall.target at hmap
    exact hmap
  have hxiTarget (i : ι) : c.hom (xi i) ∈ c.restrictBall.target := by
    have hmap := c.restrictBall.map_source (hxiBall i)
    change c.hom (xi i) ∈ c.restrictBall.target at hmap
    exact hmap
  intro i
  have hout := IsNormalDiag.target_of_inv_dom (I := I) Y hcomplete hconn x
    hq he hzTarget (hxiTarget i) (hdom i).1
  have hzDecode : c.inv (c.hom z) = z :=
    c.hom.left_inv (c.ball_subset hzBall)
  have hxiDecode : c.inv (c.hom (xi i)) = xi i :=
    c.hom.left_inv (c.ball_subset (hxiBall i))
  rwa [hzDecode, hxiDecode] at hout

omit [CompleteSpace E] in
theorem HasCenterOfMassChartSolution.invVelocity_zero
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) {c : NormalChartAt (I := I) Y x}
    {q : NNReal} {delta : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q)
    (he : IsNormalDiag (I := I) Y hcomplete hconn x q delta e (c := c))
    (hf : NormalDiagFence (I := I) Y x q e (c := c))
    {ι : Type} [Fintype ι] (z : E) (mu : ι → Real) (xi : ι → E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : ConnectedSpace Y.M := hconn
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M :=
      Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : Y.M ↦ TangentSpace I y) :=
      Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    HasCenterOfMassChartSolution (I := I) Y.metric (normal_enorm (I := I) Y) x c
        (IsNormalDiag.toBranch (I := I) Y hcomplete hconn x hq he)
        z (mu, xi) →
      invVelocitySum e mu xi z = 0 := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : ConnectedSpace Y.M := hconn
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : Y.M ↦ TangentSpace I y) :=
    Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  intro hsol
  have htgt := HasCenterOfMassChartSolution.target_mem (I := I) Y hcomplete hconn x
    hq he z mu xi hsol
  exact (IsNormalDiag.chartCenterOfMassEquation_zero_iff (I := I) Y hcomplete hconn x
    hq he hf z mu xi htgt).mp hsol.2.2.2.1

theorem chartCenterOfMassEquation_has_invertible_derivative
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) {c : NormalChartAt (I := I) Y x}
    {q : NNReal} {delta : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q)
    (he : IsNormalDiag (I := I) Y hcomplete hconn x q delta e (c := c))
    (hf : NormalDiagFence (I := I) Y x q e (c := c))
    {eta : NNReal}
    (happrox : ApproximatesLinearOn (e.symm : E × E → E × E)
      ((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E)) e.target eta)
    (heta : eta < 1)
    {ι : Type} [Fintype ι] (z : E) (mu : ι → Real) (xi : ι → E)
    (htgt : ∀ i, (z, xi i) ∈ e.target)
    (hmu : ∀ i, 0 ≤ mu i) (hsum : ∑ i, mu i = 1) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : ConnectedSpace Y.M := hconn
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M :=
      Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
      (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    ∃ L : E ≃L[Real] E,
      HasFDerivAt
        (fun u : E =>
          chartCenterOfMassEquation (I := I) Y.metric (normal_enorm (I := I) Y) x c
            (IsNormalDiag.toBranch (I := I) Y hcomplete hconn x hq he)
            u (mu, xi))
        (L : E →L[Real] E) z := by
  classical
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : ConnectedSpace Y.M := hconn
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
    (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  have heData := he
  change e.source = Metric.ball (0 : E × E) q ∧
    e 0 = 0 ∧
    ContDiffOn Real ∞ (e : E × E → E × E) e.source ∧
    Metric.closedBall (0 : E × E) delta ⊆ e.target ∧
    ContDiffOn Real ∞ e.symm e.target ∧
    ∀ a ∈ Metric.closedBall (0 : E × E) q,
      normalPair (I := I) Y x (e a) (c := c) =
        diagExp (I := I) Y.metric (normal_enorm (I := I) Y)
          (normalTangent (I := I) Y x a (c := c)) at heData
  have hinv : ContDiffOn Real ∞ (e.symm : E × E → E × E) e.target :=
    heData.2.2.2.2.1
  obtain ⟨L, hL⟩ :=
    invVelocitySum_inv e mu xi hinv htgt happrox hmu hsum heta
  have htgtNhd : ∀ i, ∀ᶠ u in nhds z, (u, xi i) ∈ e.target := by
    intro i
    have hpair : ContinuousAt (fun u : E => (u, xi i)) z := by fun_prop
    exact hpair.preimage_mem_nhds (e.open_target.mem_nhds (htgt i))
  have heq :
      (fun u : E =>
        chartCenterOfMassEquation (I := I) Y.metric (normal_enorm (I := I) Y) x c
          (IsNormalDiag.toBranch (I := I) Y hcomplete hconn x hq he)
          u (mu, xi)) =ᶠ[nhds z]
      invVelocitySum e mu xi := by
    filter_upwards [Filter.eventually_all.mpr htgtNhd] with u hu
    exact chartCenterOfMassEquation_factor (I := I) Y hcomplete hconn x
      hq he hf u mu xi hu
  exact ⟨L, hL.congr_of_eventuallyEq heq⟩

theorem chartCenterOfMassEquation_has_strict_solution
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) {c : NormalChartAt (I := I) Y x}
    {q : NNReal} {delta : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q)
    (he : IsNormalDiag (I := I) Y hcomplete hconn x q delta e (c := c))
    (hf : NormalDiagFence (I := I) Y x q e (c := c))
    {eta : NNReal}
    (happrox : ApproximatesLinearOn (e.symm : E × E → E × E)
      ((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E)) e.target eta)
    (heta : eta < 1)
    {ι : Type} [Fintype ι] (z : E) (mu : ι → Real) (xi : ι → E)
    (htgt : ∀ i, (z, xi i) ∈ e.target)
    (hmu : ∀ i, 0 ≤ mu i) (hsum : ∑ i, mu i = 1)
    (hdata :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : IsManifold I 1 Y.M := IsManifold.of_le
        (I := I) (M := Y.M) (n := ∞) (by decide)
      letI : SigmaCompactSpace Y.M := Y.sigmaCompact
      letI : T2Space Y.M := Y.t2
      letI : ConnectedSpace Y.M := hconn
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      letI : TopologicalSpace.MetrizableSpace Y.M :=
        Manifold.metrizableSpace I Y.M
      letI : T3Space Y.M := inferInstance
      letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
        Y.riemBundle (I := I)
      letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
        Y.riemInner (I := I)
      letI : IsContinuousRiemannianBundle E
        (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
      letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
      letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
      let B := IsNormalDiag.toBranch (I := I) Y hcomplete hconn x hq he
      z ∈ Metric.ball (0 : E) c.radius ∧
        (∀ i, xi i ∈ Metric.ball (0 : E) c.radius) ∧
        (∀ i, (c.hom z, c.hom (xi i)) ∈ B.chartCoordinateDomain c) ∧
        chartCenterOfMassEquation (I := I) Y.metric (normal_enorm (I := I) Y) x c
          B z (mu, xi) = 0) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : ConnectedSpace Y.M := hconn
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M :=
      Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
      (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    let B := IsNormalDiag.toBranch (I := I) Y hcomplete hconn x hq he
    ∃ L : E ≃L[Real] E,
      HasFDerivAt
          (fun u : E =>
            chartCenterOfMassEquation (I := I) Y.metric (normal_enorm (I := I) Y)
              x c B u (mu, xi))
          (L : E →L[Real] E) z ∧
        ∃ (f : ((ι → Real) × (ι → E)) → E)
            (Df : ((ι → Real) × (ι → E)) →L[Real] E),
          f (mu, xi) = z ∧ HasStrictFDerivAt f Df (mu, xi) ∧
            (∀ᶠ params in nhds (mu, xi),
              chartCenterOfMassEquation (I := I) Y.metric (normal_enorm (I := I) Y)
                x c B (f params) params = 0) ∧
            (∀ᶠ zp in nhds (z, (mu, xi)),
              chartCenterOfMassEquation (I := I) Y.metric (normal_enorm (I := I) Y)
                  x c B zp.1 zp.2 = 0 →
                zp.1 = f zp.2) := by
  classical
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : ConnectedSpace Y.M := hconn
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  let B := IsNormalDiag.toBranch (I := I) Y hcomplete hconn x hq he
  rcases hdata with ⟨hz, hxi, hdom, hzero⟩
  obtain ⟨L, hL⟩ := chartCenterOfMassEquation_has_invertible_derivative (I := I) Y hcomplete hconn x hq he hf
    happrox heta z mu xi htgt hmu hsum
  refine ⟨L, hL, ?_⟩
  exact chartCenterOfMassEquation_implicitFunction_hasStrictFDerivAt (I := I) Y.metric (normal_enorm (I := I) Y)
    x c B z (mu, xi) hz hxi hdom ⟨L, hL⟩ hzero

theorem chartCenterOfMassEquation_has_contDiff_solution
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) {c : NormalChartAt (I := I) Y x}
    {q : NNReal} {delta : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q)
    (he : IsNormalDiag (I := I) Y hcomplete hconn x q delta e (c := c))
    (hf : NormalDiagFence (I := I) Y x q e (c := c))
    {eta : NNReal}
    (happrox : ApproximatesLinearOn (e.symm : E × E → E × E)
      ((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E)) e.target eta)
    (heta : eta < 1)
    {ι : Type} [Fintype ι] (z : E) (mu : ι → Real) (xi : ι → E)
    (n : Nat) (hn : 1 ≤ n)
    (htgt : ∀ i, (z, xi i) ∈ e.target)
    (hmu : ∀ i, 0 ≤ mu i) (hsum : ∑ i, mu i = 1)
    (hdata :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : IsManifold I 1 Y.M := IsManifold.of_le
        (I := I) (M := Y.M) (n := ∞) (by decide)
      letI : SigmaCompactSpace Y.M := Y.sigmaCompact
      letI : T2Space Y.M := Y.t2
      letI : ConnectedSpace Y.M := hconn
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      letI : TopologicalSpace.MetrizableSpace Y.M :=
        Manifold.metrizableSpace I Y.M
      letI : T3Space Y.M := inferInstance
      letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
        Y.riemBundle (I := I)
      letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
        Y.riemInner (I := I)
      letI : IsContinuousRiemannianBundle E
        (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
      letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
      letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
      let B := IsNormalDiag.toBranch (I := I) Y hcomplete hconn x hq he
      z ∈ Metric.ball (0 : E) c.radius ∧
        (∀ i, xi i ∈ Metric.ball (0 : E) c.radius) ∧
        (∀ i, (c.hom z, c.hom (xi i)) ∈ B.chartCoordinateDomain c) ∧
        chartCenterOfMassEquation (I := I) Y.metric (normal_enorm (I := I) Y) x c
          B z (mu, xi) = 0) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : ConnectedSpace Y.M := hconn
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M :=
      Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
      (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    let B := IsNormalDiag.toBranch (I := I) Y hcomplete hconn x hq he
    ∃ f : ((ι → Real) × (ι → E)) → E,
      f (mu, xi) = z ∧ ContDiffAt Real (n : ℕ∞) f (mu, xi) ∧
        (∀ᶠ params in nhds (mu, xi),
          chartCenterOfMassEquation (I := I) Y.metric (normal_enorm (I := I) Y)
            x c B (f params) params = 0) ∧
        (∀ᶠ zp in nhds (z, (mu, xi)),
          chartCenterOfMassEquation (I := I) Y.metric (normal_enorm (I := I) Y)
              x c B zp.1 zp.2 = 0 →
            zp.1 = f zp.2) := by
  classical
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : ConnectedSpace Y.M := hconn
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  let B := IsNormalDiag.toBranch (I := I) Y hcomplete hconn x hq he
  rcases hdata with ⟨hz, hxi, hdom, hzero⟩
  obtain ⟨L, hL⟩ := chartCenterOfMassEquation_has_invertible_derivative (I := I) Y hcomplete hconn x hq he hf
    happrox heta z mu xi htgt hmu hsum
  exact chartCenterOfMassEquation_implicitFunction_contDiffAt (I := I) Y.metric (normal_enorm (I := I) Y)
    x c B z (mu, xi) n hn hz hxi hdom ⟨L, hL⟩ hzero
theorem normalChartCenterOfMassEquationWithBranch_factor
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) {q : NNReal} {delta : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q) (he : IsNormalDiag (I := I) Y hcomplete hconn x q delta e)
    (hf : NormalDiagFence (I := I) Y x q e)
    {ι : Type} [Fintype ι] (z : E) (mu : ι → Real) (xi : ι → E)
    (htgt : ∀ i, (z, xi i) ∈ e.target) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : ConnectedSpace Y.M := hconn
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M :=
      Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
      (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    normalChartCenterOfMassEquationWithBranch (I := I) Y.metric (normal_enorm (I := I) Y) x
        (toBranch (I := I) Y hcomplete hconn x hq he) z (mu, xi) =
      normalReadCLM (I := I) Y x z (invVelocitySum e mu xi z) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : ConnectedSpace Y.M := hconn
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
    (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  unfold normalChartCenterOfMassEquationWithBranch invVelocitySum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul]
  congr 1
  change (toBranch (I := I) Y hcomplete hconn x hq he).diagonalInverseCoordinates
      (normalPair (I := I) Y x (z, xi i)) =
    normalReadCLM (I := I) Y x z (e.symm (z, xi i)).2
  exact diagonalInverseCoordinates_normalPair_eq (I := I) Y hcomplete hconn x hq he hf (htgt i)

theorem normalChartCenterOfMass_zero_iff
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) {q : NNReal} {delta : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q) (he : IsNormalDiag (I := I) Y hcomplete hconn x q delta e)
    (hf : NormalDiagFence (I := I) Y x q e)
    {ι : Type} [Fintype ι] (z : E) (mu : ι → Real) (xi : ι → E)
    (htgt : ∀ i, (z, xi i) ∈ e.target)
    (hz : z ∈ normalBall (I := I) Y x) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : ConnectedSpace Y.M := hconn
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M :=
      Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
      (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    (normalChartCenterOfMassEquationWithBranch (I := I) Y.metric (normal_enorm (I := I) Y) x
        (toBranch (I := I) Y hcomplete hconn x hq he) z (mu, xi) = 0 ↔
      invVelocitySum e mu xi z = 0) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : ConnectedSpace Y.M := hconn
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
    (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  have hzNormLt : ‖z‖ < expMapC2Radius (I := I) Y.metric x := by
    have hz' := hz
    change z ∈ Metric.ball (0 : E)
      (expMapC2Radius (I := I) Y.metric x) at hz'
    rwa [Metric.mem_ball, dist_zero_right] at hz'
  have hzSource : z ∈ (expMapDiffeo (I := I) Y.metric x).source :=
    mem_expMapDiffeo_source_of_norm_lt_radius (I := I) Y.metric x hzNormLt
  have hbase : expMapDiffeo (I := I) Y.metric x z ∈
      (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact NormalCoordinates.exp_target_sub_chart (I := I) Y.metric x
      ((expMapDiffeo (I := I) Y.metric x).map_source hzSource)
  rw [normalChartCenterOfMassEquationWithBranch_factor (I := I) Y hcomplete hconn x hq he hf z mu xi htgt,
    ← normalReadCLE_coe (I := I) Y x hz hbase]
  exact (normalReadCLE (I := I) Y x hz hbase).map_eq_zero_iff

theorem chartCenterOfMassEquation_solution_of_inverse_velocity_sum
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) {q : NNReal} {delta : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q)
    (he : IsNormalDiag (I := I) Y hcomplete hconn x q delta e
      (c := c2RadiusNormalBallChart (I := I) Y x))
    (hf : NormalDiagFence (I := I) Y x q e
      (c := c2RadiusNormalBallChart (I := I) Y x))
    {eta : NNReal}
    (happrox : ApproximatesLinearOn (e.symm : E × E → E × E)
      ((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E)) e.target eta)
    (heta : eta < 1)
    {ι : Type} [Fintype ι] (z : E) (mu : ι → Real) (xi : ι → E)
    (htgt : ∀ i, (z, xi i) ∈ e.target)
    (hmu : ∀ i, 0 ≤ mu i) (hsum : ∑ i, mu i = 1)
    (hz : z ∈ normalBall (I := I) Y x)
    (hvel : invVelocitySum e mu xi z = 0) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : ConnectedSpace Y.M := hconn
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M :=
      Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
      (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    let c := c2RadiusNormalBallChart (I := I) Y x
    let B := IsNormalDiag.toBranch (I := I) Y hcomplete hconn x hq he
    ∃ L : E ≃L[Real] E,
      HasFDerivAt
          (fun u : E =>
            chartCenterOfMassEquation (I := I) Y.metric (normal_enorm (I := I) Y)
              x c B u (mu, xi))
          (L : E →L[Real] E) z ∧
        ∃ (f : ((ι → Real) × (ι → E)) → E)
            (Df : ((ι → Real) × (ι → E)) →L[Real] E),
          f (mu, xi) = z ∧ HasStrictFDerivAt f Df (mu, xi) ∧
            (∀ᶠ params in nhds (mu, xi),
              chartCenterOfMassEquation (I := I) Y.metric (normal_enorm (I := I) Y)
                x c B (f params) params = 0) ∧
            (∀ᶠ zp in nhds (z, (mu, xi)),
              chartCenterOfMassEquation (I := I) Y.metric (normal_enorm (I := I) Y)
                  x c B zp.1 zp.2 = 0 →
                zp.1 = f zp.2) := by
  classical
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : ConnectedSpace Y.M := hconn
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  let c := c2RadiusNormalBallChart (I := I) Y x
  let B := IsNormalDiag.toBranch (I := I) Y hcomplete hconn x hq he
  have hzBall : z ∈ Metric.ball (0 : E) c.radius := by
    with_unfolding_all
      exact hz
  have hxiBall (i : ι) : xi i ∈ Metric.ball (0 : E) c.radius :=
    (IsNormalDiag.target_mem_ball (I := I) Y hcomplete hconn x
      he hf (htgt i)).2
  have hzTarget : c.hom z ∈ c.restrictBall.target := by
    have hmap := c.restrictBall.map_source hzBall
    simpa only [NormalBallChart.restrict_ball_apply] using hmap
  have hdom (i : ι) :
      (c.hom z, c.hom (xi i)) ∈ B.chartCoordinateDomain c := by
    have hpair :
        normalPair (I := I) Y x (z, xi i) (c := c) ∈ B.dom := by
      rw [← (IsNormalDiag.branch_coordinate_transport (I := I) Y hcomplete hconn
        x hq he hf).2.1]
      refine ⟨(z, xi i), htgt i, ?_⟩
      exact c.pairHome_apply (z, xi i)
    refine ⟨?_, hzTarget⟩
    simpa only [normalPair, NormalBallChart.pair] using hpair
  have hzeroC :
      chartCenterOfMassEquation (I := I) Y.metric (normal_enorm (I := I) Y)
        x c B z (mu, xi) = 0 :=
    (IsNormalDiag.chartCenterOfMassEquation_zero_iff (I := I) Y hcomplete hconn x
      hq he hf z mu xi htgt).mpr hvel
  exact IsNormalDiag.chartCenterOfMassEquation_has_strict_solution (I := I) Y hcomplete hconn x
    hq he hf happrox heta z mu xi htgt hmu hsum
      ⟨hzBall, hxiBall, hdom, hzeroC⟩

theorem normalChartCenterOfMassEquationWithBranch_has_invertible_derivative
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) {q : NNReal} {delta : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q) (he : IsNormalDiag (I := I) Y hcomplete hconn x q delta e)
    (hf : NormalDiagFence (I := I) Y x q e)
    {eta : NNReal}
    (happrox : ApproximatesLinearOn (e.symm : E × E → E × E)
      ((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E)) e.target eta)
    (heta : eta < 1)
    {ι : Type} [Fintype ι] (z : E) (mu : ι → Real) (xi : ι → E)
    (htgt : ∀ i, (z, xi i) ∈ e.target)
    (hmu : ∀ i, 0 ≤ mu i) (hsum : ∑ i, mu i = 1) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : ConnectedSpace Y.M := hconn
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M :=
      Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
      (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    normalChartCenterOfMassEquationWithBranch (I := I) Y.metric (normal_enorm (I := I) Y) x
        (toBranch (I := I) Y hcomplete hconn x hq he) z (mu, xi) = 0 →
      ∃ L : E ≃L[Real] E,
      HasFDerivAt
        (fun u : E => normalChartCenterOfMassEquationWithBranch (I := I) Y.metric
          (normal_enorm (I := I) Y) x
          (toBranch (I := I) Y hcomplete hconn x hq he) u (mu, xi))
        (L : E →L[Real] E) z := by
  classical
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : ConnectedSpace Y.M := hconn
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
    (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  intro hzero
  have heData := he
  change e.source = Metric.ball (0 : E × E) q ∧
    e 0 = 0 ∧
    ContDiffOn Real ∞ (e : E × E → E × E) e.source ∧
    Metric.closedBall (0 : E × E) delta ⊆ e.target ∧
    ContDiffOn Real ∞ e.symm e.target ∧
    ∀ a ∈ Metric.closedBall (0 : E × E) q,
      normalPair (I := I) Y x (e a) =
        diagExp (I := I) Y.metric (normal_enorm (I := I) Y)
          (normalTangent (I := I) Y x a) at heData
  have hinv : ContDiffOn Real ∞ (e.symm : E × E → E × E) e.target :=
    heData.2.2.2.2.1
  have huniv : (Finset.univ : Finset ι).Nonempty := by
    by_contra hne
    have hempty : (Finset.univ : Finset ι) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hempty] at hsum
    simp at hsum
  obtain ⟨i0, hi0⟩ := huniv
  have hzBall : e.symm (z, xi i0) ∈ Metric.ball (0 : E × E) q := by
    rw [← heData.1]
    exact e.map_target (htgt i0)
  have hfence := hf
  change ∀ a ∈ Metric.closedBall (0 : E × E) q,
    a.1 ∈ normalBall (I := I) Y x ∧
    (e a).1 ∈ normalBall (I := I) Y x ∧
    (e a).2 ∈ normalBall (I := I) Y x at hfence
  have hzNormal : z ∈ normalBall (I := I) Y x := by
    have hz := (hfence (e.symm (z, xi i0))
      (Metric.ball_subset_closedBall hzBall)).2.1
    simpa only [e.right_inv (htgt i0)] using hz
  have hzNormLt : ‖z‖ < expMapC2Radius (I := I) Y.metric x := by
    have hzNormal' := hzNormal
    change z ∈ Metric.ball (0 : E)
      (expMapC2Radius (I := I) Y.metric x) at hzNormal'
    rwa [Metric.mem_ball, dist_zero_right] at hzNormal'
  have hzExpSource : z ∈ (expMapDiffeo (I := I) Y.metric x).source :=
    mem_expMapDiffeo_source_of_norm_lt_radius (I := I) Y.metric x hzNormLt
  have hbase : expMapDiffeo (I := I) Y.metric x z ∈
      (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact NormalCoordinates.exp_target_sub_chart (I := I) Y.metric x
      ((expMapDiffeo (I := I) Y.metric x).map_source hzExpSource)
  have hfactor := normalChartCenterOfMassEquationWithBranch_factor (I := I) Y hcomplete hconn x
    hq he hf z mu xi htgt
  have hreadZero : normalReadCLM (I := I) Y x z (invVelocitySum e mu xi z) = 0 := by
    rw [← hfactor]
    exact hzero
  have hvelZero : invVelocitySum e mu xi z = 0 := by
    apply (normalReadCLE (I := I) Y x hzNormal hbase).injective
    have hcoe := normalReadCLE_coe (I := I) Y x hzNormal hbase
    rw [show normalReadCLE (I := I) Y x hzNormal hbase (invVelocitySum e mu xi z) =
        normalReadCLM (I := I) Y x z (invVelocitySum e mu xi z) from
      congrArg (fun A : E →L[Real] E => A (invVelocitySum e mu xi z)) hcoe,
      show normalReadCLE (I := I) Y x hzNormal hbase 0 =
        normalReadCLM (I := I) Y x z 0 from
      congrArg (fun A : E →L[Real] E => A 0) hcoe,
      hreadZero, map_zero]
  obtain ⟨L, hL⟩ := normalComp_inv (I := I) Y x e mu xi hzNormal hinv
    htgt happrox hmu hsum heta hvelZero hbase
  have htgtNhd : ∀ i, ∀ᶠ u in nhds z, (u, xi i) ∈ e.target := by
    intro i
    have hpair : ContinuousAt (fun u : E => (u, xi i)) z := by fun_prop
    exact hpair.preimage_mem_nhds (e.open_target.mem_nhds (htgt i))
  have heq :
      (fun u : E => normalChartCenterOfMassEquationWithBranch (I := I) Y.metric
        (normal_enorm (I := I) Y) x
        (toBranch (I := I) Y hcomplete hconn x hq he) u (mu, xi)) =ᶠ[nhds z]
      (fun u : E => normalReadCLM (I := I) Y x u (invVelocitySum e mu xi u)) := by
    filter_upwards [Filter.eventually_all.mpr htgtNhd] with u hu
    exact normalChartCenterOfMassEquationWithBranch_factor (I := I) Y hcomplete hconn x
      hq he hf u mu xi hu
  exact ⟨L, hL.congr_of_eventuallyEq heq⟩

theorem normalChartCenterOfMassEquationWithBranch_has_strict_solution
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) {q : NNReal} {delta : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q) (he : IsNormalDiag (I := I) Y hcomplete hconn x q delta e)
    (hf : NormalDiagFence (I := I) Y x q e)
    {eta : NNReal}
    (happrox : ApproximatesLinearOn (e.symm : E × E → E × E)
      ((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E)) e.target eta)
    (heta : eta < 1)
    {ι : Type} [Fintype ι] (z : E) (mu : ι → Real) (xi : ι → E)
    (htgt : ∀ i, (z, xi i) ∈ e.target)
    (hmu : ∀ i, 0 ≤ mu i) (hsum : ∑ i, mu i = 1)
    (hzero :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : IsManifold I 1 Y.M := IsManifold.of_le
        (I := I) (M := Y.M) (n := ∞) (by decide)
      letI : SigmaCompactSpace Y.M := Y.sigmaCompact
      letI : T2Space Y.M := Y.t2
      letI : ConnectedSpace Y.M := hconn
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      letI : TopologicalSpace.MetrizableSpace Y.M :=
        Manifold.metrizableSpace I Y.M
      letI : T3Space Y.M := inferInstance
      letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
        Y.riemBundle (I := I)
      letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
        Y.riemInner (I := I)
      letI : IsContinuousRiemannianBundle E
        (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
      letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
      letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
      normalChartCenterOfMassEquationWithBranch (I := I) Y.metric (normal_enorm (I := I) Y) x
        (toBranch (I := I) Y hcomplete hconn x hq he) z (mu, xi) = 0) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : ConnectedSpace Y.M := hconn
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M :=
      Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
      (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    let B := toBranch (I := I) Y hcomplete hconn x hq he
    ∃ L : E ≃L[Real] E,
      HasFDerivAt
          (fun u : E => normalChartCenterOfMassEquationWithBranch (I := I) Y.metric
            (normal_enorm (I := I) Y) x B u (mu, xi))
          (L : E →L[Real] E) z ∧
        ∃ (f : ((ι → Real) × (ι → E)) → E)
            (Df : ((ι → Real) × (ι → E)) →L[Real] E),
          f (mu, xi) = z ∧ HasStrictFDerivAt f Df (mu, xi) ∧
            (∀ᶠ params in nhds (mu, xi),
              normalChartCenterOfMassEquationWithBranch (I := I) Y.metric (normal_enorm (I := I) Y)
                x B (f params) params = 0) ∧
            (∀ᶠ zp in nhds (z, (mu, xi)),
              normalChartCenterOfMassEquationWithBranch (I := I) Y.metric (normal_enorm (I := I) Y)
                  x B zp.1 zp.2 = 0 →
                zp.1 = f zp.2) := by
  classical
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : ConnectedSpace Y.M := hconn
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
    (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  let B := toBranch (I := I) Y hcomplete hconn x hq he
  obtain ⟨L, hL⟩ := normalChartCenterOfMassEquationWithBranch_has_invertible_derivative (I := I) Y hcomplete hconn x hq he hf
    happrox heta z mu xi htgt hmu hsum hzero
  refine ⟨L, hL, ?_⟩
  have heData := he
  change e.source = Metric.ball (0 : E × E) q ∧
    e 0 = 0 ∧
    ContDiffOn Real ∞ (e : E × E → E × E) e.source ∧
    Metric.closedBall (0 : E × E) delta ⊆ e.target ∧
    ContDiffOn Real ∞ e.symm e.target ∧
    ∀ a ∈ Metric.closedBall (0 : E × E) q,
      normalPair (I := I) Y x (e a) =
        diagExp (I := I) Y.metric (normal_enorm (I := I) Y)
          (normalTangent (I := I) Y x a) at heData
  have hfence := hf
  change ∀ a ∈ Metric.closedBall (0 : E × E) q,
    a.1 ∈ normalBall (I := I) Y x ∧
    (e a).1 ∈ normalBall (I := I) Y x ∧
    (e a).2 ∈ normalBall (I := I) Y x at hfence
  have hnormal (i : ι) : z ∈ normalBall (I := I) Y x ∧
      xi i ∈ normalBall (I := I) Y x := by
    have hpre : e.symm (z, xi i) ∈ Metric.ball (0 : E × E) q := by
      rw [← heData.1]
      exact e.map_target (htgt i)
    have hout := (hfence (e.symm (z, xi i))
      (Metric.ball_subset_closedBall hpre)).2
    simpa only [e.right_inv (htgt i)] using hout
  have hcoordTarget {v : E} (hv : v ∈ normalBall (I := I) Y x) :
      v ∈ (NormalCoordinates.normalChartAt (I := I) Y.metric x).target := by
    change v ∈ Metric.ball (0 : E) (expMapC2Radius (I := I) Y.metric x) at hv
    rw [NormalCoordinates.normalChartAt_target_eq]
    exact mem_expMapDiffeo_source_of_norm_lt_radius (I := I) Y.metric x
      (by rwa [Metric.mem_ball, dist_zero_right] at hv)
  have huniv : (Finset.univ : Finset ι).Nonempty := by
    by_contra hne
    have hempty : (Finset.univ : Finset ι) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hempty] at hsum
    simp at hsum
  obtain ⟨i0, _hi0⟩ := huniv
  have hchz : ContMDiffAt 𝓘(Real, E) I 1
      (fun u : E =>
        (NormalCoordinates.normalChartAt (I := I) Y.metric x).symm u) z := by
    have hzTarget := hcoordTarget (hnormal i0).1
    exact (NormalCoordinates.normalChartAt_symm_contMDiffOn
      (I := I) Y.metric x z hzTarget).contMDiffAt
        ((NormalCoordinates.normalChartAt (I := I) Y.metric x).open_target.mem_nhds
          hzTarget)
  have hchxi (i : ι) : ContMDiffAt 𝓘(Real, E) I 1
      (fun u : E =>
        (NormalCoordinates.normalChartAt (I := I) Y.metric x).symm u) (xi i) := by
    have hiTarget := hcoordTarget (hnormal i).2
    exact (NormalCoordinates.normalChartAt_symm_contMDiffOn
      (I := I) Y.metric x (xi i) hiTarget).contMDiffAt
        ((NormalCoordinates.normalChartAt (I := I) Y.metric x).open_target.mem_nhds
          hiTarget)
  have htransport := branch_coordinate_transport (I := I) Y hcomplete hconn x hq he hf
  have hread (i : ι) :
      ContMDiffAt (I.prod I) 𝓘(Real, E) 1
        (fun yq : Y.M × Y.M => B.diagonalInverseCoordinates yq)
        ((NormalCoordinates.normalChartAt (I := I) Y.metric x).symm z,
          (NormalCoordinates.normalChartAt (I := I) Y.metric x).symm (xi i)) := by
    have hdom :
        ((NormalCoordinates.normalChartAt (I := I) Y.metric x).symm z,
          (NormalCoordinates.normalChartAt (I := I) Y.metric x).symm (xi i)) ∈ B.dom := by
      rw [← htransport.2.1]
      refine ⟨(z, xi i), htgt i, ?_⟩
      rfl
    have hzTarget := hcoordTarget (hnormal i).1
    have hbase :
        (NormalCoordinates.normalChartAt (I := I) Y.metric x).symm z ∈
          (trivializationAt E (TangentSpace I) x).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact NormalCoordinates.exp_target_sub_chart (I := I) Y.metric x
        ((expMapDiffeo (I := I) Y.metric x).map_source (by
          simpa only [NormalCoordinates.normalChartAt_target_eq] using hzTarget))
    have hmem :
        ((NormalCoordinates.normalChartAt (I := I) Y.metric x).symm z,
          (NormalCoordinates.normalChartAt (I := I) Y.metric x).symm (xi i)) ∈
            B.coordinateDomain := ⟨hdom, hbase⟩
    have hdata := B.diagonalInverseCoordinates_properties
    exact ((hdata.2.2.1 _ hmem).contMDiffAt (hdata.1.mem_nhds hmem)).of_le
      (by simp)
  exact normalChartCenterOfMassEquationWithBranch_implicitFunction_hasStrictFDerivAt (I := I) Y.metric (normal_enorm (I := I) Y) x B
    z (mu, xi) hchz hchxi hread ⟨L, hL⟩ hzero

theorem normalChartCenterOfMassEquationWithBranch_has_contDiff_solution
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) {q : NNReal} {delta : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q) (he : IsNormalDiag (I := I) Y hcomplete hconn x q delta e)
    (hf : NormalDiagFence (I := I) Y x q e)
    {eta : NNReal}
    (happrox : ApproximatesLinearOn (e.symm : E × E → E × E)
      ((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E)) e.target eta)
    (heta : eta < 1)
    {ι : Type} [Fintype ι] (z : E) (mu : ι → Real) (xi : ι → E)
    (htgt : ∀ i, (z, xi i) ∈ e.target)
    (hmu : ∀ i, 0 ≤ mu i) (hsum : ∑ i, mu i = 1)
    (n : Nat) (hn : 1 ≤ n)
    (hzero :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : IsManifold I 1 Y.M := IsManifold.of_le
        (I := I) (M := Y.M) (n := ∞) (by decide)
      letI : SigmaCompactSpace Y.M := Y.sigmaCompact
      letI : T2Space Y.M := Y.t2
      letI : ConnectedSpace Y.M := hconn
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      letI : TopologicalSpace.MetrizableSpace Y.M :=
        Manifold.metrizableSpace I Y.M
      letI : T3Space Y.M := inferInstance
      letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
        Y.riemBundle (I := I)
      letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
        Y.riemInner (I := I)
      letI : IsContinuousRiemannianBundle E
        (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
      letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
      letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
      normalChartCenterOfMassEquationWithBranch (I := I) Y.metric (normal_enorm (I := I) Y) x
        (toBranch (I := I) Y hcomplete hconn x hq he) z (mu, xi) = 0) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : ConnectedSpace Y.M := hconn
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M :=
      Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
      (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    let B := toBranch (I := I) Y hcomplete hconn x hq he
    ∃ f : ((ι → Real) × (ι → E)) → E,
      f (mu, xi) = z ∧ ContDiffAt Real (n : ℕ∞) f (mu, xi) ∧
        (∀ᶠ params in nhds (mu, xi),
          normalChartCenterOfMassEquationWithBranch (I := I) Y.metric (normal_enorm (I := I) Y)
            x B (f params) params = 0) ∧
        (∀ᶠ zp in nhds (z, (mu, xi)),
          normalChartCenterOfMassEquationWithBranch (I := I) Y.metric (normal_enorm (I := I) Y)
              x B zp.1 zp.2 = 0 →
            zp.1 = f zp.2) := by
  classical
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : ConnectedSpace Y.M := hconn
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  let B := toBranch (I := I) Y hcomplete hconn x hq he
  obtain ⟨L, hL, _hstrict⟩ := normalChartCenterOfMassEquationWithBranch_has_strict_solution (I := I) Y hcomplete hconn x
    hq he hf happrox heta z mu xi htgt hmu hsum hzero
  have heData := he
  change e.source = Metric.ball (0 : E × E) q ∧
    e 0 = 0 ∧
    ContDiffOn Real ∞ (e : E × E → E × E) e.source ∧
    Metric.closedBall (0 : E × E) delta ⊆ e.target ∧
    ContDiffOn Real ∞ e.symm e.target ∧
    ∀ a ∈ Metric.closedBall (0 : E × E) q,
      normalPair (I := I) Y x (e a) =
        diagExp (I := I) Y.metric (normal_enorm (I := I) Y)
          (normalTangent (I := I) Y x a) at heData
  have hfence := hf
  change ∀ a ∈ Metric.closedBall (0 : E × E) q,
    a.1 ∈ normalBall (I := I) Y x ∧
    (e a).1 ∈ normalBall (I := I) Y x ∧
    (e a).2 ∈ normalBall (I := I) Y x at hfence
  have hnormal (i : ι) : z ∈ normalBall (I := I) Y x ∧
      xi i ∈ normalBall (I := I) Y x := by
    have hpre : e.symm (z, xi i) ∈ Metric.ball (0 : E × E) q := by
      rw [← heData.1]
      exact e.map_target (htgt i)
    have hout := (hfence (e.symm (z, xi i))
      (Metric.ball_subset_closedBall hpre)).2
    simpa only [e.right_inv (htgt i)] using hout
  have hcoordTarget {v : E} (hv : v ∈ normalBall (I := I) Y x) :
      v ∈ (NormalCoordinates.normalChartAt (I := I) Y.metric x).target := by
    change v ∈ Metric.ball (0 : E) (expMapC2Radius (I := I) Y.metric x) at hv
    rw [NormalCoordinates.normalChartAt_target_eq]
    exact mem_expMapDiffeo_source_of_norm_lt_radius (I := I) Y.metric x
      (by rwa [Metric.mem_ball, dist_zero_right] at hv)
  have huniv : (Finset.univ : Finset ι).Nonempty := by
    by_contra hne
    have hempty : (Finset.univ : Finset ι) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hempty] at hsum
    simp at hsum
  obtain ⟨i0, _hi0⟩ := huniv
  have hchz : ContMDiffAt 𝓘(Real, E) I (n : ℕ∞)
      (fun u : E =>
        (NormalCoordinates.normalChartAt (I := I) Y.metric x).symm u) z := by
    change ContMDiffAt 𝓘(Real, E) I (n : ℕ∞)
      (fun u : E => expMapDiffeo (I := I) Y.metric x u) z
    exact ((exp_map_diffeo_cont_mdiff_on_exp_ball (I := I) Y x).contMDiffAt
      (Metric.isOpen_ball.mem_nhds (hnormal i0).1)).of_le
        (WithTop.coe_le_coe.mpr le_top)
  have hchxi (i : ι) : ContMDiffAt 𝓘(Real, E) I (n : ℕ∞)
      (fun u : E =>
        (NormalCoordinates.normalChartAt (I := I) Y.metric x).symm u) (xi i) := by
    change ContMDiffAt 𝓘(Real, E) I (n : ℕ∞)
      (fun u : E => expMapDiffeo (I := I) Y.metric x u) (xi i)
    exact ((exp_map_diffeo_cont_mdiff_on_exp_ball (I := I) Y x).contMDiffAt
      (Metric.isOpen_ball.mem_nhds (hnormal i).2)).of_le
        (WithTop.coe_le_coe.mpr le_top)
  have htransport := branch_coordinate_transport (I := I) Y hcomplete hconn x hq he hf
  have hread (i : ι) :
      ContMDiffAt (I.prod I) 𝓘(Real, E) (n : ℕ∞)
        (fun yq : Y.M × Y.M => B.diagonalInverseCoordinates yq)
        ((NormalCoordinates.normalChartAt (I := I) Y.metric x).symm z,
          (NormalCoordinates.normalChartAt (I := I) Y.metric x).symm (xi i)) := by
    have hdom :
        ((NormalCoordinates.normalChartAt (I := I) Y.metric x).symm z,
          (NormalCoordinates.normalChartAt (I := I) Y.metric x).symm (xi i)) ∈ B.dom := by
      rw [← htransport.2.1]
      refine ⟨(z, xi i), htgt i, ?_⟩
      rfl
    have hbase :
        (NormalCoordinates.normalChartAt (I := I) Y.metric x).symm z ∈
          (trivializationAt E (TangentSpace I) x).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact NormalCoordinates.exp_target_sub_chart (I := I) Y.metric x
        ((expMapDiffeo (I := I) Y.metric x).map_source
          (hcoordTarget (hnormal i).1))
    have hmem :
        ((NormalCoordinates.normalChartAt (I := I) Y.metric x).symm z,
          (NormalCoordinates.normalChartAt (I := I) Y.metric x).symm (xi i)) ∈
            B.coordinateDomain := ⟨hdom, hbase⟩
    have hdata := B.diagonalInverseCoordinates_properties
    exact ((hdata.2.2.1 _ hmem).contMDiffAt (hdata.1.mem_nhds hmem)).of_le
      (WithTop.coe_le_coe.mpr le_top)
  exact normalChartCenterOfMassEquationWithBranch_implicitFunction_contDiffAt (I := I) Y.metric (normal_enorm (I := I) Y) x B
    z (mu, xi) n hn hchz hchxi hread ⟨L, hL⟩ hzero

end IsNormalDiag

namespace HasControlledNormalBranch

theorem hess_pos
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hb : NormalCoordMetricBounds (I := I) X) (k : Nat)
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (hconn : letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (x : (X.obj k).M) {q : NNReal} {δ ρ : Real}
    (hfull : HasControlledNormalBranch (I := I) (X.obj k) hcomplete hconn x q δ ρ)
    (hqAcc : 3 * hb.metricC 1 * (2 * (q : Real)) ^ 2 ≤
      (2 / 3 : Real) * (q : Real)) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : IsManifold I 1 (X.obj k).M := IsManifold.of_le
      (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : ConnectedSpace (X.obj k).M := hconn
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
      Manifold.metrizableSpace I (X.obj k).M
    letI : T3Space (X.obj k).M := inferInstance
    letI : RiemannianBundle
        (fun z : (X.obj k).M ↦ TangentSpace I z) :=
      (X.obj k).riemBundle (I := I)
    letI : (z : (X.obj k).M) → InnerProductSpace Real (TangentSpace I z) :=
      (X.obj k).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun z : (X.obj k).M ↦ TangentSpace I z) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
    letI : CompleteSpace (X.obj k).M :=
      MetricComplete.complete (I := I) (X.obj k) hcomplete
    letI : MetricSpace (X.obj k).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj k).M)
    Metric.ball (0 : E) ρ ⊆ normalQuarter (I := I) (X.obj k) x →
      0 < ρ →
      2 * ρ < (q : Real) →
      ρ ≤ hb.radius k x →
      ρ / 2 ≤ metricCoerciveExpRadius (I := I) (X.obj k).metric x →
      ∀ {y pt : (X.obj k).M},
        max (riemannianEDist I x y) (riemannianEDist I x pt) <
            ENNReal.ofReal (ρ / 2) →
        ∀ {v : TangentSpace I y}, v ≠ 0 →
          0 < hessFun (I := I) (X.obj k).metric
            (CenterOfMass.halfSqDist pt) y v v := by
  classical
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : IsManifold I 1 (X.obj k).M := IsManifold.of_le
    (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  let : T2Space (X.obj k).M := (X.obj k).t2
  let : ConnectedSpace (X.obj k).M := hconn
  let : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  let : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  let : T3Space (X.obj k).M := inferInstance
  let : RiemannianBundle
      (fun z : (X.obj k).M ↦ TangentSpace I z) :=
    (X.obj k).riemBundle (I := I)
  let : (z : (X.obj k).M) → InnerProductSpace Real (TangentSpace I z) :=
    (X.obj k).riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun z : (X.obj k).M ↦ TangentSpace I z) :=
    (X.obj k).riemBundle_cont (I := I)
  let : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
  let : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) hcomplete
  let : MetricSpace (X.obj k).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj k).M)
  intro hquarter hρ hρq hρmetric hρexp y pt hpairs v hv
  dsimp only [HasControlledNormalBranch] at hfull
  rcases hfull with
    ⟨hq, e, he, hf, _hclosed, _hδdom, _hhom, _hpair, _hinv,
      _hδinv, eta, heta, happrox⟩
  have hyLt : riemannianEDist I x y < ENNReal.ofReal (ρ / 2) :=
    (le_max_left _ _).trans_lt hpairs
  have hptLt : riemannianEDist I x pt < ENNReal.ofReal (ρ / 2) :=
    (le_max_right _ _).trans_lt hpairs
  have hyFin : riemannianEDist I x y ≠ ⊤ :=
    ne_of_lt (hyLt.trans ENNReal.ofReal_lt_top)
  have hptFin : riemannianEDist I x pt ≠ ⊤ :=
    ne_of_lt (hptLt.trans ENNReal.ofReal_lt_top)
  have hyReal : (riemannianEDist I x y).toReal < ρ / 2 :=
    (ENNReal.lt_ofReal_iff_toReal_lt hyFin).mp hyLt
  have hptReal : (riemannianEDist I x pt).toReal < ρ / 2 :=
    (ENNReal.lt_ofReal_iff_toReal_lt hptFin).mp hptLt
  have hyControl := hb.raw_chart_mem_norm_le k x y
    ⟨hyFin, hyReal.trans_le hρexp⟩
  have hptControl := hb.raw_chart_mem_norm_le k x pt
    ⟨hptFin, hptReal.trans_le hρexp⟩
  let z : E := NormalCoordinates.normalChartAt
    (I := I) (X.obj k).metric x y
  let xi : E := NormalCoordinates.normalChartAt
    (I := I) (X.obj k).metric x pt
  have hzρ : ‖z‖ < ρ := by
    calc
      ‖z‖ ≤ 2 * (riemannianEDist I x y).toReal := hyControl.2
      _ < 2 * (ρ / 2) := mul_lt_mul_of_pos_left hyReal (by norm_num)
      _ = ρ := by ring
  have hzBall : z ∈ Metric.ball (0 : E) ρ := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hzρ
  have hzQ : z ∈ normalQuarter (I := I) (X.obj k) x := hquarter hzBall
  have hzMetric : z ∈ Metric.ball (0 : E) (hb.radius k x) :=
    Metric.ball_subset_ball hρmetric hzBall
  have hdom := (IsNormalDiag.inv_is_min (I := I) hb k hcomplete hconn x
    hq he hf hρ hρq hρmetric hρexp hpairs).choose_spec.1
  have hw : (z, xi) ∈ e.target := by
    simpa only [z, xi] using
      IsNormalDiag.target_of_chart_dom (I := I) (X.obj k) hcomplete hconn x
        hq he hf hyControl.1 hptControl.1 hdom
  have hzSource : z ∈
      (expMapDiffeo (I := I) (X.obj k).metric x).source := by
    change z ∈ (NormalCoordinates.normalChartAt
      (I := I) (X.obj k).metric x).target
    simpa only [z] using
      (NormalCoordinates.normalChartAt
        (I := I) (X.obj k).metric x).map_source hyControl.1
  have hyDecode : expMapDiffeo (I := I) (X.obj k).metric x z = y := by
    change (NormalCoordinates.normalChartAt
      (I := I) (X.obj k).metric x).symm z = y
    simpa only [z] using NormalCoordinates.normalChartAt_left_inv
      (I := I) (X.obj k).metric x hyControl.1
  let hloc : IsLocalDiffeomorphAt 𝓘(Real, E) I 1
      (expMapDiffeo (I := I) (X.obj k).metric x) z :=
    PartialDiffeomorph.isLocalDiffeomorphAt
      (I := 𝓘(Real, E)) (J := I) (n := 1)
      (expMapDiffeo (I := I) (X.obj k).metric x) hzSource
  let dExpEquiv : E ≃L[Real] TangentSpace I
      (expMapDiffeo (I := I) (X.obj k).metric x z) :=
    hloc.mfderivToContinuousLinearEquiv (by norm_num)
  let vExp : TangentSpace I
      (expMapDiffeo (I := I) (X.obj k).metric x z) :=
    (tangentSpaceModelContinuousLinearEquiv (I := I)
      (expMapDiffeo (I := I) (X.obj k).metric x z)).symm
        ((tangentSpaceModelContinuousLinearEquiv (I := I) y) v)
  have hvExp : vExp ≠ 0 := by
    intro hvExp0
    have hmodel := congrArg
      (tangentSpaceModelContinuousLinearEquiv (I := I)
        (expMapDiffeo (I := I) (X.obj k).metric x z)) hvExp0
    apply hv
    apply (tangentSpaceModelContinuousLinearEquiv (I := I) y).injective
    simpa only [vExp, ContinuousLinearEquiv.apply_symm_apply, map_zero] using hmodel
  let u : E := dExpEquiv.symm vExp
  have hu : u ≠ 0 := by
    intro hu0
    apply hvExp
    change dExpEquiv.symm vExp = 0 at hu0
    have hzero := congrArg dExpEquiv hu0
    simpa only [map_zero, dExpEquiv.apply_symm_apply] using hzero
  have hdExp : mfderiv 𝓘(Real, E) I
      (fun w : E ↦ expMapDiffeo (I := I) (X.obj k).metric x w) z u = vExp := by
    have hcoe := hloc.mfderivToContinuousLinearEquiv_coe (by norm_num)
    change (mfderiv 𝓘(Real, E) I
      (expMapDiffeo (I := I) (X.obj k).metric x) z) u = vExp
    rw [← hcoe, ContinuousLinearEquiv.coe_coe]
    change dExpEquiv (dExpEquiv.symm vExp) = vExp
    exact dExpEquiv.apply_symm_apply vExp
  have hptDecode : expMapDiffeo (I := I) (X.obj k).metric x xi = pt := by
    change (NormalCoordinates.normalChartAt
      (I := I) (X.obj k).metric x).symm xi = pt
    simpa only [xi] using NormalCoordinates.normalChartAt_left_inv
      (I := I) (X.obj k).metric x hptControl.1
  have hmetric := hb.metric_equiv k x z hzMetric u
  have hnorm : 0 < ‖u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
  have hgpos : 0 < normalCoordMetric (I := I) (X.obj k) x z u u := by
    nlinarith [hmetric.1]
  have hpairs' : max
      (riemannianEDist I x
        (expMapDiffeo (I := I) (X.obj k).metric x z))
      (riemannianEDist I x
        (expMapDiffeo (I := I) (X.obj k).metric x xi)) <
        ENNReal.ofReal (ρ / 2) := by
    simpa only [hyDecode, hptDecode] using hpairs
  have hhess := IsNormalDiag.hess_inv_sixth (I := I) hb k hcomplete hconn x
    hq he hf happrox heta hqAcc hw hzQ hzMetric u hρ hρq hρmetric hρexp hpairs'
  have hdExp' : mfderiv 𝓘(Real, E) I
      (fun w : E ↦ expMapDiffeo (I := I) (X.obj k).metric x w) z u = vExp :=
    hdExp
  rw [hdExp'] at hhess
  rw [hyDecode] at hhess
  rw [hptDecode] at hhess
  let vY : TangentSpace I y :=
    (tangentSpaceModelContinuousLinearEquiv (I := I) y).symm
      ((tangentSpaceModelContinuousLinearEquiv (I := I)
        (expMapDiffeo (I := I) (X.obj k).metric x z)) vExp)
  have hvY : vY = v := by
    with_unfolding_all
      exact (tangentSpaceModelContinuousLinearEquiv (I := I) y).apply_symm_apply v
  have hhessY : (1 / 6 : Real) *
        normalCoordMetric (I := I) (X.obj k) x z u u ≤
      hessFun (I := I) (X.obj k).metric
        (CenterOfMass.halfSqDist pt) y vY vY := by
    with_unfolding_all
      exact hhess
  have hhess' : (1 / 6 : Real) *
        normalCoordMetric (I := I) (X.obj k) x z u u ≤
      hessFun (I := I) (X.obj k).metric
        (CenterOfMass.halfSqDist pt) y v v := by
    simpa only [hvY] using hhessY
  nlinarith

end HasControlledNormalBranch

end CheegerGromovCompactness
end DifferentialGeometry
