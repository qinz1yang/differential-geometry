import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ShortTime.ReducedJacobianLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Jacobian.SourceGaussianTail

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open scoped ContDiff ENNReal Manifold _root_.Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open MeasureTheory

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompactSpace M] in
theorem lReducedJacobian_source_le_of_bdd
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (x : M) {Z : TangentSpace I x} {sigma tau : ℝ}
    (hmin : (Z, sigma) ∈ lMinDomain S T x) (htau : 0 < tau) (hlt : tau < sigma)
    (hbdd : BddBelow {r : ℝ | ∃ alpha : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧ alpha 0 = x ∧
        alpha (Real.sqrt sigma) = lExp S T x Z sigma ∧
        lRegularizedAction S T alpha 0 (Real.sqrt sigma) = r}) :
    ENNReal.ofReal (lReducedJacobian S T x Z tau * lSourceDensity S T x) ≤
      ENNReal.ofReal (lSourceGaussian S T x Z) := by
  change E at Z
  apply ENNReal.ofReal_le_ofReal
  rw [lSourceGaussian_eq_metric_norm]
  have hh := mul_le_mul_of_nonneg_right
    (lReducedJacobian_le_gaussian_of_bdd S hS T x hmin htau hlt hbdd)
    (lSourceDensity_pos S T x).le
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hh

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lReducedJacobian_source_le
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau)
    (hZ : Z ∈ lInjDomain (E := E) (I := I) S T x tau) :
    ENNReal.ofReal (lReducedJacobian S T x Z tau * lSourceDensity S T x) ≤
      ENNReal.ofReal (lSourceGaussian S T x Z) := by
  obtain ⟨sigma, hlt, hmin⟩ := hZ
  apply lReducedJacobian_source_le_of_bdd S hS T x hmin htau hlt
  apply lRegularizedCosts_bdd_of_compact S hS T (Real.sqrt_nonneg sigma)
  intro t ht
  exact D.regular_subset (lExpPosDom_regularity S T x Z
    ((mem_lMinDomain S T x Z sigma).mp hmin).1 ht)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lReducedJacobian_tail_le
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (tau R : Real) (htau : 0 < tau) :
    (∫⁻ Z : E in
        lInjDomain S T x tau ∩
          {Z | R < Real.sqrt ((S.base.metric T).inner x Z Z)},
        ENNReal.ofReal (lReducedJacobian S T x Z tau * lSourceDensity S T x)
          ∂(modelHaar (E := E))) ≤
      ∫⁻ Z : E in
        {Z | R < Real.sqrt ((S.base.metric T).inner x Z Z)},
        ENNReal.ofReal (lSourceGaussian S T x Z)
          ∂(modelHaar (E := E)) := by
  have htail : MeasurableSet
      {Z : E | R < Real.sqrt ((S.base.metric T).inner x Z Z)} := by
    have heq : (fun Z : E ↦ (S.base.metric T).inner x Z Z) =
        fun Z ↦ inner Real (toEuclidean Z)
          (Matrix.toEuclideanCLM (n := Fin (Module.finrank Real E))
            (𝕜 := Real) (lSourceGram S T x) (toEuclidean Z)) := by
      funext Z
      exact (lSourceGram_quadraticForm S T x Z).symm
    have htail' : MeasurableSet
        {Z : E | R < Real.sqrt (inner Real (toEuclidean Z)
          (Matrix.toEuclideanCLM (n := Fin (Module.finrank Real E))
            (𝕜 := Real) (lSourceGram S T x) (toEuclidean Z)))} := by
      apply measurableSet_lt measurable_const
      fun_prop
    exact (congrArg (fun f : E → Real ↦
      {Z : E | R < Real.sqrt (f Z)}) heq).symm ▸ htail'
  have hset : MeasurableSet
      (lInjDomain S T x tau ∩
        {Z : E | R < Real.sqrt ((S.base.metric T).inner x Z Z)}) :=
    (lInj_isOpen S hS T x tau).measurableSet.inter htail
  calc
    (∫⁻ Z : E in
        lInjDomain S T x tau ∩
          {Z | R < Real.sqrt ((S.base.metric T).inner x Z Z)},
        ENNReal.ofReal (lReducedJacobian S T x Z tau * lSourceDensity S T x)
          ∂(modelHaar (E := E))) ≤
        ∫⁻ Z : E in
          lInjDomain S T x tau ∩
            {Z | R < Real.sqrt ((S.base.metric T).inner x Z Z)},
          ENNReal.ofReal (lSourceGaussian S T x Z)
            ∂(modelHaar (E := E)) := by
      refine setLIntegral_mono' hset ?_
      intro Z hZ
      exact lReducedJacobian_source_le S hS T x htau hZ.1
    _ ≤ ∫⁻ Z : E in
        {Z | R < Real.sqrt ((S.base.metric T).inner x Z Z)},
        ENNReal.ofReal (lSourceGaussian S T x Z)
          ∂(modelHaar (E := E)) :=
      lintegral_mono_set inter_subset_right

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lReducedJacobian_tail_lim
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (tau : Real) (htau : 0 < tau) :
    Tendsto
      (fun R : Real ↦
        ∫⁻ Z : E in
          lInjDomain S T x tau ∩
            {Z | R < Real.sqrt ((S.base.metric T).inner x Z Z)},
          ENNReal.ofReal (lReducedJacobian S T x Z tau * lSourceDensity S T x)
            ∂(modelHaar (E := E)))
      atTop (nhds 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds (lSourceGaussian_tail_tendsto_zero S T x)
    (fun _ ↦ bot_le)
    (fun R ↦ lReducedJacobian_tail_le S hS T x tau R htau)

end DifferentialGeometry.PDE.RicciFlow.Perelman
