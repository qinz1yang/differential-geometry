import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ShortTime.ReducedJacobianLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Jacobian.SourceGaussianTail

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open scoped ContDiff ENNReal Manifold Topology

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
theorem lRedJac_src_le
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau)
    (hZ : Z ∈ lInjDomain (E := E) (I := I) S T x tau) :
    ENNReal.ofReal (lRedJac S T x Z tau * lSrcDensity S T x) ≤
      ENNReal.ofReal (lSrcGauss S T x Z) := by
  change E at Z
  apply ENNReal.ofReal_le_ofReal
  rw [lSrcGauss_eq]
  calc
    lRedJac S T x Z tau * lSrcDensity S T x ≤
        (((Real.pi : Real) ^
            ((Module.finrank Real E : Real) / 2))⁻¹ *
          Real.exp (-(S.base.metric T).inner x Z Z)) *
            lSrcDensity S T x :=
      mul_le_mul_of_nonneg_right
        (lRedJac_le_gaussian S hS T x htau hZ)
        (lSrcDensity_pos S T x).le
    _ = ((Real.pi : Real) ^
          ((Module.finrank Real E : Real) / 2))⁻¹ *
        lSrcDensity S T x *
          Real.exp (-(S.base.metric T).inner x Z Z) := by
      ring

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lRedJac_tail_le
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (tau R : Real) (htau : 0 < tau) :
    (∫⁻ Z : E in
        lInjDomain S T x tau ∩
          {Z | R < Real.sqrt ((S.base.metric T).inner x Z Z)},
        ENNReal.ofReal (lRedJac S T x Z tau * lSrcDensity S T x)
          ∂(modelHaar (E := E))) ≤
      ∫⁻ Z : E in
        {Z | R < Real.sqrt ((S.base.metric T).inner x Z Z)},
        ENNReal.ofReal (lSrcGauss S T x Z)
          ∂(modelHaar (E := E)) := by
  have htail : MeasurableSet
      {Z : E | R < Real.sqrt ((S.base.metric T).inner x Z Z)} := by
    have heq : (fun Z : E ↦ (S.base.metric T).inner x Z Z) =
        fun Z ↦ inner Real (toEuclidean Z)
          (Matrix.toEuclideanCLM (n := Fin (Module.finrank Real E))
            (𝕜 := Real) (lSrcGram S T x) (toEuclidean Z)) := by
      funext Z
      exact (lSrcGram_quad S T x Z).symm
    have htail' : MeasurableSet
        {Z : E | R < Real.sqrt (inner Real (toEuclidean Z)
          (Matrix.toEuclideanCLM (n := Fin (Module.finrank Real E))
            (𝕜 := Real) (lSrcGram S T x) (toEuclidean Z)))} := by
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
        ENNReal.ofReal (lRedJac S T x Z tau * lSrcDensity S T x)
          ∂(modelHaar (E := E))) ≤
        ∫⁻ Z : E in
          lInjDomain S T x tau ∩
            {Z | R < Real.sqrt ((S.base.metric T).inner x Z Z)},
          ENNReal.ofReal (lSrcGauss S T x Z)
            ∂(modelHaar (E := E)) := by
      refine setLIntegral_mono' hset ?_
      intro Z hZ
      exact lRedJac_src_le S hS T x htau hZ.1
    _ ≤ ∫⁻ Z : E in
        {Z | R < Real.sqrt ((S.base.metric T).inner x Z Z)},
        ENNReal.ofReal (lSrcGauss S T x Z)
          ∂(modelHaar (E := E)) :=
      lintegral_mono_set inter_subset_right

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lRedJac_tail_lim
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (tau : Real) (htau : 0 < tau) :
    Tendsto
      (fun R : Real ↦
        ∫⁻ Z : E in
          lInjDomain S T x tau ∩
            {Z | R < Real.sqrt ((S.base.metric T).inner x Z Z)},
          ENNReal.ofReal (lRedJac S T x Z tau * lSrcDensity S T x)
            ∂(modelHaar (E := E)))
      atTop (nhds 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds (lSrcGauss_tail S T x)
    (fun _ ↦ bot_le)
    (fun R ↦ lRedJac_tail_le S hS T x tau R htau)

end DifferentialGeometry.PDE.RicciFlow.Perelman
