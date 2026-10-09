import DifferentialGeometry.Geometry.Neck.PointwiseChart
import DifferentialGeometry.Geometry.Metric.BilinearPerturbation
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Flat
import DifferentialGeometry.Geometry.Metric.RoundCylinder

set_option autoImplicit false
noncomputable section
open Set Function Bundle Manifold TopologicalSpace DifferentialGeometry
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.Geometry.Neck

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance (O : Opens (S2 × ℝ)) : SigmaCompactSpace O :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen IC O.isOpen)

theorem openCylinder_inv_le_bufferedCylinder (δ : ℝ) :
    openCylinder δ⁻¹ ≤ bufferedCylinder δ := by
  intro q hq
  change -δ⁻¹ < q.2 ∧ q.2 < δ⁻¹ at hq
  change -δ⁻¹ - 1 < q.2 ∧ q.2 < δ⁻¹ + 1
  constructor <;> linarith [hq.1, hq.2]

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

namespace normalizedDatum

variable {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}

def controlledMap (d : normalizedDatum g x₀ δ k) : openCylinder δ⁻¹ → M :=
  d.map ∘ Opens.inclusion (openCylinder_inv_le_bufferedCylinder δ)

theorem controlledMap_apply (d : normalizedDatum g x₀ δ k) (q : openCylinder δ⁻¹) :
    d.controlledMap q = d.map (Opens.inclusion (openCylinder_inv_le_bufferedCylinder δ) q) :=
  rfl

theorem controlledMap_smooth (d : normalizedDatum g x₀ δ k) :
    ContMDiff IC I ∞ d.controlledMap :=
  d.smooth.comp (contMDiff_inclusion (openCylinder_inv_le_bufferedCylinder δ))

theorem controlledMap_isOpenEmbedding (d : normalizedDatum g x₀ δ k) :
    _root_.Topology.IsOpenEmbedding d.controlledMap :=
  d.isOpenEmbedding_map.comp (Opens.isOpenEmbedding_of_le
    (openCylinder_inv_le_bufferedCylinder δ))

theorem controlledMap_mfderiv (d : normalizedDatum g x₀ δ k) (q : openCylinder δ⁻¹)
    (v : TangentSpace IC q) :
    mfderiv IC I d.controlledMap q v =
      mfderiv IC I d.map (Opens.inclusion (openCylinder_inv_le_bufferedCylinder δ) q) v := by
  have h := mfderiv_comp q
    (d.smooth.mdifferentiable (by decide) _)
    ((contMDiff_inclusion (I := IC) (n := ∞)
      (openCylinder_inv_le_bufferedCylinder δ)).mdifferentiable (by decide) q)
  have hv := congrArg (fun f => f v) h
  simpa only [controlledMap, mfderiv_opens_incl, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] using! hv

def controlledMetric (d : normalizedDatum g x₀ δ k) :
    SmoothRiemannianMetric IC (openCylinder δ⁻¹) :=
  d.normalizedMetric.restrictOpenOfSubset (openCylinder_inv_le_bufferedCylinder δ)

theorem controlledMetric_inner (d : normalizedDatum g x₀ δ k) (q : openCylinder δ⁻¹)
    (v w : TangentSpace IC q) :
    d.controlledMetric.inner q v w = metricScalarAt g x₀ *
      g.inner (d.controlledMap q) (mfderiv IC I d.controlledMap q v)
        (mfderiv IC I d.controlledMap q w) := by
  rw [controlledMap_mfderiv, controlledMap_mfderiv]
  exact d.normalizedMetric_inner
    (Opens.inclusion (openCylinder_inv_le_bufferedCylinder δ) q) v w

private theorem metricDerivNorm_controlledMetric (d : normalizedDatum g x₀ δ k)
    (j : ℕ) (q : openCylinder δ⁻¹) :
    metricDerivNorm j d.controlledMetric
      ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (openCylinder δ⁻¹))
      ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (openCylinder δ⁻¹)) q =
      metricDerivNorm j d.normalizedMetric (referenceMetric δ) (referenceMetric δ)
        (Opens.inclusion (openCylinder_inv_le_bufferedCylinder δ) q) := by
  simpa only [controlledMetric, referenceMetric, SmoothRiemannianMetric.restrictOpen_flat]
    using! metricDerivNorm_flat (openCylinder_inv_le_bufferedCylinder δ)
      d.normalizedMetric (referenceMetric δ) (referenceMetric δ) j q

theorem controlledMetric_error_lt (d : normalizedDatum g x₀ δ k) :
    metricDerivENormSupOn univ k d.controlledMetric
      ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (openCylinder δ⁻¹))
      ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (openCylinder δ⁻¹)) <
        ENNReal.ofReal δ := by
  apply lt_of_le_of_lt _ d.normalizedMetric_error_lt
  apply (metricDerivENormSupOn_le_iff _ _ _ _ _ _).mpr
  intro j hj q _
  rw [metricDerivNorm_controlledMetric]
  apply ofReal_metricDerivNorm_le_sup _ _ _ _ _ hj
  exact ⟨q.property.1.le, q.property.2.le⟩

theorem controlledMetric_cylinder_lower (d : normalizedDatum g x₀ δ k) :
    0 < 1 - Real.sqrt δ ∧ ∀ (q : openCylinder δ⁻¹) (v : TangentSpace IC q),
      (1 - Real.sqrt δ) * (roundCylinderMetric (E := E3) (n := 2)).inner q.val v v ≤
        d.controlledMetric.inner q v v := by
  constructor
  · apply sub_pos.mpr
    exact (Real.sqrt_lt d.precision_pos.le zero_le_one).mpr
      (by simpa using d.precision_lt_one)
  · intro q v
    have hl := (inner_bounds_of_metricDerivENormSupOn_lt
      ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (openCylinder δ⁻¹))
      d.controlledMetric d.controlledMetric_error_lt (mem_univ q) v).1
    change (1 - δ) * (roundCylinderMetric (E := E3) (n := 2)).inner q.val v v ≤ _ at hl
    apply le_trans _ hl
    apply mul_le_mul_of_nonneg_right _
      (metric_inner_self_nonneg (roundCylinderMetric (E := E3) (n := 2)) q.val v)
    linarith [Real.le_sqrt_self_iff.mpr d.precision_lt_one.le]

end normalizedDatum
end DifferentialGeometry.Geometry.Neck
