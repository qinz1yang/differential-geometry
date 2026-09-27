import DifferentialGeometry.Geometry.Neck.BufferedRotation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckMarkSideBridge
import DifferentialGeometry.Geometry.Neck.Recentering

noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
private instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp [ThreeSpace]⟩
private instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric ThreeModel M} {δ : ℝ} {k : ℕ}

namespace NormalizedNeck

def rotatedDatum (N : NormalizedNeck g δ k) (e : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
    (he : sphereDiffeo (n := 2) e spherePoint = N.sphereMark) (side : Bool) :
    normalizedDatum g N.center δ k := by
  let ρ := bufferedCylinderRotation δ e
  let H : SmoothRiemannianMetric ((𝓡 2).prod 𝓘(ℝ)) (bufferedCylinder δ) := N.normalizedMetric
  have hH (q : bufferedCylinder δ) (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) q) :
      H.inner q v w = N.scale * g.inner (N.chart q)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ)) ThreeModel N.chart q v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ)) ThreeModel N.chart q w) := N.normalized_inner q v w
  let φ : bufferedCylinder δ → M := N.chart ∘ ρ
  have hφ : ContMDiff NeckCylinderModel ThreeModel ∞ φ := N.chart_smooth.contMDiff.comp ρ.contMDiff
  have hi : Injective φ := N.chart_smooth.isEmbedding.injective.comp ρ.injective
  have himm : ∀ q, Injective (mfderiv NeckCylinderModel ThreeModel φ q) := by
    intro q
    rw [show φ = N.chart ∘ ρ from rfl, mfderiv_comp q
      (N.chart_smooth.contMDiff.mdifferentiable (by simp) _) (ρ.contMDiff.mdifferentiable (by simp) _)]
    exact (injective_mfderiv_of_isImmersionAt NeckCylinderModel ThreeModel N.chart _
      (N.chart_smooth.isImmersion.isImmersionAt _)).comp
      (ρ.mfderivToContinuousLinearEquiv (by simp) q).injective
  have hpos : 0 < metricScalarAt g N.center := N.scale_scalar ▸ N.scale_pos
  have hloc := isLocalDiffeomorph_of_injective_mfderiv φ hφ himm (by simp [ThreeSpace])
  have hmetric : pullbackMetricOfInjectiveLocalDiffeomorph (scaleMetric _ hpos g) φ hloc hi =
      Diffeomorph.pullbackMetric H ρ := by
    apply SmoothRiemannianMetric.ext_inner
    intro q v w
    rw [pullbackMetricOfInjectiveLocalDiffeomorph_inner, scaleMetric_inner,
      Diffeomorph.pullbackMetric_inner, hH, N.scale_scalar]
    rw [show φ = N.chart ∘ ρ from rfl, mfderiv_comp q
      (N.chart_smooth.contMDiff.mdifferentiable (by simp) _) (ρ.contMDiff.mdifferentiable (by simp) _)]
    rfl
  refine { precision_pos := N.delta_pos
           precision_lt_one := N.delta_lt_one
           map := φ
           smooth := hφ
           injective := hi
           immersion := himm
           center_eq := ?_
           scalar_pos := hpos
           retainedSide := side
           error_lt := ?_ }
  · change N.chart (ρ (cylinderCenter δ N.delta_pos)) = N.center
    convert N.marked using 1
    congr 1
    apply Subtype.ext
    change (bufferedCylinderRotation δ e (cylinderCenter δ N.delta_pos)).val = _
    rw [bufferedCylinderRotation_apply]
    exact Prod.ext he rfl
  · change metricDerivENormSupOn (controlledCylinder δ) k
      (pullbackMetricOfInjectiveLocalDiffeomorph (scaleMetric _ hpos g) φ hloc hi)
      (referenceMetric δ) (referenceMetric δ) < _
    rw [hmetric]
    have hrot := metricDerivENormSupOn_bufferedCylinderRotation δ e H (referenceMetric δ) k
    rw [pullback_referenceMetric_bufferedCylinderRotation] at hrot
    change metricDerivENormSupOn (controlledCylinder δ) k
      (Diffeomorph.pullbackMetric H (bufferedCylinderRotation δ e))
      (referenceMetric δ) (referenceMetric δ) < _
    rw [hrot, metricDerivENormSupOn_eq_ofReal_of_isCompact (isCompact_controlledCylinder δ)]
    apply (ENNReal.ofReal_lt_ofReal_iff N.delta_pos).mpr
    have hset : controlledCylinder δ = neckClosedTest δ := by ext q; rfl
    rw [hset, referenceMetric_eq_roundCylinderMetric_neckBuffer]
    exact N.closeness

@[simp] theorem rotatedDatum_map (N : NormalizedNeck g δ k)
    (e : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace) (he : sphereDiffeo (n := 2) e spherePoint = N.sphereMark)
    (side : Bool) : (N.rotatedDatum e he side).map = N.chart ∘ bufferedCylinderRotation δ e := rfl

@[simp] theorem rotatedDatum_retainedSide (N : NormalizedNeck g δ k)
    (e : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace) (he : sphereDiffeo (n := 2) e spherePoint = N.sphereMark)
    (side : Bool) : (N.rotatedDatum e he side).retainedSide = side := rfl

theorem exists_rotatedDatum (N : NormalizedNeck g δ k) (side : Bool) :
    ∃ e : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace, LinearMap.det e.toLinearMap = 1 ∧
      sphereDiffeo (n := 2) e spherePoint = N.sphereMark ∧
      ∃ d : normalizedDatum g N.center δ k,
        d.map = N.chart ∘ bufferedCylinderRotation δ e ∧ d.retainedSide = side := by
  obtain ⟨e, hdet, he⟩ := exists_sphereDiffeo_det_one (n := 2) (by norm_num) spherePoint N.sphereMark
  exact ⟨e, hdet, he, N.rotatedDatum e he side, rfl, rfl⟩

theorem rotatedDatum_range (N : NormalizedNeck g δ k)
    (e : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace) (he : sphereDiffeo (n := 2) e spherePoint = N.sphereMark)
    (side : Bool) : range (N.rotatedDatum e he side).map = range N.chart := by
  rw [rotatedDatum_map]
  exact (bufferedCylinderRotation δ e).surjective.range_comp N.chart

theorem rotatedDatum_image_height (N : NormalizedNeck g δ k)
    (e : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace) (he : sphereDiffeo (n := 2) e spherePoint = N.sphereMark)
    (side : Bool) (S : Set ℝ) :
    (N.rotatedDatum e he side).map '' {q : bufferedCylinder δ | q.val.2 ∈ S} =
      N.chart '' {q : neckBuffer δ | q.val.2 ∈ S} := by
  let F : bufferedCylinder δ → M := N.chart
  change (N.rotatedDatum e he side).map '' _ = F '' {q : bufferedCylinder δ | q.val.2 ∈ S}
  have hmap : (N.rotatedDatum e he side).map = F ∘ bufferedCylinderRotation δ e := rfl
  rw [hmap, image_comp, image_bufferedCylinderRotation_height]

theorem rotatedDatum_normalizedMetric (N : NormalizedNeck g δ k)
    (e : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace) (he : sphereDiffeo (n := 2) e spherePoint = N.sphereMark)
    (side : Bool) :
    let H : SmoothRiemannianMetric ((𝓡 2).prod 𝓘(ℝ)) (bufferedCylinder δ) := N.normalizedMetric
    (N.rotatedDatum e he side).normalizedMetric = Diffeomorph.pullbackMetric H (bufferedCylinderRotation δ e) := by
  let H : SmoothRiemannianMetric ((𝓡 2).prod 𝓘(ℝ)) (bufferedCylinder δ) := N.normalizedMetric
  have hH (q : bufferedCylinder δ) (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) q) :
      H.inner q v w = N.scale * g.inner (N.chart q)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ)) ThreeModel N.chart q v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ)) ThreeModel N.chart q w) := N.normalized_inner q v w
  let F : bufferedCylinder δ → M := N.chart
  have hF : ContMDiff ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ F := N.chart_smooth.contMDiff
  change (N.rotatedDatum e he side).normalizedMetric = Diffeomorph.pullbackMetric H (bufferedCylinderRotation δ e)
  apply SmoothRiemannianMetric.ext_inner
  intro q v w
  rw [normalizedDatum.normalizedMetric_inner]
  change metricScalarAt g N.center * g.inner ((F ∘ bufferedCylinderRotation δ e) q)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ)) ThreeModel (F ∘ bufferedCylinderRotation δ e) q v)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ)) ThreeModel (F ∘ bufferedCylinderRotation δ e) q w) =
      (Diffeomorph.pullbackMetric H (bufferedCylinderRotation δ e)).inner q v w
  rw [Diffeomorph.pullbackMetric_inner, hH, N.scale_scalar]
  rw [mfderiv_comp q (hF.mdifferentiable (by simp) _)
    ((bufferedCylinderRotation δ e).contMDiff.mdifferentiable (by simp) _)]
  rfl

theorem rotatedDatum_offsetPoint (N : NormalizedNeck g δ k)
    (e : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace) (he : sphereDiffeo (n := 2) e spherePoint = N.sphereMark)
    (side : Bool) {σ : ℝ} (hσ : σ ^ 2 = 1) :
    (N.rotatedDatum e he side).offsetPoint hσ =
      N.chart ⟨(N.sphereMark, σ), offset_mem_bufferedCylinder N.delta_pos hσ N.sphereMark⟩ := by
  change N.chart (bufferedCylinderRotation δ e
    ⟨(spherePoint, σ), offset_mem_bufferedCylinder N.delta_pos hσ spherePoint⟩) = _
  apply congrArg N.chart
  apply Subtype.ext
  rw [bufferedCylinderRotation_apply]
  exact Prod.ext he rfl

theorem rotatedDatum_offset_scalar_bounds (N : NormalizedNeck g δ k)
    (e : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace) (he : sphereDiffeo (n := 2) e spherePoint = N.sphereMark)
    (side : Bool) (hk : 2 ≤ k) (hδ : δ ≤ 1 / 8646) {σ : ℝ} (hσ : σ ^ 2 = 1) :
    N.scale / 2 ≤ metricScalarAt g ((N.rotatedDatum e he side).offsetPoint hσ) ∧
      metricScalarAt g ((N.rotatedDatum e he side).offsetPoint hσ) ≤ (3 / 2 : ℝ) * N.scale := by
  rw [rotatedDatum_offsetPoint]
  have hfit : (⟨(N.sphereMark, σ), offset_mem_bufferedCylinder N.delta_pos hσ N.sphereMark⟩ : neckBuffer δ) ∈
      neckClosedTest δ := by
    change -δ⁻¹ ≤ σ ∧ σ ≤ δ⁻¹
    have hi := (one_le_inv₀ N.delta_pos).mpr N.delta_lt_one.le
    rcases sq_eq_one_iff.mp hσ with rfl | rfl <;> constructor <;> linarith
  have hr := N.abs_scalar_ratio_sub_one_le hk (by linarith) _ hfit
  have hlo : (1 / 2 : ℝ) ≤ metricScalarAt g (N.chart
      ⟨(N.sphereMark, σ), offset_mem_bufferedCylinder N.delta_pos hσ N.sphereMark⟩) / N.scale := by
    have h := (abs_le.mp hr).1
    linarith
  have hhi : metricScalarAt g (N.chart
      ⟨(N.sphereMark, σ), offset_mem_bufferedCylinder N.delta_pos hσ N.sphereMark⟩) / N.scale ≤ (3 / 2 : ℝ) := by
    have h := (abs_le.mp hr).2
    linarith
  exact ⟨by linarith [(le_div_iff₀ N.scale_pos).mp hlo],
    (div_le_iff₀ N.scale_pos).mp hhi⟩

end NormalizedNeck
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
