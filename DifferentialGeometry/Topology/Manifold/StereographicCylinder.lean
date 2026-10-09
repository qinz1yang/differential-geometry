import DifferentialGeometry.Topology.Manifold.RoundCylinderOrientation
import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import DifferentialGeometry.Geometry.Metric.PolarCoordinates

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.Manifold
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E4 := EuclideanSpace ℝ (Fin 4)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev S3 := Metric.sphere (0 : E4) 1
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

def stereographicCylinderMap (v : S3) (q : S2 × ℝ) : S3 :=
  (stereographic' 3 v).symm (exponentialPolarMap q)

theorem stereographicCylinderMap_coordinates (v : S3) (q : S2 × ℝ) :
    stereographic' 3 v (stereographicCylinderMap v q) = Real.exp q.2 • (q.1 : E3) :=
  (stereographic' 3 v).right_inv (by simp)

theorem stereographicCylinderMap_coordinate_norm (v : S3) (q : S2 × ℝ) :
    ‖stereographic' 3 v (stereographicCylinderMap v q)‖ = Real.exp q.2 := by
  rw [stereographicCylinderMap_coordinates, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), norm_eq_of_mem_sphere, mul_one]

private theorem stereo_inverse_local (v : S3) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (stereographic' 3 v).symm := by
  have he : chartAt E3 (-v) = stereographic' 3 v := by
    change stereographic' 3 (-(-v)) = stereographic' 3 v
    rw [neg_neg]
  let D : PartialDiffeomorph (𝓡 3) (𝓡 3) S3 E3 ∞ :=
    { toPartialEquiv := (chartAt E3 (-v)).toPartialEquiv
      open_source := (chartAt E3 (-v)).open_source
      open_target := (chartAt E3 (-v)).open_target
      contMDiffOn_toFun := contMDiffOn_chart
      contMDiffOn_invFun := contMDiffOn_chart_symm }
  intro x
  have h := PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ D.symm
    (show x ∈ D.target from by change x ∈ (chartAt E3 (-v)).target; rw [he]; simp)
  change IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (chartAt E3 (-v)).symm x at h
  simpa only [he] using h

theorem stereographicCylinderMap_isLocalDiffeomorph (v : S3) :
    IsLocalDiffeomorph IC (𝓡 3) ∞ (stereographicCylinderMap v) := by
  have hp : IsLocalDiffeomorph IC (𝓡 3) ∞ exponentialPolarMap :=
    isLocalDiffeomorph_of_injective_mfderiv _ exponentialPolarMap_contMDiff
      (fun q => (exponentialPolarMap_mfderiv_bijective q).injective) (by simp)
  intro q
  exact (hp q).comp (𝓡 3) S3 (stereo_inverse_local v (exponentialPolarMap q))

private theorem exponential_injective : Injective exponentialPolarMap := by
  intro a b h
  have hn := congrArg norm h
  change ‖euclideanPolarMap (positiveCylinderReparametrization a)‖ =
    ‖euclideanPolarMap (positiveCylinderReparametrization b)‖ at hn
  rw [euclideanPolarMap_norm_of_pos (Real.exp_pos a.2),
    euclideanPolarMap_norm_of_pos (Real.exp_pos b.2)] at hn
  have ht : a.2 = b.2 := Real.exp_injective hn
  apply Prod.ext _ ht
  apply Subtype.ext
  change Real.exp a.2 • (a.1 : E3) = Real.exp b.2 • (b.1 : E3) at h
  rw [ht] at h
  exact (smul_right_injective E3 (Real.exp_ne_zero b.2)) h

theorem stereographicCylinderMap_isOpenEmbedding (v : S3) :
    _root_.Topology.IsOpenEmbedding (stereographicCylinderMap v) := by
  have hi : _root_.Topology.IsOpenEmbedding (stereographic' 3 v).symm :=
    (stereographic' 3 v).symm.isOpenEmbedding (by simp)
  exact .of_continuous_injective_isOpenMap
    (stereographicCylinderMap_isLocalDiffeomorph v).contMDiff.continuous
    (hi.injective.comp exponential_injective)
    (stereographicCylinderMap_isLocalDiffeomorph v).isOpenMap

theorem stereographicCylinderMap_ne_pole (v : S3) (q : S2 × ℝ) :
    stereographicCylinderMap v q ≠ v := by
  have h := (stereographic' 3 v).map_target
    (show exponentialPolarMap q ∈ (stereographic' 3 v).target by simp)
  simpa only [stereographicCylinderMap, stereographic'_source, mem_compl_iff, mem_singleton_iff] using h
end DifferentialGeometry.Topology.Manifold
