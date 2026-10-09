import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialLoopBase
import DifferentialGeometry.Topology.Embedding.Sphere
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingDiffeomorph
import DifferentialGeometry.Topology.Manifold.ImmersionCriterionInteriorTarget

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly.FC39P0.X135Radial
local instance complexDim_LoopX135 : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨by simp⟩

def radialLoopScale : ℂ ≃ₘ⟮𝓘(ℝ, ℂ), 𝓘(ℝ, ℂ)⟯ ℂ where
  toFun z := seamSecond (-(1 / 2 : ℝ)) • z
  invFun z := (seamSecond (-(1 / 2 : ℝ)))⁻¹ • z
  left_inv z := by
    change (seamSecond (-(1 / 2 : ℝ)))⁻¹ • (seamSecond (-(1 / 2 : ℝ)) • z) = z
    rw [smul_smul, inv_mul_cancel₀ (seamSecond_pos (by norm_num)).ne', one_smul]
  right_inv z := by
    change seamSecond (-(1 / 2 : ℝ)) • ((seamSecond (-(1 / 2 : ℝ)))⁻¹ • z) = z
    rw [smul_smul, mul_inv_cancel₀ (seamSecond_pos (by norm_num)).ne', one_smul]
  contMDiff_toFun := (contDiff_const_smul (seamSecond (-(1 / 2 : ℝ)))).contMDiff
  contMDiff_invFun := by
    change ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (fun z : ℂ => (seamSecond (-(1 / 2 : ℝ)))⁻¹ • z)
    exact (contDiff_const_smul ((seamSecond (-(1 / 2 : ℝ)))⁻¹)).contMDiff

def radialBaseComplex (b : radialCircleBase) : ℂ := modelPlaneComplex b.val.val

theorem radialBaseComplex_smooth : ContMDiff (𝓡 2) 𝓘(ℝ, ℂ) ∞ radialBaseComplex :=
  modelPlaneComplex.contDiff.contMDiff.comp (contMDiff_subtype_val.comp contMDiff_subtype_val)

theorem radialBaseComplex_embedding : Topology.IsEmbedding radialBaseComplex :=
  modelPlaneComplex.toHomeomorph.isEmbedding.comp
    (Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal)

theorem radialLoop_complex_eq : radialBaseComplex ∘ radialLoopBase =
    radialLoopScale ∘ (fun c : Circle => (c : ℂ)) := by
  funext c
  exact radialLoopBase_complex c

theorem radialLoop_complex_embedding : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℂ) ∞
    (radialBaseComplex ∘ radialLoopBase) := by
  have hs : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun c : Circle => (c : ℂ)) :=
    isSmoothEmbedding_coe_sphere (E := ℂ) (n := 1)
  have hh := DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_diffeomorph_comp
    (𝓡 1) 𝓘(ℝ, ℂ) (fun c : Circle => (c : ℂ)) hs radialLoopScale
  exact radialLoop_complex_eq.symm ▸ hh

theorem radialLoopBase_embedding : IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ radialLoopBase := by
  have he : Topology.IsEmbedding radialLoopBase :=
    radialBaseComplex_embedding.of_comp_iff.mp radialLoop_complex_embedding.isEmbedding
  apply
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_of_injective_mfderiv_of_interior_GSF
    (by simp) radialLoopBase_smooth he
  · intro c
    have hc := mfderiv_comp c
      (radialBaseComplex_smooth.mdifferentiableAt (by simp))
      (radialLoopBase_smooth.mdifferentiableAt (by simp))
    have hi := radialLoop_complex_embedding.isImmersion.mfderiv_injective (by simp) c
    have hj : Injective ((mfderiv (𝓡 2) 𝓘(ℝ, ℂ) radialBaseComplex (radialLoopBase c)).comp
        (mfderiv (𝓡 1) (𝓡 2) radialLoopBase c)) := hc ▸ hi
    exact Function.Injective.of_comp
      (f := fun v => (mfderiv (𝓡 2) 𝓘(ℝ, ℂ) radialBaseComplex (radialLoopBase c)) v)
      (g := fun v => (mfderiv (𝓡 1) (𝓡 2) radialLoopBase c) v) hj
  · intro c
    exact BoundarylessManifold.isInteriorPoint

theorem radialLoopBase_range : range radialLoopBase =
    {b : radialCircleBase | ‖b.val.val‖ ^ 2 = (3 / 4 : ℝ)} := by
  ext b
  constructor
  · rintro ⟨c, rfl⟩
    exact radialLoopBase_norm c
  · intro hb
    change ‖b.val.val‖ ^ 2 = (3 / 4 : ℝ) at hb
    let z : ℂ := modelPlaneComplex b.val.val
    have hn : ‖z‖ = Real.sqrt (3 / 4 : ℝ) := by
      rw [← hb, Real.sqrt_sq (norm_nonneg b.val.val)]
      exact modelPlaneComplex.norm_map _
    have hr : seamSecond (-(1 / 2 : ℝ)) = Real.sqrt (3 / 4 : ℝ) := by
      rw [seamSecond, seamClamp_of_mem (by norm_num) (by norm_num)]
      norm_num
    refine ⟨unitOf z, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply modelPlaneComplex.injective
    rw [radialLoopBase_complex, hr, ← hn]
    exact norm_smul_unitOf z

theorem radialLoopFace_eq : Subtype.val '' (radialCircleProjection ⁻¹' range radialLoopBase) =
    {p : carrier.Carrier | height p = -(1 / 2 : ℝ)} := by
  rw [radialLoopBase_range]
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hn : ‖(radialCircleProjection q).val.val‖ ^ 2 = (3 / 4 : ℝ) := hq
    have hh := radialCircleProjection_height q
    change height q.val = -(1 / 2 : ℝ)
    rw [hn] at hh
    linarith
  · intro hp
    change height p = -(1 / 2 : ℝ) at hp
    have hd : p ∈ radialCircleDomain := by
      change -1 < height p ∧ height p < 0
      rw [hp]
      norm_num
    refine ⟨⟨p, hd⟩, ?_, rfl⟩
    have hh := radialCircleProjection_height ⟨p, hd⟩
    change ‖(radialCircleProjection ⟨p, hd⟩).val.val‖ ^ 2 = (3 / 4 : ℝ)
    change height p = 1 - 2 * ‖(radialCircleProjection ⟨p, hd⟩).val.val‖ ^ 2 at hh
    rw [hp] at hh
    linarith

end GC.GraphManifold.Assembly.FC39P0.X135Radial
