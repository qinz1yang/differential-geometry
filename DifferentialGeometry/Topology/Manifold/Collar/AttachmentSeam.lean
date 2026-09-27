import DifferentialGeometry.Topology.Collar.AttachmentSeam
import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

open Set Function Manifold Topology
open scoped ContDiff
set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Manifold.Collar

local instance : Fact ((-1 : ℝ) < 1) := ⟨by norm_num⟩

theorem attachmentSeam_embedding_contMDiff
    {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
    {F G M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] [TopologicalSpace M] [ChartedSpace G M]
    {J : ModelWithCorners ℝ E H} {I : ModelWithCorners ℝ F G}
    {ε : ℝ} [Fact ((0 : ℝ) < ε)]
    (f : C(B, M)) (c : C(B × Icc (0 : ℝ) ε, M)) (a : Icc (0 : ℝ) ε)
    (ha : 0 < a.val) (h2a : 2 * a.val ≤ ε)
    (hzero : ∀ p, c (p, ⟨0, ⟨le_rfl, a.property.1.trans a.property.2⟩⟩) = f p)
    (hc : IsEmbedding c) (hcs : ContMDiff (J.prod (𝓡∂ 1)) I ∞ c)
    (σ : C(Icc (0 : ℝ) ε, Icc (0 : ℝ) ε))
    (hσnear : ∀ t : Icc (0 : ℝ) ε, t.val ≤ a.val → (σ t).val = t.val + a.val)
    (h : DifferentialGeometry.Topology.MappingCylinder f ≃ₜ M)
    (hO : ∀ x, h (DifferentialGeometry.Topology.mappingCylinderOriginal f x) =
      DifferentialGeometry.Topology.Collar.rescale c hc σ x)
    (hP : ∀ q : B × Icc (0 : ℝ) 1, h (DifferentialGeometry.Topology.mappingCylinderProduct f q) =
      c (q.1, ⟨a.val * (1 - q.2.val),
        ⟨mul_nonneg a.property.1 (sub_nonneg.mpr q.2.property.2), by
          nlinarith [q.2.property.1, a.property.1, a.property.2]⟩⟩)) :
    IsEmbedding (DifferentialGeometry.Topology.Collar.attachmentSeam f c a hzero) ∧
      ContMDiff (J.prod (𝓡∂ 1)) I ∞
        (fun q => h (DifferentialGeometry.Topology.Collar.attachmentSeam f c a hzero q)) := by
  let φ : Icc (-1 : ℝ) 1 → Icc (0 : ℝ) ε :=
    fun t => ⟨a.val * (1 - t.val),
      mul_nonneg a.property.1 (sub_nonneg.mpr t.property.2), by
        nlinarith [t.property.1, a.property.1]⟩
  have hφ : ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ φ := by
    intro t
    apply (ContMDiffAt.iff_comp_isImmersionAtOfComplement (f := φ)
      (isImmersionOfComplement_subtypeVal_Icc (x := (0 : ℝ)) (y := ε) (n := ∞) (φ t))).mpr
    refine ⟨by fun_prop, ?_⟩
    have hlin : ContDiff ℝ ∞ (fun t : ℝ => a.val * (1 - t)) := by fun_prop
    exact hlin.contMDiff.contMDiffAt.comp t
      (contMDiff_subtypeVal_Icc (x := (-1 : ℝ)) (y := 1)).contMDiffAt
  have hφinj : Injective φ := by
    intro s t hh
    have ht := congrArg Subtype.val hh
    apply Subtype.ext
    change a.val * (1 - s.val) = a.val * (1 - t.val) at ht
    nlinarith
  have hφe : IsEmbedding φ := (hφ.continuous.isClosedEmbedding hφinj).isEmbedding
  have heq (q : B × Icc (-1 : ℝ) 1) :
      h (DifferentialGeometry.Topology.Collar.attachmentSeam f c a hzero q) = c (q.1, φ q.2) :=
    DifferentialGeometry.Topology.Collar.attachmentSeam_realization f c a hzero hc h2a σ hσnear h hO hP q
  constructor
  · apply h.isEmbedding.of_comp_iff.mp
    have hh := hc.comp (IsEmbedding.id.prodMap hφe)
    convert hh using 1
    exact funext heq
  · exact (hcs.comp (contMDiff_id.prodMap hφ)).congr heq

end DifferentialGeometry.Manifold.Collar
