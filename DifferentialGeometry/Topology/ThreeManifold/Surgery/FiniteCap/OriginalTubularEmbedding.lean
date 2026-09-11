import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingLocalDiffeomorph
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingOpenTarget
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CoreAmbientCoordinates
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.SphericalCutCore
import Mathlib.Geometry.Manifold.Instances.Icc

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev TubeE3 := EuclideanSpace ℝ (Fin 3)
private abbrev TubeE2 := EuclideanSpace ℝ (Fin 2)
private abbrev TubeS2 := Metric.sphere (0 : TubeE3) 1
private abbrev TubeIR := (𝓡 2).prod (𝓡∂ 1)
private abbrev TubeIC := (𝓡 2).prod 𝓘(ℝ)
private local instance : Fact (Module.finrank ℝ TubeE3 = 2 + 1) := ⟨by simp⟩
private local instance : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
variable {M : Type*} [TopologicalSpace M] {δ : ℝ}

private def originalTubularDomainMap (hδ : 0 < δ) (hδ1 : δ < 1) :
    TubeS2 × Icc (-2 : ℝ) 2 → bufferedCylinder δ := fun q =>
  ⟨(q.1, q.2.val), by
    have hi : 1 < δ⁻¹ := (one_lt_inv₀ hδ).mpr hδ1
    change -δ⁻¹ - 1 < q.2.val ∧ q.2.val < δ⁻¹ + 1
    constructor <;> linarith [q.2.property.1, q.2.property.2]⟩

def originalTubularMap (hδ : 0 < δ) (hδ1 : δ < 1) (f : bufferedCylinder δ → M) :
    TubeS2 × Icc (-2 : ℝ) 2 → M := f ∘ originalTubularDomainMap hδ hδ1

omit [TopologicalSpace M] in
theorem range_originalTubularMap_subset (hδ : 0 < δ) (hδ1 : δ < 1) (f : bufferedCylinder δ → M) :
    range (originalTubularMap hδ hδ1 f) ⊆ range f := range_comp_subset_range (originalTubularDomainMap hδ hδ1) f

omit [TopologicalSpace M] in
theorem originalTubularMap_central_image (hδ : 0 < δ) (hδ1 : δ < 1) (f : bufferedCylinder δ → M) :
    originalTubularMap hδ hδ1 f '' {q : TubeS2 × Icc (-2 : ℝ) 2 | q.2.val ∈ Ioo (-1 : ℝ) 1} = removedSlab f := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨originalTubularDomainMap hδ hδ1 q, hq, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    let r : TubeS2 × Icc (-2 : ℝ) 2 := (q.val.1, ⟨q.val.2, by
      change -1 < q.val.2 ∧ q.val.2 < 1 at hq
      constructor <;> linarith [hq.1, hq.2]⟩)
    refine ⟨r, hq, ?_⟩
    exact congrArg f (Subtype.ext rfl)

section Smooth
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [ChartedSpace H M] [IsManifold I ∞ M]

theorem originalTubularMap_isSmoothEmbedding (hdim : Module.finrank ℝ E = 3)
    (hδ : 0 < δ) (hδ1 : δ < 1) (f : bufferedCylinder δ → M)
    (hf : _root_.Topology.IsOpenEmbedding f) (hs : IsLocalDiffeomorph TubeIC I ∞ f) :
    IsSmoothEmbedding TubeIR I ∞ (originalTubularMap hδ hδ1 f) := by
  let : Nonempty H := ⟨I.toHomeomorph.symm 0⟩
  let j := originalTubularDomainMap hδ hδ1
  have hj : IsSmoothEmbedding TubeIR TubeIC ∞ j :=
    isSmoothEmbedding_intoOpen TubeIR TubeIC (bufferedCylinder δ) j
      ((IsSmoothEmbedding.id : IsSmoothEmbedding (𝓡 2) (𝓡 2) ∞ (id : TubeS2 → TubeS2)).prodMap
        (isSmoothEmbedding_subtypeVal_Icc (x := (-2 : ℝ)) (y := 2)))
  let ψ := coreAmbientNormalizingHomeomorph I hdim 0 1 (by norm_num)
  let B : (ModelProd TubeE2 ℝ) ≃ₘ⟮TubeIC, I⟯ H :=
    { toEquiv := ψ.toEquiv
      contMDiff_toFun := coreAmbientNormalizingHomeomorph_contMDiff I hdim 0 1 (by norm_num)
      contMDiff_invFun := coreAmbientNormalizingHomeomorph_symm_contMDiff I hdim 0 1 (by norm_num) }
  let A := (coreAmbientLinearEquiv hdim).symm
  have hA (y : ModelProd TubeE2 ℝ) : I (B y) = A (TubeIC y) := by
    change I (ψ y) = (coreAmbientLinearEquiv hdim).symm (y.1, y.2)
    have h := coreAmbientNormalizingHomeomorph_extend I hdim 0 1 (by norm_num) y
    simpa only [zero_add, one_mul] using h
  exact isSmoothEmbedding_openLocalDiffeomorph_comp TubeIR TubeIC I j hj f hf hs B A hA
end Smooth

variable {ι : Type*} {precision : ι → ℝ}
omit [TopologicalSpace M] in
theorem originalTubularMap_pairwise_disjoint (hδ : ∀ i, 0 < precision i) (hδ1 : ∀ i, precision i < 1)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))) :
    Pairwise (fun i j => Disjoint (range (originalTubularMap (hδ i) (hδ1 i) (f i)))
      (range (originalTubularMap (hδ j) (hδ1 j) (f j)))) := by
  intro i j hij
  exact (hdisj hij).mono (range_originalTubularMap_subset (hδ i) (hδ1 i) (f i))
    (range_originalTubularMap_subset (hδ j) (hδ1 j) (f j))

omit [TopologicalSpace M] in
theorem cutCore_eq_originalTubularComplement (hδ : ∀ i, 0 < precision i) (hδ1 : ∀ i, precision i < 1)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) :
    cutCore f = (⋃ i, originalTubularMap (hδ i) (hδ1 i) (f i) ''
      {q : TubeS2 × Icc (-2 : ℝ) 2 | q.2.val ∈ Ioo (-1 : ℝ) 1})ᶜ := by
  simp only [originalTubularMap_central_image]
  rfl
end DifferentialGeometry.Topology.ThreeManifold.Surgery
