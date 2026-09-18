import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeck
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.EqualDimensionImmersion
import DifferentialGeometry.Topology.SphereSeparation.BicollarLineReparametrization
import DifferentialGeometry.Topology.SphereSeparation.BicollarCompactSides

set_option autoImplicit false

noncomputable section

open Manifold Set
open scoped Manifold ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

private local instance spatialTopologySphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

private local instance spatialTopologySphereConnected : ConnectedSpace SpatialNeckSphere := by
  apply Subtype.connectedSpace
  apply isConnected_sphere
  · rw [← Module.finrank_eq_rank]
    norm_num
  · norm_num

private def spatialNeckLineHomeomorph (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    SpatialNeckCylinder ≃ₜ spatialNeckBuffer epsilon :=
  (bicollarLineHomeomorph (A := SpatialNeckSphere) (epsilon⁻¹ + 1) (by positivity)).trans
    (Homeomorph.setCongr (by
      ext x
      change (-(epsilon⁻¹ + 1) < x.2 ∧ x.2 < epsilon⁻¹ + 1) ↔
        (-epsilon⁻¹ - 1 < x.2 ∧ x.2 < epsilon⁻¹ + 1)
      simp only [neg_add, sub_eq_add_neg]))

private theorem spatialNeckLine_center (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (y : SpatialNeckSphere) :
    spatialNeckLineHomeomorph epsilon hepsilon (y, 0) =
      spatialNeckCentralPoint epsilon hepsilon y := by
  apply Subtype.ext
  exact bicollarLineHomeomorph_center (epsilon⁻¹ + 1) (by positivity) y

private theorem spatialNeckLine_negative_iff (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (p : SpatialNeckCylinder) :
    (spatialNeckLineHomeomorph epsilon hepsilon p).val.2 < 0 ↔ p.2 < 0 :=
  bicollarLineHomeomorph_negative_iff (epsilon⁻¹ + 1) (by positivity) p.1 p.2

private theorem spatialNeckLine_positive_iff (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (p : SpatialNeckCylinder) :
    0 < (spatialNeckLineHomeomorph epsilon hepsilon p).val.2 ↔ 0 < p.2 :=
  bicollarLineHomeomorph_positive_iff (epsilon⁻¹ + 1) (by positivity) p.1 p.2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]

namespace SpatialNeckWitness

variable {h : SmoothRiemannianMetric I N} {yStar : SpatialNeckSphere}
  {p : N} {epsilon : ℝ} (W : SpatialNeckWitness h yStar p epsilon)

theorem embedding_isOpenEmbedding : Topology.IsOpenEmbedding W.embedding := by
  apply smoothEmbedding_isOpenEmbedding_of_finrank_eq _ W.smooth_embedding
  simpa [Module.finrank_prod] using W.dimension_three.symm

theorem compact_end_sides_of_homeomorph (e : N ≃ₜ E) :
    ∃ B U : Set N,
      IsConnected B ∧ IsConnected U ∧ IsOpen B ∧ IsOpen U ∧ Disjoint B U ∧
      B ∪ U = W.centralSphereᶜ ∧
      IsCompact (closure B) ∧ ¬ IsCompact (closure U) ∧
      closure B = B ∪ W.centralSphere ∧ interior (closure B) = B ∧
      frontier (closure B) = W.centralSphere ∧ frontier U = W.centralSphere ∧
      (((∀ x : spatialNeckBuffer epsilon, x.val.2 < 0 → W.embedding x ∈ B) ∧
        (∀ x : spatialNeckBuffer epsilon, 0 < x.val.2 → W.embedding x ∈ U)) ∨
       ((∀ x : spatialNeckBuffer epsilon, x.val.2 < 0 → W.embedding x ∈ U) ∧
        (∀ x : spatialNeckBuffer epsilon, 0 < x.val.2 → W.embedding x ∈ B))) := by
  let η := spatialNeckLineHomeomorph epsilon W.epsilon_pos
  let φ : SpatialNeckCylinder → N := W.embedding ∘ η
  have hφ : Topology.IsOpenEmbedding φ := W.embedding_isOpenEmbedding.comp η.isOpenEmbedding
  have hdim : 2 ≤ Module.finrank ℝ E := by rw [W.dimension_three]; norm_num
  obtain ⟨B, U, hB, hU, hBop, hUop, hBU, hcover, hBc, hUnc, hcl, hint, hfr, hUfr, hsides⟩ :=
    exists_bicollar_compact_end_sides hdim e φ hφ
  have hcenter : range (fun y => φ (y, 0)) = W.centralSphere := by
    rw [W.centralSphere_eq_range]
    congr 1
    funext y
    change W.embedding (η (y, 0)) = W.centralMap y
    rw [spatialNeckLine_center]
    rfl
  have hneg (T : Set N) (hT : ∀ y z, z < 0 → φ (y, z) ∈ T) :
      ∀ x : spatialNeckBuffer epsilon, x.val.2 < 0 → W.embedding x ∈ T := by
    intro x hx
    have hxs : (η (η.symm x)).val.2 < 0 := by rw [η.apply_symm_apply]; exact hx
    have ht : (η.symm x).2 < 0 :=
      (spatialNeckLine_negative_iff epsilon W.epsilon_pos (η.symm x)).mp hxs
    have hmem := hT (η.symm x).1 (η.symm x).2 ht
    change W.embedding (η (η.symm x)) ∈ T at hmem
    rwa [η.apply_symm_apply] at hmem
  have hpos (T : Set N) (hT : ∀ y z, 0 < z → φ (y, z) ∈ T) :
      ∀ x : spatialNeckBuffer epsilon, 0 < x.val.2 → W.embedding x ∈ T := by
    intro x hx
    have hxs : 0 < (η (η.symm x)).val.2 := by rw [η.apply_symm_apply]; exact hx
    have ht : 0 < (η.symm x).2 :=
      (spatialNeckLine_positive_iff epsilon W.epsilon_pos (η.symm x)).mp hxs
    have hmem := hT (η.symm x).1 (η.symm x).2 ht
    change W.embedding (η (η.symm x)) ∈ T at hmem
    rwa [η.apply_symm_apply] at hmem
  rw [hcenter] at hcover hcl hfr hUfr
  refine ⟨B, U, hB, hU, hBop, hUop, hBU, hcover, hBc, hUnc, hcl, hint, hfr, hUfr, ?_⟩
  rcases hsides with ⟨hn, hp⟩ | ⟨hn, hp⟩
  · exact Or.inl ⟨hneg B hn, hpos U hp⟩
  · exact Or.inr ⟨hneg U hn, hpos B hp⟩

theorem compact_end_sides_of_homotopic_disjoint
    [ConnectedSpace N] [LocallyConnectedSpace N] [NoncompactSpace N]
    (r : C(N, N)) (hr : ContinuousMap.Homotopic r (ContinuousMap.id N))
    (hdisjoint : Disjoint (range r) W.centralSphere)
    (hends : ¬ DifferentialGeometry.Geometry.Topology.HasAtLeastEnds N 2) :
    ∃ B U : Set N,
      IsConnected B ∧ IsConnected U ∧ IsOpen B ∧ IsOpen U ∧ Disjoint B U ∧
      B ∪ U = W.centralSphereᶜ ∧
      IsCompact (closure B) ∧ ¬ IsCompact (closure U) ∧
      closure B = B ∪ W.centralSphere ∧ interior (closure B) = B ∧
      frontier (closure B) = W.centralSphere ∧ frontier U = W.centralSphere ∧
      (((∀ x : spatialNeckBuffer epsilon, x.val.2 < 0 → W.embedding x ∈ B) ∧
        (∀ x : spatialNeckBuffer epsilon, 0 < x.val.2 → W.embedding x ∈ U)) ∨
       ((∀ x : spatialNeckBuffer epsilon, x.val.2 < 0 → W.embedding x ∈ U) ∧
        (∀ x : spatialNeckBuffer epsilon, 0 < x.val.2 → W.embedding x ∈ B))) := by
  let η := spatialNeckLineHomeomorph epsilon W.epsilon_pos
  let φ : SpatialNeckCylinder → N := W.embedding ∘ η
  have hφ : Topology.IsOpenEmbedding φ := W.embedding_isOpenEmbedding.comp η.isOpenEmbedding
  have hcenter : range (fun y => φ (y, 0)) = W.centralSphere := by
    rw [W.centralSphere_eq_range]
    congr 1
    funext y
    change W.embedding (η (y, 0)) = W.centralMap y
    rw [spatialNeckLine_center]
    rfl
  have hdisjointφ : Disjoint (range r) (range (fun y => φ (y, 0))) := by
    rwa [hcenter]
  obtain ⟨B, U, hB, hU, hBop, hUop, hBU, hcover, hBc, hUnc, hcl, hint, hfr, hUfr, hsides⟩ :=
    exists_bicollar_compact_end_sides_of_homotopic_disjoint φ hφ r hr hdisjointφ hends
  have hneg (T : Set N) (hT : ∀ y z, z < 0 → φ (y, z) ∈ T) :
      ∀ x : spatialNeckBuffer epsilon, x.val.2 < 0 → W.embedding x ∈ T := by
    intro x hx
    have hxs : (η (η.symm x)).val.2 < 0 := by rw [η.apply_symm_apply]; exact hx
    have ht : (η.symm x).2 < 0 :=
      (spatialNeckLine_negative_iff epsilon W.epsilon_pos (η.symm x)).mp hxs
    have hmem := hT (η.symm x).1 (η.symm x).2 ht
    change W.embedding (η (η.symm x)) ∈ T at hmem
    rwa [η.apply_symm_apply] at hmem
  have hpos (T : Set N) (hT : ∀ y z, 0 < z → φ (y, z) ∈ T) :
      ∀ x : spatialNeckBuffer epsilon, 0 < x.val.2 → W.embedding x ∈ T := by
    intro x hx
    have hxs : 0 < (η (η.symm x)).val.2 := by rw [η.apply_symm_apply]; exact hx
    have ht : 0 < (η.symm x).2 :=
      (spatialNeckLine_positive_iff epsilon W.epsilon_pos (η.symm x)).mp hxs
    have hmem := hT (η.symm x).1 (η.symm x).2 ht
    change W.embedding (η (η.symm x)) ∈ T at hmem
    rwa [η.apply_symm_apply] at hmem
  rw [hcenter] at hcover hcl hfr hUfr
  refine ⟨B, U, hB, hU, hBop, hUop, hBU, hcover, hBc, hUnc, hcl, hint, hfr, hUfr, ?_⟩
  rcases hsides with ⟨hn, hp⟩ | ⟨hn, hp⟩
  · exact Or.inl ⟨hneg B hn, hpos U hp⟩
  · exact Or.inr ⟨hneg U hn, hpos B hp⟩

end SpatialNeckWitness

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
