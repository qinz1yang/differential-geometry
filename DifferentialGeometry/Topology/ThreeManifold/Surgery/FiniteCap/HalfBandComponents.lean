import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreSelection
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry.Geometry.Neck

namespace DifferentialGeometry.Topology.ThreeManifold.Surgery

variable {ι M : Type*} [TopologicalSpace M] {precision : ι → ℝ}
variable (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))

theorem cutCore_negative_half_component_eq (i : ι)
    (q : bufferedCylinder (precision i)) (hq : q.val.2 ≤ -1) :
    ConnectedComponents.mk
        (⟨f i q, (cutCore_chart_iff f (fun j => (hf j).injective) hdisj i q).mpr
          (Or.inl hq)⟩ : cutCore f) =
      cuttingSphereComponent hδ f hf hdisj (i, false) := by
  let S2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
  let : ConnectedSpace S2 := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num)
      (0 : EuclideanSpace ℝ (Fin 3)) (by norm_num : (0 : ℝ) ≤ 1))
  let : PreconnectedSpace (Icc q.val.2 (-1 : ℝ)) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  let ψ : S2 × Icc q.val.2 (-1 : ℝ) → bufferedCylinder (precision i) := fun p =>
    ⟨(p.1, p.2.val), by
      change -(precision i)⁻¹ - 1 < p.2.val ∧ p.2.val < (precision i)⁻¹ + 1
      have hqbuffer : -(precision i)⁻¹ - 1 < q.val.2 ∧
          q.val.2 < (precision i)⁻¹ + 1 := q.property
      refine ⟨hqbuffer.1.trans_le p.2.property.1, ?_⟩
      linarith [p.2.property.2, inv_pos.mpr (hδ i)]⟩
  let F : S2 × Icc q.val.2 (-1 : ℝ) → cutCore f := fun p =>
    ⟨f i (ψ p), (cutCore_chart_iff f (fun j => (hf j).injective) hdisj i (ψ p)).mpr
      (Or.inl p.2.property.2)⟩
  have hψ : Continuous ψ :=
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  have hF : Continuous F := ((hf i).continuous.comp hψ).subtype_mk _
  change ConnectedComponents.mk _ = ConnectedComponents.mk
    (cuttingSphereAttachment hδ f (fun j => (hf j).injective) hdisj
      ⟨(i, false), spherePoint⟩)
  apply ConnectedComponents.coe_eq_coe'.mpr
  apply (isPreconnected_range hF).subset_connectedComponent
  · refine ⟨(spherePoint, ⟨-1, hq, le_rfl⟩), ?_⟩
    apply Subtype.ext
    apply congrArg (f i)
    exact Subtype.ext rfl
  · refine ⟨(q.val.1, ⟨q.val.2, le_rfl, hq⟩), ?_⟩
    apply Subtype.ext
    apply congrArg (f i)
    exact Subtype.ext rfl

theorem negative_half_image_subset_discardedCore
    (R : Set (ConnectedComponents (cutCore f))) (i : ι)
    (hi : cuttingSphereComponent hδ f hf hdisj (i, false) ∉ R) :
    f i '' {q : bufferedCylinder (precision i) | q.val.2 ≤ -1} ⊆
      Subtype.val '' discardedCore f R := by
  rintro x ⟨q, hq, rfl⟩
  let p : cutCore f :=
    ⟨f i q, (cutCore_chart_iff f (fun j => (hf j).injective) hdisj i q).mpr (Or.inl hq)⟩
  refine ⟨p, ?_, rfl⟩
  change ConnectedComponents.mk p ∉ R
  rw [cutCore_negative_half_component_eq hδ f hf hdisj i q hq]
  exact hi

theorem negative_closed_half_band_image_subset_discardedCore
    (R : Set (ConnectedComponents (cutCore f))) (i : ι)
    (hi : cuttingSphereComponent hδ f hf hdisj (i, false) ∉ R) :
    f i '' {q : bufferedCylinder (precision i) |
        q.val.2 ∈ Icc (-(precision i)⁻¹) (-1 : ℝ)} ⊆
      Subtype.val '' discardedCore f R := by
  rintro x ⟨q, hq, rfl⟩
  exact negative_half_image_subset_discardedCore hδ f hf hdisj R i hi ⟨q, hq.2, rfl⟩

end DifferentialGeometry.Topology.ThreeManifold.Surgery
