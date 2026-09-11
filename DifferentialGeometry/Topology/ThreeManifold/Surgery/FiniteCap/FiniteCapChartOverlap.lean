import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreInteriorCollar
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapOpenChart

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace
open DifferentialGeometry.Topology.Manifold.Attachment DifferentialGeometry.Geometry.Neck
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev RadialE3 := EuclideanSpace ℝ (Fin 3)
private abbrev RadialS2 := Metric.sphere (0 : RadialE3) 1
private abbrev RadialCollar (δ : ℝ) := RadialS2 × Ico (0 : ℝ) (cuttingCollarWidth δ)
variable {ι M : Type*} [Finite ι] [TopologicalSpace M] [T2Space M]
variable {precision : ι → ℝ} {L : ℝ}

theorem finiteCoreInterior_collar_iff (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
    (b : ι × Bool) (q : RadialCollar (precision b.1)) :
    finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
      (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q) ∈
        finiteCoreInterior hL hδ f (fun i => (hf i).injective) hdisj ↔ 0 < q.2.val := by
  change cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q ∈
    finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj ⁻¹'
      finiteCoreInterior hL hδ f (fun i => (hf i).injective) hdisj ↔ _
  rw [finiteCoreInterior_core_preimage]
  exact cuttingCollar_interior_iff hδ f hf hdisj b q

theorem finiteCapOpenChart_interior_overlap_image (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))) (b : ι × Bool) :
    finiteCapOpenChart hL hδ f hf hdisj b ''
      ((finiteCapOpenChart hL hδ f hf hdisj b).source ∩
        finiteCoreInterior hL hδ f (fun i => (hf i).injective) hdisj) =
          {x : RadialE3 | L < ‖x‖ ∧ ‖x‖ < L + cuttingCollarWidth (precision b.1)} := by
  ext x
  constructor
  · rintro ⟨p, ⟨hpN, hpI⟩, rfl⟩
    rw [finiteCapOpenChart_source] at hpN
    rcases hpN with ⟨y, rfl⟩ | ⟨q, rfl⟩
    · have he : (⟨b, y⟩ : IndexedCaps ι L) ∈
          finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⁻¹'
            finiteCoreInterior hL hδ f (fun i => (hf i).injective) hdisj := hpI
      rw [finiteCoreInterior_cap_preimage hL hδ f hf hdisj] at he
      exact he.elim
    · have ht := (finiteCoreInterior_collar_iff hL hδ f hf hdisj b q).mp hpI
      rw [finiteCapOpenChart_collar]
      have hn : ‖(L + q.2.val) • q.1.val‖ = L + q.2.val := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (add_pos_of_pos_of_nonneg hL q.2.property.1)]
        have hy : ‖q.1.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using q.1.property
        rw [hy, mul_one]
      change L < ‖(L + q.2.val) • q.1.val‖ ∧ ‖(L + q.2.val) • q.1.val‖ < _
      rw [hn]
      exact ⟨lt_add_of_pos_right L ht, by linarith [q.2.property.2]⟩
  · intro hx
    let s : {y : {z : RadialE3 // ‖z‖ < L + cuttingCollarWidth (precision b.1)} // L ≤ ‖y.val‖} :=
      ⟨⟨x, hx.2⟩, hx.1.le⟩
    let q : RadialCollar (precision b.1) := (retainedCylinderHomeomorphShell hL).symm s
    have hq : q.2.val = ‖x‖ - L := rfl
    have hr : (L + q.2.val) • q.1.val = x := by
      have he := congrArg (fun y : {y : {z : RadialE3 // ‖z‖ < L + cuttingCollarWidth (precision b.1)} // L ≤ ‖y.val‖} => y.val.val)
        ((retainedCylinderHomeomorphShell hL).apply_symm_apply s)
      exact he
    refine ⟨finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
      (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q), ⟨?_, ?_⟩, ?_⟩
    · rw [finiteCapOpenChart_source]
      exact Or.inr ⟨q, rfl⟩
    · apply (finiteCoreInterior_collar_iff hL hδ f hf hdisj b q).mpr
      rw [hq]
      exact sub_pos.mpr hx.1
    · rw [finiteCapOpenChart_collar]
      exact hr
end DifferentialGeometry.Topology.ThreeManifold.Surgery
