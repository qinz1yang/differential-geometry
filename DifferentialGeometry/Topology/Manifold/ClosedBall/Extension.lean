import DifferentialGeometry.Topology.Manifold.ClosedBall.BallChart
import DifferentialGeometry.Topology.Manifold.ClosedBall.Collar
import DifferentialGeometry.Topology.Manifold.SphereCollarCoordinates
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.CompactGluing

noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {m : ℕ}

private local instance closedCellCharts : ChartedSpace (EuclideanHalfSpace (m + 1))
    (ClosedCell (m + 1)) := Handle.closedCellChartedSpaceSucc m
private local instance closedCellSmooth : IsManifold (𝓡∂ (m + 1)) ∞ (ClosedCell (m + 1)) :=
  Handle.closedCellIsManifold m
private local instance sphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) := ⟨by simp⟩

variable {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) N]
  [IsManifold (𝓡 (m + 1)) ∞ N] [T2Space N]

theorem exists_partialDiffeomorph_extension_closedCell
    (f : ClosedCell (m + 1) → N)
    (hf : IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ f) :
    ∃ φ : PartialDiffeomorph (𝓡 (m + 1)) (𝓡 (m + 1))
        (EuclideanSpace ℝ (Fin (m + 1))) N ∞,
      Metric.closedBall 0 1 ⊆ φ.source ∧ ∀ x : ClosedCell (m + 1), φ x.val = f x := by
  let V := EuclideanSpace ℝ (Fin (m + 1))
  let S := Metric.sphere (0 : V) 1
  let v : S := ⟨EuclideanSpace.single 0 1, by
    change EuclideanSpace.single 0 (1 : ℝ) ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1
    simp⟩
  obtain ⟨φ₀, h₀source, -, h₀eq⟩ := exists_partialDiffeomorph_of_closedCell_embedding f hf
  obtain ⟨d, hwidth, hd⟩ := exists_smoothTwoSidedCollar_of_closedCell_embedding f hf
  let φ₁ := d.radialPartialDiffeomorph v
  have h₁eq (x : ClosedCell (m + 1)) (hx : x.val ∈ φ₁.source) : φ₁ x.val = f x := by
    obtain ⟨hne, ht⟩ := (d.mem_radialPartialDiffeomorph_source_iff v x.val).mp hx
    let z := sphereDirection v x.val
    have heq := d.radialPartialDiffeomorph_apply v z ‖x.val‖ (norm_pos_iff.mpr hne) ht
    rw [norm_smul_sphereDirection v hne] at heq
    change φ₁ x.val = d.toFun (z, ⟨1 - ‖x.val‖, ht⟩) at heq
    refine heq.trans ((hd (z, ⟨1 - ‖x.val‖, ht⟩) (sub_nonneg.mpr x.property)).trans ?_)
    apply congrArg f
    apply Subtype.ext
    dsimp only
    rw [sub_sub_cancel, norm_smul_sphereDirection v hne]
  let φ : Bool → PartialDiffeomorph (𝓡 (m + 1)) (𝓡 (m + 1)) V N ∞ :=
    fun b => if b then φ₁ else φ₀
  have heq (i : Bool) (x : ClosedCell (m + 1)) (hx : x.val ∈ (φ i).source) :
      φ i x.val = f x := by
    cases i with
    | false =>
      have hnorm : ‖x.val‖ < 1 := mem_ball_zero_iff.mp (h₀source ▸ hx)
      exact h₀eq x.val hnorm
    | true => exact h₁eq x hx
  have hcover : Metric.closedBall (0 : V) 1 ⊆ ⋃ i, (φ i).source := by
    intro x hx
    have hnorm := mem_closedBall_zero_iff.mp hx
    by_cases hlt : ‖x‖ < 1
    · exact mem_iUnion.mpr ⟨false, h₀source ▸ mem_ball_zero_iff.mpr hlt⟩
    · have hsphere : x ∈ Metric.sphere (0 : V) 1 :=
        mem_sphere_zero_iff_norm.mpr (le_antisymm hnorm (le_of_not_gt hlt))
      exact mem_iUnion.mpr ⟨true, d.sphere_subset_radialPartialDiffeomorph_source v hsphere⟩
  have hover (i j : Bool) : EqOn (φ i) (φ j) ((φ i).source ∩ (φ j).source) := by
    intro x hx
    by_cases hij : i = j
    · rw [hij]
    have hlt : ‖x‖ < 1 := by
      cases i <;> cases j
      · exact (hij rfl).elim
      · exact mem_ball_zero_iff.mp (h₀source ▸ hx.1)
      · exact mem_ball_zero_iff.mp (h₀source ▸ hx.2)
      · exact (hij rfl).elim
    exact (heq i ⟨x, hlt.le⟩ hx.1).trans (heq j ⟨x, hlt.le⟩ hx.2).symm
  have himage (i j : Bool) :
      φ i '' (Metric.closedBall (0 : V) 1 ∩ (φ i).source) ∩
        φ j '' (Metric.closedBall (0 : V) 1 ∩ (φ j).source) ⊆
        φ i '' (Metric.closedBall (0 : V) 1 ∩ (φ i).source ∩ (φ j).source) := by
    rintro y ⟨⟨x, hx, rfl⟩, ⟨z, hz, hzx⟩⟩
    have hfx : f ⟨x, mem_closedBall_zero_iff.mp hx.1⟩ =
        f ⟨z, mem_closedBall_zero_iff.mp hz.1⟩ :=
      (heq i ⟨x, mem_closedBall_zero_iff.mp hx.1⟩ hx.2).symm.trans
        (hzx.symm.trans (heq j ⟨z, mem_closedBall_zero_iff.mp hz.1⟩ hz.2))
    have hxz : x = z := congrArg Subtype.val (hf.isEmbedding.injective hfx)
    exact ⟨x, ⟨hx, hxz ▸ hz.2⟩, rfl⟩
  obtain ⟨ψ, hs, hψ⟩ := PartialDiffeomorph.exists_gluing_of_isCompact φ
    (isCompact_closedBall (0 : V) 1) ⟨0, Metric.mem_closedBall_self zero_le_one⟩
    (fun i => (φ i).open_source) (fun _ => subset_rfl) hcover hover himage
  refine ⟨ψ, hs, ?_⟩
  intro x
  have hx : x.val ∈ Metric.closedBall (0 : V) 1 := mem_closedBall_zero_iff.mpr x.property
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
  exact (hψ i ⟨hs hx, hi⟩).trans (heq i x hi)

end DifferentialGeometry.Topology.Manifold
