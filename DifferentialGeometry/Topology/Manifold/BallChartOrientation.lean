import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.OrientationSign
import DifferentialGeometry.Topology.Manifold.BallChartAffine
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

open DifferentialGeometry.Topology.Manifold
open _root_.OrientationAssembly

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

private theorem orientation_map_or_map_neg_on
    {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    (b : _root_.PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
    (o : ManifoldOrientation (𝓡 3) M 3)
    {s : Set E3} (hs : IsPreconnected s) (hsource : s ⊆ b.source) :
    (∀ (x : E3) (hx : x ∈ s), Orientation.map (Fin 3)
      ((b.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (hsource hx)).mfderivToContinuousLinearEquiv
        (by simp)).toLinearEquiv (stdOrientation x) = o.orientation (b x)) ∨
    (∀ (x : E3) (hx : x ∈ s), Orientation.map (Fin 3)
      ((b.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (hsource hx)).mfderivToContinuousLinearEquiv
        (by simp)).toLinearEquiv (stdOrientation x) = -o.orientation (b x)) := by
  let oE := euclideanSmoothOrientation E3 stdOrientationModel
  let oM := smoothOrientationOfManifoldOrientation (𝓡 3)
    (reindexManifoldOrientation (𝓡 3) csIdx o)
  have h := DifferentialGeometry.PartialDiffeomorph.tangentOrientationEquiv_eq_or_eq_neg_of_isPreconnected
    b oE oM hs hsource
  have hmap (x : E3) (hx : x ∈ s) :
      tangentOrientationEquiv
        ((b.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (hsource hx)).mfderivToContinuousLinearEquiv
          (by simp)).toLinearEquiv (oE.val x) =
      Orientation.reindex ℝ E3 csIdx (Orientation.map (Fin 3)
        ((b.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (hsource hx)).mfderivToContinuousLinearEquiv
          (by simp)).toLinearEquiv (stdOrientation x)) := by
    let L : E3 ≃ₗ[ℝ] E3 :=
      ((b.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (hsource hx)).mfderivToContinuousLinearEquiv
        (by simp)).toLinearEquiv
    change tangentOrientationEquiv L stdOrientationModel =
      Orientation.reindex ℝ E3 csIdx (Orientation.map (Fin 3) L (stdOrientation x))
    rw [tangentOrientationEquiv_self]
    exact (orientation_reindex_map_comm (R := ℝ) csIdx L (stdOrientation x)).symm
  rcases h with h | h
  · left
    intro x hx
    apply (Orientation.reindex ℝ E3 csIdx).injective
    rw [← hmap x hx]
    exact h x hx
  · right
    intro x hx
    apply (Orientation.reindex ℝ E3 csIdx).injective
    exact (hmap x hx).symm.trans ((h x hx).trans
      (Orientation.reindex_neg csIdx (o.orientation (b x))).symm)


theorem BallChart.exists_oriented
    {M : ClosedOrientedManifold 3} (b : BallChart 3 (𝓡 3) M.Carrier) :
    (∃ c : OrientedBallChart M, ∀ x, c.chart x = b.chart x) ∨
    (∃ c : OrientedBallChart M.opposite, ∀ x, c.chart x = b.chart x) := by
  let U := connectedComponentIn b.chart.source (0 : E3)
  have hU : U ⊆ b.chart.source := connectedComponentIn_subset _ _
  have hball : Metric.closedBall (0 : E3) 2 ⊆ U :=
    (convex_closedBall (0 : E3) (2 : ℝ)).isPreconnected.subset_connectedComponentIn
      (Metric.mem_closedBall_self (by norm_num)) b.closedBall_subset_source
  let C : BallChart 3 (𝓡 3) M.Carrier := {
    chart := PartialDiffeomorph.restrict b.chart U b.chart.open_source.connectedComponentIn
    closedBall_subset_source := fun x hx => ⟨b.closedBall_subset_source hx, hball hx⟩ }
  have hsrc : C.chart.source = U := Set.inter_eq_right.mpr hU
  have hpre : IsPreconnected C.chart.source := by
    rw [hsrc]
    exact isPreconnected_connectedComponentIn
  rcases orientation_map_or_map_neg_on C.chart M.orientation hpre (fun _ hx => hx) with hpos | hneg
  · exact Or.inl ⟨{ toBallChart := C, preserves_orientation := hpos }, fun _ => rfl⟩
  · exact Or.inr ⟨{ toBallChart := C, preserves_orientation := hneg }, fun _ => rfl⟩

theorem BallChart.exists_oriented_scaled
    {M : ClosedOrientedManifold 3} (b : BallChart 3 (𝓡 3) M.Carrier)
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    (∃ c : OrientedBallChart M, ∀ x, c.chart x = b.chart (a • x)) ∨
    (∃ c : OrientedBallChart M.opposite, ∀ x, c.chart x = b.chart (a • x)) := by
  let B := b.affine 0 a ha (by simpa using (mul_le_mul_of_nonneg_left ha1 (by norm_num : (0 : ℝ) ≤ 2)))
  have hB (x : E3) : B.chart x = b.chart (a • x) := by
    change b.chart ((0 : E3) + a • x) = b.chart (a • x)
    rw [zero_add]
  rcases B.exists_oriented with ⟨c, hc⟩ | ⟨c, hc⟩
  · exact Or.inl ⟨c, fun x => (hc x).trans (hB x)⟩
  · exact Or.inr ⟨c, fun x => (hc x).trans (hB x)⟩

end DifferentialGeometry.Topology
