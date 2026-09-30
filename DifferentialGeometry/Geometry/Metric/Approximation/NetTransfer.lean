import DifferentialGeometry.Geometry.Metric.Approximation.PointedBallApproximation
import DifferentialGeometry.Topology.MetricSpace.FiniteNets

set_option autoImplicit false

open Set

namespace Metric

theorem exists_internal_finset_net_of_finite_centers
    {Y L : Type*} [PseudoMetricSpace Y] (A : Set Y) (F : Finset L) (c : L → Y)
    {η : ℝ} (_hη : 0 < η)
    (hcover : ∀ y ∈ A, ∃ a ∈ F, dist y (c a) < η) :
    ∃ T : Finset Y, T.card ≤ F.card ∧ (∀ y ∈ T, y ∈ A) ∧
      ∀ y ∈ A, ∃ z ∈ T, dist y z < 2 * η := by
  classical
  let G := F.filter (fun a => ∃ y ∈ A, dist y (c a) < η)
  have hG (a : G) : ∃ y ∈ A, dist y (c a.val) < η :=
    (Finset.mem_filter.mp a.property).2
  choose z hzA hzc using hG
  let T := Finset.univ.image z
  refine ⟨T, ?_, ?_, ?_⟩
  · calc
      T.card ≤ (Finset.univ : Finset G).card := Finset.card_image_le
      _ = G.card := by simp
      _ ≤ F.card := Finset.card_filter_le _ _
  · intro y hy
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hy
    exact hzA a
  · intro y hy
    obtain ⟨a, ha, hya⟩ := hcover y hy
    let aG : G := ⟨a, Finset.mem_filter.mpr ⟨ha, y, hy, hya⟩⟩
    refine ⟨z aG, Finset.mem_image.mpr ⟨aG, Finset.mem_univ _, rfl⟩, ?_⟩
    have hza := hzc aG
    have htri := dist_triangle y (c a) (z aG)
    rw [dist_comm (c a) (z aG)] at htri
    change dist (z aG) (c a) < η at hza
    linarith

end Metric

namespace GC.MetricGeometry.PointedBallApprox

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
variable {p : X} {q : Y} {R δ ε : ℝ}

theorem exists_internal_finset_net (f : PointedBallApprox p q (R + 2) ε)
    (_hR : 0 < R) (hδ : 0 < δ) (hεquarter : ε < 1 / 4) (hεδ : ε < δ / 8)
    (F : Finset X) (hFin : ∀ a ∈ F, dist a p ≤ R + 1)
    (hnet : ∀ x : X, dist x p ≤ R + 1 → ∃ a ∈ F, dist x a ≤ δ / 4) :
    ∃ T : Finset Y, T.card ≤ F.card ∧ (∀ y ∈ T, dist y q ≤ R) ∧
      ∀ y : Y, dist y q ≤ R → ∃ z ∈ T, dist y z < δ := by
  classical
  let c (a : X) : Y := if ha : a ∈ F then f.toFun ⟨a, by linarith [hFin a ha]⟩ else q
  have hcover : ∀ y ∈ Metric.closedBall q R, ∃ a ∈ F, dist y (c a) < δ / 2 := by
    intro y hy
    have hyr : dist y q ≤ R := hy
    obtain ⟨x, hxy⟩ := f.coverage y (by linarith)
    have hrad := f.radial_lower x
    have htri := dist_triangle (f.toFun x) y q
    rw [dist_comm (f.toFun x) y] at htri
    have hxr : dist x.val p ≤ R + 1 := by linarith
    obtain ⟨a, ha, hxa⟩ := hnet x.val hxr
    let aR : BallCarrier p (R + 2) := ⟨a, by linarith [hFin a ha]⟩
    have hd := (abs_lt.mp (f.distortion x aR)).2
    have htri' := dist_triangle y (f.toFun x) (f.toFun aR)
    refine ⟨a, ha, ?_⟩
    have hca : c a = f.toFun aR := by simp only [c, dite_eq_left ha, aR]
    rw [hca]
    change dist (f.toFun x) (f.toFun aR) - dist x.val a < ε at hd
    linarith
  obtain ⟨T, hcard, hinside, hcoverT⟩ :=
    Metric.exists_internal_finset_net_of_finite_centers (Metric.closedBall q R) F c
      (half_pos hδ) hcover
  refine ⟨T, hcard, hinside, fun y hy => ?_⟩
  obtain ⟨z, hz, hyz⟩ := hcoverT y hy
  exact ⟨z, hz, by linarith⟩

end GC.MetricGeometry.PointedBallApprox
