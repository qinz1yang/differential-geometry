import DifferentialGeometry.Geometry.Metric.Approximation.NetTransfer
import DifferentialGeometry.Geometry.Metric.L2Product

set_option autoImplicit false

open Set Metric

namespace GC.MetricGeometry.PointedBallApprox

variable {X E Y : Type*} [MetricSpace X] [MetricSpace E] [MetricSpace Y]
variable {p : X} {u : E} {q : Y} {R δ ε : ℝ}

theorem exists_internal_finset_net_factor
    (f : PointedBallApprox p (WithLp.toLp 2 (u, q)) (R + 2) ε)
    (hR : 0 < R) (hδ : 0 < δ) (hεquarter : ε < 1 / 4) (hεδ : ε < δ / 8)
    (F : Finset X) (hFin : ∀ a ∈ F, dist a p ≤ R + 1)
    (hnet : ∀ x : X, dist x p ≤ R + 1 → ∃ a ∈ F, dist x a ≤ δ / 4) :
    ∃ T : Finset Y, T.card ≤ F.card ∧ (∀ y ∈ T, dist y q ≤ R) ∧
      ∀ y : Y, dist y q ≤ R → ∃ z ∈ T, dist y z < δ := by
  classical
  obtain ⟨S, hcard, hS, hcover⟩ := f.exists_internal_finset_net hR hδ hεquarter hεδ F hFin hnet
  refine ⟨S.image WithLp.snd, (Finset.card_image_le).trans hcard, ?_, ?_⟩
  · intro y hy
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
    exact (WithLp.dist_snd_le w (WithLp.toLp 2 (u, q))).trans (hS w hw)
  · intro y hy
    have hr : dist (WithLp.toLp 2 (u, y)) (WithLp.toLp 2 (u, q)) ≤ R := by
      rwa [(WithLp.isometry_prodMk_left u).dist_eq y q]
    obtain ⟨w, hw, hd⟩ := hcover (WithLp.toLp 2 (u, y)) hr
    exact ⟨w.snd, Finset.mem_image.mpr ⟨w, hw, rfl⟩,
      (WithLp.dist_snd_le (WithLp.toLp 2 (u, y)) w).trans_lt hd⟩

end GC.MetricGeometry.PointedBallApprox
