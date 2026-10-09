import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.IsometryTopology
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.KleinCompactification
import Mathlib.Topology.CompactOpen

namespace DifferentialGeometry.Hyperboloid

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem continuous_kleinClosedBallHomeomorph_apply :
    Continuous (fun p : (Hyperboloid E ≃ᵢ Hyperboloid F) × Metric.closedBall (0 : E) 1 =>
      kleinClosedBallHomeomorph p.1 p.2) := by
  apply continuous_induced_rng.2
  change Continuous (fun p : (Hyperboloid E ≃ᵢ Hyperboloid F) × Metric.closedBall (0 : E) 1 =>
    (kleinClosedBallHomeomorph p.1 p.2 : F))
  simp_rw [kleinClosedBallHomeomorph_apply_coe]
  have h : Continuous (fun p : (Hyperboloid E ≃ᵢ Hyperboloid F) × Metric.closedBall (0 : E) 1 =>
      lorentzExtension p.1 (1, (p.2 : E))) :=
    (continuous_lorentzExtension_apply (E := E) (F := F)).comp
      (continuous_fst.prodMk (continuous_const.prodMk
        (continuous_subtype_val.comp continuous_snd)))
  exact (h.fst.inv₀ fun p => (lorentzExtension_time_pos_of_norm_le_one p.1
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using p.2.property)).ne').smul h.snd

theorem continuous_boundaryHomeomorph_apply :
    Continuous (fun p : (Hyperboloid E ≃ᵢ Hyperboloid F) × Metric.sphere (0 : E) 1 =>
      boundaryHomeomorph p.1 p.2) := by
  apply continuous_induced_rng.2
  change Continuous (fun p : (Hyperboloid E ≃ᵢ Hyperboloid F) × Metric.sphere (0 : E) 1 =>
    (boundaryHomeomorph p.1 p.2 : F))
  simp_rw [boundaryHomeomorph_apply_coe]
  have h : Continuous (fun p : (Hyperboloid E ≃ᵢ Hyperboloid F) × Metric.sphere (0 : E) 1 =>
      lorentzExtension p.1 (1, (p.2 : E))) :=
    (continuous_lorentzExtension_apply (E := E) (F := F)).comp
      (continuous_fst.prodMk (continuous_const.prodMk
        (continuous_subtype_val.comp continuous_snd)))
  exact (h.fst.inv₀ fun p => (lorentzExtension_sphere_time_pos p.1 p.2).ne').smul h.snd

theorem continuous_kleinClosedBallHomeomorph_toContinuousMap :
    Continuous (fun f : Hyperboloid E ≃ᵢ Hyperboloid F =>
      (kleinClosedBallHomeomorph f :
        C(Metric.closedBall (0 : E) 1, Metric.closedBall (0 : F) 1))) :=
  ContinuousMap.continuous_of_continuous_uncurry _ continuous_kleinClosedBallHomeomorph_apply

theorem continuous_boundaryHomeomorph_toContinuousMap :
    Continuous (fun f : Hyperboloid E ≃ᵢ Hyperboloid F =>
      (boundaryHomeomorph f : C(Metric.sphere (0 : E) 1, Metric.sphere (0 : F) 1))) :=
  ContinuousMap.continuous_of_continuous_uncurry _ continuous_boundaryHomeomorph_apply

end DifferentialGeometry.Hyperboloid
