import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.IsometryTopology

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem continuous_boost : Continuous (boost (E := E)) := by
  apply IsometryEquiv.continuous_iff.mpr
  intro y
  apply continuous_induced_rng.mpr
  change Continuous (fun x : Hyperboloid E => ((boost x y).time, (boost x y).space))
  simp_rw [boost_coordinates]
  have hi : Continuous (fun x : Hyperboloid E => inner ℝ x.space y.space) :=
    continuous_space.inner continuous_const
  have ht : Continuous (fun x : Hyperboloid E => x.time + 1) :=
    continuous_time.add continuous_const
  have hn (x : Hyperboloid E) : x.time + 1 ≠ 0 := by linarith [x.time_pos]
  exact ((continuous_time.mul continuous_const).add hi).prodMk
    (continuous_const.add ((continuous_const.add (hi.div ht hn)).smul continuous_space))

end DifferentialGeometry.Hyperboloid
