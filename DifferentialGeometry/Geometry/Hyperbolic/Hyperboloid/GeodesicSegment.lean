import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Projection
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.IsometryClassification
import Mathlib.Analysis.Convex.StrictConvexBetween

noncomputable section

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem isometryEquiv_geodesicLine {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (e : Hyperboloid E ≃ᵢ Hyperboloid F) (x : Hyperboloid E) (v : ℝ × E)
    (hv : lorentzForm E v v = 1) (ho : lorentzForm E (x.time, x.space) v = 0) (t : ℝ) :
    e (geodesicLine x v hv ho t) =
      geodesicLine (e x) (lorentzExtension e v)
        (by rw [(lorentzExtension e).map_app]; exact hv)
        (by rw [← lorentzExtension_apply e x, (lorentzExtension e).map_app]; exact ho) t := by
  apply ext
  have h := lorentzExtension_apply e (geodesicLine x v hv ho t)
  rw [geodesicLine_time, geodesicLine_space] at h
  change lorentzExtension e
      (Real.cosh t • (x.time, x.space) + Real.sinh t • v) =
    ((e (geodesicLine x v hv ho t)).time, (e (geodesicLine x v hv ho t)).space) at h
  rw [map_add, map_smul, map_smul, lorentzExtension_apply] at h
  rw [geodesicLine_space]
  exact (congrArg Prod.snd h).symm

private theorem metric_segment_axis (u : E) (hu : ‖u‖ = 1) (a b : ℝ) (hab : a ≤ b) :
    let c := geodesicLine (origin : Hyperboloid E) (0, u)
      (by simp [lorentzForm_apply, hu]) (by simp [lorentzForm_apply])
    {z : Hyperboloid E | dist (c a) z + dist z (c b) = dist (c a) (c b)} =
      c '' Set.Icc a b := by
  let c := geodesicLine (origin : Hyperboloid E) (0, u)
    (by simp [lorentzForm_apply, hu]) (by simp [lorentzForm_apply])
  have hc : Isometry c := isometry_geodesicLine origin (0, u) _ _
  change {z : Hyperboloid E | dist (c a) z + dist z (c b) = dist (c a) (c b)} = c '' Set.Icc a b
  ext z
  constructor
  · intro hz
    change dist (c a) z + dist z (c b) = dist (c a) (c b) at hz
    let p := lineProjection u hu z
    have hpRange : p ∈ Set.range c := lineProjection_mem_range u hu z
    have hpyth (t : ℝ) : Real.cosh (dist z (c t)) =
        Real.cosh (dist z p) * Real.cosh (dist p (c t)) :=
      cosh_dist_eq_mul_cosh_dist_lineProjection u hu z (c t) ⟨t, rfl⟩
    have hproj (t : ℝ) : dist p (c t) ≤ dist z (c t) := by
      have hcosh : Real.cosh (dist p (c t)) ≤ Real.cosh (dist z (c t)) := by
        rw [hpyth]
        calc
          Real.cosh (dist p (c t)) = 1 * Real.cosh (dist p (c t)) := (one_mul _).symm
          _ ≤ Real.cosh (dist z p) * Real.cosh (dist p (c t)) :=
            mul_le_mul_of_nonneg_right (Real.one_le_cosh _) (Real.cosh_pos _).le
      simpa only [abs_of_nonneg dist_nonneg] using Real.cosh_le_cosh.mp hcosh
    have htri : dist (c a) (c b) ≤ dist p (c a) + dist p (c b) := by
      simpa only [dist_comm (c a) p] using dist_triangle (c a) p (c b)
    have hza : dist p (c a) = dist z (c a) := by
      have ha := hproj a
      have hb := hproj b
      rw [dist_comm (c a) z] at hz
      linarith
    have hcosh : Real.cosh (dist z p) = 1 := by
      have h := hpyth a
      rw [← hza] at h
      apply mul_right_cancel₀ (Real.cosh_pos (dist p (c a))).ne'
      simpa only [one_mul] using h.symm
    have hzp : z = p := by
      apply dist_eq_zero.mp
      rw [← Real.arcosh_cosh dist_nonneg, hcosh, Real.arcosh_zero]
    obtain ⟨r, hr⟩ := hpRange
    have hzr : c r = z := hr.trans hzp.symm
    refine ⟨r, ?_, hzr⟩
    have hreal : dist a r + dist r b = dist a b := by
      rw [← hzr] at hz
      simpa only [hc.dist_eq] using hz
    have hseg : r ∈ segment ℝ a b :=
      mem_segment_iff_wbtw.mpr ((dist_add_dist_eq_iff (V := ℝ)).mp hreal)
    simpa only [segment_eq_Icc hab] using hseg
  · rintro ⟨r, hr, rfl⟩
    change dist (c a) (c r) + dist (c r) (c b) = dist (c a) (c b)
    rw [hc.dist_eq, hc.dist_eq, hc.dist_eq, dist_add_dist_eq_iff (V := ℝ),
      ← mem_segment_iff_wbtw, segment_eq_Icc hab]
    exact hr

theorem metric_segment_eq_image_geodesicLine (x : Hyperboloid E) (v : ℝ × E)
    (hv : lorentzForm E v v = 1) (ho : lorentzForm E (x.time, x.space) v = 0)
    (a b : ℝ) (hab : a ≤ b) :
    {z : Hyperboloid E | dist (geodesicLine x v hv ho a) z +
        dist z (geodesicLine x v hv ho b) =
          dist (geodesicLine x v hv ho a) (geodesicLine x v hv ho b)} =
      geodesicLine x v hv ho '' Set.Icc a b := by
  let c := geodesicLine x v hv ho
  let e := (boost x).symm
  let w := lorentzExtension e v
  have hx : e x = origin := by
    change (boost x).symm x = origin
    simpa only [boost_origin] using (boost x).symm_apply_apply origin
  have hw : lorentzForm E w w = 1 := by
    dsimp only [w]
    rw [(lorentzExtension e).map_app]
    exact hv
  have hwo : lorentzForm E ((e x).time, (e x).space) w = 0 := by
    rw [← lorentzExtension_apply e x]
    change lorentzForm E (lorentzExtension e (x.time, x.space)) (lorentzExtension e v) = 0
    rw [(lorentzExtension e).map_app]
    exact ho
  have ht : w.1 = 0 := by
    rw [hx] at hwo
    simpa only [lorentzForm_apply, origin_time, origin_space, inner_zero_left,
      one_mul, zero_sub, neg_eq_zero] using hwo
  have hn : ‖w.2‖ = 1 := by
    rw [lorentzForm_apply, ht, zero_mul, sub_zero, real_inner_self_eq_norm_sq] at hw
    nlinarith [norm_nonneg w.2]
  let d := geodesicLine (origin : Hyperboloid E) (0, w.2)
    (by simp [lorentzForm_apply, hn]) (by simp [lorentzForm_apply])
  have hline (t : ℝ) : e (c t) = d t := by
    apply ext
    have h := congrArg space (isometryEquiv_geodesicLine e x v hv ho t)
    simpa only [d, geodesicLine_space, hx, origin_space, smul_zero, zero_add] using h
  have haxis : {z : Hyperboloid E | dist (d a) z + dist z (d b) = dist (d a) (d b)} =
      d '' Set.Icc a b := metric_segment_axis w.2 hn a b hab
  change {z : Hyperboloid E | dist (c a) z + dist z (c b) = dist (c a) (c b)} = c '' Set.Icc a b
  ext z
  constructor
  · intro hz
    have heq : e z ∈ d '' Set.Icc a b := by
      rw [← haxis]
      change dist (d a) (e z) + dist (e z) (d b) = dist (d a) (d b)
      rw [← hline a, ← hline b, e.dist_eq, e.dist_eq, e.dist_eq]
      exact hz
    obtain ⟨t, ht, htz⟩ := heq
    exact ⟨t, ht, e.injective ((hline t).trans htz)⟩
  · rintro ⟨t, ht, rfl⟩
    have heq : d t ∈ {z : Hyperboloid E | dist (d a) z + dist z (d b) = dist (d a) (d b)} := by
      rw [haxis]
      exact ⟨t, ht, rfl⟩
    change dist (c a) (c t) + dist (c t) (c b) = dist (c a) (c b)
    rw [← e.dist_eq (c a) (c t), ← e.dist_eq (c t) (c b), ← e.dist_eq (c a) (c b),
      hline a, hline t, hline b]
    exact heq

end DifferentialGeometry.Hyperboloid
