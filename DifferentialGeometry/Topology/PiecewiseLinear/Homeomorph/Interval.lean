import DifferentialGeometry.Topology.PiecewiseLinear.PLImage
import DifferentialGeometry.Topology.PiecewiseLinear.PLPath

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem isPLHomeomorphOn_mul_add_Icc_of_neg {m c a b a' b' : ℝ} (hm : m < 0)
    (ha' : m * b + c = a') (hb' : m * a + c = b') :
    IsPLHomeomorphOn (fun t : ℝ => m * t + c) (Icc a b) (Icc a' b') := by
  subst ha' hb'
  have hm0 : m ≠ 0 := hm.ne
  refine isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
    (isPiecewiseAffineOn_of_affine_of_isHPolytope
      (m • AffineMap.id ℝ ℝ + AffineMap.const ℝ ℝ c) isHPolytope_Icc) ⟨?_, ?_, ?_⟩
  · intro t ht
    change m * t + c ∈ Icc (m * b + c) (m * a + c)
    have h1 := mul_le_mul_of_nonpos_left ht.1 hm.le
    have h2 := mul_le_mul_of_nonpos_left ht.2 hm.le
    exact ⟨by linarith, by linarith⟩
  · intro s _ t _ hst
    change m * s + c = m * t + c at hst
    exact mul_left_cancel₀ hm0 (by linarith)
  · intro y hy
    have hy1 : m * b + c ≤ y := hy.1
    have hy2 : y ≤ m * a + c := hy.2
    have hdiv : m * ((y - c) / m) = y - c := by field_simp
    refine ⟨(y - c) / m, ⟨?_, ?_⟩, ?_⟩
    · by_contra h
      push Not at h
      nlinarith [mul_lt_mul_of_neg_left h hm]
    · by_contra h
      push Not at h
      nlinarith [mul_lt_mul_of_neg_left h hm]
    · change m * ((y - c) / m) + c = y
      rw [hdiv]
      ring

end DifferentialGeometry.Topology.PiecewiseLinear
