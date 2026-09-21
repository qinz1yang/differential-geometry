import DifferentialGeometry.Geometry.Comparison.Toponogov.AngleKernel
import DifferentialGeometry.Geometry.Comparison.Toponogov.LimitingRadialAngle

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology

namespace DifferentialGeometry.Toponogov

variable {X : Type*} [MetricSpace X] {ι : Type*} {L : ι → ℝ} {gamma : ι → ℝ → X}

theorem limitingRadialAngle_self {i : ι} (hL : 0 < L i)
    (hmin : ∀ s ∈ Ioc 0 (L i), ∀ t ∈ Ioc 0 (L i), dist (gamma i s) (gamma i t) = |s - t|) :
    limitingRadialAngle L gamma i i = 0 := by
  have hset : positiveRectangleValues (L i) (L i) (radialComparisonAngle gamma i i) = {0} := by
    ext z
    constructor
    · rintro ⟨s, hs, t, ht, rfl⟩
      change comparisonAngle s t (dist (gamma i s) (gamma i t)) = 0
      rw [hmin s hs t ht, comparisonAngle_abs_sub hs.1 ht.1]
    · intro hz
      rw [mem_singleton_iff] at hz
      subst z
      refine ⟨L i, ⟨hL, le_rfl⟩, L i, ⟨hL, le_rfl⟩, ?_⟩
      dsimp only [radialComparisonAngle]
      rw [hmin _ ⟨hL, le_rfl⟩ _ ⟨hL, le_rfl⟩, comparisonAngle_abs_sub hL hL]
  rw [limitingRadialAngle, hset, csSup_singleton]

theorem limitingRadialAngle_triangle_of_minimizing
    (z : X) (hL : ∀ i, 0 < L i) (hrad : IsRadialFamily z L gamma)
    (hmin : ∀ i, ∀ s ∈ Ioc 0 (L i), ∀ t ∈ Ioc 0 (L i), dist (gamma i s) (gamma i t) = |s - t|)
    (hmono : ∀ i j, i ≠ j → CoordinatewiseNonincreasingOn (L i) (L j) (radialComparisonAngle gamma i j))
    (i j k : ι) :
    limitingRadialAngle L gamma i k ≤ limitingRadialAngle L gamma i j + limitingRadialAngle L gamma j k := by
  rcases eq_or_ne i j with hij | hij
  · subst j
    rw [limitingRadialAngle_self (hL i) (hmin i), zero_add]
  rcases eq_or_ne j k with hjk | hjk
  · subst k
    rw [limitingRadialAngle_self (hL j) (hmin j), add_zero]
  rcases eq_or_ne i k with hik | hik
  · subst k
    rw [limitingRadialAngle_self (hL i) (hmin i)]
    exact add_nonneg (limitingRadialAngle_mem_Icc gamma (hL i) (hL j)).1
      (limitingRadialAngle_mem_Icc gamma (hL j) (hL i)).1
  · exact limitingRadialAngle_triangle z L gamma hL hrad hmono hij hjk hik

def limitingRadialAngleKernel
    (z : X) (L : ι → ℝ) (gamma : ι → ℝ → X)
    (hL : ∀ i, 0 < L i) (hrad : IsRadialFamily z L gamma)
    (hmin : ∀ i, ∀ s ∈ Ioc 0 (L i), ∀ t ∈ Ioc 0 (L i), dist (gamma i s) (gamma i t) = |s - t|)
    (hmono : ∀ i j, i ≠ j → CoordinatewiseNonincreasingOn (L i) (L j) (radialComparisonAngle gamma i j)) :
    AngleKernel ι where
  angle := limitingRadialAngle L gamma
  nonneg := fun i j => (limitingRadialAngle_mem_Icc gamma (hL i) (hL j)).1
  self := fun i => limitingRadialAngle_self (hL i) (hmin i)
  symm := limitingRadialAngle_comm L gamma
  triangle := limitingRadialAngle_triangle_of_minimizing z hL hrad hmin hmono

@[simp] theorem limitingRadialAngleKernel_angle
    (z : X) (L : ι → ℝ) (gamma : ι → ℝ → X)
    (hL : ∀ i, 0 < L i) (hrad : IsRadialFamily z L gamma)
    (hmin : ∀ i, ∀ s ∈ Ioc 0 (L i), ∀ t ∈ Ioc 0 (L i), dist (gamma i s) (gamma i t) = |s - t|)
    (hmono : ∀ i j, i ≠ j → CoordinatewiseNonincreasingOn (L i) (L j) (radialComparisonAngle gamma i j))
    (i j : ι) :
    (limitingRadialAngleKernel z L gamma hL hrad hmin hmono).angle i j = limitingRadialAngle L gamma i j := rfl

end DifferentialGeometry.Toponogov
