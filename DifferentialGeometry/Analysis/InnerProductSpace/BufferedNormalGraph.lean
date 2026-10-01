import DifferentialGeometry.Analysis.InnerProductSpace.OrthogonalErrorCoordinates
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.LocalExtr

set_option autoImplicit false
noncomputable section
open Set Metric
namespace DifferentialGeometry.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

private theorem buffered_graph_candidate
    (L : Submodule ℝ H) [L.HasOrthogonalProjection]
    (o : H) (g : L → Lᗮ) (R a : ℝ)
    (hR : 0 < R) (ha : a ≤ 1 / 100)
    (hsmall : ∀ t ∈ ball (0 : L) (4 * R), ‖g t‖ ≤ a * R)
    (z : H) (hz : z ∈ ball o R) :
    let u := L.orthogonalProjectionOnto (z - o)
    ‖u‖ < R ∧
      dist z (o + orthogonalCoordinateSum L (u, g u)) < 3 * R / 2 := by
  let q : L → H := fun t => o + orthogonalCoordinateSum L (t, g t)
  let u : L := L.orthogonalProjectionOnto (z - o)
  let v : Lᗮ := Lᗮ.orthogonalProjectionOnto (z - o)
  have hz' : ‖z - o‖ < R := by simpa only [mem_ball, dist_eq_norm] using hz
  have hu : ‖u‖ < R := (L.norm_orthogonalProjectionOnto_apply_le (z - o)).trans_lt hz'
  have hv : ‖v‖ < R := (Lᗮ.norm_orthogonalProjectionOnto_apply_le (z - o)).trans_lt hz'
  have huz : o + ((u : H) + (v : H)) = z := by
    change o + (L.starProjection (z - o) + Lᗮ.starProjection (z - o)) = z
    rw [L.starProjection_add_starProjection_orthogonal]
    abel
  have hu4 : u ∈ ball (0 : L) (4 * R) := by
    rw [mem_ball, dist_zero_right]
    linarith
  have hcandidate : dist z (q u) < 3 * R / 2 := by
    have heq : q u - z = ((g u - v : Lᗮ) : H) := by
      rw [← huz]
      change (o + ((u : H) + (g u : H))) - (o + ((u : H) + (v : H))) = (g u : H) - (v : H)
      abel
    rw [dist_comm, dist_eq_norm, heq]
    change ‖g u - v‖ < 3 * R / 2
    have hh := norm_sub_le (g u) v
    have hb := hsmall u hu4
    have haR := mul_le_mul_of_nonneg_right ha hR.le
    nlinarith
  exact ⟨hu, hcandidate⟩

theorem exists_nearest_on_buffered_normal_graph
    (L : Submodule ℝ H) [FiniteDimensional ℝ L]
    (o : H) (g : L → Lᗮ) (W : Set H) (R a : ℝ)
    (hR : 0 < R) (ha : a ≤ 1 / 100)
    (hg : ContinuousOn g (ball 0 (4 * R)))
    (hsmall : ∀ t ∈ ball (0 : L) (4 * R), ‖g t‖ ≤ a * R)
    (hgraph : ∀ t ∈ ball (0 : L) (4 * R),
      o + orthogonalCoordinateSum L (t, g t) ∈ W)
    (hsheet : ∀ y ∈ W ∩ ball o (3 * R), ∃ t ∈ ball (0 : L) (4 * R),
      y = o + orthogonalCoordinateSum L (t, g t))
    (z : H) (hz : z ∈ ball o R) :
    ∃ t ∈ ball (0 : L) (5 * R / 2),
      o + orthogonalCoordinateSum L (t, g t) ∈ W ∧
      IsMinOn (fun y => dist z y) W (o + orthogonalCoordinateSum L (t, g t)) := by
  classical
  let q : L → H := fun t => o + orthogonalCoordinateSum L (t, g t)
  let u : L := L.orthogonalProjectionOnto (z - o)
  obtain ⟨hu, hcandidate⟩ := buffered_graph_candidate L o g R a hR ha hsmall z hz
  change ‖u‖ < R at hu
  change dist z (q u) < 3 * R / 2 at hcandidate
  let K : Set L := closedBall 0 (5 * R / 2)
  have hK4 : K ⊆ ball (0 : L) (4 * R) := by
    intro t ht
    have ht' : ‖t‖ ≤ 5 * R / 2 := by simpa only [K, mem_closedBall, dist_zero_right] using ht
    rw [mem_ball, dist_zero_right]
    linarith
  have huK : u ∈ K := by
    change dist u 0 ≤ 5 * R / 2
    rw [dist_zero_right]
    linarith
  have hq : ContinuousOn q K :=
    continuousOn_const.add ((orthogonalCoordinateSum L).continuous.comp_continuousOn
      (continuousOn_id.prodMk ((hg.mono hK4))))
  have hdist : ContinuousOn (fun s : L => dist z (q s)) K := by
    simpa only [dist_eq_norm, Pi.sub_apply] using
      ((continuousOn_const : ContinuousOn (fun _ : L => z) K).sub hq).norm
  obtain ⟨t, ht, hmin⟩ := (isCompact_closedBall (0 : L) (5 * R / 2)).exists_isMinOn
    ⟨u, huK⟩ hdist
  have htnear : dist z (q t) < 3 * R / 2 := (hmin huK).trans_lt hcandidate
  have hhorizontal (s : L) : ‖s - u‖ ≤ dist z (q s) := by
    have heq : L.orthogonalProjectionOnto (q s - z) = s - u := by
      have hsub : q s - z = ((s : H) + (g s : H)) - (z - o) := by
        change (o + ((s : H) + (g s : H))) - z = _
        abel
      rw [hsub, map_sub, map_add, L.orthogonalProjectionOnto_mem_subspace_eq_self,
        Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal (g s).property, add_zero]
    have hp := L.norm_orthogonalProjectionOnto_apply_le (q s - z)
    rw [heq] at hp
    simpa only [dist_eq_norm, norm_sub_rev] using hp
  have htinside : t ∈ ball (0 : L) (5 * R / 2) := by
    have hh := hhorizontal t
    have htri : ‖t‖ ≤ ‖t - u‖ + ‖u‖ := by
      calc
        ‖t‖ = ‖(t - u) + u‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    rw [mem_ball, dist_zero_right]
    linarith
  refine ⟨t, htinside, hgraph t (hK4 ht), ?_⟩
  intro y hy
  change dist z (q t) ≤ dist z y
  by_cases hyball : y ∈ ball o (3 * R)
  · obtain ⟨s, _hs, rfl⟩ := hsheet y ⟨hy, hyball⟩
    by_cases hsK : s ∈ K
    · exact hmin hsK
    · have hslarge : 5 * R / 2 < ‖s‖ := by
        simpa only [K, mem_closedBall, dist_zero_right, not_le] using hsK
      have hh := hhorizontal s
      have htri : ‖s‖ ≤ ‖s - u‖ + ‖u‖ := by
        calc
          ‖s‖ = ‖(s - u) + u‖ := by rw [sub_add_cancel]
          _ ≤ _ := norm_add_le _ _
      change dist z (q t) ≤ dist z (q s)
      linarith
  · have hyfar : 3 * R ≤ dist y o := le_of_not_gt hyball
    have htri := dist_triangle y z o
    rw [dist_comm y z] at htri
    have hzo : dist z o < R := hz
    linarith

theorem minimizer_mem_buffered_normal_graph
    (L : Submodule ℝ H) [L.HasOrthogonalProjection]
    (o : H) (g : L → Lᗮ) (W : Set H) (R a : ℝ)
    (hR : 0 < R) (ha : a ≤ 1 / 100)
    (hsmall : ∀ t ∈ ball (0 : L) (4 * R), ‖g t‖ ≤ a * R)
    (hgraph : ∀ t ∈ ball (0 : L) (4 * R),
      o + orthogonalCoordinateSum L (t, g t) ∈ W)
    (hsheet : ∀ y ∈ W ∩ ball o (3 * R), ∃ t ∈ ball (0 : L) (4 * R),
      y = o + orthogonalCoordinateSum L (t, g t))
    (z y : H) (hz : z ∈ ball o R) (hy : y ∈ W)
    (hmin : IsMinOn (fun w => dist z w) W y) :
    dist z y < 3 * R / 2 ∧ y ∈ ball o (5 * R / 2) ∧
      ∃ t ∈ ball (0 : L) (5 * R / 2),
        y = o + orthogonalCoordinateSum L (t, g t) := by
  let u : L := L.orthogonalProjectionOnto (z - o)
  obtain ⟨hu, hcandidate⟩ := buffered_graph_candidate L o g R a hR ha hsmall z hz
  change ‖u‖ < R at hu
  change dist z (o + orthogonalCoordinateSum L (u, g u)) < 3 * R / 2 at hcandidate
  have hu4 : u ∈ ball (0 : L) (4 * R) := by
    rw [mem_ball, dist_zero_right]
    linarith
  have hnear : dist z y < 3 * R / 2 := (hmin (hgraph u hu4)).trans_lt hcandidate
  have hynear : dist y o < 5 * R / 2 := by
    have ht := dist_triangle y z o
    rw [dist_comm y z] at ht
    have hzdist : dist z o < R := hz
    linarith
  have hy3 : y ∈ ball o (3 * R) := by
    change dist y o < 3 * R
    linarith
  obtain ⟨t, _ht4, heq⟩ := hsheet y ⟨hy, hy3⟩
  have hprojection : L.orthogonalProjectionOnto (y - o) = t := by
    have hyo : y - o = (t : H) + (g t : H) := by
      rw [heq]
      change (o + ((t : H) + (g t : H))) - o = _
      abel
    rw [hyo, map_add, L.orthogonalProjectionOnto_mem_subspace_eq_self,
      Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal (g t).property, add_zero]
  have ht : t ∈ ball (0 : L) (5 * R / 2) := by
    rw [mem_ball, dist_zero_right]
    have hp := L.norm_orthogonalProjectionOnto_apply_le (y - o)
    rw [hprojection] at hp
    exact hp.trans_lt (by simpa only [dist_eq_norm] using hynear)
  exact ⟨hnear, hynear, t, ht, heq⟩

end DifferentialGeometry.Analysis
