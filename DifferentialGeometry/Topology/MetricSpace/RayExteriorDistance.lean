import DifferentialGeometry.Topology.MetricSpace.ClosedSegmentNeighborhood

set_option autoImplicit false

open Set Metric

namespace Metric

variable {X : Type*} [MetricSpace X]

theorem dist_to_isometric_ray_of_not_mem_range
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    (hopen : ∀ (a b : ℝ) (σ : Icc a b → X), Isometry σ →
      IsOpen (σ '' {t | a < (t : ℝ) ∧ (t : ℝ) < b}))
    {γ : Ici (0 : ℝ) → X} (hγ : Isometry γ) {x : X} (hx : x ∉ range γ)
    (t : Ici (0 : ℝ)) :
    dist x (γ t) = dist x (γ ⟨0, by simp⟩) + (t : ℝ) := by
  let p := γ ⟨0, by simp⟩
  let D := dist x p
  let R := D + (t : ℝ) + 1
  have hD : 0 ≤ D := dist_nonneg
  have ht0 : 0 ≤ (t : ℝ) := t.property
  have hR : 0 < R := by dsimp [R]; linarith
  have hDR : D < R := by dsimp [R]; linarith
  have htR : (t : ℝ) ≤ R := by dsimp [R]; linarith
  let c := γ ⟨R, hR.le⟩
  have hcp : dist c p = R := by
    dsimp [c, p]
    rw [hγ.dist_eq]
    simp only [Subtype.dist_eq, Real.dist_eq, sub_zero, abs_of_pos hR]
  have hb := closedBall_on_isometric_ray_of_isOpen_segments hsegments hopen hγ hR
  have hRx : R < dist c x := by
    by_contra hn
    have hxc : x ∈ closedBall c R := by
      simpa only [mem_closedBall, dist_comm] using le_of_not_gt hn
    have hxray : x ∈ γ '' {s | (s : ℝ) ≤ 2 * R} := by rwa [hb] at hxc
    exact hx ((image_subset_range _ _) hxray)
  have hcx : dist c x ≤ R + D := by
    have h := dist_triangle c p x
    rw [hcp, dist_comm p x] at h
    exact h
  obtain ⟨f, _, hf0, hf1, hfd⟩ := hsegments c x
  obtain ⟨σ, hσ, hσ0, hσend⟩ := exists_isometric_segment_of_dist_eq_mul hf0 hf1 hfd
  let s : Icc (0 : ℝ) (dist c x) := ⟨R, hR.le, hRx.le⟩
  have hσs : dist (σ s) c = R := by
    rw [← hσ0, hσ.dist_eq]
    simp only [Subtype.dist_eq, Real.dist_eq, sub_zero, s, abs_of_pos hR]
  have hσx : dist (σ s) x = dist c x - R := by
    calc
      dist (σ s) x = dist (σ s) (σ ⟨dist c x, (hR.trans hRx).le, le_rfl⟩) :=
        congrArg (dist (σ s)) hσend.symm
      _ = dist s ⟨dist c x, (hR.trans hRx).le, le_rfl⟩ := hσ.dist_eq _ _
      _ = dist c x - R := by
        change |R - dist c x| = dist c x - R
        rw [abs_of_nonpos (by linarith)]
        ring
  have hσmem : σ s ∈ γ '' {u | (u : ℝ) ≤ 2 * R} := by
    rw [← hb]
    change dist (σ s) c ≤ R
    exact hσs.le
  obtain ⟨u, _, hu⟩ := hσmem
  have hud : |(u : ℝ) - R| = R := by
    have h := hσs
    rw [← hu, hγ.dist_eq] at h
    exact h
  have hσp : σ s = p := by
    rcases le_total (u : ℝ) R with huR | hRu
    · rw [abs_of_nonpos (sub_nonpos.mpr huR)] at hud
      have hu0 : u = (⟨0, by simp⟩ : Ici (0 : ℝ)) := Subtype.ext (by linarith)
      rw [← hu, hu0]
    · rw [abs_of_nonneg (sub_nonneg.mpr hRu)] at hud
      have hu2 : (u : ℝ) = 2 * R := by linarith
      have hpu : dist p (σ s) = 2 * R := by
        rw [← hu, hγ.dist_eq]
        change |0 - (u : ℝ)| = 2 * R
        rw [zero_sub, abs_neg, abs_of_nonneg u.property, hu2]
      have htri := dist_triangle p x (σ s)
      rw [hpu, dist_comm p x, dist_comm x (σ s), hσx] at htri
      change 2 * R ≤ D + (dist c x - R) at htri
      linarith
  have heq : dist c x = D + R := by
    rw [hσp, dist_comm p x] at hσx
    change D = dist c x - R at hσx
    linarith
  have hct : dist (γ t) c = R - (t : ℝ) := by
    rw [hγ.dist_eq]
    change |(t : ℝ) - R| = R - (t : ℝ)
    rw [abs_of_nonpos (sub_nonpos.mpr htR)]
    ring
  have hpt : dist p (γ t) = (t : ℝ) := by
    rw [hγ.dist_eq]
    simp only [Subtype.dist_eq, Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg ht0]
  have hlo := dist_triangle x (γ t) c
  have hhi := dist_triangle x p (γ t)
  rw [dist_comm x c, heq, hct] at hlo
  rw [hpt] at hhi
  change dist x (γ t) = D + (t : ℝ)
  change dist x (γ t) ≤ D + (t : ℝ) at hhi
  linarith

end Metric
