import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornDeepMinimizers

set_option autoImplicit false
noncomputable section
open Manifold Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W]

theorem finiteHorn_exists_compact_near_minimizing_hull
    (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g) (i : ℕ)
    {A B : Set W} (hA : IsCompact A) (hB : IsCompact B)
    (hgap : ∀ x ∈ A, ∀ y ∈ B,
      dist x y < dist (x : UniformSpace.Completion W) H.endpoint +
        dist (y : UniformSpace.Completion W) H.endpoint) :
    ∃ eps : ℝ, 0 < eps ∧ ∃ K : Set W, IsCompact K ∧
      ∀ x ∈ A, ∀ y ∈ B, ∀ z ∈ H.subend i,
        dist x z + dist z y ≤ dist x y + eps → z ∈ K := by
  by_cases hAne : A.Nonempty
  · by_cases hBne : B.Nonempty
    · let radial (x : W) : ℝ := dist (x : UniformSpace.Completion W) H.endpoint
      let gap (q : W × W) : ℝ := radial q.1 + radial q.2 - dist q.1 q.2
      have hc : Continuous radial :=
        (UniformSpace.Completion.continuous_coe W).dist continuous_const
      have hgapCont : Continuous gap :=
        ((hc.comp continuous_fst).add (hc.comp continuous_snd)).sub
          (continuous_fst.dist continuous_snd)
      obtain ⟨q, hq, hmin⟩ := (hA.prod hB).exists_isMinOn
        (hAne.prod hBne) hgapCont.continuousOn
      have hqpos : 0 < gap q := sub_pos.mpr (hgap q.1 hq.1 q.2 hq.2)
      let eps : ℝ := gap q / 2
      let a : ℝ := gap q / 4
      have heps : 0 < eps := half_pos hqpos
      have ha : 0 < a := by dsimp only [a]; positivity
      let K : Set W := {z : W |
        (z : UniformSpace.Completion W) ∈
          closure ((fun w : W => (w : UniformSpace.Completion W)) '' H.subend i) ∧
        a ≤ radial z}
      refine ⟨eps, heps, K, finiteHorn_isCompact_radial_annulus g H i ha, ?_⟩
      intro x hx y hy z hz hsegment
      refine ⟨subset_closure ⟨z, hz, rfl⟩, ?_⟩
      have hxy : gap q ≤ gap (x, y) := hmin ⟨hx, hy⟩
      have hxz := dist_triangle (x : UniformSpace.Completion W)
        (z : UniformSpace.Completion W) H.endpoint
      have hyz := dist_triangle (y : UniformSpace.Completion W)
        (z : UniformSpace.Completion W) H.endpoint
      rw [UniformSpace.Completion.dist_eq] at hxz hyz
      rw [dist_comm y z] at hyz
      change radial x ≤ dist x z + radial z at hxz
      change radial y ≤ dist z y + radial z at hyz
      dsimp only [gap] at hxy
      dsimp only [eps] at hsegment
      dsimp only [a]
      linarith
    · refine ⟨1, zero_lt_one, ∅, isCompact_empty, ?_⟩
      intro x hx y hy
      exact (hBne ⟨y, hy⟩).elim
  · refine ⟨1, zero_lt_one, ∅, isCompact_empty, ?_⟩
    intro x hx
    exact (hAne ⟨x, hx⟩).elim

variable [SigmaCompactSpace W]

theorem exists_finiteHorn_compact_connectors_depth :
    ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g),
      H₀ ≤ H.collar_depth → ∀ outer : ℕ, ∃ inner : ℕ,
        closure (H.subend inner) ⊆ H.subend outer ∧
        ∀ A B : Set W, IsCompact A → IsCompact B →
          A ⊆ H.subend inner → B ⊆ H.subend inner →
          ∃ K : Set W, IsCompact K ∧ ∀ x ∈ A, ∀ y ∈ B,
            ∃ gamma : ℝ → W, gamma 0 = x ∧ gamma 1 = y ∧
              ContMDiff 𝓘(ℝ, ℝ) I3 ∞ gamma ∧
              (∀ s ∈ Icc (0 : ℝ) 1, gamma s ∈ H.subend outer ∩ K) ∧
              ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
                dist (gamma s) (gamma t) = |s - t| * dist x y := by
  obtain ⟨Hsave, hHsave, hsave⟩ := exists_finiteHorn_no_endpoint_shortcut_depth (W := W)
  obtain ⟨Hmin, hHmin, hmin⟩ := exists_finiteHorn_deep_minimizer_depth (W := W)
  refine ⟨max Hsave Hmin, hHsave.trans_le (le_max_left _ _), ?_⟩
  intro g H hdepth outer
  obtain ⟨j, hj, hconnect⟩ := hmin g H ((le_max_right _ _).trans hdepth) outer
  obtain ⟨d, hd, hrays⟩ := finiteHorn_exists_intrinsic_endRay_near_endpoint g H
  obtain ⟨k, hk⟩ := finiteHorn_subend_radial_small g H hd
  have hmono : Antitone H.subend := antitone_nat_of_succ_le H.nested
  refine ⟨max j k, (closure_mono (hmono (le_max_left j k))).trans hj, ?_⟩
  intro A B hA hB hAin hBin
  have hgap : ∀ x ∈ A, ∀ y ∈ B,
      dist x y < dist (x : UniformSpace.Completion W) H.endpoint +
        dist (y : UniformSpace.Completion W) H.endpoint := by
    intro x hx y hy
    obtain ⟨a, ha⟩ := hrays x (hk x (hmono (le_max_right j k) (hAin hx)))
    obtain ⟨b, hb⟩ := hrays y (hk y (hmono (le_max_right j k) (hBin hy)))
    have haRad := a.radial a.length ⟨a.length_pos, le_rfl⟩
    have hbRad := b.radial b.length ⟨b.length_pos, le_rfl⟩
    rw [ha] at haRad
    rw [hb] at hbRad
    have h := hsave g H ((le_max_left _ _).trans hdepth) a b
    rwa [ha, hb, ← haRad, ← hbRad] at h
  obtain ⟨eps, heps, K, hK, htrap⟩ :=
    finiteHorn_exists_compact_near_minimizing_hull g H outer hA hB hgap
  refine ⟨K, hK, ?_⟩
  intro x hx y hy
  obtain ⟨gamma, hstart, hend, hsmooth, hmem, hdist⟩ :=
    hconnect x (hmono (le_max_left j k) (hAin hx))
      y (hmono (le_max_left j k) (hBin hy))
  refine ⟨gamma, hstart, hend, hsmooth, ?_, hdist⟩
  intro s hs
  refine ⟨hmem s hs, htrap x hx y hy (gamma s) (hmem s hs) ?_⟩
  have hleft := hdist 0 ⟨le_rfl, by norm_num⟩ s hs
  have hright := hdist s hs 1 ⟨by norm_num, le_rfl⟩
  rw [hstart, abs_of_nonpos (by linarith [hs.1] : (0 : ℝ) - s ≤ 0)] at hleft
  rw [hend, abs_of_nonpos (by linarith [hs.2] : s - 1 ≤ 0)] at hright
  nlinarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
