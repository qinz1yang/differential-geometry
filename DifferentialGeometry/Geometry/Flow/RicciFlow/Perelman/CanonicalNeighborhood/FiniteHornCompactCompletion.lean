import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornCompactHull

set_option autoImplicit false
noncomputable section
open Manifold Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle

universe u
variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W] [SigmaCompactSpace W]

theorem exists_finiteHorn_compact_complete_metric_depth :
    ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g),
      H₀ ≤ H.collar_depth → ∀ outer : ℕ, ∃ inner : ℕ,
        closure (H.subend inner) ⊆ H.subend outer ∧
        ∀ A B : Set W, IsCompact A → IsCompact B →
          A ⊆ H.subend inner → B ⊆ H.subend inner →
          ∃ (g' : SmoothRiemannianMetric I3 W) (U K : Set W) (eta : ℝ),
            RiemannianMetricComplete g' ∧ IsOpen U ∧ IsCompact K ∧ 0 < eta ∧
            K ⊆ U ∧ A ∪ B ⊆ U ∧
            (∀ z ∈ U, g'.inner z = g.inner z) ∧
            (∀ z (v : TangentSpace I3 z), g.inner z v v ≤ g'.inner z v v) ∧
            ∀ x ∈ A, ∀ y ∈ B,
              riemannianEDistOf g' x y = ENNReal.ofReal (dist x y) ∧
              (∀ z : W, dist x z + dist z y ≤ dist x y + eta →
                z ∈ H.subend outer ∩ K) ∧
              ∀ gamma : ℝ → W,
                ContMDiffOn 𝓘(ℝ, ℝ) I3 1 gamma (Icc (0 : ℝ) 1) →
                gamma 0 = x → gamma 1 = y →
                metricPathELength g gamma 0 1 ≤
                  ENNReal.ofReal (dist x y) + ENNReal.ofReal eta →
                ∀ s ∈ Icc (0 : ℝ) 1, gamma s ∈ H.subend outer ∩ K := by
  obtain ⟨Hsave, hHsave, hsave⟩ := exists_finiteHorn_no_endpoint_shortcut_depth (W := W)
  obtain ⟨Hmin, _hHmin, hmin⟩ := exists_finiteHorn_deep_minimizer_depth (W := W)
  refine ⟨max Hsave Hmin, hHsave.trans_le (le_max_left _ _), ?_⟩
  intro g H hdepth outer
  obtain ⟨j, hj, _hconnect⟩ := hmin g H ((le_max_right _ _).trans hdepth) outer
  obtain ⟨d, hd, hrays⟩ := finiteHorn_exists_intrinsic_endRay_near_endpoint g H
  obtain ⟨delta, hdelta, hball⟩ := finiteHorn_ball_subset_subend g H outer
  obtain ⟨k, hk⟩ := finiteHorn_subend_radial_small g H
    (lt_min hd (by positivity : 0 < delta / 8))
  have hmono : Antitone H.subend := antitone_nat_of_succ_le H.nested
  refine ⟨max j k, (closure_mono (hmono (le_max_left j k))).trans hj, ?_⟩
  intro A B hA hB hAin hBin
  have hsmall (z : W) (hz : z ∈ H.subend (max j k)) :
      dist (z : UniformSpace.Completion W) H.endpoint < min d (delta / 8) :=
    hk z (hmono (le_max_right j k) hz)
  have hgap : ∀ x ∈ A, ∀ y ∈ B,
      dist x y < dist (x : UniformSpace.Completion W) H.endpoint +
        dist (y : UniformSpace.Completion W) H.endpoint := by
    intro x hx y hy
    obtain ⟨a, ha⟩ := hrays x ((hsmall x (hAin hx)).trans_le (min_le_left _ _))
    obtain ⟨b, hb⟩ := hrays y ((hsmall y (hBin hy)).trans_le (min_le_left _ _))
    have haRad := a.radial a.length ⟨a.length_pos, le_rfl⟩
    have hbRad := b.radial b.length ⟨b.length_pos, le_rfl⟩
    rw [ha] at haRad
    rw [hb] at hbRad
    have h := hsave g H ((le_max_left _ _).trans hdepth) a b
    rwa [ha, hb, ← haRad, ← hbRad] at h
  obtain ⟨eps, heps, K₀, hK₀, hcapture⟩ :=
    finiteHorn_exists_compact_near_minimizing_hull g H outer hA hB hgap
  let eta : ℝ := min eps (delta / 4)
  have heta : 0 < eta := lt_min heps (by positivity)
  let K : Set W := K₀ ∪ (A ∪ B)
  have hK : IsCompact K := hK₀.union (hA.union hB)
  have hpointTrap : ∀ x ∈ A, ∀ y ∈ B, ∀ z : W,
      dist x z + dist z y ≤ dist x y + eta → z ∈ H.subend outer ∩ K := by
    intro x hx y hy z hlength
    have hxrad := (hsmall x (hAin hx)).trans_le (min_le_right _ _)
    have hyrad := (hsmall y (hBin hy)).trans_le (min_le_right _ _)
    have hxy := hgap x hx y hy
    have htri := dist_triangle (z : UniformSpace.Completion W)
      (x : UniformSpace.Completion W) H.endpoint
    rw [UniformSpace.Completion.dist_eq, dist_comm z x] at htri
    have hetadelta : eta ≤ delta / 4 := min_le_right _ _
    have hrad : dist (z : UniformSpace.Completion W) H.endpoint < delta := by
      linarith [dist_nonneg (x := z) (y := y)]
    have houter : z ∈ H.subend outer := hball _ hrad
    refine ⟨houter, Or.inl (hcapture x hx y hy z houter ?_)⟩
    exact hlength.trans (by
      dsimp only [eta]
      gcongr
      exact min_le_left _ _)
  have htrap : ∀ x ∈ A, ∀ y ∈ B, ∀ gamma : ℝ → W,
      ContMDiffOn 𝓘(ℝ, ℝ) I3 1 gamma (Icc (0 : ℝ) 1) → gamma 0 = x → gamma 1 = y →
      metricPathELength g gamma 0 1 ≤ riemannianEDistOf g x y + ENNReal.ofReal eta →
      ∀ s ∈ Icc (0 : ℝ) 1, gamma s ∈ H.subend outer ∩ K := by
    intro x hx y hy gamma hsmooth hstart hend hnear s hs
    have hleft := edistOf_le_metricPathELength g hs.1
      (hsmooth.mono (Icc_subset_Icc le_rfl hs.2))
    have hright := edistOf_le_metricPathELength g hs.2
      (hsmooth.mono (Icc_subset_Icc hs.1 le_rfl))
    rw [hstart, H.edist_eq_ofReal_dist] at hleft
    rw [hend, H.edist_eq_ofReal_dist] at hright
    have hsum := ((add_le_add hleft hright).trans_eq
      (metricPathELength_add g gamma hs.1 hs.2)).trans hnear
    rw [← ENNReal.ofReal_add dist_nonneg dist_nonneg, H.edist_eq_ofReal_dist,
      ← ENNReal.ofReal_add dist_nonneg heta.le] at hsum
    have hlength : dist x (gamma s) + dist (gamma s) y ≤ dist x y + eta :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hsum
    exact hpointTrap x hx y hy (gamma s) hlength
  obtain ⟨g', U, hcomplete, hU, hKU, heq, hle⟩ :=
    exists_riemannianMetricComplete_eqOn_of_isCompact g hK
  refine ⟨g', U, K, eta, hcomplete, hU, hK, heta, hKU,
    fun z hz => hKU (Or.inr hz), heq, hle, ?_⟩
  intro x hx y hy
  have hfinite : riemannianEDistOf g x y ≠ ⊤ := by
    rw [H.edist_eq_ofReal_dist]
    exact ENNReal.ofReal_ne_top
  have hdist := riemannianEDistOf_eq_of_near_minimizer_trapping g g' heta hfinite
    (fun z hz => heq z (hKU hz)) hle
    (fun gamma hsmooth hstart hend hnear s hs =>
      (htrap x hx y hy gamma hsmooth hstart hend hnear s hs).2)
  refine ⟨hdist.trans (edist_eq_ofReal_dist g H x y), hpointTrap x hx y hy, ?_⟩
  simpa only [H.edist_eq_ofReal_dist] using htrap x hx y hy

theorem auxiliary_sectional_nonnegative_of_distance_add
    (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    (g' : SmoothRiemannianMetric I3 W) {U : Set W}
    (hU : IsOpen U) (heq : ∀ z ∈ U, g'.inner z = g.inner z)
    (hle : ∀ z (v : TangentSpace I3 z), g.inner z v v ≤ g'.inner z v v)
    {x y : W} (hdist : riemannianEDistOf g' x y = ENNReal.ofReal (dist x y))
    {eta : ℝ} (heta : 0 ≤ eta)
    (hcapture : ∀ z : W, dist x z + dist z y ≤ dist x y + eta → z ∈ U)
    {z : W} (hz : riemannianEDistOf g' x z + riemannianEDistOf g' z y =
      riemannianEDistOf g' x y) :
    metricRm04At (I := I3) g' z ∈ tensor04SectionalNonnegativeCone (I := I3) (M := W) := by
  have hsum := (add_le_add (edistOf_mono g g' hle x z)
    (edistOf_mono g g' hle z y)).trans_eq (hz.trans hdist)
  rw [H.edist_eq_ofReal_dist, H.edist_eq_ofReal_dist,
    ← ENNReal.ofReal_add dist_nonneg dist_nonneg] at hsum
  have hmetric : dist x z + dist z y ≤ dist x y :=
    (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp hsum
  have hzU : z ∈ U := hcapture z (hmetric.trans (le_add_of_nonneg_right heta))
  apply (metricRm04At_mem_tensor04SectionalNonnegativeCone_iff g' z).mpr
  intro v w
  rw [metricRm04StandardAt_congr_metric g g' hU heq hzU v w w v]
  have hslots : (fun i => ![v, w, w, v] i) = vec4 v w w v := by
    funext i
    fin_cases i <;> rfl
  simpa only [zero_mul, metricRm04StandardAt_apply, hslots] using H.nonnegative z (mem_univ z) v w

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
