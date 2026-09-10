import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornIntrinsicRays
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornCollarRadius
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornSectionOrder

set_option autoImplicit false
noncomputable section
open Filter Manifold Set
open DifferentialGeometry.Geometry.Curvature
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W]

theorem exists_finiteHorn_no_endpoint_shortcut_depth :
    ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g),
      H₀ ≤ H.collar_depth → ∀ a b : EndRay H.endpoint,
        dist (a.point a.length) (b.point b.length) < a.length + b.length := by
  obtain ⟨D, hD, hshortcuts⟩ := exists_uniform_transverse_shortcuts (M := W)
  refine ⟨4 * (D + 1), by positivity, ?_⟩
  intro g H hdepth a b
  obtain ⟨w, C, F, p, G, _hcenter, hsource, hQ, ⟨cmp⟩, _hnear, haout, hbout⟩ :=
    finiteHorn_exists_inner_collar g H (a.point a.length) (b.point b.length)
      (eta := 1) (by norm_num)
  obtain ⟨s, hs, q, hq⟩ := G.endRay_meets_center g H a haout
  obtain ⟨t, ht, r, hr⟩ := G.endRay_meets_center g H b hbout
  have hlevel : ∀ z : Sphere 2, (z, (0 : ℝ)) ∈
      (univ ×ˢ Icc (-H.collar_depth) H.collar_depth : Set Cylinder) := by
    intro z
    exact ⟨mem_univ _, by constructor <;> linarith [H.collar_depth_pos]⟩
  obtain ⟨gamma, hstart, hend, hsmooth, _hmem, hlength⟩ :=
    hshortcuts C (fun _ => C.metric 0)
      (fun _ => scaleMetric (metricScalarAt g w) hQ g) F
      (univ ×ˢ Icc (-H.collar_depth) H.collar_depth) {0}
      (⌈H.neck_precision⁻¹⌉₊) H.neck_precision 0 cmp rfl H.neck_precision_pos.le
      (by linarith [H.neck_precision_small]) (by simp) hsource hlevel q r
  have hdist := (edistOf_le_metricPathELength (scaleMetric (metricScalarAt g w) hQ g)
    (by norm_num : (0 : ℝ) ≤ 1) hsmooth).trans hlength
  rw [hstart, hend, edistOf_scale, H.edist_eq_ofReal_dist,
    ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at hdist
  have hreal := (ENNReal.ofReal_le_ofReal_iff hD.le).mp hdist
  have hsbound := collar_endpoint_distance_lower_bound g H hQ C F cmp
    (by linarith [H.neck_precision_small]) (by simp) H.collar_depth_pos
    hsource (fun _ hz => hz) q
  have htbound := collar_endpoint_distance_lower_bound g H hQ C F cmp
    (by linarith [H.neck_precision_small]) (by simp) H.collar_depth_pos
    hsource (fun _ hz => hz) r
  rw [hq, a.radial s hs] at hsbound
  rw [hr, b.radial t ht] at htbound
  have hsave : dist (F (q, 0)) (F (r, 0)) < s + t := by
    have hsqrt := Real.sqrt_pos.mpr hQ
    apply (mul_lt_mul_iff_right₀ hsqrt).mp
    nlinarith
  have hleft : dist (a.point a.length) (F (q, 0)) = a.length - s := by
    rw [hq, a.minimizing a.length ⟨a.length_pos, le_rfl⟩ s hs,
      abs_of_nonneg (sub_nonneg.mpr hs.2)]
  have hright : dist (F (r, 0)) (b.point b.length) = b.length - t := by
    rw [hr, b.minimizing t ht b.length ⟨b.length_pos, le_rfl⟩,
      abs_of_nonpos (sub_nonpos.mpr ht.2)]
    ring
  have htri₁ := dist_triangle (a.point a.length) (F (q, 0)) (b.point b.length)
  have htri₂ := dist_triangle (F (q, 0)) (F (r, 0)) (b.point b.length)
  rw [hleft] at htri₁
  rw [hright] at htri₂
  linarith

variable [SigmaCompactSpace W]

theorem exists_finiteHorn_deep_minimizer_depth :
    ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g),
      H₀ ≤ H.collar_depth → ∀ i : ℕ, ∃ j : ℕ, closure (H.subend j) ⊆ H.subend i ∧
        ∀ x ∈ H.subend j, ∀ y ∈ H.subend j,
        ∃ gamma : ℝ → W, gamma 0 = x ∧ gamma 1 = y ∧
          ContMDiff 𝓘(ℝ, ℝ) I3 ∞ gamma ∧
          (∀ s ∈ Icc (0 : ℝ) 1, gamma s ∈ H.subend i) ∧
          ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
            dist (gamma s) (gamma t) = |s - t| * dist x y := by
  obtain ⟨H₀, hH₀, hsave⟩ := exists_finiteHorn_no_endpoint_shortcut_depth (W := W)
  refine ⟨H₀, hH₀, ?_⟩
  intro g H hdepth i
  let : IsManifold I3 1 W := IsManifold.of_le (n := (∞ : WithTop ℕ∞)) (by decide)
  let : T2Space (TangentBundle I3 W) := inferInstance
  obtain ⟨d, hd, hrays⟩ := finiteHorn_exists_intrinsic_endRay_near_endpoint g H
  obtain ⟨delta, hdelta, hball⟩ := finiteHorn_ball_subset_subend g H i
  obtain ⟨j, hj⟩ := finiteHorn_subend_radial_small g H (lt_min hd (by positivity : 0 < delta / 8))
  obtain ⟨k, hk⟩ := ((tendsto_order.1 H.cut_height_zero).2 _ (H.cut_height_mem i).1).exists
  have hkbuffer : closure (H.subend k) ⊆ H.subend i := by
    have hclosed : IsClosed {z : W | H.tube.height z ≤ H.cut_height k} :=
      isClosed_le H.tube.continuous_height continuous_const
    have hsub : H.subend k ⊆ {z : W | H.tube.height z ≤ H.cut_height k} := by
      intro z hz
      rw [H.subend_eq k] at hz
      change H.tube.height z < H.cut_height k at hz
      exact hz.le
    intro z hz
    rw [H.subend_eq i]
    exact (closure_minimal hsub hclosed hz).trans_lt hk
  have hmono : Antitone H.subend := antitone_nat_of_succ_le H.nested
  refine ⟨max j k, (closure_mono (hmono (le_max_right j k))).trans hkbuffer, ?_⟩
  intro x hx y hy
  replace hx := hmono (le_max_left j k) hx
  replace hy := hmono (le_max_left j k) hy
  have hxd := (hj x hx).trans_le (min_le_left _ _)
  have hyd := (hj y hy).trans_le (min_le_left _ _)
  have hxdelta : dist (x : UniformSpace.Completion W) H.endpoint < delta / 8 :=
    (hj x hx).trans_le (min_le_right _ _)
  have hydelta : dist (y : UniformSpace.Completion W) H.endpoint < delta / 8 :=
    (hj y hy).trans_le (min_le_right _ _)
  obtain ⟨a, ha⟩ := hrays x hxd
  obtain ⟨b, hb⟩ := hrays y hyd
  have haRad := a.radial a.length ⟨a.length_pos, le_rfl⟩
  have hbRad := b.radial b.length ⟨b.length_pos, le_rfl⟩
  rw [ha] at haRad
  rw [hb] at hbRad
  have hstrict := hsave g H hdepth a b
  rw [ha, hb, ← haRad, ← hbRad] at hstrict
  let rx : ℝ := dist (x : UniformSpace.Completion W) H.endpoint
  let ry : ℝ := dist (y : UniformSpace.Completion W) H.endpoint
  change dist x y < rx + ry at hstrict
  let eta : ℝ := (rx + ry - dist x y) / 2
  have heta : 0 < eta := half_pos (sub_pos.mpr hstrict)
  let low : ℝ := (rx + ry - dist x y - eta) / 2
  have hlow : 0 < low := by dsimp [low, eta]; linarith
  let K : Set W := {z | (z : UniformSpace.Completion W) ∈
    closure ((fun w : W => (w : UniformSpace.Completion W)) '' H.subend i) ∧
    low ≤ dist (z : UniformSpace.Completion W) H.endpoint}
  have hK : IsCompact K := finiteHorn_isCompact_radial_annulus g H i hlow
  have hfinite : riemannianEDistOf g x y ≠ ⊤ := by
    rw [H.edist_eq_ofReal_dist]
    exact ENNReal.ofReal_ne_top
  have htrap : ∀ gamma : ℝ → W,
      ContMDiffOn 𝓘(ℝ, ℝ) I3 1 gamma (Icc (0 : ℝ) 1) → gamma 0 = x → gamma 1 = y →
      metricPathELength g gamma 0 1 ≤ riemannianEDistOf g x y + ENNReal.ofReal eta →
      ∀ s ∈ Icc (0 : ℝ) 1, gamma s ∈ K := by
    intro gamma hsmooth hstart hend hnear s hs
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
    have htriX := dist_triangle (x : UniformSpace.Completion W)
      (gamma s : UniformSpace.Completion W) H.endpoint
    have htriY := dist_triangle (y : UniformSpace.Completion W)
      (gamma s : UniformSpace.Completion W) H.endpoint
    have htriOut := dist_triangle (gamma s : UniformSpace.Completion W)
      (x : UniformSpace.Completion W) H.endpoint
    rw [UniformSpace.Completion.dist_eq] at htriX htriY htriOut
    rw [dist_comm y (gamma s)] at htriY
    rw [dist_comm (gamma s) x] at htriOut
    change rx ≤ dist x (gamma s) + dist (gamma s : UniformSpace.Completion W) H.endpoint at htriX
    change ry ≤ dist (gamma s) y + dist (gamma s : UniformSpace.Completion W) H.endpoint at htriY
    change dist (gamma s : UniformSpace.Completion W) H.endpoint ≤ dist x (gamma s) + rx at htriOut
    have hradlow : low ≤ dist (gamma s : UniformSpace.Completion W) H.endpoint := by
      dsimp [low]
      linarith
    have hradup : dist (gamma s : UniformSpace.Completion W) H.endpoint < delta := by
      change rx < delta / 8 at hxdelta
      change ry < delta / 8 at hydelta
      dsimp [eta] at hlength
      linarith [dist_nonneg (x := gamma s) (y := y)]
    exact ⟨subset_closure ⟨gamma s, hball _ hradup, rfl⟩, hradlow⟩
  obtain ⟨gamma, hstart, hend, hsmooth, _hmem, _hlength, hsub⟩ :=
    exists_smooth_minimizer_with_subinterval_lengths g hK heta hfinite htrap
  let L : ℝ≥0 := ⟨dist x y, dist_nonneg⟩
  have hLip : LipschitzOnWith L gamma (Icc (0 : ℝ) 1) := by
    apply lipschitzOnWith_of_subinterval_lengths (L := L) g H
      hsmooth dist_nonneg le_rfl
    intro s hs t ht
    simpa only [H.edist_eq_ofReal_dist] using hsub s hs t ht
  have hfLip : LipschitzWith L (fun s : Icc (0 : ℝ) 1 => gamma s) := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    exact (lipschitzOnWith_iff_dist_le_mul.mp hLip) s s.property t t.property
  have hmetric : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      dist (gamma s) (gamma t) = |s - t| * dist x y := by
    have hfull : dist (gamma 0) (gamma 1) = L := by rw [hstart, hend]; rfl
    have heq := dist_eq_mul_of_lipschitz_interval
      (fun s : Icc (0 : ℝ) 1 => gamma s) hfLip hfull
    intro s hs t ht
    have h := heq ⟨s, hs⟩ ⟨t, ht⟩
    change dist (gamma s) (gamma t) = dist x y * |s - t| at h
    simpa only [mul_comm] using h
  refine ⟨gamma, hstart, hend, hsmooth, ?_, hmetric⟩
  intro s hs
  apply hball
  have hdist : dist (gamma s) x ≤ dist x y := by
    have h := hmetric s hs 0 (by norm_num)
    rw [hstart, sub_zero, abs_of_nonneg hs.1] at h
    rw [h]
    exact mul_le_of_le_one_left dist_nonneg hs.2
  have htri := dist_triangle (gamma s : UniformSpace.Completion W)
    (x : UniformSpace.Completion W) H.endpoint
  rw [UniformSpace.Completion.dist_eq] at htri
  change rx < delta / 8 at hxdelta
  change ry < delta / 8 at hydelta
  change dist (gamma s : UniformSpace.Completion W) H.endpoint ≤ dist (gamma s) x + rx at htri
  linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
