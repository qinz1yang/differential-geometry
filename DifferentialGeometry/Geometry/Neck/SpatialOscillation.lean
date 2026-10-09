import DifferentialGeometry.Geometry.Metric.SmoothLipschitz
import DifferentialGeometry.Geometry.Neck.Spatial
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CollarMetricControl

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

set_option backward.isDefEq.respectTransparency false in
private theorem abs_sub_le_of_path_bound
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    (g : SmoothRiemannianMetric I3 M) {f : M → ℝ} {γ : ℝ → M} {a b L B : ℝ}
    (hab : a ≤ b) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hγ : ContMDiffOn 𝓘(ℝ) I3 1 γ (Icc a b))
    (hf : ∀ t ∈ Icc a b, ContMDiffAt I3 𝓘(ℝ) 1 f (γ t))
    (hbound : ∀ t ∈ Ioo a b, ∀ v : TangentSpace I3 (γ t),
      |(show ℝ from mfderiv I3 𝓘(ℝ) f (γ t) v)| ≤ L * Real.sqrt (g.inner (γ t) v v))
    (hlen : metricPathELength g γ a b ≤ ENNReal.ofReal B) :
    |f (γ a) - f (γ b)| ≤ L * B := by
  have hh := Geometry.edist_comp_le_lintegral_of_metric_mfderiv_bound g hab hL hγ hf
    (fun t ht v => by
      change ‖(show ℝ from mfderiv I3 𝓘(ℝ) f (γ t) v)‖ ≤ _
      simpa only [Real.norm_eq_abs] using hbound t ht v)
  rw [← metricPathELength_eq] at hh
  have hh' := hh.trans (mul_le_mul' le_rfl hlen)
  rw [edist_dist, Real.dist_eq, ← ENNReal.ofReal_mul hL] at hh'
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hL hB)).mp hh'

private theorem scale_mfderiv_bound
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    (g : SmoothRiemannianMetric I3 M) {Q L : ℝ} (hQ : 0 < Q) {f : M → ℝ} {x : M}
    (h : ∀ v : TangentSpace I3 x,
      |(show ℝ from mfderiv I3 𝓘(ℝ) f x v)| ≤ L * Real.sqrt (g.inner x v v)) :
    ∀ v : TangentSpace I3 x,
      |(show ℝ from mfderiv I3 𝓘(ℝ) f x v)| ≤
        (L / Real.sqrt Q) * Real.sqrt ((scaleMetric Q hQ g).inner x v v) := by
  intro v
  rw [scaleMetric_inner, Real.sqrt_mul hQ.le]
  convert h v using 1
  field_simp

universe u

theorem exists_spatial_neck_slab_oscillation_constant :
    ∃ D : ℝ, 0 < D ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] (g : SmoothRiemannianMetric I3 M) (eps : ℝ) (p : M)
        (nk : SpatialNeck g eps p) (f : M → ℝ) (L : ℝ), 0 ≤ L →
        (∀ x ∈ nk.map '' (univ ×ˢ Icc (-1 : ℝ) 1), ContMDiffAt I3 𝓘(ℝ) 1 f x) →
        (∀ x ∈ nk.map '' (univ ×ˢ Icc (-1 : ℝ) 1), ∀ v : TangentSpace I3 x,
          |(show ℝ from mfderiv I3 𝓘(ℝ) f x v)| ≤ L * Real.sqrt (g.inner x v v)) →
        ∀ x ∈ nk.map '' (univ ×ˢ Icc (-1 : ℝ) 1),
          ∀ y ∈ nk.map '' (univ ×ˢ Icc (-1 : ℝ) 1),
            |f x - f y| ≤ D * L / Real.sqrt (metricScalarAt g p) := by
  obtain ⟨D, hD, htrans⟩ := exists_transverse_shortcuts_uniform_in_manifold.{u}
  refine ⟨D + 4, by linarith, ?_⟩
  intro M _ _ _ g eps p nk f L hL hf hb x hx y hy
  obtain ⟨zx, hzx, rfl⟩ := hx
  obtain ⟨zy, hzy, rfl⟩ := hy
  have hlen : (1 : ℝ) < eps⁻¹ :=
    (one_lt_inv₀ nk.eps_pos).mpr (nk.eps_small.trans (by norm_num))
  have hunit : (univ ×ˢ Icc (-1 : ℝ) 1 : Set Cylinder) ⊆
      univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ := by
    intro z hz
    exact ⟨hz.1, (neg_lt_neg hlen).trans_le hz.2.1, hz.2.2.trans_lt hlen⟩
  let gQ := scaleMetric (metricScalarAt g p) nk.Q_pos g
  let C : ℝ := L / Real.sqrt (metricScalarAt g p)
  have hC : 0 ≤ C := div_nonneg hL (Real.sqrt_nonneg _)
  have hscaled (z : M) (hz : z ∈ nk.map '' (univ ×ˢ Icc (-1 : ℝ) 1)) :=
    scale_mfderiv_bound g nk.Q_pos (hb z hz)
  obtain ⟨γ, hγ0, hγ1, hγ, hinside, hlength⟩ :=
    htrans M nk.cylinder (fun _ => nk.cylinder.metric 0) (fun _ => gQ) nk.map
      (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) {0} (⌈eps⁻¹⌉₊) eps zx.2 nk.comparison rfl
      nk.eps_pos.le (nk.eps_small.le.trans (by norm_num)) (by simp) nk.domain
      (fun u => hunit ⟨mem_univ _, hzx.2⟩) zx.1 zy.1
  have hγunit (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      γ s ∈ nk.map '' (univ ×ˢ Icc (-1 : ℝ) 1) := by
    obtain ⟨z, hz, heq⟩ := hinside s hs
    exact ⟨z, ⟨hz.1, hz.2 ▸ hzx.2⟩, heq⟩
  have hfirst : |f (nk.map zx) - f (nk.map (zy.1, zx.2))| ≤ C * D := by
    have h := abs_sub_le_of_path_bound gQ (by norm_num : (0 : ℝ) ≤ 1) hC hD.le hγ
      (fun s hs => hf _ (hγunit s hs))
      (fun s hs => hscaled _ (hγunit s ⟨hs.1.le, hs.2.le⟩)) hlength
    simpa only [hγ0, hγ1] using h
  have haxis (a b : ℝ) (hab : a ≤ b) (ha : a ∈ Icc (-1 : ℝ) 1)
      (hb' : b ∈ Icc (-1 : ℝ) 1) :
      |f (nk.map (zy.1, a)) - f (nk.map (zy.1, b))| ≤ C * (2 * (b - a)) := by
    have hsource (t : ℝ) (ht : t ∈ Icc a b) : (zy.1, t) ∈ univ ×ˢ Icc (-1 : ℝ) 1 :=
      ⟨mem_univ _, ha.1.trans ht.1, ht.2.trans hb'.2⟩
    have hcurve : ContMDiffOn 𝓘(ℝ) IC 1 (fun t : ℝ => (zy.1, t)) (Icc a b) :=
      contMDiffOn_const.prodMk contMDiffOn_id
    have hmap : ContMDiffOn 𝓘(ℝ) I3 1 (fun t : ℝ => nk.map (zy.1, t)) (Icc a b) :=
      (nk.map.contMDiffOn_toFun.of_le (by simp)).comp hcurve
        (fun t ht => nk.domain (hunit (hsource t ht)))
    have hpath := (collar_pathELength_bounds nk.cylinder (fun _ => gQ) nk.map nk.comparison
      rfl nk.eps_pos.le (nk.eps_small.le.trans (by norm_num)) (by simp) nk.domain hcurve
      (fun t ht => hunit (hsource t ht))).2
    have hl : metricPathELength gQ (fun t : ℝ => nk.map (zy.1, t)) a b ≤
        ENNReal.ofReal (2 * (b - a)) := by
      have hs : Real.sqrt (1 + eps) ≤ 2 := by
        have he : 1 + eps ≤ (2 : ℝ) ^ 2 := by linarith [nk.eps_small]
        exact (Real.sqrt_le_left (by norm_num)).mpr he
      exact hpath.trans ((mul_le_mul' (ENNReal.ofReal_le_ofReal hs)
        (nk.cylinder.axial_metricPathELength_le zy.1 a b)).trans_eq
          (ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)).symm)
    exact abs_sub_le_of_path_bound gQ hab hC (by positivity) hmap
      (fun t ht => hf _ ⟨(zy.1, t), hsource t ht, rfl⟩)
      (fun t ht => hscaled _ ⟨(zy.1, t), hsource t ⟨ht.1.le, ht.2.le⟩, rfl⟩) hl
  have hsecond : |f (nk.map (zy.1, zx.2)) - f (nk.map zy)| ≤ C * 4 := by
    rcases le_total zx.2 zy.2 with hxy | hyx
    · have hh := haxis zx.2 zy.2 hxy hzx.2 hzy.2
      exact hh.trans (mul_le_mul_of_nonneg_left (by linarith [hzx.2.1, hzy.2.2]) hC)
    · have hh := haxis zy.2 zx.2 hyx hzy.2 hzx.2
      rw [abs_sub_comm] at hh
      exact hh.trans (mul_le_mul_of_nonneg_left (by linarith [hzy.2.1, hzx.2.2]) hC)
  have ht := (abs_sub_le (f (nk.map zx)) (f (nk.map (zy.1, zx.2))) (f (nk.map zy))).trans
    (add_le_add hfirst hsecond)
  exact ht.trans_eq (by dsimp only [C]; ring)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
