import DifferentialGeometry.Geometry.Comparison.Toponogov.RadialDistance
import DifferentialGeometry.Geometry.Comparison.Toponogov.AngleKernelCompactness

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology

namespace DifferentialGeometry.Toponogov

variable {X : Type*} [MetricSpace X] {ι : Type*} {z : X}
  {L : ι → ℝ} {gamma : ι → ℝ → X}

theorem exists_finset_radial_net
    (hrad : IsRadialFamily z L gamma) (hL : ∀ i, 0 < L i)
    (K : AngleKernel ι) (hK : ∀ i j, K.angle i j = limitingRadialAngle L gamma i j)
    (htb : let _ := K.metricSpace; TotallyBounded (univ : Set (Quotient K.setoid)))
    {eps : ℝ} (heps : 0 < eps) :
    ∃ A : Finset ι, ∃ d > 0, (∀ a ∈ A, d ≤ L a) ∧
      ∀ s ∈ Ioc 0 d, ∀ i, s ≤ L i → ∃ a ∈ A,
        dist (gamma i s) (gamma a s) < eps * s := by
  obtain ⟨A, hA⟩ := (K.totallyBounded_iff_finset_angle_net.mp htb) eps heps
  have hsmall : ∀ᶠ d in 𝓝[>] (0 : ℝ), ∀ a ∈ A, d ≤ L a :=
    (eventually_all_finset A).mpr (fun a _ => by
      filter_upwards [Ioc_mem_nhdsGT (hL a)] with d hd
      exact hd.2)
  have hpositive : ∀ᶠ d in 𝓝[>] (0 : ℝ), 0 < d := self_mem_nhdsWithin
  obtain ⟨d, hd, hda⟩ := (hpositive.and hsmall).exists
  refine ⟨A, d, hd, hda, fun s hs i hsi => ?_⟩
  obtain ⟨a, ha, hangle⟩ := hA i
  refine ⟨a, ha, ?_⟩
  rw [dist_comm]
  have hh := dist_le_mul_limitingRadialAngle hrad
    (show s ∈ Ioc 0 (L a) from ⟨hs.1, hs.2.trans (hda a ha)⟩) ⟨hs.1, hsi⟩
  rw [← hK] at hh
  exact hh.trans_lt (by simpa only [mul_comm eps s] using mul_lt_mul_of_pos_left hangle hs.1)

theorem exists_finset_radial_annulus_net
    (hrad : IsRadialFamily z L gamma) (hL : ∀ i, 0 < L i)
    (hmin : ∀ i, ∀ s ∈ Ioc 0 (L i), ∀ t ∈ Ioc 0 (L i), dist (gamma i s) (gamma i t) = |s - t|)
    (K : AngleKernel ι) (hK : ∀ i j, K.angle i j = limitingRadialAngle L gamma i j)
    (htb : let _ := K.metricSpace; TotallyBounded (univ : Set (Quotient K.setoid)))
    {a b eps : ℝ} (ha : 0 < a) (hab : a ≤ b) (heps : 0 < eps) :
    ∃ S : Finset (ι × ℝ), (∀ p ∈ S, p.2 ∈ Icc a b) ∧
      ∃ d > 0, (∀ p ∈ S, d * p.2 ≤ L p.1) ∧
        ∀ rho ∈ Ioc 0 d, ∀ i, ∀ r ∈ Icc a b, rho * r ≤ L i →
          ∃ p ∈ S, dist (gamma i (rho * r)) (gamma p.1 (rho * p.2)) / rho < eps := by
  classical
  have hb : 0 < b := ha.trans_le hab
  obtain ⟨A, d0, hd0, hAd, hA⟩ := exists_finset_radial_net hrad hL K hK htb
    (show 0 < eps / (2 * b) by positivity)
  obtain ⟨T, hTab, hTfin, hTcover⟩ := (isCompact_Icc : IsCompact (Icc a b)).finite_cover_balls
    (show 0 < eps / 2 by positivity)
  let d := d0 / b
  have hd : 0 < d := div_pos hd0 hb
  have hscale {rho r : ℝ} (hrho : rho ∈ Ioc 0 d) (hr : r ∈ Icc a b) :
      rho * r ∈ Ioc 0 d0 := by
    refine ⟨mul_pos hrho.1 (ha.trans_le hr.1), ?_⟩
    calc
      rho * r ≤ rho * b := mul_le_mul_of_nonneg_left hr.2 hrho.1.le
      _ ≤ d * b := mul_le_mul_of_nonneg_right hrho.2 hb.le
      _ = d0 := div_mul_cancel₀ _ hb.ne'
  refine ⟨A ×ˢ hTfin.toFinset, ?_, d, hd, ?_, ?_⟩
  · intro p hp
    exact hTab (hTfin.mem_toFinset.mp (Finset.mem_product.mp hp).2)
  · intro p hp
    obtain ⟨hi, ht⟩ := Finset.mem_product.mp hp
    have ht' := hTab (hTfin.mem_toFinset.mp ht)
    exact (hscale ⟨hd, le_rfl⟩ ht').2.trans (hAd p.1 hi)
  · intro rho hrho i r hr hri
    obtain ⟨j, hj, hnear⟩ := hA (rho * r) (hscale hrho hr) i hri
    obtain ⟨t, ht⟩ := mem_iUnion.mp (hTcover hr)
    obtain ⟨htT, hrt⟩ := mem_iUnion.mp ht
    have ht' := hTab htT
    have hrt' : |r - t| < eps / 2 := by simpa only [Metric.mem_ball, Real.dist_eq] using hrt
    have hrd := hscale hrho hr
    have htd := hscale hrho ht'
    have hsegment : dist (gamma j (rho * r)) (gamma j (rho * t)) = rho * |r - t| := by
      rw [hmin j _ ⟨hrd.1, hrd.2.trans (hAd j hj)⟩ _ ⟨htd.1, htd.2.trans (hAd j hj)⟩,
        ← mul_sub, abs_mul, abs_of_pos hrho.1]
    refine ⟨(j, t), Finset.mem_product.mpr ⟨hj, hTfin.mem_toFinset.mpr htT⟩, ?_⟩
    apply (div_lt_iff₀ hrho.1).mpr
    have htri := dist_triangle (gamma i (rho * r)) (gamma j (rho * r)) (gamma j (rho * t))
    rw [hsegment] at htri
    have hang : eps / (2 * b) * (rho * r) ≤ eps * rho / 2 := by
      have hh := mul_le_mul_of_nonneg_left hr.2 (show 0 ≤ eps / (2 * b) * rho from mul_nonneg (div_nonneg heps.le (by positivity)) hrho.1.le)
      have heq : eps / (2 * b) * rho * b = eps * rho / 2 := by field_simp
      rw [heq] at hh
      simpa only [mul_assoc] using hh
    have hradial := mul_lt_mul_of_pos_left hrt' hrho.1
    dsimp only
    nlinarith only [htri, hnear, hang, hradial]

end DifferentialGeometry.Toponogov
