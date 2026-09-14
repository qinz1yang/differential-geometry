import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Bernstein
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LocalRegularity
import DifferentialGeometry.Geometry.Metric.Coordinates.InnerExpansion
import DifferentialGeometry.Analysis.Calculus.Displacement

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem curvatureSq_sub_le_arcLength (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    {p q x y t Λ N : ℝ} (ht : t ∈ J) (hx : x ∈ Icc p q) (hy : y ∈ Icc p q)
    (hcurv : ∀ z ∈ Icc p q, c.curvatureSq g z t ≤ Λ)
    (hderiv : ∀ z ∈ Icc p q, c.normSq g (c.Ds g (c.curvatureVector g)) z t ≤ N) :
    |c.curvatureSq g x t - c.curvatureSq g y t| ≤
      2 * Real.sqrt Λ * Real.sqrt N * c.arcLength g p q t := by
  have hdf (z : ℝ) (hz : z ∈ Icc p q) :
      |c.ds g (c.curvatureSq g) z t| ≤ 2 * Real.sqrt Λ * Real.sqrt N := by
    rw [c.ds_curvatureSq_eq g J hc hi z t ht, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hh := DifferentialGeometry.Geometry.Riemannian.abs_inner_le_sqrt_mul_sqrt
      (g t) (c.lift z t) (c.Ds g (c.curvatureVector g) z t) (c.curvatureVector g z t)
    have hb := mul_le_mul (Real.sqrt_le_sqrt (hderiv z hz)) (Real.sqrt_le_sqrt (hcurv z hz))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg N)
    have he := mul_le_mul_of_nonneg_left (hh.trans hb) (by norm_num : (0 : ℝ) ≤ 2)
    linarith only [he]
  have hf := c.curvatureSq_contDiff g J hc hi t ht
  have hfd : ContDiff ℝ ∞ (fun z => deriv (fun w => c.curvatureSq g w t) z) := by
    simpa using hf.iterate_deriv 1
  have hsp := (c.speed_contDiff g J hc hi t ht).continuous
  have hbound (z : ℝ) (hz : z ∈ Icc p q) :
      |deriv (fun w => c.curvatureSq g w t) z| ≤
        2 * Real.sqrt Λ * Real.sqrt N * c.speed g z t := by
    have hv := c.speed_pos g hi z t ht
    have he : deriv (fun w => c.curvatureSq g w t) z = c.speed g z t * c.ds g (c.curvatureSq g) z t := by
      dsimp only [CurveMap.ds]
      field_simp
    rw [he, abs_mul, abs_of_pos hv]
    have hh := mul_le_mul_of_nonneg_left (hdf z hz) hv.le
    linarith only [hh]
  have hh := DifferentialGeometry.Analysis.norm_sub_le_integral_norm_deriv_of_mem_Icc
    hf.continuous.continuousOn (hf.differentiable (by simp)).differentiableOn
    (hfd.continuous.norm.intervalIntegrable (μ := volume) p q) hx hy
  have hm := intervalIntegral.integral_mono_on (hx.1.trans hx.2)
    (hfd.continuous.norm.intervalIntegrable (μ := volume) p q)
    ((show Continuous (fun z => 2 * Real.sqrt Λ * Real.sqrt N * c.speed g z t) from
      continuous_const.mul hsp).intervalIntegrable (μ := volume) p q)
    (fun z hz => by simpa only [Real.norm_eq_abs] using hbound z hz)
  rw [intervalIntegral.integral_const_mul] at hm
  simpa only [Real.norm_eq_abs, CurveMap.arcLength] using hh.trans hm

theorem exists_arcTotalCurvature_ge_of_curvatureSq_bounds
    (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    {p q t Λ N ell κ : ℝ} (ht : t ∈ J) (hpq : p ≤ q) (hell : 0 ≤ ell) (hκ : 0 ≤ κ)
    (hlen : ell ≤ c.arcLength g p q t)
    (hcurv : ∀ z ∈ Icc p q, c.curvatureSq g z t ≤ Λ)
    (hderiv : ∀ z ∈ Icc p q, c.normSq g (c.Ds g (c.curvatureVector g)) z t ≤ N)
    (hpeak : κ ^ 2 + 2 * Real.sqrt Λ * Real.sqrt N * ell ≤ c.curvatureSq g p t) :
    ∃ v ∈ Icc p q, c.arcLength g p v t = ell ∧ κ * ell ≤ c.arcTotalCurvature g p v t := by
  have hsp := (c.speed_contDiff g J hc hi t ht).continuous
  have himage : ell ∈ (fun v => c.arcLength g p v t) '' Icc p q := by
    apply intermediate_value_Icc hpq (intervalIntegral.differentiable_integral_of_continuous hsp).continuous.continuousOn
    exact ⟨by simpa only [CurveMap.arcLength, intervalIntegral.integral_same] using hell, hlen⟩
  obtain ⟨v, hv, heq⟩ := himage
  change c.arcLength g p v t = ell at heq
  refine ⟨v, hv, heq, ?_⟩
  have hsub : Icc p v ⊆ Icc p q := Icc_subset_Icc le_rfl hv.2
  have hk (z : ℝ) (hz : z ∈ Icc p v) : κ ≤ c.curvature g z t := by
    have hh := c.curvatureSq_sub_le_arcLength g hc hi ht hz ⟨le_rfl, hv.1⟩
      (fun w hw => hcurv w (hsub hw)) (fun w hw => hderiv w (hsub hw))
    rw [heq] at hh
    have hlow : κ ^ 2 ≤ c.curvatureSq g z t := by
      linarith only [(abs_le.mp hh).1, hpeak]
    exact (Real.sqrt_sq hκ).symm.le.trans (Real.sqrt_le_sqrt hlow)
  have hccont : Continuous (fun z => c.curvature g z t) :=
    (c.curvatureSq_contDiff g J hc hi t ht).continuous.sqrt
  have hm := intervalIntegral.integral_mono_on hv.1
    ((show Continuous (fun z => κ * c.speed g z t) from continuous_const.mul hsp).intervalIntegrable (μ := volume) p v)
    ((show Continuous (fun z => c.curvature g z t * c.speed g z t) from hccont.mul hsp).intervalIntegrable (μ := volume) p v)
    (fun z hz => mul_le_mul_of_nonneg_right (hk z hz) (c.speed_nonneg g z t))
  rw [intervalIntegral.integral_const_mul] at hm
  change κ * c.arcLength g p v t ≤ c.arcTotalCurvature g p v t at hm
  rwa [heq] at hm

theorem exists_arcTotalCurvature_ge_of_curvatureSq_peak
    (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    {p q t Λ β : ℝ} (ht : t ∈ J) (hpq : p ≤ q) (hΛ : 0 < Λ) (hβ : 0 < β)
    (hlen : 1 / (32 * Real.sqrt β * Real.sqrt Λ) ≤ c.arcLength g p q t)
    (hcurv : ∀ z ∈ Icc p q, c.curvatureSq g z t ≤ Λ)
    (hderiv : ∀ z ∈ Icc p q, c.normSq g (c.Ds g (c.curvatureVector g)) z t ≤ 4 * β * Λ ^ 2)
    (hpeak : Λ / 2 ≤ c.curvatureSq g p t) :
    ∃ v ∈ Icc p q, c.arcLength g p v t = 1 / (32 * Real.sqrt β * Real.sqrt Λ) ∧
      1 / (64 * Real.sqrt β) ≤ c.arcTotalCurvature g p v t := by
  have hsΛ : 0 < Real.sqrt Λ := Real.sqrt_pos.mpr hΛ
  have hsβ : 0 < Real.sqrt β := Real.sqrt_pos.mpr hβ
  have hsN : Real.sqrt (4 * β * Λ ^ 2) = 2 * Real.sqrt β * Λ := by
    rw [Real.sqrt_mul (by positivity : 0 ≤ 4 * β), Real.sqrt_sq hΛ.le,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hdrop : (Real.sqrt Λ / 2) ^ 2 + 2 * Real.sqrt Λ * Real.sqrt (4 * β * Λ ^ 2) *
      (1 / (32 * Real.sqrt β * Real.sqrt Λ)) = 3 * Λ / 8 := by
    rw [div_pow, Real.sq_sqrt hΛ.le, hsN]
    field_simp
    ring
  have hmass : (Real.sqrt Λ / 2) * (1 / (32 * Real.sqrt β * Real.sqrt Λ)) = 1 / (64 * Real.sqrt β) := by
    field_simp
    norm_num
  obtain ⟨v, hv, heq, htc⟩ := c.exists_arcTotalCurvature_ge_of_curvatureSq_bounds g hc hi ht hpq
    (by positivity) (by positivity) hlen hcurv hderiv (κ := Real.sqrt Λ / 2) (by
      rw [hdrop]
      linarith only [hpeak, hΛ])
  exact ⟨v, hv, heq, by rwa [hmass] at htc⟩

variable [CompleteSpace E] [T2Space M] [SigmaCompactSpace M]
    {D : RealTimeInterval} {a b s u : ℝ}

theorem exists_arcTotalCurvature_ge_of_curvatureSq_le_div
    (B : RicciBackground (I := I) (M := M) D a b) (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    (C K : ℝ) (hC : B.C ≤ C) (hK : 1 ≤ K) (hlen : u - s ≤ 1)
    (hk : ∀ x t, t ∈ Ioc s u → c.curvatureSq B.family.metric x t ≤ K / (t - s))
    (hDR : ∀ x t, t ∈ Icc s u → normSq0S (B.family.metric t) (c.lift x t) 5
      (totalNabla0SFun 4 (B.family.connection t) (B.family.rm04 t) (c.lift x t)) ≤ C ^ 2)
    (hDDRic : ∀ x t, t ∈ Icc s u → normSq0S (B.family.metric t) (c.lift x t) 4
      (totalNabla0SFun 3 (B.family.connection t)
        (covStep (B.family.metric t) 2 (B.family.ricci t)) (c.lift x t)) ≤ C ^ 2)
    {p q : ℝ} (hpq : p ≤ q)
    (harc : 1 / (64 * (1 + 64 * (1 + C)) * Real.sqrt (K / (u - s))) ≤ c.arcLength B.family.metric p q u)
    (hpeak : K / (2 * (u - s)) ≤ c.curvatureSq B.family.metric p u) :
    ∃ v ∈ Icc p q,
      c.arcLength B.family.metric p v u = 1 / (64 * (1 + 64 * (1 + C)) * Real.sqrt (K / (u - s))) ∧
      1 / (128 * (1 + 64 * (1 + C))) ≤ c.arcTotalCurvature B.family.metric p v u := by
  let b := 1 + 64 * (1 + C)
  let Λ := K / (u - s)
  let β := 4 * b ^ 2
  have hC0 : 0 ≤ C := by
    dsimp only [RicciBackground.C] at hC
    linarith [B.B₀_nonneg, B.B₁_nonneg, B.B₂_nonneg]
  have hb : 0 < b := by dsimp only [b]; positivity
  have hΛ : 0 < Λ := div_pos (lt_of_lt_of_le zero_lt_one hK) (sub_pos.mpr hsu)
  have hβ : 0 < β := by dsimp only [β]; positivity
  have hsβ : Real.sqrt β = 2 * b := by
    dsimp only [β]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), Real.sqrt_sq hb.le]
    norm_num
  have hlength : 1 / (32 * Real.sqrt β * Real.sqrt Λ) ≤ c.arcLength B.family.metric p q u := by
    rw [hsβ]
    convert harc using 1
    ring
  have hD := c.curvatureDerivative_bernstein_bound_of_curvatureSq_le_div B hsu hwindow hc C K hC hK hlen hk hDR hDDRic
  have hDbound (z : ℝ) : c.normSq B.family.metric (c.Ds B.family.metric (c.curvatureVector B.family.metric)) z u ≤
      4 * β * Λ ^ 2 := by
    refine (hD z).trans_eq ?_
    dsimp only [β, b, Λ]
    ring
  have hpeak' : Λ / 2 ≤ c.curvatureSq B.family.metric p u := by
    change K / (u - s) / 2 ≤ c.curvatureSq B.family.metric p u
    rwa [div_div, mul_comm (u - s) 2]
  obtain ⟨v, hv, heq, htc⟩ := c.exists_arcTotalCurvature_ge_of_curvatureSq_peak B.family.metric
    hc.smooth hc.immersed ⟨hsu.le, le_rfl⟩ hpq hΛ hβ hlength
    (fun z _ => hk z u ⟨hsu, le_rfl⟩) (fun z _ => hDbound z) hpeak'
  refine ⟨v, hv, ?_, ?_⟩
  · rw [heq, hsβ]
    dsimp only [b, Λ]
    congr 1
    ring
  · rw [hsβ] at htc
    convert htc using 1
    dsimp only [b]
    ring

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap
