import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductCurveRegularityInput
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.CurvatureLength

noncomputable section

open Manifold Set MeasureTheory
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Curvature (RealTimeInterval)

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem arcTotalCurvature_le_mul_arcLength_of_curvature_le [I.Boundaryless]
    (g : ℝ → SmoothRiemannianMetric I M) (c : CurveMap M) {J : Set ℝ}
    (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    {p q t K : ℝ} (hpq : p ≤ q) (ht : t ∈ J)
    (hK : ∀ x ∈ Icc p q, c.curvature g x t ≤ K) :
    c.arcTotalCurvature g p q t ≤ K * c.arcLength g p q t := by
  have hspd : Continuous fun x => c.speed g x t :=
    (c.speed_contDiff g J hc hi t ht).continuous
  have hcurv : Continuous fun x => c.curvature g x t :=
    Real.continuous_sqrt.comp (c.curvatureSq_contDiff g J hc hi t ht).continuous
  have hmono := intervalIntegral.integral_mono_on hpq
    ((hcurv.mul hspd).intervalIntegrable (μ := volume) p q)
    ((continuous_const.mul hspd).intervalIntegrable (μ := volume) p q)
    (fun x hx => mul_le_mul_of_nonneg_right (hK x hx) (c.speed_nonneg g x t))
  change (∫ x in p..q, c.curvature g x t * c.speed g x t) ≤
    ∫ x in p..q, K * c.speed g x t at hmono
  simpa only [arcTotalCurvature, arcLength, intervalIntegral.integral_const_mul] using hmono

variable [T2Space M] [CompactSpace M] [I.Boundaryless]
variable {D : RealTimeInterval} {a b : ℝ}

theorem exists_iteratedDs_curvature_bounds_on_Ico_of_curvature_le
    (B : RicciBackground (I := I) (M := M) D a b) {T : ℝ}
    (haT : a < T) (hTb : T ≤ b) (c : CurveMap M)
    (hc : c.IsSolutionOn B.family.metric (Ico a T)) {K : ℝ}
    (hcurv : ∀ x t, t ∈ Ico a T → c.curvature B.family.metric x t ≤ K)
    (s : ℝ) (has : a < s) :
    ∃ A : ℕ → ℝ, (∀ m, 0 < A m) ∧ ∀ m x t, t ∈ Ico s T →
      c.normSq B.family.metric
        (c.iteratedDs B.family.metric m (c.curvatureVector B.family.metric)) x t ≤ A m := by
  let L := c.length B.family.metric a
  have hL : 0 < L := c.length_pos_of_immersed B.family.metric hc.smooth hc.immersed ⟨le_rfl, haT⟩
  let K₁ := max K 0
  have hK₁ : 0 ≤ K₁ := le_max_right _ _
  have hcurv' : ∀ x t, t ∈ Ico a T → c.curvature B.family.metric x t ≤ K₁ :=
    fun x t ht => (hcurv x t ht).trans (le_max_left _ _)
  have htotal : c.totalCurvature B.family.metric a ≤ K₁ * L :=
    c.totalCurvature_le_mul_length_of_curvature_le B.family.metric hc.smooth hc.immersed
      ⟨le_rfl, haT⟩ (fun x => hcurv' x a ⟨le_rfl, haT⟩)
  let R := curveShorteningRegularityInput B L (K₁ * L) hL.le (mul_nonneg hK₁ hL.le)
  obtain ⟨ell, hell, hellbound⟩ := c.exists_length_lower_bound_of_curvature_le_Ico B haT hTb hc hcurv'
  let r := min R.radius (min ell (R.delta / (K₁ + 1)))
  have hr : 0 < r := lt_min R.radius_pos (lt_min hell (div_pos R.delta_pos (by linarith)))
  have hrr : r ≤ R.radius := min_le_left _ _
  have hrell : r ≤ ell := (min_le_right _ _).trans (min_le_left _ _)
  have hrδ : r ≤ R.delta / (K₁ + 1) := (min_le_right _ _).trans (min_le_right _ _)
  have hKr : K₁ * r ≤ R.delta := by
    have hh := (le_div_iff₀ (by linarith : 0 < K₁ + 1)).mp hrδ
    nlinarith
  let d := min (R.delta * r ^ 2) ((s - a) / 2)
  have hd : 0 < d := lt_min (mul_pos R.delta_pos (pow_pos hr 2)) (half_pos (sub_pos.mpr has))
  have hdreg : d ≤ R.delta * r ^ 2 := min_le_left _ _
  have hds : d ≤ (s - a) / 2 := min_le_right _ _
  refine ⟨fun m => R.coefficient m * d ^ (-((m : ℤ) + 1)),
    fun m => mul_pos (R.coefficient_pos m) (zpow_pos hd _), ?_⟩
  intro m x t ht
  have htJ : t ∈ Ico a T := ⟨has.le.trans ht.1, ht.2⟩
  have hstart : t - d ∈ Ico a T := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have harc : ∀ p q : ℝ, p ≤ q → q ≤ p + 1 →
      c.arcLength B.family.metric p q (t - d) = r →
      c.arcTotalCurvature B.family.metric p q (t - d) ≤ R.delta := by
    intro p q hpq _ hlen
    have hb := c.arcTotalCurvature_le_mul_arcLength_of_curvature_le B.family.metric hc.smooth hc.immersed
      hpq hstart (fun x _ => hcurv' x (t - d) hstart)
    rw [hlen] at hb
    exact hb.trans hKr
  have hh := R.curve T haT hTb (Ico a T) (Or.inl rfl) c hc le_rfl htotal
    (t - d) hstart r hr hrr (hrell.trans (hellbound (t - d) hstart)) harc m x t htJ
    (by linarith) (by linarith)
  simpa only [sub_sub_cancel] using hh

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap
