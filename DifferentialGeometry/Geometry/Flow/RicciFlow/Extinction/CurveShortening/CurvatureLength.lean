import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Evolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ContinuationFrontier

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace CurveMap

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem length_pos_of_immersed [I.Boundaryless]
    (g : ℝ → SmoothRiemannianMetric I M) (c : CurveMap M) {J : Set ℝ}
    (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J) {t : ℝ} (ht : t ∈ J) :
    0 < c.length g t := by
  have hspd : Continuous fun x => c.speed g x t := (c.speed_contDiff g J hc hi t ht).continuous
  have h := intervalIntegral.intervalIntegral_pos_of_pos (hspd.intervalIntegrable 0 1)
    (fun x => c.speed_pos g hi x t ht) (by norm_num : (0 : ℝ) < 1)
  simpa only [CurveMap.length, CurveMap.integral, one_mul] using h

omit [CompleteSpace E] in
theorem totalCurvature_le_mul_length_of_curvature_le [I.Boundaryless]
    (g : ℝ → SmoothRiemannianMetric I M) (c : CurveMap M) {J : Set ℝ}
    (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    {t : ℝ} (ht : t ∈ J) {K : ℝ}
    (hK : ∀ x, c.curvature g x t ≤ K) :
    c.totalCurvature g t ≤ K * c.length g t := by
  have hspd : Continuous fun x => c.speed g x t := (c.speed_contDiff g J hc hi t ht).continuous
  have hcur : Continuous fun x => c.curvatureSq g x t :=
    (c.curvatureSq_contDiff g J hc hi t ht).continuous
  have hcurv : Continuous fun x => c.curvature g x t := Real.continuous_sqrt.comp hcur
  have hint₁ : IntervalIntegrable (fun x => c.curvature g x t * c.speed g x t) volume 0 1 :=
    (hcurv.mul hspd).intervalIntegrable 0 1
  have hint₂ : IntervalIntegrable (fun x => K * c.speed g x t) volume 0 1 :=
    (continuous_const.mul hspd).intervalIntegrable 0 1
  have hmono := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hint₁ hint₂
    (fun x _ => mul_le_mul_of_nonneg_right (hK x) (c.speed_nonneg g x t))
  have hconst : (∫ x in (0 : ℝ)..1, K * c.speed g x t) = K * ∫ x in (0 : ℝ)..1, c.speed g x t :=
    intervalIntegral.integral_const_mul K _
  calc c.totalCurvature g t
      = ∫ x in (0 : ℝ)..1, c.curvature g x t * c.speed g x t := rfl
    _ ≤ ∫ x in (0 : ℝ)..1, K * c.speed g x t := hmono
    _ = K * c.length g t := by
        rw [hconst]
        simp only [CurveMap.length, CurveMap.integral, one_mul]

omit [CompleteSpace E] in
theorem two_pi_le_mul_length_of_curvature_le_of_totalCurvature_ge [I.Boundaryless]
    (g : ℝ → SmoothRiemannianMetric I M) (c : CurveMap M) {J : Set ℝ}
    (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    {t : ℝ} (ht : t ∈ J) {K : ℝ}
    (hK : ∀ x, c.curvature g x t ≤ K)
    (h2π : 2 * Real.pi ≤ c.totalCurvature g t) :
    2 * Real.pi ≤ K * c.length g t :=
  h2π.trans (c.totalCurvature_le_mul_length_of_curvature_le g hc hi ht hK)

end CurveMap

variable [SigmaCompactSpace M] [t2M : T2Space M] [compactM : CompactSpace M]
  [nonemptyM : Nonempty M] [hBoundary : I.Boundaryless]
include t2M compactM nonemptyM hBoundary
variable {D : RealTimeInterval} {a b : ℝ}

namespace CurveMap

omit compactM nonemptyM in
theorem length_lower_bound_of_curvature_le
    (B : RicciBackground (I := I) (M := M) D a b) {s u : ℝ} (hsu : s < u)
    (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    {K : ℝ} (hcurv : ∀ x t, t ∈ Icc s u → c.curvature B.family.metric x t ≤ K)
    {t : ℝ} (ht : t ∈ Icc s u) :
    c.length B.family.metric s * Real.exp (-(K ^ 2 + B.B₀) * (t - s)) ≤
      c.length B.family.metric t := by
  have hs : s ∈ Icc s u := ⟨le_rfl, hsu.le⟩
  have hspd_s : Continuous fun x => c.speed B.family.metric x s :=
    (c.speed_contDiff B.family.metric (Icc s u) hc.smooth hc.immersed s hs).continuous
  have hspd_t : Continuous fun x => c.speed B.family.metric x t :=
    (c.speed_contDiff B.family.metric (Icc s u) hc.smooth hc.immersed t ht).continuous
  have hint₁ : IntervalIntegrable
      (fun x => c.speed B.family.metric x s * Real.exp (-(K ^ 2 + B.B₀) * (t - s)))
      volume 0 1 :=
    (hspd_s.mul continuous_const).intervalIntegrable 0 1
  have hint₂ : IntervalIntegrable (fun x => c.speed B.family.metric x t) volume 0 1 :=
    hspd_t.intervalIntegrable 0 1
  have hmono := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hint₁ hint₂
    (fun x _ => (speed_exponential_bounds B hsu hwindow c hc K hcurv x t ht).1)
  have hconst : (∫ x in (0 : ℝ)..1,
        c.speed B.family.metric x s * Real.exp (-(K ^ 2 + B.B₀) * (t - s))) =
      (∫ x in (0 : ℝ)..1, c.speed B.family.metric x s) *
        Real.exp (-(K ^ 2 + B.B₀) * (t - s)) :=
    intervalIntegral.integral_mul_const _ _
  calc c.length B.family.metric s * Real.exp (-(K ^ 2 + B.B₀) * (t - s))
      = (∫ x in (0 : ℝ)..1, c.speed B.family.metric x s) *
          Real.exp (-(K ^ 2 + B.B₀) * (t - s)) := by
        simp only [CurveMap.length, CurveMap.integral, one_mul]
    _ = ∫ x in (0 : ℝ)..1,
          c.speed B.family.metric x s * Real.exp (-(K ^ 2 + B.B₀) * (t - s)) := hconst.symm
    _ ≤ ∫ x in (0 : ℝ)..1, c.speed B.family.metric x t := hmono
    _ = c.length B.family.metric t := by
        simp only [CurveMap.length, CurveMap.integral, one_mul]

end CurveMap

namespace CurveMap

omit compactM nonemptyM in
theorem length_lower_bound_of_curvature_le_Ico
    (B : RicciBackground (I := I) (M := M) D a b) {T : ℝ} (haT : a < T) (hTb : T ≤ b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Ico a T))
    {K : ℝ} (hcurv : ∀ x t, t ∈ Ico a T → c.curvature B.family.metric x t ≤ K) :
    ∀ t ∈ Ico a T,
      c.length B.family.metric a * Real.exp (-(K ^ 2 + B.B₀) * (b - a)) ≤
        c.length B.family.metric t := by
  intro t ht
  have hpos : 0 ≤ c.length B.family.metric a :=
    intervalIntegral.integral_nonneg (by norm_num : (0 : ℝ) ≤ 1)
      (fun x _ => mul_nonneg zero_le_one (c.speed_nonneg B.family.metric x a))
  have hsub : Icc a t ⊆ Ico a T := fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
  rcases lt_or_eq_of_le ht.1 with hat | heq
  · have hc' : c.IsSolutionOn B.family.metric (Icc a t) :=
      hc.mono hsub (fun s hs => ((uniqueDiffOn_Icc hat) s hs).uniqueMDiffWithinAt)
    have hbase := length_lower_bound_of_curvature_le B hat
      (Set.Icc_subset_Icc le_rfl (ht.2.le.trans hTb)) c hc'
      (fun x s hs => hcurv x s (hsub hs)) ⟨ht.1, le_rfl⟩
    have hfac : Real.exp (-(K ^ 2 + B.B₀) * (b - a)) ≤
        Real.exp (-(K ^ 2 + B.B₀) * (t - a)) := by
      rw [Real.exp_le_exp]
      nlinarith [sq_nonneg K, B.B₀_nonneg, ht.2.le]
    exact (mul_le_mul_of_nonneg_left hfac hpos).trans hbase
  · rw [← heq]
    have hfac : Real.exp (-(K ^ 2 + B.B₀) * (b - a)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [sq_nonneg K, B.B₀_nonneg, B.lt]
    calc c.length B.family.metric a * Real.exp (-(K ^ 2 + B.B₀) * (b - a))
        ≤ c.length B.family.metric a * 1 := mul_le_mul_of_nonneg_left hfac hpos
      _ = c.length B.family.metric a := mul_one _

omit compactM nonemptyM in
theorem exists_length_lower_bound_of_curvature_le_Ico
    (B : RicciBackground (I := I) (M := M) D a b) {T : ℝ} (haT : a < T) (hTb : T ≤ b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Ico a T))
    {K : ℝ} (hcurv : ∀ x t, t ∈ Ico a T → c.curvature B.family.metric x t ≤ K) :
    ∃ r : ℝ, 0 < r ∧ ∀ t ∈ Ico a T, r ≤ c.length B.family.metric t := by
  refine ⟨c.length B.family.metric a * Real.exp (-(K ^ 2 + B.B₀) * (b - a)), ?_, ?_⟩
  · exact mul_pos (c.length_pos_of_immersed B.family.metric hc.smooth hc.immersed
      ⟨le_rfl, haT⟩) (Real.exp_pos _)
  · intro t ht
    exact c.length_lower_bound_of_curvature_le_Ico B haT hTb hc hcurv t ht

end CurveMap

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
