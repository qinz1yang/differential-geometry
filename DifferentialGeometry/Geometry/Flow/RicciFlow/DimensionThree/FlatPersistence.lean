import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.RicciFlat
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Compact
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Stationary
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Nullity
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.CurvatureRank

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Set DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] [I.Boundaryless] in
private theorem mem_curvatureOperatorImageAnnihilatorAt_of_finrank_eq_zero
    (g : SmoothRiemannianMetric I M) (x : M)
    (hz : Module.finrank ℝ (curvatureOperatorImageAt g x
      ⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩) = 0)
    (v : TangentSpace I x) : v ∈ curvatureOperatorImageAnnihilatorAt g x
      ⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩ := by
  let _ : FiniteDimensional ℝ (TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) :=
    (ContinuousAlternatingMap.elementaryCovectorBasis (k := 2)
      (Module.finBasis ℝ (TangentSpace I x))).finiteDimensional_of_finite
  have hbot := Submodule.finrank_eq_zero.mp hz
  apply ContinuousAlternatingMap.mem_contractionAnnihilator_iff.mpr
  intro beta hbeta
  rw [hbot] at hbeta
  simp only [Submodule.mem_bot] at hbeta
  simp [hbeta]

theorem stationary_flat_of_curvatureOperatorImageAt_finrank_eq_zero_of_complete_forward_uniqueness
    [ConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3)
    {a b s : ℝ} (hs : s ∈ Ioo a b) (hreg : Ioo a b ⊆ D.regular)
    (hR : ∀ t ∈ Ioo a b, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
        algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hcomplete : ∀ t ∈ Ioo a b, RiemannianMetricComplete (S.family.metric t))
    (hbound : ∀ u v, a < u → u < v → v < b →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc u v, ∀ x : M,
        normSq0S (I := I) (S.family.metric t) x 4
          (metricRm04At (S.family.metric t) x) ≤ C)
    (hunique : ∀ u v, a < u → (huv : u < v) → v < b →
      ∀ S₁ S₂ : CompleteBoundedCurvatureSolutionOn (I := I) (M := M)
        (D := RealTimeInterval.closedOpen u v huv),
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ico u v, ∀ x : M,
        normSq0S (I := I) (S₁.solution.base.metric t) x 4
          (metricRm04At (S₁.solution.base.metric t) x) ≤ C) →
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ico u v, ∀ x : M,
        normSq0S (I := I) (S₂.solution.base.metric t) x 4
          (metricRm04At (S₂.solution.base.metric t) x) ≤ C) →
      S₁.solution.base.metric u = S₂.solution.base.metric u →
      ∀ t ∈ Ico u v, S₁.solution.base.metric t = S₂.solution.base.metric t)
    (x₀ : M)
    (hzero : Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric s) x₀
      ⟨metricRm04At (S.family.metric s) x₀,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric s) x₀⟩) = 0) :
    ∀ t ∈ Ioo a b, S.family.metric t = S.family.metric s ∧
      ∀ (x : M) (u v w : TangentSpace I x),
        riemannOp (LeviCivita (S.family.metric t))
          x u v w = 0 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hzeroPast (t : ℝ) (ht : t ∈ Ioo a b) (hts : t ≤ s) (x : M) :
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) = 0 := by
    rcases hts.eq_or_lt with rfl | hts
    · obtain ⟨r, har, hrs⟩ := exists_between hs.1
      have hsub : Icc r t ⊆ Ioo a b := fun q hq =>
        ⟨har.trans_le hq.1, hq.2.trans_lt hs.2⟩
      exact (curvatureOperatorImageAt_finrank_eq_at_later_time S hS hdim hrs
        (hsub.trans hreg) (fun q hq => hR q (hsub hq)) x x₀).trans hzero
    · have hsub : Icc t s ⊆ Ioo a b := fun q hq =>
        ⟨ht.1.trans_le hq.1, hq.2.trans_lt hs.2⟩
      have hle := curvatureOperatorImageAt_finrank_le_at_later_time S hS hdim hts
        (hsub.trans hreg) (fun q hq => hR q (hsub hq)) x x₀
      omega
  have hforward (u v : ℝ) (hu : u ∈ Ioo a b) (hv : v ∈ Ioo a b) (huv : u ≤ v)
      (hRicci : ∀ (x : M) (w z : TangentSpace I x),
        ricciTensor (S.family.metric u) x w z = 0) :
      S.family.metric v = S.family.metric u := by
    obtain ⟨w, hvw, hwb⟩ := exists_between hv.2
    have huw : u < w := huv.trans_lt hvw
    have hsub : Ico u w ⊆ Ioo a b := fun q hq =>
      ⟨hu.1.trans_le hq.1, hq.2.trans hwb⟩
    let S' : CompleteBoundedCurvatureSolutionOn (I := I) (M := M)
        (D := RealTimeInterval.closedOpen u w huw) := {
      solution := S.timeRestrict (RealTimeInterval.closedOpen u w huw)
      isSolution := isSoln_timeRestrict hS
        (fun q hq => D.regular_subset (hreg (hsub hq)))
        (fun q hq => hreg (hsub ⟨hq.1.le, hq.2⟩))
      complete := fun q hq => hcomplete q (hsub hq)
      curvatureBound := by
        intro q hq
        obtain ⟨C, hC, hb⟩ := hbound u w hu.1 huw hwb
        exact ⟨C, hC, hb q ⟨hq.1, hq.2.le⟩⟩ }
    have hbound' : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ico u w, ∀ x : M,
        normSq0S (I := I) (S'.solution.base.metric t) x 4
          (metricRm04At (S'.solution.base.metric t) x) ≤ C := by
      obtain ⟨C, hC, hb⟩ := hbound u w hu.1 huw hwb
      exact ⟨C, hC, fun q hq => hb q ⟨hq.1, hq.2.le⟩⟩
    exact metric_eq_initial_of_ricci_flat_of_complete_forward_uniqueness huw S'
      hbound' (hunique u w hu.1 huw hwb) hRicci v ⟨huv, hvw⟩
  intro t ht
  have hmetric : S.family.metric t = S.family.metric s := by
    rcases le_total s t with hst | hts
    · exact hforward s t hs ht hst fun x w z =>
        ricciTensor_eq_zero_of_mem_curvatureOperatorImageAnnihilatorAt (S.family.metric s) x
          (mem_curvatureOperatorImageAnnihilatorAt_of_finrank_eq_zero
            (S.family.metric s) x (hzeroPast s hs le_rfl x) w) z
    · exact (hforward t s ht hs hts fun x w z =>
        ricciTensor_eq_zero_of_mem_curvatureOperatorImageAnnihilatorAt (S.family.metric t) x
          (mem_curvatureOperatorImageAnnihilatorAt_of_finrank_eq_zero
            (S.family.metric t) x (hzeroPast t ht hts x) w) z).symm
  refine ⟨hmetric, ?_⟩
  intro x u v w
  rw [hmetric]
  exact riemannOp_eq_zero_of_mem_curvatureOperatorImageAnnihilatorAt (S.family.metric s) x
    (mem_curvatureOperatorImageAnnihilatorAt_of_finrank_eq_zero
      (S.family.metric s) x (hzeroPast s hs le_rfl x) w) u v


omit [SigmaCompactSpace M] in
theorem metric_eq_on_of_curvatureOperatorImageAt_finrank_eq_zero
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hreg : Set.Ioo a b ⊆ D.regular)
    (hzero : ∀ t ∈ Set.Ioo a b, ∀ x, Module.finrank ℝ (curvatureOperatorImageAt
      (S.family.metric t) x ⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) = 0)
    {s t : ℝ} (hs : s ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b) :
    S.family.metric s = S.family.metric t := by
  apply SmoothRiemannianMetric.ext_inner
  intro x u v
  have hderiv (r : ℝ) (hr : r ∈ Set.Ioo a b) :
      HasDerivAt (fun z => (S.family.metric z).inner x u v) 0 r := by
    let _ : FiniteDimensional ℝ (TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) :=
      (ContinuousAlternatingMap.elementaryCovectorBasis (k := 2)
        (Module.finBasis ℝ (TangentSpace I x))).finiteDimensional_of_finite
    have hnull : u ∈ curvatureOperatorImageAnnihilatorAt (S.family.metric r) x
        ⟨metricRm04At (S.family.metric r) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩ := by
      apply ContinuousAlternatingMap.mem_contractionAnnihilator_iff.mpr
      intro beta hbeta
      rw [Submodule.finrank_eq_zero.mp (hzero r hr x)] at hbeta
      simp only [Submodule.mem_bot] at hbeta
      simp [hbeta]
    have hricci := ricciTensor_eq_zero_of_mem_curvatureOperatorImageAnnihilatorAt
      (S.family.metric r) x hnull v
    have h := metricDerivAt S hS ⟨r, hreg hr⟩ x u v
    change HasDerivAt (fun z => (S.family.metric z).inner x u v)
      (-2 * metricRicciAt (S.family.metric r) x (vec2 u v)) r at h
    rw [metricRicciAt_apply_eq_ricciTensor, hricci, mul_zero] at h
    exact h
  exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun r hr => (hderiv r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hderiv r hr).deriv) hs ht

omit [SigmaCompactSpace M] in
theorem stationary_flat_of_curvatureOperatorImageAt_finrank_eq_zero_of_compact
    [CompactSpace M] [ConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3)
    {a b s : ℝ} (hs : s ∈ Ioo a b) (hreg : Ioo a b ⊆ D.regular)
    (hR : ∀ t ∈ Ioo a b, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
        algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (x₀ : M)
    (hzero : Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric s) x₀
      ⟨metricRm04At (S.family.metric s) x₀,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric s) x₀⟩) = 0) :
    ∀ t ∈ Ioo a b, S.family.metric t = S.family.metric s ∧
      ∀ (x : M) (u v w : TangentSpace I x),
        riemannOp (LeviCivita (S.family.metric t))
          x u v w = 0 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hzeroPast (t : ℝ) (ht : t ∈ Ioo a b) (hts : t ≤ s) (x : M) :
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) = 0 := by
    rcases hts.eq_or_lt with rfl | hts
    · obtain ⟨r, har, hrs⟩ := exists_between hs.1
      have hsub : Icc r t ⊆ Ioo a b := fun q hq =>
        ⟨har.trans_le hq.1, hq.2.trans_lt hs.2⟩
      exact (curvatureOperatorImageAt_finrank_eq_at_later_time S hS hdim hrs
        (hsub.trans hreg) (fun q hq => hR q (hsub hq)) x x₀).trans hzero
    · have hsub : Icc t s ⊆ Ioo a b := fun q hq =>
        ⟨ht.1.trans_le hq.1, hq.2.trans_lt hs.2⟩
      have hle := curvatureOperatorImageAt_finrank_le_at_later_time S hS hdim hts
        (hsub.trans hreg) (fun q hq => hR q (hsub hq)) x x₀
      omega
  have hforward (u v : ℝ) (hu : u ∈ Ioo a b) (hv : v ∈ Ioo a b) (huv : u ≤ v)
      (hRicci : ∀ (x : M) (w z : TangentSpace I x),
        ricciTensor (S.family.metric u) x w z = 0) :
      S.family.metric v = S.family.metric u := by
    obtain ⟨w, hvw, hwb⟩ := exists_between hv.2
    have huw : u < w := huv.trans_lt hvw
    have hsub : Ico u w ⊆ Ioo a b := fun q hq =>
      ⟨hu.1.trans_le hq.1, hq.2.trans hwb⟩
    have heq := metric_eq_on_Ico_of_initial_of_compact S hS
      (SolutionOn.const (S.family.metric u) D)
      (isSolutionOn_const_of_ricciTensor_eq_zero (S.family.metric u) hRicci D)
      huw (hsub.trans hreg) (hsub.trans hreg) rfl
    exact heq v ⟨huv, hvw⟩
  intro t ht
  have hmetric : S.family.metric t = S.family.metric s := by
    rcases le_total s t with hst | hts
    · exact hforward s t hs ht hst fun x w z =>
        ricciTensor_eq_zero_of_mem_curvatureOperatorImageAnnihilatorAt (S.family.metric s) x
          (mem_curvatureOperatorImageAnnihilatorAt_of_finrank_eq_zero
            (S.family.metric s) x (hzeroPast s hs le_rfl x) w) z
    · exact (hforward t s ht hs hts fun x w z =>
        ricciTensor_eq_zero_of_mem_curvatureOperatorImageAnnihilatorAt (S.family.metric t) x
          (mem_curvatureOperatorImageAnnihilatorAt_of_finrank_eq_zero
            (S.family.metric t) x (hzeroPast t ht hts x) w) z).symm
  refine ⟨hmetric, ?_⟩
  intro x u v w
  rw [hmetric]
  exact riemannOp_eq_zero_of_mem_curvatureOperatorImageAnnihilatorAt (S.family.metric s) x
    (mem_curvatureOperatorImageAnnihilatorAt_of_finrank_eq_zero
      (S.family.metric s) x (hzeroPast s hs le_rfl x) w) u v

end DifferentialGeometry.PDE.RicciFlow
