import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.GoodWindows
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.RampLengthEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.SliceRegularityFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.SliceRegularityImmersed

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    [SigmaCompactSpace Q] [hT2 : T2Space Q] [hCompact : CompactSpace Q]
    [hConnected : ConnectedSpace Q] [hBoundary : I.Boundaryless]
    {D : RealTimeInterval} {a b : ℝ}

include hT2 hCompact hConnected hBoundary

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  hT2 hCompact hConnected hBoundary in
theorem goodWindowUnion_empty (d : ℝ) :
    goodWindowUnion (∅ : Finset ℝ) d = ∅ := by
  ext t
  simp [goodWindowUnion]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  hT2 hCompact hConnected hBoundary in
theorem goodWindowUnion_singleton (w d : ℝ) :
    goodWindowUnion {w} d = Icc (w + 5 * d / 8) (w + 7 * d / 8) := by
  ext t
  simp [goodWindowUnion]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  hT2 hCompact hConnected hBoundary in
theorem goodWindowUnion_singleton_nonempty {w d : ℝ} (hd : 0 ≤ d) :
    (goodWindowUnion {w} d).Nonempty := by
  rw [goodWindowUnion_singleton]
  exact ⟨w + 5 * d / 8, left_mem_Icc.mpr (by linarith)⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  hT2 hCompact hConnected hBoundary in
theorem goodWindowUnion_singleton_subset_Ioo {w d : ℝ} (hd : 0 < d) :
    goodWindowUnion {w} d ⊆ Ioo (w + d / 2) (w + d) := by
  intro t ht
  rw [goodWindowUnion_singleton] at ht
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  hT2 hCompact hConnected hBoundary in
theorem exists_nonempty_goodWindow_finset_of_zero_energy :
    ∃ starts : Finset ℝ,
      starts.Nonempty ∧
      (∀ w ∈ starts, w ∈ Icc (0 : ℝ) (3 - 1) ∧ (0 : ℝ) ≤ 1) ∧
      goodWindowUnion starts 1 ⊆ Ioo (0 : ℝ) 3 ∧
      volume (Icc (0 : ℝ) 3 \ goodWindowUnion starts 1) ≤ ENNReal.ofReal (1 + 0 / 1) ∧
      ∀ w ∈ starts, Icc (w + 5 * 1 / 8) (w + 7 * 1 / 8) ⊆ Ioo (w + 1 / 2) (w + 1) := by
  obtain ⟨starts, hmem, hsub, hvol, hwin⟩ :=
    exists_goodWindow_finset_of_energy_bound (a := (0 : ℝ)) (b := 3) (d := 1) (C := 0)
      (threshold := 1) (f := fun _ : ℝ => 0) (by norm_num) (by norm_num)
      intervalIntegrable_const (fun t _ => by norm_num)
      (by rw [intervalIntegral.integral_const]; norm_num) (by norm_num)
  refine ⟨starts, ?_, ?_, hsub, hvol, hwin⟩
  · rcases Finset.eq_empty_or_nonempty starts with h | h
    · exfalso
      rw [h, goodWindowUnion_empty, Set.sdiff_empty, Real.volume_Icc] at hvol
      simp only [sub_zero] at hvol
      have hle : (3 : ℝ) ≤ 1 + 0 / 1 := (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp hvol
      norm_num at hle
    · exact h
  · intro w hw
    exact ⟨(hmem w hw).1, (hmem w hw).2⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  hT2 hCompact hConnected hBoundary in
theorem integral_bound_necessary_for_goodWindow_finset :
    ∃ (f : ℝ → ℝ) (C : ℝ),
      IntervalIntegrable f volume (0 : ℝ) 3 ∧ (∀ t ∈ Icc (0 : ℝ) 3, 0 ≤ f t) ∧
      C < ∫ t in (0 : ℝ)..3, f t ∧
      ¬ ∃ starts : Finset ℝ,
        (∀ w ∈ starts, w ∈ Icc (0 : ℝ) (3 - 1) ∧ f w ≤ 1) ∧
        goodWindowUnion starts 1 ⊆ Ioo (0 : ℝ) 3 ∧
        volume (Icc (0 : ℝ) 3 \ goodWindowUnion starts 1) ≤ ENNReal.ofReal (1 + C / 1) ∧
        ∀ w ∈ starts, Icc (w + 5 * 1 / 8) (w + 7 * 1 / 8) ⊆ Ioo (w + 1 / 2) (w + 1) :=
  ⟨fun _ => 2, 0, intervalIntegrable_const, fun t _ => by norm_num,
    by rw [intervalIntegral.integral_const]; norm_num, by
      rintro ⟨starts, hmem, -, hvol, -⟩
      have hempty : starts = ∅ := Finset.not_nonempty_iff_eq_empty.mp fun hne => by
        obtain ⟨w, hw⟩ := hne
        have h : (2 : ℝ) ≤ 1 := (hmem w hw).2
        norm_num at h
      rw [hempty, goodWindowUnion_empty, Set.sdiff_empty, Real.volume_Icc] at hvol
      simp only [sub_zero] at hvol
      have hle : (3 : ℝ) ≤ 1 + 0 / 1 := (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp hvol
      norm_num at hle⟩

omit hT2 hCompact hConnected hBoundary [FiniteDimensional ℝ E] [CompleteSpace E]
  [SigmaCompactSpace Q] in
theorem exists_ramp_with_not_immersed_projection (g : SmoothRiemannianMetric I Q) {lambda : ℝ}
    (hlambda : 0 < lambda) (q : Q) :
    ∃ c : ProductCurve Q,
      c.SmoothOn (I := I) (univ : Set ℝ) ∧ c.IsRampOn (fun _ : ℝ => g) lambda (univ : Set ℝ) ∧
        c.degree = 1 ∧ ¬ c.projection.ImmersedOn (I := I) (univ : Set ℝ) :=
  ⟨_, initialRamp_constantLoop_rampData (I := I) g hlambda q⟩

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
theorem rfs_finite_good_windows_of_length_evolution_and_slice_regularity
    (B : RicciBackground (I := I) (M := Q) D a b)
    (L₀ Theta₀ : ℝ) (K : CurveShorteningRegularityInput B L₀ Theta₀)
    (hev : RampLengthEvolution (I := I) (Q := Q) (D := D) (a := a) (b := b) B)
    (hslice : CurveShorteningSliceRegularity (I := I) (Q := Q) (D := D) (a := a) (b := b)
      B L₀) :
    let delta := localRegularityDelta B L₀ Theta₀ K
    let r₀ := localRegularityRadius B L₀ Theta₀ K
    let areg := localRegularityCoefficient B L₀ Theta₀ K 0
    let C_E := Real.exp (B.B₀ * (b - a)) * L₀
    ∀ ell threshold : ℝ, 0 < ell → 0 < threshold →
      let r := min r₀ (min (ell / 2) (delta ^ 2 / threshold))
      let d := delta * r ^ 2
      d < b - a →
      ∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 → ∀ c : ProductCurve Q,
        c.IsSolutionOn B.family.metric lambda (Icc a b) →
        c.IsRampOn B.family.metric lambda (Icc a b) → c.degree = 1 →
        c.length B.family.metric lambda a ≤ L₀ →
        c.totalCurvature B.family.metric lambda a ≤ Theta₀ →
        (∀ t ∈ Icc a b, ell ≤ c.length B.family.metric lambda t) →
        ∃ starts : Finset ℝ,
          (∀ w ∈ starts, w ∈ Icc a (b - d) ∧
            c.energy B.family.metric lambda w ≤ threshold) ∧
          goodWindowUnion starts d ⊆ Ioo a b ∧
          volume (Icc a b \ goodWindowUnion starts d) ≤ ENNReal.ofReal (d + C_E / threshold) ∧
          (∀ x t, t ∈ goodWindowUnion starts d →
            c.curvature B.family.metric lambda x t ≤ Real.sqrt (2 * areg / d)) ∧
          ∀ w ∈ starts, Icc (w + 5 * d / 8) (w + 7 * d / 8) ⊆ Ioo (w + d / 2) (w + d) :=
  rfs_finite_good_windows_of_length_evolution B L₀ Theta₀ K hev
    fun lambda hlambda hlambda_one c hsol hlen t ht =>
      hslice lambda hlambda hlambda_one c hsol hlen t ht

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
