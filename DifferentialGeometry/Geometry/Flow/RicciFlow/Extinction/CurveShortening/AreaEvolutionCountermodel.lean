import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaEvolution

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [hBoundary : I.Boundaryless] [hT2 : T2Space M] [hCompact : CompactSpace M]
  [hNonempty : Nonempty M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {a b : ℝ}

theorem not_slope_bound_of_constant_area {A S Err : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hA : ∀ t ∈ Icc a b, A t = A a) (hErr : Err a = 0) (hSA : 0 ≤ S a * A a / 2) :
    ¬ (∀ t ∈ Ico a b, ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ b →
      (A (t + h) - A t) / h ≤ -2 * Real.pi - S t * A t / 2 + Err t + ε) := by
  intro h
  obtain ⟨δ, hδpos, hδ⟩ := h a ⟨le_rfl, hab⟩ Real.pi Real.pi_pos
  obtain ⟨k, hkpos, hkδ, hkb⟩ :
      ∃ k : ℝ, 0 < k ∧ k < δ ∧ k ≤ (b - a) / 2 := by
    refine ⟨min (δ / 2) ((b - a) / 2), lt_min (by linarith) (by linarith), ?_, min_le_right _ _⟩
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hak : a + k ≤ b := by linarith
  have hAeq : A (a + k) = A a := hA (a + k) ⟨by linarith, hak⟩
  have hquot : (A (a + k) - A a) / k = 0 := by rw [hAeq, sub_self, zero_div]
  have hle := hδ k ⟨hkpos, hkδ⟩ hak
  rw [hquot, hErr] at hle
  have hneg : 0 ≤ -Real.pi - S a * A a / 2 := by linarith
  linarith [Real.pi_pos, hSA]

theorem exists_not_slope_bound_data :
    ∀ {S : ℝ → ℝ} {a : ℝ}, S a = 0 →
      ¬ (∀ t ∈ Ico a (a + 1), ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ a + 1 →
        (0 - 0) / h ≤ -2 * Real.pi - S t * 0 / 2 + 0 + ε) := by
  intro S a hS
  refine not_slope_bound_of_constant_area (A := fun _ => 0) (S := S) (Err := fun _ => 0)
    (by linarith) (fun t _ => rfl) rfl ?_
  rw [hS]
  norm_num

omit hBoundary hCompact hNonempty [SigmaCompactSpace M] in
theorem not_area_conclusion_of_static_family
    (B : RicciBackground (I := I) (M := M) D a b) (γ : ℝ → ContinuousFreeLoop M)
    (hstatic : ∀ t, B.family.metric t = B.family.metric a)
    (hfixed : ∀ t, γ t = γ a)
    (hErr : (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) a = 0)
    (hS : 0 ≤ scalarMinimum B.family a)
    (hA : 0 ≤ loopFamilyLeastArea B.family.metric γ a) :
    ¬ (∀ t ∈ Ico a b, ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ b →
      (loopFamilyLeastArea B.family.metric γ (t + h) -
          loopFamilyLeastArea B.family.metric γ t) / h ≤
        -2 * Real.pi -
            scalarMinimum B.family t * loopFamilyLeastArea B.family.metric γ t / 2 +
          (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t + ε) := by
  refine not_slope_bound_of_constant_area (S := scalarMinimum B.family)
    (Err := (curveOfLoopFamily γ).areaError B.family.metric (Icc a b)) B.lt ?_ hErr ?_
  · intro t _
    rw [loopFamilyLeastArea, loopFamilyLeastArea, hstatic t, hfixed t]
  · exact div_nonneg (mul_nonneg hS hA) (by norm_num)

omit hNonempty [SigmaCompactSpace M] in
theorem not_rfs_csf_embedded_area_of_static_family
    (B : RicciBackground (I := I) (M := M) D a b) (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hctr : ∀ t ∈ Icc a b, IsContractibleLoop (γ t))
    (hstatic : ∀ t, B.family.metric t = B.family.metric a)
    (hfixed : ∀ t, γ t = γ a)
    (hErr : (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) a = 0)
    (hS : 0 ≤ scalarMinimum B.family a) :
    ¬ (∀ t ∈ Ico a b, ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ b →
      (loopFamilyLeastArea B.family.metric γ (t + h) -
          loopFamilyLeastArea B.family.metric γ t) / h ≤
        -2 * Real.pi -
            scalarMinimum B.family t * loopFamilyLeastArea B.family.metric γ t / 2 +
          (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t + ε) :=
  not_area_conclusion_of_static_family B γ hstatic hfixed hErr hS
    (loopFamilyLeastArea_nonneg B.family.metric γ hγ hctr a ⟨le_rfl, B.lt.le⟩)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
