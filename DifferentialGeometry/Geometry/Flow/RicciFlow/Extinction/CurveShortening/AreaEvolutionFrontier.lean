import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.MinimalDiskAreaVariation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LoopFamilyContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.BoundaryIsotopy

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

def LoopFamilyLeastAreaSlopeBound (B : RicciBackground (I := I) (M := M) D a b)
    (γ : ℝ → ContinuousFreeLoop M) : Prop :=
  ∀ t ∈ Ico a b, ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ b →
    (loopFamilyLeastArea B.family.metric γ (t + h) -
        loopFamilyLeastArea B.family.metric γ t) / h ≤
      -2 * Real.pi - scalarMinimum B.family t * loopFamilyLeastArea B.family.metric γ t / 2 +
        (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t + ε

omit hBoundary hCompact hNonempty [SigmaCompactSpace M] in
theorem loopFamilyLeastAreaSlopeBound_of_minimalDiskAreaVariation
    (B : RicciBackground (I := I) (M := M) D a b) (γ : ℝ → ContinuousFreeLoop M)
    (hvar : MinimalDiskAreaVariation (I := I) (M := M) B γ) :
    LoopFamilyLeastAreaSlopeBound (I := I) (M := M) B γ :=
  rfs_csf_embedded_area_of_minimalDiskAreaVariation (I := I) (M := M) B γ hvar

omit [SigmaCompactSpace M] in
theorem rfs_csf_immersed_area_of_loopFamilyLeastAreaSlopeBound
    (B : RicciBackground (I := I) (M := M) D a b) (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b))
    (hctr : ∀ t ∈ Icc a b, IsContractibleLoop (γ t))
    (hbound : LoopFamilyLeastAreaSlopeBound (I := I) (M := M) B γ) :
    ContinuousOn (loopFamilyLeastArea B.family.metric γ) (Icc a b) ∧
      (∀ s ∈ Icc a b, ∀ t ∈ Icc s b,
        areaIntegratingFactor B.family s t * loopFamilyLeastArea B.family.metric γ t ≤
          loopFamilyLeastArea B.family.metric γ s +
            ∫ v in s..t, areaIntegratingFactor B.family s v *
              (-2 * Real.pi + (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) v)) ∧
      (∀ t ∈ Ico a b, ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ b →
        (loopFamilyLeastArea B.family.metric γ (t + h) -
            loopFamilyLeastArea B.family.metric γ t) / h ≤
          -2 * Real.pi - scalarMinimum B.family t * loopFamilyLeastArea B.family.metric γ t / 2 +
            (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t + ε) :=
  rfs_csf_immersed_area_of_slope (I := I) (M := M) B γ hγ hi hctr hbound

omit hBoundary hCompact hNonempty [SigmaCompactSpace M] in
theorem loopFamilyLeastAreaSlopeBound_of_rfs_csf_immersed_area
    (h : ∀ (B : RicciBackground (I := I) (M := M) D a b) (_ : Module.finrank ℝ E = 3)
        (γ : ℝ → ContinuousFreeLoop M),
      (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b) →
      (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b) →
      (∀ t ∈ Icc a b, IsContractibleLoop (γ t)) →
      ContinuousOn (loopFamilyLeastArea B.family.metric γ) (Icc a b) ∧
        (∀ s ∈ Icc a b, ∀ t ∈ Icc s b,
          areaIntegratingFactor B.family s t * loopFamilyLeastArea B.family.metric γ t ≤
            loopFamilyLeastArea B.family.metric γ s +
              ∫ v in s..t, areaIntegratingFactor B.family s v *
                (-2 * Real.pi + (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) v)) ∧
        (∀ t ∈ Ico a b, ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ b →
          (loopFamilyLeastArea B.family.metric γ (t + h) -
              loopFamilyLeastArea B.family.metric γ t) / h ≤
            -2 * Real.pi - scalarMinimum B.family t * loopFamilyLeastArea B.family.metric γ t / 2 +
              (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t + ε)) :
    ∀ (B : RicciBackground (I := I) (M := M) D a b) (_ : Module.finrank ℝ E = 3)
      (γ : ℝ → ContinuousFreeLoop M),
      (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b) →
      (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b) →
      (∀ t ∈ Icc a b, IsContractibleLoop (γ t)) →
      LoopFamilyLeastAreaSlopeBound (I := I) (M := M) B γ :=
  fun B hdim γ hγ hi hctr => (h B hdim γ hγ hi hctr).2.2

omit hBoundary hCompact hNonempty [SigmaCompactSpace M] in
theorem rfs_csf_embedded_area_of_rfs_csf_immersed_area
    (h : ∀ (B : RicciBackground (I := I) (M := M) D a b) (_ : Module.finrank ℝ E = 3)
        (γ : ℝ → ContinuousFreeLoop M),
      (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b) →
      (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b) →
      (∀ t ∈ Icc a b, IsContractibleLoop (γ t)) →
      ContinuousOn (loopFamilyLeastArea B.family.metric γ) (Icc a b) ∧
        (∀ s ∈ Icc a b, ∀ t ∈ Icc s b,
          areaIntegratingFactor B.family s t * loopFamilyLeastArea B.family.metric γ t ≤
            loopFamilyLeastArea B.family.metric γ s +
              ∫ v in s..t, areaIntegratingFactor B.family s v *
                (-2 * Real.pi + (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) v)) ∧
        (∀ t ∈ Ico a b, ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ b →
          (loopFamilyLeastArea B.family.metric γ (t + h) -
              loopFamilyLeastArea B.family.metric γ t) / h ≤
            -2 * Real.pi - scalarMinimum B.family t * loopFamilyLeastArea B.family.metric γ t / 2 +
              (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t + ε)) :
    ∀ (B : RicciBackground (I := I) (M := M) D a b) (_ : Module.finrank ℝ E = 3)
      (γ : ℝ → ContinuousFreeLoop M),
      (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b) →
      (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b) →
      (∀ t ∈ Icc a b, IsContractibleLoop (γ t)) →
      (∀ t ∈ Icc a b, Topology.IsEmbedding (γ t)) →
      ContinuousOn (loopFamilyLeastArea B.family.metric γ) (Icc a b) ∧
        (∀ s ∈ Icc a b, ∀ t ∈ Icc s b,
          areaIntegratingFactor B.family s t * loopFamilyLeastArea B.family.metric γ t ≤
            loopFamilyLeastArea B.family.metric γ s +
              ∫ v in s..t, areaIntegratingFactor B.family s v *
                (-2 * Real.pi + (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) v)) ∧
        (∀ t ∈ Ico a b, ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ b →
          (loopFamilyLeastArea B.family.metric γ (t + h) -
              loopFamilyLeastArea B.family.metric γ t) / h ≤
            -2 * Real.pi - scalarMinimum B.family t * loopFamilyLeastArea B.family.metric γ t / 2 +
              (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t + ε) :=
  fun B hdim γ hγ hi hctr _hemb => h B hdim γ hγ hi hctr

omit [CompleteSpace E] hNonempty in
theorem rfs_csf_boundary_isotopy_of_velocityExtension_exists
    (hvel : ∀ (a' b' : ℝ) (γ : ℝ → ContinuousFreeLoop M),
      (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a' b') →
      (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a' b') →
      (∀ t ∈ Icc a' b', Topology.IsEmbedding (γ t)) →
      LoopFamilyVelocityExtension (I := I) a' b' γ)
    (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b))
    (hemb : ∀ t ∈ Icc a b, Topology.IsEmbedding (γ t))
    (t₀ : ℝ) (ht₀ : t₀ ∈ Icc a b) (hab : a < b) :
      ∃ ε > 0, ∃ Φ : ℝ → Diffeomorph I I M M ∞,
        ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun p : M × ℝ => Φ p.2 p.1)
          (univ ×ˢ (Icc a b ∩ Ioo (t₀ - ε) (t₀ + ε))) ∧
        (∀ p, Φ t₀ p = p) ∧
        ∀ t ∈ Icc a b ∩ Ioo (t₀ - ε) (t₀ + ε), ∀ z, Φ t (γ t₀ z) = γ t z := by
  let _ := hab
  exact rfs_csf_boundary_isotopy_of_velocityExtension a b γ t₀ ht₀ (hvel a b γ hγ hi hemb)

theorem tendsto_div_eq_zero_of_eventually_eq_zero {A : ℝ → ℝ} {c : ℝ}
    (hA : ∀ᶠ h in 𝓝[>] (0 : ℝ), A h = 0)
    (ht : Tendsto (fun h : ℝ => A h / h) (𝓝[>] (0 : ℝ)) (𝓝 c)) : c = 0 := by
  have h0 : Tendsto (fun h : ℝ => A h / h) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.congr' (hA.mono fun h hh => by simp only [hh, zero_div])
  exact tendsto_nhds_unique ht h0

theorem not_exists_tendsto_div_of_eventually_eq_zero_of_neg_bound {A : ℝ → ℝ} {th : ℝ}
    (hth : th < 0) (hA : ∀ᶠ h in 𝓝[>] (0 : ℝ), A h = 0) :
    ¬ ∃ c : ℝ, c ≤ th ∧ Tendsto (fun h : ℝ => A h / h) (𝓝[>] (0 : ℝ)) (𝓝 c) := by
  rintro ⟨c, hc, ht⟩
  have hc0 : c = 0 := tendsto_div_eq_zero_of_eventually_eq_zero hA ht
  linarith

omit hBoundary hCompact hNonempty [SigmaCompactSpace M] in
theorem not_minimalDiskAreaVariation_of_eventually_diskArea_eq
    (B : RicciBackground (I := I) (M := M) D a b) (γ : ℝ → ContinuousFreeLoop M)
    {t : ℝ} (ht : t ∈ Ico a b)
    (hth : -2 * Real.pi - scalarMinimum B.family t *
        loopFamilyLeastArea B.family.metric γ t / 2 +
        (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t < 0)
    (hz : ∀ (u : Width.DiskCompetitor (B.family.metric t) (γ t)) (φ : ℝ → M → M),
      ∀ᶠ h in 𝓝[>] (0 : ℝ),
        Width.diskArea (B.family.metric (t + h)) (fun z : Width.Disk => φ h (u.1.map z)) -
          Width.diskArea (B.family.metric t) u.1.map = 0) :
    ¬ MinimalDiskAreaVariation (I := I) (M := M) B γ := by
  intro hvar
  obtain ⟨u, φ, -, -, -, -, -, c, hc, htend⟩ := hvar t ht
  exact not_exists_tendsto_div_of_eventually_eq_zero_of_neg_bound hth (hz u φ) ⟨c, hc, htend⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
