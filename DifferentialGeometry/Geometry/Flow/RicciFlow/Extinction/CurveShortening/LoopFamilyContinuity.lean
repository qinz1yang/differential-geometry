import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.MinimalDiskAreaVariation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.Loops

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [hBoundary : I.Boundaryless] [hT2 : T2Space M] [hCompact : CompactSpace M]
  [hNonempty : Nonempty M] [SigmaCompactSpace M]
  {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval} {a b : ℝ}

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] hBoundary hT2 hCompact
  hNonempty [SigmaCompactSpace M] in
theorem continuousOn_deriv_embeddedLoopFamily {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (γ : ℝ → ContinuousFreeLoop M) {J : Set ℝ} (hJ : UniqueDiffOn ℝ J)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) J) :
    ContinuousOn
      (fun p : ℝ × ℝ => deriv (fun s : ℝ => e.map (γ p.2 (s : Surgery.Topology.Circle))) p.1)
      (univ ×ˢ J) := by
  have hG : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞
      (fun p : ℝ × ℝ => e.map (γ p.2 (p.1 : Surgery.Topology.Circle))) (univ ×ˢ J) :=
    (e.smooth.contMDiffOn (s := univ)).comp hγ fun p _ => mem_univ _
  have hG' : ContDiffOn ℝ ∞
      (fun p : ℝ × ℝ => e.map (γ p.2 (p.1 : Surgery.Topology.Circle))) (univ ×ˢ J) :=
    contMDiffOn_iff_contDiffOn.mp hG
  have huniq : UniqueDiffOn ℝ ((univ : Set ℝ) ×ˢ J) :=
    UniqueDiffOn.prod uniqueDiffOn_univ hJ
  have hfd : ContinuousOn (fderivWithin ℝ
      (fun p : ℝ × ℝ => e.map (γ p.2 (p.1 : Surgery.Topology.Circle))) (univ ×ˢ J))
      (univ ×ˢ J) :=
    hG'.continuousOn_fderivWithin huniq (by simp)
  refine (hfd.clm_apply (continuousOn_const (c := ContinuousLinearMap.inl ℝ ℝ ℝ 1))).congr
    fun q hq => ?_
  have hqJ : q.2 ∈ J := hq.2
  have hd : HasFDerivWithinAt
      (fun p : ℝ × ℝ => e.map (γ p.2 (p.1 : Surgery.Topology.Circle)))
      (fderivWithin ℝ
        (fun p : ℝ × ℝ => e.map (γ p.2 (p.1 : Surgery.Topology.Circle))) (univ ×ˢ J) q)
      (univ ×ˢ J) q :=
    ((hG'.contDiffWithinAt ⟨mem_univ _, hqJ⟩).differentiableWithinAt (by simp)).hasFDerivWithinAt
  have hι : HasDerivWithinAt (fun t : ℝ => (t, q.2))
      ((ContinuousLinearMap.inl ℝ ℝ ℝ) 1) univ q.1 :=
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) q.1 q.2).hasDerivAt.hasDerivWithinAt
  have hcomp := hd.comp_hasDerivWithinAt (t := (univ : Set ℝ) ×ˢ J) q.1 hι
    (fun t (_ : t ∈ (univ : Set ℝ)) => ⟨mem_univ _, hqJ⟩)
  exact (hcomp.hasDerivAt univ_mem).deriv

omit [CompleteSpace E] [SigmaCompactSpace M] in
theorem exists_continuousOn_contractibleRegularLoop_family
    (γ : ℝ → ContinuousFreeLoop M) {a b : ℝ}
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hctr : ∀ t ∈ Icc a b, IsContractibleLoop (γ t)) :
    ∃ Γ : ℝ → Width.ContractibleRegularLoop (I := I) (Q := M),
      ContinuousOn Γ (Icc a b) ∧ ∀ t ∈ Icc a b, (Γ t).1.toContinuousLoop = γ t := by
  classical
  let Γ : ℝ → Width.ContractibleRegularLoop (I := I) (Q := M) := fun t =>
    if ht : t ∈ Icc a b then ⟨regularLoopSlice γ hγ t ht, hctr t ht⟩
    else Width.constantContractibleRegularLoop (I := I) (Q := M)
      (Classical.choice (inferInstance : Nonempty M))
  refine ⟨Γ, ?_, ?_⟩
  · by_cases hab : a < b
    · obtain ⟨N, ⟨e⟩⟩ := Width.smoothLoopEmbedding_exists (I := I) (Q := M)
      have huniq : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
      have hreindex : Continuous (fun p : ↥(Icc a b) × ℝ => (p.2, p.1.1)) := by fun_prop
      have hmem : ∀ p : ↥(Icc a b) × ℝ, (p.2, p.1.1) ∈ (univ : Set ℝ) ×ˢ Icc a b :=
        fun p => ⟨mem_univ _, p.1.2⟩
      have hGc : ContinuousOn
          (fun p : ℝ × ℝ => e.map (γ p.2 (p.1 : Surgery.Topology.Circle)))
          (univ ×ˢ Icc a b) :=
        ((e.smooth.contMDiffOn (s := univ)).comp hγ fun p _ => mem_univ _).continuousOn
      have hvalℝ : Continuous
          (fun p : ↥(Icc a b) × ℝ => e.map (γ p.1.1 (p.2 : Surgery.Topology.Circle))) :=
        hGc.comp_continuous hreindex hmem
      have hval : Continuous
          (fun p : ↥(Icc a b) × Surgery.Topology.Circle => e.map (γ p.1.1 p.2)) :=
        (IsOpenQuotientMap.id.prodMap
          (QuotientAddGroup.isOpenQuotientMap_mk)).continuous_comp_iff.mp hvalℝ
      have hder : Continuous (fun p : ↥(Icc a b) × ℝ =>
          deriv (fun t : ℝ => e.map (γ p.1.1 (t : Surgery.Topology.Circle))) p.2) :=
        (continuousOn_deriv_embeddedLoopFamily (I := I) (M := M) e γ huniq hγ).comp_continuous
          hreindex hmem
      have hslice : Continuous (fun τ : ↥(Icc a b) => regularLoopSlice γ hγ τ.1 τ.2) :=
        (Width.continuous_regularLoop_iff (I := I) (Q := M) e _).mpr ⟨hval, hder⟩
      rw [continuousOn_iff_continuous_domRestrict]
      exact (hslice.subtype_mk (fun τ => hctr τ.1 τ.2)).congr fun τ => by
        simp only [Γ, Set.domRestrict_apply, dite_eq_left τ.2]
    · rw [not_lt] at hab
      refine (continuousOn_singleton Γ a).mono fun x hx => ?_
      simp only [mem_singleton_iff]
      linarith [hx.1, hx.2, hab]
  · intro t ht
    simp only [Γ, dite_eq_left ht]
    rfl

omit [SigmaCompactSpace M] in
theorem continuousOn_loopFamilyLeastArea_of_contractible
    (B : RicciBackground (I := I) (M := M) D a b)
    (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hctr : ∀ t ∈ Icc a b, IsContractibleLoop (γ t)) :
    ContinuousOn (loopFamilyLeastArea B.family.metric γ) (Icc a b) := by
  obtain ⟨Γ, hΓ, hagree⟩ := exists_continuousOn_contractibleRegularLoop_family γ hγ hctr
  exact continuousOn_loopFamilyLeastArea_of_continuousRegularFamily B γ Γ hΓ hagree

omit [SigmaCompactSpace M] in
theorem rfs_csf_immersed_area_of_slope
    (B : RicciBackground (I := I) (M := M) D a b)
    (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b))
    (hctr : ∀ t ∈ Icc a b, IsContractibleLoop (γ t))
    (hslope : ∀ t ∈ Ico a b, ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ b →
      (loopFamilyLeastArea B.family.metric γ (t + h) -
          loopFamilyLeastArea B.family.metric γ t) / h ≤
        -2 * Real.pi - scalarMinimum B.family t * loopFamilyLeastArea B.family.metric γ t / 2 +
          (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t + ε) :
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
  rfs_csf_immersed_area_of_continuousOn_leastArea_of_slope B γ hγ hi
    (continuousOn_loopFamilyLeastArea_of_contractible B γ hγ hctr) hslope

omit [SigmaCompactSpace M] in
theorem rfs_csf_immersed_area_of_minimalDiskAreaVariation
    (B : RicciBackground (I := I) (M := M) D a b)
    (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b))
    (hctr : ∀ t ∈ Icc a b, IsContractibleLoop (γ t))
    (hvar : MinimalDiskAreaVariation (I := I) (M := M) B γ) :
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
  rfs_csf_immersed_area_of_continuousOn_leastArea_of_minimalDiskAreaVariation B γ hγ hi
    (continuousOn_loopFamilyLeastArea_of_contractible B γ hγ hctr) hvar

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
