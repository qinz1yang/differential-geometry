import DifferentialGeometry.Analysis.Parabolic.Moser.EvolvingSmallExponentLocalBoundedness
import DifferentialGeometry.Analysis.Calculus.SmoothClamp
import DifferentialGeometry.Geometry.Operator.LaplacianBridge

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Moser

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.Energy
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

def evolvingSeparatedCylinderHarnackFactor
    (n : ℕ) (V : ℝ≥0∞)
    (C G Bearly Blate rate p₀ Ctail W A earlyLower earlyUpper b τ c d D
      lower upper innerLower innerUpper : ℝ) : ℝ :=
  let c₀ := max 1 (V.toReal * (4 * Ctail * W))
  evolvingMoserPositiveExponentLocalBoundFactor
      n V V C G Blate p₀ A earlyLower earlyUpper b innerLower innerUpper *
    canonicalEvolvingBombieriGiustiWeakHarnackBound
      n V C G Bearly Blate rate p₀ c₀ A b τ c d D lower upper

theorem evolvingSeparatedCylinderHarnackFactor_nonneg
    (n : ℕ) (V : ℝ≥0∞)
    (C G Bearly Blate rate Ctail W : ℝ)
    {p₀ A earlyLower earlyUpper b τ c d D lower upper innerLower innerUpper : ℝ}
    (hp₀ : 0 < p₀) :
    0 ≤ evolvingSeparatedCylinderHarnackFactor
      n V C G Bearly Blate rate p₀ Ctail W A earlyLower earlyUpper b
        τ c d D lower upper innerLower innerUpper := by
  unfold evolvingSeparatedCylinderHarnackFactor
    canonicalEvolvingBombieriGiustiWeakHarnackBound
  exact mul_nonneg
    (evolvingMoserPositiveExponentLocalBoundFactor_nonneg
      n V V C G Blate hp₀)
    (mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (Real.exp_pos _).le
        (mul_nonneg
          (evolvingBombieriGiustiLatePointwiseFactor_nonneg
            n V C G Blate p₀ τ c d D lower upper)
          (Real.exp_pos _).le)))

theorem evolving_harnack_on_separated_cylinders
    (qMetric : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho outer : SmoothScalar qMetric)
    (averagingCutoff : M → ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (Ccenter Ctail H W rate : ℝ)
    {p₀ A earlyLower earlyUpper b τ c d D C G Bearly Blate
      lower upper innerLower innerUpper t₀ : ℝ}
    (V : ℝ≥0∞)
    (hpos : ∀ t ∈ Icc A D, ∀ x, 0 < u t x)
    (hp₀ : 0 < p₀) (hp₀_one : p₀ < 1)
    (hAearly : A < earlyLower) (hearly : earlyLower ≤ earlyUpper)
    (hearlyb : earlyUpper < b) (hbτ : b < τ)
    (hτc : τ < c) (hcd : c ≤ d) (hdD : d < D)
    (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hBearly : 0 ≤ Bearly) (hBlate : 0 ≤ Blate)
    (hCtail : 0 ≤ Ctail) (hrate : 0 ≤ rate)
    (hlowerUpper : lower < upper) (hupperInner : upper ≤ innerLower)
    (hinner : innerLower < innerUpper)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun z : ℝ × M =>
          chartGramMatrix (I := I) (g z.1) x₀ z.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (haveragingCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞
      averagingCutoff)
    (hne : ∃ x, averagingCutoff x ≠ 0)
    (hPcenter : HasEvolvingLocalizedPoincare
      (I := I) (M := M) g averagingCutoff averagingCutoff Ccenter (Icc A D))
    (hPtail : HasEvolvingLocalizedPoincareAtAverage
      (I := I) (M := M) g outer.toFun averagingCutoff Ctail (Icc A D))
    (htraceAbs : ∀ t ∈ Icc A D, ∀ x : M,
      |(1 / 2) * traceTimeDerivMetric (I := I) g t x| ≤ H)
    (hmass_le : ∀ t ∈ Icc A D,
      evolvingCutoffMass (I := I) (M := M) g averagingCutoff t ≤ W)
    (hdrift_le : ∀ t ∈ Icc A D,
      evolvingLogCenterDrift
        (I := I) (M := M) g averagingCutoff Ccenter H t ≤ rate)
    (hSobolev : ∀ t ∈ Icc A D,
      localizedSobolevConstant (I := I) (M := M) (g t) hdim ≤ C)
    (htraceEarly : ∀ t ∈ Icc A D, ∀ x : M,
      -traceTimeDerivMetric (I := I) g t x ≤ Bearly)
    (htraceLate : ∀ t ∈ Icc A D, ∀ x : M,
      traceTimeDerivMetric (I := I) g t x ≤ Blate)
    (hrho : ∀ t ∈ Icc A D, ∀ x : M,
      (g t).inner x
          (gradFun (I := I) (g t) rho.toFun x)
          (gradFun (I := I) (g t) rho.toFun x) ≤ G)
    (hpde : ∀ t ∈ Icc A D, ∀ x : M,
      deriv (fun s => u s x) t =
        Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x)
    (hVzero : V ≠ 0) (hVtop : V ≠ ⊤)
    (hvolume : ∀ t ∈ Icc A D,
      riemannianMeasureFamily (I := I) (M := M) g t ≤
          V • riemannianVolumeMeasure (I := I) (M := M) qMetric ∧
        riemannianVolumeMeasure (I := I) (M := M) qMetric ≤
          V • riemannianMeasureFamily (I := I) (M := M) g t)
    (hearlyMeasure : ∀ k,
      localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k) A
          (bombieriGiustiIncreasingLevel b τ k) ≠ 0)
    (hearlyMeasure_le_one : ∀ k,
      (localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k) A
          (bombieriGiustiIncreasingLevel b τ k)).real Set.univ ≤ 1)
    (hlateMeasure : ∀ k,
      localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k)
          (bombieriGiustiDescendingLevel τ c k)
          (bombieriGiustiIncreasingLevel d D k) ≠ 0)
    (hlateMeasure_le_one : ∀ k,
      (localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k)
          (bombieriGiustiDescendingLevel τ c k)
          (bombieriGiustiIncreasingLevel d D k)).real Set.univ ≤ 1)
    (houter : ∀ k x,
      (bombieriGiustiSpatialCutoff rho lower upper k).toFun x ^ 2 ≤
        outer.toFun x ^ 2) :
    ∀ t ∈ Icc earlyLower earlyUpper, ∀ x : M,
      (bombieriGiustiSpatialCutoff rho innerLower innerUpper 0).toFun x ≠ 0 →
      ∀ q ∈ Icc c d, ∀ y : M,
        (bombieriGiustiSpatialCutoff rho innerLower innerUpper 0).toFun y ≠ 0 →
        u t x ≤
          evolvingSeparatedCylinderHarnackFactor
              (Module.finrank ℝ E) V C G Bearly Blate rate p₀ Ctail W
                A earlyLower earlyUpper b τ c d D lower upper
                innerLower innerUpper *
            u q y := by
  let U : ℝ × M → ℝ := fun z => u z.1 z.2
  have hU : Continuous U := hu.continuous
  have hAD : A ≤ D :=
    hAearly.le.trans (hearly.trans
      (hearlyb.le.trans (hbτ.le.trans (hτc.le.trans (hcd.trans hdD.le)))))
  have hK : IsCompact (Icc A D ×ˢ (Set.univ : Set M)) :=
    isCompact_Icc.prod isCompact_univ
  have hKne : (Icc A D ×ˢ (Set.univ : Set M)).Nonempty := by
    obtain ⟨x, _⟩ := hne
    exact ⟨(A, x), ⟨⟨le_rfl, hAD⟩, Set.mem_univ x⟩⟩
  obtain ⟨clamp, hclamp, hclamp_pos, hclamp_eq⟩ :=
    DifferentialGeometry.exists_smooth_positive_clamp_eventuallyEq_on_compact
      hK hKne hU (fun z hz => hpos z.1 hz.1 z.2)
  let v : ℝ → M → ℝ := fun t x => clamp (u t x)
  have hv : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M => v z.1 z.2) := by
    simpa only [v, U, Function.comp_apply] using hclamp.contMDiff.comp hu
  have hvpos : ∀ t x, 0 < v t x := fun t x => hclamp_pos (u t x)
  have hv_eq_u : ∀ t ∈ Icc A D, ∀ x, v t x = u t x := by
    intro t ht x
    have heq := (hclamp_eq (t, x) ⟨ht, Set.mem_univ x⟩).self_of_nhds
    simpa only [v, U, Function.comp_apply] using heq
  have hpde_v : ∀ t ∈ Icc A D, ∀ x : M,
      deriv (fun s => v s x) t =
        Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) v hv t).toContMDiffMap x := by
    intro t ht x
    have hjoint := hclamp_eq (t, x) ⟨ht, Set.mem_univ x⟩
    have htime :
        (fun s : ℝ => v s x) =ᶠ[nhds t] (fun s : ℝ => u s x) := by
      simpa only [v, U, Function.comp_apply] using
        hjoint.comp_tendsto (continuousAt_id.prodMk continuousAt_const)
    have hspace :
        (fun y : M => v t y) =ᶠ[nhds x] (fun y : M => u t y) := by
      simpa only [v, U, Function.comp_apply] using
        hjoint.comp_tendsto (continuousAt_const.prodMk continuousAt_id)
    calc
      deriv (fun s => v s x) t = deriv (fun s => u s x) t := htime.deriv_eq
      _ = Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x := hpde t ht x
      _ = Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) v hv t).toContMDiffMap x := by
        exact (Δ_g_congr_of_eventuallyEq (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) v hv t).smooth
          (smoothScalarSlice (I := I) (g t) u hu t).smooth hspace).symm
  let n := Module.finrank ℝ E
  let c₀ := max 1 (V.toReal * (4 * Ctail * W))
  let earlyNorm := localizedSpacetimeRpowNorm (I := I) (M := M)
    (bombieriGiustiSpatialCutoff rho lower upper 0) v p₀ A b
  let earlyFactor := evolvingMoserPositiveExponentLocalBoundFactor
    n V V C G Blate p₀ A earlyLower earlyUpper b innerLower innerUpper
  let weakFactor := canonicalEvolvingBombieriGiustiWeakHarnackBound
    n V C G Bearly Blate rate p₀ c₀ A b τ c d D lower upper
  have houterSpatial : bombieriGiustiDescendingLevel lower upper 1 < upper := by
    simpa only [bombieriGiustiDescendingLevel_zero] using
      bombieriGiustiDescendingLevel_strictAnti hlowerUpper
        (Nat.zero_lt_succ 0)
  have hAb : A ≤ b :=
    hAearly.le.trans (hearly.trans hearlyb.le)
  have hbD : b ≤ D :=
    hbτ.le.trans (hτc.le.trans (hcd.trans hdD.le))
  have hearlyFactor : 0 ≤ earlyFactor :=
    evolvingMoserPositiveExponentLocalBoundFactor_nonneg
      n V V C G Blate hp₀
  intro t ht x hx q hq y hy
  have hyOuter :
      (bombieriGiustiSpatialCutoff rho lower upper 0).toFun y ≠ 0 := by
    intro hzero
    have hle := bombieriGiustiSpatialCutoff_le_outer
      rho houterSpatial hupperInner hinner 0 y
    have hle' :
        (bombieriGiustiSpatialCutoff rho innerLower innerUpper 0).toFun y ^ 2 ≤
          (bombieriGiustiSpatialCutoff rho lower upper 0).toFun y ^ 2 := by
      simpa [bombieriGiustiSpatialCutoff] using hle
    rw [hzero, zero_pow (by norm_num : 2 ≠ 0)] at hle'
    exact hy (sq_eq_zero_iff.mp (le_antisymm hle' (sq_nonneg _)))
  have hlocal : v t x ≤ earlyFactor * earlyNorm := by
    simpa [earlyFactor, earlyNorm, n, bombieriGiustiSpatialCutoff] using
      (evolving_local_boundedness_of_subsolution_rpow_of_volume_le
        (I := I) (M := M) qMetric g hdim rho v hv hvpos V V hp₀
          hAearly hearly hearlyb hC hG hBlate houterSpatial hupperInner
          hinner hg hgram
          (fun s hs => hSobolev s ⟨hs.1, hs.2.trans hbD⟩)
          (fun s hs z => (hpde_v s ⟨hs.1, hs.2.trans hbD⟩ z).le)
          (fun s hs z => htraceLate s ⟨hs.1, hs.2.trans hbD⟩ z)
          (fun s hs z => hrho s ⟨hs.1, hs.2.trans hbD⟩ z)
          hVtop hVtop
          (fun s hs => (hvolume s ⟨hs.1, hs.2.trans hbD⟩).2)
          (fun s hs => (hvolume s ⟨hs.1, hs.2.trans hbD⟩).1)
          t ht x hx)
  have hweak : earlyNorm ≤ weakFactor * v q y := by
    simpa only [earlyNorm, weakFactor, c₀, n] using
      (localizedSpacetimeRpowNorm_le_canonicalEvolvingBombieriGiustiWeakHarnackBound_mul_of_supersolution
        (I := I) (M := M) qMetric g hdim rho outer averagingCutoff
          v hv hvpos Ccenter Ctail H W rate V hp₀ hp₀_one hAb hbτ
          hτc hcd hdD hC hG hBearly hBlate hCtail hrate hlowerUpper
          hg hgram haveragingCutoff hne hPcenter hPtail htraceAbs hmass_le
          hdrift_le hSobolev htraceEarly htraceLate hrho
          (fun s hs z => (hpde_v s hs z).ge)
          hVzero hVtop hvolume hearlyMeasure hearlyMeasure_le_one
          hlateMeasure hlateMeasure_le_one houter q hq y hyOuter)
  have htAD : t ∈ Icc A D := by
    exact ⟨hAearly.le.trans ht.1,
      ht.2.trans (hearlyb.le.trans hbD)⟩
  have hqAD : q ∈ Icc A D := by
    exact ⟨hAb.trans (hbτ.le.trans (hτc.le.trans hq.1)),
      hq.2.trans hdD.le⟩
  calc
    u t x = v t x := (hv_eq_u t htAD x).symm
    _ ≤ earlyFactor * earlyNorm := hlocal
    _ ≤ earlyFactor * (weakFactor * u q y) :=
      mul_le_mul_of_nonneg_left (by simpa [hv_eq_u q hqAD y] using hweak)
        hearlyFactor
    _ = evolvingSeparatedCylinderHarnackFactor
          n V C G Bearly Blate rate p₀ Ctail W A earlyLower earlyUpper b
            τ c d D lower upper innerLower innerUpper * u q y := by
      change earlyFactor * (weakFactor * u q y) =
        (earlyFactor * weakFactor) * u q y
      ring

end DifferentialGeometry.Analysis.Parabolic.Moser

end
