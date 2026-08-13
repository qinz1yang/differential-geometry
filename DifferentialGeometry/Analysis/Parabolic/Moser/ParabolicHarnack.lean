import DifferentialGeometry.Analysis.Parabolic.Moser.BombieriGiustiCrossover
import DifferentialGeometry.Analysis.Parabolic.Moser.SmallExponentLocalBoundedness
import DifferentialGeometry.Analysis.Integration.Measure.Invariance
import DifferentialGeometry.Analysis.Elliptic.Operator.SmoothDenseLp

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Moser

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Parabolic.Energy
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

def separatedCylinderHarnackFactor
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho averagingCutoff : SmoothScalar g)
    (C p A earlyLower earlyUpper b τ c lateLower lateUpper d D B
      lower upper innerLower innerUpper : ℝ) : ℝ :=
  moserPositiveExponentLocalBoundFactor (I := I) (M := M)
      g hdim rho p A earlyLower earlyUpper b innerLower innerUpper *
    moserPositiveExponentLocalBoundFactor (I := I) (M := M)
      g hdim rho p c lateLower lateUpper d innerLower innerUpper *
    canonicalBombieriGiustiCrossoverBound (I := I) (M := M)
      g hdim rho averagingCutoff C p A b τ c d D B lower upper

theorem separatedCylinderHarnackFactor_nonneg
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho averagingCutoff : SmoothScalar g)
    {C p A earlyLower earlyUpper b τ c lateLower lateUpper d D B
      lower upper innerLower innerUpper : ℝ} (hp : 0 < p) :
    0 ≤ separatedCylinderHarnackFactor (I := I) (M := M)
      g hdim rho averagingCutoff C p A earlyLower earlyUpper b τ c
        lateLower lateUpper d D B lower upper innerLower innerUpper := by
  unfold separatedCylinderHarnackFactor
  exact mul_nonneg
    (mul_nonneg
      (moserPositiveExponentLocalBoundFactor_nonneg
        g hdim rho hp)
      (moserPositiveExponentLocalBoundFactor_nonneg
        g hdim rho hp))
    (by unfold canonicalBombieriGiustiCrossoverBound; positivity)

theorem harnack_on_separated_cylinders
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho outer averagingCutoff : SmoothScalar g)
    (C : ℝ) (hC : 0 < C)
    (hP : HasLocalizedPoincareAtAverage (I := I) (M := M) g
      outer averagingCutoff C)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M ↦ u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p A earlyLower earlyUpper b τ c lateLower lateUpper d D B
      lower upper innerLower innerUpper : ℝ}
    (hp : 0 < p) (hp_one : p < 1)
    (hAearly : A < earlyLower) (hearly : earlyLower ≤ earlyUpper)
    (hearlyb : earlyUpper < b) (hbτ : b < τ)
    (hτc : τ < c) (hclate : c < lateLower)
    (hlate : lateLower ≤ lateUpper) (hlated : lateUpper < d)
    (hdD : d < D) (hB : 0 ≤ B)
    (hlowerUpper : lower < upper) (hupperInner : upper ≤ innerLower)
    (hinner : innerLower < innerUpper)
    (hrho : ∀ x : M,
      g.inner x
          (gradFun (I := I) g rho.toFun x)
          (gradFun (I := I) g rho.toFun x) ≤ B)
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
        outer.toFun x ^ 2)
    (hmass : 0 < cutoffMass (I := I) (M := M) averagingCutoff)
    (hpde : ∀ t ∈ Icc A D, ∀ x : M,
      deriv (fun q ↦ u q x) t =
        Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x) :
    ∀ t ∈ Icc earlyLower earlyUpper, ∀ x : M,
      (bombieriGiustiSpatialCutoff rho innerLower innerUpper 0).toFun x ≠ 0 →
      ∀ q ∈ Icc lateLower lateUpper, ∀ y : M,
        (bombieriGiustiSpatialCutoff rho innerLower innerUpper 0).toFun y ≠ 0 →
        u t x ≤
          separatedCylinderHarnackFactor (I := I) (M := M)
              g hdim rho averagingCutoff C p A earlyLower earlyUpper b τ c
                lateLower lateUpper d D B lower upper innerLower innerUpper *
            u q y := by
  let v : ℝ → M → ℝ := fun t x ↦ (u t x)⁻¹
  let earlyNorm := localizedSpacetimeRpowNorm (I := I) (M := M)
    (bombieriGiustiSpatialCutoff rho lower upper 0) u p A b
  let lateNorm := localizedSpacetimeRpowNorm (I := I) (M := M)
    (bombieriGiustiSpatialCutoff rho lower upper 0) v p c d
  let earlyFactor := moserPositiveExponentLocalBoundFactor (I := I) (M := M)
    g hdim rho p A earlyLower earlyUpper b innerLower innerUpper
  let lateFactor := moserPositiveExponentLocalBoundFactor (I := I) (M := M)
    g hdim rho p c lateLower lateUpper d innerLower innerUpper
  let crossoverBound := canonicalBombieriGiustiCrossoverBound (I := I) (M := M)
    g hdim rho averagingCutoff C p A b τ c d D B lower upper
  have houterSpatial :
      bombieriGiustiDescendingLevel lower upper 1 < upper := by
    simpa only [bombieriGiustiDescendingLevel_zero] using
      bombieriGiustiDescendingLevel_strictAnti hlowerUpper
        (Nat.zero_lt_succ 0)
  have hbD : b ≤ D :=
    hbτ.le.trans (hτc.le.trans (hclate.le.trans
      (hlate.trans (hlated.le.trans hdD.le))))
  have hAc : A ≤ c :=
    hAearly.le.trans (hearly.trans (hearlyb.le.trans (hbτ.le.trans hτc.le)))
  have hv : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M ↦ v z.1 z.2) := by
    simpa only [v, Real.rpow_neg_one] using
      contMDiff_rpow_of_pos hu hpos (-1 : ℝ)
  have hvpos : ∀ t x, 0 < v t x := fun t x ↦ inv_pos.mpr (hpos t x)
  have hvpde : ∀ t ∈ Icc c d, ∀ x : M,
      deriv (fun s ↦ v s x) t ≤
        Δ_g (I := I) g (smoothScalarSlice (I := I) g v hv t).toContMDiffMap x := by
    intro t ht x
    have h := rpow_subsolution_of_supersolution
      (I := I) (M := M) g u (fun _ _ ↦ 0) hu hpos
      (q := -1) (by norm_num) (t := t) (x := x)
      (by simpa using (hpde t ⟨hAc.trans ht.1, ht.2.trans hdD.le⟩ x).ge)
    simpa only [v, Real.rpow_neg_one, rpowSource, mul_zero, add_zero] using h
  have hnorm : earlyNorm * lateNorm ≤ crossoverBound := by
    simpa only [earlyNorm, lateNorm, v, crossoverBound] using
      localizedSpacetimeRpowNorm_mul_inv_le_canonicalBombieriGiustiCrossover_of_supersolution
        (I := I) (M := M) g hdim rho outer averagingCutoff C hC hP
          u hu hpos hp hp_one (hAearly.le.trans (hearly.trans hearlyb.le)) hbτ
          hτc (hclate.le.trans (hlate.trans hlated.le)) hdD hB hlowerUpper
          hrho hearlyMeasure hearlyMeasure_le_one hlateMeasure
          hlateMeasure_le_one houter hmass
          (fun t ht x ↦ (hpde t ht x).ge)
  have hearlyFactor : 0 ≤ earlyFactor := by
    exact moserPositiveExponentLocalBoundFactor_nonneg g hdim rho hp
  have hlateFactor : 0 ≤ lateFactor := by
    exact moserPositiveExponentLocalBoundFactor_nonneg g hdim rho hp
  have hearlyNorm : 0 ≤ earlyNorm := by
    exact localizedSpacetimeRpowNorm_nonneg _ u (fun t x ↦ (hpos t x).le) p A b
  intro t ht x hx q hq y hy
  have hlocalEarly : u t x ≤ earlyFactor * earlyNorm := by
    simpa [earlyFactor, earlyNorm, bombieriGiustiSpatialCutoff] using
      local_boundedness_of_subsolution_rpow
        (I := I) (M := M) g hdim rho u hu hpos hp hAearly hearly hearlyb
          houterSpatial hupperInner hinner
          (fun s hs z ↦ (hpde s ⟨hs.1, hs.2.trans hbD⟩ z).le)
          t ht x hx
  have hlocalLate : (u q y)⁻¹ ≤ lateFactor * lateNorm := by
    simpa [lateFactor, lateNorm, v, bombieriGiustiSpatialCutoff] using
      local_boundedness_of_subsolution_rpow
        (I := I) (M := M) g hdim rho v hv hvpos hp hclate hlate hlated
          houterSpatial hupperInner hinner hvpde q hq y hy
  have hpointProduct : u t x * (u q y)⁻¹ ≤
      (earlyFactor * earlyNorm) * (lateFactor * lateNorm) :=
    mul_le_mul hlocalEarly hlocalLate (inv_pos.mpr (hpos q y)).le
      (mul_nonneg hearlyFactor hearlyNorm)
  have hbound : u t x * (u q y)⁻¹ ≤
      earlyFactor * lateFactor * crossoverBound := by
    calc
      u t x * (u q y)⁻¹ ≤
          (earlyFactor * earlyNorm) * (lateFactor * lateNorm) := hpointProduct
      _ = (earlyFactor * lateFactor) * (earlyNorm * lateNorm) := by ring
      _ ≤ (earlyFactor * lateFactor) * crossoverBound :=
        mul_le_mul_of_nonneg_left hnorm (mul_nonneg hearlyFactor hlateFactor)
  calc
    u t x = (u t x * (u q y)⁻¹) * u q y := by
      field_simp [ne_of_gt (hpos q y)]
    _ ≤ (earlyFactor * lateFactor * crossoverBound) * u q y :=
      mul_le_mul_of_nonneg_right hbound (hpos q y).le
    _ = separatedCylinderHarnackFactor (I := I) (M := M)
          g hdim rho averagingCutoff C p A earlyLower earlyUpper b τ c
            lateLower lateUpper d D B lower upper innerLower innerUpper *
          u q y := by
      rfl

theorem harnack_on_separated_cylinders_of_global_volume_normalization
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho outer averagingCutoff : SmoothScalar g)
    (C : ℝ) (hC : 0 < C)
    (hP : HasLocalizedPoincareAtAverage (I := I) (M := M) g
      outer averagingCutoff C)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M ↦ u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {A α β b c γ δ d D : ℝ}
    (hAα : A < α) (hαβ : α < β) (hβb : β < b) (hbc : b < c)
    (hcγ : c < γ) (hγδ : γ < δ) (hδd : δ < d) (hdD : d < D)
    {p lower upper innerLower innerUpper B : ℝ}
    (hp : 0 < p) (hp_one : p < 1)
    (hlowerUpper : lower < upper) (hupperInner : upper ≤ innerLower)
    (hinner : innerLower < innerUpper)
    (hrhoLevels : ∀ x : M, innerUpper ≤ rho.toFun x)
    (hrho : ∀ x : M,
      g.inner x
          (gradFun (I := I) g rho.toFun x)
          (gradFun (I := I) g rho.toFun x) ≤ B)
    (hB : 0 ≤ B)
    (houter : ∀ x : M, 1 ≤ outer.toFun x)
    (hmass : 0 < cutoffMass (I := I) (M := M) averagingCutoff)
    (hcyl : 0 < (D - A) * (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
      (I := I) (M := M) g).real Set.univ ∧
      (D - A) * (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I)
        (M := M) g).real Set.univ ≤ 1)
    (hpde : ∀ t ∈ Icc A D, ∀ x : M,
      deriv (fun q ↦ u q x) t =
        Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x) :
    ∀ t ∈ Icc α β, ∀ x : M, ∀ q ∈ Icc γ δ, ∀ y : M,
      u t x ≤
        separatedCylinderHarnackFactor (I := I) (M := M)
            g hdim rho averagingCutoff C p A α β b ((b + c) / 2) c γ δ d D B
              lower upper innerLower innerUpper *
          u q y := by
  classical
  let τ : ℝ := (b + c) / 2
  have hτb : b < τ := by
    dsimp [τ]
    linarith
  have hτc : τ < c := by
    dsimp [τ]
    linarith
  have hvol_pos : 0 < (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I)
    (M := M) g).real Set.univ := by
    have hDA : 0 < D - A := by linarith
    exact pos_of_mul_pos_right hcyl.1 (le_of_lt hDA)
  have hvol_nonneg : 0 ≤ (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I)
    (M := M) g).real Set.univ :=
    le_of_lt hvol_pos
  have hcutoff_one : ∀ (k : ℕ) (x : M),
      (bombieriGiustiSpatialCutoff rho lower upper k).toFun x = 1 := by
    intro k x
    unfold bombieriGiustiSpatialCutoff
    exact spatialCutoffBetween_eq_one_of_outer_le
      (bombieriGiustiDescendingLevel_strictAnti hlowerUpper (by omega)) (by
        calc
          bombieriGiustiDescendingLevel lower upper (2 * k) ≤ upper :=
            bombieriGiustiDescendingLevel_le hlowerUpper _
          _ ≤ innerLower := hupperInner
          _ ≤ rho.toFun x := le_trans (le_of_lt hinner) (hrhoLevels x))
  have hcutoffMass : ∀ (k : ℕ),
      cutoffMass (I := I) (M := M) (bombieriGiustiSpatialCutoff rho lower upper k) =
        (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I)
          (M := M) g).real Set.univ := by
    intro k
    unfold cutoffMass
    have hfun : (fun x : M => (bombieriGiustiSpatialCutoff rho lower upper k).toFun x ^ 2) =
        (fun _ : M => (1 : ℝ)) := by
      funext x
      rw [hcutoff_one k x]
      norm_num
    rw [hfun]
    simp
  have hcutoffMass_ne : ∀ (k : ℕ),
      cutoffMass (I := I) (M := M) (bombieriGiustiSpatialCutoff rho lower upper k) ≠ 0 := by
    intro k
    rw [hcutoffMass k]
    exact ne_of_gt hvol_pos
  have houter_engine : ∀ (k : ℕ) (x : M),
      (bombieriGiustiSpatialCutoff rho lower upper k).toFun x ^ 2 ≤ outer.toFun x ^ 2 := by
    intro k x
    rw [hcutoff_one k x]
    simpa [pow_two] using mul_le_mul (houter x) (houter x) zero_le_one
      (le_trans zero_le_one (houter x))
  have hA_increasing : ∀ (k : ℕ),
      A < bombieriGiustiIncreasingLevel b τ k := by
    intro k
    have hinc_ge : b ≤ bombieriGiustiIncreasingLevel b τ k :=
      bombieriGiustiIncreasingLevel_ge hτb k
    linarith
  have hinc_lt_D : ∀ (k : ℕ), bombieriGiustiIncreasingLevel b τ k < D := by
    intro k
    have hinc : bombieriGiustiIncreasingLevel b τ k < τ :=
      bombieriGiustiIncreasingLevel_lt hτb k
    linarith
  have hearlyMeasure : ∀ (k : ℕ),
      localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k) A
          (bombieriGiustiIncreasingLevel b τ k) ≠ 0 := by
    intro k
    exact localizedSpacetimeMeasure_ne_zero_of
      (bombieriGiustiSpatialCutoff rho lower upper k) (hA_increasing k) (hcutoffMass_ne k)
  have hearlyMeasure_le_one : ∀ (k : ℕ),
      (localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k) A
          (bombieriGiustiIncreasingLevel b τ k)).real Set.univ ≤ 1 := by
    intro k
    apply localizedSpacetimeMeasure_le_one_of
    · exact le_of_lt (hA_increasing k)
    · have hinc_le_D : bombieriGiustiIncreasingLevel b τ k ≤ D := le_of_lt (hinc_lt_D k)
      have hmul_le : (bombieriGiustiIncreasingLevel b τ k - A) *
            (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I)
              (M := M) g).real Set.univ ≤
          (D - A) * (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I)
            (M := M) g).real Set.univ := by
        exact mul_le_mul_of_nonneg_right (sub_le_sub_right hinc_le_D A) hvol_nonneg
      rw [hcutoffMass k]
      exact le_trans hmul_le hcyl.2
  have hdesc_gt_A : ∀ (k : ℕ), A < bombieriGiustiDescendingLevel τ c k := by
    intro k
    have hdesc_gt : τ < bombieriGiustiDescendingLevel τ c k :=
      bombieriGiustiDescendingLevel_gt hτc k
    linarith
  have hdesc_lt_inc : ∀ (k : ℕ),
      bombieriGiustiDescendingLevel τ c k < bombieriGiustiIncreasingLevel d D k := by
    intro k
    have hdesc_le_c : bombieriGiustiDescendingLevel τ c k ≤ c :=
      bombieriGiustiDescendingLevel_le hτc k
    have hinc_ge_d : d ≤ bombieriGiustiIncreasingLevel d D k :=
      bombieriGiustiIncreasingLevel_ge hdD k
    linarith
  have hinc_d_lt_D : ∀ (k : ℕ), bombieriGiustiIncreasingLevel d D k < D := by
    intro k
    exact bombieriGiustiIncreasingLevel_lt hdD k
  have hlateMeasure : ∀ (k : ℕ),
      localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k)
          (bombieriGiustiDescendingLevel τ c k)
          (bombieriGiustiIncreasingLevel d D k) ≠ 0 := by
    intro k
    exact localizedSpacetimeMeasure_ne_zero_of
      (bombieriGiustiSpatialCutoff rho lower upper k) (hdesc_lt_inc k) (hcutoffMass_ne k)
  have hlateMeasure_le_one : ∀ (k : ℕ),
      (localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k)
          (bombieriGiustiDescendingLevel τ c k)
          (bombieriGiustiIncreasingLevel d D k)).real Set.univ ≤ 1 := by
    intro k
    apply localizedSpacetimeMeasure_le_one_of
    · exact le_of_lt (hdesc_lt_inc k)
    · have hlen : bombieriGiustiIncreasingLevel d D k -
      bombieriGiustiDescendingLevel τ c k ≤ D - A := by
        linarith [hinc_d_lt_D k, hdesc_gt_A k]
      have hmul_le : (bombieriGiustiIncreasingLevel d D k - bombieriGiustiDescendingLevel τ c k) *
            (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I)
              (M := M) g).real Set.univ ≤
          (D - A) * (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I)
            (M := M) g).real Set.univ := by
        exact mul_le_mul_of_nonneg_right hlen hvol_nonneg
      rw [hcutoffMass k]
      exact le_trans hmul_le hcyl.2
  have hcutoff_target_one : ∀ (x : M),
      (bombieriGiustiSpatialCutoff rho innerLower innerUpper 0).toFun x = 1 := by
    intro x
    unfold bombieriGiustiSpatialCutoff
    exact spatialCutoffBetween_eq_one_of_outer_le
      (bombieriGiustiDescendingLevel_strictAnti hinner (by norm_num)) (by
        calc
          bombieriGiustiDescendingLevel innerLower innerUpper 0 ≤ innerUpper := by simp
          _ ≤ rho.toFun x := hrhoLevels x)
  intro t ht x q hq y
  have h := harnack_on_separated_cylinders (I := I) (M := M) g hdim rho outer averagingCutoff
    C hC hP u hu hpos hp hp_one hAα (le_of_lt hαβ) hβb hτb hτc hcγ (le_of_lt hγδ)
    hδd hdD hB hlowerUpper hupperInner hinner hrho hearlyMeasure hearlyMeasure_le_one
    hlateMeasure hlateMeasure_le_one houter_engine hmass (fun t ht x => hpde t ht x)
  exact h t ht x (by rw [hcutoff_target_one x]; norm_num) q hq y
    (by rw [hcutoff_target_one y]; norm_num)

theorem harnack_on_standard_separated_cylinders_of_global_volume_normalization
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho outer averagingCutoff : SmoothScalar g)
    (C : ℝ) (hC : 0 < C)
    (hP : HasLocalizedPoincareAtAverage (I := I) (M := M) g
      outer averagingCutoff C)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M ↦ u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {A D : ℝ} (hAD : A < D)
    {B : ℝ} (hB : 0 ≤ B)
    (hrho : ∀ x : M, 1 ≤ rho.toFun x)
    (hrhoGrad : ∀ x : M,
      g.inner x
          (gradFun (I := I) g rho.toFun x)
          (gradFun (I := I) g rho.toFun x) ≤ B)
    (houter : ∀ x : M, 1 ≤ outer.toFun x)
    (hmass : 0 < cutoffMass (I := I) (M := M) averagingCutoff)
    (hcyl : 0 < (D - A) * (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
      (I := I) (M := M) g).real Set.univ ∧
      (D - A) * (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I)
        (M := M) g).real Set.univ ≤ 1)
    (hpde : ∀ t ∈ Icc A D, ∀ x : M,
      deriv (fun q ↦ u q x) t =
        Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x) :
    ∀ t ∈ Icc (A + (D - A) / 8) (A + (D - A) / 4), ∀ x : M,
      ∀ q ∈ Icc (A + 3 * (D - A) / 4) (A + 7 * (D - A) / 8), ∀ y : M,
        u t x ≤
          separatedCylinderHarnackFactor (I := I) (M := M)
              g hdim rho averagingCutoff C (1 / 2)
                A (A + (D - A) / 8) (A + (D - A) / 4) (A + 3 * (D - A) / 8)
                ((A + 3 * (D - A) / 8 + (A + 5 * (D - A) / 8)) / 2)
                (A + 5 * (D - A) / 8) (A + 3 * (D - A) / 4) (A + 7 * (D - A) / 8)
                (A + 15 * (D - A) / 16) D B 0 (1 / 4) (1 / 2) 1 *
            u q y := by
  classical
  let α : ℝ := A + (D - A) / 8
  let β : ℝ := A + (D - A) / 4
  let b : ℝ := A + 3 * (D - A) / 8
  let c : ℝ := A + 5 * (D - A) / 8
  let γ : ℝ := A + 3 * (D - A) / 4
  let δ : ℝ := A + 7 * (D - A) / 8
  let d : ℝ := A + 15 * (D - A) / 16
  have hAα : A < α := by
    dsimp [α]
    linarith
  have hαβ : α < β := by
    dsimp [α, β]
    linarith
  have hβb : β < b := by
    dsimp [β, b]
    linarith
  have hbc : b < c := by
    dsimp [b, c]
    linarith
  have hcγ : c < γ := by
    dsimp [c, γ]
    linarith
  have hγδ : γ < δ := by
    dsimp [γ, δ]
    linarith
  have hδd : δ < d := by
    dsimp [δ, d]
    linarith
  have hdD : d < D := by
    dsimp [d]
    linarith
  simpa [α, β, b, c, γ, δ, d] using
    harnack_on_separated_cylinders_of_global_volume_normalization
      (I := I) (M := M) g hdim rho outer averagingCutoff C hC hP u hu hpos
      (A := A) (α := α) (β := β) (b := b) (c := c) (γ := γ) (δ := δ) (d := d) (D := D)
      (p := (1 / 2 : ℝ)) (lower := (0 : ℝ)) (upper := (1 / 4 : ℝ))
      (innerLower := (1 / 2 : ℝ)) (innerUpper := (1 : ℝ)) (B := B)
      hAα hαβ hβb hbc hcγ hγδ hδd hdD
      (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < (1 / 4 : ℝ))
      (by norm_num : (1 / 4 : ℝ) ≤ (1 / 2 : ℝ))
      (by norm_num : (1 / 2 : ℝ) < 1)
      hrho hrhoGrad hB houter hmass hcyl hpde

theorem harnack_on_standard_separated_cylinders_of_poincare_inequality
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (C : ℝ) (hC : 0 < C)
    (hP : HasLocalizedPoincareAtAverage (I := I) (M := M) g
      (SmoothScalar.one g) (SmoothScalar.one g) C)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M ↦ u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {A D : ℝ} (hAD : A < D)
    (hvol : 0 < (D - A) * (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
      (I := I) (M := M) g).real Set.univ ∧
      (D - A) * (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I)
        (M := M) g).real Set.univ ≤ 1)
    (hpde : ∀ t ∈ Icc A D, ∀ x : M,
      deriv (fun q ↦ u q x) t =
        Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x) :
    ∀ t ∈ Icc (A + (D - A) / 8) (A + (D - A) / 4), ∀ x : M,
      ∀ q ∈ Icc (A + 3 * (D - A) / 4) (A + 7 * (D - A) / 8), ∀ y : M,
        u t x ≤
          separatedCylinderHarnackFactor (I := I) (M := M)
              g hdim (SmoothScalar.one g) (SmoothScalar.one g) C (1 / 2)
                A (A + (D - A) / 8) (A + (D - A) / 4) (A + 3 * (D - A) / 8)
                ((A + 3 * (D - A) / 8 + (A + 5 * (D - A) / 8)) / 2)
                (A + 5 * (D - A) / 8) (A + 3 * (D - A) / 4) (A + 7 * (D - A) / 8)
                (A + 15 * (D - A) / 16) D 0 0 (1 / 4) (1 / 2) 1 *
            u q y := by
  classical
  have hgrad_one : ∀ x : M, gradFun (I := I) g (SmoothScalar.one g).toFun x = 0 := by
    intro x
    unfold gradFun
    rw [SmoothScalar.one_toFun]
    rw [mfderiv_const]
    simp
    rfl
  have hrhoGrad : ∀ x : M,
      g.inner x (gradFun (I := I) g (SmoothScalar.one g).toFun x)
        (gradFun (I := I) g (SmoothScalar.one g).toFun x) ≤ 0 := by
    intro x
    rw [hgrad_one x]
    simp
  have hcutoffMass_one : cutoffMass (I := I) (M := M) (SmoothScalar.one g) =
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I)
        (M := M) g).real Set.univ := by
    simp [cutoffMass, SmoothScalar.one]
  have hmass : 0 < cutoffMass (I := I) (M := M) (SmoothScalar.one g) := by
    rw [hcutoffMass_one]
    have hDA : 0 < D - A := sub_pos.mpr hAD
    exact pos_of_mul_pos_right hvol.1 (le_of_lt hDA)
  simpa using
    harnack_on_standard_separated_cylinders_of_global_volume_normalization
      (I := I) (M := M) g hdim (SmoothScalar.one g) (SmoothScalar.one g) (SmoothScalar.one g)
      C hC hP u hu hpos (B := (0 : ℝ)) hAD
      (by norm_num : 0 ≤ (0 : ℝ))
      (by intro x; simp) hrhoGrad (by intro x; simp) hmass hvol hpde

end DifferentialGeometry.Analysis.Parabolic.Moser

end
