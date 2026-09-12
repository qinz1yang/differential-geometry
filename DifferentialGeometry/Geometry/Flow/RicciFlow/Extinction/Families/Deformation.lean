import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.GoodWindows
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.GapComparison



noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open Surgery.Topology Width CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    [SigmaCompactSpace Q] [hT2 : T2Space Q] [hCompact : CompactSpace Q]
    [hConnected : ConnectedSpace Q] [hBoundary : I.Boundaryless]
    {D : RealTimeInterval} {a b : ℝ}

include hT2 hCompact hConnected hBoundary

theorem rfs_uniform_ramp_alternative (B : RicciBackground (I := I) (M := Q) D a b)
    (hdim : Module.finrank ℝ E = 3)
    (L₀ Theta₀ Ainit : ℝ) (hL₀ : 0 ≤ L₀) (hTheta₀ : 0 ≤ Theta₀) (hAinit : 0 ≤ Ainit)
    (ell epsilon : ℝ) (hell : 0 < ell) (hepsilon : 0 < epsilon) :
    ∃ lambda₀ : ℝ, 0 < lambda₀ ∧ lambda₀ ≤ 1 ∧
      ∀ lambda : ℝ, 0 < lambda → lambda ≤ lambda₀ → ∀ c : ProductCurve Q,
        c.IsSolutionOn B.family.metric lambda (Icc a b) →
        c.IsRampOn B.family.metric lambda (Icc a b) → c.degree = 1 →
        ∀ γ : ℝ → ContinuousFreeLoop Q,
          (∀ t ∈ Icc a b, ∀ z, γ t z = c.projection z t) →
          (∀ t ∈ Icc a b, IsContractibleLoop (γ t)) →
          c.length B.family.metric lambda a ≤ L₀ →
          c.totalCurvature B.family.metric lambda a ≤ Theta₀ →
          loopFamilyLeastArea B.family.metric γ a ≤ Ainit →
          loopLength (B.family.metric b) (γ b) < ell ∨
            loopFamilyLeastArea B.family.metric γ b ≤
              affineComparison B.family a b (loopFamilyLeastArea B.family.metric γ a) + epsilon := by
  sorry

theorem rfs_family_deformation (B : RicciBackground (I := I) (M := Q) D a b)
    (hdim : Module.finrank ℝ E = 3) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2))
    (epsilon ell : ℝ) (hepsilon : 0 < epsilon) (hell : 0 < ell) :
    ∃ lambda : ℝ, 0 < lambda ∧ lambda ≤ 1 ∧
      ∃ solutions : Sphere 2 → ProductCurve Q,
        ∃ deformed : C(Icc a b, RegularFamily (I := I) (Q := Q) (Sphere 2)),
          @Continuous (Sphere 2) (ProductCurve Q) inferInstance
            (smoothProductCylinderTopology e (Icc a b)) solutions ∧
          (∀ p, (solutions p).IsSolutionOn B.family.metric lambda (Icc a b) ∧
            (solutions p).IsRampOn B.family.metric lambda (Icc a b) ∧ (solutions p).degree = 1) ∧
          (∀ t : Icc a b, ∀ p z,
            ((deformed t) p).1 z = (solutions p).projection z t) ∧
          (∀ t : Icc a b, HasContinuousSmoothLoopJets e (deformed t) ∧
            FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp (deformed t)) =
              FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp Γ)) ∧
          (∀ p, |regularLeastArea (B.family.metric a) ((deformed ⟨a, le_rfl, B.lt.le⟩) p) -
            regularLeastArea (B.family.metric a) (Γ p)| < epsilon) ∧
          ∀ p,
            loopLength (B.family.metric b)
              (((deformed ⟨b, B.lt.le, le_rfl⟩) p).1.toContinuousLoop) < ell ∨
            regularLeastArea (B.family.metric b) ((deformed ⟨b, B.lt.le, le_rfl⟩) p) ≤
              affineComparison B.family a b (regularLeastArea (B.family.metric a) (Γ p)) + epsilon := by
  sorry

omit [CompleteSpace E] [SigmaCompactSpace Q] hCompact hConnected hBoundary in
omit [TopologicalSpace Q] hT2 in
theorem gap_interval_union_eq (starts : Finset ℝ) (d : ℝ) :
    {t : ℝ | ∃ uv ∈ starts.image (fun w => (w + 5 * d / 8, w + 7 * d / 8)),
      t ∈ Icc uv.1 uv.2} = goodWindowUnion starts d := by
  ext t
  constructor
  · rintro ⟨uv, huv, ht⟩
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp huv
    exact ⟨w, hw, ht⟩
  · rintro ⟨w, hw, ht⟩
    exact ⟨(w + 5 * d / 8, w + 7 * d / 8),
      Finset.mem_image.mpr ⟨w, hw, rfl⟩, ht⟩

omit [SigmaCompactSpace Q] hBoundary in
theorem rfs_uniform_ramp_alternative_of_window_data
    (B : RicciBackground (I := I) (M := Q) D a b)
    (L₀ Theta₀ Ainit : ℝ) (hL₀ : 0 ≤ L₀) (hTheta₀ : 0 ≤ Theta₀)
    (Abar Cup eta threshold : ℝ) (hAbar : 0 ≤ Abar) (hCup : 0 ≤ Cup)
    (hthreshold : 0 < threshold) (heta : 0 < eta)
    (ell l epsilon : ℝ) (hlpos : 0 < l)
    (delta r₀ : ℝ) (hdelta : 0 < delta) (hr₀ : 0 < r₀)
    (r d : ℝ) (hr : r = min r₀ (min (l / 2) (delta ^ 2 / threshold)))
    (hd : d = delta * r ^ 2)
    (lambda₀ : ℝ) (ThetaBar : ℝ) (hThetaBar : 0 ≤ ThetaBar)
    (hlength : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ lambda₀ → ∀ c : ProductCurve Q,
      c.IsSolutionOn B.family.metric lambda (Icc a b) →
      c.IsRampOn B.family.metric lambda (Icc a b) → c.degree = 1 →
      c.length B.family.metric lambda a ≤ L₀ →
      c.totalCurvature B.family.metric lambda a ≤ Theta₀ →
      ∀ γ : ℝ → ContinuousFreeLoop Q, (∀ z, γ b z = c.projection z b) →
      ell ≤ loopLength (B.family.metric b) (γ b) →
      ∀ t ∈ Icc a b, l ≤ c.length B.family.metric lambda t)
    (hwindows : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ lambda₀ → ∀ c : ProductCurve Q,
      c.IsSolutionOn B.family.metric lambda (Icc a b) →
      c.IsRampOn B.family.metric lambda (Icc a b) → c.degree = 1 →
      c.length B.family.metric lambda a ≤ L₀ →
      c.totalCurvature B.family.metric lambda a ≤ Theta₀ →
      (∀ t ∈ Icc a b, l ≤ c.length B.family.metric lambda t) →
      ∃ starts : Finset ℝ,
        goodWindowUnion starts d ⊆ Ioo a b ∧
        volume (Icc a b \ goodWindowUnion starts d) ≤
          ENNReal.ofReal (d + Real.exp (B.B₀ * (b - a)) * L₀ / threshold) ∧
        ∀ x t, t ∈ goodWindowUnion starts d →
          0 < c.angle B.family.metric lambda x t ∧
          c.angle B.family.metric lambda x t ≤ eta)
    (hcontinuous : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ lambda₀ → ∀ c : ProductCurve Q,
      c.IsSolutionOn B.family.metric lambda (Icc a b) →
      c.IsRampOn B.family.metric lambda (Icc a b) → c.degree = 1 →
      c.length B.family.metric lambda a ≤ L₀ →
      c.totalCurvature B.family.metric lambda a ≤ Theta₀ →
      ∀ γ : ℝ → ContinuousFreeLoop Q, (∀ t ∈ Icc a b, ∀ z, γ t z = c.projection z t) →
      (∀ t ∈ Icc a b, IsContractibleLoop (γ t)) →
      loopFamilyLeastArea B.family.metric γ a ≤ Ainit →
      ContinuousOn (loopFamilyLeastArea B.family.metric γ) (Icc a b) ∧
      (∀ t ∈ Icc a b, 0 ≤ loopFamilyLeastArea B.family.metric γ t ∧
        loopFamilyLeastArea B.family.metric γ t ≤ Abar) ∧
      (∀ s ∈ Icc a b, ∀ t ∈ Icc s b,
        loopFamilyLeastArea B.family.metric γ t - loopFamilyLeastArea B.family.metric γ s ≤
          Cup * (t - s)))
    (hDini : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ lambda₀ → ∀ c : ProductCurve Q,
      c.IsSolutionOn B.family.metric lambda (Icc a b) →
      c.IsRampOn B.family.metric lambda (Icc a b) → c.degree = 1 →
      c.length B.family.metric lambda a ≤ L₀ →
      c.totalCurvature B.family.metric lambda a ≤ Theta₀ →
      ∀ γ : ℝ → ContinuousFreeLoop Q, (∀ t ∈ Icc a b, ∀ z, γ t z = c.projection z t) →
      (∀ t ∈ Icc a b, IsContractibleLoop (γ t)) →
      loopFamilyLeastArea B.family.metric γ a ≤ Ainit →
      ∀ starts : Finset ℝ,
        (∀ x t, t ∈ goodWindowUnion starts d →
          0 < c.angle B.family.metric lambda x t ∧ c.angle B.family.metric lambda x t ≤ eta) →
      ∀ t ∈ Ico a b, t ∈ goodWindowUnion starts d → ∀ eps > 0, ∃ dd > 0,
        ∀ h ∈ Ioo (0 : ℝ) dd, t + h ≤ b →
          (loopFamilyLeastArea B.family.metric γ (t + h) -
              loopFamilyLeastArea B.family.metric γ t) / h ≤
            -2 * Real.pi - halfScalarMinimum B.family t * loopFamilyLeastArea B.family.metric γ t +
              eta ^ 2 / Real.sqrt (1 - eta ^ 2) * ThetaBar + eps)
    (herror : Real.exp (2 * scalarComparisonBound B.family a b * (b - a)) *
      (eta ^ 2 / Real.sqrt (1 - eta ^ 2) * ThetaBar * (b - a) +
        (Cup + scalarComparisonBound B.family a b * Abar + 2 * Real.pi) *
          (d + Real.exp (B.B₀ * (b - a)) * L₀ / threshold)) ≤ epsilon) :
    ∀ lambda : ℝ, 0 < lambda → lambda ≤ lambda₀ → ∀ c : ProductCurve Q,
      c.IsSolutionOn B.family.metric lambda (Icc a b) →
      c.IsRampOn B.family.metric lambda (Icc a b) → c.degree = 1 →
      ∀ γ : ℝ → ContinuousFreeLoop Q,
        (∀ t ∈ Icc a b, ∀ z, γ t z = c.projection z t) →
        (∀ t ∈ Icc a b, IsContractibleLoop (γ t)) →
        c.length B.family.metric lambda a ≤ L₀ →
        c.totalCurvature B.family.metric lambda a ≤ Theta₀ →
        loopFamilyLeastArea B.family.metric γ a ≤ Ainit →
        loopLength (B.family.metric b) (γ b) < ell ∨
          loopFamilyLeastArea B.family.metric γ b ≤
            affineComparison B.family a b (loopFamilyLeastArea B.family.metric γ a) + epsilon := by
  intro lambda hlambda hlambda_one c hsol hramp hdeg γ hγ hctr hlen0 hcurv0 hAinit
  let _ := hL₀
  let _ := hTheta₀
  let _ := heta
  by_cases hshort : loopLength (B.family.metric b) (γ b) < ell
  · exact Or.inl hshort
  right
  have hleb : ell ≤ loopLength (B.family.metric b) (γ b) := le_of_not_gt hshort
  have hrpos : 0 < r := by
    rw [hr]
    exact lt_min hr₀ (lt_min (by linarith) (div_pos (pow_pos hdelta 2) hthreshold))
  have hdpos : 0 < d := by rw [hd]; exact mul_pos hdelta (pow_pos hrpos 2)
  have hlenall : ∀ t ∈ Icc a b, l ≤ c.length B.family.metric lambda t :=
    hlength lambda hlambda hlambda_one c hsol hramp hdeg hlen0 hcurv0
      γ (fun z => hγ b ⟨B.lt.le, le_rfl⟩ z) hleb
  obtain ⟨starts, hwsub, hwvol, hwangle⟩ :=
    hwindows lambda hlambda hlambda_one c hsol hramp hdeg hlen0 hcurv0 hlenall
  obtain ⟨hcont, hrange, hup⟩ :=
    hcontinuous lambda hlambda hlambda_one c hsol hramp hdeg hlen0 hcurv0
      γ hγ hctr hAinit
  set mu := d + Real.exp (B.B₀ * (b - a)) * L₀ / threshold with hmu
  set err := eta ^ 2 / Real.sqrt (1 - eta ^ 2) * ThetaBar with herr
  have hmu_nn : 0 ≤ mu := by
    rw [hmu]; positivity
  have herr_nn : 0 ≤ err := by
    rw [herr]
    exact mul_nonneg (div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)) hThetaBar
  have hgap : volume (Icc a b \ {t : ℝ | ∃ uv ∈ starts.image
      (fun w => (w + 5 * d / 8, w + 7 * d / 8)), t ∈ Icc uv.1 uv.2}) ≤
      ENNReal.ofReal mu := by
    rw [gap_interval_union_eq starts d, hmu]
    exact hwvol
  have hDini' : ∀ uv ∈ starts.image (fun w => (w + 5 * d / 8, w + 7 * d / 8)),
      ∀ v ∈ Ico uv.1 uv.2, ∀ epsilon > 0, ∃ delta > 0,
        ∀ h ∈ Ioo (0 : ℝ) delta, v + h ≤ uv.2 →
          (loopFamilyLeastArea B.family.metric γ (v + h) -
              loopFamilyLeastArea B.family.metric γ v) / h ≤
            -2 * Real.pi - halfScalarMinimum B.family v * loopFamilyLeastArea B.family.metric γ v +
              err + epsilon := by
    intro uv huv v hv eps heps
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp huv
    have hmem : v ∈ goodWindowUnion starts d := ⟨w, hw, ⟨hv.1, hv.2.le⟩⟩
    have hvI : v ∈ Ico a b :=
      ⟨le_trans (hwsub ⟨w, hw, ⟨le_refl _, by linarith [hdpos]⟩⟩).1.le hv.1,
        lt_trans hv.2 (hwsub ⟨w, hw, ⟨by linarith [hdpos], le_refl _⟩⟩).2⟩
    obtain ⟨dd, hdd, hdd'⟩ :=
      hDini lambda hlambda hlambda_one c hsol hramp hdeg hlen0 hcurv0
        γ hγ hctr hAinit starts hwangle v hvI hmem eps heps
    exact ⟨dd, hdd, fun h hh hvu => by
      have hb' : v + h ≤ b :=
        le_trans hvu (hwsub ⟨w, hw, ⟨by linarith [hdpos], le_refl _⟩⟩).2.le
      exact hdd' h hh hb'⟩
  have hmain := rfs_width_gap_comparison B (loopFamilyLeastArea B.family.metric γ) Abar Cup mu err
    hAbar hCup hmu_nn herr_nn hcont hrange hup
    (starts.image (fun w => (w + 5 * d / 8, w + 7 * d / 8)))
    (by
      intro uv huv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp huv
      have h1 : a < w + 5 * d / 8 :=
        (hwsub ⟨w, hw, ⟨le_refl _, by linarith [hdpos]⟩⟩).1
      have h2 : w + 7 * d / 8 < b :=
        (hwsub ⟨w, hw, ⟨by linarith [hdpos], le_refl _⟩⟩).2
      exact ⟨h1, by linarith [hdpos], h2⟩)
    hgap hDini'
  linarith [hmain, herror]

omit [SigmaCompactSpace Q] hBoundary in
theorem rfs_family_deformation_of_prepared_flow
    (B : RicciBackground (I := I) (M := Q) D a b) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2))
    (epsilon ell : ℝ) (hepsilon : 0 < epsilon)
    (L₀ Theta₀ Ainit : ℝ) (hL₀ : 0 ≤ L₀) (hTheta₀ : 0 ≤ Theta₀) (hAinit : 0 ≤ Ainit)
    (hprepared : ∀ (eta : ℝ), 0 < eta →
      ∃ prepared : RegularFamily (I := I) (Q := Q) (Sphere 2),
        HasContinuousSmoothLoopJets e prepared ∧
        ContinuousMap.Homotopic prepared Γ ∧
        (∀ p, |regularLeastArea (B.family.metric a) (prepared p) -
          regularLeastArea (B.family.metric a) (Γ p)| < eta) ∧
        ∀ p (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
          (initialRamp (prepared p).1).SmoothOn (I := I) univ ∧
          (initialRamp (prepared p).1).IsRampOn (fun _ => B.family.metric a) lambda univ ∧
          (initialRamp (prepared p).1).length (fun _ => B.family.metric a) lambda 0 ≤ L₀ ∧
          (initialRamp (prepared p).1).totalCurvature (fun _ => B.family.metric a) lambda 0 ≤ Theta₀ ∧
          regularLeastArea (B.family.metric a) (prepared p) ≤ Ainit)
    (hflow : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
      ∀ (prepared : RegularFamily (I := I) (Q := Q) (Sphere 2)),
        HasContinuousSmoothLoopJets e prepared →
      ∃ solutions : Sphere 2 → ProductCurve Q,
        ∃ projected : C(Icc a b, RegularFamily (I := I) (Q := Q) (Sphere 2)),
          @Continuous (Sphere 2) (ProductCurve Q) inferInstance
            (smoothProductCylinderTopology e (Icc a b)) solutions ∧
          (∀ p, (solutions p).IsSolutionOn B.family.metric lambda (Icc a b) ∧
            (solutions p).IsRampOn B.family.metric lambda (Icc a b) ∧ (solutions p).degree = 1) ∧
          (∀ t : Icc a b, ∀ p z,
            ((projected t) p).1 z = (solutions p).projection z t) ∧
          projected ⟨a, le_rfl, B.lt.le⟩ = prepared ∧
          (∀ t : Icc a b, HasContinuousSmoothLoopJets e (projected t)) ∧
          (∀ t : Icc a b,
            FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp (projected t)) =
              FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp prepared)) ∧
          (∀ p, (solutions p).length B.family.metric lambda a ≤ L₀ ∧
            (solutions p).totalCurvature B.family.metric lambda a ≤ Theta₀))
    (halt : ∀ (L Theta A : ℝ), 0 ≤ L → 0 ≤ Theta → 0 ≤ A →
      ∃ lambda₀ : ℝ, 0 < lambda₀ ∧ lambda₀ ≤ 1 ∧
        ∀ lambda : ℝ, 0 < lambda → lambda ≤ lambda₀ → ∀ c : ProductCurve Q,
          c.IsSolutionOn B.family.metric lambda (Icc a b) →
          c.IsRampOn B.family.metric lambda (Icc a b) → c.degree = 1 →
          ∀ γ : ℝ → ContinuousFreeLoop Q,
            (∀ t ∈ Icc a b, ∀ z, γ t z = c.projection z t) →
            (∀ t ∈ Icc a b, IsContractibleLoop (γ t)) →
            c.length B.family.metric lambda a ≤ L →
            c.totalCurvature B.family.metric lambda a ≤ Theta →
            loopFamilyLeastArea B.family.metric γ a ≤ A →
            loopLength (B.family.metric b) (γ b) < ell ∨
              loopFamilyLeastArea B.family.metric γ b ≤
                affineComparison B.family a b (loopFamilyLeastArea B.family.metric γ a) +
                  epsilon / 2) :
    ∃ lambda : ℝ, 0 < lambda ∧ lambda ≤ 1 ∧
      ∃ solutions : Sphere 2 → ProductCurve Q,
        ∃ deformed : C(Icc a b, RegularFamily (I := I) (Q := Q) (Sphere 2)),
          @Continuous (Sphere 2) (ProductCurve Q) inferInstance
            (smoothProductCylinderTopology e (Icc a b)) solutions ∧
          (∀ p, (solutions p).IsSolutionOn B.family.metric lambda (Icc a b) ∧
            (solutions p).IsRampOn B.family.metric lambda (Icc a b) ∧ (solutions p).degree = 1) ∧
          (∀ t : Icc a b, ∀ p z,
            ((deformed t) p).1 z = (solutions p).projection z t) ∧
          (∀ t : Icc a b, HasContinuousSmoothLoopJets e (deformed t) ∧
            FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp (deformed t)) =
              FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp Γ)) ∧
          (∀ p, |regularLeastArea (B.family.metric a) ((deformed ⟨a, le_rfl, B.lt.le⟩) p) -
            regularLeastArea (B.family.metric a) (Γ p)| < epsilon) ∧
          ∀ p,
            loopLength (B.family.metric b)
              (((deformed ⟨b, B.lt.le, le_rfl⟩) p).1.toContinuousLoop) < ell ∨
            regularLeastArea (B.family.metric b) ((deformed ⟨b, B.lt.le, le_rfl⟩) p) ≤
              affineComparison B.family a b (regularLeastArea (B.family.metric a) (Γ p)) + epsilon := by
  have hMnn : 0 ≤ scalarComparisonBound B.family a b := (rfs_width_flow_background B).2.2.1
  set eta := epsilon / 2 * Real.exp (-(scalarComparisonBound B.family a b * (b - a))) with heta
  have heta_pos : 0 < eta := by rw [heta]; positivity
  have hexp : Real.exp (scalarComparisonBound B.family a b * (b - a)) * eta = epsilon / 2 := by
    have h1 : Real.exp (scalarComparisonBound B.family a b * (b - a)) *
        Real.exp (-(scalarComparisonBound B.family a b * (b - a))) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    rw [heta]
    calc Real.exp (scalarComparisonBound B.family a b * (b - a)) *
          (epsilon / 2 * Real.exp (-(scalarComparisonBound B.family a b * (b - a))))
        = (Real.exp (scalarComparisonBound B.family a b * (b - a)) *
            Real.exp (-(scalarComparisonBound B.family a b * (b - a)))) * (epsilon / 2) := by ring
      _ = epsilon / 2 := by rw [h1, one_mul]
  have heta_le : eta ≤ epsilon / 2 := by
    rw [heta]
    have h1 : Real.exp (-(scalarComparisonBound B.family a b * (b - a))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [hMnn, sub_nonneg.mpr B.lt.le])
    nlinarith [h1, hepsilon.le]
  have heta_lt : eta < epsilon := by nlinarith [heta_le, hepsilon]
  obtain ⟨prepared, hjets, hhom, harea, hrampdata⟩ := hprepared eta heta_pos
  obtain ⟨lambda₀, hl₀pos, hl₀one, halt'⟩ := halt L₀ Theta₀ Ainit hL₀ hTheta₀ hAinit
  obtain ⟨solutions, projected, hcont, hsol, hproj, hat, hjets', hclass, hbounds⟩ :=
    hflow lambda₀ hl₀pos hl₀one prepared hjets
  have hclassΓ : FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp prepared) =
      FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp Γ) :=
    (FreeHomotopyClass.mk_eq_mk_iff _ _).mpr
      ((ContinuousMap.Homotopic.refl contractibleRegularLoopInclusion).comp hhom)
  refine ⟨lambda₀, hl₀pos, hl₀one, solutions, projected, hcont, hsol, hproj, ?_, ?_, ?_⟩
  · intro t
    exact ⟨hjets' t, (hclass t).trans hclassΓ⟩
  · intro p
    rw [hat]
    linarith [harea p, heta_lt]
  · intro p
    set γ : ℝ → ContinuousFreeLoop Q := fun t => if ht : t ∈ Icc a b
      then ((projected ⟨t, ht⟩) p).1.toContinuousLoop
      else ((projected ⟨a, le_rfl, B.lt.le⟩) p).1.toContinuousLoop with hγ
    have hγproj : ∀ t ∈ Icc a b, ∀ z, γ t z = (solutions p).projection z t := by
      intro t ht z
      rw [hγ]
      simp only [dif_pos ht]
      exact hproj ⟨t, ht⟩ p z
    have hγctr : ∀ t ∈ Icc a b, IsContractibleLoop (γ t) := by
      intro t ht
      rw [hγ]
      simp only [dif_pos ht]
      exact (projected ⟨t, ht⟩ p).2
    have ha_mem : a ∈ Icc a b := ⟨le_rfl, B.lt.le⟩
    have hb_mem : b ∈ Icc a b := ⟨B.lt.le, le_rfl⟩
    have hγa0 : γ a = (prepared p).1.toContinuousLoop := by
      rw [hγ]
      simp only [dif_pos ha_mem]
      rw [hat]
    have hγb0 : γ b = ((projected ⟨b, B.lt.le, le_rfl⟩) p).1.toContinuousLoop := by
      rw [hγ]
      simp only [dif_pos hb_mem]
    have hinit : loopFamilyLeastArea B.family.metric γ a ≤ Ainit := by
      have h1 : regularLeastArea (B.family.metric a) (prepared p) ≤ Ainit :=
        (hrampdata p lambda₀ hl₀pos hl₀one).2.2.2.2
      simp only [loopFamilyLeastArea, hγa0, regularLeastArea, leastArea] at h1 ⊢
      exact h1
    have hγa : loopFamilyLeastArea B.family.metric γ a =
        regularLeastArea (B.family.metric a) (prepared p) := by
      simp only [loopFamilyLeastArea, hγa0, regularLeastArea, leastArea]
    have hγb : loopFamilyLeastArea B.family.metric γ b =
        regularLeastArea (B.family.metric b) ((projected ⟨b, B.lt.le, le_rfl⟩) p) := by
      simp only [loopFamilyLeastArea, hγb0, regularLeastArea, leastArea]
    have haff : affineComparison B.family a b (regularLeastArea (B.family.metric a) (prepared p)) ≤
        affineComparison B.family a b (regularLeastArea (B.family.metric a) (Γ p)) + epsilon / 2 := by
      have h := (rfs_width_affine_comparison B).2.2.2 a ha_mem b hb_mem
        (regularLeastArea (B.family.metric a) (Γ p))
        (regularLeastArea (B.family.metric a) (prepared p))
      have h2 : affineComparison B.family a b (regularLeastArea (B.family.metric a) (prepared p)) -
          affineComparison B.family a b (regularLeastArea (B.family.metric a) (Γ p)) ≤
          Real.exp (scalarComparisonBound B.family a b * (b - a)) * eta :=
        (le_abs_self (affineComparison B.family a b (regularLeastArea (B.family.metric a) (prepared p)) -
          affineComparison B.family a b (regularLeastArea (B.family.metric a) (Γ p)))).trans
          (h.trans (mul_le_mul_of_nonneg_left (harea p).le (Real.exp_nonneg _)))
      linarith [h2, hexp]
    rcases halt' lambda₀ hl₀pos le_rfl (solutions p) (hsol p).1 (hsol p).2.1 (hsol p).2.2
      γ hγproj hγctr (hbounds p).1 (hbounds p).2 hinit with hshort | hlong
    · exact Or.inl (by rw [← hγb0]; exact hshort)
    · right
      calc regularLeastArea (B.family.metric b) ((projected ⟨b, B.lt.le, le_rfl⟩) p)
          = loopFamilyLeastArea B.family.metric γ b := hγb.symm
        _ ≤ affineComparison B.family a b (loopFamilyLeastArea B.family.metric γ a) + epsilon / 2 := hlong
        _ = affineComparison B.family a b (regularLeastArea (B.family.metric a) (prepared p)) +
              epsilon / 2 := by rw [hγa]
        _ ≤ affineComparison B.family a b (regularLeastArea (B.family.metric a) (Γ p)) + epsilon := by
            linarith [haff]

omit [SigmaCompactSpace Q] hBoundary in
theorem rfs_family_deformation_of_prepared_family
    (B : RicciBackground (I := I) (M := Q) D a b) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2))
    (epsilon ell : ℝ) (hepsilon : 0 < epsilon)
    (eta : ℝ) (heta : 0 < eta)
    (heta_exp : Real.exp (scalarComparisonBound B.family a b * (b - a)) * eta ≤ epsilon / 2)
    (prepared : RegularFamily (I := I) (Q := Q) (Sphere 2))
    (L₀ Theta₀ Ainit : ℝ) (hL₀ : 0 ≤ L₀) (hTheta₀ : 0 ≤ Theta₀) (hAinit : 0 ≤ Ainit)
    (hjets : HasContinuousSmoothLoopJets e prepared)
    (hhom : ContinuousMap.Homotopic prepared Γ)
    (harea : ∀ p, |regularLeastArea (B.family.metric a) (prepared p) -
      regularLeastArea (B.family.metric a) (Γ p)| < eta)
    (hrampdata : ∀ p (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
      (initialRamp (prepared p).1).SmoothOn (I := I) univ ∧
      (initialRamp (prepared p).1).IsRampOn (fun _ => B.family.metric a) lambda univ ∧
      (initialRamp (prepared p).1).length (fun _ => B.family.metric a) lambda 0 ≤ L₀ ∧
      (initialRamp (prepared p).1).totalCurvature (fun _ => B.family.metric a) lambda 0 ≤ Theta₀ ∧
      regularLeastArea (B.family.metric a) (prepared p) ≤ Ainit)
    (hflow : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
      ∀ (prepared : RegularFamily (I := I) (Q := Q) (Sphere 2)),
        HasContinuousSmoothLoopJets e prepared →
      ∃ solutions : Sphere 2 → ProductCurve Q,
        ∃ projected : C(Icc a b, RegularFamily (I := I) (Q := Q) (Sphere 2)),
          @Continuous (Sphere 2) (ProductCurve Q) inferInstance
            (smoothProductCylinderTopology e (Icc a b)) solutions ∧
          (∀ p, (solutions p).IsSolutionOn B.family.metric lambda (Icc a b) ∧
            (solutions p).IsRampOn B.family.metric lambda (Icc a b) ∧ (solutions p).degree = 1) ∧
          (∀ t : Icc a b, ∀ p z,
            ((projected t) p).1 z = (solutions p).projection z t) ∧
          projected ⟨a, le_rfl, B.lt.le⟩ = prepared ∧
          (∀ t : Icc a b, HasContinuousSmoothLoopJets e (projected t)) ∧
          (∀ t : Icc a b,
            FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp (projected t)) =
              FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp prepared)) ∧
          (∀ p, (solutions p).length B.family.metric lambda a ≤ L₀ ∧
            (solutions p).totalCurvature B.family.metric lambda a ≤ Theta₀))
    (halt : ∀ (L Theta A : ℝ), 0 ≤ L → 0 ≤ Theta → 0 ≤ A →
      ∃ lambda₀ : ℝ, 0 < lambda₀ ∧ lambda₀ ≤ 1 ∧
        ∀ lambda : ℝ, 0 < lambda → lambda ≤ lambda₀ → ∀ c : ProductCurve Q,
          c.IsSolutionOn B.family.metric lambda (Icc a b) →
          c.IsRampOn B.family.metric lambda (Icc a b) → c.degree = 1 →
          ∀ γ : ℝ → ContinuousFreeLoop Q,
            (∀ t ∈ Icc a b, ∀ z, γ t z = c.projection z t) →
            (∀ t ∈ Icc a b, IsContractibleLoop (γ t)) →
            c.length B.family.metric lambda a ≤ L →
            c.totalCurvature B.family.metric lambda a ≤ Theta →
            loopFamilyLeastArea B.family.metric γ a ≤ A →
            loopLength (B.family.metric b) (γ b) < ell ∨
              loopFamilyLeastArea B.family.metric γ b ≤
                affineComparison B.family a b (loopFamilyLeastArea B.family.metric γ a) +
                  epsilon / 2) :
    ∃ lambda : ℝ, 0 < lambda ∧ lambda ≤ 1 ∧
      ∃ solutions : Sphere 2 → ProductCurve Q,
        ∃ deformed : C(Icc a b, RegularFamily (I := I) (Q := Q) (Sphere 2)),
          @Continuous (Sphere 2) (ProductCurve Q) inferInstance
            (smoothProductCylinderTopology e (Icc a b)) solutions ∧
          (∀ p, (solutions p).IsSolutionOn B.family.metric lambda (Icc a b) ∧
            (solutions p).IsRampOn B.family.metric lambda (Icc a b) ∧ (solutions p).degree = 1) ∧
          (∀ t : Icc a b, ∀ p z,
            ((deformed t) p).1 z = (solutions p).projection z t) ∧
          (∀ t : Icc a b, HasContinuousSmoothLoopJets e (deformed t) ∧
            FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp (deformed t)) =
              FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp Γ)) ∧
          (∀ p, |regularLeastArea (B.family.metric a) ((deformed ⟨a, le_rfl, B.lt.le⟩) p) -
            regularLeastArea (B.family.metric a) (Γ p)| < epsilon) ∧
          ∀ p,
            loopLength (B.family.metric b)
              (((deformed ⟨b, B.lt.le, le_rfl⟩) p).1.toContinuousLoop) < ell ∨
            regularLeastArea (B.family.metric b) ((deformed ⟨b, B.lt.le, le_rfl⟩) p) ≤
              affineComparison B.family a b (regularLeastArea (B.family.metric a) (Γ p)) + epsilon := by
  have heta_lt : eta < epsilon := by
    have hMnn : 0 ≤ scalarComparisonBound B.family a b := (rfs_width_flow_background B).2.2.1
    have h1 : 1 ≤ Real.exp (scalarComparisonBound B.family a b * (b - a)) :=
      Real.one_le_exp (mul_nonneg hMnn (sub_nonneg.mpr B.lt.le))
    have h2 : eta ≤ Real.exp (scalarComparisonBound B.family a b * (b - a)) * eta := by
      nlinarith [h1, heta.le]
    exact lt_of_le_of_lt (le_trans h2 heta_exp) (half_lt_self hepsilon)
  obtain ⟨lambda₀, hl₀pos, hl₀one, halt'⟩ := halt L₀ Theta₀ Ainit hL₀ hTheta₀ hAinit
  obtain ⟨solutions, projected, hcont, hsol, hproj, hat, hjets', hclass, hbounds⟩ :=
    hflow lambda₀ hl₀pos hl₀one prepared hjets
  have hclassΓ : FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp prepared) =
      FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp Γ) :=
    (FreeHomotopyClass.mk_eq_mk_iff _ _).mpr
      ((ContinuousMap.Homotopic.refl contractibleRegularLoopInclusion).comp hhom)
  refine ⟨lambda₀, hl₀pos, hl₀one, solutions, projected, hcont, hsol, hproj, ?_, ?_, ?_⟩
  · intro t
    exact ⟨hjets' t, (hclass t).trans hclassΓ⟩
  · intro p
    rw [hat]
    linarith [harea p, heta_lt]
  · intro p
    set γ : ℝ → ContinuousFreeLoop Q := fun t => if ht : t ∈ Icc a b
      then ((projected ⟨t, ht⟩) p).1.toContinuousLoop
      else ((projected ⟨a, le_rfl, B.lt.le⟩) p).1.toContinuousLoop with hγ
    have hγproj : ∀ t ∈ Icc a b, ∀ z, γ t z = (solutions p).projection z t := by
      intro t ht z
      rw [hγ]
      simp only [dif_pos ht]
      exact hproj ⟨t, ht⟩ p z
    have hγctr : ∀ t ∈ Icc a b, IsContractibleLoop (γ t) := by
      intro t ht
      rw [hγ]
      simp only [dif_pos ht]
      exact (projected ⟨t, ht⟩ p).2
    have ha_mem : a ∈ Icc a b := ⟨le_rfl, B.lt.le⟩
    have hb_mem : b ∈ Icc a b := ⟨B.lt.le, le_rfl⟩
    have hγa0 : γ a = (prepared p).1.toContinuousLoop := by
      rw [hγ]
      simp only [dif_pos ha_mem]
      rw [hat]
    have hγb0 : γ b = ((projected ⟨b, B.lt.le, le_rfl⟩) p).1.toContinuousLoop := by
      rw [hγ]
      simp only [dif_pos hb_mem]
    have hinit : loopFamilyLeastArea B.family.metric γ a ≤ Ainit := by
      have h1 : regularLeastArea (B.family.metric a) (prepared p) ≤ Ainit :=
        (hrampdata p lambda₀ hl₀pos hl₀one).2.2.2.2
      simp only [loopFamilyLeastArea, hγa0, regularLeastArea, leastArea] at h1 ⊢
      exact h1
    have hγa : loopFamilyLeastArea B.family.metric γ a =
        regularLeastArea (B.family.metric a) (prepared p) := by
      simp only [loopFamilyLeastArea, hγa0, regularLeastArea, leastArea]
    have hγb : loopFamilyLeastArea B.family.metric γ b =
        regularLeastArea (B.family.metric b) ((projected ⟨b, B.lt.le, le_rfl⟩) p) := by
      simp only [loopFamilyLeastArea, hγb0, regularLeastArea, leastArea]
    have haff : affineComparison B.family a b (regularLeastArea (B.family.metric a) (prepared p)) ≤
        affineComparison B.family a b (regularLeastArea (B.family.metric a) (Γ p)) + epsilon / 2 := by
      have h := (rfs_width_affine_comparison B).2.2.2 a ha_mem b hb_mem
        (regularLeastArea (B.family.metric a) (Γ p))
        (regularLeastArea (B.family.metric a) (prepared p))
      have h2 : affineComparison B.family a b (regularLeastArea (B.family.metric a) (prepared p)) -
          affineComparison B.family a b (regularLeastArea (B.family.metric a) (Γ p)) ≤
          Real.exp (scalarComparisonBound B.family a b * (b - a)) * eta :=
        (le_abs_self (affineComparison B.family a b (regularLeastArea (B.family.metric a) (prepared p)) -
          affineComparison B.family a b (regularLeastArea (B.family.metric a) (Γ p)))).trans
          (h.trans (mul_le_mul_of_nonneg_left (harea p).le (Real.exp_nonneg _)))
      linarith [h2, heta_exp]
    rcases halt' lambda₀ hl₀pos le_rfl (solutions p) (hsol p).1 (hsol p).2.1 (hsol p).2.2
      γ hγproj hγctr (hbounds p).1 (hbounds p).2 hinit with hshort | hlong
    · exact Or.inl (by rw [← hγb0]; exact hshort)
    · right
      calc regularLeastArea (B.family.metric b) ((projected ⟨b, B.lt.le, le_rfl⟩) p)
          = loopFamilyLeastArea B.family.metric γ b := hγb.symm
        _ ≤ affineComparison B.family a b (loopFamilyLeastArea B.family.metric γ a) + epsilon / 2 := hlong
        _ = affineComparison B.family a b (regularLeastArea (B.family.metric a) (prepared p)) +
              epsilon / 2 := by rw [hγa]
        _ ≤ affineComparison B.family a b (regularLeastArea (B.family.metric a) (Γ p)) + epsilon := by
            linarith [haff]

private def rampLen (B₀ L a b : ℝ) : ℝ := Real.exp (B₀ * (b - a)) * L

private def rampCurv (B₀ C L T a b : ℝ) : ℝ := (T + L) * Real.exp ((C + B₀) * (b - a))

private def rampArea (B₀ C L T A a b : ℝ) : ℝ :=
  Real.exp (2 * B₀ * (b - a)) * (A + (b - a) * rampCurv B₀ C L T a b)

private def rampRate (B₀ C L T A a b : ℝ) : ℝ :=
  Real.exp (2 * B₀ * (b - a)) * (2 * B₀ * rampArea B₀ C L T A a b + rampCurv B₀ C L T a b)

omit [SigmaCompactSpace Q] hBoundary in
theorem rfs_uniform_ramp_alternative_of_product_bounds
    (B : RicciBackground (I := I) (M := Q) D a b)
    (L₀ Theta₀ Ainit : ℝ) (hL₀ : 0 ≤ L₀) (hTheta₀ : 0 ≤ Theta₀) (hAinit : 0 ≤ Ainit)
    (ell epsilon : ℝ) (hell : 0 < ell) (hepsilon : 0 < epsilon)
    (hproduct : ∀ (L Theta : ℝ), 0 ≤ L → 0 ≤ Theta →
      ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 → ∀ c : ProductCurve Q,
        c.IsSolutionOn B.family.metric lambda (Icc a b) →
        c.length B.family.metric lambda a ≤ L →
        c.totalCurvature B.family.metric lambda a ≤ Theta →
        ∀ t ∈ Icc a b,
          c.length B.family.metric lambda t ≤ rampLen B.B₀ L a t ∧
          c.length B.family.metric lambda b ≤
            Real.exp (B.B₀ * (b - t)) * c.length B.family.metric lambda t ∧
          (∫ v in a..t, c.energy B.family.metric lambda v) ≤ rampLen B.B₀ L a t ∧
          c.totalCurvature B.family.metric lambda t + c.length B.family.metric lambda t ≤
            rampCurv B.B₀ B.C L Theta a t)
    (hprojlen : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 → ∀ c : ProductCurve Q,
      c.IsSolutionOn B.family.metric lambda (Icc a b) →
      ∀ γ : ℝ → ContinuousFreeLoop Q, (∀ z, γ b z = c.projection z b) →
        loopLength (B.family.metric b) (γ b) ≤ c.length B.family.metric lambda b)
    (harea : ∀ (L Theta : ℝ), 0 ≤ L → 0 ≤ Theta →
      ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 → ∀ c : ProductCurve Q,
        c.IsSolutionOn B.family.metric lambda (Icc a b) →
        c.length B.family.metric lambda a ≤ L →
        c.totalCurvature B.family.metric lambda a ≤ Theta →
        ∀ γ : ℝ → ContinuousFreeLoop Q,
          (∀ t ∈ Icc a b, ∀ z, γ t z = c.projection z t) →
          (∀ t ∈ Icc a b, IsContractibleLoop (γ t)) →
          loopFamilyLeastArea B.family.metric γ a ≤ Ainit →
          ContinuousOn (loopFamilyLeastArea B.family.metric γ) (Icc a b) ∧
          (∀ t ∈ Icc a b, 0 ≤ loopFamilyLeastArea B.family.metric γ t ∧
            loopFamilyLeastArea B.family.metric γ t ≤ rampArea B.B₀ B.C L Theta Ainit a b) ∧
          (∀ s ∈ Icc a b, ∀ t ∈ Icc s b,
            loopFamilyLeastArea B.family.metric γ t - loopFamilyLeastArea B.family.metric γ s ≤
              rampRate B.B₀ B.C L Theta Ainit a b * (t - s)))
    (delta r₀ : ℝ) (hdelta : 0 < delta) (hr₀ : 0 < r₀)
    (eta threshold : ℝ) (heta : 0 < eta) (hthreshold : 0 < threshold)
    (r d : ℝ) (hr : r = min r₀ (min (Real.exp (-(B.B₀ * (b - a))) * ell / 2)
      (delta ^ 2 / threshold))) (hd : d = delta * r ^ 2)
    (lambda₀ : ℝ) (hl₀ : 0 < lambda₀) (hl₀_one : lambda₀ ≤ 1)
    (hwindows : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ lambda₀ → ∀ c : ProductCurve Q,
      c.IsSolutionOn B.family.metric lambda (Icc a b) →
      c.IsRampOn B.family.metric lambda (Icc a b) → c.degree = 1 →
      c.length B.family.metric lambda a ≤ L₀ →
      c.totalCurvature B.family.metric lambda a ≤ Theta₀ →
      (∀ t ∈ Icc a b, Real.exp (-(B.B₀ * (b - a))) * ell ≤ c.length B.family.metric lambda t) →
      ∃ starts : Finset ℝ,
        goodWindowUnion starts d ⊆ Ioo a b ∧
        volume (Icc a b \ goodWindowUnion starts d) ≤
          ENNReal.ofReal (d + Real.exp (B.B₀ * (b - a)) * L₀ / threshold) ∧
        ∀ x t, t ∈ goodWindowUnion starts d →
          0 < c.angle B.family.metric lambda x t ∧
          c.angle B.family.metric lambda x t ≤ eta)
    (hDini : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ lambda₀ → ∀ c : ProductCurve Q,
      c.IsSolutionOn B.family.metric lambda (Icc a b) →
      c.IsRampOn B.family.metric lambda (Icc a b) → c.degree = 1 →
      c.length B.family.metric lambda a ≤ L₀ →
      c.totalCurvature B.family.metric lambda a ≤ Theta₀ →
      ∀ γ : ℝ → ContinuousFreeLoop Q, (∀ t ∈ Icc a b, ∀ z, γ t z = c.projection z t) →
      (∀ t ∈ Icc a b, IsContractibleLoop (γ t)) →
      loopFamilyLeastArea B.family.metric γ a ≤ Ainit →
      ∀ starts : Finset ℝ,
        (∀ x t, t ∈ goodWindowUnion starts d →
          0 < c.angle B.family.metric lambda x t ∧ c.angle B.family.metric lambda x t ≤ eta) →
      ∀ t ∈ Ico a b, t ∈ goodWindowUnion starts d → ∀ eps > 0, ∃ dd > 0,
        ∀ h ∈ Ioo (0 : ℝ) dd, t + h ≤ b →
          (loopFamilyLeastArea B.family.metric γ (t + h) -
              loopFamilyLeastArea B.family.metric γ t) / h ≤
            -2 * Real.pi - halfScalarMinimum B.family t * loopFamilyLeastArea B.family.metric γ t +
              eta ^ 2 / Real.sqrt (1 - eta ^ 2) * rampCurv B.B₀ B.C L₀ Theta₀ a b + eps)
    (herror : Real.exp (2 * scalarComparisonBound B.family a b * (b - a)) *
      (eta ^ 2 / Real.sqrt (1 - eta ^ 2) * rampCurv B.B₀ B.C L₀ Theta₀ a b * (b - a) +
        (rampRate B.B₀ B.C L₀ Theta₀ Ainit a b + scalarComparisonBound B.family a b *
          rampArea B.B₀ B.C L₀ Theta₀ Ainit a b + 2 * Real.pi) *
          (d + Real.exp (B.B₀ * (b - a)) * L₀ / threshold)) ≤ epsilon) :
    ∃ lambda₀ : ℝ, 0 < lambda₀ ∧ lambda₀ ≤ 1 ∧
      ∀ lambda : ℝ, 0 < lambda → lambda ≤ lambda₀ → ∀ c : ProductCurve Q,
        c.IsSolutionOn B.family.metric lambda (Icc a b) →
        c.IsRampOn B.family.metric lambda (Icc a b) → c.degree = 1 →
        ∀ γ : ℝ → ContinuousFreeLoop Q,
          (∀ t ∈ Icc a b, ∀ z, γ t z = c.projection z t) →
          (∀ t ∈ Icc a b, IsContractibleLoop (γ t)) →
          c.length B.family.metric lambda a ≤ L₀ →
          c.totalCurvature B.family.metric lambda a ≤ Theta₀ →
          loopFamilyLeastArea B.family.metric γ a ≤ Ainit →
          loopLength (B.family.metric b) (γ b) < ell ∨
            loopFamilyLeastArea B.family.metric γ b ≤
              affineComparison B.family a b (loopFamilyLeastArea B.family.metric γ a) + epsilon := by
  let _ := hepsilon
  have hThetaBar : 0 ≤ rampCurv B.B₀ B.C L₀ Theta₀ a b :=
    mul_nonneg (by linarith) (Real.exp_nonneg _)
  have hAbar : 0 ≤ rampArea B.B₀ B.C L₀ Theta₀ Ainit a b :=
    mul_nonneg (Real.exp_nonneg _) (add_nonneg hAinit (mul_nonneg (by linarith [B.lt.le]) hThetaBar))
  have hCup : 0 ≤ rampRate B.B₀ B.C L₀ Theta₀ Ainit a b :=
    mul_nonneg (Real.exp_nonneg _)
      (add_nonneg (mul_nonneg (by linarith [B.B₀_nonneg]) hAbar) hThetaBar)
  have hlength : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ lambda₀ → ∀ c : ProductCurve Q,
      c.IsSolutionOn B.family.metric lambda (Icc a b) →
      c.IsRampOn B.family.metric lambda (Icc a b) → c.degree = 1 →
      c.length B.family.metric lambda a ≤ L₀ →
      c.totalCurvature B.family.metric lambda a ≤ Theta₀ →
      ∀ γ : ℝ → ContinuousFreeLoop Q, (∀ z, γ b z = c.projection z b) →
      ell ≤ loopLength (B.family.metric b) (γ b) →
      ∀ t ∈ Icc a b, Real.exp (-(B.B₀ * (b - a))) * ell ≤ c.length B.family.metric lambda t := by
    intro lambda hlambda hlam₀ c hsol _hramp _hdeg hlen hcurv γ hγb hellen t ht
    have hlam₁ : lambda ≤ 1 := le_trans hlam₀ hl₀_one
    have hkey := (hproduct L₀ Theta₀ hL₀ hTheta₀ lambda hlambda hlam₁ c hsol hlen hcurv t ht).2.1
    have hproj := hprojlen lambda hlambda hlam₁ c hsol γ hγb
    have hellb : ell ≤ c.length B.family.metric lambda b := hellen.trans hproj
    have hstep : Real.exp (-(B.B₀ * (b - t))) * c.length B.family.metric lambda b ≤
        c.length B.family.metric lambda t := by
      have h := mul_le_mul_of_nonneg_left hkey (Real.exp_nonneg (-(B.B₀ * (b - t))))
      rwa [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul] at h
    have hmono : Real.exp (-(B.B₀ * (b - a))) ≤ Real.exp (-(B.B₀ * (b - t))) := by
      refine Real.exp_le_exp.mpr ?_
      have hle : b - t ≤ b - a := by linarith [ht.1]
      linarith [mul_le_mul_of_nonneg_left hle B.B₀_nonneg]
    calc Real.exp (-(B.B₀ * (b - a))) * ell
        ≤ Real.exp (-(B.B₀ * (b - t))) * ell := mul_le_mul_of_nonneg_right hmono hell.le
      _ ≤ Real.exp (-(B.B₀ * (b - t))) * c.length B.family.metric lambda b :=
          mul_le_mul_of_nonneg_left hellb (Real.exp_nonneg _)
      _ ≤ c.length B.family.metric lambda t := hstep
  have hcontinuous : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ lambda₀ → ∀ c : ProductCurve Q,
      c.IsSolutionOn B.family.metric lambda (Icc a b) →
      c.IsRampOn B.family.metric lambda (Icc a b) → c.degree = 1 →
      c.length B.family.metric lambda a ≤ L₀ →
      c.totalCurvature B.family.metric lambda a ≤ Theta₀ →
      ∀ γ : ℝ → ContinuousFreeLoop Q, (∀ t ∈ Icc a b, ∀ z, γ t z = c.projection z t) →
      (∀ t ∈ Icc a b, IsContractibleLoop (γ t)) →
      loopFamilyLeastArea B.family.metric γ a ≤ Ainit →
      ContinuousOn (loopFamilyLeastArea B.family.metric γ) (Icc a b) ∧
      (∀ t ∈ Icc a b, 0 ≤ loopFamilyLeastArea B.family.metric γ t ∧
        loopFamilyLeastArea B.family.metric γ t ≤ rampArea B.B₀ B.C L₀ Theta₀ Ainit a b) ∧
      (∀ s ∈ Icc a b, ∀ t ∈ Icc s b,
        loopFamilyLeastArea B.family.metric γ t - loopFamilyLeastArea B.family.metric γ s ≤
          rampRate B.B₀ B.C L₀ Theta₀ Ainit a b * (t - s)) := by
    intro lambda hlambda hlam₀ c hsol _hramp _hdeg hlen hcurv γ hγ hctr hA
    exact harea L₀ Theta₀ hL₀ hTheta₀ lambda hlambda (le_trans hlam₀ hl₀_one) c hsol hlen hcurv
      γ hγ hctr hA
  refine ⟨lambda₀, hl₀, hl₀_one, ?_⟩
  intro lambda hlambda hlambda_one c hsol hramp hdeg γ hγ hctr hlen0 hcurv0 hAinit0
  exact rfs_uniform_ramp_alternative_of_window_data B L₀ Theta₀ Ainit hL₀ hTheta₀
    (rampArea B.B₀ B.C L₀ Theta₀ Ainit a b) (rampRate B.B₀ B.C L₀ Theta₀ Ainit a b)
    eta threshold hAbar hCup hthreshold heta ell (Real.exp (-(B.B₀ * (b - a))) * ell) epsilon
    (mul_pos (Real.exp_pos _) hell) delta r₀ hdelta hr₀ r d hr hd lambda₀
    (rampCurv B.B₀ B.C L₀ Theta₀ a b) hThetaBar
    hlength hwindows hcontinuous hDini herror
    lambda hlambda hlambda_one c hsol hramp hdeg γ hγ hctr hlen0 hcurv0 hAinit0

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
