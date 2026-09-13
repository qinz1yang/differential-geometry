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

omit [SigmaCompactSpace Q] hBoundary in
def RampWindowInput (B : RicciBackground (I := I) (M := Q) D a b)
    (L₀ Theta₀ Ainit : ℝ) (ell eta threshold d : ℝ) : Prop :=
  ∃ lambda₀ : ℝ, 0 < lambda₀ ∧ lambda₀ ≤ 1 ∧
    (∀ (lambda : ℝ), 0 < lambda → lambda ≤ lambda₀ → ∀ c : ProductCurve Q,
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
          c.angle B.family.metric lambda x t ≤ eta) ∧
    (∀ (lambda : ℝ), 0 < lambda → lambda ≤ lambda₀ → ∀ c : ProductCurve Q,
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

omit [SigmaCompactSpace Q] hBoundary in
theorem rfs_uniform_ramp_alternative_of_frontier
    (B : RicciBackground (I := I) (M := Q) D a b)
    (hdim : Module.finrank ℝ E = 3)
    (L₀ Theta₀ Ainit : ℝ) (hL₀ : 0 ≤ L₀) (hTheta₀ : 0 ≤ Theta₀) (hAinit : 0 ≤ Ainit)
    (ell epsilon : ℝ) (hell : 0 < ell) (hepsilon : 0 < epsilon)
    (hproduct : RampProductBounds B) (harea : RampAreaBounds B Ainit)
    (hwindow : ∀ eta : ℝ, 0 < eta → eta < 1 → ∀ threshold : ℝ, 1 ≤ threshold →
      ∀ d : ℝ, 0 < d → RampWindowInput B L₀ Theta₀ Ainit ell eta threshold d) :
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
  let _ := hdim
  have hΔ : 0 ≤ b - a := sub_nonneg.mpr B.lt.le
  have hM : 0 ≤ scalarComparisonBound B.family a b := (rfs_width_flow_background B).2.2.1
  have hΘbar0 : 0 ≤ rampCurv B.B₀ B.C L₀ Theta₀ a b :=
    mul_nonneg (by linarith only [hL₀, hTheta₀]) (Real.exp_nonneg _)
  have hAbar0 : 0 ≤ rampArea B.B₀ B.C L₀ Theta₀ Ainit a b := by
    simp only [rampArea]
    exact mul_nonneg (Real.exp_nonneg _) (add_nonneg hAinit (mul_nonneg hΔ hΘbar0))
  have hCup0 : 0 ≤ rampRate B.B₀ B.C L₀ Theta₀ Ainit a b := by
    simp only [rampRate]
    exact mul_nonneg (Real.exp_nonneg _)
      (add_nonneg (mul_nonneg (by linarith only [B.B₀_nonneg]) hAbar0) hΘbar0)
  set T2 : ℝ := Real.exp (2 * scalarComparisonBound B.family a b * (b - a)) with hT2
  set E : ℝ := Real.exp (B.B₀ * (b - a)) with hE
  set Θbar : ℝ := rampCurv B.B₀ B.C L₀ Theta₀ a b with hΘbar
  set Abar : ℝ := rampArea B.B₀ B.C L₀ Theta₀ Ainit a b with hAbar
  set Cup : ℝ := rampRate B.B₀ B.C L₀ Theta₀ Ainit a b with hCup
  set S : ℝ := Cup + scalarComparisonBound B.family a b * Abar + 2 * Real.pi with hS
  have hT2pos : 0 < T2 := by rw [hT2]; exact Real.exp_pos _
  have hEpos : 0 < E := by rw [hE]; exact Real.exp_pos _
  have hΘnn : 0 ≤ Θbar := by rw [hΘbar]; exact hΘbar0
  have hAnn : 0 ≤ Abar := by rw [hAbar]; exact hAbar0
  have hCnn : 0 ≤ Cup := by rw [hCup]; exact hCup0
  have hSnn : 0 ≤ S := by
    rw [hS]
    exact add_nonneg (add_nonneg hCnn (mul_nonneg hM hAnn)) (by positivity)
  set G : ℝ := Θbar * (b - a) + 1 with hG
  have hG1 : 1 ≤ G := by
    rw [hG]
    have h := mul_nonneg hΘnn hΔ
    linarith only [h]
  have hGpos : 0 < G := lt_of_lt_of_le one_pos hG1
  set K : ℝ := T2 * S + T2 * G + 1 with hK
  have hK1 : 1 ≤ K := by
    rw [hK]
    have h1 : 0 ≤ T2 * S := mul_nonneg hT2pos.le hSnn
    have h2 : 0 ≤ T2 * G := mul_nonneg hT2pos.le hGpos.le
    linarith only [h1, h2]
  have hKpos : 0 < K := lt_of_lt_of_le one_pos hK1
  have hT2G : T2 * G ≤ K := by
    rw [hK]
    have h1 : 0 ≤ T2 * S := mul_nonneg hT2pos.le hSnn
    linarith only [h1]
  have hT2S : T2 * S ≤ K := by
    rw [hK]
    have h1 : 0 ≤ T2 * G := mul_nonneg hT2pos.le hGpos.le
    linarith only [h1]
  set eta : ℝ := min (1 / 2) (epsilon / (3 * K)) with heta
  have h3Kpos : 0 < 3 * K := by linarith only [hKpos]
  have heta_pos : 0 < eta := by
    rw [heta]
    exact lt_min (by norm_num) (div_pos hepsilon h3Kpos)
  have heta_half : eta ≤ 1 / 2 := by rw [heta]; exact min_le_left _ _
  have heta_one : eta < 1 := lt_of_le_of_lt heta_half (by norm_num)
  have heta_le : eta ≤ epsilon / (3 * K) := by rw [heta]; exact min_le_right _ _
  have hetaK : eta * K ≤ epsilon / 3 := by
    have h1 := mul_le_mul_of_nonneg_right heta_le hKpos.le
    have h2 : epsilon / (3 * K) * K = epsilon / 3 := by field_simp
    linarith only [h1, h2]
  have heta_sq : eta ^ 2 ≤ 1 / 4 := by nlinarith only [heta_half, heta_pos]
  have hsqrt_pos : 0 < Real.sqrt (1 - eta ^ 2) := Real.sqrt_pos.2 (by nlinarith only [heta_sq])
  have heta_le_sqrt : eta ≤ Real.sqrt (1 - eta ^ 2) := by
    rw [Real.le_sqrt heta_pos.le (by nlinarith only [heta_sq])]
    nlinarith only [heta_sq]
  have hfrac : eta ^ 2 / Real.sqrt (1 - eta ^ 2) ≤ eta := by
    rw [div_le_iff₀ hsqrt_pos]
    nlinarith only [heta_le_sqrt, heta_pos.le]
  set threshold : ℝ := max 1 (3 * K * E * L₀ / epsilon) with hthreshold
  have hthreshold_one : 1 ≤ threshold := by rw [hthreshold]; exact le_max_left _ _
  have hthreshold_pos : 0 < threshold := lt_of_lt_of_le one_pos hthreshold_one
  have hthreshold_le : 3 * K * E * L₀ / epsilon ≤ threshold := by
    rw [hthreshold]; exact le_max_right _ _
  have hEL : E * L₀ / threshold ≤ epsilon / (3 * K) := by
    rw [div_le_div_iff₀ hthreshold_pos h3Kpos]
    have h1 := mul_le_mul_of_nonneg_right hthreshold_le hepsilon.le
    rw [div_mul_cancel₀ _ (ne_of_gt hepsilon)] at h1
    nlinarith only [h1]
  set delta : ℝ := min 1 (epsilon / (3 * K)) with hdelta
  have hdelta_pos : 0 < delta := by
    rw [hdelta]
    exact lt_min one_pos (div_pos hepsilon h3Kpos)
  have hdelta_one : delta ≤ 1 := by rw [hdelta]; exact min_le_left _ _
  have hdelta_le : delta ≤ epsilon / (3 * K) := by rw [hdelta]; exact min_le_right _ _
  set r₀ : ℝ := E * ell / 2 with hr₀
  have hr₀_pos : 0 < r₀ := by
    rw [hr₀]
    exact div_pos (mul_pos hEpos hell) (by norm_num)
  set r : ℝ := min r₀ (min (Real.exp (-(B.B₀ * (b - a))) * ell / 2)
    (delta ^ 2 / threshold)) with hr
  have hr_pos : 0 < r := by
    rw [hr]
    refine lt_min hr₀_pos (lt_min ?_ (div_pos (pow_pos hdelta_pos 2) hthreshold_pos))
    exact div_pos (mul_pos (Real.exp_pos _) hell) (by norm_num)
  have hr_le : r ≤ delta ^ 2 / threshold := by
    rw [hr]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  set d : ℝ := delta * r ^ 2 with hd
  have hd_pos : 0 < d := by rw [hd]; exact mul_pos hdelta_pos (pow_pos hr_pos 2)
  have hd_le : d ≤ epsilon / (3 * K) := by
    rw [hd]
    have h1 : r ^ 2 ≤ (delta ^ 2 / threshold) ^ 2 := pow_le_pow_left₀ hr_pos.le hr_le 2
    have h2 : delta * r ^ 2 ≤ delta * (delta ^ 2 / threshold) ^ 2 :=
      mul_le_mul_of_nonneg_left h1 hdelta_pos.le
    have h3 : delta * (delta ^ 2 / threshold) ^ 2 = delta ^ 5 / threshold ^ 2 := by
      rw [div_pow]
      ring
    have h6 : delta ^ 5 ≤ 1 := pow_le_one₀ hdelta_pos.le hdelta_one
    have h4 : delta ^ 5 / threshold ^ 2 ≤ delta ^ 5 := by
      rw [div_le_iff₀ (pow_pos hthreshold_pos 2)]
      have h5 : 1 ≤ threshold ^ 2 := by nlinarith only [hthreshold_one]
      have h7 : 0 < delta ^ 5 := pow_pos hdelta_pos 5
      nlinarith only [h6, h5, h7]
    have h5 : delta ^ 5 ≤ delta := by
      calc delta ^ 5 = delta ^ 4 * delta := by ring
        _ ≤ 1 * delta :=
            mul_le_mul_of_nonneg_right (pow_le_one₀ hdelta_pos.le hdelta_one) hdelta_pos.le
        _ = delta := one_mul _
    linarith only [h2, h3, h4, h5, hdelta_le]
  have hterm1 : T2 * (eta ^ 2 / Real.sqrt (1 - eta ^ 2) * Θbar * (b - a)) ≤ epsilon / 3 := by
    have hA0 : 0 ≤ eta ^ 2 / Real.sqrt (1 - eta ^ 2) :=
      div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
    have hX0 : 0 ≤ Θbar * (b - a) := mul_nonneg hΘnn hΔ
    have hstep1 : eta ^ 2 / Real.sqrt (1 - eta ^ 2) * Θbar * (b - a) ≤ eta * G := by
      have h1 : eta ^ 2 / Real.sqrt (1 - eta ^ 2) * Θbar * (b - a) =
          (eta ^ 2 / Real.sqrt (1 - eta ^ 2)) * (Θbar * (b - a)) := by ring
      rw [h1]
      calc (eta ^ 2 / Real.sqrt (1 - eta ^ 2)) * (Θbar * (b - a))
          ≤ eta * (Θbar * (b - a)) := mul_le_mul_of_nonneg_right hfrac hX0
        _ ≤ eta * G := by
            rw [hG]
            exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) heta_pos.le
    have hstep2 : T2 * (eta * G) ≤ epsilon / 3 := by
      have h1 : T2 * (eta * G) = eta * (T2 * G) := by ring
      have h2 : eta * (T2 * G) ≤ eta * K := mul_le_mul_of_nonneg_left hT2G heta_pos.le
      linarith only [h1, h2, hetaK]
    exact le_trans (mul_le_mul_of_nonneg_left hstep1 hT2pos.le) hstep2
  have hterm2 : T2 * (S * (E * L₀ / threshold)) ≤ epsilon / 3 := by
    have h1 : T2 * (S * (E * L₀ / threshold)) = T2 * S * (E * L₀ / threshold) := by ring
    rw [h1]
    have h2 : T2 * S * (E * L₀ / threshold) ≤ K * (E * L₀ / threshold) :=
      mul_le_mul_of_nonneg_right hT2S (div_nonneg (mul_nonneg hEpos.le hL₀) hthreshold_pos.le)
    have h3 := mul_le_mul_of_nonneg_left hEL hKpos.le
    have h4 : K * (epsilon / (3 * K)) = epsilon / 3 := by field_simp
    linarith only [h2, h3, h4]
  have hterm3 : T2 * (S * d) ≤ epsilon / 3 := by
    have h1 : T2 * (S * d) = T2 * S * d := by ring
    rw [h1]
    have h2 : T2 * S * d ≤ K * d := mul_le_mul_of_nonneg_right hT2S hd_pos.le
    have h3 := mul_le_mul_of_nonneg_left hd_le hKpos.le
    have h4 : K * (epsilon / (3 * K)) = epsilon / 3 := by field_simp
    linarith only [h2, h3, h4]
  have hkey : T2 * (eta ^ 2 / Real.sqrt (1 - eta ^ 2) * Θbar * (b - a) +
      S * (d + E * L₀ / threshold)) ≤ epsilon := by
    nlinarith only [hterm1, hterm2, hterm3]
  have herror : Real.exp (2 * scalarComparisonBound B.family a b * (b - a)) *
      (eta ^ 2 / Real.sqrt (1 - eta ^ 2) * rampCurv B.B₀ B.C L₀ Theta₀ a b * (b - a) +
        (rampRate B.B₀ B.C L₀ Theta₀ Ainit a b + scalarComparisonBound B.family a b *
          rampArea B.B₀ B.C L₀ Theta₀ Ainit a b + 2 * Real.pi) *
          (d + Real.exp (B.B₀ * (b - a)) * L₀ / threshold)) ≤ epsilon := by
    simpa only [hT2, hE, hΘbar, hAbar, hCup, hS] using hkey
  obtain ⟨lambda₀, hl₀, hl₀_one, hwindows, hDini⟩ :=
    hwindow eta heta_pos heta_one threshold hthreshold_one d hd_pos
  refine rfs_uniform_ramp_alternative_of_product_bounds B L₀ Theta₀ Ainit hL₀ hTheta₀ hAinit
    ell epsilon hell hepsilon ?_ (rfs_ramp_projected_length B) ?_ delta r₀ hdelta_pos hr₀_pos eta
    threshold heta_pos hthreshold_pos r d hr hd lambda₀ hl₀ hl₀_one hwindows hDini herror
  · intro L Theta hL hT lambda hlambda hlambda_one c hsol hlen hcurv t ht
    simpa only [rampLen, rampCurv, mul_comm] using
      hproduct L Theta hL hT lambda hlambda hlambda_one c hsol hlen hcurv t ht
  · intro L Theta hL hT lambda hlambda hlambda_one c hsol hlen hcurv γ hγ hctr hA
    simpa only [rampArea, rampRate, rampCurv] using
      harea L Theta hL hT lambda hlambda hlambda_one c hsol hlen hcurv γ hγ hctr hA

omit [SigmaCompactSpace Q] hBoundary in
def PreparedFamilyApproximation (B : RicciBackground (I := I) (M := Q) D a b) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2)) (L₀ Theta₀ Ainit : ℝ) : Prop :=
  ∀ (eta : ℝ), 0 < eta →
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
        regularLeastArea (B.family.metric a) (prepared p) ≤ Ainit

omit [SigmaCompactSpace Q] hBoundary in
def PreparedFamilyFlowData (B : RicciBackground (I := I) (M := Q) D a b) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d) (L₀ Theta₀ : ℝ) : Prop :=
  ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
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
          (solutions p).totalCurvature B.family.metric lambda a ≤ Theta₀)

omit [SigmaCompactSpace Q] hBoundary in
def RampAlternativeData (B : RicciBackground (I := I) (M := Q) D a b)
    (ell epsilon : ℝ) : Prop :=
  ∀ (L Theta A : ℝ), 0 ≤ L → 0 ≤ Theta → 0 ≤ A →
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
                epsilon / 2

omit [SigmaCompactSpace Q] hBoundary in
theorem rfs_family_deformation_of_frontier
    (B : RicciBackground (I := I) (M := Q) D a b) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2))
    (epsilon ell : ℝ) (hepsilon : 0 < epsilon)
    (L₀ Theta₀ Ainit : ℝ) (hL₀ : 0 ≤ L₀) (hTheta₀ : 0 ≤ Theta₀) (hAinit : 0 ≤ Ainit)
    (hprepared : PreparedFamilyApproximation B e Γ L₀ Theta₀ Ainit)
    (hflow : PreparedFamilyFlowData B e L₀ Theta₀)
    (halt : RampAlternativeData B ell epsilon) :
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
              affineComparison B.family a b (regularLeastArea (B.family.metric a) (Γ p)) + epsilon :=
  rfs_family_deformation_of_prepared_flow B e Γ epsilon ell hepsilon L₀ Theta₀ Ainit hL₀ hTheta₀
    hAinit hprepared hflow halt

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
