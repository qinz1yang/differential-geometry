import DifferentialGeometry.Analysis.ODE.Gronwall.EnergyIntegral
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.Deformation


noncomputable section

open Bundle Manifold Set MeasureTheory Filter
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

omit hCompact hConnected hBoundary in
def RampLengthEvolution (B : RicciBackground (I := I) (M := Q) D a b) : Prop :=
  ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 → ∀ c : ProductCurve Q,
    c.IsSolutionOn B.family.metric lambda (Icc a b) →
    ∀ s t : ℝ, a ≤ s → s ≤ t → t ≤ b →
      ContinuousOn (c.length B.family.metric lambda) (Icc s t) ∧
      IntervalIntegrable (c.energy B.family.metric lambda) volume s t ∧
      (∀ v ∈ Icc s t, 0 ≤ c.energy B.family.metric lambda v) ∧
      (∫ v in s..t, c.energy B.family.metric lambda v) ≤
        Real.exp (B.B₀ * (t - s)) * c.length B.family.metric lambda s ∧
      (∀ v ∈ Icc s t,
        c.length B.family.metric lambda v ≤
          Real.exp (B.B₀ * (v - s)) * c.length B.family.metric lambda s)

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
theorem rampLengthEvolution_of_hasDerivAt_length
    (B : RicciBackground (I := I) (M := Q) D a b)
    (h : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 → ∀ c : ProductCurve Q,
      c.IsSolutionOn B.family.metric lambda (Icc a b) →
      ∀ s t : ℝ, a ≤ s → s ≤ t → t ≤ b →
        ContinuousOn (c.length B.family.metric lambda) (Icc s t) ∧
        IntervalIntegrable (c.energy B.family.metric lambda) volume s t ∧
        (∀ v ∈ Icc s t, 0 ≤ c.energy B.family.metric lambda v) ∧
        (∀ v ∈ Ioo s t, HasDerivAt (c.length B.family.metric lambda)
          (B.B₀ * c.length B.family.metric lambda v - c.energy B.family.metric lambda v) v) ∧
        (∀ v ∈ Icc s t,
          c.length B.family.metric lambda v ≤
            Real.exp (B.B₀ * (v - s)) * c.length B.family.metric lambda s)) :
    RampLengthEvolution (I := I) (Q := Q) (D := D) (a := a) (b := b) B := by
  intro lambda hlambda hlambda_one c hsol s t has hst htb
  obtain ⟨hcont, hint, hnn, hderiv, hgrowth⟩ :=
    h lambda hlambda hlambda_one c hsol s t has hst htb
  exact ⟨hcont, hint, hnn,
    DifferentialGeometry.Analysis.ODE.integral_le_exp_mul_of_hasDerivAt_sub B.B₀_nonneg hst
      hcont hderiv hint hnn (productCurve_length_nonneg B.family.metric lambda t c),
    hgrowth⟩

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
theorem rfs_rampProductBounds_of_length_evolution
    (B : RicciBackground (I := I) (M := Q) D a b)
    (hev : RampLengthEvolution (I := I) (Q := Q) (D := D) (a := a) (b := b) B)
    (hcurv : curveShorteningTotalCurvatureBound (I := I) (M := Q) (D := D) (a := a) (b := b) B) :
    RampProductBounds (I := I) (Q := Q) (D := D) (a := a) (b := b) B := by
  intro L Theta hL hTheta lambda hlambda hlambda_one c hsol hlen htot t ht
  have hexp : 0 ≤ Real.exp (B.B₀ * (t - a)) := Real.exp_nonneg _
  have hgrowth_at : c.length B.family.metric lambda t ≤
      Real.exp (B.B₀ * (t - a)) * c.length B.family.metric lambda a :=
    (hev lambda hlambda hlambda_one c hsol a t le_rfl ht.1 ht.2).2.2.2.2 t ⟨ht.1, le_rfl⟩
  have henergy : (∫ v in a..t, c.energy B.family.metric lambda v) ≤
      Real.exp (B.B₀ * (t - a)) * c.length B.family.metric lambda a :=
    (hev lambda hlambda hlambda_one c hsol a t le_rfl ht.1 ht.2).2.2.2.1
  have hreverse : c.length B.family.metric lambda b ≤
      Real.exp (B.B₀ * (b - t)) * c.length B.family.metric lambda t :=
    (hev lambda hlambda hlambda_one c hsol t b ht.1 ht.2 le_rfl).2.2.2.2 b ⟨ht.2, le_rfl⟩
  have htot_add : c.totalCurvature B.family.metric lambda t + c.length B.family.metric lambda t ≤
      Real.exp ((B.C + B.B₀) * (t - a)) * (Theta + L) := by
    refine (hcurv lambda hlambda hlambda_one c hsol t ht).trans ?_
    exact mul_le_mul_of_nonneg_left (add_le_add htot hlen) (Real.exp_nonneg _)
  exact ⟨hgrowth_at.trans (mul_le_mul_of_nonneg_left hlen hexp),
    hreverse,
    henergy.trans (mul_le_mul_of_nonneg_left hlen hexp),
    htot_add⟩


omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
theorem rfs_goodWindows_energy_of_length_evolution
    (B : RicciBackground (I := I) (M := Q) D a b) (L₀ : ℝ)
    (hev : RampLengthEvolution (I := I) (Q := Q) (D := D) (a := a) (b := b) B) :
    ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 → ∀ c : ProductCurve Q,
      c.IsSolutionOn B.family.metric lambda (Icc a b) →
      c.length B.family.metric lambda a ≤ L₀ →
      IntegrableOn (c.energy B.family.metric lambda) (Icc a b) volume ∧
        (∫ v in a..b, c.energy B.family.metric lambda v) ≤
          Real.exp (B.B₀ * (b - a)) * L₀ := by
  intro lambda hlambda hlambda_one c hsol hlen
  obtain ⟨-, hint, -, hbound, -⟩ :=
    hev lambda hlambda hlambda_one c hsol a b le_rfl B.lt.le le_rfl
  exact ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le B.lt.le).mp hint,
    hbound.trans (mul_le_mul_of_nonneg_left hlen (Real.exp_nonneg _))⟩

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
theorem rfs_finite_good_windows_of_length_evolution
    (B : RicciBackground (I := I) (M := Q) D a b)
    (L₀ Theta₀ : ℝ) (K : CurveShorteningRegularityInput B L₀ Theta₀)
    (hev : RampLengthEvolution (I := I) (Q := Q) (D := D) (a := a) (b := b) B)
    (hslice : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 → ∀ c : ProductCurve Q,
      c.IsSolutionOn B.family.metric lambda (Icc a b) →
      c.length B.family.metric lambda a ≤ L₀ →
      ∀ t ∈ Icc a b, c.SliceRegularity B.family.metric lambda t) :
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
  rfs_finite_good_windows_of_energy_bound B L₀ Theta₀ K
    (rfs_goodWindows_energy_of_length_evolution B L₀ hev) hslice

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
