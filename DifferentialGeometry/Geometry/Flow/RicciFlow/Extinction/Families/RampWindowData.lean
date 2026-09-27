import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.RampAngleWindow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.RampLengthEvolution



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

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
theorem rfs_ramp_window_data_of_length_evolution
    (B : RicciBackground (I := I) (M := Q) D a b)
    (L₀ Theta₀ ell eta threshold : ℝ)
    (K : CurveShorteningRegularityInput B L₀ Theta₀)
    (hev : RampLengthEvolution (I := I) (Q := Q) (D := D) (a := a) (b := b) B)
    (hslice : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 → ∀ c : ProductCurve Q,
      c.IsSolutionOn B.family.metric lambda (Icc a b) →
      c.length B.family.metric lambda a ≤ L₀ →
      ∀ t ∈ Icc a b, c.SliceRegularity B.family.metric lambda t)
    (hL₀ : 0 ≤ L₀) (hell : 0 < ell) (heta : 0 < eta) (hthreshold : 0 < threshold) :
    let R := min K.radius (min (Real.exp (-(B.B₀ * (b - a))) * ell / 2)
      (K.delta ^ 2 / threshold))
    ∃ lambda₀ : ℝ, 0 < lambda₀ ∧ lambda₀ ≤ 1 ∧
      (∀ (lambda : ℝ), 0 < lambda → lambda ≤ lambda₀ → ∀ c : ProductCurve Q,
        c.IsSolutionOn B.family.metric lambda (Icc a b) →
        c.IsRampOn B.family.metric lambda (Icc a b) → c.degree = 1 →
        c.length B.family.metric lambda a ≤ L₀ →
        c.totalCurvature B.family.metric lambda a ≤ Theta₀ →
        (∀ t ∈ Icc a b,
          Real.exp (-(B.B₀ * (b - a))) * ell ≤ c.length B.family.metric lambda t) →
        ∃ starts : Finset ℝ,
          goodWindowUnion starts (K.delta * R ^ 2) ⊆ Ioo a b ∧
          volume (Icc a b \ goodWindowUnion starts (K.delta * R ^ 2)) ≤
            ENNReal.ofReal (K.delta * R ^ 2 + Real.exp (B.B₀ * (b - a)) * L₀ / threshold) ∧
          ∀ x t, t ∈ goodWindowUnion starts (K.delta * R ^ 2) →
            0 < c.angle B.family.metric lambda x t ∧
            c.angle B.family.metric lambda x t ≤ eta) := by
  dsimp only
  set R : ℝ := min K.radius (min (Real.exp (-(B.B₀ * (b - a))) * ell / 2)
    (K.delta ^ 2 / threshold)) with hR
  have hRpos : 0 < R := by
    rw [hR]
    exact lt_min K.radius_pos
      (lt_min (div_pos (mul_pos (Real.exp_pos _) hell) (by norm_num))
        (div_pos (pow_pos K.delta_pos 2) hthreshold))
  have hdpos : 0 < K.delta * R ^ 2 := mul_pos K.delta_pos (pow_pos hRpos 2)
  have hdlt_one : K.delta < 1 := K.delta_lt_one
  set Kang : ℝ := Real.sqrt (2 * K.coefficient 0 / (K.delta * R ^ 2)) with hKang
  have hKangpos : 0 < Kang := by
    rw [hKang]
    exact Real.sqrt_pos.2 (div_pos (mul_pos (by norm_num) (K.coefficient_pos 0)) hdpos)
  obtain ⟨lambda₀, hl₀pos, hl₀one, hsmall⟩ :=
    exists_lambda_small_angle (ell := Real.exp (-(B.B₀ * (b - a))) * ell) (K := Kang) (eta := eta)
      (mul_pos (Real.exp_pos _) hell) hKangpos heta
  refine ⟨lambda₀, hl₀pos, hl₀one, ?_⟩
  intro lambda hlambda hle c hsol hramp hdeg hlen htc hlenlower
  rcases lt_or_ge (K.delta * R ^ 2) (b - a) with hdlt | hdle
  · obtain ⟨starts, _hmem, hsub, hvol, hcurv, _⟩ :=
      rfs_finite_good_windows_of_length_evolution B L₀ Theta₀ K hev hslice
        (Real.exp (-(B.B₀ * (b - a))) * ell) threshold (mul_pos (Real.exp_pos _) hell) hthreshold
        hdlt lambda hlambda (hle.trans hl₀one) c hsol hramp hdeg hlen htc hlenlower
    refine ⟨starts, ?_, ?_, ?_⟩
    · simpa only [localRegularityDelta, localRegularityRadius, hR] using hsub
    · simpa only [localRegularityDelta, localRegularityRadius, hR] using hvol
    · intro x t ht
      have hwsub : t ∈ Ioo a b := by
        simpa only [localRegularityDelta, localRegularityRadius, hR] using hsub ht
      have htIcc : t ∈ Icc a b := ⟨hwsub.1.le, hwsub.2.le⟩
      refine ⟨hramp.2 x t htIcc, ?_⟩
      have hsub' : (univ : Set ℝ) ×ˢ ({t} : Set ℝ) ⊆ univ ×ˢ Icc a b :=
        Set.prod_mono subset_rfl (singleton_subset_iff.mpr htIcc)
      have hsmooth : c.SmoothOn (I := I) {t} :=
        ⟨hsol.smooth.1.mono hsub', hsol.smooth.2.mono hsub'⟩
      have hramp' : c.IsRampOn (fun _ => B.family.metric t) lambda {t} := by
        constructor
        · intro z s hs
          rw [Set.mem_singleton_iff] at hs
          rw [hs]
          exact hramp.1 z t htIcc
        · intro z s hs
          rw [Set.mem_singleton_iff] at hs
          rw [hs]
          exact hramp.2 z t htIcc
      have hcurv' : ∀ z, c.curvature (fun _ => B.family.metric t) lambda z t ≤ Kang := by
        intro z
        have h := hcurv z t ht
        have heq : c.curvature (fun _ : ℝ => B.family.metric t) lambda z t =
            c.curvature B.family.metric lambda z t := rfl
        rw [heq]
        simpa only [localRegularityCoefficient, localRegularityDelta, localRegularityRadius, hKang,
          hR] using h
      have hlen' : Real.exp (-(B.B₀ * (b - a))) * ell ≤
          c.length (fun _ => B.family.metric t) lambda t := hlenlower t htIcc
      have hb := rfs_ramp_small_angle (B.family.metric t) c lambda t
        (Real.exp (-(B.B₀ * (b - a))) * ell) Kang hlambda (mul_pos (Real.exp_pos _) hell) hKangpos
        hdeg hsmooth hramp' hlen' hcurv' x
      exact le_trans hb (hsmall lambda hlambda hle)
  · refine ⟨∅, ?_, ?_, ?_⟩
    · intro t ht
      obtain ⟨w, hw, _⟩ := ht
      exact absurd hw (Finset.notMem_empty w)
    · have hg : goodWindowUnion (∅ : Finset ℝ) (K.delta * R ^ 2) = ∅ := by
        ext t
        simp [goodWindowUnion]
      rw [hg, Set.sdiff_empty, Real.volume_Icc]
      refine ENNReal.ofReal_le_ofReal ?_
      have hq : 0 ≤ Real.exp (B.B₀ * (b - a)) * L₀ / threshold :=
        div_nonneg (mul_nonneg (Real.exp_nonneg _) hL₀) hthreshold.le
      linarith only [hdle, hq]
    · intro x t ht
      obtain ⟨w, hw, _⟩ := ht
      exact absurd hw (Finset.notMem_empty w)

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
