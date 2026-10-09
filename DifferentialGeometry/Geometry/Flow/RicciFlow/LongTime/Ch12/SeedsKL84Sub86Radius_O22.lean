import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84Glue_O12

/-!
# CH12-O22 G1: radius monotonicity adapters `r0 / 8 ⇒ r0 / 40`

`[FROZEN v2] CH12-O22` replaces the traced-region radius `r0 / 8` of KL Sub86.3 / Lemma 86.2
(`[FROZEN] CH12-O12` and its addendum) by `r0 / 40`.  A traced region is monotone in its radius,
so every statement in the old `r0 / 8` form implies the new `r0 / 40` form; this file records the
pointwise lemma and the two statement-level adapters.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.VolumeComparison DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow

namespace GC.LongTime.Ch12

universe u

/-- Pointwise radius monotonicity: a traced region of radius `r0 / 8` contains the traced region
of radius `r0 / 40` with the same depth and curvature bound. -/
theorem tracedRegion_mono_radius_O22 {H : ObservedHistory.{u}} {u : Icc (0 : ℝ) H.horizon}
    {p : (H.stageAt u).Carrier} {r0 τ K : ℝ} (h : H.isTracedRegion u p (r0 / 8) τ K)
    (hr0 : 0 < r0) : H.isTracedRegion u p (r0 / 40) τ K :=
  h.mono_radius (by positivity) (by linarith)

/-- `hG2c` of `[FROZEN] CH12-O12` (radius `r0 / 8`) implies `hG2c v2` of `[FROZEN v2] CH12-O22`
(radius `r0 / 40`). -/
theorem hG2c_v2_of_v1_O22 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hG2c : ∃ ε C₁ K τ₁ τ₂ b T : ℝ, 0 < ε ∧ 1 ≤ C₁ ∧ 0 < K ∧ 0 < τ₁ ∧ 0 < τ₂ ∧ 0 < b ∧ 0 < T ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ (x0 : (s.history.stageAt (sliceTop_S8 s)).Carrier) (r0 : ℝ), 0 < r0 →
        r0 ≤ b * Real.sqrt s.time →
        (∀ n (i : Fin (F.tower.history n).eventCount),
          (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time →
          ∀ h, C₁ * (Hp.records n i).nominalRadius h ≤ r0) →
        (∀ q ∈ riemannianBallOf
            (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) x0 r0,
          SectionalBoundedBelowAt
            (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time)
            q (-(r0 ^ 2)⁻¹)) →
        (∀ z ∈ riemannianBallOf
            (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) x0 r0,
          ∀ ρ : ℝ, 0 < ρ → ρ ≤ r0 →
            ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * ρ ^ 3) ≤
              ballVolume (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time)
                z ρ) →
        ∃ (a : Icc (0 : ℝ) s.history.horizon) (hat : a ≤ sliceTop_S8 s)
          (X : BackwardPointTrace s.history (s.history.activeStage a)
            (s.history.activeStage (sliceTop_S8 s)) (s.history.activeStage_mono hat) x0),
          (a : ℝ) = s.time - τ₁ * r0 ^ 2 ∧
          ∀ (u : Icc (0 : ℝ) s.history.horizon) (hau : a ≤ u) (hut : u ≤ sliceTop_S8 s),
            s.history.isTracedRegion u
              (X.point (s.history.activeStage u) (s.history.activeStage_mono hau)
                (s.history.activeStage_mono hut))
              (r0 / 8) (τ₂ * r0 ^ 2) (K * (r0 ^ 2)⁻¹)) :
    ∃ ε C₁ K τ₁ τ₂ b T : ℝ, 0 < ε ∧ 1 ≤ C₁ ∧ 0 < K ∧ 0 < τ₁ ∧ 0 < τ₂ ∧ 0 < b ∧ 0 < T ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ (x0 : (s.history.stageAt (sliceTop_S8 s)).Carrier) (r0 : ℝ), 0 < r0 →
        r0 ≤ b * Real.sqrt s.time →
        (∀ n (i : Fin (F.tower.history n).eventCount),
          (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time →
          ∀ h, C₁ * (Hp.records n i).nominalRadius h ≤ r0) →
        (∀ q ∈ riemannianBallOf
            (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) x0 r0,
          SectionalBoundedBelowAt
            (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time)
            q (-(r0 ^ 2)⁻¹)) →
        (∀ z ∈ riemannianBallOf
            (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) x0 r0,
          ∀ ρ : ℝ, 0 < ρ → ρ ≤ r0 →
            ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * ρ ^ 3) ≤
              ballVolume (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time)
                z ρ) →
        ∃ (a : Icc (0 : ℝ) s.history.horizon) (hat : a ≤ sliceTop_S8 s)
          (X : BackwardPointTrace s.history (s.history.activeStage a)
            (s.history.activeStage (sliceTop_S8 s)) (s.history.activeStage_mono hat) x0),
          (a : ℝ) = s.time - τ₁ * r0 ^ 2 ∧
          ∀ (u : Icc (0 : ℝ) s.history.horizon) (hau : a ≤ u) (hut : u ≤ sliceTop_S8 s),
            s.history.isTracedRegion u
              (X.point (s.history.activeStage u) (s.history.activeStage_mono hau)
                (s.history.activeStage_mono hut))
              (r0 / 40) (τ₂ * r0 ^ 2) (K * (r0 ^ 2)⁻¹) := by
  obtain ⟨ε, C₁, K, τ₁, τ₂, b, T, hε, hC₁, hK, hτ₁, hτ₂, hb, hT, hc⟩ := hG2c
  refine ⟨ε, C₁, K, τ₁, τ₂, b, T, hε, hC₁, hK, hτ₁, hτ₂, hb, hT, ?_⟩
  intro s hs x0 r0 hr0 hrb hrec hsec hvol
  obtain ⟨a, hat, X, haeq, hTF⟩ := hc s hs x0 r0 hr0 hrb hrec hsec hvol
  exact ⟨a, hat, X, haeq, fun u hau hut => tracedRegion_mono_radius_O22 (hTF u hau hut) hr0⟩

/-- The `sub86_3` body of `[FROZEN] CH12-O12 addendum` (radius `r0 / 8`, `r0 ≤ neckRadius`)
implies the `sub86_3` body of `[FROZEN v2] CH12-O22` (radius `r0 / 40`). -/
theorem sub86_3_v2_of_v1_O22 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (h86 : ∃ ε C₁ K τ₁ τ₂ T : ℝ, 0 < ε ∧ 1 ≤ C₁ ∧ 0 < K ∧ 0 < τ₁ ∧ 0 < τ₂ ∧ 0 < T ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ (x0 : (s.history.stageAt (sliceTop_S8 s)).Carrier) (r0 : ℝ), 0 < r0 →
        r0 ≤ Hp.parameters.neckRadius s.time →
        (∀ n (i : Fin (F.tower.history n).eventCount),
          (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time →
          ∀ h, C₁ * (Hp.records n i).nominalRadius h ≤ r0) →
        (∀ q ∈ riemannianBallOf
            (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) x0 r0,
          SectionalBoundedBelowAt
            (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time)
            q (-(r0 ^ 2)⁻¹)) →
        (∀ z ∈ riemannianBallOf
            (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) x0 r0,
          ∀ ρ : ℝ, 0 < ρ → ρ ≤ r0 →
            ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * ρ ^ 3) ≤
              ballVolume (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time)
                z ρ) →
        ∃ (a : Icc (0 : ℝ) s.history.horizon) (hat : a ≤ sliceTop_S8 s)
          (X : BackwardPointTrace s.history (s.history.activeStage a)
            (s.history.activeStage (sliceTop_S8 s)) (s.history.activeStage_mono hat) x0),
          (a : ℝ) = s.time - τ₁ * r0 ^ 2 ∧
          ∀ (u : Icc (0 : ℝ) s.history.horizon) (hau : a ≤ u) (hut : u ≤ sliceTop_S8 s),
            s.history.isTracedRegion u
              (X.point (s.history.activeStage u) (s.history.activeStage_mono hau)
                (s.history.activeStage_mono hut))
              (r0 / 8) (τ₂ * r0 ^ 2) (K * (r0 ^ 2)⁻¹)) :
    ∃ ε C₁ K τ₁ τ₂ T : ℝ, 0 < ε ∧ 1 ≤ C₁ ∧ 0 < K ∧ 0 < τ₁ ∧ 0 < τ₂ ∧ 0 < T ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ (x0 : (s.history.stageAt (sliceTop_S8 s)).Carrier) (r0 : ℝ), 0 < r0 →
        r0 ≤ Hp.parameters.neckRadius s.time →
        (∀ n (i : Fin (F.tower.history n).eventCount),
          (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time →
          ∀ h, C₁ * (Hp.records n i).nominalRadius h ≤ r0) →
        (∀ q ∈ riemannianBallOf
            (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) x0 r0,
          SectionalBoundedBelowAt
            (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time)
            q (-(r0 ^ 2)⁻¹)) →
        (∀ z ∈ riemannianBallOf
            (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) x0 r0,
          ∀ ρ : ℝ, 0 < ρ → ρ ≤ r0 →
            ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * ρ ^ 3) ≤
              ballVolume (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time)
                z ρ) →
        ∃ (a : Icc (0 : ℝ) s.history.horizon) (hat : a ≤ sliceTop_S8 s)
          (X : BackwardPointTrace s.history (s.history.activeStage a)
            (s.history.activeStage (sliceTop_S8 s)) (s.history.activeStage_mono hat) x0),
          (a : ℝ) = s.time - τ₁ * r0 ^ 2 ∧
          ∀ (u : Icc (0 : ℝ) s.history.horizon) (hau : a ≤ u) (hut : u ≤ sliceTop_S8 s),
            s.history.isTracedRegion u
              (X.point (s.history.activeStage u) (s.history.activeStage_mono hau)
                (s.history.activeStage_mono hut))
              (r0 / 40) (τ₂ * r0 ^ 2) (K * (r0 ^ 2)⁻¹) := by
  obtain ⟨ε, C₁, K, τ₁, τ₂, T, hε, hC₁, hK, hτ₁, hτ₂, hT, hc⟩ := h86
  refine ⟨ε, C₁, K, τ₁, τ₂, T, hε, hC₁, hK, hτ₁, hτ₂, hT, ?_⟩
  intro s hs x0 r0 hr0 hrn hrec hsec hvol
  obtain ⟨a, hat, X, haeq, hTF⟩ := hc s hs x0 r0 hr0 hrn hrec hsec hvol
  exact ⟨a, hat, X, haeq, fun u hau hut => tracedRegion_mono_radius_O22 (hTF u hau hut) hr0⟩

end GC.LongTime.Ch12
