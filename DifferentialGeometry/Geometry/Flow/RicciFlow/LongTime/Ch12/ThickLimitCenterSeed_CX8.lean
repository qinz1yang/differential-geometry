import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CanonicalNbhdP6Seed_S23

set_option autoImplicit false

/-!
# CH12-CX8: a fixed normalized backward window from a normalized seed

W2 is retained verbatim as an explicit input. The radius is chosen after its volume constant
and before the late-time threshold. The recent-surgery premise follows from the profile's
cutoff smallness and the monotonicity of its neck radius, as in S23's K2 argument.
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.LongTime Set Filter
open scoped Manifold ContDiff ENNReal Topology

namespace GC.LongTime.Ch12
universe u

/-- A single-time normalized seed supplies a uniform positive backward time and spatial radius.
Only W2 is assumed; in particular its recent-surgery condition is proved here. -/
theorem traced_window_of_seed_CX8 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hW2 : ∀ w : ℝ, 0 < w → ∃ T Λ b τ C : ℝ, 0 < T ∧ 1 ≤ Λ ∧ 0 < b ∧ 0 < τ ∧ 0 < C ∧
      τ * b ^ 2 < 1 / 2 ∧
      ∀ s : GC.LongTime.RegularSlice F.observation, T ≤ s.time →
      ∀ (p : (s.history.stageAt (sliceTop_S8 s)).Carrier) (r : ℝ), 0 < r →
        r ≤ b * Real.sqrt s.time →
        (∀ q ∈ riemannianBallOf (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s))
            s.time) p r,
          SectionalBoundedBelowAt (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s))
            s.time) q (-(r ^ 2)⁻¹)) →
        ENNReal.ofReal (w * r ^ 3) ≤ ballVolume (s.history.stageMetric
          (s.history.activeStage (sliceTop_S8 s)) s.time) p r →
        (∀ n (i : Fin (F.tower.history n).eventCount),
          (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time →
          ∀ h, Λ * (Hp.records n i).nominalRadius h ≤ r) →
        s.history.isTracedRegion (sliceTop_S8 s) p (2 * r) (τ * r ^ 2) (C / r ^ 2))
    {a v : ℝ} (ha : 0 < a) (hv : 0 < v) :
    ∃ b θ K T : ℝ, 0 < b ∧ b ≤ a ∧ 0 < θ ∧ θ < 1 / 2 ∧ 0 < K ∧ 0 < T ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time → ∀ p : s.stage.Carrier,
        HasNormalizedSeed_S13 s p a v →
        ∀ p' : (s.history.stageAt (sliceTop_S8 s)).Carrier, HEq p' p →
          s.history.isTracedRegion (sliceTop_S8 s) p' (2 * (b * Real.sqrt s.time))
            (θ * s.time) (K / s.time) := by
  obtain ⟨c, hc, hsd⟩ := seed_scale_down_S21.{u}
  obtain ⟨T1, Λ, b, τ, C, hT1, hΛ, hb, hτ, hC, hτb, hW⟩ := hW2 (c * v) (mul_pos hc hv)
  let b1 := min a b
  have hb1 : 0 < b1 := lt_min ha hb
  have hb1a : b1 ≤ a := min_le_left _ _
  have hb1b : b1 ≤ b := min_le_right _ _
  have hΛ0 : 0 < Λ := by linarith
  let N0 := Hp.parameters.neckRadius 0
  have hN0 : 0 < N0 := Hp.parameters.neckRadius_pos 0 le_rfl
  let ε := b1 / (Λ * N0)
  have hε : 0 < ε := by positivity
  obtain ⟨T2, hT2, hrecent⟩ := Hp.recent_cutoff_smallness ε hε
  refine ⟨b1, τ * b1 ^ 2, C / b1 ^ 2, max (max T1 T2) 1,
    hb1, hb1a, by positivity, ?_, by positivity, lt_max_of_lt_right one_pos, ?_⟩
  · exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb1.le hb1b 2) hτ.le).trans_lt hτb
  intro s hs p hseed
  have ht := s.positive
  have hT1s : T1 ≤ s.time := ((le_max_left _ _).trans (le_max_left _ _)).trans hs
  have hT2s : T2 ≤ s.time := ((le_max_right _ _).trans (le_max_left _ _)).trans hs
  have h1s : 1 ≤ s.time := (le_max_right _ _).trans hs
  have hst : 1 ≤ Real.sqrt s.time := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt h1s
  have hsqrt : 0 < Real.sqrt s.time := Real.sqrt_pos.mpr ht
  have hsq : Real.sqrt s.time ^ 2 = s.time := Real.sq_sqrt ht.le
  obtain ⟨hsec, hvol⟩ := physSeed_S23 s p ha hseed
  have hgen : ∀ (j : Fin (s.history.eventCount + 1))
      (hj : s.history.activeStage (sliceTop_S8 s) = j) (p : (s.history.stage j).Carrier),
      (∀ q ∈ riemannianBallOf (s.history.stageMetric j s.time) p (a * Real.sqrt s.time),
        SectionalBoundedBelowAt (s.history.stageMetric j s.time) q
          (-((a * Real.sqrt s.time) ^ 2)⁻¹)) →
      ENNReal.ofReal (v * (a * Real.sqrt s.time) ^ 3) ≤
        ballVolume (s.history.stageMetric j s.time) p (a * Real.sqrt s.time) →
      ∀ p' : (s.history.stageAt (sliceTop_S8 s)).Carrier, HEq p' p →
        s.history.isTracedRegion (sliceTop_S8 s) p' (2 * (b1 * Real.sqrt s.time))
          ((τ * b1 ^ 2) * s.time) ((C / b1 ^ 2) / s.time) := by
    intro j hj p hsec hvol
    obtain ⟨hs1, hv1⟩ := hsd _ (s.history.stageMetric j s.time) p v
      (a * Real.sqrt s.time) (b1 * Real.sqrt s.time) hv (mul_pos hb1 hsqrt)
      (mul_le_mul_of_nonneg_right hb1a hsqrt.le) hsec hvol
    subst hj
    intro p' hp'
    cases hp'
    have hrec : ∀ n (i : Fin (F.tower.history n).eventCount),
        (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time →
        ∀ h, Λ * (Hp.records n i).nominalRadius h ≤ b1 * Real.sqrt s.time := by
      intro n i hi h
      have h1 := hrecent s.time hT2s n i hi h
      have h2 : Hp.parameters.neckRadius s.time ≤ N0 :=
        Hp.radius_antitone (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht.le) ht.le
      have h3 := mul_le_mul_of_nonneg_left
        (h1.trans (mul_le_mul_of_nonneg_left h2 hε.le)) hΛ0.le
      have h4 : Λ * (ε * N0) = b1 := by dsimp [ε]; field_simp
      exact (h4 ▸ h3).trans (by simpa using mul_le_mul_of_nonneg_left hst hb1.le)
    have htr := hW s hT1s p (b1 * Real.sqrt s.time) (mul_pos hb1 hsqrt)
      (mul_le_mul_of_nonneg_right hb1b hsqrt.le) hs1 hv1 hrec
    simpa only [mul_pow, hsq, ← mul_assoc, div_mul_eq_div_div] using htr
  exact hgen (Fin.last _) s.history.activeStage_at_horizon p hsec hvol

end GC.LongTime.Ch12
