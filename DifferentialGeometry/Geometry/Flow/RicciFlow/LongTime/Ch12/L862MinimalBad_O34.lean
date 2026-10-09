import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862Guard_O28
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862TowerFamily_O28
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862KappaCert_O28
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862Selection_CX12
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862TraceFamily_CX12

/-!
# CH12-O34 G1: the minimal-bad-ball argument of KL Lemma 86.2 inside one tower history

`[FROZEN v4] CH12-O34` (lead ruling after external review R4, D-R4-5).  KL Lemma 86.2 (`hG2c`,
κ-cert form of `[FROZEN v3] CH12-O28`) from ONE base+step contract `hBS` with common constants
`ε θ C K τ₁ τ₂ κ Λ b T`: base (Sublemma 86.3 below the neck scale) and step (Sublemma 86.6: a ball
above the neck scale all of whose children are good is good).  The bad set lives in the single
tower history `N := sliceTowerHistory_CX2 s` (FINDING 2 of `[FROZEN] CH12-O28`), on the domain
`u ≤ t₀`, `t₀ / 2 ≤ u - Λ r ^ 2`, `θ · neck t₀ ≤ r ≤ b √u`; there every window guard is
automatic (`guardHalf_of_neck_fraction_O28` at `t₀`).  No minimum is assumed attained: the bad
radii have the positive floor `θ · neck t₀`, and `exists_bad_without_smaller_predecessor_CX12`
(proved, via the infimum `r_*` and a bad radius `< r_* / θ`) gives a bad ball all of whose
children are good; base or step then makes it good.
-/
set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.VolumeComparison DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- Abstract minimal-bad-element induction (S1): if every element of the domain is good as soon
as all domain elements that are not later and at most `θ` times smaller are good, and the domain
has a positive radius floor, then every element of the domain is good. -/
theorem minimal_bad_induction_O34 {ι : Type*} (time radius : ι → ℝ) (D G : ι → Prop)
    {ρ θ : ℝ} (hρ : 0 < ρ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (htime : ∀ i, D i → 0 ≤ time i) (hfloor : ∀ i, D i → ρ ≤ radius i)
    (hstep : ∀ i, D i →
      (∀ j, time j ≤ time i → 0 ≤ radius j → radius j ≤ θ * radius i → D j → G j) → G i) :
    ∀ i, D i → G i := by
  by_contra hcon
  push Not at hcon
  obtain ⟨i0, hDi0, hGi0⟩ := hcon
  obtain ⟨i, ⟨hDi, hGi⟩, hmin⟩ := exists_bad_without_smaller_predecessor_CX12 time radius
    {i | D i ∧ ¬ G i} ⟨i0, hDi0, hGi0⟩ hρ hθ hθ1 (fun i hi => htime i hi.1)
    (fun i hi => hfloor i hi.1)
  exact hGi (hstep i hDi fun j hj hr hrj hDj => by_contra fun hGj => hmin j hj hr hrj ⟨hDj, hGj⟩)

/-- The minimal-bad-element induction over the balls `(v, y, r)` of one observed history
(curried form of `minimal_bad_induction_O34`, key `v + Λ r ^ 2` handled by the caller). -/
theorem minimal_bad_history_O34 (H : ObservedHistory.{u})
    (D G : ∀ v : Icc (0 : ℝ) H.horizon, (H.stageAt v).Carrier → ℝ → Prop) {ρ θ : ℝ}
    (hρ : 0 < ρ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (hfloor : ∀ v y r, D v y r → ρ ≤ r)
    (hstep : ∀ v y r, D v y r →
      (∀ (w : Icc (0 : ℝ) H.horizon) (z : (H.stageAt w).Carrier) (r' : ℝ), (w : ℝ) ≤ v →
        0 ≤ r' → r' ≤ θ * r → D w z r' → G w z r') → G v y r) :
    ∀ v y r, D v y r → G v y r := fun v y r hD =>
  minimal_bad_induction_O34 (ι := Σ v : Icc (0 : ℝ) H.horizon, (H.stageAt v).Carrier × ℝ)
    (fun i => (i.1 : ℝ)) (fun i => i.2.2) (fun i => D i.1 i.2.1 i.2.2)
    (fun i => G i.1 i.2.1 i.2.2) hρ hθ hθ1 (fun i _ => i.1.2.1) (fun _ hi => hfloor _ _ _ hi)
    (fun _ hi hIH => hstep _ _ _ hi fun w z r' hw hr' hrr hD' => hIH ⟨w, z, r'⟩ hw hr' hrr hD')
    ⟨v, y, r⟩ hD

/-- Monotonicity of the "good ball" conclusion in its constants (later start, smaller traced
radius and depth, larger curvature bound), via `traced_family_mono_CX12`. -/
theorem good_mono_O34 {H : ObservedHistory.{u}} {U : Icc (0 : ℝ) H.horizon}
    {x : (H.stageAt U).Carrier} {r κ τ₁ τ₂ K κ' τ₁' τ₂' K' : ℝ} (hr : 0 < r)
    (hκ' : 0 < κ') (hκ : κ' ≤ κ) (hτ₁' : 0 < τ₁') (hτ₁ : τ₁' ≤ τ₁) (hτ₂' : 0 < τ₂')
    (hτ₂ : τ₂' ≤ τ₂) (hK : 0 ≤ K) (hKK : K ≤ K')
    (hG : ∃ (a : Icc (0 : ℝ) H.horizon) (hau : a ≤ U)
      (X : BackwardPointTrace H (H.activeStage a) (H.activeStage U) (H.activeStage_mono hau) x),
      (a : ℝ) = U - τ₁ * r ^ 2 ∧
      ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvu : v ≤ U),
        H.isTracedRegion v (X.point (H.activeStage v) (H.activeStage_mono hav)
          (H.activeStage_mono hvu)) (κ * r) (τ₂ * r ^ 2) (K * (r ^ 2)⁻¹)) :
    ∃ (a : Icc (0 : ℝ) H.horizon) (hau : a ≤ U)
      (X : BackwardPointTrace H (H.activeStage a) (H.activeStage U) (H.activeStage_mono hau) x),
      (a : ℝ) = U - τ₁' * r ^ 2 ∧
      ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvu : v ≤ U),
        H.isTracedRegion v (X.point (H.activeStage v) (H.activeStage_mono hav)
          (H.activeStage_mono hvu)) (κ' * r) (τ₂' * r ^ 2) (K' * (r ^ 2)⁻¹) := by
  obtain ⟨a, hau, X, ha, hfam⟩ := hG
  have hr2 : 0 < r ^ 2 := by positivity
  have hle : (a : ℝ) ≤ (U : ℝ) - τ₁' * r ^ 2 := by
    rw [ha]; nlinarith
  have hb0 : 0 ≤ (U : ℝ) - τ₁' * r ^ 2 := a.2.1.trans hle
  have hbU' : (U : ℝ) - τ₁' * r ^ 2 ≤ U := by nlinarith
  let b : Icc (0 : ℝ) H.horizon := ⟨(U : ℝ) - τ₁' * r ^ 2, hb0, hbU'.trans U.2.2⟩
  have hab : a ≤ b := hle
  have hbU : b ≤ U := hbU'
  refine ⟨b, hbU, X.restrictFirst (H.activeStage_mono hab) (H.activeStage_mono hbU), rfl, ?_⟩
  exact traced_family_mono_CX12 (hat := hau) X hfam hab hbU (by positivity)
    (mul_le_mul_of_nonneg_right hκ hr.le) (by positivity)
    (mul_le_mul_of_nonneg_right hτ₂ hr2.le) (by positivity)
    (mul_le_mul_of_nonneg_right hKK (inv_nonneg.mpr hr2.le))

/-- S0 + S4 of `hG2c_of_baseStep_O34`: the original slice ball, pushed to `N`, is good — by the
base clause below the neck scale, by the induction `hind` above it — and the traced family is
brought back to the slice (`tracedFamily_slice_of_tower_O28`). -/
theorem hG2c_root_O34 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (s : RegularSlice F.observation) {ε θ C K τ₁ τ₂ κ Λ b T : ℝ} (hθ1 : θ ≤ 1 / 2)
    (hΛ : 0 < Λ) (hΛb : Λ * b ^ 2 ≤ 1 / 2) (hTs : T ≤ s.time)
    (hbase :
      ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ (u : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon), T ≤ (u : ℝ) → (u : ℝ) ≤ s.time →
        (0 < (u : ℝ) ∧ (u : ℝ) ∉ F.observation.eventTimes) →
      ∀ (x : ((sliceTowerHistory_CX2 s).stageAt u).Carrier) (r : ℝ), 0 < r → r ≤ Hp.parameters.neckRadius (u : ℝ) →
        r ≤ b * Real.sqrt u →
        (∀ m (i : Fin (F.tower.history m).eventCount),
          (F.tower.history m).time i.succ ∈ Icc ((u : ℝ) - Λ * r ^ 2) u →
          ∀ h, C * (Hp.records m i).nominalRadius h ≤ r) →
        (∀ q ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage u) u) x r,
          SectionalBoundedBelowAt ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage u) u) q (-(r ^ 2)⁻¹)) →
        (∀ z ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage u) u) x r,
          ∀ ρ : ℝ, 0 < ρ → ρ ≤ r →
            ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * ρ ^ 3) ≤
              ballVolume ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage u) u) z ρ) →
        (∃ (a : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (hau : a ≤ u)
          (X : BackwardPointTrace (sliceTowerHistory_CX2 s)
            ((sliceTowerHistory_CX2 s).activeStage a) ((sliceTowerHistory_CX2 s).activeStage u)
            ((sliceTowerHistory_CX2 s).activeStage_mono hau) x),
          (a : ℝ) = u - τ₁ * r ^ 2 ∧
          ∀ (w : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (haw : a ≤ w) (hwu : w ≤ u),
            (sliceTowerHistory_CX2 s).isTracedRegion w
              (X.point ((sliceTowerHistory_CX2 s).activeStage w) ((sliceTowerHistory_CX2 s).activeStage_mono haw)
                ((sliceTowerHistory_CX2 s).activeStage_mono hwu))
              (κ * r) (τ₂ * r ^ 2) (K * (r ^ 2)⁻¹)))
    (hind : ∀ (u : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (x : ((sliceTowerHistory_CX2 s).stageAt u).Carrier) (r : ℝ),
      ((u : ℝ) ≤ s.time ∧ s.time / 2 ≤ (u : ℝ) - Λ * r ^ 2 ∧
      θ * Hp.parameters.neckRadius s.time ≤ r ∧ r ≤ b * Real.sqrt u ∧ (0 < (u : ℝ) ∧ (u : ℝ) ∉ F.observation.eventTimes) ∧
      (∀ q ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage u) u) x r,
        SectionalBoundedBelowAt ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage u) u) q (-(r ^ 2)⁻¹)) ∧
      (∀ z ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage u) u) x r,
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ r →
          ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * ρ ^ 3) ≤
            ballVolume ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage u) u) z ρ)) →
      (∃ (a : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (hau : a ≤ u)
        (X : BackwardPointTrace (sliceTowerHistory_CX2 s)
          ((sliceTowerHistory_CX2 s).activeStage a) ((sliceTowerHistory_CX2 s).activeStage u)
          ((sliceTowerHistory_CX2 s).activeStage_mono hau) x),
        (a : ℝ) = u - τ₁ * r ^ 2 ∧
        ∀ (w : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (haw : a ≤ w) (hwu : w ≤ u),
          (sliceTowerHistory_CX2 s).isTracedRegion w
            (X.point ((sliceTowerHistory_CX2 s).activeStage w) ((sliceTowerHistory_CX2 s).activeStage_mono haw)
              ((sliceTowerHistory_CX2 s).activeStage_mono hwu))
            (κ * r) (τ₂ * r ^ 2) (K * (r ^ 2)⁻¹))) :
    ∀ (x0 : (s.history.stageAt (sliceTop_S8 s)).Carrier) (r0 : ℝ), 0 < r0 →
        r0 ≤ b * Real.sqrt s.time →
        (∀ n (i : Fin (F.tower.history n).eventCount),
          (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time →
          ∀ h, C * (Hp.records n i).nominalRadius h ≤ r0) →
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
              (κ * r0) (τ₂ * r0 ^ 2) (K * (r0 ^ 2)⁻¹) := by
  intro x0 r0 hr0 hr0b hguard hsec hvol
  have ht₀ : 0 < s.time := s.positive
  have hneck : 0 < Hp.parameters.neckRadius s.time := Hp.parameters.neckRadius_pos _ ht₀.le
  have hsecN := sectional_slice_to_tower_O28 s (sliceTop_S8 s) x0 r0 _ hsec
  have hvolN := volume_slice_to_tower_O28 s (sliceTop_S8 s) x0 r0 ε hvol
  have hr0sq : r0 ^ 2 ≤ b ^ 2 * s.time := by
    have h1 : r0 ^ 2 ≤ (b * Real.sqrt s.time) ^ 2 := pow_le_pow_left₀ hr0.le hr0b 2
    rwa [mul_pow, Real.sq_sqrt ht₀.le] at h1
  have hΛr0 : Λ * r0 ^ 2 ≤ s.time / 2 := by
    have h1 : Λ * r0 ^ 2 ≤ Λ * (b ^ 2 * s.time) := mul_le_mul_of_nonneg_left hr0sq hΛ.le
    nlinarith
  have hUval : (((restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) (sliceTop_S8 s)) : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) : ℝ) = s.time := rfl
  have hregU : 0 < (((restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) (sliceTop_S8 s)) : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) : ℝ) ∧
      (((restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) (sliceTop_S8 s)) : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) : ℝ) ∉ F.observation.eventTimes := ⟨ht₀, s.regular⟩
  have hGoodN : (∃ (a : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (hau : a ≤ (restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) (sliceTop_S8 s)))
          (X : BackwardPointTrace (sliceTowerHistory_CX2 s)
            ((sliceTowerHistory_CX2 s).activeStage a) ((sliceTowerHistory_CX2 s).activeStage (restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) (sliceTop_S8 s)))
            ((sliceTowerHistory_CX2 s).activeStage_mono hau) (restrictPoint_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) (sliceTop_S8 s) x0)),
          (a : ℝ) = (restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) (sliceTop_S8 s)) - τ₁ * r0 ^ 2 ∧
          ∀ (w : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (haw : a ≤ w) (hwu : w ≤ (restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) (sliceTop_S8 s))),
            (sliceTowerHistory_CX2 s).isTracedRegion w
              (X.point ((sliceTowerHistory_CX2 s).activeStage w) ((sliceTowerHistory_CX2 s).activeStage_mono haw)
                ((sliceTowerHistory_CX2 s).activeStage_mono hwu))
              (κ * r0) (τ₂ * r0 ^ 2) (K * (r0 ^ 2)⁻¹)) := by
    by_cases hr0n : r0 ≤ Hp.parameters.neckRadius s.time
    · exact hbase s hTs (restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) (sliceTop_S8 s)) hTs le_rfl hregU (restrictPoint_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) (sliceTop_S8 s) x0) r0 hr0 hr0n hr0b
        (guardWin_of_guardHalf_O28 Hp hΛr0 hguard) hsecN hvolN
    · push Not at hr0n
      have hθn : θ * Hp.parameters.neckRadius s.time ≤ r0 :=
        le_trans (mul_le_of_le_one_left hneck.le (by linarith)) hr0n.le
      have hwinU : s.time / 2 ≤ (((restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) (sliceTop_S8 s)) : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) : ℝ) - Λ * r0 ^ 2 := by
        rw [hUval]; linarith
      have hrbU : r0 ≤ b * Real.sqrt (((restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) (sliceTop_S8 s)) : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) : ℝ) := by
        rw [hUval]; exact hr0b
      exact hind (restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) (sliceTop_S8 s)) (restrictPoint_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) (sliceTop_S8 s) x0) r0 ⟨hUval.le, hwinU, hθn, hrbU, hregU, hsecN, hvolN⟩
  obtain ⟨a', ha'U, X', ha', hfam'⟩ := hGoodN
  exact tracedFamily_slice_of_tower_O28 s ⟨(a' : ℝ), a'.2.1, le_trans ha'U (sliceTop_S8 s).2.2⟩
    ha'U ha' X' hfam'

/-- **KL Lemma 86.2 (κ-cert form of `[FROZEN v3] CH12-O28`)** from the base+step contract `hBS`
of `[FROZEN v4] CH12-O34` (common constants): minimal-bad-ball argument inside
`sliceTowerHistory_CX2 s`.  Output constants: `ε C K τ₁ τ₂ κ b` of `hBS`, and
`T_out := max (2 T) T_g` with `T_g` the recent-cutoff threshold of `guardHalf_of_neck_fraction_O28`
for `(C, θ)` (i.e. `δ ≤ θ / C` after `T_g`). -/
theorem hG2c_of_baseStep_O34 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hBS : ∃ ε θ C K τ₁ τ₂ κ Λ b T : ℝ, 0 < ε ∧ ε ≤ 1 / 2 ∧ 0 < θ ∧ θ ≤ 1 / 2 ∧ 1 ≤ C ∧ 0 < K ∧
      0 < τ₁ ∧ 0 < τ₂ ∧ 0 < κ ∧ τ₁ + τ₂ ≤ Λ ∧ 0 < b ∧ b ≤ 1 / (2 * (Λ + τ₁ + τ₂ + 1)) ∧ 0 < T ∧
      2 * Λ * Hp.parameters.neckRadius 0 ^ 2 ≤ T ∧
     (∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ (u : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon), T ≤ (u : ℝ) → (u : ℝ) ≤ s.time →
        (0 < (u : ℝ) ∧ (u : ℝ) ∉ F.observation.eventTimes) →
      ∀ (x : ((sliceTowerHistory_CX2 s).stageAt u).Carrier) (r : ℝ), 0 < r → r ≤ Hp.parameters.neckRadius (u : ℝ) →
        r ≤ b * Real.sqrt u →
        (∀ m (i : Fin (F.tower.history m).eventCount),
          (F.tower.history m).time i.succ ∈ Icc ((u : ℝ) - Λ * r ^ 2) u →
          ∀ h, C * (Hp.records m i).nominalRadius h ≤ r) →
        (∀ q ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage u) u) x r,
          SectionalBoundedBelowAt ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage u) u) q (-(r ^ 2)⁻¹)) →
        (∀ z ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage u) u) x r,
          ∀ ρ : ℝ, 0 < ρ → ρ ≤ r →
            ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * ρ ^ 3) ≤
              ballVolume ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage u) u) z ρ) →
        (∃ (a : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (hau : a ≤ u)
          (X : BackwardPointTrace (sliceTowerHistory_CX2 s)
            ((sliceTowerHistory_CX2 s).activeStage a) ((sliceTowerHistory_CX2 s).activeStage u)
            ((sliceTowerHistory_CX2 s).activeStage_mono hau) x),
          (a : ℝ) = u - τ₁ * r ^ 2 ∧
          ∀ (w : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (haw : a ≤ w) (hwu : w ≤ u),
            (sliceTowerHistory_CX2 s).isTracedRegion w
              (X.point ((sliceTowerHistory_CX2 s).activeStage w) ((sliceTowerHistory_CX2 s).activeStage_mono haw)
                ((sliceTowerHistory_CX2 s).activeStage_mono hwu))
              (κ * r) (τ₂ * r ^ 2) (K * (r ^ 2)⁻¹))) ∧
     (∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ (u : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon), T ≤ (u : ℝ) → (u : ℝ) ≤ s.time →
        (0 < (u : ℝ) ∧ (u : ℝ) ∉ F.observation.eventTimes) →
      ∀ (x : ((sliceTowerHistory_CX2 s).stageAt u).Carrier) (r : ℝ), 0 < r → Hp.parameters.neckRadius (u : ℝ) < r →
        r ≤ b * Real.sqrt u →
        (∀ m (i : Fin (F.tower.history m).eventCount),
          (F.tower.history m).time i.succ ∈ Icc ((u : ℝ) - Λ * r ^ 2) u →
          ∀ h, C * (Hp.records m i).nominalRadius h ≤ r) →
        (∀ q ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage u) u) x r,
          SectionalBoundedBelowAt ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage u) u) q (-(r ^ 2)⁻¹)) →
        (∀ z ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage u) u) x r,
          ∀ ρ : ℝ, 0 < ρ → ρ ≤ r →
            ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * ρ ^ 3) ≤
              ballVolume ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage u) u) z ρ) →
        (∀ (v : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon)
          (y : ((sliceTowerHistory_CX2 s).stageAt v).Carrier) (r' : ℝ), v ≤ u →
          (u : ℝ) - Λ * r ^ 2 ≤ v - Λ * r' ^ 2 → θ * Hp.parameters.neckRadius (u : ℝ) ≤ r' →
          r' ≤ θ * r → (0 < (v : ℝ) ∧ (v : ℝ) ∉ F.observation.eventTimes) → r' ≤ b * Real.sqrt v →
          (∀ q ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage v) v) y r',
            SectionalBoundedBelowAt ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage v) v) q (-(r' ^ 2)⁻¹)) →
          (∀ z ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage v) v) y r',
            ∀ ρ : ℝ, 0 < ρ → ρ ≤ r' →
              ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * ρ ^ 3) ≤
                ballVolume ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage v) v) z ρ) →
          (∃ (a : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (hau : a ≤ v)
            (X : BackwardPointTrace (sliceTowerHistory_CX2 s)
              ((sliceTowerHistory_CX2 s).activeStage a) ((sliceTowerHistory_CX2 s).activeStage v)
              ((sliceTowerHistory_CX2 s).activeStage_mono hau) y),
            (a : ℝ) = v - τ₁ * r' ^ 2 ∧
            ∀ (w : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (haw : a ≤ w) (hwu : w ≤ v),
              (sliceTowerHistory_CX2 s).isTracedRegion w
                (X.point ((sliceTowerHistory_CX2 s).activeStage w) ((sliceTowerHistory_CX2 s).activeStage_mono haw)
                  ((sliceTowerHistory_CX2 s).activeStage_mono hwu))
                (κ * r') (τ₂ * r' ^ 2) (K * (r' ^ 2)⁻¹))) →
        (∃ (a : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (hau : a ≤ u)
          (X : BackwardPointTrace (sliceTowerHistory_CX2 s)
            ((sliceTowerHistory_CX2 s).activeStage a) ((sliceTowerHistory_CX2 s).activeStage u)
            ((sliceTowerHistory_CX2 s).activeStage_mono hau) x),
          (a : ℝ) = u - τ₁ * r ^ 2 ∧
          ∀ (w : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (haw : a ≤ w) (hwu : w ≤ u),
            (sliceTowerHistory_CX2 s).isTracedRegion w
              (X.point ((sliceTowerHistory_CX2 s).activeStage w) ((sliceTowerHistory_CX2 s).activeStage_mono haw)
                ((sliceTowerHistory_CX2 s).activeStage_mono hwu))
              (κ * r) (τ₂ * r ^ 2) (K * (r ^ 2)⁻¹)))) :
    ∃ ε C₁ K τ₁ τ₂ κ₀ b T : ℝ, 0 < ε ∧ ε ≤ 1 / 2 ∧ 1 ≤ C₁ ∧ 0 < K ∧ 0 < τ₁ ∧ 0 < τ₂ ∧
      0 < κ₀ ∧ 0 < b ∧ (τ₁ + τ₂) * b ^ 2 ≤ 1 / 2 ∧ 0 < T ∧
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
              (κ₀ * r0) (τ₂ * r0 ^ 2) (K * (r0 ^ 2)⁻¹) := by
  obtain ⟨ε, θ, C, K, τ₁, τ₂, κ, Λ, b, T, hε, hε2, hθ, hθ2, hC, hK, hτ₁, hτ₂, hκ, hΛτ, hb, hbL,
    hT, -, hbase, hstep⟩ := hBS
  have hΛ : 0 < Λ := by linarith
  have hbL' : b * (2 * (Λ + τ₁ + τ₂ + 1)) ≤ 1 := (le_div_iff₀ (by positivity)).mp hbL
  have hb1 : b ≤ 1 := by nlinarith
  have hbb : b ^ 2 ≤ b := by nlinarith
  have hΛb : Λ * b ^ 2 ≤ 1 / 2 := by nlinarith
  have hcert : (τ₁ + τ₂) * b ^ 2 ≤ 1 / 2 := by nlinarith
  obtain ⟨Tg, hTg, hg⟩ := guardHalf_of_neck_fraction_O28 Hp (by linarith : (0 : ℝ) < C) hθ
  refine ⟨ε, C, K, τ₁, τ₂, κ, b, max (2 * T) Tg, hε, hε2, hC, hK, hτ₁, hτ₂, hκ, hb, hcert,
    lt_max_of_lt_right hTg, ?_⟩
  intro s hTs
  have h2T : 2 * T ≤ s.time := le_trans (le_max_left _ _) hTs
  have hgs := hg s.time (le_trans (le_max_right _ _) hTs)
  have ht₀ : 0 < s.time := s.positive
  have hind := minimal_bad_history_O34 (sliceTowerHistory_CX2 s)
    (fun u x r => (u : ℝ) ≤ s.time ∧ s.time / 2 ≤ (u : ℝ) - Λ * r ^ 2 ∧
      θ * Hp.parameters.neckRadius s.time ≤ r ∧ r ≤ b * Real.sqrt u ∧ (0 < (u : ℝ) ∧ (u : ℝ) ∉ F.observation.eventTimes) ∧
      (∀ q ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage u) u) x r,
        SectionalBoundedBelowAt ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage u) u) q (-(r ^ 2)⁻¹)) ∧
      (∀ z ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage u) u) x r,
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ r →
          ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * ρ ^ 3) ≤
            ballVolume ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage u) u) z ρ))
    (fun u x r => (∃ (a : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (hau : a ≤ u)
        (X : BackwardPointTrace (sliceTowerHistory_CX2 s)
          ((sliceTowerHistory_CX2 s).activeStage a) ((sliceTowerHistory_CX2 s).activeStage u)
          ((sliceTowerHistory_CX2 s).activeStage_mono hau) x),
        (a : ℝ) = u - τ₁ * r ^ 2 ∧
        ∀ (w : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (haw : a ≤ w) (hwu : w ≤ u),
          (sliceTowerHistory_CX2 s).isTracedRegion w
            (X.point ((sliceTowerHistory_CX2 s).activeStage w) ((sliceTowerHistory_CX2 s).activeStage_mono haw)
              ((sliceTowerHistory_CX2 s).activeStage_mono hwu))
            (κ * r) (τ₂ * r ^ 2) (K * (r ^ 2)⁻¹)))
    (ρ := θ * Hp.parameters.neckRadius s.time) (θ := θ)
    (mul_pos hθ (Hp.parameters.neckRadius_pos _ ht₀.le)) hθ.le (by linarith)
    (fun _ _ _ hi => hi.2.2.1) (by
      rintro u x r ⟨hut, hwin, hrθ, hrb, hreg, hsecu, hvolu⟩ hIH
      have hu0 : 0 ≤ (u : ℝ) := u.2.1
      have hr : 0 < r :=
        lt_of_lt_of_le (mul_pos hθ (Hp.parameters.neckRadius_pos _ ht₀.le)) hrθ
      have hΛr : 0 ≤ Λ * r ^ 2 := by positivity
      have hTu : T ≤ (u : ℝ) := by linarith
      have hgw : ∀ m (i : Fin (F.tower.history m).eventCount),
          (F.tower.history m).time i.succ ∈ Icc ((u : ℝ) - Λ * r ^ 2) u →
          ∀ h, C * (Hp.records m i).nominalRadius h ≤ r :=
        fun m i hi h => hgs r hrθ m i ⟨by linarith [hi.1], le_trans hi.2 hut⟩ h
      by_cases hrn : r ≤ Hp.parameters.neckRadius (u : ℝ)
      · exact hbase s (by linarith) u hTu hut hreg x r hr hrn hrb hgw hsecu hvolu
      · push Not at hrn
        refine hstep s (by linarith) u hTu hut hreg x r hr hrn hrb hgw hsecu hvolu ?_
        intro v y r' hvu hwin' hr'θ hr'r hregv hr'b hsecv hvolv
        have hnu : Hp.parameters.neckRadius s.time ≤ Hp.parameters.neckRadius (u : ℝ) :=
          Hp.radius_antitone (mem_Ici.mpr hu0) (mem_Ici.mpr ht₀.le) hut
        have hr'0 : 0 ≤ r' :=
          le_trans (mul_nonneg hθ.le (Hp.parameters.neckRadius_pos _ hu0).le) hr'θ
        exact hIH v y r' hvu hr'0 hr'r
          ⟨le_trans hvu hut, by linarith, le_trans (mul_le_mul_of_nonneg_left hnu hθ.le) hr'θ,
            hr'b, hregv, hsecv, hvolv⟩)
  exact hG2c_root_O34 Hp s hθ2 hΛ hΛb (by linarith) hbase hind

end GC.LongTime.Ch12
