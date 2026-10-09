import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LateCoreP6X

/-!
# Full late canonical/time-control output from the existing selected-sequence closure

This is the proof of `lateCoreAt_of_selected_P6X` in `P6LateCoreP6X.lean`,
lines 156–274, with the same native canonical supply, native time-derivative supply,
neck-radius monotonicity, and selected-sequence contradiction hypothesis `hP6`.
The conclusion retains the whole `HasSpatialCanonicalTimeControl` predicate:
the contradiction starts with failure of that predicate and passes it directly to
the same selector, instead of first projecting to the spatial witness.

Source SHA-256: `1d39d44b84a90d060e456136836b3f641d971d79999310c03039bad317a8125b`.

The hypothesis `hP6` remains an explicit, unpaid closure assumption. This theorem
does not recover time control from the projected spatial statement P6(b), and does
not complete `hspine`. No new closure assumption or replacement supply is introduced.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Collapse Set Filter
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace GC.LongTime.Ch11

universe u

/-- At one `A > 1`, the original selected-sequence contradiction hypothesis gives
late, history-uniform spatial canonical neighborhoods with their guarded one-sided
time-derivative control. All hypotheses, including `hP6`, are unchanged from
`lateCoreAt_of_selected_P6X`; only its spatial projection is avoided. -/
theorem lateGoodAt_of_selected_CXSP {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hcan : HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2)
    (hder : TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    {A : ℝ} (hA : 1 < A)
    (hP6 : ∀ (ind : ℕ → ℕ),
      let Kh : ℕ → ObservedHistory.{u} := fun k => (F.tower.history (ind k)).toHistory
      ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier)
        (r : ℕ → ℝ), (∀ k, 0 < r k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tn k : ℝ)) →
        (∀ k, 2 * r k ^ 2 < (Tn k : ℝ)) →
        (∀ k, hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) (r k)) →
        (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤
          ballVolume ((Kh k).stageMetric ((Kh k).activeStage (Tn k)) (Tn k)) (pT k) (r k)) →
      ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
        (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - r k ^ 2) →
      ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
          ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
        (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
        (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
        (∀ k, R k = metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
        (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k * r k ^ 2) →
        Tendsto L atTop atTop →
        (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
        (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
          (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
          ∀ z : ((Kh k).stageAt v).Carrier,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                  ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                  ((seedTrace k).point ((Kh k).activeStage (σ k))
                    ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                ENNReal.ofReal (L k / Real.sqrt (R k)) →
            4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
            (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
        (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
        (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - r k ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
        Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - r k ^ 2 / 2))) atTop atTop →
        Tendsto (fun k => r k / 200 * Real.sqrt (R k)) atTop atTop → False) :
    ∃ K₁ T : ℝ, 0 < K₁ ∧ 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ y ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
          K₁ * (r ^ 2)⁻¹ ≤ metricScalarAt (H.stageMetric (H.activeStage t) t) y →
          H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime t y := by
  by_contra hcon
  have hk : ∀ k : ℕ, ∃ (n : ℕ) (t : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon)
      (p : ((F.tower.history n).toHistory.stageAt t).Carrier) (r : ℝ)
      (x : ((F.tower.history n).toHistory.stageAt t).Carrier),
      (k : ℝ) + 1 ≤ (t : ℝ) ∧ 2 * r ^ 2 < (t : ℝ) ∧
      hasSmallParabolicCurvature (F.tower.history n).toHistory t p r ∧
      ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume ((F.tower.history n).toHistory.stageMetric
        ((F.tower.history n).toHistory.activeStage t) t) p r ∧
      x ∈ riemannianBallOf ((F.tower.history n).toHistory.stageMetric
        ((F.tower.history n).toHistory.activeStage t) t) p (A * r) ∧
      ((k : ℝ) + 1) * (r ^ 2)⁻¹ ≤ metricScalarAt ((F.tower.history n).toHistory.stageMetric
        ((F.tower.history n).toHistory.activeStage t) t) x ∧
      ¬ (F.tower.history n).toHistory.HasSpatialCanonicalTimeControl
        ε C1 C2 Ctime t x := by
    intro k
    by_contra hk
    refine hcon ⟨(k : ℝ) + 1, (k : ℝ) + 1, by positivity, by positivity, ?_⟩
    intro n _ t p r hT ht hs hv x hx hK
    by_contra hW
    exact hk ⟨n, t, p, r, x, hT, ht, hs, hv, hx, hK, hW⟩
  choose ind Tn pT r x hlate htime hsmall hvol hx hK hbad0 using hk
  have hr : ∀ k, 0 < r k := fun k => (hsmall k).1
  have hseed : ∀ k, ∃ (a : Icc (0 : ℝ) (F.tower.history (ind k)).toHistory.horizon)
      (hat : a ≤ Tn k), (a : ℝ) = (Tn k : ℝ) - r k ^ 2 ∧
      Nonempty (BackwardPointTrace (F.tower.history (ind k)).toHistory
        ((F.tower.history (ind k)).toHistory.activeStage a)
        ((F.tower.history (ind k)).toHistory.activeStage (Tn k))
        ((F.tower.history (ind k)).toHistory.activeStage_mono hat) (pT k)) := fun k => by
    obtain ⟨hrk, a, hat, ha, htr⟩ := hsmall k
    have hp : pT k ∈ riemannianBallOf ((F.tower.history (ind k)).toHistory.stageMetric
        ((F.tower.history (ind k)).toHistory.activeStage (Tn k)) (Tn k)) (pT k) (r k) := by
      change riemannianEDistOf _ (pT k) (pT k) < ENNReal.ofReal (r k)
      rw [riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr hrk
    obtain ⟨tr, -⟩ := htr (pT k) hp
    exact ⟨a, hat, ha, ⟨tr⟩⟩
  choose aSeed haT hclock hst using hseed
  have hRx : ∀ k : ℕ, (k : ℝ) + 1 ≤ metricScalarAt ((F.tower.history (ind k)).toHistory.stageMetric
      ((F.tower.history (ind k)).toHistory.activeStage (Tn k)) (Tn k)) (x k) * r k ^ 2 := by
    intro k
    have h2 : 0 < r k ^ 2 := by have := hr k; positivity
    have := mul_le_mul_of_nonneg_right (hK k) h2.le
    rwa [mul_assoc, inv_mul_cancel₀ h2.ne', mul_one] at this
  have hRpos0 : ∀ k, 0 < metricScalarAt ((F.tower.history (ind k)).toHistory.stageMetric
      ((F.tower.history (ind k)).toHistory.activeStage (Tn k)) (Tn k)) (x k) := by
    intro k
    have h2 : 0 < r k ^ 2 := by have := hr k; positivity
    have : 0 < ((k : ℝ) + 1) * (r k ^ 2)⁻¹ := by positivity
    exact this.trans_le (hK k)
  have hdiv : Tendsto (fun k => metricScalarAt ((F.tower.history (ind k)).toHistory.stageMetric
      ((F.tower.history (ind k)).toHistory.activeStage (Tn k)) (Tn k)) (x k) * r k ^ 2)
      atTop atTop :=
    tendsto_atTop_mono (fun k : ℕ => (by linarith [hRx k] : (k : ℝ) ≤ _))
      tendsto_natCast_atTop_atTop
  have hsel := ObservedHistory.selection_of_bad_sequence_P6X
    (Kh := fun k => (F.tower.history (ind k)).toHistory) (fun _ => q) le_rfl le_rfl le_rfl
    (fun _ => hanti) (fun k => hcan (ind k))
    (fun k v z hlo hhi hR =>
      stageDerivative_of_timeDerivativeSupply_P6X hder (ind k) v z hlo hhi hR)
    Tn pT r A hr (zero_lt_one.trans hA) aSeed haT hclock (fun k => (hst k).some) x hx hRpos0
    hbad0 hdiv
  obtain ⟨σ, y, R, hsT, has, L, hRdef, hRpos, hRle, -, hL, hbad, hgood, hwin, hwin', hroom,
    hradii⟩ := hsel
  have hRr : ∀ k : ℕ, (k : ℝ) + 1 ≤ R k * r k ^ 2 := fun k => by
    have h2 : 0 ≤ r k ^ 2 := sq_nonneg _
    have := mul_le_mul_of_nonneg_right (hRle k) h2
    linarith [hRx k]
  exact hP6 ind Tn pT r hr hlate htime hsmall hvol aSeed haT hclock (fun k => (hst k).some) σ y R
    hsT has L hRdef hRpos hRr hL hbad hgood hwin hwin' hroom hradii

end GC.LongTime.Ch11
