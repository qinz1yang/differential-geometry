import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84B4Static_S87

/-!
# CH12-S87 G3: `hsub86N_S87` (tower-history window form, hscale and the event-time seed as explicit inputs)
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.VolumeComparison DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow
open scoped NNReal Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

theorem hsub86N_trace_S87 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    {Ctime : ℝ≥0} (hP2 : P2_O2 Hp Ctime)
    (hscale : ∀ n (i : Fin (F.tower.history n).eventCount)
      (b : ((F.tower.history n).toHistory.event i).RetainedBoundaryIndex) (z : ThreeBall),
      ((Hp.records n i).static b).neck.scale / 2 ≤
        metricScalarAt ((Hp.records n i).static b).witness.metric
          (((Hp.records n i).static b).witness.cap z))
    (s : RegularSlice F.observation) (u : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon)
    (hu0 : 0 < (u : ℝ))
    (hreg : (sliceTowerHistory_CX2 s).time ((sliceTowerHistory_CX2 s).activeStage u) < (u : ℝ))
    (x0 : ((sliceTowerHistory_CX2 s).stageAt u).Carrier) {r0 : ℝ} (hr0 : 0 < r0)
    (hrad : r0 ≤ Hp.parameters.neckRadius u)
    {A A' Cb β C₁ τ₁ τ₂ : ℝ} (hA : 0 < A) (hAA' : A < A') (hA'1 : 1 ≤ A') (hCb : 0 < Cb)
    (hCbC : (Ctime : ℝ) ≤ Cb) (hβdef : β = r0 ^ 2 / (8 * A')) (hτ₁def : τ₁ = 1 / (64 * Cb * A'))
    (hτ₂ : 0 < τ₂) (hτ₂le : τ₂ ≤ τ₁) (hC₁A : 8 * A' + 1 ≤ C₁)
    (hLu : (τ₁ + τ₂) * r0 ^ 2 ≤ (u : ℝ) / 2)
    (hrcI : ∀ t : ℝ, (u : ℝ) / 2 < t → Hp.parameters.recenterConstant * δ t ≤ 1 / 2)
    (htop : metricScalarAt ((sliceTowerHistory_CX2 s).stageMetric
      ((sliceTowerHistory_CX2 s).activeStage u) u) x0 ≤ 4 * A / r0 ^ 2)
    (hnom : ∀ m (i : Fin (F.tower.history m).eventCount),
      (F.tower.history m).time i.succ ∈ Icc ((u : ℝ) - (τ₁ + τ₂) * r0 ^ 2) u →
      ∀ h, C₁ * (Hp.records m i).nominalRadius h ≤ r0) :
    ∃ (a₂ : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (_ : (a₂ : ℝ) = (u : ℝ) - (τ₁ + τ₂) * r0 ^ 2)
      (hau : a₂ ≤ u)
      (X : BackwardPointTrace (sliceTowerHistory_CX2 s) ((sliceTowerHistory_CX2 s).activeStage a₂)
        ((sliceTowerHistory_CX2 s).activeStage u) ((sliceTowerHistory_CX2 s).activeStage_mono hau) x0),
      ∀ (w : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (haw : a₂ ≤ w) (hwu : w ≤ u),
        metricScalarAt ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage w) w)
          (X.point ((sliceTowerHistory_CX2 s).activeStage w)
            ((sliceTowerHistory_CX2 s).activeStage_mono haw)
            ((sliceTowerHistory_CX2 s).activeStage_mono hwu)) ≤ 16 * A' / r0 ^ 2 := by
  have hr2 : 0 < r0 ^ 2 := by positivity
  have hτ₁ : 0 < τ₁ := by rw [hτ₁def]; positivity
  have hu1 := u.2.2
  have hLnn : 0 ≤ (τ₁ + τ₂) * r0 ^ 2 := by positivity
  let a₂ : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon :=
    ⟨(u : ℝ) - (τ₁ + τ₂) * r0 ^ 2, by linarith, by linarith⟩
  have ha₂u : a₂ ≤ u := show (u : ℝ) - (τ₁ + τ₂) * r0 ^ 2 ≤ u by linarith
  have hβ : 0 < β := by rw [hβdef]; positivity
  have hβM : β * (r0 ^ 2)⁻¹ < 1 := by
    rw [hβdef]; field_simp; nlinarith
  have hneck : ∀ t : ℝ, t ≤ u → (Hp.parameters.neckRadius (max t 0) ^ 2)⁻¹ ≤ (r0 ^ 2)⁻¹ := by
    intro t ht
    have h := Hp.radius_antitone (Set.mem_Ici.mpr (le_max_right t 0)) (Set.mem_Ici.mpr hu0.le)
      (max_le ht hu0.le)
    exact inv_anti₀ hr2 (pow_le_pow_left₀ hr0.le (hrad.trans h) 2)
  have hw : 2 * Cb * ((τ₁ + τ₂) * r0 ^ 2) ≤ β / 2 := by
    calc 2 * Cb * ((τ₁ + τ₂) * r0 ^ 2) ≤ 2 * Cb * ((2 * τ₁) * r0 ^ 2) := by gcongr; linarith
      _ = β / 2 := by rw [hτ₁def, hβdef]; field_simp; ring
  have hbarr : ∀ v : ℝ, (a₂ : ℝ) ≤ v → v ≤ u → β / 2 ≤ β - 2 * Cb * ((u : ℝ) - v) := by
    intro v hv _
    have : 2 * Cb * ((u : ℝ) - v) ≤ 2 * Cb * ((τ₁ + τ₂) * r0 ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      change (u : ℝ) - v ≤ (τ₁ + τ₂) * r0 ^ 2
      have : (a₂ : ℝ) = u - (τ₁ + τ₂) * r0 ^ 2 := rfl
      linarith
    linarith
  have hRinv : ∀ v : ℝ, (a₂ : ℝ) ≤ v → v ≤ u → (β - 2 * Cb * ((u : ℝ) - v))⁻¹ ≤ 16 * A' / r0 ^ 2 := by
    intro v h1 h2
    have h := hbarr v h1 h2
    calc (β - 2 * Cb * ((u : ℝ) - v))⁻¹ ≤ (β / 2)⁻¹ := inv_anti₀ (by positivity) h
      _ = 16 * A' / r0 ^ 2 := by rw [hβdef]; field_simp; ring
  have hden : 0 < β - 2 * Cb * ((u : ℝ) - a₂) := by
    have := hbarr a₂ le_rfl ha₂u; linarith
  have hcapB : (β - 2 * Cb * ((u : ℝ) - a₂))⁻¹ < C₁ ^ 2 / (4 * r0 ^ 2) := by
    refine (hRinv a₂ le_rfl ha₂u).trans_lt ?_
    rw [div_lt_div_iff₀ hr2 (by positivity)]
    have h64 : 64 * A' < C₁ ^ 2 := by nlinarith
    calc 16 * A' * (4 * r0 ^ 2) = (64 * A') * r0 ^ 2 := by ring
      _ < C₁ ^ 2 * r0 ^ 2 := by gcongr
  have hx0 : metricScalarAt ((sliceTowerHistory_CX2 s).stageMetric
      ((sliceTowerHistory_CX2 s).activeStage u) u) x0 < β⁻¹ := by
    refine htop.trans_lt ?_
    rw [hβdef, inv_div, div_lt_div_iff₀ hr2 hr2]
    nlinarith [hAA', hr2, mul_pos hr2 hA]
  have hevt : ∀ i : Fin (sliceTowerHistory_CX2 s).eventCount,
      (sliceTowerHistory_CX2 s).activeStage a₂ ≤ i.castSucc →
      i.succ ≤ (sliceTowerHistory_CX2 s).activeStage u →
      (u : ℝ) / 2 < (sliceTowerHistory_CX2 s).time i.succ ∧
      (sliceTowerHistory_CX2 s).time i.succ ≤ (u : ℝ) := by
    intro i hf hl
    obtain ⟨h1, h2⟩ := window_event_S87 (sliceTowerHistory_CX2 s) i hf hl
    exact ⟨by have : (a₂ : ℝ) = u - (τ₁ + τ₂) * r0 ^ 2 := rfl; linarith, h2⟩
  have hnomN : ∀ i : Fin (sliceTowerHistory_CX2 s).eventCount,
      (sliceTowerHistory_CX2 s).activeStage a₂ ≤ i.castSucc →
      i.succ ≤ (sliceTowerHistory_CX2 s).activeStage u →
      ∀ h, C₁ * (Hp.records (sliceTowerIndex_CX2 s) i).nominalRadius h ≤ r0 := by
    intro i hf hl h
    obtain ⟨h1, h2⟩ := window_event_S87 (sliceTowerHistory_CX2 s) i hf hl
    exact hnom (sliceTowerIndex_CX2 s) i ⟨(show (u : ℝ) - (τ₁ + τ₂) * r0 ^ 2 < _ from h1).le, h2⟩ h
  obtain ⟨X₂, hX₂⟩ := exists_trace_scalar_bound_S74 (sliceTowerHistory_CX2 s)
    (Hp.records (sliceTowerIndex_CX2 s)) (C₁ := C₁) (r0 := r0) (M := (r0 ^ 2)⁻¹) (β := β) (C := Cb)
    (θ := fun t => (Hp.parameters.neckRadius (max t 0) ^ 2)⁻¹) hCb hβ hβM (by linarith) hr0
    (hscale (sliceTowerIndex_CX2 s))
    (fun i y t ht hlt => by
      have hmax : max t 0 = t := max_eq_left (((sliceTowerHistory_CX2 s).time_nonneg _).trans ht.1.le)
      simp only [hmax] at hlt
      refine (hP2.1 (sliceTowerIndex_CX2 s) i y t ht hlt).trans ?_
      exact mul_le_mul_of_nonneg_right hCbC (sq_nonneg _))
    (fun h y t ht hlt => by
      have hmax : max t 0 = t := max_eq_left (((sliceTowerHistory_CX2 s).time_nonneg _).trans ht.1.le)
      simp only [hmax] at hlt
      refine (hP2.2 (sliceTowerIndex_CX2 s) h y t ht hlt).trans ?_
      exact mul_le_mul_of_nonneg_right hCbC (sq_nonneg _))
    ha₂u (fun t ht => hneck t ht) hreg hden hcapB
    (fun i hf hl => by
      have ht := (hevt i hf hl).1
      rw [Hp.accuracy_eq]
      have h := hrcI _ ht
      exact h)
    hnomN x0 hx0
  exact ⟨a₂, rfl, ha₂u, X₂, fun w haw hwu => (hX₂ w haw hwu).trans (hRinv w haw hwu)⟩

end GC.LongTime.Ch12
