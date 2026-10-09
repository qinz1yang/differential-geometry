import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff

/-!
# Deep backward necks (C12X, S16 `hwin` route β; O-C12X-S16H G4a)

The record field `GeometricCutoffRecord.backward` stores an `IncomingBackwardNeck` of depth
exactly `r_α² = R_term(c_α)⁻¹` (`nominalRadius_sq_eq_inv_scalar_C12X`).  For far-early window
points the depth-one window `[t - R(y,t)⁻¹, t]` of a full strong neck can start before
`time i.succ - r²` (by up to `O(δ) r²`), and no hypothesis of `hwin` controls the flow there.

Route β (lead decision, P1): the record producer supplies a backward neck of depth `θ r²`,
`θ > 1` fixed.  `IncomingBackwardNeckDeep_C12X` is that contract: it extends the depth-one
`IncomingBackwardNeck` (so the projection is `toIncomingBackwardNeck`) by charts, crossings,
metric identification, jets and parabolic closeness on `[-θ, 0]`, for the same metric family.

* `IncomingBackwardNeck.toDeepOne_C12X`: depth `θ = 1` is exactly the old contract.
* `window_fits_of_depth_C12X`, `window_fits_two_C12X`: a depth `θ r²` covers the closed
  depth-one window of `(y, t)`, `t ≥ time i.succ`, once `1 ≤ θ R r²` (`θ = 2`: `R r² ≥ 1/2`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable (H : ObservedHistory.{u}) (i : Fin H.eventCount)

/-- A backward neck of depth `θ r²` (`θ ≥ 1`): the depth-one `IncomingBackwardNeck` together
with stage charts, regular crossings, metric identification, time jets and parabolic
`δ`-closeness to the shrinking cylinder on the normalized window `[-θ, 0]`. -/
structure IncomingBackwardNeckDeep_C12X {δ : ℝ} {k : ℕ}
    (neck : NormalizedNeck (H.event i).terminal.metric δ k) (r θ : ℝ)
    extends IncomingBackwardNeck H i neck r where
  one_le_depth : 1 ≤ θ
  deep_left_nonneg : 0 ≤ H.time i.succ - θ * r ^ 2
  deepChart : (j : Fin H.eventCount) → j.val ≤ i.val →
    H.time i.succ - θ * r ^ 2 < H.time j.succ →
    C(neckBuffer δ, (H.stage j.castSucc).Carrier)
  deepChart_smooth : ∀ j hj ha,
    IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ (deepChart j hj ha)
  deepChart_eq : ∀ j hj ha ha', deepChart j hj ha' = stageChart j hj ha
  deep_crossing : ∀ (j : Fin H.eventCount) (hj : j.val < i.val),
    let next : Fin H.eventCount := ⟨j.val + 1, by omega⟩
    ∀ ha : H.time i.succ - θ * r ^ 2 < H.time j.succ,
    ∀ hn : H.time i.succ - θ * r ^ 2 < H.time next.succ,
    ∀ x : neckBuffer δ,
      (H.event j).RegularCrossing (deepChart j hj.le ha x)
        (deepChart next (by change j.val + 1 ≤ i.val; omega) hn x)
  deep_metric_on_slab : ∀ (j : Fin H.eventCount) hj ha, ∀ v ∈ Ico (-θ) 0,
    H.time j.castSucc ≤ H.time i.succ + r ^ 2 * v →
    H.time i.succ + r ^ 2 * v < H.time j.succ → ∀ x V W,
      (metric v).inner x V W = (r ^ 2)⁻¹ *
        ((H.event j).incoming.flow.base.metric (H.time i.succ + r ^ 2 * v)).inner
          (deepChart j hj ha x)
          (mfderiv NeckCylinderModel ThreeModel (deepChart j hj ha) x V)
          (mfderiv NeckCylinderModel ThreeModel (deepChart j hj ha) x W)
  deepJet : (b : ℕ) → (v : Icc (-θ) 0) →
    Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2
  deepJet_eq : ∀ b v x,
    deepJet b v x =
      iteratedDerivWithin b (fun t =>
        (metricTensorField (metric t) x) -
          (metricTensorField ((shrinkingCylinderMetric
            ⟨min t 0, lt_of_le_of_lt (min_le_right (t : ℝ) 0)
              (show (0 : ℝ) < 1 by norm_num)⟩).restrictOpen
              (neckBuffer δ)) x)) (Icc (-θ) 0) v.1
  deep_closeness : ∃ η : ℝ, η < δ ∧ ∀ a b : ℕ, a + 2 * b ≤ k →
    ∀ v : Icc (-θ) 0, ∀ x ∈ neckClosedTest δ,
      let g := (shrinkingCylinderMetric
        ⟨v.1, lt_of_le_of_lt v.2.2 (show (0 : ℝ) < 1 by norm_num)⟩).restrictOpen
        (neckBuffer δ)
      Real.sqrt (normSq0S g x (a + 2)
        (cylinderTensorCovDeriv g (deepJet b v) a x)) ≤ η
  deep_metric_smooth : ∀ p : neckBuffer δ, ∀ t ∈ Icc (-θ) 0,
    ∃ U : Set (neckBuffer δ), IsOpen U ∧ p ∈ U ∧
      U ⊆ (trivializationAt (EuclideanSpace ℝ (Fin 2) × ℝ)
        (TangentSpace NeckCylinderModel) p).baseSet ∧
    ∃ V : Set ℝ, IsOpen V ∧ t ∈ V ∧
    ∃ A : ℝ × neckBuffer δ → (EuclideanSpace ℝ (Fin 2) × ℝ) →
        (EuclideanSpace ℝ (Fin 2) × ℝ) → ℝ,
      (∀ v w, ContMDiffOn (𝓘(ℝ, ℝ).prod NeckCylinderModel) 𝓘(ℝ, ℝ) ∞
        (fun z => A z v w) (V ×ˢ U)) ∧
      ∀ s ∈ V ∩ Icc (-θ) 0, ∀ x ∈ U, ∀ v w,
        A (s, x) v w = (metric s).inner x
          ((trivializationAt (EuclideanSpace ℝ (Fin 2) × ℝ)
            (TangentSpace NeckCylinderModel) p).symmL ℝ x v)
          ((trivializationAt (EuclideanSpace ℝ (Fin 2) × ℝ)
            (TangentSpace NeckCylinderModel) p).symmL ℝ x w)

variable {H i}

/-- Depth `θ = 1` is exactly the depth-one contract: every `IncomingBackwardNeck` is a deep
backward neck of depth one. -/
def IncomingBackwardNeck.toDeepOne_C12X {δ : ℝ} {k : ℕ}
    {neck : NormalizedNeck (H.event i).terminal.metric δ k} {r : ℝ}
    (N : IncomingBackwardNeck H i neck r) : IncomingBackwardNeckDeep_C12X H i neck r 1 where
  toIncomingBackwardNeck := N
  one_le_depth := le_rfl
  deep_left_nonneg := by simpa only [one_mul] using N.left_nonneg
  deepChart j hj ha := N.stageChart j hj (by simpa only [one_mul] using ha)
  deepChart_smooth j hj ha := N.stageChart_smooth j hj _
  deepChart_eq _ _ _ _ := rfl
  deep_crossing j hj ha hn x :=
    N.crossing j hj (by simpa only [one_mul] using ha) (by simpa only [one_mul] using hn) x
  deep_metric_on_slab j hj ha v hv := N.metric_on_slab j hj _ v hv
  deepJet := N.timeDifferenceJet
  deepJet_eq := N.timeDifferenceJet_eq
  deep_closeness := N.parabolic_closeness
  deep_metric_smooth := N.metric_smooth

namespace IncomingBackwardNeckDeep_C12X

variable {δ : ℝ} {k : ℕ} {neck : NormalizedNeck (H.event i).terminal.metric δ k} {r θ : ℝ}

/-- The deep window starts no later than the depth-one window. -/
theorem start_le (D : IncomingBackwardNeckDeep_C12X H i neck r θ) :
    H.time i.succ - θ * r ^ 2 ≤ H.time i.succ - r ^ 2 := by
  have h1 := D.one_le_depth
  have h2 : r ^ 2 ≤ θ * r ^ 2 := le_mul_of_one_le_left (sq_nonneg r) h1
  linarith

/-- The deep charts agree with the depth-one charts wherever the latter are defined. -/
theorem deepChart_apply (D : IncomingBackwardNeckDeep_C12X H i neck r θ) (j : Fin H.eventCount)
    (hj : j.val ≤ i.val) (ha : H.time i.succ - r ^ 2 < H.time j.succ) (x : neckBuffer δ) :
    D.deepChart j hj (lt_of_le_of_lt D.start_le ha) x = D.stageChart j hj ha x := by
  rw [D.deepChart_eq j hj ha]

end IncomingBackwardNeckDeep_C12X

/-- Exact recorded depth: `r_α² = R_term(c_α)⁻¹` (terminal metric, record neck center). -/
theorem GeometricCutoffRecord.nominalRadius_sq_eq_inv_scalar_C12X {p : CutoffParameters}
    (R : GeometricCutoffRecord H i p) (α : (H.event i).transition.trace.tubes.Index) :
    (R.nominalRadius ⟨α⟩) ^ 2 =
      (metricScalarAt (H.event i).terminal.metric (R.neck α).center)⁻¹ := by
  rw [← (R.neck α).scale_scalar, R.scale_eq α, inv_inv]

/-- Route β window arithmetic: a backward depth `θ r²` with `1 ≤ θ R r²` covers the closed
depth-one window `[t - R⁻¹, t]` of every `t ≥ t₀`. -/
theorem window_fits_of_depth_C12X {t₀ t r R θ : ℝ} (hR : 0 < R) (ht : t₀ ≤ t)
    (hθ : 1 ≤ θ * R * r ^ 2) : t₀ - θ * r ^ 2 ≤ t - R⁻¹ := by
  have hinv : R⁻¹ ≤ θ * r ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hθ (inv_pos.mpr hR).le
    have hc : R⁻¹ * (θ * R * r ^ 2) = θ * r ^ 2 := by
      field_simp
    linarith
  linarith

/-- `θ = 2` suffices once `R r² ≥ 1/2`. -/
theorem window_fits_two_C12X {t₀ t r R : ℝ} (hR : 0 < R) (ht : t₀ ≤ t)
    (hhalf : 1 / 2 ≤ R * r ^ 2) : t₀ - 2 * r ^ 2 ≤ t - R⁻¹ :=
  window_fits_of_depth_C12X hR ht (by nlinarith)

/-- The depth-one gap is genuine: if `t - t₀ < R⁻¹ - r²` the closed window of `(y, t)` starts
strictly before the depth-one data `t₀ - r²`. -/
theorem window_starts_before_of_lt_C12X {t₀ t r R : ℝ} (ht : t - t₀ < R⁻¹ - r ^ 2) :
    t - R⁻¹ < t₀ - r ^ 2 := by
  linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
