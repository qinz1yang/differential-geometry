import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BoundaryWiringG2_S16
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitInterfaceProps
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LargeTriggerSeed_S21
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LargeTriggerRicci_S21
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LargeTriggerTransfer_S21

/-!
# CH12-S21 / T3 (TCF04): large volume triggers disappear, from LTF03 (explicit input)

Quantifier order (review CH12-R1 Q3 3.1): `w, b` first, then the seed constants and the thickness
lower bound, then `w'`, then the thresholds coming from `L.alternatives w'` and TCF02.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open GC.LongTime Set Filter
open scoped Manifold ContDiff ENNReal Topology

namespace GC.LongTime.Ch12

universe u

theorem ballVolume_mono_S21 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (p : M) {a ρ : ℝ} (h : a ≤ ρ) :
    ballVolume g p a ≤ ballVolume g p ρ := by
  apply MeasureTheory.measure_mono
  intro q hq
  exact lt_of_lt_of_le hq (ENNReal.ofReal_le_ofReal h)

/-- Collapse of a thin piece at its curvature scale, from the `thin` alternative. -/
theorem LateCutFamily.thin_collapse_S21 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} {slices : ℕ → RegularSlice F.observation}
    (L : GC.LongTime.LateCutFamily F K slices) (j : ℕ)
    (c : ConnectedComponents (slices j).stage.Carrier)
    (i : Fin (L.decomposition j c).components.count) (w' : ℝ)
    (A : (i : Fin (L.decomposition j c).components.count) →
      HyperbolicOrThin (L.decomposition j c) (L.metric j c) (L.thin j c) K w' i)
    (hthin : L.thin j c i) (p : ((L.decomposition j c).component i).Carrier)
    (hD : ENNReal.ofReal 10 <
      distanceToBoundary ((L.decomposition j c).component i) (L.metric j c i) p) :
    volumeCollapsedAtCurvatureScale (L.metric j c i) w' p := by
  cases hA : A i with
  | hyperbolic hnot _ _ => exact absurd hthin hnot
  | nonnegative hnot _ _ => exact absurd hthin hnot
  | thin _ hgeometry =>
    rcases hgeometry with ⟨-, hall⟩ | ⟨-, hbv⟩
    · exact hall p
    · exact hbv p (by simpa [boundaryBufferDistance] using hD)

/-- The numerical contradiction: seed volume `v a³` versus collapse `w' ρ³` with `ρ ≤ 5`. -/
theorem trigger_numeric_S21 {v a w' w₁ ρ : ℝ} (hv : 0 < v) (ha : 0 < a) (hw'pos : 0 < w')
    (hw₁ : w₁ = v * a ^ 3 / 125) (hw'₁ : w' ≤ w₁ / 2) (hρ : 0 < ρ) (hρ5 : ρ ≤ 5)
    (hchain : v * a ^ 3 ≤ w' * ρ ^ 3) : False := by
  have hρ3 : ρ ^ 3 ≤ 5 ^ 3 := pow_le_pow_left₀ hρ.le hρ5 3
  have h1 : v * a ^ 3 ≤ w' * 125 := by
    calc v * a ^ 3 ≤ w' * ρ ^ 3 := hchain
      _ ≤ w' * 5 ^ 3 := by gcongr
      _ = w' * 125 := by norm_num
  have h2 : w' * 125 ≤ v * a ^ 3 / 2 := by
    have : w' * 125 ≤ w₁ / 2 * 125 := by gcongr
    calc w' * 125 ≤ w₁ / 2 * 125 := this
      _ = v * a ^ 3 / 2 := by rw [hw₁]; ring
  have : 0 < v * a ^ 3 := by positivity
  linarith

/-- The per-ball contradiction (everything about one fixed bad ball). -/
theorem LateCutFamily.trigger_false_S21 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} {slices : ℕ → RegularSlice F.observation}
    (L : GC.LongTime.LateCutFamily F K slices) (j : ℕ)
    (c : ConnectedComponents (slices j).stage.Carrier)
    (i : Fin (L.decomposition j c).components.count) (hthin : L.thin j c i)
    (p : ((L.decomposition j c).component i).Carrier) {v a w' w₁ b r : ℝ}
    (hv : 0 < v) (ha : 0 < a) (hab : a ≤ b) (hbr : b ≤ r) (hw'pos : 0 < w')
    (hw₁ : w₁ = v * a ^ 3 / 125) (hw'₁ : w' ≤ w₁ / 2)
    (hrR : ENNReal.ofReal r < curvatureRadius (L.metric j c i) p)
    (hRD : curvatureRadius (L.metric j c i) p <
      distanceToBoundary ((L.decomposition j c).component i) (L.metric j c i) p)
    (hcol : volumeCollapsedAtCurvatureScale (L.metric j c i) w' p)
    (hseedvol : ENNReal.ofReal (v * a ^ 3) ≤ ballVolume (slices j).normalizedMetric
      (cutPieceMap (L.decomposition j c) i p).val a)
    (hR5 : curvatureRadius (slices j).normalizedMetric
      (cutPieceMap (L.decomposition j c) i p).val ≤ ENNReal.ofReal 5) : False := by
  have hRp : curvatureRadius (L.metric j c i) p ≤ ENNReal.ofReal 5 := by
    rw [← LateCutFamily.cutPiece_normalized_radius_S21 L j c i p hRD]
    exact hR5
  have hfin : curvatureRadius (L.metric j c i) p ≠ ⊤ := L.finite_scales j c i hthin p
  obtain ⟨ρ, hρeq⟩ : ∃ ρ : ℝ, curvatureRadius (L.metric j c i) p = ENNReal.ofReal ρ :=
    ⟨_, (ENNReal.ofReal_toReal hfin).symm⟩
  have hρpos : 0 < ρ := by
    have := curvatureRadius_pos (L.metric j c i) p
    rw [hρeq] at this
    exact ENNReal.ofReal_pos.mp this
  have hρ5 : ρ ≤ 5 := by
    rw [hρeq] at hRp
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp hRp
  have harρ : a ≤ ρ := by
    have h := hrR
    rw [hρeq] at h
    have := (ENNReal.ofReal_lt_ofReal_iff hρpos).mp h
    linarith
  have hupper := hcol ρ hρpos hρeq
  have hraD : ENNReal.ofReal a <
      distanceToBoundary ((L.decomposition j c).component i) (L.metric j c i) p :=
    lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (hab.trans hbr)) (hrR.trans hRD)
  obtain ⟨-, hva, -⟩ := LateCutFamily.cutPiece_normalized_transfer_hd_S21 L j c i p a ha hraD
  have hlow : ENNReal.ofReal (v * a ^ 3) ≤ ballVolume (L.metric j c i) p a := by
    rw [hva]; exact hseedvol
  have hmono := ballVolume_mono_S21 (L.metric j c i) p harρ
  have hchain := hlow.trans (hmono.trans hupper)
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hchain
  exact trigger_numeric_S21 hv ha hw'pos hw₁ hw'₁ hρpos hρ5 hchain

theorem LateCutFamily.hT3_of_LTF03_S21 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ) (δ : ℝ → ℝ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (H : AnalyticSurgeryProfile F δ) (hneg : EventuallyNegativeScalar_S13 F)
    (slices : ℕ → RegularSlice F.observation)
    (htimes : ∀ j : ℕ, (j : ℝ) < (slices j).time)
    (L : GC.LongTime.LateCutFamily F K slices)
    (hLTF03 : ∀ (S : LatePointSequence_S13 F) (a v Lr : ℝ),
      SeedHyperbolicOnFixedBallsSeq_S13 H hdec hneg S a v Lr) :
    ∀ w : ℝ, 0 < w → w < euclideanThreeUnitBallVolume → ∀ b : ℝ, 0 < b →
      ∃ N : ℕ, ∀ j, N ≤ j → ∀ c i, L.thin j c i →
        ∀ p : ((L.decomposition j c).component i).Carrier,
          ENNReal.ofReal 10 <
            distanceToBoundary ((L.decomposition j c).component i) (L.metric j c i) p →
          ∀ r : ℝ, 0 < r → ENNReal.ofReal r < curvatureRadius (L.metric j c i) p →
            ENNReal.ofReal (w * r ^ 3) ≤ ballVolume (L.metric j c i) p r → r < b := by
  intro w hw hwω b hb
  obtain ⟨c0, hc0, hseed⟩ := seed_scale_down_S21.{u}
  set a : ℝ := min b 1 with ha
  have hapos : 0 < a := lt_min hb one_pos
  have hab : a ≤ b := min_le_left _ _
  set v : ℝ := c0 * w with hv
  have hvpos : 0 < v := mul_pos hc0 hw
  set w₁ : ℝ := v * a ^ 3 / 125 with hw₁
  have hw₁pos : 0 < w₁ := by positivity
  set w' : ℝ := min (w₁ / 2) (euclideanThreeUnitBallVolume / 2) with hw'
  have hω : 0 < euclideanThreeUnitBallVolume := lt_trans hw hwω
  have hw'pos : 0 < w' := lt_min (by positivity) (by positivity)
  have hw'ω : w' < euclideanThreeUnitBallVolume :=
    lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hw'₁ : w' ≤ w₁ / 2 := min_le_left _ _
  obtain ⟨N1, hN1⟩ := L.alternatives w' hw'pos hw'ω
  obtain ⟨N2, hN2⟩ := LateCutFamily.eventually_interior_scale_core_T2 L (collarNegativePlane_S16 K)
  by_contra hno
  push Not at hno
  have hno' : ∀ ℓ : ℕ, ∃ j, max (max N1 N2) ℓ ≤ j ∧ ∃ c i, L.thin j c i ∧
      ∃ p : ((L.decomposition j c).component i).Carrier,
        ENNReal.ofReal 10 <
          distanceToBoundary ((L.decomposition j c).component i) (L.metric j c i) p ∧
        ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r < curvatureRadius (L.metric j c i) p ∧
          ENNReal.ofReal (w * r ^ 3) ≤ ballVolume (L.metric j c i) p r ∧ b ≤ r := by
    intro ℓ
    obtain ⟨j, hj, c, i, hi, p, hD, r, hr, hrR, hvol, hbr⟩ := hno (max (max N1 N2) ℓ)
    exact ⟨j, hj, c, i, hi, p, hD, r, hr, hrR, hvol, hbr⟩
  choose J hJ c i hthin p hD r hr hrR hvol hbr using hno'
  have hN1' : ∀ ℓ, N1 ≤ J ℓ := fun ℓ => (le_max_left _ _).trans ((le_max_left _ _).trans (hJ ℓ))
  have hN2' : ∀ ℓ, N2 ≤ J ℓ := fun ℓ => (le_max_right _ _).trans ((le_max_left _ _).trans (hJ ℓ))
  have hℓJ : ∀ ℓ, ℓ ≤ J ℓ := fun ℓ => (le_max_right _ _).trans (hJ ℓ)
  -- the core data of TCF02 at the `ℓ`-th bad ball
  have hcore := fun ℓ => hN2 (J ℓ) (hN2' ℓ) (c ℓ) (i ℓ) (hthin ℓ) (p ℓ) (hD ℓ)
  -- the ambient point
  let x : ∀ ℓ, (slices (J ℓ)).stage.Carrier := fun ℓ =>
    (cutPieceMap (L.decomposition (J ℓ) (c ℓ)) (i ℓ) (p ℓ)).val
  have hrD : ∀ ℓ, ENNReal.ofReal (r ℓ) <
      distanceToBoundary ((L.decomposition (J ℓ) (c ℓ)).component (i ℓ))
        (L.metric (J ℓ) (c ℓ) (i ℓ)) (p ℓ) :=
    fun ℓ => (hrR ℓ).trans (hcore ℓ).2.1
  let S : LatePointSequence_S13 F :=
    { slices := fun ℓ => slices (J ℓ)
      times_tendsto := by
        refine tendsto_atTop_mono (fun ℓ => ?_) tendsto_natCast_atTop_atTop
        exact ((Nat.cast_le.mpr (hℓJ ℓ)).trans (htimes (J ℓ)).le)
      point := x }
  have hS : ∀ ℓ, HasNormalizedSeed_S13 (S.slices ℓ) (S.point ℓ) a v := by
    intro ℓ
    obtain ⟨h1, -, -⟩ := LateCutFamily.cutPiece_normalized_transfer_hd_S21 L (J ℓ) (c ℓ) (i ℓ)
      (p ℓ) (r ℓ) (hr ℓ) (hrD ℓ)
    obtain ⟨h2, h3, -⟩ := LateCutFamily.cutPiece_normalized_transfer_hd_S21 L (J ℓ) (c ℓ) (i ℓ)
      (p ℓ) (r ℓ) (hr ℓ) (hrD ℓ)
    have hsec := h1 (hrR ℓ)
    have hvolr : ENNReal.ofReal (w * r ℓ ^ 3) ≤
        ballVolume (slices (J ℓ)).normalizedMetric (x ℓ) (r ℓ) := by
      rw [← h3]; exact hvol ℓ
    exact hseed (slices (J ℓ)).stage.Carrier (slices (J ℓ)).normalizedMetric (x ℓ) w (r ℓ) a hw
      hapos (hab.trans (hbr ℓ)) hsec hvolr
  have hev := hLTF03 S a v 1 hapos hvpos one_pos hS (1 / 4) (by norm_num)
  obtain ⟨ℓ, hℓ⟩ := hev.exists
  -- the center lies in the ball of radius 1
  have hxin : x ℓ ∈ riemannianBallOf (S.slices ℓ).normalizedMetric (S.point ℓ) 1 := by
    change riemannianEDistOf _ (x ℓ) (x ℓ) < ENNReal.ofReal 1
    rw [riemannianEDistOf_self]; exact ENNReal.ofReal_pos.mpr one_pos
  have hdefect : NormalizedRicciDefect_S13 (S.slices ℓ) (S.point ℓ) < 1 / 4 := hℓ _ hxin
  have hR5 : curvatureRadius (slices (J ℓ)).normalizedMetric (x ℓ) ≤ ENNReal.ofReal 5 :=
    curvatureRadius_le_five_of_defect_S21 _ _ hdefect
  obtain ⟨A⟩ := hN1 (J ℓ) (hN1' ℓ) (c ℓ)
  have hcol := LateCutFamily.thin_collapse_S21 L (J ℓ) (c ℓ) (i ℓ) w' A (hthin ℓ) (p ℓ) (hD ℓ)
  exact LateCutFamily.trigger_false_S21 L (J ℓ) (c ℓ) (i ℓ) (hthin ℓ) (p ℓ) hvpos hapos hab
    (hbr ℓ) hw'pos hw₁ hw'₁ (hrR ℓ) (hcore ℓ).2.1 hcol (hS ℓ).2 hR5

end GC.LongTime.Ch12
