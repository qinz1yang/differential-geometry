import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedGeom_S117
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.OuterThinStatic_S35
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CoverCkErr_S90
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MetricWindow_S49

set_option autoImplicit false

/-! # CH12-O76 G1: thick basepoint transfer and bounded preimage of `H'.basepoint`

`basepoint_preimage_O76`: for models `H`, `H'` (a truncation of `H'` given) there is `D ≥ 0` such that
every smooth embedding `f` of `B_H(bp, R)` (`R ≥ 16 (D + 1)`) into `H'` with `ckErr⁰ < 1/8` hits
`H'.basepoint` from inside `B_H(bp, 16 (D + 1))`.
* thickness transfer: `seed_geom_S117` (radius `1`): `vol_H B(bp, 1/2) / 8 ≤ vol_H' B(f bp, 1)`;
* thick part of `H'` is bounded: `hpi07_log_bound_gen_S35` (truncation `Tr'`, radius `1`):
  `d(bp', f bp) ≤ D := C₀ + C₁ log(1/w)`, `w` depending on `H` only;
* cover: `seed_geom_S117` (radius `D + 1`): `B_H'(f bp, D + 1) ⊆ f '' B_H(bp, 16 (D + 1))`.
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open Set Manifold TopologicalSpace
open scoped Manifold ContDiff ENNReal

universe u

namespace GC.LongTime.Ch12

/-- Metric window `1/4 ≤ f^*g'/h ≤ 3` from `ckErr⁰ < 1/8`. -/
theorem window_of_ckErr0_O76 (H H' : FiniteVolumeHyperbolicModel.{u}) (f : H.Carrier → H'.Carrier)
    (p : H.Carrier) (h0 : ckErr_O19 H H'.metric 1 f 0 p < 1 / 8) (w : TangentSpace (𝓡 3) p) :
    (1 / 4 : ℝ) * H.metric.inner p w w ≤
        H'.metric.inner (f p) (mfderiv (𝓡 3) (𝓡 3) f p w) (mfderiv (𝓡 3) (𝓡 3) f p w) ∧
      H'.metric.inner (f p) (mfderiv (𝓡 3) (𝓡 3) f p w) (mfderiv (𝓡 3) (𝓡 3) f p w) ≤
        3 * H.metric.inner p w w := by
  have hlo := pullback_inner_ge_of_ckErr_S90 H H'.metric 1 f p h0 w
  have hhi := pullback_inner_le_of_ckErr_S49 H H'.metric 1 f p h0 w
  have hnn := metric_inner_self_nonneg H.metric p w
  constructor <;> nlinarith

/-- **G1.** Thick basepoint ⇒ the preimage of `H'.basepoint` lies in a ball of radius `16 (D + 1)`,
`D` uniform in `R`, `U`, `f`. -/
theorem basepoint_preimage_O76 (H H' : FiniteVolumeHyperbolicModel.{u})
    (Tr' : HyperbolicTruncation H') :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (R : ℝ) (U : Opens H.Carrier) (f : H.Carrier → H'.Carrier),
      16 * (D + 1) ≤ R →
      riemannianBallOf H.metric H.basepoint R ⊆ U →
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U →
      IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) →
      (∀ p ∈ riemannianBallOf H.metric H.basepoint R, ckErr_O19 H H'.metric 1 f 0 p < 1 / 8) →
      ∃ p₀ ∈ riemannianBallOf H.metric H.basepoint (16 * (D + 1)), f p₀ = H'.basepoint := by
  classical
  -- thickness of the basepoint of `H`
  set V₀ := ballVolume H.metric H.basepoint (1 / 2) with hV₀
  have : (Integral.Measure.riemannianVolumeMeasure (𝓡 3) H.Carrier H.metric).IsOpenPosMeasure :=
    Integral.Measure.riemannianVolumeMeasure_isOpenPosMeasure H.metric
  have hV₀pos : 0 < V₀ := (isOpen_riemannianBallOf H.metric H.basepoint (1 / 2)).measure_pos _
    ⟨H.basepoint, by
      change riemannianEDistOf H.metric H.basepoint H.basepoint < ENNReal.ofReal (1 / 2)
      rw [riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr (by norm_num)⟩
  have hV₀top : V₀ ≠ ⊤ :=
    ne_top_of_le_ne_top H.finite_volume.ne (MeasureTheory.measure_mono (subset_univ _))
  have hV₀r : 0 < V₀.toReal := ENNReal.toReal_pos hV₀pos.ne' hV₀top
  set w : ℝ := min 1 ((1 / 8) * V₀.toReal) with hw
  have hw0 : 0 < w := lt_min one_pos (by positivity)
  have hw1 : w ≤ 1 := min_le_left _ _
  -- the thick part of `H'` is bounded
  obtain ⟨C₀, C₁, hC₀, hC₁, hlog⟩ := hpi07_log_bound_gen_S35 Tr' H'.basepoint (ρ := 1) one_pos
  have hlogw : 0 ≤ Real.log (1 / w) := Real.log_nonneg (by rw [le_div_iff₀ hw0]; linarith)
  refine ⟨C₀ + C₁ * Real.log (1 / w), by positivity, ?_⟩
  intro R U f hR hRU hf hemb hck
  set D := C₀ + C₁ * Real.log (1 / w) with hD
  have hD0 : 0 ≤ D := by positivity
  let U₀ : Opens H.Carrier :=
    ⟨riemannianBallOf H.metric H.basepoint R, isOpen_riemannianBallOf _ _ _⟩
  have hf₀ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f (U₀ : Set H.Carrier) := hf.mono hRU
  have hinj : InjOn f (U₀ : Set H.Carrier) := fun x hx y hy hxy =>
    congrArg Subtype.val (hemb.isEmbedding.injective (a₁ := ⟨x, hRU hx⟩) (a₂ := ⟨y, hRU hy⟩) hxy)
  have hlow : ∀ p ∈ (U₀ : Set H.Carrier), ∀ v : TangentSpace (𝓡 3) p,
      (1 / 4 : ℝ) * H.metric.inner p v v ≤
        H'.metric.inner (f p) (mfderiv (𝓡 3) (𝓡 3) f p v) (mfderiv (𝓡 3) (𝓡 3) f p v) :=
    fun p hp v => (window_of_ckErr0_O76 H H' f p (hck p hp) v).1
  have hup : ∀ p ∈ (U₀ : Set H.Carrier), ∀ v : TangentSpace (𝓡 3) p,
      H'.metric.inner (f p) (mfderiv (𝓡 3) (𝓡 3) f p v) (mfderiv (𝓡 3) (𝓡 3) f p v) ≤
        3 * H.metric.inner p v v :=
    fun p hp v => (window_of_ckErr0_O76 H H' f p (hck p hp) v).2
  have : LocallyCompactSpace H'.Carrier :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) H'.Carrier
  have : T3Space H'.Carrier := inferInstance
  -- step 1: volume at the image of the basepoint
  obtain ⟨-, hvol, -⟩ := seed_geom_S117 H H'.metric f U₀ hf₀ hinj hlow hup (R := 8) (a := 1)
    one_pos (by norm_num) (riemannianBallOf_mono _ _ (by linarith))
  have hthick : ENNReal.ofReal w ≤ ballVolume H'.metric (f H.basepoint) 1 := by
    refine le_trans ?_ hvol
    calc ENNReal.ofReal w ≤ ENNReal.ofReal ((1 / 8) * V₀.toReal) :=
          ENNReal.ofReal_le_ofReal (min_le_right _ _)
      _ = ENNReal.ofReal (1 / 8) * V₀ := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hV₀top]
  have hd := hlog w hw0 hw1 (f H.basepoint) hthick
  -- step 2: cover of `B_H'(f bp, D + 1)`
  obtain ⟨hcov, -, -⟩ := seed_geom_S117 H H'.metric f U₀ hf₀ hinj hlow hup (R := 8 * (D + 1))
    (a := D + 1) (by linarith) (by linarith) (riemannianBallOf_mono _ _ (by linarith))
  have hmem : H'.basepoint ∈ riemannianBallOf H'.metric (f H.basepoint) (D + 1) := by
    change riemannianEDistOf H'.metric (f H.basepoint) H'.basepoint < ENNReal.ofReal (D + 1)
    rw [riemannianEDistOf_comm]
    exact hd.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith))
  obtain ⟨p₀, hp₀, hfp₀⟩ := hcov hmem
  refine ⟨p₀, ?_, hfp₀⟩
  rwa [show 16 * (D + 1) = 2 * (8 * (D + 1)) by ring]

end GC.LongTime.Ch12
