import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82ComponentVolume_CX11
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KcanVolumeChain_O14
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862Pinching_CX12
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MacroWholeBallWbd01

/-!
# CH12-S127, group 1: hFE-vol (the centre-volume conjunct of hFE) from the terminal volume premise at `p`

`[FROZEN v3] CH12-S127 hFE`: hFE v3 = hFE v2 (NO new binder).  The "hvol" of the lead's ruling is the premise
`ofReal (w ρ³) ≤ ballVolume s.metric p ρ` that hFE v2 already carries (= the terminal's hT2 volume at `r := ρ`).
The F-S96-1 claim "not derivable at `q ∈ B(p,ρ) \ B(p,ρ/2)`" is WITHDRAWN: Bishop–Gromov at `q` directly would need
curvature control on `B(q, 2ρ) ⊄ B(p, 2ρ)`, but a midpoint `m` of a short path `p ⇝ q` removes this
(`d(p,m) ≤ ρ/2`, `d(m,q) < ρ/2`; `B(p,ρ) ⊆ B(m,3ρ/2) ⊆ B(p,2ρ)`, `B(m,ρ/2) ⊆ B(q,ρ) ⊆ B(p,2ρ)`):

* `centre_volume_S127`: `sec ≥ -ρ⁻²` on `B(p,2ρ)` and `vol B(p,ρ) ≥ wρ³` ⇒ `vol B(q,ρ') ≥ w/(27 e⁵) ρ'³` for
  `q ∈ B(p,ρ)`, `ρ' ≤ ρ` (three local Bishop–Gromov steps `m`, `q`, `ballVolume_small_of_sec_component_CX11`);
* `hFEvol_S127`: the slice form (history metric at the top stage, `HEq q' q`): `sec ≥ -ρ⁻²` on `B(p,2ρ)` from
  `R ≤ C0/ρ²` there by `slice_history_sectional_of_scalar_CX12` (needs `ρ ≤ b √s.time`, `b` depending on `C0` only).
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Collapse
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch12

universe u

section Abstract

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [T2Space M] [SigmaCompactSpace M] in
/-- Ball inclusion by the triangle inequality: `d(x,y) ≤ a` (or `< a`), `r + a ≤ R` ⇒ `B(y,r) ⊆ B(x,R)`. -/
theorem ball_subset_of_edist_S127 (g : SmoothRiemannianMetric ThreeModel M) {x y : M} {a r R : ℝ}
    (ha : 0 ≤ a) (hr : 0 ≤ r) (hxy : riemannianEDistOf g x y ≤ ENNReal.ofReal a) (hR : r + a ≤ R) :
    riemannianBallOf g y r ⊆ riemannianBallOf g x R := by
  intro z hz
  change riemannianEDistOf g y z < ENNReal.ofReal r at hz
  change riemannianEDistOf g x z < ENNReal.ofReal R
  calc riemannianEDistOf g x z ≤ riemannianEDistOf g x y + riemannianEDistOf g y z :=
        riemannianEDistOf_triangle _ _ _ _
    _ < ENNReal.ofReal a + ENNReal.ofReal r :=
        ENNReal.add_lt_add_of_le_of_lt (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hxy) hxy hz
    _ = ENNReal.ofReal (a + r) := (ENNReal.ofReal_add ha hr).symm
    _ ≤ ENNReal.ofReal R := ENNReal.ofReal_le_ofReal (by linarith)

/-- **Centre volume at `q ∈ B(p,ρ)` from the volume of `B(p,ρ)`** (two-step Bishop–Gromov through a midpoint). -/
theorem centre_volume_S127 (g : SmoothRiemannianMetric ThreeModel M) (hg : RiemannianMetricComplete g)
    {p q : M} {ρ w ρ' : ℝ} (hρ : 0 < ρ)
    (hsec : ∀ z ∈ riemannianBallOf g p (2 * ρ), SectionalBoundedBelowAt g z (-(ρ ^ 2)⁻¹))
    (hvol : ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume g p ρ) (hq : q ∈ riemannianBallOf g p ρ)
    (hρ' : 0 < ρ') (hρ'ρ : ρ' ≤ ρ) :
    ENNReal.ofReal (w / (27 * Real.exp 5) * ρ' ^ 3) ≤ ballVolume g q ρ' := by
  have hsecq : ∀ z ∈ riemannianBallOf g p (2 * ρ), SectionalBoundedBelowAt g z (-(ρ⁻¹ ^ 2)) := by
    intro z hz
    simpa only [inv_pow] using hsec z hz
  have hq0 : 0 ≤ ρ⁻¹ := inv_nonneg.mpr hρ.le
  -- midpoint `m`
  have hq' : riemannianEDistOf g p q < ENNReal.ofReal ρ := hq
  obtain ⟨m, hpm, hmq⟩ := exists_intermediate_point_O14 g (c := ρ / 2) (D := ρ) (by positivity)
    (by linarith) hq'
  have hmq' : riemannianEDistOf g q m < ENNReal.ofReal (ρ / 2) := by
    rw [riemannianEDistOf_comm]
    have : ρ - ρ / 2 = ρ / 2 := by ring
    rwa [this] at hmq
  have hqm : riemannianEDistOf g q m ≤ ENNReal.ofReal (ρ / 2) := hmq'.le
  have hmp : riemannianEDistOf g m p ≤ ENNReal.ofReal (ρ / 2) := by
    rw [riemannianEDistOf_comm]; exact hpm
  -- `B(p,ρ) ⊆ B(m,3ρ/2) ⊆ B(p,2ρ)`
  have h1 : riemannianBallOf g p ρ ⊆ riemannianBallOf g m (3 * ρ / 2) :=
    ball_subset_of_edist_S127 g (a := ρ / 2) (by positivity) hρ.le hmp (by linarith)
  have h2 : riemannianBallOf g m (3 * ρ / 2) ⊆ riemannianBallOf g p (2 * ρ) :=
    ball_subset_of_edist_S127 g (a := ρ / 2) (by positivity) (by positivity) hpm (by linarith)
  have hv1 : ENNReal.ofReal ((8 * w / 27) * (3 * ρ / 2) ^ 3) ≤ ballVolume g m (3 * ρ / 2) := by
    have he : (8 * w / 27) * (3 * ρ / 2) ^ 3 = w * ρ ^ 3 := by ring
    rw [he]; exact hvol.trans (MeasureTheory.measure_mono h1)
  have hb1 := ballVolume_small_of_sec_component_CX11 g hg m (q := ρ⁻¹) (s := ρ / 2) (R := 3 * ρ / 2)
    hq0 (by positivity) (by linarith) (fun z hz => hsecq z (h2 hz)) hv1
  have he1 : 2 * ρ⁻¹ * (3 * ρ / 2) = (3 : ℝ) := by field_simp
  rw [he1] at hb1
  -- `B(m,ρ/2) ⊆ B(q,ρ) ⊆ B(p,2ρ)`
  have h3 : riemannianBallOf g m (ρ / 2) ⊆ riemannianBallOf g q ρ :=
    ball_subset_of_edist_S127 g (a := ρ / 2) (by positivity) (by positivity) hqm (by linarith)
  have h4 : riemannianBallOf g q ρ ⊆ riemannianBallOf g p (2 * ρ) := by
    refine ball_subset_of_edist_S127 g (a := ρ) hρ.le hρ.le hq'.le (by linarith)
  have hv2 : ENNReal.ofReal ((w / (27 * Real.exp 3)) * ρ ^ 3) ≤ ballVolume g q ρ := by
    have he : 8 * w / 27 * (ρ / 2) ^ 3 / Real.exp 3 = (w / (27 * Real.exp 3)) * ρ ^ 3 := by
      field_simp; ring
    rw [he] at hb1
    exact hb1.trans (MeasureTheory.measure_mono h3)
  have hb2 := ballVolume_small_of_sec_component_CX11 g hg q (q := ρ⁻¹) (s := ρ') (R := ρ)
    hq0 hρ' hρ'ρ (fun z hz => hsecq z (h4 hz)) hv2
  have he2 : 2 * ρ⁻¹ * ρ = (2 : ℝ) := by field_simp
  rw [he2] at hb2
  have hfin : w / (27 * Real.exp 3) * ρ' ^ 3 / Real.exp 2 = w / (27 * Real.exp 5) * ρ' ^ 3 := by
    have hexp : Real.exp 5 = Real.exp 3 * Real.exp 2 := by rw [← Real.exp_add]; norm_num
    rw [hexp]; field_simp
  rw [hfin] at hb2
  exact hb2

end Abstract

section Slice

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}

/-- **hFE-vol (slice form).**  For `0 ≤ C0` there is `b > 0` (depending on `C0` and `Hp` only) such that, on a slice,
`ρ ≤ b √s.time`, `vol B(p,ρ) ≥ wρ³` and `R ≤ C0/ρ²` on `B(p,2ρ)` give, for every `q ∈ B(p,ρ)`, `q'` with
`HEq q' q` and `ρ' ≤ ρ`: `vol B(q',ρ') ≥ w/(27 e⁵) ρ'³` in the history metric at the top stage (the form of the
last conjunct of hFE v2 with `w₁ := w/(27 e⁵)`, valid for all `ρ' ≤ ρ`, in particular `ρ' ≤ θ'ρ`, `θ' ≤ 1`). -/
theorem hFEvol_S127 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) {C0 : ℝ} (hC0 : 0 ≤ C0) :
    ∃ b : ℝ, 0 < b ∧ ∀ (s : RegularSlice F.observation) (p : s.stage.Carrier) (ρ w : ℝ), 0 < ρ →
      ρ ≤ b * Real.sqrt s.time →
      ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.metric p ρ →
      (∀ x ∈ riemannianBallOf s.metric p (2 * ρ), metricScalarAt s.metric x ≤ C0 / ρ ^ 2) →
      ∀ q ∈ riemannianBallOf s.metric p ρ, ∀ q' : (s.history.stageAt (sliceTop_S8 s)).Carrier,
        HEq q' q → ∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ ρ →
        ENNReal.ofReal (w / (27 * Real.exp 5) * ρ' ^ 3) ≤
          ballVolume (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) q' ρ' := by
  obtain ⟨b, hb, hsec⟩ := slice_history_sectional_of_scalar_CX12 Hp hC0
  refine ⟨b, hb, fun s p ρ w hρ hρb hvol hR q hq q' hq' ρ' hρ' hρ'ρ => ?_⟩
  have hgen : ∀ (j : Fin (s.history.eventCount + 1)) (hj : s.history.activeStage (sliceTop_S8 s) = j)
      (p q : (s.history.stage j).Carrier),
      ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume (s.history.stageMetric j s.time) p ρ →
      (∀ x ∈ riemannianBallOf (s.history.stageMetric j s.time) p (2 * ρ),
        metricScalarAt (s.history.stageMetric j s.time) x ≤ C0 / ρ ^ 2) →
      q ∈ riemannianBallOf (s.history.stageMetric j s.time) p ρ →
      ∀ q' : (s.history.stageAt (sliceTop_S8 s)).Carrier, HEq q' q →
      ENNReal.ofReal (w / (27 * Real.exp 5) * ρ' ^ 3) ≤
        ballVolume (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) q' ρ' := by
    intro j hj
    subst hj
    intro p q hvol hR hq q' hq'
    cases hq'
    refine centre_volume_S127 _ (RiemannianMetricComplete.of_compact _) hρ ?_ hvol hq hρ' hρ'ρ
    intro z hz
    exact hsec s (sliceTop_S8 s) z ρ hρ hρb (hR z hz)
  exact hgen (Fin.last _) s.history.activeStage_at_horizon p q hvol hR hq q' hq'

end Slice

section Assembly

open DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}

/-- **`hFE v3` from `hFE-core` and the centre volume.**  `hcore` = hFE v2 (`hFE` binder of `hZT_of_kl82_S113`) with the
produced constant `w₁` and the last conjunct (centre volume) removed -- the exact statement of the hFE-core lane
(G2/G3); the conclusion is the hFE v2 binder verbatim (= `[FROZEN v3] CH12-S127 hFE`, no new binder), with
`w₁ := w / (27 e⁵)`, `bF := min bF_core b_vol`, `θ₁ := min θ₁_core 1`. -/
theorem hFE_of_core_S127 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (hcore : ∀ w : ℝ, 0 < w → ∀ Λ : ℝ, 1 ≤ Λ → ∀ (θ Dcap C0 : ℝ), 0 < θ → 0 < C0 → StandardCap.transitionEnd + 3 < Dcap →
          ∃ (bF TF K τ₁ τ₂ θ₁ εF : ℝ), 0 < bF ∧ 0 < TF ∧ 0 < K ∧ 0 < τ₁ ∧ 0 < τ₂ ∧ 0 < θ₁ ∧ 0 < εF ∧
          ∀ s : RegularSlice F.observation, TF ≤ s.time → ∀ T₀ : ℝ, TF ≤ T₀ → T₀ ≤ s.time →
          ∀ (pp : CutoffParameters)
            (records : ∀ i : Fin (sliceHistoryR_O3 F s).eventCount,
              T₀ - θ ≤ (sliceHistoryR_O3 F s).time i.succ →
              GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i pp),
            pp.delta = Hp.parameters.delta → pp.neckRadius = Hp.parameters.neckRadius →
            pp.fixed = Hp.parameters.fixed → pp.recenterConstant = Hp.parameters.recenterConstant →
            32 * (Dcap + 1) + 2 ≤ pp.modelRadius →
            pp.modelAccuracy ≤ εF → 4 ≤ pp.modelOrder →
            (∀ i hi b, linkedCanonicalWindow_O2 ((records i hi).static b)) →
          ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ → ρ ≤ bF * Real.sqrt s.time →
            (∃ n, ∃ i : Fin (F.tower.history n).eventCount, ∃ h,
              (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time ∧
              ρ < Λ * (Hp.records n i).nominalRadius h) →
            (∃ z ∈ connectedComponent p, ¬ SectionalBoundedBelowAt s.metric z 0) →
            (∀ q ∈ riemannianBallOf s.metric p ρ,
              SectionalBoundedBelowAt s.metric q (-(ρ ^ 2)⁻¹)) →
            ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.metric p ρ →
            (∀ x ∈ riemannianBallOf s.metric p (2 * ρ), metricScalarAt s.metric x ≤ C0 / ρ ^ 2) →
            ∀ q ∈ riemannianBallOf s.metric p ρ,
              ¬ (∃ (j : Fin (sliceHistoryR_O3 F s).eventCount)
                (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ)
                (hl : j.succ ≤ Fin.last (sliceHistoryR_O3 F s).eventCount)
                (B : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory j.succ
                  (Fin.last (sliceHistoryR_O3 F s).eventCount) hl q)
                (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
                (x : standardCapWindow pp.modelRadius),
                B.point j.succ le_rfl hl = ((records j hj).static b).window x ∧
                  ‖x.val‖ < Dcap + 1 ∧
                  s.time - (sliceHistoryR_O3 F s).time j.succ ≤
                    θ * (((records j hj).static b).neck.scale)⁻¹) →
            ∀ θ' : ℝ, 0 < θ' → θ' ≤ θ₁ → ∀ q' : (s.history.stageAt (sliceTop_S8 s)).Carrier, HEq q' q →
              ∃ (a' : Icc (0 : ℝ) s.history.horizon) (hat : a' ≤ sliceTop_S8 s)
                (X : BackwardPointTrace s.history (s.history.activeStage a')
                  (s.history.activeStage (sliceTop_S8 s)) (s.history.activeStage_mono hat) q'),
                (a' : ℝ) = s.time - τ₁ * (θ' * ρ) ^ 2 ∧
                (∀ (u : Icc (0 : ℝ) s.history.horizon) (hau : a' ≤ u) (hut : u ≤ sliceTop_S8 s),
                  s.history.isTracedRegion u
                    (X.point (s.history.activeStage u) (s.history.activeStage_mono hau)
                      (s.history.activeStage_mono hut))
                    (θ' * ρ / 40) (τ₂ * (θ' * ρ) ^ 2) (K * ((θ' * ρ) ^ 2)⁻¹))) :
    ∀ w : ℝ, 0 < w → ∀ Λ : ℝ, 1 ≤ Λ → ∀ (θ Dcap C0 : ℝ), 0 < θ → 0 < C0 → StandardCap.transitionEnd + 3 < Dcap →
          ∃ (bF TF K τ₁ τ₂ w₁ θ₁ εF : ℝ), 0 < bF ∧ 0 < TF ∧ 0 < K ∧ 0 < τ₁ ∧ 0 < τ₂ ∧ 0 < w₁ ∧ 0 < θ₁ ∧ 0 < εF ∧
          ∀ s : RegularSlice F.observation, TF ≤ s.time → ∀ T₀ : ℝ, TF ≤ T₀ → T₀ ≤ s.time →
          ∀ (pp : CutoffParameters)
            (records : ∀ i : Fin (sliceHistoryR_O3 F s).eventCount,
              T₀ - θ ≤ (sliceHistoryR_O3 F s).time i.succ →
              GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i pp),
            pp.delta = Hp.parameters.delta → pp.neckRadius = Hp.parameters.neckRadius →
            pp.fixed = Hp.parameters.fixed → pp.recenterConstant = Hp.parameters.recenterConstant →
            32 * (Dcap + 1) + 2 ≤ pp.modelRadius →
            pp.modelAccuracy ≤ εF → 4 ≤ pp.modelOrder →
            (∀ i hi b, linkedCanonicalWindow_O2 ((records i hi).static b)) →
          ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ → ρ ≤ bF * Real.sqrt s.time →
            (∃ n, ∃ i : Fin (F.tower.history n).eventCount, ∃ h,
              (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time ∧
              ρ < Λ * (Hp.records n i).nominalRadius h) →
            (∃ z ∈ connectedComponent p, ¬ SectionalBoundedBelowAt s.metric z 0) →
            (∀ q ∈ riemannianBallOf s.metric p ρ,
              SectionalBoundedBelowAt s.metric q (-(ρ ^ 2)⁻¹)) →
            ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.metric p ρ →
            (∀ x ∈ riemannianBallOf s.metric p (2 * ρ), metricScalarAt s.metric x ≤ C0 / ρ ^ 2) →
            ∀ q ∈ riemannianBallOf s.metric p ρ,
              ¬ (∃ (j : Fin (sliceHistoryR_O3 F s).eventCount)
                (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ)
                (hl : j.succ ≤ Fin.last (sliceHistoryR_O3 F s).eventCount)
                (B : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory j.succ
                  (Fin.last (sliceHistoryR_O3 F s).eventCount) hl q)
                (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
                (x : standardCapWindow pp.modelRadius),
                B.point j.succ le_rfl hl = ((records j hj).static b).window x ∧
                  ‖x.val‖ < Dcap + 1 ∧
                  s.time - (sliceHistoryR_O3 F s).time j.succ ≤
                    θ * (((records j hj).static b).neck.scale)⁻¹) →
            ∀ θ' : ℝ, 0 < θ' → θ' ≤ θ₁ → ∀ q' : (s.history.stageAt (sliceTop_S8 s)).Carrier, HEq q' q →
              ∃ (a' : Icc (0 : ℝ) s.history.horizon) (hat : a' ≤ sliceTop_S8 s)
                (X : BackwardPointTrace s.history (s.history.activeStage a')
                  (s.history.activeStage (sliceTop_S8 s)) (s.history.activeStage_mono hat) q'),
                (a' : ℝ) = s.time - τ₁ * (θ' * ρ) ^ 2 ∧
                (∀ (u : Icc (0 : ℝ) s.history.horizon) (hau : a' ≤ u) (hut : u ≤ sliceTop_S8 s),
                  s.history.isTracedRegion u
                    (X.point (s.history.activeStage u) (s.history.activeStage_mono hau)
                      (s.history.activeStage_mono hut))
                    (θ' * ρ / 40) (τ₂ * (θ' * ρ) ^ 2) (K * ((θ' * ρ) ^ 2)⁻¹)) ∧
                (∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ θ' * ρ →
                  ENNReal.ofReal (w₁ * ρ' ^ 3) ≤
                    ballVolume (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) q' ρ') := by
  intro w hw Λ hΛ θ Dcap C0 hθ hC0 hDcap
  obtain ⟨bF, TF, K, τ₁, τ₂, θ₁, εF, hbF, hTF, hK, hτ₁, hτ₂, hθ₁, hεF, hcs⟩ :=
    hcore w hw Λ hΛ θ Dcap C0 hθ hC0 hDcap
  obtain ⟨bV, hbV, hvolc⟩ := hFEvol_S127 Hp hC0.le
  refine ⟨min bF bV, TF, K, τ₁, τ₂, w / (27 * Real.exp 5), min θ₁ 1, εF, lt_min hbF hbV, hTF, hK, hτ₁,
    hτ₂, by positivity, lt_min hθ₁ one_pos, hεF, ?_⟩
  intro s hs T₀ hT₀a hT₀b pp records h1 h2 h3 h4 hmr hacc hord hlink p ρ hρ hρb hev hnn hsec hvol hR q hq hnc
    θ' hθ' hθ'1 q' hq'
  have hρF : ρ ≤ bF * Real.sqrt s.time :=
    hρb.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _))
  have hρV : ρ ≤ bV * Real.sqrt s.time :=
    hρb.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg _))
  obtain ⟨a', hat, X, haeq, hTFam⟩ := hcs s hs T₀ hT₀a hT₀b pp records h1 h2 h3 h4 hmr hacc hord hlink
    p ρ hρ hρF hev hnn hsec hvol hR q hq hnc θ' hθ' (hθ'1.trans (min_le_left _ _)) q' hq'
  refine ⟨a', hat, X, haeq, hTFam, fun ρ' hρ' hρ'le => ?_⟩
  have hθ1 : θ' ≤ 1 := hθ'1.trans (min_le_right _ _)
  have hle : θ' * ρ ≤ ρ := (mul_le_mul_of_nonneg_right hθ1 hρ.le).trans_eq (one_mul ρ)
  exact hvolc s p ρ w hρ hρV hvol hR q hq q' hq' ρ' hρ' (hρ'le.trans hle)

end Assembly

end GC.LongTime.Ch12
