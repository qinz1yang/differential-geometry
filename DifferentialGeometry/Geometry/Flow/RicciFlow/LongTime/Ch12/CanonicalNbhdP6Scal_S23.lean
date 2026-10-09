import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CanonicalNbhdP6K2_S23
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CanonicalNbhdP6Level_S23

/-!
# CH12-S23 / K3: `hscal` (normalised scalar upper bound on fixed balls) from P6, `hW2`, `hcenter`

Blueprint LTF03 ¶2: the centre scalar curvature is negative (C1 `hcenter`); if some point of the
ball had `R ≥ C(L)/t`, a point `z` of the ball with `R(z) = C(L)/t` exists (path-connected ball,
intermediate value); by K2 it has a canonical neighbourhood, which is not the round component
(`p` lies in `z`'s component and `R(p) < 0`), so it gives a normalised seed at `z` of constants
`(b, κ)` independent of the sequence; C1 at `z` makes `R̄(z) < 0`, contradicting `R̄(z) = C(L) > 0`.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.LongTime Set Filter
open scoped Manifold ContDiff ENNReal Topology
namespace GC.LongTime.Ch12
universe u

/-- Per-slice step of K3. -/
theorem exists_seed_point_S23 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    {a v L Cq T κ b : ℝ} (hL : 0 < L) (hCq : 1 ≤ Cq) (hb : 0 < b)
    (hbC : b ^ 2 * Hp.C2 * Cq ≤ 1)
    (hK2 : ∀ s : RegularSlice F.observation, T ≤ s.time → ∀ p : s.stage.Carrier,
        HasNormalizedSeed_S13 s p a v →
        ∀ y ∈ riemannianBallOf s.metric p (L * Real.sqrt s.time),
          Cq / s.time ≤ metricScalarAt s.metric y →
          ∃ W : SpatialCanonicalWitness s.metric Hp.epsilon Hp.C1 Hp.C2 y,
            W.capTubeHasNeckChart Hp.epsilon)
    (hκ : ∀ (s : RegularSlice F.observation) (z : s.stage.Carrier)
        (W : SpatialCanonicalWitness s.metric Hp.epsilon Hp.C1 Hp.C2 z),
        W.capTubeHasNeckChart Hp.epsilon → W.alternative.requiresVolume →
        ∀ r : ℝ, 0 < r → r ^ 4 * Tensor0SBundle.normSq0S s.metric z 4 (metricRm04At s.metric z) ≤ 1 →
          ENNReal.ofReal (κ * r ^ 3) ≤ ballVolume s.metric z r)
    (s : RegularSlice F.observation) (hT : T ≤ s.time) (p : s.stage.Carrier)
    (hseed : HasNormalizedSeed_S13 s p a v)
    (hdef : NormalizedRicciDefect_S13 s p < 1)
    (y : s.stage.Carrier) (hy : y ∈ riemannianBallOf s.normalizedMetric p L)
    (hyC : Cq < metricScalarAt s.normalizedMetric y) :
    ∃ z : s.stage.Carrier, metricScalarAt s.normalizedMetric z = Cq ∧
      HasNormalizedSeed_S13 s z b κ := by
  have ht := s.positive
  have hsc : ∀ x, metricScalarAt s.normalizedMetric x = s.time * metricScalarAt s.metric x := by
    intro x
    change metricScalarAt (scaleMetric s.time⁻¹ _ s.metric) x = _
    rw [metricScalarAt_scaleMetric, inv_inv]
  have hpneg : metricScalarAt s.metric p < 0 := by
    have h := scalar_neg_of_defect_S23 s.normalizedMetric p hdef
    rw [hsc] at h
    by_contra hh
    push Not at hh
    nlinarith [mul_nonneg ht.le hh]
  have hCt : 0 < Cq / s.time := by positivity
  have hyR : Cq / s.time < metricScalarAt s.metric y := by
    rw [hsc] at hyC
    rw [div_lt_iff₀ ht]; linarith
  have hy' : y ∈ riemannianBallOf s.metric p (L * Real.sqrt s.time) := by
    rw [← ball_norm_eq_S23]; exact hy
  have hLs : 0 < L * Real.sqrt s.time := mul_pos hL (Real.sqrt_pos.mpr ht)
  obtain ⟨z, hz, hzR, hzc⟩ := exists_level_point_S23 s.metric p y hLs hy'
    (lt_trans hpneg hCt) hyR.le
  obtain ⟨W, hchart⟩ := hK2 s hT p hseed z hz hzR.ge
  have hzpos : 0 < metricScalarAt s.metric z := W.Q_pos
  have hreq : W.alternative.requiresVolume := by
    cases hA : W.alternative with
    | round whole data =>
      exfalso
      have hpd : p ∈ W.domain.carrier := by
        rw [whole, ← connectedComponent_eq hzc]; exact mem_connectedComponent
      have h1 := (W.scalar_bounds p hpd).1
      have hC2 : 1 ≤ Hp.C2 := W.one_le_comparison_constant
      have : 0 < Hp.C2⁻¹ * metricScalarAt s.metric z :=
        mul_pos (inv_pos.mpr (by linarith)) hzpos
      linarith
    | neck data => exact trivial
    | cap data deep => exact trivial
    | positive whole data sec => exact trivial
  refine ⟨z, ?_, ?_⟩
  · rw [hsc, hzR]; field_simp
  · refine seed_of_witness_S23 s z W (hκ s z W hchart hreq) hb ?_
    rw [hzR, mul_div_cancel₀ _ ht.ne']
    exact hbC

theorem hscal_of_P6_S23 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hP6 : P6_S23 Hp)
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
    (hcenter : ∀ (S : LatePointSequence_S13 F) (a v : ℝ), 0 < a → 0 < v →
      (∀ j, HasNormalizedSeed_S13 (S.slices j) (S.point j) a v) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, NormalizedRicciDefect_S13 (S.slices j) (S.point j) < ε) :
    ∀ a v L : ℝ, 0 < a → 0 < v → 0 < L → ∃ K : ℝ,
      ∀ S : LatePointSequence_S13 F,
        (∀ j, HasNormalizedSeed_S13 (S.slices j) (S.point j) a v) →
        ∀ᶠ j in atTop, ∀ y ∈ riemannianBallOf (S.slices j).normalizedMetric (S.point j) L,
          metricScalarAt (S.slices j).normalizedMetric y ≤ K := by
  intro a v L ha hv hL
  obtain ⟨Cq, T, hCq, hT, hK2⟩ := hK2_of_P6_S23 Hp hP6 hW2 a v L ha hv hL
  obtain ⟨κ, hκpos, hκ0⟩ := exists_ball_volume_of_spatialCanonicalWitness.{u}
    Hp.epsilon Hp.C1 Hp.C2
  have hC2 : 1 ≤ Hp.C2 := by
    have := Hp.C2_ge_one; exact this
  set b : ℝ := (Real.sqrt (Hp.C2 * Cq))⁻¹ with hbdef
  have hCC : 0 < Hp.C2 * Cq := by nlinarith
  have hb : 0 < b := inv_pos.mpr (Real.sqrt_pos.mpr hCC)
  have hbC : b ^ 2 * Hp.C2 * Cq ≤ 1 := by
    rw [hbdef, inv_pow, Real.sq_sqrt hCC.le, mul_assoc, inv_mul_cancel₀ hCC.ne']
  refine ⟨Cq, fun S hS => ?_⟩
  by_contra hfail
  have hT' : ∀ᶠ j in atTop, T ≤ (S.slices j).time := S.times_tendsto.eventually_ge_atTop T
  have hd : ∀ᶠ j in atTop, NormalizedRicciDefect_S13 (S.slices j) (S.point j) < 1 :=
    hcenter S a v ha hv hS 1 one_pos
  rw [Filter.not_eventually] at hfail
  have hfr : ∃ᶠ j in atTop, (T ≤ (S.slices j).time ∧
      NormalizedRicciDefect_S13 (S.slices j) (S.point j) < 1) ∧
      ∃ y ∈ riemannianBallOf (S.slices j).normalizedMetric (S.point j) L,
        Cq < metricScalarAt (S.slices j).normalizedMetric y := by
    refine (hfail.and_eventually (hT'.and hd)).mono fun j hj => ⟨hj.2, ?_⟩
    have h1 := hj.1
    push Not at h1
    exact h1
  obtain ⟨φ, hφ, hφj⟩ := Filter.extraction_of_frequently_atTop hfr
  have hz : ∀ j, ∃ z : (S.slices (φ j)).stage.Carrier,
      metricScalarAt (S.slices (φ j)).normalizedMetric z = Cq ∧
        HasNormalizedSeed_S13 (S.slices (φ j)) z b κ := by
    intro j
    obtain ⟨⟨hTj, hdj⟩, y, hy, hyC⟩ := hφj j
    exact exists_seed_point_S23 Hp hL hCq hb hbC hK2
      (fun s z W hchart hreq r hr hcurv => hκ0 W hchart hreq r hr hcurv)
      (S.slices (φ j)) hTj (S.point (φ j)) (hS (φ j)) hdj y hy hyC
  choose z hzR hzseed using hz
  let S' : LatePointSequence_S13 F :=
    { slices := fun j => S.slices (φ j)
      times_tendsto := S.times_tendsto.comp hφ.tendsto_atTop
      point := z }
  obtain ⟨j, hj⟩ := (hcenter S' b κ hb hκpos hzseed 1 one_pos).exists
  have hneg := scalar_neg_of_defect_S23 (S.slices (φ j)).normalizedMetric (z j) hj
  have hCq0 : 0 < Cq := by linarith
  rw [hzR j] at hneg
  linarith

end GC.LongTime.Ch12
