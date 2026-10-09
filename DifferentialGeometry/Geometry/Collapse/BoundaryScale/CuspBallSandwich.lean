import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspVolumeTransfer
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspCollarOneEndLowerDistance
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspBoundaryBandApplications
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.HalfProductVolume

/-!
# The small-ball sandwich near the boundary (statement V.3)

For a nearly cuspidal boundary `B` with `0 ≤ δ ≤ 1/1000` and a point `q` with `d(q, ∂W) ≤ b₀ = 1/100`
(`NearlyCuspidalBoundary.ball_sandwich`, the interface `V_ball_sandwich` verbatim): `q = e_i(x, z₁)`
with `0 ≤ z₁ ≤ b₀/√(1-δ)` (E.4, one choice for all radii), and for `0 < r ≤ b₀`

`e(E_{r/λ₊}) ⊆ B_g(q, r) ⊆ e(E_{r/λ₋})`,  `λ₋³ F(r/λ₊) ≤ V_q(r) ≤ λ₊³ F(r/λ₋)`,

where `E_ρ = {(t, z) : 0 ≤ z, (z - z₁)² + d_T(x, t)² < ρ²}`, `F(ρ) = μ₀(E_ρ)` (flat measure
`vol_{g_T} ⊗ Lebesgue`), `λ₊ = √(1+δ)`, `λ₋ = √((1-δ) e^{-h₀})`, `h₀ = 4/100`.

* inner inclusion: the flat upper distance up to the boundary
  (`CuspEmbedding.image_subset_ball_flat`, lane B-5a);
* outer inclusion: the one-endpoint lower distortion with `z₀ = 0`, `a = h₀`
  (`CuspEmbedding.exists_preimage_frozen_le_riemannianEDistOf`; margins `z₁ ≤ 2/100 = h₀/2`,
  `r ≤ 1/100 ≤ √(1-δ) h₀/2`);
* volumes: V.1 (`CuspEmbedding.volume_transfer`) on `E_ρ` (Borel, heights `< 100`) and
  `e^{-h₀} μ₀ ≤ μ_H ≤ μ₀` at heights in `[0, h₀]`; the weaker constant `λ₋³ ≤ (1-δ)^{3/2} e^{-h₀}`
  is kept (design D4).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Function
open DifferentialGeometry DifferentialGeometry.Integral.Measure GC.Endpoint
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff ENNReal Real

namespace DifferentialGeometry.Geometry.Collapse

private local instance instMeasTorus : MeasurableSpace Torus := borel Torus
private local instance instBorelTorus : BorelSpace Torus := ⟨rfl⟩

universe u

/-- The flat half ellipsoids `E_ρ = {(t, z) : 0 ≤ z, (z - z₁)² + d_T(x, t)² < ρ²}` are Borel. -/
theorem measurableSet_halfEllipsoid (gT : SmoothRiemannianMetric torusModel Torus) (x : Torus)
    (z₁ ρ : ℝ) :
    MeasurableSet[borel (Torus × ℝ)] {p : Torus × ℝ | 0 ≤ p.2 ∧
      (p.2 - z₁) ^ 2 + (riemannianEDistOf gT x p.1).toReal ^ 2 < ρ ^ 2} := by
  let : MeasurableSpace (Torus × ℝ) := borel (Torus × ℝ)
  have : BorelSpace (Torus × ℝ) := ⟨rfl⟩
  have hD : Continuous fun t : Torus => (riemannianEDistOf gT x t).toReal :=
    ENNReal.continuousOn_toReal.comp_continuous
      (Geometry.Riemannian.continuous_riemannianEDist gT x) fun t => riemannianEDistOf_ne_top gT x t
  exact (isClosed_le continuous_const continuous_snd).measurableSet.inter
    (isOpen_lt (((continuous_snd.sub continuous_const).pow 2).add ((hD.comp continuous_fst).pow 2))
      continuous_const).measurableSet

/-- The flat half ellipsoids have finite `μ₀`-measure. -/
theorem halfEllipsoid_measure_ne_top (gT : SmoothRiemannianMetric torusModel Torus) (x : Torus)
    (z₁ ρ : ℝ) :
    (@Measure.prod Torus ℝ (borel Torus) _ (riemannianVolumeMeasure torusModel Torus gT) volume)
      {p : Torus × ℝ | 0 ≤ p.2 ∧
        (p.2 - z₁) ^ 2 + (riemannianEDistOf gT x p.1).toReal ^ 2 < ρ ^ 2} ≠ ⊤ := by
  have : IsFiniteMeasure (riemannianVolumeMeasure torusModel Torus gT) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := torusModel) (M := Torus) gT
  have hsub : {p : Torus × ℝ | 0 ≤ p.2 ∧
      (p.2 - z₁) ^ 2 + (riemannianEDistOf gT x p.1).toReal ^ 2 < ρ ^ 2} ⊆
      univ ×ˢ Icc (z₁ - |ρ|) (z₁ + |ρ|) := by
    rintro p ⟨-, hp⟩
    have h2 : (p.2 - z₁) ^ 2 < |ρ| ^ 2 := by
      rw [sq_abs]
      nlinarith [sq_nonneg (riemannianEDistOf gT x p.1).toReal]
    have := abs_lt_of_sq_lt_sq' h2 (abs_nonneg ρ)
    exact ⟨mem_univ _, by linarith [this.1], by linarith [this.2]⟩
  refine ne_top_of_le_ne_top ?_ (measure_mono hsub)
  rw [Measure.prod_prod, Real.volume_Icc]
  exact ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top

/-- At non-negative heights the cusp measure is at most the flat measure. -/
theorem cuspMeasure_le_flat (gT : SmoothRiemannianMetric torusModel Torus)
    {S : Set (Torus × ℝ)} (hS : MeasurableSet[borel (Torus × ℝ)] S) (hSd : ∀ p ∈ S, 0 ≤ p.2) :
    ((@Measure.prod Torus ℝ (borel Torus) _ (riemannianVolumeMeasure torusModel Torus gT)
        volume).withDensity fun p => ENNReal.ofReal (Real.exp (-p.2))) S ≤
      (@Measure.prod Torus ℝ (borel Torus) _ (riemannianVolumeMeasure torusModel Torus gT)
        volume) S := by
  rw [withDensity_apply _ (measurableSet_prod_of_borel hS), ← setLIntegral_one]
  refine setLIntegral_mono' (measurableSet_prod_of_borel hS) fun p hp => ?_
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hSd p hp)))

/-- At heights `≤ h` the cusp measure is at least `e^{-h}` times the flat measure. -/
theorem exp_mul_flat_le_cuspMeasure (gT : SmoothRiemannianMetric torusModel Torus)
    {S : Set (Torus × ℝ)} (hS : MeasurableSet[borel (Torus × ℝ)] S) {h : ℝ}
    (hSd : ∀ p ∈ S, p.2 ≤ h) :
    ENNReal.ofReal (Real.exp (-h)) *
        (@Measure.prod Torus ℝ (borel Torus) _ (riemannianVolumeMeasure torusModel Torus gT)
          volume) S ≤
      ((@Measure.prod Torus ℝ (borel Torus) _ (riemannianVolumeMeasure torusModel Torus gT)
        volume).withDensity fun p => ENNReal.ofReal (Real.exp (-p.2))) S := by
  rw [withDensity_apply _ (measurableSet_prod_of_borel hS), ← setLIntegral_const]
  refine setLIntegral_mono' (measurableSet_prod_of_borel hS) fun p hp => ?_
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg (hSd p hp)))

theorem rpow_three_halves_eq {x : ℝ} (hx : 0 < x) : x ^ ((3 : ℝ) / 2) = x * Real.sqrt x := by
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hx, Real.rpow_one,
    Real.sqrt_eq_rpow]

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}

/-- **Ball sandwich near the boundary (statement V.3, interface `V_ball_sandwich`).** A point `q`
within `b₀ = 1/100` of `∂W` is a collar point `e_i(x, z₁)`, `0 ≤ z₁ ≤ b₀/√(1-δ)`, and for
`0 < r ≤ b₀`: `λ₋³ F(r/λ₊) ≤ V_q(r) ≤ λ₊³ F(r/λ₋)`, `F(ρ) = μ₀(E_ρ)` the flat half-ellipsoid
volume, `λ₋ = √((1-δ) e^{-4/100})`, `λ₊ = √(1+δ)`. -/
theorem NearlyCuspidalBoundary.ball_sandwich (B : NearlyCuspidalBoundary W g K δ) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 / 1000) {q : W.Carrier}
    (hq : distanceToBoundary W g q ≤ ENNReal.ofReal (1 / 100)) :
    ∃ i, ∃ x : Torus, ∃ z₁ : ℝ, 0 ≤ z₁ ∧ z₁ ≤ (1 / 100) / Real.sqrt (1 - δ) ∧
      (B.collar i).toFun (x, halfSpaceOneLift z₁) = q ∧
      let F : ℝ → ℝ := fun r =>
        ((@Measure.prod Torus ℝ (borel Torus) _
          (riemannianVolumeMeasure torusModel Torus (B.collar i).cusp.torusMetric) volume)
          {p : Torus × ℝ | 0 ≤ p.2 ∧ (p.2 - z₁) ^ 2 +
            (riemannianEDistOf (B.collar i).cusp.torusMetric x p.1).toReal ^ 2 < r ^ 2}).toReal
      let lm : ℝ := Real.sqrt ((1 - δ) * Real.exp (-(4 / 100)))
      let lp : ℝ := Real.sqrt (1 + δ)
      ∀ r : ℝ, 0 < r → r ≤ 1 / 100 →
        lm ^ 3 * F (r / lp) ≤ (ballVolume g q r).toReal ∧
          (ballVolume g q r).toReal ≤ lp ^ 3 * F (r / lm) := by
  have hδ1 : δ < 1 := by linarith
  set m := Real.sqrt (1 - δ) with hm
  have hm2 : 1 / 2 ≤ m := Real.le_sqrt_of_sq_le (by nlinarith)
  have hmpos : 0 < m := by linarith
  have hb₀m : (1 / 100) / m ≤ 2 / 100 := by
    rw [div_le_iff₀ hmpos]
    nlinarith
  obtain ⟨i, x, z₁, hz₁0, hz₁, hxq⟩ :=
    B.exists_collar_coordinate hδ1 (by norm_num) (by rw [cuspDepth]; linarith) hq
  refine ⟨i, x, z₁, hz₁0, hz₁, hxq, ?_⟩
  intro F lm lp r hr hr1
  set e := B.collar i with he
  set gT := e.cusp.torusMetric with hgT
  set μ₀ := @Measure.prod Torus ℝ (borel Torus) _
    (riemannianVolumeMeasure torusModel Torus gT) volume with hμ₀
  set μH := μ₀.withDensity fun p => ENNReal.ofReal (Real.exp (-p.2)) with hμH
  set E : ℝ → Set (Torus × ℝ) := fun ρ => {p : Torus × ℝ | 0 ≤ p.2 ∧ (p.2 - z₁) ^ 2 +
    (riemannianEDistOf gT x p.1).toReal ^ 2 < ρ ^ 2} with hE
  set L : Torus × ℝ → CuspHalfSpace := fun p => (p.1, halfSpaceOneLift p.2) with hL
  have hz₁2 : z₁ ≤ 2 / 100 := hz₁.trans hb₀m
  set p₁ : CuspHalfSpace := (x, halfSpaceOneLift z₁) with hp₁
  have hp₁z : p₁.2.val 0 = z₁ := by
    change max z₁ 0 = z₁
    exact max_eq_left hz₁0
  have hp₁d : p₁ ∈ cuspDomain := by
    change p₁.2.val 0 < cuspDepth
    rw [hp₁z, cuspDepth]
    linarith
  -- the constants
  have hlp2 : lp ^ 2 = 1 + δ := Real.sq_sqrt (by linarith)
  have hlp1 : 1 ≤ lp := Real.le_sqrt_of_sq_le (by linarith)
  have hexp : Real.sqrt (Real.exp (-(4 / 100))) = Real.exp (-(4 / 100) / 2) :=
    (Real.exp_half _).symm
  have hlm : lm = m * Real.exp (-(4 / 100) / 2) := by
    change Real.sqrt ((1 - δ) * Real.exp (-(4 / 100))) = _
    rw [Real.sqrt_mul (by linarith), hexp]
  have hexp2 : 1 / 2 ≤ Real.exp (-(4 / 100) / 2) := by
    have := Real.add_one_le_exp (-(4 / 100) / 2)
    linarith
  have hlm4 : 1 / 4 ≤ lm := by
    rw [hlm]
    nlinarith
  have hlmpos : 0 < lm := by linarith
  have hlm_le_m : lm ≤ m := by
    rw [hlm]
    have : Real.exp (-(4 / 100) / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    nlinarith
  have hlm2 : lm ^ 2 = (1 - δ) * Real.exp (-(4 / 100)) :=
    Real.sq_sqrt (mul_nonneg (by linarith) (Real.exp_pos _).le)
  have hlm3 : lm ^ 3 ≤ (1 - δ) ^ ((3 : ℝ) / 2) * Real.exp (-(4 / 100)) := by
    rw [rpow_three_halves_eq (by linarith : (0 : ℝ) < 1 - δ), ← hm]
    have h3 : lm ^ 3 = lm ^ 2 * lm := by ring
    rw [h3, hlm2]
    have hpos : 0 ≤ (1 - δ) * Real.exp (-(4 / 100)) := mul_nonneg (by linarith) (Real.exp_pos _).le
    nlinarith [mul_le_mul_of_nonneg_left hlm_le_m hpos]
  have hlp3 : (1 + δ) ^ ((3 : ℝ) / 2) = lp ^ 3 := by
    rw [rpow_three_halves_eq (by linarith : (0 : ℝ) < 1 + δ)]
    change (1 + δ) * lp = lp ^ 3
    rw [← hlp2]
    ring
  -- heights in the half ellipsoids
  have hEheight : ∀ ρ, 0 ≤ ρ → ∀ p ∈ E ρ, p.2 < z₁ + ρ := by
    intro ρ hρ p hp
    have h2 : (p.2 - z₁) ^ 2 < ρ ^ 2 := by
      nlinarith [hp.2, sq_nonneg (riemannianEDistOf gT x p.1).toReal]
    linarith [(abs_lt_of_sq_lt_sq' h2 hρ).2]
  have hLz : ∀ p : Torus × ℝ, 0 ≤ p.2 → (L p).2.val 0 = p.2 := by
    intro p hp
    change max p.2 0 = p.2
    exact max_eq_left hp
  have hEm : ∀ ρ, MeasurableSet[borel (Torus × ℝ)] (E ρ) := fun ρ =>
    measurableSet_halfEllipsoid gT x z₁ ρ
  have hEd : ∀ ρ, 0 ≤ ρ → ρ ≤ 1 / 10 → ∀ p ∈ E ρ, 0 ≤ p.2 ∧ p.2 < cuspDepth := by
    intro ρ hρ hρ1 p hp
    refine ⟨hp.1, ?_⟩
    have := hEheight ρ hρ p hp
    rw [cuspDepth]
    linarith
  have hrlp0 : 0 ≤ r / lp := div_nonneg hr.le (by linarith)
  have hrlp : r / lp ≤ r := div_le_self hr.le hlp1
  have hrlm0 : 0 ≤ r / lm := div_nonneg hr.le hlmpos.le
  have hrlm : r / lm ≤ 4 / 100 := by
    rw [div_le_iff₀ hlmpos]
    nlinarith
  -- inner inclusion: `e(E_{r/λ₊}) ⊆ B(q, r)`
  have hin1 : e.toFun '' (L '' E (r / lp)) ⊆ riemannianBallOf g q r := by
    rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    have hLd : L p ∈ cuspDomain := by
      change (L p).2.val 0 < cuspDepth
      rw [hLz p hp.1]
      exact (hEd (r / lp) hrlp0 (by linarith) p hp).2
    have hQ : (p₁.2.val 0 - (L p).2.val 0) ^ 2 +
        (riemannianEDistOf e.cusp.torusMetric p₁.1 (L p).1).toReal ^ 2 <
          (r / Real.sqrt (1 + δ)) ^ 2 := by
      rw [hp₁z, hLz p hp.1]
      have h := hp.2
      have hsq : (z₁ - p.2) ^ 2 = (p.2 - z₁) ^ 2 := by ring
      rw [hsq]
      exact h
    have := e.image_subset_ball_flat (by linarith) hp₁d hr ⟨L p, ⟨hLd, hQ⟩, rfl⟩
    rw [← hxq]
    exact this
  -- outer inclusion: `B(q, r) ⊆ e(E_{r/λ₋})`
  have hin2 : riemannianBallOf g q r ⊆ e.toFun '' (L '' E (r / lm)) := by
    intro y hy
    have hy' : riemannianEDistOf g q y < ENNReal.ofReal r := hy
    have hd : riemannianEDistOf g (e.toFun p₁) y <
        ENNReal.ofReal (Real.sqrt (1 - δ) * (4 / 100 / 2)) := by
      rw [hxq]
      refine hy'.trans_le (ENNReal.ofReal_le_ofReal ?_)
      rw [← hm]
      nlinarith
    obtain ⟨p', hp'd, -, hp'y, hlow⟩ := e.exists_preimage_frozen_le_riemannianEDistOf
      (z₀ := 0) (a := 4 / 100) (by rw [cuspDepth]; norm_num)
      (by rw [hp₁z, sub_zero, abs_of_nonneg hz₁0]; linarith) hd
    rw [hxq] at hlow
    have hlow' := hlow.trans_lt hy'
    rw [ENNReal.ofReal_lt_ofReal_iff hr, neg_zero, Real.exp_zero, one_mul, hp₁z, ← hm,
      ← mul_assoc, ← hlm] at hlow'
    have hz'0 : 0 ≤ p'.2.val 0 := p'.2.2
    refine ⟨p', ⟨(p'.1, p'.2.val 0), ⟨hz'0, ?_⟩, ?_⟩, hp'y⟩
    · have hQ : Real.sqrt ((p'.2.val 0 - z₁) ^ 2 +
          (riemannianEDistOf gT x p'.1).toReal ^ 2) < r / lm := by
        rw [lt_div_iff₀ hlmpos, mul_comm]
        exact hlow'
      have hQ0 : 0 ≤ (p'.2.val 0 - z₁) ^ 2 + (riemannianEDistOf gT x p'.1).toReal ^ 2 := by
        positivity
      have := (Real.sqrt_lt' (by positivity)).mp hQ
      exact this
    · change (p'.1, halfSpaceOneLift (p'.2.val 0)) = p'
      rw [halfSpaceOneLift_val_zero_self]
  -- volumes
  have hfin : IsFiniteMeasure (riemannianVolumeMeasure W.model W.Carrier g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := W.model) (M := W.Carrier) g
  have hV : ballVolume g q r = riemannianVolumeMeasure W.model W.Carrier g
      (riemannianBallOf g q r) := rfl
  have hVtop : ballVolume g q r ≠ ⊤ := by rw [hV]; exact measure_ne_top _ _
  have hlow := (e.volume_transfer hδ0 hδ1 (hEm (r / lp))
    (hEd (r / lp) hrlp0 (by linarith))).1
  have hup := (e.volume_transfer hδ0 hδ1 (hEm (r / lm))
    (hEd (r / lm) hrlm0 (by linarith))).2
  have hHlow := exp_mul_flat_le_cuspMeasure gT (hEm (r / lp)) (h := 4 / 100) fun p hp => by
    have := hEheight (r / lp) hrlp0 p hp
    linarith
  have hHup := cuspMeasure_le_flat gT (hEm (r / lm)) fun p hp => hp.1
  have hFtop : ∀ ρ, μ₀ (E ρ) ≠ ⊤ := fun ρ => halfEllipsoid_measure_ne_top gT x z₁ ρ
  constructor
  · -- lower bound
    have hENN : ENNReal.ofReal (lm ^ 3) * μ₀ (E (r / lp)) ≤ ballVolume g q r := by
      calc ENNReal.ofReal (lm ^ 3) * μ₀ (E (r / lp))
          ≤ ENNReal.ofReal ((1 - δ) ^ ((3 : ℝ) / 2) * Real.exp (-(4 / 100))) *
            μ₀ (E (r / lp)) := by gcongr
        _ = ENNReal.ofReal ((1 - δ) ^ ((3 : ℝ) / 2)) *
            (ENNReal.ofReal (Real.exp (-(4 / 100))) * μ₀ (E (r / lp))) := by
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith) _), mul_assoc]
        _ ≤ ENNReal.ofReal ((1 - δ) ^ ((3 : ℝ) / 2)) * μH (E (r / lp)) := by gcongr
        _ ≤ riemannianVolumeMeasure W.model W.Carrier g (e.toFun '' (L '' E (r / lp))) := hlow
        _ ≤ ballVolume g q r := by rw [hV]; exact measure_mono hin1
    have := ENNReal.toReal_mono hVtop hENN
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
  · -- upper bound
    have hENN : ballVolume g q r ≤ ENNReal.ofReal (lp ^ 3) * μ₀ (E (r / lm)) := by
      calc ballVolume g q r
          ≤ riemannianVolumeMeasure W.model W.Carrier g (e.toFun '' (L '' E (r / lm))) := by
            rw [hV]; exact measure_mono hin2
        _ ≤ ENNReal.ofReal ((1 + δ) ^ ((3 : ℝ) / 2)) * μH (E (r / lm)) := hup
        _ ≤ ENNReal.ofReal (lp ^ 3) * μ₀ (E (r / lm)) := by rw [hlp3]; gcongr
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hFtop _)) hENN
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this

end DifferentialGeometry.Geometry.Collapse
