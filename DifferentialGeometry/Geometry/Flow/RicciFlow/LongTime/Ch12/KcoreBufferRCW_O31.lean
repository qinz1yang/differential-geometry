import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KcoreWitnessVolume_O31

/-!
# CH12-O31, group 4: buffered re-centred witness (`[FROZEN v2] CH12-O31 G4`, review R4 / D-R4-2)

`exists_buffered_rcw_O31`: along an escape sequence (`R(z n)/R(y n) → ∞`, `z n` eventually in every
normalized ball of radius `> ρ` about `y n`), eventually there is `w` with `R(w) = 2 R(y n)` at
normalized distance `< ρ − 19/50` from `y n`.  Hence for every `b ≤ 1/4` (in particular
`b_* = min {1/4, C₂^{-1/2}/2}`) the normalized ball `B'(w, b/√2)` lies in `B'(y n, r_*)`,
`r_* = ρ − 2^{-1/2}/4`: the buffer `d'(y n, w) + δ < r_* < ρ` of D-R4-2 (`δ = b/√λ`, `λ = 2`).
At `w` the non-round strong witness of G3 gives the centre volume.

No minimizing geodesic is used: a near-midpoint `x` (`d'(y,x) < ρ − 19/50`, `d'(x,z) < 2/5`) has
`R(x) ≥ 2 R(y)` — otherwise the canonical witness at `x` (or at a point `x'` with
`R(x') = 3/2 R(y)` between `x` and `z`, intermediate value theorem) would bound `R(z) < 2 C₂ R(y)` —
and the intermediate value theorem on `B(y, ρ − 19/50)` gives `w`.  The neck clause of `hStrong` is
the free predicate `NK` (instances: `[FROZEN] CH12-O23 hStrong`, `[FROZEN v2] CH12-O31 hStrong`).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian Set Filter
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

/-- `c / √Ry ≤ (√Rp)⁻¹` from `c² Rp ≤ Ry`. -/
theorem div_sqrt_le_inv_sqrt_O31 {c Ry Rp : ℝ} (hc : 0 < c) (hRy : 0 < Ry) (hRp : 0 < Rp)
    (h : c ^ 2 * Rp ≤ Ry) : c / Real.sqrt Ry ≤ (Real.sqrt Rp)⁻¹ := by
  have hsy : 0 < Real.sqrt Ry := Real.sqrt_pos.mpr hRy
  have hsp : 0 < Real.sqrt Rp := Real.sqrt_pos.mpr hRp
  have h1 := Real.sq_sqrt hRy.le
  have h2 := Real.sq_sqrt hRp.le
  have hcs : c * Real.sqrt Rp ≤ Real.sqrt Ry := by
    nlinarith [mul_pos hc hsp]
  rw [div_le_iff₀ hsy]
  calc c = (Real.sqrt Rp)⁻¹ * (c * Real.sqrt Rp) := by field_simp
    _ ≤ (Real.sqrt Rp)⁻¹ * Real.sqrt Ry := mul_le_mul_of_nonneg_left hcs (inv_nonneg.mpr hsp.le)

/-- **Buffered re-centred witness** (`[FROZEN v2] CH12-O31 G4`). -/
theorem exists_buffered_rcw_O31 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (NK : ∀ (s : RegularSlice F.observation) (x : s.stage.Carrier),
      (Hp.parameters.neckRadius s.time ^ 2)⁻¹ < metricScalarAt s.metric x →
      SpatialCanonicalWitness s.metric Hp.epsilon Hp.C1 Hp.C2 x → Prop)
    (hStrong : ∃ T : ℝ, ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ x : s.stage.Carrier,
      ∀ hR : (Hp.parameters.neckRadius s.time ^ 2)⁻¹ < metricScalarAt s.metric x,
      ∃ W : SpatialCanonicalWitness s.metric Hp.epsilon Hp.C1 Hp.C2 x,
        W.capTubeHasNeckChart Hp.epsilon ∧ NK s x hR W) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (s : ℕ → RegularSlice F.observation) (y z : ∀ n, (s n).stage.Carrier)
      (ρ : ℝ),
      Tendsto (fun n => (s n).time) atTop atTop →
      (∀ n, (Hp.parameters.neckRadius (s n).time ^ 2)⁻¹ ≤
        metricScalarAt (s n).metric (y n)) →
      Tendsto (fun n => metricScalarAt (s n).metric (y n)) atTop atTop →
      Tendsto (fun n => metricScalarAt (s n).metric (z n) /
        metricScalarAt (s n).metric (y n)) atTop atTop →
      (∀ r : ℝ, ρ < r → ∀ᶠ n in atTop, z n ∈ riemannianBallOf (s n).metric (y n)
        (r / Real.sqrt (metricScalarAt (s n).metric (y n)))) →
      ∀ᶠ n in atTop, ∃ w : (s n).stage.Carrier,
        w ∈ riemannianBallOf (s n).metric (y n)
          ((ρ - 19 / 50) / Real.sqrt (metricScalarAt (s n).metric (y n))) ∧
        (∀ b : ℝ, 0 ≤ b → b ≤ 1 / 4 →
          riemannianBallOf (s n).metric w
            ((b / Real.sqrt 2) / Real.sqrt (metricScalarAt (s n).metric (y n))) ⊆
          riemannianBallOf (s n).metric (y n)
            ((ρ - (Real.sqrt 2)⁻¹ / 4) / Real.sqrt (metricScalarAt (s n).metric (y n)))) ∧
        metricScalarAt (s n).metric w = 2 * metricScalarAt (s n).metric (y n) ∧
        ∃ hR : (Hp.parameters.neckRadius (s n).time ^ 2)⁻¹ < metricScalarAt (s n).metric w,
        ∃ W : SpatialCanonicalWitness (s n).metric Hp.epsilon Hp.C1 Hp.C2 w,
          W.capTubeHasNeckChart Hp.epsilon ∧ ¬ W.alternative.isWholeComponent ∧
          (∀ b : ℝ, 0 < b → b ≤ (Real.sqrt Hp.C2)⁻¹ →
            ENNReal.ofReal (κ * b ^ 3) ≤
              riemannianVolumeMeasure ThreeModel (s n).stage.Carrier
                (scaleMetric (metricScalarAt (s n).metric w) W.Q_pos (s n).metric)
                (riemannianBallOf (scaleMetric (metricScalarAt (s n).metric w) W.Q_pos
                  (s n).metric) w b)) ∧
          NK (s n) w hR W := by
  obtain ⟨T0, hT0⟩ := hStrong
  obtain ⟨κ, hκ, T, hT⟩ := strong_witness_nonround_volume_O31 Hp NK ⟨T0, hT0⟩
  refine ⟨κ, hκ, ?_⟩
  intro s y z ρ htime hneck hRy hratio hesc
  have hC2 : (1 : ℝ) ≤ Hp.C2 := Hp.C2_ge_one
  filter_upwards [hesc (ρ + 1 / 50) (by linarith),
    hratio.eventually (eventually_gt_atTop (2 * Hp.C2)),
    htime.eventually (eventually_ge_atTop (max T T0)), hRy.eventually (eventually_ge_atTop 1)]
    with n hz hc hTn hR1
  have hTn' : T ≤ (s n).time := le_trans (le_max_left _ _) hTn
  have hTn0 : T0 ≤ (s n).time := le_trans (le_max_right _ _) hTn
  set g' := (s n).metric with hg'
  set Ry : ℝ := metricScalarAt g' (y n) with hRydef
  have hRpos : 0 < Ry := lt_of_lt_of_le one_pos hR1
  have hsq : 0 < Real.sqrt Ry := Real.sqrt_pos.mpr hRpos
  have hzR : 2 * Hp.C2 * Ry < metricScalarAt g' (z n) := (lt_div_iff₀ hRpos).mp hc
  have hcont : Continuous (metricScalarAt g') := (metricScalar_smooth g').continuous
  have hthr : (Hp.parameters.neckRadius (s n).time ^ 2)⁻¹ ≤ Ry := hneck n
  -- a point with `Ry < R p < 2 Ry` cannot see `z` within its own canonical radius
  have hkey : ∀ p : (s n).stage.Carrier, Ry < metricScalarAt g' p →
      metricScalarAt g' p < 2 * Ry →
      riemannianEDistOf g' p (z n) < ENNReal.ofReal (Real.sqrt (metricScalarAt g' p))⁻¹ →
      False := by
    intro p hp1 hp2 hpz
    obtain ⟨W, -, -⟩ := hT0 (s n) hTn0 p (lt_of_le_of_lt hthr hp1)
    have hb := (W.scalar_bounds_of_mem_ball (z := z n) hpz).2
    change metricScalarAt g' (z n) ≤ Hp.C2 * metricScalarAt g' p at hb
    nlinarith
  -- no point below `2 Ry` within `2/5` of `z`
  have hshort : ∀ x : (s n).stage.Carrier, metricScalarAt g' x < 2 * Ry →
      riemannianEDistOf g' x (z n) < ENNReal.ofReal ((2 / 5) / Real.sqrt Ry) → False := by
    intro x hx2 hxz
    by_cases hx3 : 3 / 2 * Ry ≤ metricScalarAt g' x
    · have hxpos : 0 < metricScalarAt g' x := by linarith
      refine hkey x (by linarith) hx2 (lt_of_lt_of_le hxz (ENNReal.ofReal_le_ofReal ?_))
      exact div_sqrt_le_inv_sqrt_O31 (by norm_num) hRpos hxpos (by nlinarith)
    · rw [not_le] at hx3
      have hB := (isPathConnected_riemannianBallOf g' x
        (div_pos (by norm_num : (0 : ℝ) < 2 / 5) hsq)).isConnected.isPreconnected
      have hxB : x ∈ riemannianBallOf g' x ((2 / 5) / Real.sqrt Ry) := by
        change riemannianEDistOf g' x x < ENNReal.ofReal _
        rw [riemannianEDistOf_self]
        exact ENNReal.ofReal_pos.mpr (div_pos (by norm_num) hsq)
      have hmid : 3 / 2 * Ry ∈ Icc (metricScalarAt g' x) (metricScalarAt g' (z n)) :=
        ⟨hx3.le, by nlinarith⟩
      obtain ⟨x', hx'B, hx'⟩ := hB.intermediate_value hxB hxz hcont.continuousOn hmid
      have hx'pos : 0 < metricScalarAt g' x' := by rw [hx']; linarith
      refine hkey x' (by rw [hx']; linarith) (by rw [hx']; linarith) ?_
      have hx'x : riemannianEDistOf g' x' x < ENNReal.ofReal ((2 / 5) / Real.sqrt Ry) := by
        rw [riemannianEDistOf_comm]; exact hx'B
      calc riemannianEDistOf g' x' (z n)
          ≤ riemannianEDistOf g' x' x + riemannianEDistOf g' x (z n) :=
            riemannianEDistOf_triangle g' x' x (z n)
        _ < ENNReal.ofReal ((2 / 5) / Real.sqrt Ry) + ENNReal.ofReal ((2 / 5) / Real.sqrt Ry) :=
            ENNReal.add_lt_add hx'x hxz
        _ = ENNReal.ofReal ((4 / 5) / Real.sqrt Ry) := by
            rw [← ENNReal.ofReal_add (div_pos (by norm_num) hsq).le (div_pos (by norm_num) hsq).le]
            congr 1; ring
        _ ≤ ENNReal.ofReal (Real.sqrt (metricScalarAt g' x'))⁻¹ :=
            ENNReal.ofReal_le_ofReal
              (div_sqrt_le_inv_sqrt_O31 (by norm_num) hRpos hx'pos (by rw [hx']; nlinarith))
  -- the split point
  by_cases hρ' : 0 < ρ - 19 / 50
  swap
  · exfalso
    refine hshort (y n) (by linarith) (lt_of_lt_of_le hz (ENNReal.ofReal_le_ofReal ?_))
    exact div_le_div_of_nonneg_right (by linarith) hsq.le
  have hsplit : riemannianEDistOf g' (y n) (z n) <
      ENNReal.ofReal ((ρ - 19 / 50) / Real.sqrt Ry + (2 / 5) / Real.sqrt Ry) := by
    have : (ρ - 19 / 50) / Real.sqrt Ry + (2 / 5) / Real.sqrt Ry = (ρ + 1 / 50) / Real.sqrt Ry := by
      ring
    rw [this]; exact hz
  obtain ⟨x, hyx, hxz⟩ := exists_riemannianEDistOf_lt_of_lt_add g' (div_pos hρ' hsq)
    (div_pos (by norm_num) hsq) hsplit
  have hx2 : 2 * Ry ≤ metricScalarAt g' x := by
    by_contra hlt
    exact hshort x (lt_of_not_ge hlt) hxz
  have hB := (isPathConnected_riemannianBallOf g' (y n) (div_pos hρ' hsq)).isConnected.isPreconnected
  have hyB : y n ∈ riemannianBallOf g' (y n) ((ρ - 19 / 50) / Real.sqrt Ry) := by
    change riemannianEDistOf g' (y n) (y n) < ENNReal.ofReal _
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (div_pos hρ' hsq)
  have hmid : 2 * Ry ∈ Icc (metricScalarAt g' (y n)) (metricScalarAt g' x) :=
    ⟨by rw [← hRydef]; linarith, hx2⟩
  obtain ⟨w, hwB, hw⟩ := hB.intermediate_value hyB hyx hcont.continuousOn hmid
  have hq : (Hp.parameters.neckRadius (s n).time ^ 2)⁻¹ < metricScalarAt (s n).metric w := by
    change _ < metricScalarAt g' w
    rw [hw]; linarith
  have hwz : riemannianEDistOf g' w (z n) < ⊤ := by
    have h1 : riemannianEDistOf g' w (y n) < ⊤ := by
      rw [riemannianEDistOf_comm]; exact lt_trans hwB ENNReal.ofReal_lt_top
    have h2 : riemannianEDistOf g' (y n) (z n) < ⊤ := lt_trans hz ENNReal.ofReal_lt_top
    exact lt_of_le_of_lt (riemannianEDistOf_triangle g' w (y n) (z n))
      (ENNReal.add_lt_top.mpr ⟨h1, h2⟩)
  have hC2w : Hp.C2 * metricScalarAt (s n).metric w < metricScalarAt (s n).metric (z n) := by
    change Hp.C2 * metricScalarAt g' w < metricScalarAt g' (z n)
    rw [hw]; linarith
  have hbuf : ∀ b : ℝ, 0 ≤ b → b ≤ 1 / 4 →
      riemannianBallOf (s n).metric w ((b / Real.sqrt 2) / Real.sqrt Ry) ⊆
        riemannianBallOf (s n).metric (y n) ((ρ - (Real.sqrt 2)⁻¹ / 4) / Real.sqrt Ry) := by
    intro b hb0 hb1 q hqB
    have hs2 : (7 / 5 : ℝ) ≤ Real.sqrt 2 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    have hs2p : 0 < Real.sqrt 2 := by linarith
    have hinv : (Real.sqrt 2)⁻¹ ≤ 5 / 7 := by
      rw [inv_le_comm₀ hs2p (by norm_num)]; linarith
    have harith : (ρ - 19 / 50) + b / Real.sqrt 2 ≤ ρ - (Real.sqrt 2)⁻¹ / 4 := by
      rw [div_eq_mul_inv b]
      nlinarith [inv_nonneg.mpr hs2p.le]
    change riemannianEDistOf g' (y n) q < ENNReal.ofReal _
    have hwq : riemannianEDistOf g' w q < ENNReal.ofReal ((b / Real.sqrt 2) / Real.sqrt Ry) :=
      hqB
    calc riemannianEDistOf g' (y n) q
        ≤ riemannianEDistOf g' (y n) w + riemannianEDistOf g' w q :=
          riemannianEDistOf_triangle g' (y n) w q
      _ < ENNReal.ofReal ((ρ - 19 / 50) / Real.sqrt Ry) +
            ENNReal.ofReal ((b / Real.sqrt 2) / Real.sqrt Ry) := ENNReal.add_lt_add hwB hwq
      _ = ENNReal.ofReal ((ρ - 19 / 50) / Real.sqrt Ry + (b / Real.sqrt 2) / Real.sqrt Ry) :=
          (ENNReal.ofReal_add (div_pos hρ' hsq).le
            (div_nonneg (div_nonneg hb0 hs2p.le) hsq.le)).symm
      _ ≤ ENNReal.ofReal ((ρ - (Real.sqrt 2)⁻¹ / 4) / Real.sqrt Ry) := by
          apply ENNReal.ofReal_le_ofReal
          rw [← add_div]
          exact div_le_div_of_nonneg_right harith hsq.le
  exact ⟨w, hwB, hbuf, hw, hq, hT (s n) hTn' w hq (z n) hwz hC2w⟩

end GC.LongTime.Ch12
