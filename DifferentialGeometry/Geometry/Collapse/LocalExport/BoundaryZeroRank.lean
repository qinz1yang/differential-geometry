import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroLocal
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInteriorCut
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInteriorBudget

/-!
# LC88 / BCP04, packet P3c start: the zero stratum stays far from the boundary (BDRY-3)

Lemma L-Z of sheet-BDRY-2 §P3c (review 45 §2.3: the zero family has centres in `U₁ = {D > 10}`
without any `V·Λ` smallness). For an export packet `P` of the boundary collar (tolerance
`ε ≤ β₁²/1000`, threshold `w₀ ≤ β₁²/1000`) and a scale `ρ` with the collar smallness
`ρ ≤ β₁³/2000` on the collar heights `z ≤ 96`:
* `one_le_rank_of_distance_band_BDRY3`: every `x` with `10 < D(x) ≤ 85` has scaled splitting rank
  at least `1` (localisation E.4 at `b = 85` gives a collar point of height `< 92`; X121's small
  ball height band puts its packet height in `(5, 95)` and its collar height in `(6, 93)`; KL 16.4's
  adapted coordinate at `L = 0` splits it);
* `ofReal_eightyFive_lt_of_rank_eq_zero_BDRY3`: hence a rank-zero point with `D > 10` has `D > 85`;
* `ofReal_ten_lt_of_near_far_zero_BDRY3` (consumer, the centre margin): a point `v ∈ W°` whose
  `d_ĝ`-distance to a point `z` with `D(z) > 85` is below `V ρ(v)`, with BCP04.a at `v`
  (`ρ(v) < (D(v) + 3)/n`) and `13 V < 75 n`, has `D(v) > 10` (needs only `ĝ ≥ g°`).
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u


section Packet

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier}
  {K : ℕ} {A : ℝ → ℝ} {w₀ ε : ℝ}

/-- **The collar packet over PRESCRIBED premises.** The producer of
`BoundaryCollarPacket.nonempty_of_premises` keeps the given premises: some collar packet has
exactly them (in particular the given cusp structure). -/
theorem exists_boundaryCollarPacket_premises_eq_BDRY3 (P : BoundaryCollapsePremises W g K A w₀)
    (hK : 2 ≤ K) (hw : w₀ ≤ 1 / 6408) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ Q : BoundaryCollarPacket W g K A w₀ ε, Q.toBoundaryCollapsePremises = P := by
  have h := fun i => (P.cusp.collar i).exists_innerCollar_diffeomorph_torus_Icc
    (by omega) hε
  choose η F a har hη hF hZ hmid hchar hret using h
  refine ⟨{
    toBoundaryCollapsePremises := P
    threshold := hw
    tolerance_pos := hε
    tolerance_le_one := hε1
    height := η
    contMDiff_height := hη
    height_contract := hZ
    level := F
    levelBase := a
    levelBase_lt := har
    contMDiff_level := hF
    level_eq_height := hmid
    level_sublevel_eq := fun i => by
      ext y
      constructor
      · intro hy
        obtain ⟨p, hp, rfl, h⟩ := (hchar i y).mp hy
        exact ⟨p, ⟨hp, h⟩, rfl⟩
      · rintro ⟨p, ⟨hp, h⟩, rfl⟩
        exact (hchar i _).mpr ⟨p, hp, rfl, h⟩
    retained := hret
    buffer := ?_
    pinching := ?_ }, rfl⟩
  · intro i p x hp hx h9
    obtain ⟨q, hq, rfl, h6, h93⟩ := (P.cusp.collar i).exists_height_mem_of_edist_lt_one
      (by linarith) hp hx h9
    have h := abs_lt.mp (hZ i q hq (by linarith) (by linarith)).1
    exact ⟨q, hq, rfl, h6, h93, by linarith, by linarith⟩
  · intro i q hq u w
    exact (P.cusp.collar i).sectional_pinching hK (P.cusp.collar i).delta_nonneg hw hq u w

/-- **The export packet over a prescribed cusp structure** (connected carrier, `2 ≤ K`,
`w₀ ≤ 1/6408`, `0 < ε ≤ 1/1000`): some export packet has `P.cusp = B`. -/
theorem exists_boundaryExportPacket_cusp_eq_BDRY3 [ConnectedSpace W.Carrier]
    (B : NearlyCuspidalBoundary W g K w₀) (hv : boundaryVolumeCollapsed W g w₀)
    (hd : curvatureDerivativesControlled g K A w₀) (hK : 2 ≤ K) (hw : w₀ ≤ 1 / 6408)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 1000) :
    ∃ P : BoundaryExportPacket W g K A w₀ ε, P.cusp = B := by
  obtain ⟨Q, hQ⟩ := exists_boundaryCollarPacket_premises_eq_BDRY3 ⟨B, hv, hd⟩ hK hw hε
    (by linarith)
  refine ⟨BoundaryExportPacket.ofCollarPacket Q (by omega) hε1, ?_⟩
  change Q.toBoundaryCollapsePremises.cusp = B
  rw [hQ]

end Packet

section Kernel

variable {W : CompactCarrier.{u}} [ConnectedSpace W.Carrier]
  {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {A : ℝ → ℝ} {w₀ ε : ℝ}

/-- **L-Z (kernel).** For an export packet with tolerance and threshold below `β₁²/1000` and a scale
with the collar smallness `ρ ≤ β₁³/2000` on the collar heights `≤ 96`, every point at boundary
distance in `(10, 85]` has scaled splitting rank at least `1`. -/
theorem one_le_rank_of_distance_band_BDRY3 (P : BoundaryExportPacket W g K A w₀ ε)
    (ρ : W.Carrier → ℝ) (hρ : ∀ x, 0 < ρ x) (βs : ℕ → ℝ) (hβ : 0 < βs 1) (hβ1 : βs 1 < 1)
    (hδβ : w₀ ≤ βs 1 ^ 2 / 1000) (hεβ : ε ≤ βs 1 ^ 2 / 1000)
    (hsmall : ∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
      ρ ((P.cusp.collar i).toFun q) ≤ βs 1 ^ 3 / 2000)
    (x : W.Carrier) (h10 : ENNReal.ofReal 10 < distanceToBoundary W g x)
    (h85 : distanceToBoundary W g x ≤ ENNReal.ofReal 85) :
    1 ≤ @scaledSplittingRank.{u, 0} W.Carrier (inducedMetricSpace g) ρ hρ βs x := by
  have hw : w₀ ≤ 1 / 6408 := P.threshold
  have hw0 : 0 ≤ w₀ := (P.cusp.collar ⟨0, P.cusp.count_pos⟩).delta_nonneg
  have hs : 85 / 92 < Real.sqrt (1 - w₀) :=
    Real.lt_sqrt_of_sq_lt (by nlinarith)
  have hspos : 0 < Real.sqrt (1 - w₀) := by linarith
  have h92 : 85 / Real.sqrt (1 - w₀) < 92 := by
    rw [div_lt_iff₀ hspos]
    linarith
  obtain ⟨i, t, z₁, -, hz₁, hx⟩ := P.cusp.exists_collar_coordinate (by linarith)
    (by norm_num : (0 : ℝ) ≤ 85) (by unfold cuspDepth; linarith) h85
  have hp : (t, halfSpaceOneLift z₁).2.val 0 < 92 := by
    change (halfSpaceOneLift z₁).1 0 < 92
    rw [halfSpaceOneLift_val_zero]
    exact max_lt (by linarith) (by norm_num)
  have hmeet : (P.cusp.collar i).toFun (t, halfSpaceOneLift z₁) ∈
      riemannianBallOf g x (1 / 200) := by
    rw [hx]
    change riemannianEDistOf g x x < ENNReal.ofReal (1 / 200)
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (by norm_num)
  have hxx : x ∈ riemannianBallOf g x (1 / 200) := hx ▸ hmeet
  obtain ⟨q, -, hqy, hq6, hq93, hη5, hη95⟩ :=
    P.small_ball_height_band i (by norm_num) h10 hp hmeet x hxx
  have hrank := P.one_le_rank_of_small_scale i ρ hρ βs ((βs 1 + 1) / 2) 0 hβ (by linarith)
    (by linarith) le_rfl hδβ hεβ q (by linarith) (by linarith)
    (by simpa only [add_zero, mul_one] using hsmall i q (by linarith))
    (by simpa only [hqy] using hη5.le) (by simpa only [hqy] using hη95.le)
  rwa [hqy] at hrank

/-- **L-Z, contrapositive form.** Under the hypotheses of `one_le_rank_of_distance_band_BDRY3`, a
rank-zero point at boundary distance `> 10` is at boundary distance `> 85`. -/
theorem ofReal_eightyFive_lt_of_rank_eq_zero_BDRY3 (P : BoundaryExportPacket W g K A w₀ ε)
    (ρ : W.Carrier → ℝ) (hρ : ∀ x, 0 < ρ x) (βs : ℕ → ℝ) (hβ : 0 < βs 1) (hβ1 : βs 1 < 1)
    (hδβ : w₀ ≤ βs 1 ^ 2 / 1000) (hεβ : ε ≤ βs 1 ^ 2 / 1000)
    (hsmall : ∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
      ρ ((P.cusp.collar i).toFun q) ≤ βs 1 ^ 3 / 2000)
    (x : W.Carrier) (h10 : ENNReal.ofReal 10 < distanceToBoundary W g x)
    (h0 : @scaledSplittingRank.{u, 0} W.Carrier (inducedMetricSpace g) ρ hρ βs x = 0) :
    ENNReal.ofReal 85 < distanceToBoundary W g x := by
  by_contra h85
  have h := one_le_rank_of_distance_band_BDRY3 P ρ hρ βs hβ hβ1 hδβ hεβ hsmall x h10
    (not_lt.mp h85)
  omega

end Kernel

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1

/-- **The centre margin (consumer).** For `ĝ ≥ g°` on `W°`, a point `v ∈ W°` within `d_ĝ`-distance
`V ρ(v)` of a point `z` with `D(z) > 85`, with BCP04.a at `v` and `13 V < 75 n`, lies in
`U₁ = {D > 10}`. -/
theorem ofReal_ten_lt_of_near_far_zero_BDRY3 (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
    (g : SmoothRiemannianMetric W.model W.Carrier)
    (ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤))
    (hle : ∀ (x : W.pieceInterior ⊤) (v : TangentSpace (𝓡 3) x),
      (pieceInteriorMetric W g ⊤).inner x v v ≤ ĝ.inner x v v)
    (v z : W.pieceInterior ⊤) {ρv V n : ℝ} (hρv : 0 < ρv) (hV : 0 ≤ V) (hVn : 13 * V < 75 * n)
    (hbcp : n * (distanceToBoundary W g v).toReal / ((distanceToBoundary W g v).toReal + 3) <
      (distanceToBoundary W g v).toReal / ρv)
    (hz : ENNReal.ofReal 85 < distanceToBoundary W g z)
    (hvz : riemannianEDistOf ĝ v z < ENNReal.ofReal (V * ρv)) :
    ENNReal.ofReal 10 < distanceToBoundary W g v := by
  by_contra h10
  have hD10 : distanceToBoundary W g v ≤ ENNReal.ofReal 10 := not_lt.mp h10
  have htop : distanceToBoundary W g v ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hD10
  set d := (distanceToBoundary W g v).toReal with hd
  have hd0 : 0 ≤ d := ENNReal.toReal_nonneg
  have hd10 : d ≤ 10 := by
    rw [hd, ← ENNReal.ofReal_le_ofReal_iff (by norm_num), ENNReal.ofReal_toReal htop]
    exact hD10
  have hdpos : 0 < d := by
    by_contra hd0'
    have hd00 : d = 0 := le_antisymm (not_lt.mp hd0') hd0
    rw [hd00] at hbcp
    simp at hbcp
  -- BCP04.a at `v`: `n ρ(v) < d + 3 ≤ 13`
  have hnρ : n * ρv < d + 3 := by
    rw [div_lt_div_iff₀ (by linarith) hρv] at hbcp
    nlinarith
  have hVρ : V * ρv < 75 := by
    have h13 : n * ρv < 13 := by linarith
    by_cases hV0 : V = 0
    · rw [hV0, zero_mul]; norm_num
    have hVpos : 0 < V := lt_of_le_of_ne hV (Ne.symm hV0)
    have hn : 0 < n := by nlinarith
    nlinarith
  have : Nonempty (W.pieceInterior ⊤) := ⟨v⟩
  have hdist := (riemannianEDistOf_val_le_completion_BDRY1 W g ĝ hle v z).trans_lt hvz
  have htri := distanceToBoundary_le_add W g z.val v.val
  rw [riemannianEDistOf_comm] at htri
  have hlt : distanceToBoundary W g z < ENNReal.ofReal 85 := by
    calc distanceToBoundary W g z ≤ distanceToBoundary W g v + riemannianEDistOf g v.val z.val :=
          htri
      _ < ENNReal.ofReal 10 + ENNReal.ofReal 75 := by
          exact ENNReal.add_lt_add_of_le_of_lt htop hD10
            (hdist.trans_le (ENNReal.ofReal_le_ofReal hVρ.le))
      _ = ENNReal.ofReal 85 := by
          rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
          norm_num
  exact (lt_asymm hz hlt).elim

end DifferentialGeometry.Geometry.Collapse
