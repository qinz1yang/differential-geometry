import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitInterfaceProps
import DifferentialGeometry.Geometry.Comparison.Volume.AllCentreSeedVolume
import DifferentialGeometry.Geometry.Comparison.SectionalLowerBound

/-!
# CH12-O5 / LTF03, group S: fixed balls from the centre lemma

Blueprint LTF03 (`lem:hyp-macroscopic-seed-hyperbolic-balls`), last paragraph: once the centre
statement (C1) holds for *every* pair of seed constants and a curvature lower bound (C2) holds on
every fixed normalised ball about a seeded centre, Bishop–Gromov gives a seed of fixed constants
`(b, w)` at every `q ∈ B(p, L)`, and uniformity over the ball follows from C1 applied to a sequence
of worst points.

* `seed_transfer_O5` (S0): Bishop–Gromov seed transfer on a closed three-manifold, constants
  chosen before the manifold (via `FILL910.A13_all_centre_volume_of_seed`).
* `seedHyperbolicOnFixedBallsSeq_O5` (S1): `SeedHyperbolicOnFixedBallsSeq_S13` for all `S a v L`
  from the explicit inputs C1 (`hcenter`) and C2 (`hcurv`).
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.LongTime Set Filter
open scoped Manifold ContDiff ENNReal Topology
namespace GC.LongTime.Ch12
universe u

/-- **S0.** Bishop–Gromov seed transfer.  A seed `vol B(p,a) ≥ v a³` together with `sec ≥ -Λ` on
`B(p, 3 max(L,a))` gives, at every `q ∈ B(p, L)`, a seed of constants `(b, w)` depending only on
`(a, v, L, Λ)`: `sec ≥ -b⁻²` on `B(q, b)` and `vol B(q, b) ≥ w b³`. -/
theorem seed_transfer_O5 (a v L Λ : ℝ) (ha : 0 < a) (hv : 0 < v) (hL : 0 < L) (hΛ : 0 ≤ Λ) :
    ∃ b w : ℝ, 0 < b ∧ 0 < w ∧
      ∀ (X : Type u) [TopologicalSpace X] [ChartedSpace ThreeSpace X]
        [IsManifold ThreeModel ∞ X] [T2Space X] [CompactSpace X]
        (g : SmoothRiemannianMetric ThreeModel X) (p : X),
        ENNReal.ofReal (v * a ^ 3) ≤ ballVolume g p a →
        (∀ y ∈ riemannianBallOf g p (3 * max L a), SectionalBoundedBelowAt g y (-Λ)) →
        ∀ q ∈ riemannianBallOf g p L,
          (∀ y ∈ riemannianBallOf g q b, SectionalBoundedBelowAt g y (-(b ^ 2)⁻¹)) ∧
            ENNReal.ofReal (w * b ^ 3) ≤ ballVolume g q b := by
  set R := max L a with hRdef
  have hLR : L ≤ R := le_max_left _ _
  have haR : a ≤ R := le_max_right _ _
  have hR : 0 < R := ha.trans_le haR
  set b := min R (1 / (Λ + 1)) with hbdef
  have hΛ1 : 0 < Λ + 1 := by linarith
  have hb : 0 < b := lt_min hR (by positivity)
  have hbR : b ≤ R := min_le_left _ _
  have hbΛ : b ≤ 1 / (Λ + 1) := min_le_right _ _
  have hb1 : b ≤ 1 := hbΛ.trans (by rw [div_le_one hΛ1]; linarith)
  obtain ⟨κ, hκ, hall⟩ := FILL910.A13_all_centre_volume_of_seed.{u} ha hv hΛ haR hb hbR
  refine ⟨b, κ, hb, hκ, ?_⟩
  intro X _ _ _ _ _ g p hvol hsec q hq
  have hq' : riemannianEDistOf g p q < ENNReal.ofReal L := hq
  constructor
  · intro y hy
    have hy' : riemannianEDistOf g q y < ENNReal.ofReal b := hy
    have hmem : y ∈ riemannianBallOf g p (3 * R) := by
      change riemannianEDistOf g p y < ENNReal.ofReal (3 * R)
      calc riemannianEDistOf g p y ≤ riemannianEDistOf g p q + riemannianEDistOf g q y :=
            riemannianEDistOf_triangle g p q y
        _ < ENNReal.ofReal L + ENNReal.ofReal b :=
            ENNReal.add_lt_add hq' hy'
        _ = ENNReal.ofReal (L + b) := (ENNReal.ofReal_add hL.le hb.le).symm
        _ ≤ ENNReal.ofReal (3 * R) := ENNReal.ofReal_le_ofReal (by linarith)
    apply (hsec y hmem).mono
    have hb2 : b ^ 2 ≤ 1 / (Λ + 1) := by nlinarith
    have hb2pos : 0 < b ^ 2 := by positivity
    have : Λ + 1 ≤ (b ^ 2)⁻¹ := by
      rw [le_inv_comm₀ hΛ1 hb2pos, ← one_div]
      exact hb2
    linarith
  · have hqc : q ∈ riemannianClosedBallOf g p R := by
      change riemannianEDistOf g p q ≤ ENNReal.ofReal R
      exact hq'.le.trans (ENNReal.ofReal_le_ofReal hLR)
    exact hall X g p hvol hsec q hqc

/-- **S1 (LTF03).** `SeedHyperbolicOnFixedBallsSeq_S13` for every late point sequence and all
constants, from the explicit inputs
* C1 `hcenter` — the centre statement for every pair of seed constants (blueprint LTF03 ¶1:
  KL81.3 + local Shi + local flow compactness + parabolic LTF01), and
* C2 `hcurv` — a sectional lower bound on every fixed normalised ball about a seeded centre
  (blueprint LTF03 ¶2: KL84.1(b) + C1 at level points + Hamilton–Ivey). -/
theorem seedHyperbolicOnFixedBallsSeq_O5 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (H : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hneg : EventuallyNegativeScalar_S13 F)
    (hcenter : ∀ (S : LatePointSequence_S13 F) (a v : ℝ), 0 < a → 0 < v →
      (∀ j, HasNormalizedSeed_S13 (S.slices j) (S.point j) a v) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, NormalizedRicciDefect_S13 (S.slices j) (S.point j) < ε)
    (hcurv : ∀ a v L : ℝ, 0 < a → 0 < v → 0 < L → ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ S : LatePointSequence_S13 F,
        (∀ j, HasNormalizedSeed_S13 (S.slices j) (S.point j) a v) →
        ∀ᶠ j in atTop, ∀ y ∈ riemannianBallOf (S.slices j).normalizedMetric (S.point j) L,
          SectionalBoundedBelowAt (S.slices j).normalizedMetric y (-Λ)) :
    ∀ (S : LatePointSequence_S13 F) (a v L : ℝ),
      SeedHyperbolicOnFixedBallsSeq_S13 H hdec hneg S a v L := by
  intro S a v L ha hv hL hseed ε hε
  obtain ⟨Λ, hΛ, hc⟩ := hcurv a v (3 * max L a) ha hv (by positivity)
  obtain ⟨b, w, hb, hw, htr⟩ := seed_transfer_O5.{u} a v L Λ ha hv hL hΛ
  have hev := hc S hseed
  by_contra hfail
  rw [Filter.not_eventually] at hfail
  have hfr : ∃ᶠ j in atTop,
      (∀ y ∈ riemannianBallOf (S.slices j).normalizedMetric (S.point j) (3 * max L a),
          SectionalBoundedBelowAt (S.slices j).normalizedMetric y (-Λ)) ∧
        ∃ q ∈ riemannianBallOf (S.slices j).normalizedMetric (S.point j) L,
          ε ≤ NormalizedRicciDefect_S13 (S.slices j) q := by
    refine (hfail.and_eventually hev).mono fun j hj => ⟨hj.2, ?_⟩
    have h1 := hj.1
    push Not at h1
    exact h1
  obtain ⟨φ, hφ, hφj⟩ := Filter.extraction_of_frequently_atTop hfr
  choose q hqball hqdef using fun j => (hφj j).2
  let S' : LatePointSequence_S13 F :=
    { slices := fun j => S.slices (φ j)
      times_tendsto := S.times_tendsto.comp hφ.tendsto_atTop
      point := q }
  have hseed' : ∀ j, HasNormalizedSeed_S13 (S'.slices j) (S'.point j) b w := fun j =>
    htr _ (S.slices (φ j)).normalizedMetric (S.point (φ j)) (hseed (φ j)).2 (hφj j).1
      (q j) (hqball j)
  obtain ⟨j, hj⟩ := (hcenter S' b w hb hw hseed' ε hε).exists
  exact absurd hj (not_lt.mpr (hqdef j))

end GC.LongTime.Ch12
