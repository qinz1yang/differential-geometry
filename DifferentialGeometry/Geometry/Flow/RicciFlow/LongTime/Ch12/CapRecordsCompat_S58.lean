import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroSliceKernelThetaL_S44

/-!
# CH12-S58, group 1: `CompatibleUpgradedCapRecords_S58` (supply shape) and the cap-scale facts

`CompatibleUpgradedCapRecords_S58 Hp` is the independent frozen supply shape of D-R3-13 (NOT
`P5Linked`): every upgraded (large model radius) record on a slice history that has the profile's
parameters and a linked canonical window is the SAME physical cap as an old record `Hp.records n i`
(same event time) whose nominal scale is comparable (`nominal⁻² ≤ Ccmp * q`) to the upgraded cap scale.
`capScale_facts_S58` derives from it and from `Hp.recent_cutoff_smallness` the two scale facts the
ZC kernel needs, **before** any window is used: `neckRadius(s.time)⁻² ≤ ε² Ccmp q` and
`q ≥ (Ccmp ε² neckRadius(0)²)⁻¹`, and that the age window `≤ θ/q` keeps `s.time ≤ 2 t_j`.
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff NNReal

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}

/-- `[FROZEN] CH12-S58 CompatibleUpgradedCapRecords` (supply shape; lead-authorised def). -/
def CompatibleUpgradedCapRecords_S58 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) : Prop :=
  ∃ Ccmp : ℝ, 0 < Ccmp ∧ ∀ (s : RegularSlice F.observation) (p : CutoffParameters)
    (j : Fin (sliceHistoryR_O3 F s).eventCount)
    (R : GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory j p)
    (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex),
    p.delta = Hp.parameters.delta → p.neckRadius = Hp.parameters.neckRadius →
    p.fixed = Hp.parameters.fixed → p.recenterConstant = Hp.parameters.recenterConstant →
    linkedCanonicalWindow_O2 (R.static b) →
    ∃ (n : ℕ) (i : Fin (F.tower.history n).eventCount)
      (b' : ((F.tower.history n).toHistory.event i).RetainedBoundaryIndex),
      (F.tower.history n).time i.succ = (sliceHistoryR_O3 F s).time j.succ ∧
      ((Hp.records n i).nominalRadius ⟨b'.1.1⟩ ^ 2)⁻¹ ≤ Ccmp * (R.static b).neck.scale

theorem capScale_facts_S58 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (hcompat : CompatibleUpgradedCapRecords_S58 Hp) :
    ∃ Ccmp : ℝ, 0 < Ccmp ∧ ∀ ε : ℝ, 0 < ε → ∃ T : ℝ,
      ∀ (s : RegularSlice F.observation) (p : CutoffParameters)
        (j : Fin (sliceHistoryR_O3 F s).eventCount)
        (R : GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory j p)
        (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex),
        p.delta = Hp.parameters.delta → p.neckRadius = Hp.parameters.neckRadius →
        p.fixed = Hp.parameters.fixed → p.recenterConstant = Hp.parameters.recenterConstant →
        linkedCanonicalWindow_O2 (R.static b) → T ≤ s.time →
        ∀ θ : ℝ, 0 < θ → θ * Ccmp ≤ 1 →
        s.time - (sliceHistoryR_O3 F s).time j.succ ≤ θ * ((R.static b).neck.scale)⁻¹ →
        (sliceHistoryR_O3 F s).time j.succ ≤ s.time →
        (Hp.parameters.neckRadius s.time ^ 2)⁻¹ ≤ ε ^ 2 * Ccmp * (R.static b).neck.scale ∧
        (Ccmp * (ε ^ 2 * Hp.parameters.neckRadius 0 ^ 2))⁻¹ ≤ (R.static b).neck.scale := by
  obtain ⟨Ccmp, hC, hc⟩ := hcompat
  refine ⟨Ccmp, hC, fun ε hε => ?_⟩
  obtain ⟨T, -, hT⟩ := Hp.recent_cutoff_smallness ε hε
  refine ⟨T, fun s p j R b h1 h2 h3 h4 hl hTs θ hθ hθC hage hts => ?_⟩
  obtain ⟨n, i, b', htime, hnom⟩ := hc s p j R b h1 h2 h3 h4 hl
  have hq : 0 < (R.static b).neck.scale := (R.static b).neck.scale_pos
  set q := (R.static b).neck.scale with hqdef
  set N := (Hp.records n i).nominalRadius ⟨b'.1.1⟩ with hNdef
  have hN : 0 < N := (Hp.records n i).nominal_pos _
  have hNt : N ^ 2 ≤ (F.tower.history n).time i.succ := (Hp.records n i).nominal_time _
  have hN2 : 0 < N ^ 2 := by positivity
  set tj := (sliceHistoryR_O3 F s).time j.succ with htj
  have htj' : N ^ 2 ≤ tj := htime ▸ hNt
  have htj0 : 0 < tj := lt_of_lt_of_le hN2 htj'
  -- q ≥ 1 / (Ccmp tj)
  have hq1 : (N ^ 2)⁻¹ ≤ Ccmp * q := hnom
  have hq2 : tj⁻¹ ≤ (N ^ 2)⁻¹ := inv_anti₀ hN2 htj'
  have hq3 : 1 ≤ Ccmp * tj * q := by
    have h := hq2.trans hq1
    have h' : tj⁻¹ * tj ≤ Ccmp * q * tj := mul_le_mul_of_nonneg_right h htj0.le
    rw [inv_mul_cancel₀ htj0.ne'] at h'
    nlinarith
  have hqinv : q⁻¹ ≤ Ccmp * tj := by
    rw [inv_le_comm₀ hq (by positivity)]
    rw [inv_eq_one_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hage2 : s.time - tj ≤ tj := by
    have h1' : θ * q⁻¹ ≤ θ * (Ccmp * tj) := mul_le_mul_of_nonneg_left hqinv hθ.le
    have h2' : θ * (Ccmp * tj) ≤ tj := by
      have : θ * (Ccmp * tj) = (θ * Ccmp) * tj := by ring
      rw [this]
      nlinarith
    linarith
  have hmem : (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time :=
    htime ▸ ⟨by linarith, hts⟩
  have hNle : N ≤ ε * Hp.parameters.neckRadius s.time := hT s.time hTs n i hmem _
  have hr : 0 < Hp.parameters.neckRadius s.time :=
    Hp.parameters.neckRadius_pos _ s.positive.le
  have hr0 : 0 < Hp.parameters.neckRadius 0 := Hp.parameters.neckRadius_pos 0 le_rfl
  have hanti : Hp.parameters.neckRadius s.time ≤ Hp.parameters.neckRadius 0 :=
    Hp.radius_antitone (Set.mem_Ici.mpr (le_refl (0 : ℝ)))
      (Set.mem_Ici.mpr s.positive.le) s.positive.le
  have hNsq : N ^ 2 ≤ ε ^ 2 * Hp.parameters.neckRadius s.time ^ 2 := by
    have := pow_le_pow_left₀ hN.le hNle 2
    rwa [mul_pow] at this
  constructor
  · have h1' : (ε ^ 2 * Hp.parameters.neckRadius s.time ^ 2)⁻¹ ≤ (N ^ 2)⁻¹ :=
      inv_anti₀ hN2 hNsq
    have h2' : (Hp.parameters.neckRadius s.time ^ 2)⁻¹ =
        ε ^ 2 * (ε ^ 2 * Hp.parameters.neckRadius s.time ^ 2)⁻¹ := by
      field_simp
    rw [h2']
    have := mul_le_mul_of_nonneg_left (h1'.trans hq1) (sq_nonneg ε)
    linarith
  · have hNsq0 : N ^ 2 ≤ ε ^ 2 * Hp.parameters.neckRadius 0 ^ 2 := by
      have := pow_le_pow_left₀ hN.le (hNle.trans (mul_le_mul_of_nonneg_left hanti hε.le)) 2
      rwa [mul_pow] at this
    have h1' : (ε ^ 2 * Hp.parameters.neckRadius 0 ^ 2)⁻¹ ≤ (N ^ 2)⁻¹ :=
      inv_anti₀ hN2 hNsq0
    have h2' := h1'.trans hq1
    rw [mul_inv, inv_mul_le_iff₀ hC]
    exact h2'

end GC.LongTime.Ch12
