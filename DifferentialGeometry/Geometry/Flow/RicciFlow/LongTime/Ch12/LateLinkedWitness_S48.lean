import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EnhancedProfileCapJets

/-!
# CH12-S48, group 1: the late linked witness at a FIXED radius `Dbig` (step (a) of `hZC` v2)

For every cap `(R.static b)` of any cutoff record on any `RetainedCoreHistory` whose parameters have
the profile's `delta`, `recenterConstant`, `fixed`, whose model radius is `≥ Dbig` and whose static
cap is `linkedCanonicalWindow_O2`, and which is late (`T < H.time i.succ`, with `T` depending only on
`(Hp, Dbig, m, ζ)`), there is a canonical static insertion witness of order `m`, accuracy `ζ` at
radius `Dbig` (NOT at the record's radius), whose window metric is the scaled pull-back of the initial
metric along `(R.static b).window ∘ inclusion`.  This is the input `w`, `hmetric` of the cap-window
kernel `PreparedCapWindowGeometry.lean:943` with `Dbig := Dbig` and `Jbig := window ∘ inclusion`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.CheegerGromovCompactness
open Set
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch12

universe u

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

theorem late_linked_witness_S48 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hP3 : P3_O2 Hp) (Dbig : ℝ) (hDbig : 0 < Dbig) (m : ℕ) (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ T : ℝ, ∀ (H : RetainedCoreHistory.{u}) (i : Fin H.eventCount) (p : CutoffParameters)
      (R : GeometricCutoffRecord H.toHistory i p)
      (b : (H.toHistory.event i).RetainedBoundaryIndex),
      p.delta = Hp.parameters.delta → p.recenterConstant = Hp.parameters.recenterConstant →
      p.fixed = Hp.parameters.fixed → ∀ hD : Dbig ≤ p.modelRadius,
      linkedCanonicalWindow_O2 (R.static b) → T < H.time i.succ →
      ∃ (x₀ : (H.toHistory.event i).incoming.terminalRegularOpen) (δ' : ℝ)
        (d : normalizedDatum (H.toHistory.event i).terminal.metric x₀ δ' (m + 4))
        (w : DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness d
          p.fixed.collarLength p.fixed.collar_pos Dbig m ζ),
        metricScalarAt (H.toHistory.event i).terminal.metric x₀ = (R.static b).neck.scale ∧
        let Jbig : standardCapWindow Dbig → (H.toHistory.stage i.succ).Carrier :=
          (R.static b).window ∘ TopologicalSpace.Opens.inclusion
            (show standardCapWindow Dbig ≤ standardCapWindow p.modelRadius from by
              intro x hx
              change ‖x‖ < p.modelRadius + 1
              change ‖x‖ < Dbig + 1 at hx
              linarith only [hx, hD]);
        ∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
          (R.static b).neck.scale * (H.initialMetric i.succ).inner (Jbig x)
            (mfderiv ThreeModel ThreeModel Jbig x v) (mfderiv ThreeModel ThreeModel Jbig x z) := by
  obtain ⟨δ₀, hδ₀, hwit⟩ := hP3.1 Dbig hDbig m ζ hζ
  set c := Hp.parameters.recenterConstant with hcdef
  have hc4 : 4 ≤ c := Hp.parameters.recenterConstant_ge_four
  have hcpos : 0 < c := by linarith
  set η : ℝ := min δ₀ (1 / ((m : ℝ) + 4)) with hη
  have hηpos : 0 < η := lt_min hδ₀ (by positivity)
  obtain ⟨B, hB⟩ := hdec (η / c) (div_pos hηpos hcpos)
  refine ⟨B, fun H i p R b hδ hcp hf hD hlink ht => ?_⟩
  obtain ⟨x₀, δ', k, d, w₁, h1, h2, -, hδS, hk⟩ := hlink
  have hrec := R.recenter_delta b
  have hle := R.delta_le b.1.1
  rw [hδ, Hp.accuracy_eq] at hle
  rw [hcp] at hrec
  have hlt : R.delta b.1.1 < η / c := hle.trans_lt (hB _ ht)
  have hS : (R.static b).delta < η := by
    rw [hrec]
    have := mul_lt_mul_of_pos_left hlt hcpos
    rwa [mul_div_cancel₀ _ hcpos.ne'] at this
  have hδ'η : δ' < η := hδS.trans_lt hS
  have hpos : 0 < δ' := d.precision_pos
  have hlt' : δ' < 1 / ((m : ℝ) + 4) := hδ'η.trans_le (min_le_right _ _)
  have hinv : (m : ℝ) + 4 < δ'⁻¹ := by
    have h1 : (m : ℝ) + 4 = (1 / ((m : ℝ) + 4))⁻¹ := by field_simp
    rw [h1]
    exact (inv_lt_inv₀ (by positivity) hpos).mpr hlt'
  have hfloor : m + 4 ≤ ⌊δ'⁻¹⌋₊ := by
    apply Nat.le_floor
    push_cast
    exact hinv.le
  have hk' : m + 4 ≤ k := by omega
  have hδ'le : δ' ≤ δ₀ := (hδ'η.trans_le (min_le_left _ _)).le
  obtain ⟨w'⟩ := hwit δ' hpos hδ'le _ x₀ (d.lowerOrder hk')
  have hw'' : Nonempty (DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness
      (d.lowerOrder hk') p.fixed.collarLength p.fixed.collar_pos Dbig m ζ) := by
    rw [hf]; exact ⟨w'⟩
  obtain ⟨w''⟩ := hw''
  refine ⟨x₀, δ', d.lowerOrder hk', w'', h1, ?_⟩
  intro Jbig x v z
  have hsub : standardCapWindow Dbig ≤ standardCapWindow p.modelRadius := by
    intro x hx
    change ‖x‖ < p.modelRadius + 1
    change ‖x‖ < Dbig + 1 at hx
    linarith only [hx, hD]
  have hinc : MDifferentiableAt ThreeModel ThreeModel
      (TopologicalSpace.Opens.inclusion hsub) x :=
    ((contMDiff_inclusion hsub).contMDiffAt).mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hwin : MDifferentiableAt ThreeModel ThreeModel (R.static b).window
      (TopologicalSpace.Opens.inclusion hsub x) :=
    ((R.static b).window_smooth.contMDiff.contMDiffAt).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hcomp : mfderiv ThreeModel ThreeModel Jbig x =
      (mfderiv ThreeModel ThreeModel (R.static b).window
        (TopologicalSpace.Opens.inclusion hsub x)).comp
        (mfderiv ThreeModel ThreeModel (TopologicalSpace.Opens.inclusion hsub) x) :=
    mfderiv_comp x hwin hinc
  have hid := mfderiv_opens_incl (I := ThreeModel) hsub x
  have hw2 := windowMetric_inner_eq_of_lowerOrder_O2 d hk' w'' (w₁.restrictWindow hDbig hD) x v z
  rw [hw2, DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.restrictWindow_windowMetric]
  have h2x := h2 (TopologicalSpace.Opens.inclusion hsub x) v z
  have hout := H.event_output i
  change ((w₁.windowMetric.restrictOpenOfSubset hsub).inner x) v z = _
  change w₁.windowMetric.inner (TopologicalSpace.Opens.inclusion hsub x) v z = _
  rw [h2x, hcomp, hid, hout]
  rfl

end GC.LongTime.Ch12
