import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EnhancedProfileHypotheses
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PreparedCapWindowGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWitnessCoherence

/-!
# CH12-O2, group 3 (W5 / M04): all-order jets near newly inserted caps

CH12-O1 showed that with the current profile the outgoing cap window has order
`parameters.modelOrder` (an arbitrary natural number) and that the canonical-window datum
`(δ', k)` is a bare existential, so no all-K (and no K = 20) jet bound near a new cap follows.

Here, under P1 (link) + P3 (collar length / window radius) + `hdec`:

* `late_cap_window_witness_O2`: for every order `m` and accuracy `ζ > 0`, after some time every
  late cutoff record's cap window carries a `CanonicalStaticInsertionWitness` of order `m`,
  accuracy `ζ`, with the fixed collar length and the record's window radius, **whose window metric
  is the record window's pulled-back output metric** (the witness is rebuilt from the linked datum
  at lower order; `coherent_of_lowerOrder` identifies the two windows).
* `late_cap_window_jets_O2`: feeding these witnesses to the cap-window flow kernel
  `ObservedHistory.exists_uniform_prepared_incoming_cap_window_flow_with_uniform_curvature_derivative_bounds`
  (`Surgery/Topology/PreparedCapWindowGeometry.lean:668`, which accepts an arbitrary witness)
  gives, for every `N`, scale-invariant jets of order `≤ N` on the flowed cap window of every late
  cap, with constants independent of the history index, event and boundary.  The records-precision
  premise of the kernel is discharged by `hdec`; the event-slab time-derivative premise by P2.
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

/-- Two canonical static insertion witnesses built on (lower orders of) the same datum with the
same collar length and window radius have the same window metric. -/
theorem windowMetric_inner_eq_of_lowerOrder_O2 {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M]
    {h : SmoothRiemannianMetric ThreeModel M} {x₀ : M} {δ' : ℝ} {k j : ℕ}
    (d : normalizedDatum h x₀ δ' k) (hj : j ≤ k) {A : ℝ} {hA : 0 < A} {D : ℝ}
    {m₀ m₁ : ℕ} {ε₀ ε₁ : ℝ}
    (w₀ : DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness
      (d.lowerOrder hj) A hA D m₀ ε₀)
    (w₁ : DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness
      d A hA D m₁ ε₁)
    (x : standardCapWindow D) (v z : TangentSpace ThreeModel x) :
    w₀.windowMetric.inner x v z = w₁.windowMetric.inner x v z := by
  have hcoh :=
    DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.coherent_of_lowerOrder
      d hj (le_refl k) w₀ w₁
  obtain ⟨-, -, -, -, -, hout, -, -, -, -, -, hmap₀, hmap₁⟩ := hcoh
  have hwin : w₀.window = w₁.window := by
    ext x
    change w₀.data.windowMap x = w₁.data.windowMap x
    rw [hmap₀ x, hmap₁ x]
  rw [w₀.window_inner, w₁.window_inner, hwin, hout]

/-- **W5 static step.**  Under P1 + P3 + `hdec`: for every order `m` and accuracy `ζ`, every late
cap window carries an order-`m`, accuracy-`ζ` canonical witness with the record's window metric. -/
theorem late_cap_window_witness_O2 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hP1 : P1_O2 Hp) (hP3 : P3_O2 Hp) (m : ℕ) (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ T : ℝ, ∀ n (i : Fin (F.tower.history n).eventCount)
      (b : ((F.tower.history n).toHistory.event i).RetainedBoundaryIndex),
      T < (F.tower.history n).time i.succ →
      ∃ (x₀ : ((F.tower.history n).toHistory.event i).incoming.terminalRegularOpen) (δ' : ℝ)
        (d : normalizedDatum ((F.tower.history n).toHistory.event i).terminal.metric
          x₀ δ' (m + 4))
        (w : DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness d
          Hp.parameters.fixed.collarLength Hp.parameters.fixed.collar_pos
          Hp.parameters.modelRadius m ζ),
        metricScalarAt ((F.tower.history n).toHistory.event i).terminal.metric x₀ =
            ((Hp.records n i).static b).neck.scale ∧
        (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
          ((Hp.records n i).static b).neck.scale *
            ((F.tower.history n).initialMetric i.succ).inner
              (((Hp.records n i).static b).window x)
              (mfderiv ThreeModel ThreeModel ((Hp.records n i).static b).window x v)
              (mfderiv ThreeModel ThreeModel ((Hp.records n i).static b).window x z)) ∧
        (∀ z : ThreeBall, ∃ x : standardCapWindow Hp.parameters.modelRadius,
          ‖x.val‖ ≤ DifferentialGeometry.PDE.RicciFlow.StandardCap.transitionEnd ∧
          ((Hp.records n i).static b).window x =
            ((Hp.records n i).static b).inclusion (((Hp.records n i).static b).witness.cap z)) := by
  obtain ⟨δ₀, hδ₀, hwit⟩ := hP3.1 Hp.parameters.modelRadius Hp.parameters.modelRadius_pos m ζ hζ
  obtain ⟨T, hT⟩ := late_window_datum_O2 Hp hdec hP1 (m + 4) δ₀ hδ₀
  refine ⟨T, fun n i b ht => ?_⟩
  obtain ⟨x₀, δ', k, d, w, h1, h2, h3, hδ', hk⟩ := hT n i b ht
  obtain ⟨w'⟩ := hwit δ' d.precision_pos hδ' _ x₀ (d.lowerOrder hk)
  refine ⟨x₀, δ', d.lowerOrder hk, w', h1, fun x v z => ?_, h3⟩
  rw [windowMetric_inner_eq_of_lowerOrder_O2 d hk w' w x v z, h2 x v z,
    ← (F.tower.history n).event_output i]

/-- The `r` of the cap-window kernel used here (`transitionEnd + eps⁻¹ + 1 < r` at `eps = 1/1000`). -/
def capCoreRadius_O2 : ℝ := DifferentialGeometry.PDE.RicciFlow.StandardCap.transitionEnd + 1002

/-- **W5 output** (statement shape of `late_cap_window_jets_O2`, used as an argument of the
micro-regime glue). -/
def capWindowJets_O2 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) (N : ℕ) : Prop :=
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ B : ℝ, 1 ≤ B ∧ ∀ Ctime : ℝ≥0, P2_O2 Hp Ctime →
    ∃ η : ℝ, 0 < η ∧ ∃ T : ℝ,
      ∀ n (i : Fin (F.tower.history n).eventCount)
        (b : ((F.tower.history n).toHistory.event i).RetainedBoundaryIndex),
      T < (F.tower.history n).time i.succ →
      ∀ (last : Fin ((F.tower.history n).eventCount + 1)) (hle : i.succ ≤ last) (s : ℝ)
        (G : ((F.tower.history n).toHistory.stage last).IncomingSlab
          ((F.tower.history n).toHistory.time last) s)
        (L : G.TerminalLimitMetric),
      G.flow.base.metric ((F.tower.history n).toHistory.time last) =
        (F.tower.history n).toHistory.initialMetric last →
      ∀ (q₀ a₀ : ℝ), 0 < q₀ → q₀ ≤ C₀ * ((Hp.records n i).static b).neck.scale →
        1 ≤ a₀ * ((Hp.records n i).static b).neck.scale →
      (∀ x, InFixedHamiltonIveyRegion ((F.tower.history n).toHistory.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt ((F.tower.history n).toHistory.initialMetric 0) x) →
      (Hp.parameters.neckRadius ((F.tower.history n).toHistory.time last) ^ 2)⁻¹ ≤ q₀ →
      (∀ x : ((F.tower.history n).toHistory.stage last).Carrier,
        ∀ t ∈ Ioo ((F.tower.history n).toHistory.time last) s,
        q₀ < G.flow.scalar t x →
        |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ Ctime * G.flow.scalar t x ^ 2) →
      ((Hp.records n i).static b).neck.scale *
          (s - (F.tower.history n).toHistory.time i.succ) ≤ η →
      ∀ (z : standardCapWindow capWindowRadius_O2) (x : G.terminalRegularOpen)
        (A : BackwardPointTrace (F.tower.history n).toHistory i.succ last hle x.val),
        (∀ z' : standardCapWindow Hp.parameters.modelRadius, z'.val = z.val →
          A.point i.succ le_rfl hle = ((Hp.records n i).static b).window z') →
      ∃ Ξ : standardCapWindow capWindowRadius_O2 →
          (F.tower.history n).toHistory.backwardSurvivorIncomingDomain i.succ last hle G,
        (∀ (y : standardCapWindow capWindowRadius_O2)
            (y' : standardCapWindow Hp.parameters.modelRadius), y'.val = y.val →
          (F.tower.history n).toHistory.backwardSurvivorMap i.succ last hle i.succ le_rfl hle
            (Ξ y).val = ((Hp.records n i).static b).window y') ∧
        (F.tower.history n).toHistory.backwardSurvivorIncomingMap i.succ last hle G (Ξ z) = x ∧
        ∀ j ≤ N, ∀ y : standardCapWindow capWindowRadius_O2, ‖y.val‖ ≤ capCoreRadius_O2 →
          curvDerivNormSq j L.metric
              ((F.tower.history n).toHistory.backwardSurvivorIncomingMap i.succ last hle G (Ξ y)) ≤
            ((Hp.records n i).static b).neck.scale ^ (j + 2) * B

/-- **W5 / M04 (cap-window jets, all orders).**  Under P1 + P3 + `hdec`, for every order `N`
there are `C₀, B` (independent of the history, event and boundary) such that for every P2
constant `Ctime` there are `η, T`: for every late cutoff record cap window, every backward slab
continuation of length `≤ η / q` after it, and every point reached by a backward trace from the
window, the flowed window carries jets `|∇^j Rm|² ≤ q^(j+2) B` for all `j ≤ N` on the cap core
(`q` = the static neck scale).  The kernel's records-precision premise is discharged by `hdec`
and its event-slab time-derivative premise by P2 (given `neckRadius(t_last)⁻² ≤ q₀`). -/
theorem late_cap_window_jets_O2 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hP1 : P1_O2 Hp) (hP3 : P3_O2 Hp) (N : ℕ) :
    capWindowJets_O2 Hp N := by
  unfold capWindowJets_O2
  have hte := DifferentialGeometry.PDE.RicciFlow.StandardCap.transitionEnd_pos
  obtain ⟨C₀, hC₀, -, B, hB, hker⟩ :=
    ObservedHistory.exists_uniform_prepared_incoming_cap_window_flow_with_uniform_curvature_derivative_bounds.{u, 0, 0, u}
      N capWindowRadius_O2 capCoreRadius_O2 (1 / 1000) (by norm_num) (by norm_num)
      (by unfold capCoreRadius_O2; rw [show ((1 : ℝ) / 1000)⁻¹ = 1000 by norm_num]; linarith)
      (by unfold capWindowRadius_O2 capCoreRadius_O2; norm_num)
  refine ⟨C₀, hC₀, B, hB, fun Ctime hP2 => ?_⟩
  obtain ⟨η, ε₀, δ₀, hη, hε₀, -, hδ₀, hjet⟩ := hker Ctime
  -- witnesses of the required order and accuracy on late windows
  set mN : ℕ := max ⌈(1 / 1000 : ℝ)⁻¹⌉₊ N + 2 with hmN
  obtain ⟨T₁, hT₁⟩ := late_cap_window_witness_O2 Hp hdec hP1 hP3 mN ε₀ hε₀
  -- records precision
  obtain ⟨T₂, hT₂⟩ := hdec δ₀ hδ₀
  refine ⟨η, hη, max T₁ T₂, ?_⟩
  intro n i b hT last hle s G L hG q₀ a₀ hq₀ hq₀C ha₀ hHI hscal hrq hfinal hη' z x A hA
  set H := (F.tower.history n).toHistory with hH
  set S := (Hp.records n i).static b with hS
  obtain ⟨x₀, δ', d, w, -, hmetric, -⟩ := hT₁ n i b ((le_max_left _ _).trans_lt hT)
  have hmargin : capWindowRadius_O2 + 1 ≤ Hp.parameters.modelRadius := hP3.2
  have hq : 0 < S.neck.scale := S.neck.scale_pos
  have hsub : standardCapWindow capWindowRadius_O2 ≤ standardCapWindow Hp.parameters.modelRadius := by
    intro y hy
    change ‖y‖ < Hp.parameters.modelRadius + 1
    change ‖y‖ < capWindowRadius_O2 + 1 at hy
    linarith only [hy, hmargin]
  -- the records-precision premise
  have hrec : ∀ j : Fin H.eventCount, i.succ ≤ j.castSucc → j.succ ≤ last →
      ∀ b', (Hp.records n j).delta b' ≤ δ₀ := by
    intro j hj _ b'
    have hle' := (Hp.records n j).delta_le b'
    rw [Hp.accuracy_eq] at hle'
    have htj : (F.tower.history n).time i.succ < (F.tower.history n).time j.succ :=
      (F.tower.history n).time_strictMono (lt_of_le_of_lt hj Fin.castSucc_lt_succ)
    exact (hle'.trans (hT₂ _ (((le_max_right _ _).trans_lt hT).trans htj)).le)
  -- the event-slab derivative premise, from P2
  have hslab : ∀ j : Fin H.eventCount, i.succ ≤ j.castSucc → j.succ ≤ last →
      ∀ y : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
        q₀ < (H.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * (H.event j).incoming.flow.scalar t y ^ 2 := by
    intro j _ hjl y t ht hqy
    refine eventSlab_derivative_of_P2_O2 Hp hP2 n j q₀ ?_ y t ht hqy
    have h0 : 0 ≤ (F.tower.history n).time j.succ := H.time_nonneg j.succ
    have htl : (F.tower.history n).time j.succ ≤ H.time last :=
      (F.tower.history n).time_strictMono.monotone hjl
    have hr := Hp.radius_antitone (show (F.tower.history n).time j.succ ∈ Ici 0 from h0)
      (show H.time last ∈ Ici 0 from h0.trans htl) htl
    have hr0 := Hp.parameters.neckRadius_pos _ (h0.trans htl)
    have hsq : Hp.parameters.neckRadius (H.time last) ^ 2 ≤
        Hp.parameters.neckRadius ((F.tower.history n).time j.succ) ^ 2 :=
      pow_le_pow_left₀ hr0.le hr 2
    exact (inv_anti₀ (by positivity) hsq).trans hrq
  have hzmem : (z : ThreeSpace) ∈ standardCapWindow Hp.parameters.modelRadius := hsub z.2
  obtain ⟨Ξ, -, hbirth, hpoint, -, -, -, -, -, -, -, -, -, -, -, -, hjets⟩ :=
    hjet (Dbig := Hp.parameters.modelRadius) w hmargin le_rfl le_rfl H i.succ last hle s G L hG S.window S.window_smooth S.neck.scale q₀ a₀ hq hq₀
      hq₀C ha₀ hmetric Hp.parameters (Hp.records n) hHI hscal hrec hslab hfinal hη' z x A
      (hA ⟨z.val, hzmem⟩ rfl)
  refine ⟨Ξ, fun y y' hy => ?_, hpoint, fun j hj y hy => hjets j hj y hy⟩
  exact (hbirth y).trans (congrArg S.window (Subtype.ext hy.symm))

end GC.LongTime.Ch12
