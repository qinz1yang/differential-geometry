import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.AnalyticAdmissibility
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapWindows
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodInduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckTransportDecoupled

/-!
# CH12-O2, group 1: the enhanced-profile hypotheses P1–P4 (shapes only)

User decision (option 1): the A12 profile `AnalyticSurgeryProfile` is **not** changed.  The four
extra inputs identified by CH12-O1 (`docs/geometrization/chapter12/design-D2-D3-M02-20261006.md`
§1.5, §2.2) are written here as `def … : Prop` *hypothesis shapes*.  They are never assumed as
axioms and never become structure fields; every theorem of the `EnhancedProfile*` files takes
them as explicit arguments.  See `docs/geometrization/chapter12/enhanced-profile-hypotheses-20261006.md`
for the supply obligations (what A12 / chapter 11 must prove).

* `P1_O2 Hp` — the canonical cap window datum `(δ', k)` is linked to the static neck.
* `P2_O2 Hp Ctime` — scale-invariant scalar time-derivative bound above the canonical threshold.
* `P3_O2 Hp` — the fixed collar length admits all-order canonical witnesses, and the model window
  radius is large enough for the cap-window flow kernel.
* `P4_O2 Hp` — `epsilon` is below the explicit KL70.2 constant.

Proved here: P1 strengthens `canonical_windows`; P3's first clause is satisfiable
(`exists_collarLength_P3_O2`); under P1 + `hdec` every late window datum is as precise and of as
high order as wanted, uniformly in `n i b` (`late_window_datum_O2`); P2 gives the event-slab
premise of the existing kernels (`eventSlab_derivative_of_P2_O2`).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Neck
open Set
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch12

universe u

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

/-! ## Explicit constants -/

/-- The explicit cone-tolerance of the KL70.2 kernel
(`BoundedCurvatureAtDistanceBoundedThreshold.lean:923`). -/
def εKL70_O2 : ℝ :=
  min (neckModelTolerance (1 / 4000000 / 26000)) (1 / 4000000 / 26000 / 64) / (13000 * 13000)

theorem εKL70_pos_O2 : 0 < εKL70_O2 := by
  have hmin : 0 < min (neckModelTolerance (1 / 4000000 / 26000)) (1 / 4000000 / 26000 / 64) :=
    lt_min (neckModelTolerance_pos (by norm_num)) (by norm_num)
  unfold εKL70_O2
  positivity

/-- The cap-window radius used with the cap-window flow kernel
(`PreparedCapWindowGeometry.lean:668`) at `eps = 1/1000`, `r = transitionEnd + 1002`:
`64 * (r + eps⁻¹) < capWindowRadius_O2`. -/
def capWindowRadius_O2 : ℝ := 64 * (DifferentialGeometry.PDE.RicciFlow.StandardCap.transitionEnd + 1002 + 1000) + 1

/-! ## P1: linked canonical window -/

section LinkedWindow

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
  {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}

/-- `hasCanonicalWindow` (`CanonicalCapWindows.lean:22`) with the insertion datum `(δ', k)` tied
to the static neck: `δ' ≤ S.delta` and `2⌊δ'⁻¹⌋ ≤ k` (CH12-O1's P1). -/
def linkedCanonicalWindow_O2 (S : E.PresentedStaticCap fixed D m ε b) : Prop :=
  ∃ (x₀ : E.incoming.terminalRegularOpen) (δ' : ℝ) (k : ℕ)
    (d : normalizedDatum E.terminal.metric x₀ δ' k)
    (w : DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness d
      fixed.collarLength fixed.collar_pos D m ε),
    metricScalarAt E.terminal.metric x₀ = S.neck.scale ∧
    (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
      S.neck.scale * E.outputMetric.inner (S.window x)
        (mfderiv ThreeModel ThreeModel S.window x v)
        (mfderiv ThreeModel ThreeModel S.window x z)) ∧
    (∀ z : ThreeBall, ∃ x : standardCapWindow D,
      ‖x.val‖ ≤ DifferentialGeometry.PDE.RicciFlow.StandardCap.transitionEnd ∧
      S.window x = S.inclusion (S.witness.cap z)) ∧
    δ' ≤ S.delta ∧ 2 * ⌊δ'⁻¹⌋₊ ≤ k

theorem linkedCanonicalWindow_hasCanonicalWindow_O2 (S : E.PresentedStaticCap fixed D m ε b)
    (h : linkedCanonicalWindow_O2 S) : S.hasCanonicalWindow := by
  obtain ⟨x₀, δ', k, d, w, h1, h2, h3, -, -⟩ := h
  exact ⟨x₀, δ', k, d, w, h1, h2, h3⟩

end LinkedWindow

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

/-- **P1** (hypothesis shape). -/
def P1_O2 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) : Prop :=
  ∀ n (i : Fin (F.tower.history n).eventCount)
    (b : ((F.tower.history n).toHistory.event i).RetainedBoundaryIndex),
    linkedCanonicalWindow_O2 ((Hp.records n i).static b)

/-- **P2** (hypothesis shape): on every event slab and on the final slab of every history of the
tower, `|∂_t R| ≤ Ctime R²` wherever `R > neckRadius(t)⁻²`. -/
def P2_O2 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) (Ctime : ℝ≥0) : Prop :=
  (∀ n (j : Fin (F.tower.history n).eventCount)
      (y : ((F.tower.history n).stage j.castSucc).Carrier) (t : ℝ),
      t ∈ Ioo ((F.tower.history n).time j.castSucc) ((F.tower.history n).time j.succ) →
      (Hp.parameters.neckRadius t ^ 2)⁻¹ <
        ((F.tower.history n).toHistory.event j).incoming.flow.scalar t y →
      |derivWithin (fun v => ((F.tower.history n).toHistory.event j).incoming.flow.scalar v y)
          (Iic t) t| ≤
        Ctime * ((F.tower.history n).toHistory.event j).incoming.flow.scalar t y ^ 2) ∧
  (∀ n (h : (F.tower.history n).time (Fin.last (F.tower.history n).eventCount) <
        (F.tower.history n).horizon)
      (y : ((F.tower.history n).stage (Fin.last (F.tower.history n).eventCount)).Carrier)
      (t : ℝ),
      t ∈ Ioo ((F.tower.history n).time (Fin.last (F.tower.history n).eventCount))
        (F.tower.history n).horizon →
      (Hp.parameters.neckRadius t ^ 2)⁻¹ < ((F.tower.history n).finalSlab h).flow.scalar t y →
      |derivWithin (fun v => ((F.tower.history n).finalSlab h).flow.scalar v y) (Iic t) t| ≤
        Ctime * ((F.tower.history n).finalSlab h).flow.scalar t y ^ 2)

/-- The collar-length clause of **P3**: the collar length `A` admits canonical static insertion
witnesses of every order and accuracy (on 3-manifolds of universe `u`).  This is exactly the
conclusion of `StandardCap.exists_canonicalStaticInsertionWitness` for its constant `A*`. -/
def collarAdmitsAllOrders_O2 (A : ℝ) (hA : 0 < A) : Prop :=
  ∀ (D : ℝ), 0 < D → ∀ (m : ℕ) (ε : ℝ), 0 < ε →
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ' : ℝ, 0 < δ' → δ' ≤ δ₀ →
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold ThreeModel ∞ M] [T2Space M]
        (h : SmoothRiemannianMetric ThreeModel M) (x₀ : M)
        (d : normalizedDatum h x₀ δ' (m + 4)),
        Nonempty (DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness
          d A hA D m ε)

/-- **P3** (hypothesis shape). -/
def P3_O2 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) : Prop :=
  collarAdmitsAllOrders_O2.{u} Hp.parameters.fixed.collarLength Hp.parameters.fixed.collar_pos ∧
    capWindowRadius_O2 + 1 ≤ Hp.parameters.modelRadius

/-- **P4** (hypothesis shape). -/
def P4_O2 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) : Prop :=
  Hp.epsilon ≤ εKL70_O2

/-! ## Elementary consequences -/

/-- P1 strengthens the existing profile field. -/
theorem canonical_windows_of_P1_O2 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (hP1 : P1_O2 Hp) (n : ℕ) (i : Fin (F.tower.history n).eventCount)
    (b : ((F.tower.history n).toHistory.event i).RetainedBoundaryIndex) :
    ((Hp.records n i).static b).hasCanonicalWindow :=
  linkedCanonicalWindow_hasCanonicalWindow_O2 _ (hP1 n i b)

/-- Non-vacuity of P3's first clause: the constant of
`StandardCap.exists_canonicalStaticInsertionWitness` satisfies it. -/
theorem exists_collarLength_P3_O2 :
    ∃ (A : ℝ) (hA : 0 < A), 2 * A < 1 / 2 ∧ collarAdmitsAllOrders_O2.{u} A hA := by
  obtain ⟨A, hA, hsmall, h⟩ :=
    DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_canonicalStaticInsertionWitness.{0, 0, u}
  refine ⟨A, hA, hsmall, ?_⟩
  intro D hD m ε hε
  obtain ⟨δ₀, hδ₀, -, hb⟩ := h D hD m ε hε
  refine ⟨δ₀, hδ₀, fun δ' hδ' hle M _ _ _ _ hm x₀ d => ?_⟩
  exact hb δ' hδ' hle hm x₀ d

/-- Under P1 and `hdec`, after some time every canonical window datum of every cutoff record is
as precise and of as high order as wanted, uniformly in the history index, event and boundary. -/
theorem late_window_datum_O2 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hP1 : P1_O2 Hp) (m : ℕ) (δ₀ : ℝ) (hδ₀ : 0 < δ₀) :
    ∃ T : ℝ, ∀ n (i : Fin (F.tower.history n).eventCount)
      (b : ((F.tower.history n).toHistory.event i).RetainedBoundaryIndex),
      T < (F.tower.history n).time i.succ →
      ∃ (x₀ : ((F.tower.history n).toHistory.event i).incoming.terminalRegularOpen) (δ' : ℝ)
        (k : ℕ) (d : normalizedDatum ((F.tower.history n).toHistory.event i).terminal.metric
          x₀ δ' k)
        (w : DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness d
          Hp.parameters.fixed.collarLength Hp.parameters.fixed.collar_pos
          Hp.parameters.modelRadius Hp.parameters.modelOrder Hp.parameters.modelAccuracy),
        metricScalarAt ((F.tower.history n).toHistory.event i).terminal.metric x₀ =
            ((Hp.records n i).static b).neck.scale ∧
        (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
          ((Hp.records n i).static b).neck.scale *
            ((F.tower.history n).toHistory.event i).outputMetric.inner
              (((Hp.records n i).static b).window x)
              (mfderiv ThreeModel ThreeModel ((Hp.records n i).static b).window x v)
              (mfderiv ThreeModel ThreeModel ((Hp.records n i).static b).window x z)) ∧
        (∀ z : ThreeBall, ∃ x : standardCapWindow Hp.parameters.modelRadius,
          ‖x.val‖ ≤ DifferentialGeometry.PDE.RicciFlow.StandardCap.transitionEnd ∧
          ((Hp.records n i).static b).window x =
            ((Hp.records n i).static b).inclusion (((Hp.records n i).static b).witness.cap z)) ∧
        δ' ≤ δ₀ ∧ m ≤ k := by
  -- choose a target precision for the record neck: `recenterConstant * δ_rec < min δ₀ (1/(m+1))`
  set c := Hp.parameters.recenterConstant with hc
  have hc4 : 4 ≤ c := Hp.parameters.recenterConstant_ge_four
  have hcpos : 0 < c := by linarith
  set η : ℝ := min δ₀ (1 / ((m : ℝ) + 1)) with hη
  have hηpos : 0 < η := lt_min hδ₀ (by positivity)
  obtain ⟨B, hB⟩ := hdec (η / c) (div_pos hηpos hcpos)
  refine ⟨B, fun n i b ht => ?_⟩
  obtain ⟨x₀, δ', k, d, w, h1, h2, h3, hδS, hk⟩ := hP1 n i b
  refine ⟨x₀, δ', k, d, w, h1, h2, h3, ?_⟩
  -- the static neck precision
  have hrec := (Hp.records n i).recenter_delta b
  have hle := (Hp.records n i).delta_le b.1.1
  rw [Hp.accuracy_eq] at hle
  have hlt : (Hp.records n i).delta b.1.1 < η / c := hle.trans_lt (hB _ ht)
  have hS : ((Hp.records n i).static b).delta < η := by
    rw [hrec]
    have := mul_lt_mul_of_pos_left hlt hcpos
    rwa [mul_div_cancel₀ _ hcpos.ne'] at this
  have hδ'η : δ' < η := hδS.trans_lt hS
  refine ⟨(hδ'η.trans_le (min_le_left _ _)).le, ?_⟩
  -- order: `2⌊δ'⁻¹⌋ ≤ k` and `δ' < 1/(m+1)`
  have hpos : 0 < δ' := d.precision_pos
  have hlt' : δ' < 1 / ((m : ℝ) + 1) := hδ'η.trans_le (min_le_right _ _)
  have hinv : (m : ℝ) + 1 < δ'⁻¹ := by
    have h1 : (m : ℝ) + 1 = (1 / ((m : ℝ) + 1))⁻¹ := by field_simp
    rw [h1]
    exact (inv_lt_inv₀ (by positivity) hpos).mpr hlt'
  have hfloor : m + 1 ≤ ⌊δ'⁻¹⌋₊ := by
    apply Nat.le_floor
    push_cast
    exact hinv.le
  omega

/-- P2 supplies the event-slab premise `EventSlabsDerivative`-style bound of the existing kernels
for any threshold `q` above `neckRadius(time j.succ)⁻²` (the threshold is increasing in time). -/
theorem eventSlab_derivative_of_P2_O2 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    {Ctime : ℝ≥0} (hP2 : P2_O2 Hp Ctime) (n : ℕ) (j : Fin (F.tower.history n).eventCount)
    (q : ℝ) (hq : (Hp.parameters.neckRadius ((F.tower.history n).time j.succ) ^ 2)⁻¹ ≤ q)
    (y : ((F.tower.history n).stage j.castSucc).Carrier) (t : ℝ)
    (ht : t ∈ Ioo ((F.tower.history n).time j.castSucc) ((F.tower.history n).time j.succ))
    (hqy : q < ((F.tower.history n).toHistory.event j).incoming.flow.scalar t y) :
    |derivWithin (fun v => ((F.tower.history n).toHistory.event j).incoming.flow.scalar v y)
        (Iic t) t| ≤
      Ctime * ((F.tower.history n).toHistory.event j).incoming.flow.scalar t y ^ 2 := by
  apply hP2.1 n j y t ht
  have ht0 : 0 ≤ t := ((F.tower.history n).toHistory.time_nonneg j.castSucc).trans ht.1.le
  have htj : 0 ≤ (F.tower.history n).time j.succ := ht0.trans ht.2.le
  have hr := Hp.radius_antitone (show t ∈ Ici 0 from ht0)
    (show (F.tower.history n).time j.succ ∈ Ici 0 from htj) ht.2.le
  have hr0 := Hp.parameters.neckRadius_pos _ htj
  have hsq : Hp.parameters.neckRadius ((F.tower.history n).time j.succ) ^ 2 ≤
      Hp.parameters.neckRadius t ^ 2 := pow_le_pow_left₀ hr0.le hr 2
  have hinv : (Hp.parameters.neckRadius t ^ 2)⁻¹ ≤
      (Hp.parameters.neckRadius ((F.tower.history n).time j.succ) ^ 2)⁻¹ :=
    inv_anti₀ (by positivity) hsq
  exact (hinv.trans hq).trans_lt hqy

/-! ## P5 (CH12-O3, user decision): late cut records with large cap windows -/

/-- **P5** (hypothesis shape, CH12-O3).  For every window radius `D`, accuracy `ζ > 0` and order
`m`, after some time `T` every event of every history of the tower carries a cutoff record whose
parameters agree with the profile's (`delta`, `neckRadius`, `fixed`) but whose canonical cap windows
have radius `≥ D`, accuracy `≤ ζ` and order `≥ m`.  Only events after `T` are required: early
surgeries need not admit large windows.  (Supply: chapter 11; geometrically the cap window radius
of a late cutoff is `~ δ⁻¹ → ∞`.)  Used by the surgery-tolerant local KL70.2 kernel
(`MicroGlueLateRecords.lean`), whose window radius `Rrad` depends on `κ = κ(w)`. -/
def P5_O3 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) : Prop :=
  ∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ T : ℝ, ∀ n, ∃ p : CutoffParameters,
    p.delta = Hp.parameters.delta ∧ p.neckRadius = Hp.parameters.neckRadius ∧
    p.fixed = Hp.parameters.fixed ∧
    D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ζ ∧ m ≤ p.modelOrder ∧
    ∃ records : ∀ i : Fin (F.tower.history n).eventCount,
        T ≤ (F.tower.history n).time i.succ →
        GeometricCutoffRecord (F.tower.history n).toHistory i p,
      ∀ i hi b, ((records i hi).static b).hasCanonicalWindow

/-! ## P6 (CH12-S23, user decision): KL84.1(b) at late slices -/

section P6
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Riemannian

/-- **P6** (hypothesis shape, CH12-S23): Kleiner–Lott Prop. 84.1(b) at late regular slices, for each
fixed enlargement factor `A`.  Hypotheses (1)–(3) of KL84.1 at `(p, s.time, r)`: the solution is
unscathed with `|Rm| ≤ 1/(3r²)` on the backward parabolic ball (`hasSmallParabolicCurvature`,
`2r² < t`), and `vol B(p, r) ≥ A⁻¹ r³`.  Conclusion (b): every `y ∈ B(p, A r)` with
`R(y) ≥ K₁ r⁻²` has a canonical neighbourhood (a neck-chart witness, as in the profile field
`canonical`).  `K₁`, `T` depend only on `A` (and the profile), not on the slice, point or `r`.
Parts (a), (c) of KL84.1 are not included (part (c) is the profile field
`larger_ball_scalar_control`, the only part with the restriction `r ≤ r̄(A) √t`; (b) has none).
The smallness `δ < δ_A` of KL84.1 is absorbed in `T` (`largerBallAccuracy_on_late_half_interval`).
(Supply: chapter 11 / A12, blueprint `master207A.tex` l.31279 "KL84.1 estimates for each fixed
spatial enlargement factor at all sufficiently late times"; l.17089–17106.) -/
def P6_S23 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ K₁ T : ℝ, 0 < K₁ ∧ 0 < T ∧
    ∀ s : GC.LongTime.RegularSlice F.observation, T ≤ s.time →
    ∀ (p : (s.history.stageAt ⟨s.time, s.positive.le, le_rfl⟩).Carrier) (r : ℝ),
      2 * r ^ 2 < s.time →
      GC.LongTime.hasSmallParabolicCurvature s.history ⟨s.time, s.positive.le, le_rfl⟩ p r →
      ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (s.history.stageMetric
        (s.history.activeStage ⟨s.time, s.positive.le, le_rfl⟩) s.time) p r →
      ∀ y ∈ riemannianBallOf (s.history.stageMetric
        (s.history.activeStage ⟨s.time, s.positive.le, le_rfl⟩) s.time) p (A * r),
        K₁ * (r ^ 2)⁻¹ ≤ metricScalarAt (s.history.stageMetric
          (s.history.activeStage ⟨s.time, s.positive.le, le_rfl⟩) s.time) y →
        ∃ W : SpatialCanonicalWitness (s.history.stageMetric
          (s.history.activeStage ⟨s.time, s.positive.le, le_rfl⟩) s.time)
          Hp.epsilon Hp.C1 Hp.C2 y, W.capTubeHasNeckChart Hp.epsilon

end P6

end GC.LongTime.Ch12
