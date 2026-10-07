import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KcanLocalCone_O23
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroGlueLocalLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroGlueTracedLocal

/-!
# CH12-O23, group 2b: K-can forms of the escape-limit / nonnegative-flow theorems of the local KL70.2 chain

`exists_pointed_convergence_at_scalar_escape_kcan_O23` and
`exists_pointed_convergence_at_scalar_escape_of_traced_buffer_kcan_O23` are the O3 theorems
(`MicroGlueLocalLimit`, `MicroGlueTracedLocal`) with the local volume test `(σ, hσlim, hloc)`
replaced by a normalized volume lower bound at the blow-up CENTRE only (`hvx`); the volume
interface is `hvol_of_buffer_centre_O23`.  Proofs otherwise verbatim.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace GC.LongTime.Ch12

universe u v

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance pointedLimitRegular_O23l (L : PointedRiemannianManifold.{u, 0, 0} ThreeModel) :
    RegularSpace L.M := by
  let _ : LocallyCompactSpace L.M := ChartedSpace.locallyCompactSpace ThreeSpace L.M
  infer_instance

private theorem localPullMetric_restrict_inner_O23 {M N : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M]
    [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold ThreeModel ∞ N]
    (g : SmoothRiemannianMetric ThreeModel N) (Φ : PartialDiffeomorph ThreeModel ThreeModel M N ∞)
    (V : TopologicalSpace.Opens M)
    (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : V => Φ z.val))
    (z : V) (v w : TangentSpace ThreeModel z) :
    (localPullMetric g (fun z : V => Φ z.val) hf).inner z v w =
      g.inner (Φ z) (mfderiv ThreeModel ThreeModel Φ z v)
        (mfderiv ThreeModel ThreeModel Φ z w) := by
  rw [localPullMetric_inner]
  have hd := DifferentialGeometry.mfderiv_restrict_open (I := ThreeModel) (J := ThreeModel) Φ V z
  rw [hd]
  rfl

private theorem endpoint_scalar_eq_O23 {P : OrientedThreeStage.{u}} {a s : ℝ}
    (A : P.ClosedSlab a s)
    (x : (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen) :
    metricScalarAt (A.endpointTerminalLimitMetric P).metric x = A.flow.scalar s x.val :=
  metricScalarAt_restrictOpen _ _ _

private theorem endpoint_scalar_eq_limit_O23 {P : OrientedThreeStage.{u}} {a s : ℝ}
    (A : P.ClosedSlab a s)
    (x : (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen) :
    metricScalarAt (A.endpointTerminalLimitMetric P).metric x = A.flow.scalar s x.val :=
  metricScalarAt_restrictOpen _ _ _

/-- K-can form of `exists_pointed_convergence_at_scalar_escape_local_O3`: `(σ, hσlim, hloc)`
replaced by the normalized centre volume `hvx`. -/
theorem exists_pointed_convergence_at_scalar_escape_kcan_O23
    (H : ℕ → RetainedCoreHistory.{u}) (time : ℕ → ℝ)
    (A : ∀ i, ((H i).stage (Fin.last (H i).eventCount)).ClosedSlab
      ((H i).time (Fin.last (H i).eventCount)) (time i)) :
    let G := fun i => (A i).restrictIncoming le_rfl (A i).lt le_rfl;
    let L := fun i => (A i).endpointTerminalLimitMetric ((H i).stage (Fin.last (H i).eventCount));
    ∀ (_hinit : ∀ i, (A i).flow.base.metric ((H i).time (Fin.last (H i).eventCount)) =
      (H i).initialMetric (Fin.last (H i).eventCount)),
    (∀ i, (H i).horizon < time i) →
    ∀ (Ctime Cgrad : ℝ≥0) (q : ℕ → ℝ), (∀ i, 0 < q i) →
    (∀ i (j : Fin (H i).eventCount) (y : ((H i).stage j.castSucc).Carrier),
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
        q i < ((H i).toHistory.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => ((H i).toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * ((H i).toHistory.event j).incoming.flow.scalar t y ^ 2) →
    (∀ i y, ∀ t ∈ Ioo ((H i).time (Fin.last (H i).eventCount)) (time i),
      q i < (A i).flow.scalar t y →
      |derivWithin (fun v => (A i).flow.scalar v y) (Iic t) t| ≤
        Ctime * (A i).flow.scalar t y ^ 2) →
    (∀ i y, ∀ t ∈ Ioo ((H i).time (Fin.last (H i).eventCount)) (time i),
      q i < (G i).flow.scalar t y → ∀ v : TangentSpace ThreeModel y,
        |Perelman.CanonicalNeighborhood.scalarDifferential (G i).flow t y v| ≤
          Cgrad * (G i).flow.scalar t y * Real.sqrt ((G i).flow.scalar t y) *
            Real.sqrt (((G i).flow.base.metric t).inner y v v)) →
    ∀ (x : ∀ i, (G i).terminalRegularOpen) (hQ : ∀ i, 1 ≤ (A i).flow.scalar (time i) (x i).val),
    (∀ i, q i ≤ (A i).flow.scalar (time i) (x i).val) →
    ∀ θ₀ : ℝ, 0 < θ₀ →
    (∀ i, (H i).time (Fin.last (H i).eventCount) ≤
      time i - θ₀ / (A i).flow.scalar (time i) (x i).val) →
    (∃ R : ℝ, 0 < R ∧ ¬ ∃ B : ℝ, ∀ᶠ i in atTop,
      ∀ y : (G i).terminalRegularOpen,
        riemannianEDistOf (scaleMetric ((A i).flow.scalar (time i) (x i).val)
          (zero_lt_one.trans_le (hQ i)) (L i).metric) (x i) y < ENNReal.ofReal R →
        metricScalarAt (L i).metric y / (A i).flow.scalar (time i) (x i).val ≤ B) →
    ∀ (Phi : ℝ → ℝ), Perelman.AdmissiblePinchingFunction Phi →
    (∀ i j, Perelman.PhiAlmostNonnegative ((H i).toHistory.event j).incoming.flow
      (Ico ((H i).time j.castSucc) ((H i).time j.succ)) Phi) →
    (∀ i, Perelman.PhiAlmostNonnegative (G i).flow
      (Ico ((H i).time (Fin.last (H i).eventCount)) (time i)) Phi) →
    ∀ (κ a₀ : ℝ), 0 < κ → 0 < a₀ →
    (∀ i, ∀ b : ℝ, 0 < b → b ≤ a₀ →
      ENNReal.ofReal (κ * b ^ 3) ≤
        riemannianVolumeMeasure ThreeModel (G i).terminalRegularOpen
          (scaleMetric ((A i).flow.scalar (time i) (x i).val) (zero_lt_one.trans_le (hQ i))
            (L i).metric)
          (riemannianBallOf (scaleMetric ((A i).flow.scalar (time i) (x i).val)
            (zero_lt_one.trans_le (hQ i)) (L i).metric) (x i) b)) →
    ∃ (rho : ℝ), 0 < rho ∧ ∃ (ind : ℕ → ℕ), StrictMono ind ∧
      ∃ z : ∀ i, (G (ind i)).terminalRegularOpen,
      let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
        { obj := fun i =>
            { M := (G (ind i)).terminalRegularOpen
              basepoint := x (ind i)
              metric := scaleMetric ((A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val)
                (zero_lt_one.trans_le (hQ (ind i))) (L (ind i)).metric } };
      ∃ (f : ℕ → ℕ), StrictMono f ∧
        ∃ (r : ℕ → ℝ), (∀ n, 0 < r n ∧ r n < rho) ∧ Tendsto r atTop (𝓝 rho) ∧
        ∃ (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
          (F : PointedRiemannianConvergenceMaps X.connectedComponent P f),
          let U := fun i => connectedComponentOpen (I := ThreeModel) (X.obj i).basepoint;
          let hp := fun i => (mem_connectedComponent : (X.obj i).basepoint ∈ U i);
          let F' := F.liftTargetOpen U hp;
          ∃ M : MetricConvergenceData F',
            metricScalarAt P.metric P.basepoint = 1 ∧
            (∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData F' n) ∧
            (∀ z : P.M, riemannianEDistOf P.metric P.basepoint z < ENNReal.ofReal rho) ∧
            (∀ R : ℝ, 0 ≤ R → R < rho →
              IsCompact (riemannianClosedBallOf P.metric P.basepoint R)) ∧
            (∀ n, riemannianClosedBallOf (X.obj (f n)).metric (X.obj (f n)).basepoint (r n) ⊆
              F'.target n) ∧
            (∀ eps : ℝ, 0 < eps → ∀ᶠ n in atTop, ∀ y ∈ F'.source n,
              ∀ v : TangentSpace ThreeModel y,
              (1 - eps) * P.metric.inner y v v ≤
                  (X.obj (f n)).metric.inner (F'.map n y)
                    (mfderiv ThreeModel ThreeModel (F'.map n) y v)
                    (mfderiv ThreeModel ThreeModel (F'.map n) y v) ∧
                (X.obj (f n)).metric.inner (F'.map n y)
                  (mfderiv ThreeModel ThreeModel (F'.map n) y v)
                  (mfderiv ThreeModel ThreeModel (F'.map n) y v) ≤
                    (1 + eps) * P.metric.inner y v v) ∧
            (∀ n, riemannianEDistOf (X.obj (f n)).metric (X.obj (f n)).basepoint (z (f n)) ≠ ⊤) ∧
            Tendsto (fun n => (riemannianEDistOf (X.obj (f n)).metric (X.obj (f n)).basepoint
              (z (f n))).toReal) atTop (𝓝 rho) ∧
            Tendsto (fun n => metricScalarAt (L (ind (f n))).metric (z (f n)) /
              (A (ind (f n))).flow.scalar (time (ind (f n))) (x (ind (f n))).val)
              atTop atTop := by
  intro G L hinit hs Ctime Cgrad q hq hderiv hfinal hgradient x hQ hqQ θ₀ hθ₀ hwindow hfailure
    Phi hPhi hpinch hpinchFinal κ a₀ hκ ha₀ hvx
  have hQpos : ∀ i, 0 < (A i).flow.scalar (time i) (x i).val :=
    fun i => zero_lt_one.trans_le (hQ i)
  obtain ⟨rho, ind, hrho, hind, hinner, z, hfinite, hdist, hscalarEscape⟩ :=
    exists_terminal_scalar_escape_radius_of_derivative_bounds
      (fun i => (H i).stage (Fin.last (H i).eventCount))
      (fun i => (H i).time (Fin.last (H i).eventCount)) time G L x
      (fun i => (A i).flow.scalar (time i) (x i).val) hQpos Cgrad q hqQ hgradient
      (fun _ => Ctime) hfinal (fun i => (endpoint_scalar_eq_O23 (A i) (x i)).le) hfailure
  have hbuf : ∀ R : ℝ, 0 < R → R < rho → ∃ r Amax θ : ℝ,
      0 < r ∧ R + r < rho ∧ 1 ≤ Amax ∧ 0 < θ ∧ 6 * Ctime * (Amax * θ) ≤ 1 ∧
      ∀ᶠ i in atTop,
        IsCompact (riemannianClosedBallOf
          (scaleMetric ((A i).flow.scalar (time i) (x i).val) (hQpos i) (L i).metric)
            (x i) (R + r)) ∧
        (∀ y ∈ riemannianClosedBallOf
          (scaleMetric ((A i).flow.scalar (time i) (x i).val) (hQpos i) (L i).metric)
            (x i) (R + r),
          metricScalarAt (L i).metric y ≤ 2 * (Amax * (A i).flow.scalar (time i) (x i).val)) ∧
        ∃ first : Fin ((H i).eventCount + 1),
          (∀ y ∈ riemannianClosedBallOf
            (scaleMetric ((A i).flow.scalar (time i) (x i).val) (hQpos i) (L i).metric)
              (x i) (R + r),
            Nonempty (BackwardPointTrace (H i).toHistory first (Fin.last (H i).eventCount)
              (Fin.le_last first) y.val)) ∧
          (H i).time first ≤ time i - θ / (A i).flow.scalar (time i) (x i).val := by
    intro R hR hRrho
    let r := (rho - R) / 2
    have hr : 0 < r := half_pos (sub_pos.mpr hRrho)
    have hRr : R + r < rho := by dsimp [r]; linarith
    obtain ⟨B, hB⟩ := hinner (R + r) (by positivity) hRr
    let Amax := max 1 B
    have hAmax : 1 ≤ Amax := le_max_left _ _
    have hBA : B ≤ Amax := le_max_right _ _
    let θ := min θ₀ (1 / (6 * ((Ctime : ℝ) + 1) * Amax))
    have hθ : 0 < θ := lt_min hθ₀ (by positivity)
    have hθθ₀ : θ ≤ θ₀ := min_le_left _ _
    have hθbudget : θ * (6 * ((Ctime : ℝ) + 1) * Amax) ≤ 1 :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    have hbudget : 6 * (Ctime : ℝ) * (Amax * θ) ≤ 1 := by
      have hC : (0 : ℝ) ≤ Ctime := Ctime.coe_nonneg
      nlinarith [mul_nonneg (zero_le_one.trans hAmax) hθ.le]
    refine ⟨r, Amax, θ, hr, hRr, hAmax, hθ, hbudget, ?_⟩
    filter_upwards [hB] with i hi
    refine ⟨hi.1, ?_, Fin.last (H i).eventCount, ?_, ?_⟩
    · intro y hy
      have hb := (div_le_iff₀ (hQpos i)).mp (hi.2 y hy)
      have hQi := hQpos i
      nlinarith [mul_le_mul_of_nonneg_right hBA hQi.le]
    · intro y _
      exact ⟨BackwardPointTrace.singleton (H i).toHistory (Fin.last (H i).eventCount) y.val⟩
    · have hdiv : θ / (A i).flow.scalar (time i) (x i).val ≤
          θ₀ / (A i).flow.scalar (time i) (x i).val :=
        div_le_div_of_nonneg_right hθθ₀ (hQpos i).le
      linarith [hwindow i]
  have hbufR : ∀ R : ℝ, 0 < R → R < rho → ∃ r Amax θ : ℝ,
      0 < r ∧ R + r < rho ∧ 1 ≤ Amax ∧ 0 < θ ∧ 6 * Ctime * (Amax * θ) ≤ 1 ∧
      ∀ᶠ i in atTop,
        IsCompact (riemannianClosedBallOf
          (scaleMetric ((A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val)
            (hQpos (ind i)) (L (ind i)).metric) (x (ind i)) (R + r)) ∧
        (∀ y ∈ riemannianClosedBallOf
          (scaleMetric ((A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val)
            (hQpos (ind i)) (L (ind i)).metric) (x (ind i)) (R + r),
          metricScalarAt (L (ind i)).metric y ≤
            2 * (Amax * (A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val)) ∧
        ∃ first : Fin ((H (ind i)).eventCount + 1),
          (∀ y ∈ riemannianClosedBallOf
            (scaleMetric ((A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val)
              (hQpos (ind i)) (L (ind i)).metric) (x (ind i)) (R + r),
            Nonempty (BackwardPointTrace (H (ind i)).toHistory first
              (Fin.last (H (ind i)).eventCount) (Fin.le_last first) y.val)) ∧
          (H (ind i)).time first ≤
            time (ind i) - θ / (A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val := by
    intro R hR hRrho
    obtain ⟨r, Amax, θ, hrr, hrrho, hAmax, hθ, hbudget, hb⟩ := hbuf R hR hRrho
    exact ⟨r, Amax, θ, hrr, hrrho, hAmax, hθ, hbudget, hind.tendsto_atTop.eventually hb⟩
  have hvol : ∀ r R : ℝ, 0 < r → r < R → R < rho → ∀ J : ℝ, 0 ≤ J →
      ∃ a κ' : ℝ, 0 < a ∧ 0 < κ' ∧ r + a ≤ R ∧ a ^ 4 * J ^ 2 ≤ 1 ∧
      ∀ᶠ n in atTop, ∀ y ∈ riemannianClosedBallOf
        (scaleMetric ((A (ind n)).flow.scalar (time (ind n)) (x (ind n)).val)
          (zero_lt_one.trans_le (hQ (ind n))) (L (ind n)).metric) (x (ind n)) r,
        ENNReal.ofReal (κ' * a ^ 3) ≤ riemannianVolumeMeasure ThreeModel
          (G (ind n)).terminalRegularOpen
          (scaleMetric ((A (ind n)).flow.scalar (time (ind n)) (x (ind n)).val)
            (zero_lt_one.trans_le (hQ (ind n))) (L (ind n)).metric)
          (riemannianBallOf (scaleMetric ((A (ind n)).flow.scalar (time (ind n)) (x (ind n)).val)
            (zero_lt_one.trans_le (hQ (ind n))) (L (ind n)).metric) y a) :=
    hvol_of_buffer_centre_O23 Phi hPhi (fun i => H (ind i)) (fun i => time (ind i))
      (fun i => G (ind i)) (fun i => L (ind i)) (fun i => hinit (ind i)) (fun i => x (ind i))
      (fun i => q (ind i)) (fun i => (A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val)
      (fun i => hq (ind i)) (fun i => hqQ (ind i)) (fun i => hQ (ind i))
      (fun i j => hderiv (ind i) j) (fun i => hfinal (ind i)) (fun i j => hpinch (ind i) j)
      (fun i => hpinchFinal (ind i)) hrho hbufR hκ ha₀ (Eventually.of_forall fun i => hvx (ind i))
  refine ⟨rho, hrho, ind, hind, z, ?_⟩
  dsimp only
  have hconv :=
    ObservedHistory.exists_terminal_pointed_convergence_of_buffered_backward_traces
      Phi hPhi (fun i => (H (ind i)).toHistory) (fun i => Fin.last (H (ind i)).eventCount)
      (fun i => time (ind i)) (fun i => G (ind i)) (fun i => L (ind i))
      (fun i => hinit (ind i)) (fun i => x (ind i)) (fun i => q (ind i))
      (fun i => (A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val) (fun i => hq (ind i))
      (fun i => hqQ (ind i)) (fun i => hQ (ind i))
      (fun i j _ => hderiv (ind i) j) (fun i => hfinal (ind i))
      (fun i j _ => hpinch (ind i) j) (fun i => hpinchFinal (ind i)) hrho (by
        intro R hR hRrho
        obtain ⟨r, Amax, θ, hrr, hrrho, hAmax, hθ, hbudget, hb⟩ := hbufR R hR hRrho
        refine ⟨r, Amax, θ, hrr, hrrho, hAmax, hθ, hbudget, ?_⟩
        filter_upwards [hb] with i hi
        obtain ⟨first, htrace, hstart⟩ := hi.2.2
        exact ⟨hi.1, hi.2.1, first, Fin.le_last first, htrace, hstart⟩) hvol
  dsimp only at hconv
  obtain ⟨f, hf, r, hr, hrlim, P, F, M, hcanonicalDomain, hradial, hcompact, hcapture,
      hmetric⟩ := hconv
  have hscalarOne : metricScalarAt P.metric P.basepoint = 1 :=
    Perelman.KappaSolutions.pointedScalar_base_eq_of_metricCG_canonical_domains M
      hcanonicalDomain (by
        intro n
        change metricScalarAt (scaleMetric
          ((A (ind (f n))).flow.scalar (time (ind (f n))) (x (ind (f n))).val)
          (hQpos (ind (f n))) (L (ind (f n))).metric) (x (ind (f n))) = 1
        rw [metricScalarAt_scaleMetric, endpoint_scalar_eq_O23, inv_mul_cancel₀]
        exact (hQpos (ind (f n))).ne')
  exact ⟨f, hf, r, hr, hrlim, P, F, M, hscalarOne, hcanonicalDomain, hradial, hcompact,
    hcapture, hmetric, fun n => hfinite (f n), hdist.comp hf.tendsto_atTop,
    hscalarEscape.comp hf.tendsto_atTop⟩

/-- K-can form of `exists_pointed_convergence_at_scalar_escape_of_traced_buffer_local_O3`. -/
theorem exists_pointed_convergence_at_scalar_escape_of_traced_buffer_kcan_O23
    (H : ℕ → RetainedCoreHistory.{u}) (time : ℕ → ℝ)
    (A : ∀ i, ((H i).stage (Fin.last (H i).eventCount)).ClosedSlab
      ((H i).time (Fin.last (H i).eventCount)) (time i)) :
    let G := fun i => (A i).restrictIncoming le_rfl (A i).lt le_rfl;
    let L := fun i => (A i).endpointTerminalLimitMetric ((H i).stage (Fin.last (H i).eventCount));
    ∀ (_hinit : ∀ i, (A i).flow.base.metric ((H i).time (Fin.last (H i).eventCount)) =
      (H i).initialMetric (Fin.last (H i).eventCount)),
    (∀ i, (H i).horizon < time i) →
    ∀ (Ctime Cgrad : ℝ≥0) (q : ℕ → ℝ), (∀ i, 0 < q i) →
    (∀ i (j : Fin (H i).eventCount) (y : ((H i).stage j.castSucc).Carrier),
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
        q i < ((H i).toHistory.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => ((H i).toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * ((H i).toHistory.event j).incoming.flow.scalar t y ^ 2) →
    (∀ i y, ∀ t ∈ Ioo ((H i).time (Fin.last (H i).eventCount)) (time i),
      q i < (A i).flow.scalar t y →
      |derivWithin (fun v => (A i).flow.scalar v y) (Iic t) t| ≤
        Ctime * (A i).flow.scalar t y ^ 2) →
    (∀ i y, ∀ t ∈ Ioo ((H i).time (Fin.last (H i).eventCount)) (time i),
      q i < (G i).flow.scalar t y → ∀ v : TangentSpace ThreeModel y,
        |Perelman.CanonicalNeighborhood.scalarDifferential (G i).flow t y v| ≤
          Cgrad * (G i).flow.scalar t y * Real.sqrt ((G i).flow.scalar t y) *
            Real.sqrt (((G i).flow.base.metric t).inner y v v)) →
    ∀ (x : ∀ i, (G i).terminalRegularOpen) (hQ : ∀ i, 1 ≤ (A i).flow.scalar (time i) (x i).val),
    (∀ i, q i ≤ (A i).flow.scalar (time i) (x i).val) →
    (∀ R ε B : ℝ, 0 < R → 0 < ε → (∀ᶠ i in atTop, ∀ y ∈ riemannianClosedBallOf
        (scaleMetric ((A i).flow.scalar (time i) (x i).val) (zero_lt_one.trans_le (hQ i))
          (L i).metric) (x i) (R + ε),
        metricScalarAt (L i).metric y ≤ B * (A i).flow.scalar (time i) (x i).val) →
      ∃ θ : ℝ, 0 < θ ∧ ∀ᶠ i in atTop, ∃ first : Fin ((H i).eventCount + 1),
        (H i).time first ≤ time i - θ / (A i).flow.scalar (time i) (x i).val ∧
        ∀ y ∈ riemannianClosedBallOf
          (scaleMetric ((A i).flow.scalar (time i) (x i).val) (zero_lt_one.trans_le (hQ i))
            (L i).metric) (x i) R,
          Nonempty (BackwardPointTrace (H i).toHistory first (Fin.last (H i).eventCount)
            (Fin.le_last first) y.val)) →
    (∃ R : ℝ, 0 < R ∧ ¬ ∃ B : ℝ, ∀ᶠ i in atTop,
      ∀ y : (G i).terminalRegularOpen,
        riemannianEDistOf (scaleMetric ((A i).flow.scalar (time i) (x i).val)
          (zero_lt_one.trans_le (hQ i)) (L i).metric) (x i) y < ENNReal.ofReal R →
        metricScalarAt (L i).metric y / (A i).flow.scalar (time i) (x i).val ≤ B) →
    ∀ (Phi : ℝ → ℝ), Perelman.AdmissiblePinchingFunction Phi →
    (∀ i j, Perelman.PhiAlmostNonnegative ((H i).toHistory.event j).incoming.flow
      (Ico ((H i).time j.castSucc) ((H i).time j.succ)) Phi) →
    (∀ i, Perelman.PhiAlmostNonnegative (G i).flow
      (Ico ((H i).time (Fin.last (H i).eventCount)) (time i)) Phi) →
    ∀ (κ a₀ : ℝ), 0 < κ → 0 < a₀ →
    (∀ i, ∀ b : ℝ, 0 < b → b ≤ a₀ →
      ENNReal.ofReal (κ * b ^ 3) ≤
        riemannianVolumeMeasure ThreeModel (G i).terminalRegularOpen
          (scaleMetric ((A i).flow.scalar (time i) (x i).val) (zero_lt_one.trans_le (hQ i))
            (L i).metric)
          (riemannianBallOf (scaleMetric ((A i).flow.scalar (time i) (x i).val)
            (zero_lt_one.trans_le (hQ i)) (L i).metric) (x i) b)) →
    ∃ (rho : ℝ), 0 < rho ∧ ∃ (ind : ℕ → ℕ), StrictMono ind ∧
      ∃ z : ∀ i, (G (ind i)).terminalRegularOpen,
      let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
        { obj := fun i =>
            { M := (G (ind i)).terminalRegularOpen
              basepoint := x (ind i)
              metric := scaleMetric ((A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val)
                (zero_lt_one.trans_le (hQ (ind i))) (L (ind i)).metric } };
      ∃ (f : ℕ → ℕ), StrictMono f ∧
        ∃ (r : ℕ → ℝ), (∀ n, 0 < r n ∧ r n < rho) ∧ Tendsto r atTop (𝓝 rho) ∧
        ∃ (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
          (F : PointedRiemannianConvergenceMaps X.connectedComponent P f),
          let U := fun i => connectedComponentOpen (I := ThreeModel) (X.obj i).basepoint;
          let hp := fun i => (mem_connectedComponent : (X.obj i).basepoint ∈ U i);
          let F' := F.liftTargetOpen U hp;
          ∃ M : MetricConvergenceData F',
            metricScalarAt P.metric P.basepoint = 1 ∧
            (∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData F' n) ∧
            (∀ z : P.M, riemannianEDistOf P.metric P.basepoint z < ENNReal.ofReal rho) ∧
            (∀ R : ℝ, 0 ≤ R → R < rho →
              IsCompact (riemannianClosedBallOf P.metric P.basepoint R)) ∧
            (∀ n, riemannianClosedBallOf (X.obj (f n)).metric (X.obj (f n)).basepoint (r n) ⊆
              F'.target n) ∧
            (∀ eps : ℝ, 0 < eps → ∀ᶠ n in atTop, ∀ y ∈ F'.source n,
              ∀ v : TangentSpace ThreeModel y,
              (1 - eps) * P.metric.inner y v v ≤
                  (X.obj (f n)).metric.inner (F'.map n y)
                    (mfderiv ThreeModel ThreeModel (F'.map n) y v)
                    (mfderiv ThreeModel ThreeModel (F'.map n) y v) ∧
                (X.obj (f n)).metric.inner (F'.map n y)
                  (mfderiv ThreeModel ThreeModel (F'.map n) y v)
                  (mfderiv ThreeModel ThreeModel (F'.map n) y v) ≤
                    (1 + eps) * P.metric.inner y v v) ∧
            (∀ n, riemannianEDistOf (X.obj (f n)).metric (X.obj (f n)).basepoint (z (f n)) ≠ ⊤) ∧
            Tendsto (fun n => (riemannianEDistOf (X.obj (f n)).metric (X.obj (f n)).basepoint
              (z (f n))).toReal) atTop (𝓝 rho) ∧
            Tendsto (fun n => metricScalarAt (L (ind (f n))).metric (z (f n)) /
              (A (ind (f n))).flow.scalar (time (ind (f n))) (x (ind (f n))).val)
              atTop atTop := by
  intro G L hinit hs Ctime Cgrad q hq hderiv hfinal hgradient x hQ hqQ htrace hfailure
    Phi hPhi hpinch hpinchFinal κ a₀ hκ ha₀ hvx
  have hQpos : ∀ i, 0 < (A i).flow.scalar (time i) (x i).val :=
    fun i => zero_lt_one.trans_le (hQ i)
  obtain ⟨rho, ind, hrho, hind, hinner, z, hfinite, hdist, hscalarEscape⟩ :=
    exists_terminal_scalar_escape_radius_of_derivative_bounds
      (fun i => (H i).stage (Fin.last (H i).eventCount))
      (fun i => (H i).time (Fin.last (H i).eventCount)) time G L x
      (fun i => (A i).flow.scalar (time i) (x i).val) hQpos Cgrad q hqQ hgradient
      (fun _ => Ctime) hfinal (fun i => (endpoint_scalar_eq_limit_O23 (A i) (x i)).le) hfailure
  have hbuf : ∀ R : ℝ, 0 < R → R < rho → ∃ r Amax θ : ℝ,
      0 < r ∧ R + r < rho ∧ 1 ≤ Amax ∧ 0 < θ ∧ 6 * Ctime * (Amax * θ) ≤ 1 ∧
      ∀ᶠ i in atTop,
        IsCompact (riemannianClosedBallOf
          (scaleMetric ((A i).flow.scalar (time i) (x i).val) (hQpos i) (L i).metric)
            (x i) (R + r)) ∧
        (∀ y ∈ riemannianClosedBallOf
          (scaleMetric ((A i).flow.scalar (time i) (x i).val) (hQpos i) (L i).metric)
            (x i) (R + r),
          metricScalarAt (L i).metric y ≤ 2 * (Amax * (A i).flow.scalar (time i) (x i).val)) ∧
        ∃ first : Fin ((H i).eventCount + 1),
          (∀ y ∈ riemannianClosedBallOf
            (scaleMetric ((A i).flow.scalar (time i) (x i).val) (hQpos i) (L i).metric)
              (x i) (R + r),
            Nonempty (BackwardPointTrace (H i).toHistory first (Fin.last (H i).eventCount)
              (Fin.le_last first) y.val)) ∧
          (H i).time first ≤ time i - θ / (A i).flow.scalar (time i) (x i).val := by
    intro R hR hRrho
    let r := (rho - R) / 2
    have hr : 0 < r := half_pos (sub_pos.mpr hRrho)
    have hRr : R + r < rho := by dsimp [r]; linarith
    obtain ⟨B, hB⟩ := hinner (R + r) (by positivity) hRr
    let Amax := max 1 B
    have hAmax : 1 ≤ Amax := le_max_left _ _
    have hBA : B ≤ Amax := le_max_right _ _
    obtain ⟨B', hB'⟩ := hinner (R + r + r / 2) (by positivity) (by dsimp only [r]; linarith)
    obtain ⟨θ₀, hθ₀, htr⟩ := htrace (R + r) (r / 2) (max 1 B') (by positivity) (by positivity)
      (hB'.mono fun i hi y hy => by
        have hb := (div_le_iff₀ (hQpos i)).mp (hi.2 y hy)
        nlinarith [mul_le_mul_of_nonneg_right (le_max_right 1 B') (hQpos i).le])
    let θ := min θ₀ (1 / (6 * ((Ctime : ℝ) + 1) * Amax))
    have hθ : 0 < θ := lt_min hθ₀ (by positivity)
    have hθθ₀ : θ ≤ θ₀ := min_le_left _ _
    have hθbudget : θ * (6 * ((Ctime : ℝ) + 1) * Amax) ≤ 1 :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    have hbudget : 6 * (Ctime : ℝ) * (Amax * θ) ≤ 1 := by
      have hC : (0 : ℝ) ≤ Ctime := Ctime.coe_nonneg
      nlinarith [mul_nonneg (zero_le_one.trans hAmax) hθ.le]
    refine ⟨r, Amax, θ, hr, hRr, hAmax, hθ, hbudget, ?_⟩
    filter_upwards [hB, htr] with i hi hti
    obtain ⟨first, hfirst, htrf⟩ := hti
    refine ⟨hi.1, ?_, first, htrf, ?_⟩
    · intro y hy
      have hb := (div_le_iff₀ (hQpos i)).mp (hi.2 y hy)
      have hQi := hQpos i
      nlinarith [mul_le_mul_of_nonneg_right hBA hQi.le]
    · have hdiv : θ / (A i).flow.scalar (time i) (x i).val ≤
          θ₀ / (A i).flow.scalar (time i) (x i).val :=
        div_le_div_of_nonneg_right hθθ₀ (hQpos i).le
      linarith
  have hbufR : ∀ R : ℝ, 0 < R → R < rho → ∃ r Amax θ : ℝ,
      0 < r ∧ R + r < rho ∧ 1 ≤ Amax ∧ 0 < θ ∧ 6 * Ctime * (Amax * θ) ≤ 1 ∧
      ∀ᶠ i in atTop,
        IsCompact (riemannianClosedBallOf
          (scaleMetric ((A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val)
            (hQpos (ind i)) (L (ind i)).metric) (x (ind i)) (R + r)) ∧
        (∀ y ∈ riemannianClosedBallOf
          (scaleMetric ((A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val)
            (hQpos (ind i)) (L (ind i)).metric) (x (ind i)) (R + r),
          metricScalarAt (L (ind i)).metric y ≤
            2 * (Amax * (A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val)) ∧
        ∃ first : Fin ((H (ind i)).eventCount + 1),
          (∀ y ∈ riemannianClosedBallOf
            (scaleMetric ((A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val)
              (hQpos (ind i)) (L (ind i)).metric) (x (ind i)) (R + r),
            Nonempty (BackwardPointTrace (H (ind i)).toHistory first
              (Fin.last (H (ind i)).eventCount) (Fin.le_last first) y.val)) ∧
          (H (ind i)).time first ≤
            time (ind i) - θ / (A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val := by
    intro R hR hRrho
    obtain ⟨r, Amax, θ, hrr, hrrho, hAmax, hθ, hbudget, hb⟩ := hbuf R hR hRrho
    exact ⟨r, Amax, θ, hrr, hrrho, hAmax, hθ, hbudget, hind.tendsto_atTop.eventually hb⟩
  have hvol : ∀ r R : ℝ, 0 < r → r < R → R < rho → ∀ J : ℝ, 0 ≤ J →
      ∃ a κ' : ℝ, 0 < a ∧ 0 < κ' ∧ r + a ≤ R ∧ a ^ 4 * J ^ 2 ≤ 1 ∧
      ∀ᶠ n in atTop, ∀ y ∈ riemannianClosedBallOf
        (scaleMetric ((A (ind n)).flow.scalar (time (ind n)) (x (ind n)).val)
          (zero_lt_one.trans_le (hQ (ind n))) (L (ind n)).metric) (x (ind n)) r,
        ENNReal.ofReal (κ' * a ^ 3) ≤ riemannianVolumeMeasure ThreeModel
          (G (ind n)).terminalRegularOpen
          (scaleMetric ((A (ind n)).flow.scalar (time (ind n)) (x (ind n)).val)
            (zero_lt_one.trans_le (hQ (ind n))) (L (ind n)).metric)
          (riemannianBallOf (scaleMetric ((A (ind n)).flow.scalar (time (ind n)) (x (ind n)).val)
            (zero_lt_one.trans_le (hQ (ind n))) (L (ind n)).metric) y a) :=
    hvol_of_buffer_centre_O23 Phi hPhi (fun i => H (ind i)) (fun i => time (ind i))
      (fun i => G (ind i)) (fun i => L (ind i)) (fun i => hinit (ind i)) (fun i => x (ind i))
      (fun i => q (ind i)) (fun i => (A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val)
      (fun i => hq (ind i)) (fun i => hqQ (ind i)) (fun i => hQ (ind i))
      (fun i j => hderiv (ind i) j) (fun i => hfinal (ind i)) (fun i j => hpinch (ind i) j)
      (fun i => hpinchFinal (ind i)) hrho hbufR hκ ha₀ (Eventually.of_forall fun i => hvx (ind i))
  refine ⟨rho, hrho, ind, hind, z, ?_⟩
  dsimp only
  have hconv :=
    ObservedHistory.exists_terminal_pointed_convergence_of_buffered_backward_traces
      Phi hPhi (fun i => (H (ind i)).toHistory) (fun i => Fin.last (H (ind i)).eventCount)
      (fun i => time (ind i)) (fun i => G (ind i)) (fun i => L (ind i))
      (fun i => hinit (ind i)) (fun i => x (ind i)) (fun i => q (ind i))
      (fun i => (A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val) (fun i => hq (ind i))
      (fun i => hqQ (ind i)) (fun i => hQ (ind i))
      (fun i j _ => hderiv (ind i) j) (fun i => hfinal (ind i))
      (fun i j _ => hpinch (ind i) j) (fun i => hpinchFinal (ind i)) hrho (by
        intro R hR hRrho
        obtain ⟨r, Amax, θ, hrr, hrrho, hAmax, hθ, hbudget, hb⟩ := hbufR R hR hRrho
        refine ⟨r, Amax, θ, hrr, hrrho, hAmax, hθ, hbudget, ?_⟩
        filter_upwards [hb] with i hi
        obtain ⟨first, htrace, hstart⟩ := hi.2.2
        exact ⟨hi.1, hi.2.1, first, Fin.le_last first, htrace, hstart⟩) hvol
  dsimp only at hconv
  obtain ⟨f, hf, r, hr, hrlim, P, F, M, hcanonicalDomain, hradial, hcompact, hcapture,
      hmetric⟩ := hconv
  have hscalarOne : metricScalarAt P.metric P.basepoint = 1 :=
    Perelman.KappaSolutions.pointedScalar_base_eq_of_metricCG_canonical_domains M
      hcanonicalDomain (by
        intro n
        change metricScalarAt (scaleMetric
          ((A (ind (f n))).flow.scalar (time (ind (f n))) (x (ind (f n))).val)
          (hQpos (ind (f n))) (L (ind (f n))).metric) (x (ind (f n))) = 1
        rw [metricScalarAt_scaleMetric, endpoint_scalar_eq_limit_O23, inv_mul_cancel₀]
        exact (hQpos (ind (f n))).ne')
  exact ⟨f, hf, r, hr, hrlim, P, F, M, hscalarOne, hcanonicalDomain, hradial, hcompact,
    hcapture, hmetric, fun n => hfinite (f n), hdist.comp hf.tendsto_atTop,
    hscalarEscape.comp hf.tendsto_atTop⟩

/-- K-can form of `exists_nonnegative_local_flow_with_comparison_local_O3` (centre volume `hvx`). -/
theorem exists_nonnegative_local_flow_with_comparison_kcan_O23
    (H : ℕ → RetainedCoreHistory.{u}) (s : ℕ → ℝ)
    (A : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).ClosedSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n))
    (hinit : ∀ n, (A n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (Ctime : ℝ≥0) (q : ℕ → ℝ) (hq : ∀ n, 0 < q n)
    (hderiv : ∀ n (j : Fin (H n).eventCount) (y : ((H n).stage j.castSucc).Carrier),
      ∀ t ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ),
        q n < ((H n).toHistory.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => ((H n).toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * ((H n).toHistory.event j).incoming.flow.scalar t y ^ 2)
    (hfinal : ∀ n y, ∀ t ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (s n),
      q n < (A n).flow.scalar t y →
      |derivWithin (fun v => (A n).flow.scalar v y) (Iic t) t| ≤
        Ctime * (A n).flow.scalar t y ^ 2)
    (x : ∀ n, ((A n).restrictIncoming le_rfl (A n).lt le_rfl).terminalRegularOpen)
    (Q : ℕ → ℝ) (hQ : ∀ n, 1 ≤ Q n) (hqQ : ∀ n, q n ≤ Q n)
    (hQlim : Tendsto Q atTop atTop)
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ n j, Perelman.PhiAlmostNonnegative ((H n).toHistory.event j).incoming.flow
      (Ico ((H n).time j.castSucc) ((H n).time j.succ)) Phi)
    (hpinchFinal : ∀ n, Perelman.PhiAlmostNonnegative
      ((A n).restrictIncoming le_rfl (A n).lt le_rfl).flow
      (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) Phi)
    (hbuffer : ∀ R : ℝ, 0 < R → R < 1 → ∃ r Amax θ : ℝ,
      0 < r ∧ R + r < 1 ∧ 1 ≤ Amax ∧ 0 < θ ∧ 6 * Ctime * (Amax * θ) ≤ 1 ∧
      ∀ᶠ n in atTop,
        IsCompact (riemannianClosedBallOf (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n))
          ((A n).endpointTerminalLimitMetric ((H n).stage (Fin.last (H n).eventCount))).metric)
          (x n) (R + r)) ∧
        (∀ z ∈ riemannianClosedBallOf (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n))
          ((A n).endpointTerminalLimitMetric ((H n).stage (Fin.last (H n).eventCount))).metric)
          (x n) (R + r), metricScalarAt
            ((A n).endpointTerminalLimitMetric ((H n).stage (Fin.last (H n).eventCount))).metric
            z ≤ 2 * (Amax * Q n)) ∧
        ∃ first : Fin ((H n).eventCount + 1),
          (∀ z ∈ riemannianClosedBallOf (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n))
            ((A n).endpointTerminalLimitMetric ((H n).stage (Fin.last (H n).eventCount))).metric)
            (x n) (R + r), Nonempty (BackwardPointTrace (H n).toHistory first
              (Fin.last (H n).eventCount) (Fin.le_last first) z.val)) ∧
          (H n).time first ≤ s n - θ / Q n)
    (hs : ∀ n, (H n).horizon < s n)
    (hscale : ∀ n, Q n = metricScalarAt
      ((A n).endpointTerminalLimitMetric ((H n).stage (Fin.last (H n).eventCount))).metric (x n))
    {κ a₀ : ℝ} (hκ : 0 < κ) (ha₀ : 0 < a₀)
    (hvx : ∀ᶠ n in atTop, ∀ b : ℝ, 0 < b → b ≤ a₀ →
      ENNReal.ofReal (κ * b ^ 3) ≤
        riemannianVolumeMeasure ThreeModel
          ((A n).restrictIncoming le_rfl (A n).lt le_rfl).terminalRegularOpen
          (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n))
            ((A n).endpointTerminalLimitMetric ((H n).stage (Fin.last (H n).eventCount))).metric)
          (riemannianBallOf (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n))
            ((A n).endpointTerminalLimitMetric ((H n).stage (Fin.last (H n).eventCount))).metric) (x n) b))
    {N : Type v} [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold ThreeModel ∞ N]
    [T2Space N] (Hn : ℕ → SmoothRiemannianMetric ThreeModel N) (xN : ℕ → N)
    (B : ∀ n, PartialDiffeomorph ThreeModel ThreeModel N
      ((A n).restrictIncoming le_rfl (A n).lt le_rfl).terminalRegularOpen ∞)
    {R : ℝ} (hR : 0 < R)
    (hBsource : ∀ n, riemannianClosedBallOf (Hn n) (xN n) R ⊆ (B n).source)
    (hBbase : ∀ n, B n (xN n) = x n)
    (hcapture : ∀ n, riemannianClosedBallOf (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n))
      ((A n).endpointTerminalLimitMetric ((H n).stage (Fin.last (H n).eventCount))).metric)
      (x n) (R / 4) ⊆ (B n) '' riemannianClosedBallOf (Hn n) (xN n) R)
    (hBconv : ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
      ∀ y ∈ riemannianClosedBallOf (Hn n) (xN n) R, ∀ v : TangentSpace ThreeModel y,
        (1 - eta) * (Hn n).inner y v v ≤ (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n))
          ((A n).endpointTerminalLimitMetric
            ((H n).stage (Fin.last (H n).eventCount))).metric).inner
            (B n y) (mfderiv ThreeModel ThreeModel (B n) y v)
            (mfderiv ThreeModel ThreeModel (B n) y v) ∧
        (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n))
          ((A n).endpointTerminalLimitMetric
            ((H n).stage (Fin.last (H n).eventCount))).metric).inner
            (B n y) (mfderiv ThreeModel ThreeModel (B n) y v)
            (mfderiv ThreeModel ThreeModel (B n) y v) ≤ (1 + eta) * (Hn n).inner y v v) :
    ∃ (j : ℕ → ℕ) (_ : StrictMono j) (P₂ : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
      (V : TopologicalSpace.Opens P₂.M)
      (hp : P₂.basepoint ∈ V) (_ : PathConnectedSpace V) (tau : ℝ) (htau : 0 < tau)
      (g : ℝ → SmoothRiemannianMetric ThreeModel V),
      g 0 = P₂.metric.restrictOpen V ∧ metricScalarAt P₂.metric P₂.basepoint = 1 ∧
      IsSolutionOn ({ base.metric := g } : SolutionOn (I := ThreeModel) (M := V)
        (RealTimeInterval.closed (-tau) 0 (by linarith))) ∧
      (∀ t ∈ Icc (-tau) 0, ∀ y : V, metricAlgebraicCurvatureTensorAt (g t) y ∈
        algebraicCurvatureOperatorNonnegativeCone (I := ThreeModel)) ∧
      ∃ C : ℕ → PartialDiffeomorph ThreeModel ThreeModel V N ∞,
        (∀ n, C n ⟨P₂.basepoint, hp⟩ = xN (j n)) ∧
        ∃ r : ℝ, 0 < r ∧ IsCompact (riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r) ∧
        (∀ᶠ n in atTop, riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r ⊆ (C n).source ∧
          riemannianClosedBallOf (Hn (j n)) (xN (j n)) (r / 4) ⊆
            (C n) '' riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r) ∧
        ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
          ∀ a ∈ riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r,
          ∀ b ∈ riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r,
            |(riemannianEDistOf (Hn (j n)) (C n a) (C n b)).toReal -
              (riemannianEDistOf (g 0) a b).toReal| < eta := by
  let G := fun n => (A n).restrictIncoming le_rfl (A n).lt le_rfl
  let L := fun n => (A n).endpointTerminalLimitMetric ((H n).stage (Fin.last (H n).eventCount))
  have hconv := exists_normalized_terminal_pointed_convergence_kcan_O23
    Phi hPhi H s G L hinit hs x q Q hscale hq hqQ hQ hderiv hfinal hpinch hpinchFinal one_pos
    hbuffer hκ ha₀ hvx
  dsimp only at hconv
  obtain ⟨f₂, hf₂, _, _, _, P₂, F₂, M, hbase₂, hcanonical, hradial, hcompact, _, _⟩ := hconv
  let F := PointedRiemannianConvergenceMaps.liftTargetOpen
    (S := { obj := fun n =>
          { M := (G n).terminalRegularOpen
            basepoint := x n
            metric := scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric } })
    (fun i => connectedComponentOpen (I := ThreeModel) (x i))
    (fun i => (mem_connectedComponent : x i ∈ connectedComponentOpen (I := ThreeModel) (x i))) F₂
  let V : TopologicalSpace.Opens P₂.M := ⟨riemannianBallOf P₂.metric P₂.basepoint (1 / 2),
    isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist _ _) continuous_const⟩
  have hp : P₂.basepoint ∈ V := by
    change riemannianEDistOf P₂.metric P₂.basepoint P₂.basepoint < ENNReal.ofReal (1 / 2)
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (by norm_num)
  have hpath : PathConnectedSpace V := isPathConnected_iff_pathConnectedSpace.mp
    (isPathConnected_riemannianBallOf P₂.metric P₂.basepoint (by norm_num))
  have hVc : IsCompact (closure (V : Set P₂.M)) := by
    apply (hcompact (1 / 2) (by norm_num) (by norm_num)).of_isClosed_subset isClosed_closure
    refine closure_minimal (fun z (hz : riemannianEDistOf P₂.metric P₂.basepoint z <
      ENNReal.ofReal (1 / 2)) => (le_of_lt hz : riemannianEDistOf P₂.metric P₂.basepoint z ≤
        ENNReal.ofReal (1 / 2))) ?_
    exact isClosed_le (Geometry.Riemannian.continuous_riemannianEDist _ _) continuous_const
  have hupper : ∀ K : Set P₂.M, IsCompact K → ∀ C : ℝ, 1 < C → ∀ᶠ i in atTop,
      ∀ z ∈ K, ∀ v : TangentSpace ThreeModel z,
        (scaleMetric (Q (f₂ i)) (zero_lt_one.trans_le (hQ (f₂ i)))
          (L (f₂ i)).metric).inner (F.map i z)
          (mfderiv ThreeModel ThreeModel (F.map i) z v)
          (mfderiv ThreeModel ThreeModel (F.map i) z v) ≤ C ^ 2 * P₂.metric.inner z v v := by
    intro K hK C hC
    have hconv : metricSourceConvergesOn F
        (CanonicalMetricCompactness.canonicalSourceData F) K 0 := by
      have heq : M.domain = CanonicalMetricCompactness.canonicalSourceData F := funext hcanonical
      rw [← heq]
      exact M.converges K hK 0
    filter_upwards [pointed_metric_eventually_quadratic_bounds hK hconv
      (by nlinarith : 0 < C ^ 2 - 1)] with i hi
    intro z hz v
    simpa only [add_sub_cancel] using (hi.2 z hz v).2
  have hbuffer' : ∀ R : ℝ, 0 < R → R < 1 → ∃ r Amax θ : ℝ,
      0 < r ∧ R + r < 1 ∧ 1 ≤ Amax ∧ 0 < θ ∧ 6 * Ctime * (Amax * θ) ≤ 1 ∧ ∀ᶠ i in atTop,
        IsCompact (riemannianClosedBallOf
          (scaleMetric (Q (f₂ i)) (zero_lt_one.trans_le (hQ (f₂ i))) (L (f₂ i)).metric)
          (x (f₂ i)) (R + r)) ∧
        (∀ z ∈ riemannianClosedBallOf
          (scaleMetric (Q (f₂ i)) (zero_lt_one.trans_le (hQ (f₂ i))) (L (f₂ i)).metric)
          (x (f₂ i)) (R + r), metricScalarAt (L (f₂ i)).metric z ≤ 2 * (Amax * Q (f₂ i))) ∧
        ∃ first : Fin ((H (f₂ i)).eventCount + 1),
          ∃ hle : first ≤ Fin.last (H (f₂ i)).eventCount,
          (∀ z ∈ riemannianClosedBallOf
            (scaleMetric (Q (f₂ i)) (zero_lt_one.trans_le (hQ (f₂ i))) (L (f₂ i)).metric)
            (x (f₂ i)) (R + r),
            Nonempty (BackwardPointTrace (H (f₂ i)).toHistory first
              (Fin.last (H (f₂ i)).eventCount) hle z.val)) ∧
          (H (f₂ i)).time first ≤ s (f₂ i) - θ / Q (f₂ i) := by
    intro R hR hR1
    obtain ⟨r, Amax, θ, hr, hRr, hA, hθ, hbud, hev⟩ := hbuffer R hR hR1
    refine ⟨r, Amax, θ, hr, hRr, hA, hθ, hbud, ?_⟩
    filter_upwards [hf₂.tendsto_atTop.eventually hev] with i hi
    obtain ⟨first, htr, hst⟩ := hi.2.2
    exact ⟨hi.1, hi.2.1, first, Fin.le_last first, htr, hst⟩
  open ObservedHistory in
  obtain ⟨Rr, rr, Amax, θ, hθ, Bd, _, _, _, _, _, hBd, hev⟩ :=
    exists_eventually_historical_solution_with_curvature_bounds_of_pointed_convergence
      (fun n => (H n).toHistory) (fun n => Fin.last (H n).eventCount) G x L hinit q Q hq hqQ hQ F
      one_pos hradial hcompact hupper Phi hPhi (fun n j _ => hderiv n j) hfinal
      (fun n j _ => hpinch n j) hpinchFinal hbuffer' V hVc
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  choose first hle Ψ hΨ hFv gflow S hsource _ _ _ hstart _ _ hS hzero hmetric hslabs hlast _
    hcurv using fun j : ℕ => hN (j + N) (Nat.le_add_left N j)
  have hsh : StrictMono (fun j : ℕ => j + N) := fun a b h => Nat.add_lt_add_right h N
  let F₃ := F.compSubseq (fun j => j + N) hsh
  let M₃ := M.compSubseq (fun j => j + N) hsh
  have hcan₃ (j : ℕ) : M₃.domain j = CanonicalMetricCompactness.canonicalSourceData F₃ j := by
    change (M.domain (j + N)).compSubseq _ hsh j = _
    rw [hcanonical (j + N)]
    rfl
  have hterm : ∀ j (z : V) (v w : TangentSpace ThreeModel z),
      ((S j).base.metric 0).inner z v w =
        (scaleMetric (Q (f₂ (j + N))) (zero_lt_one.trans_le (hQ (f₂ (j + N))))
          (L (f₂ (j + N))).metric).inner (F₃.partialDiffeomorph j z)
          (mfderiv ThreeModel ThreeModel (F₃.partialDiffeomorph j) z v)
          (mfderiv ThreeModel ThreeModel (F₃.partialDiffeomorph j) z w) := by
    intro j z v w
    refine (congrArg (fun g : SmoothRiemannianMetric ThreeModel V => g.inner z v w)
      (hzero j)).trans ?_
    exact localPullMetric_restrict_inner_O23 _ (F.partialDiffeomorph (j + N)) V (hFv j) z v w
  have hcurv' : ∀ K : Set V, IsCompact K → ∀ m : ℕ, ∃ B' : ℝ, 0 ≤ B' ∧ ∀ᶠ j in atTop,
      ∀ t ∈ Icc (-(θ / 2)) 0, ∀ z ∈ K, curvDerivNorm m ((S j).base.metric t) z ≤ B' :=
    fun _ _ m => ⟨Bd m, hBd m, Eventually.of_forall fun j t ht z _ => hcurv j m t ht z⟩
  have hpa (j : ℕ) : Perelman.PhiAlmostNonnegative (S j) (Icc (-θ) 0)
      (Perelman.rescalePinchingFunction (Q (f₂ (j + N))) Phi) :=
    ObservedHistory.phiAlmostNonnegative_parabolic_backwardSurvivorIncomingFootprint_localPullback
      (H (f₂ (j + N))).toHistory (first j) (Fin.last (H (f₂ (j + N))).eventCount)
      (hle j) (G (f₂ (j + N))) (L (f₂ (j + N)))
      (riemannianClosedBallOf (scaleMetric (Q (f₂ (j + N))) (zero_lt_one.trans_le (hQ _))
        (L (f₂ (j + N))).metric) (x (f₂ (j + N))) (Rr + rr))
      (gflow j) (hslabs j) (hlast j) hPhi.contDiff.continuous
      (fun jj _ _ => hpinch (f₂ (j + N)) jj) (hpinchFinal (f₂ (j + N)))
      (zero_lt_one.trans_le (hQ (f₂ (j + N)))) (hstart j) (Ψ j) (hΨ j) (S j)
      (fun v _ => hmetric j v)
  have hpinching : ∀ t ∈ Icc (-(θ / 2)) 0, ∀ᶠ j in atTop, ∀ z : V,
      curvatureOperatorLowerBoundAt ((S j).base.metric t) z
        (metricAlgebraicCurvatureTensorAt ((S j).base.metric t) z)
        (Perelman.rescalePinchingFunction (Q (f₂ (j + N))) Phi
          (metricScalarAt ((S j).base.metric t) z)) := by
    intro t ht
    exact Eventually.of_forall fun j z => hpa j t ⟨by linarith [ht.1], ht.2⟩ z
  have hBconv' : ∀ eta : ℝ, 0 < eta → ∀ᶠ j in atTop,
      ∀ y ∈ riemannianClosedBallOf (Hn (f₂ (j + N))) (xN (f₂ (j + N))) R,
      ∀ v : TangentSpace ThreeModel y,
        (1 - eta) * (Hn (f₂ (j + N))).inner y v v ≤
          (scaleMetric (Q (f₂ (j + N))) (zero_lt_one.trans_le (hQ (f₂ (j + N))))
            (L (f₂ (j + N))).metric).inner (B (f₂ (j + N)) y)
            (mfderiv ThreeModel ThreeModel (B (f₂ (j + N))) y v)
            (mfderiv ThreeModel ThreeModel (B (f₂ (j + N))) y v) ∧
        (scaleMetric (Q (f₂ (j + N))) (zero_lt_one.trans_le (hQ (f₂ (j + N))))
          (L (f₂ (j + N))).metric).inner (B (f₂ (j + N)) y)
          (mfderiv ThreeModel ThreeModel (B (f₂ (j + N))) y v)
          (mfderiv ThreeModel ThreeModel (B (f₂ (j + N))) y v) ≤
            (1 + eta) * (Hn (f₂ (j + N))).inner y v v :=
    fun eta heta => (hf₂.comp hsh).tendsto_atTop.eventually (hBconv eta heta)
  obtain ⟨_, _, g, hgb, hsol, hnonneg, _, r, hr, hcpt, hcenter, hcap, hdist⟩ :=
    DifferentialGeometry.PDE.RicciFlow.exists_nonnegative_local_flow_with_end_comparison
      F₃ M₃ hcan₃ V hp (fun j => hsource j) S hS (a := -(θ / 2)) (b := 0) (by linarith)
      (fun t ht => ⟨by linarith [ht.1], ht.2⟩) (fun t ht => ⟨by linarith [ht.1], ht.2⟩)
      hterm hcurv' hPhi (fun j => Q (f₂ (j + N))) (fun j => zero_lt_one.trans_le (hQ _))
      (hQlim.comp (hf₂.comp hsh).tendsto_atTop) hpinching
      (fun j => Hn (f₂ (j + N))) (fun j => xN (f₂ (j + N))) (fun j => B (f₂ (j + N))) hR
      (fun j => hBsource _) (fun j => hBbase _) (fun j => hcapture _) hBconv'
  exact ⟨fun j => f₂ (j + N), hf₂.comp hsh, P₂, V, hp, hpath, θ / 2, by positivity, g, hgb,
    hbase₂, hsol, hnonneg, _, hcenter, r, hr, hcpt, hcap, hdist⟩

end GC.LongTime.Ch12
