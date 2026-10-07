import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapWindows
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FinitePresentedStaticCap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FullMetricModels
import DifferentialGeometry.Geometry.Neck.OrderReduction

/-!
# Linked canonical cap windows (C12X, S10 step 3 helper)

`hasLinkedCanonicalWindow_C12X` is `hasCanonicalWindow` together with the link between the
insertion datum `(δ', k)` and the static neck: `δ' ≤ S.delta ∧ 2 * ⌊δ'⁻¹⌋₊ ≤ k` (body verbatim
as ch11 `linkedCanonicalWindow_C11E`).  The Horn producer gets it from its high-order original
neck datum:

* `normalizedDatum.exists_highOrder_of_heq_lowerOrder_C12X`: a datum that is (HEq to) a lowered
  datum has a same-map datum of the high order;
* `normalizedDatum.offsetPoint_congr_C12X`, `recenteringMap_congr_C12X`: offset point and
  recentering map only depend on the datum map;
* `CanonicalStaticInsertionWitness.exists_transfer_C12X`: a canonical witness moves to a datum with
  the same centre, precision, map and side and larger order, with the same window metric;
* `exists_linked_upgrade_C12X`: the Horn situation in one step;
* `hasLinkedCanonicalWindow_of_finite_metric_stage_C12X`: sibling of the Horn producer's private
  `hasCanonicalWindow_of_finite_metric_stage` with the upgraded witness family.
-/

set_option autoImplicit false
noncomputable section

open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Manifold
open DifferentialGeometry.PDE.RicciFlow.StandardCap DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Neck.normalizedDatum

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {δ : ℝ}

/-- A datum is the lowering of any higher-order datum with the same map and side. -/
theorem eq_lowerOrder_of_map_eq_C12X {x₀ : M} {j k : ℕ} (d : normalizedDatum g x₀ δ j)
    (dH : normalizedDatum g x₀ δ k) (hjk : j ≤ k) (hmap : d.map = dH.map)
    (hside : d.retainedSide = dH.retainedSide) : d = dH.lowerOrder hjk := by
  cases d
  cases dH
  cases hmap
  cases hside
  rfl

/-- The offset point only depends on the datum map. -/
theorem offsetPoint_congr_C12X {x₀ x₀' : M} {j k : ℕ} (d : normalizedDatum g x₀ δ j)
    (d' : normalizedDatum g x₀' δ k) (hmap : d.map = d'.map) {σ : ℝ} (hσ : σ ^ 2 = 1) :
    d.offsetPoint hσ = d'.offsetPoint hσ := by
  unfold offsetPoint
  rw [hmap]

/-- The recentering map only depends on the datum map. -/
theorem recenteringMap_congr_C12X {x₀ x₀' : M} {j k : ℕ} (d : normalizedDatum g x₀ δ j)
    (d' : normalizedDatum g x₀' δ k) (hmap : d.map = d'.map) {ε σ : ℝ} (hσ : σ ^ 2 = 1)
    (hfit : ε⁻¹ + 1 ≤ δ⁻¹) :
    d.recenteringMap hσ hfit = d'.recenteringMap hσ hfit := by
  unfold recenteringMap
  rw [hmap]

/-- A datum `HEq` to the lowering of a datum `Dh` of order `K` (centred at an equal point) has a
datum of order `K` with the same map at its own centre. -/
theorem exists_highOrder_of_heq_lowerOrder_C12X {x x' : M} {j K : ℕ} (hx : x = x')
    (Dh : normalizedDatum g x δ K) (hjK : j ≤ K) (d : normalizedDatum g x' δ j)
    (hd : HEq d (Dh.lowerOrder hjK)) :
    ∃ dH : normalizedDatum g x' δ K, dH.map = d.map ∧ dH.retainedSide = d.retainedSide := by
  subst hx
  cases eq_of_heq hd
  exact ⟨Dh, rfl, rfl⟩

end DifferentialGeometry.Geometry.Neck.normalizedDatum

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {δ : ℝ}

/-- A canonical witness on `dH.lowerOrder hjk` gives one on `dH` with the same window metric. -/
theorem exists_raiseOrder_C12X {x₀ : M} {j k : ℕ} (dH : normalizedDatum g x₀ δ k) (hjk : j ≤ k)
    {A : ℝ} {hA : 0 < A} {D : ℝ} (hD : 0 < D) {m : ℕ} {ε : ℝ}
    (w : CanonicalStaticInsertionWitness (dH.lowerOrder hjk) A hA D m ε) :
    ∃ w' : CanonicalStaticInsertionWitness dH A hA D m ε, w'.windowMetric = w.windowMetric := by
  have htip : collapseTip A ∈ Ioo (-δ⁻¹) (-2 * A - transitionEnd) :=
    w.properties.profileTip_eq ▸ w.properties.profileTip_location
  have hclose := w.properties.window_close
  rw [w.properties.outMetric_eq] at hclose
  let w' := canonicalStaticInsertionWitness dH A hA D hD m ε w.properties.cut_fit
    w.properties.window_fit htip (by
      convert hclose using 3
      unfold modelWindowPullback
      congr 1
      exact w.properties.windowMap_eq.symm)
  refine ⟨w', ?_⟩
  unfold windowMetric
  congr 1
  · rw [w'.properties.outMetric_eq, w.properties.outMetric_eq]
    rfl
  · rw [w'.properties.windowMap_eq, w.properties.windowMap_eq]

/-- Transfer of a canonical witness to a datum with an equal centre, the same precision, map and
side and a larger order, keeping the window metric. -/
theorem exists_transfer_C12X {x₀ x₀' : M} {j k : ℕ} (d : normalizedDatum g x₀ δ j)
    (d' : normalizedDatum g x₀' δ k) (hx : x₀ = x₀') (hjk : j ≤ k) (hmap : d.map = d'.map)
    (hside : d.retainedSide = d'.retainedSide) {A : ℝ} {hA : 0 < A} {D : ℝ} (hD : 0 < D)
    {m : ℕ} {ε : ℝ} (w : CanonicalStaticInsertionWitness d A hA D m ε) :
    ∃ w' : CanonicalStaticInsertionWitness d' A hA D m ε, w'.windowMetric = w.windowMetric := by
  subst hx
  have he := normalizedDatum.eq_lowerOrder_of_map_eq_C12X d d' hjk hmap hside
  subst he
  exact exists_raiseOrder_C12X d' hjk hD w

end DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M}

/-- The Horn situation: `d₀` (order `j₀`) carries a recentered cap datum `dCap` (order `k`) with
witness `w`; `dH` (order `K ≥ k`) has the same map as `d₀`, and a recentering `dR` of `dH` with the
same constant exists.  Then there is a cap datum of order `K` at the same centre and precision
whose canonical witness has the same window metric as `w`. -/
theorem exists_linked_upgrade_C12X {x : M} {δ c : ℝ} {j₀ k K : ℕ}
    (d₀ : normalizedDatum g x δ j₀) (dH : normalizedDatum g x δ K) (hH : dH.map = d₀.map)
    {σ : ℝ} (hσ : σ ^ 2 = 1) (hfit : (c * δ)⁻¹ + 1 ≤ δ⁻¹)
    (dCap : normalizedDatum g (d₀.offsetPoint hσ) (c * δ) k)
    (hcap : dCap.map = d₀.recenteringMap hσ hfit) (hside : dCap.retainedSide = true) (hkK : k ≤ K)
    (dR : normalizedDatum g (dH.offsetPoint hσ) (c * δ) K)
    (hR : dR.map = dH.recenteringMap hσ hfit) (hRside : dR.retainedSide = true)
    {A : ℝ} {hA : 0 < A} {D : ℝ} (hD : 0 < D) {m : ℕ} {ε : ℝ}
    (w : CanonicalStaticInsertionWitness dCap A hA D m ε) :
    ∃ (dU : normalizedDatum g (d₀.offsetPoint hσ) (c * δ) K)
      (wU : CanonicalStaticInsertionWitness dU A hA D m ε), wU.windowMetric = w.windowMetric := by
  have hx : dH.offsetPoint hσ = d₀.offsetPoint hσ :=
    normalizedDatum.offsetPoint_congr_C12X dH d₀ hH hσ
  have hmap : dCap.map = dR.map := by
    rw [hcap, hR, normalizedDatum.recenteringMap_congr_C12X dH d₀ hH hσ hfit]
  obtain ⟨wU, hwU⟩ := CanonicalStaticInsertionWitness.exists_transfer_C12X dCap dR hx.symm hkK
    hmap (hside.trans hRside.symm) hD w
  clear hmap hR hRside
  revert dR
  rw [hx]
  intro dR wU hwU
  exact ⟨dR, wU, hwU⟩

end DifferentialGeometry.PDE.RicciFlow.StandardCap

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

/-- `2 ⌊(c δ)⁻¹⌋₊ ≤ K` from the original-neck order bound `2 ⌊δ⁻¹⌋₊ + 4 ≤ K` when `1 ≤ c`. -/
theorem two_floor_inv_mul_le_C12X {c δ : ℝ} {K : ℕ} (hc : 1 ≤ c) (hδ : 0 < δ)
    (hK : 2 * ⌊δ⁻¹⌋₊ + 4 ≤ K) : 2 * ⌊(c * δ)⁻¹⌋₊ ≤ K := by
  have hle : (c * δ)⁻¹ ≤ δ⁻¹ :=
    inv_anti₀ hδ (le_mul_of_one_le_left hδ.le hc)
  have hf := Nat.floor_mono hle
  omega

namespace MetricCutCapEvent.PresentedStaticCap

universe u

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
  {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

/-- `hasCanonicalWindow` plus the link `δ' ≤ S.delta ∧ 2 * ⌊δ'⁻¹⌋₊ ≤ k` between the insertion
datum and the static neck (body verbatim as ch11 `linkedCanonicalWindow_C11E`). -/
def hasLinkedCanonicalWindow_C12X (S : E.PresentedStaticCap fixed D m ε b) : Prop :=
  ∃ (x₀ : E.incoming.terminalRegularOpen) (δ' : ℝ) (k : ℕ)
    (d : normalizedDatum E.terminal.metric x₀ δ' k)
    (w : StandardCap.CanonicalStaticInsertionWitness d fixed.collarLength fixed.collar_pos D m ε),
    metricScalarAt E.terminal.metric x₀ = S.neck.scale ∧
    (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
      S.neck.scale * E.outputMetric.inner (S.window x)
        (mfderiv ThreeModel ThreeModel S.window x v)
        (mfderiv ThreeModel ThreeModel S.window x z)) ∧
    (∀ z : ThreeBall, ∃ x : standardCapWindow D,
      ‖x.val‖ ≤ StandardCap.transitionEnd ∧
      S.window x = S.inclusion (S.witness.cap z)) ∧
    δ' ≤ S.delta ∧ 2 * ⌊δ'⁻¹⌋₊ ≤ k

theorem hasLinkedCanonicalWindow_C12X.hasCanonicalWindow {S : E.PresentedStaticCap fixed D m ε b}
    (h : S.hasLinkedCanonicalWindow_C12X) : S.hasCanonicalWindow := by
  obtain ⟨x₀, δ', k, d, w, h1, h2, h3, -, -⟩ := h
  exact ⟨x₀, δ', k, d, w, h1, h2, h3⟩

/-- Sibling of the Horn producer's `hasCanonicalWindow_of_terminal_window`, with the link. -/
theorem hasLinkedCanonicalWindow_of_terminal_window_C12X (S : E.PresentedStaticCap fixed D m ε b)
    (G : P.IncomingSlab a s) (L : G.TerminalLimitMetric)
    (hG : E.incoming = G) (hL : HEq E.terminal L)
    {x₀ : G.terminalRegularOpen} {δ : ℝ} {k : ℕ}
    (d : normalizedDatum L.metric x₀ δ k)
    (w : CanonicalStaticInsertionWitness d fixed.collarLength fixed.collar_pos D m ε)
    (hscale : S.neck.scale = metricScalarAt L.metric x₀)
    (hmetric : ∀ x v z, w.windowMetric.inner x v z = S.neck.scale *
      E.outputMetric.inner (S.window x) (mfderiv ThreeModel ThreeModel S.window x v)
        (mfderiv ThreeModel ThreeModel S.window x z))
    (hmark : ∀ z : ThreeBall, ∃ x : standardCapWindow D, ‖x.val‖ ≤ transitionEnd ∧
      S.window x = S.inclusion (S.witness.cap z))
    (hδS : δ ≤ S.delta) (hk : 2 * ⌊δ⁻¹⌋₊ ≤ k) : S.hasLinkedCanonicalWindow_C12X := by
  cases hG
  cases eq_of_heq hL
  exact ⟨x₀, δ, k, d, w, hscale.symm, hmetric, hmark, hδS, hk⟩

end MetricCutCapEvent.PresentedStaticCap

section

universe u

attribute [local instance] threeBallChartedSpace threeBall_isManifold

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

private theorem s10_window_inner_of_map_metric_eq
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (g h : SmoothRiemannianMetric ThreeModel M) (hmetric : g = h)
    {D q r : ℝ} (hq : q = r)
    (gW gW' : SmoothRiemannianMetric ThreeModel (standardCapWindow D)) (hW : gW = gW')
    (J K : standardCapWindow D → M) (hJ : J = K)
    (hinner : ∀ x v z, gW'.inner x v z = r * h.inner (K x)
      (mfderiv ThreeModel ThreeModel K x v) (mfderiv ThreeModel ThreeModel K x z)) :
    ∀ x v z, gW.inner x v z = q * g.inner (J x)
      (mfderiv ThreeModel ThreeModel J x v) (mfderiv ThreeModel ThreeModel J x z) := by
  cases hmetric
  cases hq
  cases hW
  cases hJ
  exact hinner

/-- Sibling of the Horn producer's private `hasCanonicalWindow_of_finite_metric`: same hypotheses,
plus an upgraded witness family `wU` (order `K b`, same window metric as `w b`), the order link
`2 ⌊(c δ)⁻¹⌋₊ ≤ K` and `c δ ≤ S.delta`; conclusion: linked canonical windows. -/
theorem hasLinkedCanonicalWindow_of_finite_metric_C12X
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M] [CompactSpace M]
    (orientation : SmoothOrientation ThreeModel M)
    {ι : Type} [Finite ι] {precision : ι → ℝ}
    (hδ : ∀ j, 0 < precision j)
    (f : ∀ j : ι, bufferedCylinder (precision j) → M)
    (hf : ∀ j, _root_.Topology.IsOpenEmbedding (f j))
    (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
    (hs : ∀ j, IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ (f j))
    (R : Set (ConnectedComponents (cutCore f)))
    {t₀ t₁ : ℝ} {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} :
    letI : LocallyPathConnectedSpace M :=
      originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
    let Q := FiniteCapQuotient transitionEnd_pos hδ f
      (fun j => (hf j).injective) hdisj
    let Ret := finiteCapRetained transitionEnd_pos hδ f hf hdisj R
    let Bidx := {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
    letI : ChartedSpace ThreeSpace Q :=
      finiteCapChartedSpace ThreeModel finrank_threeSpace_eq_three transitionEnd_pos hδ f hf hdisj
    letI : IsManifold ThreeModel ∞ Q :=
      finiteCapQuotient_isManifold finrank_threeSpace_eq_three transitionEnd_pos hδ f hf hdisj hs
    letI : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    letI : CompactSpace Q := finiteCapQuotient_compactSpace transitionEnd_pos hδ f hf hdisj
    letI : CompactSpace Ret :=
      (finiteCapRetained_discarded_compactSpace transitionEnd_pos hδ f hf hdisj R).1
    ∀ (oRet : SmoothOrientation ThreeModel Ret)
      (G : (OrientedThreeStage.ofSmoothOrientation M orientation).IncomingSlab t₀ t₁)
      (L : G.TerminalLimitMetric)
      (E : MetricCutCapEvent (OrientedThreeStage.ofSmoothOrientation M orientation)
        (OrientedThreeStage.ofSmoothOrientation Ret oRet) t₀ t₁),
      E.incoming = G → HEq E.terminal L →
      ∀ (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R)
          (fun x : M => G.terminalRegularRegion x))
        (c : ℝ) (hc : 4 ≤ c) (x₀ : ι → G.terminalRegularOpen) (order : ι → ℕ)
        (d₀ : ∀ i, normalizedDatum L.metric (x₀ i) (precision i) (order i))
        (hOriginal : ∀ i, f i = neckAmbientMap G.terminalRegularOpen (d₀ i))
        (k' : Bidx → ℕ)
        (hrec : ∀ b : Bidx, (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹)
        (d : ∀ b : Bidx, normalizedDatum L.metric
          ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (k' b))
        (hmap : ∀ b : Bidx, (d b).map =
          (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b))
        (hside : ∀ b : Bidx, (d b).retainedSide = true)
        (w : ∀ b : Bidx,
          CanonicalStaticInsertionWitness (d b) fixed.collarLength fixed.collar_pos D m ε)
        (K : Bidx → ℕ)
        (dU : ∀ b : Bidx, normalizedDatum L.metric
          ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (K b))
        (wU : ∀ b : Bidx,
          CanonicalStaticInsertionWitness (dU b) fixed.collarLength fixed.collar_pos D m ε),
        (∀ b, (wU b).windowMetric = (w b).windowMetric) →
        (∀ b, 2 * ⌊(c * precision b.val.1)⁻¹⌋₊ ≤ K b) →
        E.outputMetric = finiteFullPreparedMetric ThreeModel hδ f hf hdisj hs
          G.terminalRegularOpen L.metric R hRet c hc x₀ order d₀
          hOriginal hrec d hmap hside w →
        ∀ (e : E.RetainedBoundaryIndex ≃ Bidx)
          (S : ∀ b : E.RetainedBoundaryIndex, E.PresentedStaticCap fixed D m ε b),
          (∀ b, c * precision (e b).val.1 ≤ (S b).delta) →
          (∀ b, (S b).neck.scale = metricScalarAt L.metric
            ((d₀ (e b).val.1).offsetPoint (cuttingSign_sq (e b).val.2))) →
          (∀ b z, (S b).window z =
            finiteFullWitnessMap ThreeModel finrank_threeSpace_eq_three transitionEnd_pos
              hδ f hf hdisj hs R c hc (e b) ((w (e b)).window z)) →
          (∀ b (z : ThreeBall), ∃ u : standardCapWindow D, ‖u.val‖ ≤ transitionEnd ∧
            (S b).window u = (S b).inclusion ((S b).witness.cap z)) →
          ∀ b, (S b).hasLinkedCanonicalWindow_C12X := by
  let : LocallyPathConnectedSpace M :=
    originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
  let Q := FiniteCapQuotient transitionEnd_pos hδ f (fun j => (hf j).injective) hdisj
  let Ret := finiteCapRetained transitionEnd_pos hδ f hf hdisj R
  let : ChartedSpace ThreeSpace Q := finiteCapChartedSpace ThreeModel
    finrank_threeSpace_eq_three transitionEnd_pos hδ f hf hdisj
  let : IsManifold ThreeModel ∞ Q := finiteCapQuotient_isManifold
    finrank_threeSpace_eq_three transitionEnd_pos hδ f hf hdisj hs
  let : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  let : CompactSpace Q := finiteCapQuotient_compactSpace transitionEnd_pos hδ f hf hdisj
  let : CompactSpace Ret :=
    (finiteCapRetained_discarded_compactSpace transitionEnd_pos hδ f hf hdisj R).1
  dsimp only
  intro oRet G L E hG hL hRet c hc x₀ order d₀ hOriginal k' hrec d hmap hside w K dU wU hwU hK
    hOutput e S hSδ hscale hwindow hcap b
  have hInner := finiteFullPreparedMetric_window_inner
    (E := ThreeSpace) (H := ThreeSpace) (M := M)
    (ι := ι) (precision := precision) (A := fixed.collarLength)
    (D := D) (m := m) (ε := ε) (hA := fixed.collar_pos) (k' := k')
    ThreeModel hδ f hf hdisj hs G.terminalRegularOpen L.metric R hRet c hc x₀ order d₀
    hOriginal hrec d hmap hside w (e b)
  have hJ : ((S b).window : standardCapWindow D → Ret) =
      finiteFullWitnessMap ThreeModel finrank_threeSpace_eq_three transitionEnd_pos
        hδ f hf hdisj hs R c hc (e b) ∘ (w (e b)).window := funext (hwindow b)
  have hmetric := s10_window_inner_of_map_metric_eq E.outputMetric _ hOutput (hscale b)
    (wU (e b)).windowMetric (w (e b)).windowMetric (hwU (e b)) _ _ hJ hInner
  exact MetricCutCapEvent.PresentedStaticCap.hasLinkedCanonicalWindow_of_terminal_window_C12X
    (S b) G L hG hL (dU (e b)) (wU (e b)) (hscale b) hmetric (hcap b) (hSδ b) (hK (e b))

/-- Sibling of the Horn producer's private `hasCanonicalWindow_of_finite_metric_stage`
(arbitrary oriented stage `P`), with the upgraded witness family and the link. -/
theorem hasLinkedCanonicalWindow_of_finite_metric_stage_C12X
    (P : OrientedThreeStage.{u})
    {ι : Type} [Finite ι] {precision : ι → ℝ}
    (hδ : ∀ j, 0 < precision j)
    (f : ∀ j : ι, bufferedCylinder (precision j) → P.Carrier)
    (hf : ∀ j, _root_.Topology.IsOpenEmbedding (f j))
    (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
    (hs : ∀ j, IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ (f j))
    (R : Set (ConnectedComponents (cutCore f)))
    {t₀ t₁ : ℝ} {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} :
    letI : LocallyPathConnectedSpace P.Carrier :=
      originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
    let Q := FiniteCapQuotient transitionEnd_pos hδ f
      (fun j => (hf j).injective) hdisj
    let Ret := finiteCapRetained transitionEnd_pos hδ f hf hdisj R
    let Bidx := {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
    letI : ChartedSpace ThreeSpace Q :=
      finiteCapChartedSpace ThreeModel finrank_threeSpace_eq_three transitionEnd_pos hδ f hf hdisj
    letI : IsManifold ThreeModel ∞ Q :=
      finiteCapQuotient_isManifold finrank_threeSpace_eq_three transitionEnd_pos hδ f hf hdisj hs
    letI : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    letI : CompactSpace Q := finiteCapQuotient_compactSpace transitionEnd_pos hδ f hf hdisj
    letI : CompactSpace Ret :=
      (finiteCapRetained_discarded_compactSpace transitionEnd_pos hδ f hf hdisj R).1
    ∀ (oRet : SmoothOrientation ThreeModel Ret)
      (G : P.IncomingSlab t₀ t₁)
      (L : G.TerminalLimitMetric)
      (E : MetricCutCapEvent P
        (OrientedThreeStage.ofSmoothOrientation Ret oRet) t₀ t₁),
      E.incoming = G → HEq E.terminal L →
      ∀ (hRet : MapsTo (Subtype.val : cutCore f → P.Carrier) (retainedCore f R)
          (fun x : P.Carrier => G.terminalRegularRegion x))
        (c : ℝ) (hc : 4 ≤ c) (x₀ : ι → G.terminalRegularOpen) (order : ι → ℕ)
        (d₀ : ∀ i, normalizedDatum L.metric (x₀ i) (precision i) (order i))
        (hOriginal : ∀ i, f i = neckAmbientMap G.terminalRegularOpen (d₀ i))
        (k' : Bidx → ℕ)
        (hrec : ∀ b : Bidx, (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹)
        (d : ∀ b : Bidx, normalizedDatum L.metric
          ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (k' b))
        (hmap : ∀ b : Bidx, (d b).map =
          (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b))
        (hside : ∀ b : Bidx, (d b).retainedSide = true)
        (w : ∀ b : Bidx,
          CanonicalStaticInsertionWitness (d b) fixed.collarLength fixed.collar_pos D m ε)
        (K : Bidx → ℕ)
        (dU : ∀ b : Bidx, normalizedDatum L.metric
          ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (K b))
        (wU : ∀ b : Bidx,
          CanonicalStaticInsertionWitness (dU b) fixed.collarLength fixed.collar_pos D m ε),
        (∀ b, (wU b).windowMetric = (w b).windowMetric) →
        (∀ b, 2 * ⌊(c * precision b.val.1)⁻¹⌋₊ ≤ K b) →
        E.outputMetric = finiteFullPreparedMetric ThreeModel hδ f hf hdisj hs
          G.terminalRegularOpen L.metric R hRet c hc x₀ order d₀
          hOriginal hrec d hmap hside w →
        ∀ (e : E.RetainedBoundaryIndex ≃ Bidx)
          (S : ∀ b : E.RetainedBoundaryIndex, E.PresentedStaticCap fixed D m ε b),
          (∀ b, c * precision (e b).val.1 ≤ (S b).delta) →
          (∀ b, (S b).neck.scale = metricScalarAt L.metric
            ((d₀ (e b).val.1).offsetPoint (cuttingSign_sq (e b).val.2))) →
          (∀ b z, (S b).window z =
            finiteFullWitnessMap ThreeModel finrank_threeSpace_eq_three transitionEnd_pos
              hδ f hf hdisj hs R c hc (e b) ((w (e b)).window z)) →
          (∀ b (z : ThreeBall), ∃ u : standardCapWindow D, ‖u.val‖ ≤ transitionEnd ∧
            (S b).window u = (S b).inclusion ((S b).witness.cap z)) →
          ∀ b, (S b).hasLinkedCanonicalWindow_C12X := by
  revert f
  rw [← P.ofSmoothOrientation_smoothOrientation]
  intro f hf hdisj hs R
  exact hasLinkedCanonicalWindow_of_finite_metric_C12X P.smoothOrientation hδ f hf hdisj hs R

end

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
