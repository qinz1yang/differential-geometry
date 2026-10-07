import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitVolumeAlgebra_O5
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedRicciConvergence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.AmbientQuadraticControl
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling

/-!
# CH12-O5 / LTF01b, group V: the Ricci identity of an actual limit from vanishing defect

Static route for LTF01b (finding F2 of the O5 DELIVERIES block): at a limit point `x` of an actual
unscathed parabolic limit `Q` at time `s`, if the normalised Ricci defect of the actual slices at
`Φ_j x` tends to zero, then `Ric(Q.metric s) = -(2 s)⁻¹ Q.metric s` at `x`.

The convergence must be *canonical* (`C.domain k = canonicalSourceData Φ k`): with a free reference
metric `MetricConvergenceData` carries no information (finding F1).

* `defectSet_bddAbove_O5`, `defect_quad_le_O5`: the defect set is bounded and controls the
  quadratic form `|2 Ric(V,V) + g(V,V)| ≤ defect · g(V,V)`.
* `bilin_eq_of_quad_eq_O5`: polarisation for symmetric continuous bilinear forms.
* `ricci_point_of_defect_O5`: the pointwise identity (canonical convergence + vanishing defect).
* `ricci_of_center_O5`: LTF01b (Ricci and `sec ≡ -(4 s)⁻¹`) from C1 (`hcenter`), canonical
  convergence of `Q` at `s`, and the seed-at-limit-points input V1a (`hseed`).
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.CheegerGromovCompactness
open GC.LongTime Set Filter
open scoped Manifold ContDiff ENNReal Topology
namespace GC.LongTime.Ch12
universe u

section Static

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]

/-- The set whose supremum is the Ricci defect. -/
def defectSet_O5 (g : SmoothRiemannianMetric ThreeModel M) (p : M) : Set ℝ :=
  {r : ℝ | ∃ v w : TangentSpace ThreeModel p,
    g.inner p v v ≤ 1 ∧ g.inner p w w ≤ 1 ∧
      r = |2 * ricciTensor g p v w + g.inner p v w|}

omit [SigmaCompactSpace M] in
theorem defectSet_bddAbove_O5 (g : SmoothRiemannianMetric ThreeModel M) (p : M) :
    BddAbove (defectSet_O5 g p) := by
  set C : ℝ := (Module.finrank ℝ (TangentSpace ThreeModel p) : ℝ) *
    Real.sqrt (Tensor0SBundle.normSq0S g p 2 (metricRicciAt g p)) with hC
  have hC0 : 0 ≤ C := by positivity
  have hq : ∀ u : TangentSpace ThreeModel p, |ricciTensor g p u u| ≤ C * g.inner p u u := by
    intro u
    rw [← metricRicciAt_apply_eq_ricciTensor]
    exact tensor02_quadForm_abs_le_normSq0S g (metricRicciAt g p) u
  refine ⟨2 * C + 1, ?_⟩
  rintro r ⟨v, w, hv, hw, rfl⟩
  have hsym := ricciTensor_symm g p v w
  have hgsym := g.symm p v w
  have hp := hq (v + w)
  have hm := hq (v - w)
  have hRp : ricciTensor g p (v + w) (v + w) =
      ricciTensor g p v v + ricciTensor g p v w + ricciTensor g p w v + ricciTensor g p w w := by
    simp only [map_add, add_apply]; ring
  have hRm : ricciTensor g p (v - w) (v - w) =
      ricciTensor g p v v - ricciTensor g p v w - ricciTensor g p w v + ricciTensor g p w w := by
    simp only [map_sub, sub_apply]; ring
  have hGp : g.inner p (v + w) (v + w) =
      g.inner p v v + g.inner p v w + g.inner p w v + g.inner p w w := by
    simp only [map_add, add_apply]; ring
  have hGm : g.inner p (v - w) (v - w) =
      g.inner p v v - g.inner p v w - g.inner p w v + g.inner p w w := by
    simp only [map_sub, sub_apply]; ring
  have h0p := metric_inner_self_nonneg g p (v + w)
  have h0m := metric_inner_self_nonneg g p (v - w)
  rw [hRp] at hp
  rw [hRm] at hm
  rw [hGp] at hp h0p
  rw [hGm] at hm h0m
  rw [hsym] at hp hm
  rw [← hgsym] at hp hm h0p h0m
  have hric : |ricciTensor g p w v| ≤ C := by
    rw [abs_le] at hp hm ⊢
    constructor <;> nlinarith
  have hinner : |g.inner p w v| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith
  rw [hsym, hgsym]
  calc |2 * ricciTensor g p w v + g.inner p w v|
      ≤ |2 * ricciTensor g p w v| + |g.inner p w v| := abs_add_le _ _
    _ = 2 * |ricciTensor g p w v| + |g.inner p w v| := by rw [abs_mul, abs_two]
    _ ≤ 2 * C + 1 := by linarith

omit [SigmaCompactSpace M] in
/-- The defect controls the quadratic form. -/
theorem defect_quad_le_O5 (g : SmoothRiemannianMetric ThreeModel M) (p : M)
    (V : TangentSpace ThreeModel p) :
    |2 * ricciTensor g p V V + g.inner p V V| ≤ sSup (defectSet_O5 g p) * g.inner p V V := by
  by_cases hV : V = 0
  · subst hV; simp
  have hpos : 0 < g.inner p V V := g.pos p V hV
  set c : ℝ := (Real.sqrt (g.inner p V V))⁻¹ with hc
  have hsq : Real.sqrt (g.inner p V V) ^ 2 = g.inner p V V := Real.sq_sqrt hpos.le
  have hsqpos : 0 < Real.sqrt (g.inner p V V) := Real.sqrt_pos.mpr hpos
  have hcc0 : c * c = (g.inner p V V)⁻¹ := by rw [hc, ← mul_inv, ← sq, hsq]
  have hcc : c * c * g.inner p V V = 1 := by rw [hcc0, inv_mul_cancel₀ hpos.ne']
  have hU : g.inner p (c • V) (c • V) = 1 := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    linarith [hcc]
  have hmem : |2 * ricciTensor g p (c • V) (c • V) + g.inner p (c • V) (c • V)| ∈
      defectSet_O5 g p := ⟨c • V, c • V, hU.le, hU.le, rfl⟩
  have hle := le_csSup (defectSet_bddAbove_O5 g p) hmem
  have hexp : 2 * ricciTensor g p (c • V) (c • V) + g.inner p (c • V) (c • V) =
      (c * c) * (2 * ricciTensor g p V V + g.inner p V V) := by
    simp only [map_smul, smul_apply, smul_eq_mul]; ring
  rw [hexp, abs_mul, abs_of_nonneg (by positivity : 0 ≤ c * c)] at hle
  have hinv : g.inner p V V = (c * c)⁻¹ := by
    rw [hcc0, inv_inv]
  have hcpos : 0 < c * c := by positivity
  calc |2 * ricciTensor g p V V + g.inner p V V|
      = (c * c)⁻¹ * ((c * c) * |2 * ricciTensor g p V V + g.inner p V V|) := by
        rw [← mul_assoc, inv_mul_cancel₀ hcpos.ne', one_mul]
    _ ≤ (c * c)⁻¹ * sSup (defectSet_O5 g p) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = sSup (defectSet_O5 g p) * g.inner p V V := by rw [hinv]; ring

end Static

/-- Polarisation: symmetric continuous bilinear forms with proportional quadratic forms are
proportional. -/
theorem bilin_eq_of_quad_eq_O5 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A B : V →L[ℝ] V →L[ℝ] ℝ) (c : ℝ) (hA : ∀ v w, A v w = A w v) (hB : ∀ v w, B v w = B w v)
    (h : ∀ v, A v v = c * B v v) (v w : V) : A v w = c * B v w := by
  have h1 := h (v + w)
  have h2 := h v
  have h3 := h w
  simp only [map_add, add_apply] at h1
  rw [hA w v, hB w v] at h1
  linarith

/-! ### The actual limit at time `s` as a pointed sequence / pointed manifold -/

attribute [local instance] ActualUnscathedParabolicLimit_S13.topology
  ActualUnscathedParabolicLimit_S13.charts ActualUnscathedParabolicLimit_S13.smooth
  ActualUnscathedParabolicLimit_S13.hausdorff ActualUnscathedParabolicLimit_S13.sigmaCompact

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}

/-- The pointed sequence `(M_{t_j s}, t_j⁻¹ g(t_j s), p_j)` of `Q.converges`. -/
abbrev ActualUnscathedParabolicLimit_S13.seqAt_O5 (Q : ActualUnscathedParabolicLimit_S13 F)
    (s : ℝ) (hs : s ∈ Q.timeInterval) : PointedRiemannianSeq.{u, 0, 0} (I := ThreeModel) :=
  ⟨fun j =>
    { M := (Q.slice j s hs).stage.Carrier
      topology := inferInstance
      charted := inferInstance
      smooth := inferInstance
      sigmaCompact := inferInstance
      t2 := inferInstance
      t2TangentBundle := inferInstance
      basepoint := Q.point j s hs
      metric := scaleMetric (Q.times j)⁻¹ (inv_pos.mpr (Q.times_pos j)) (Q.slice j s hs).metric }⟩

/-- The pointed limit `(Q.Carrier, Q.metric s, Q.basepoint)` of `Q.converges`. -/
abbrev ActualUnscathedParabolicLimit_S13.limitAt_O5 (Q : ActualUnscathedParabolicLimit_S13 F)
    (s : ℝ) : PointedRiemannianManifold.{u, 0, 0} (I := ThreeModel) :=
  { M := Q.Carrier
    topology := Q.topology
    charted := Q.charts
    smooth := Q.smooth
    sigmaCompact := Q.sigmaCompact
    t2 := Q.hausdorff
    t2TangentBundle := inferInstance
    basepoint := Q.basepoint
    metric := Q.metric s }

/-- **V1b.** Pointwise Ricci identity at a limit point from canonical convergence and vanishing
normalised defect along `Φ_j x`. -/
theorem ricci_point_of_defect_O5 (Q : ActualUnscathedParabolicLimit_S13 F) (s : ℝ)
    (hs : s ∈ Q.timeInterval)
    (Φ : PointedRiemannianConvergenceMaps (Q.seqAt_O5 s hs) (Q.limitAt_O5 s) id)
    (C : MetricConvergenceData Φ)
    (hcan : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Φ k)
    (x : Q.Carrier)
    (hdef : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
      NormalizedRicciDefect_S13 (Q.slice j s hs) (Φ.map j x) < ε) :
    ∀ v w : TangentSpace ThreeModel x,
      ricciTensor (Q.metric s) x v w = -(2 * s)⁻¹ * (Q.metric s).inner x v w := by
  have hs0 : 0 < s := Q.interval_pos hs
  apply bilin_eq_of_quad_eq_O5 _ _ _ (ricciTensor_symm (Q.metric s) x) ((Q.metric s).symm x)
  intro v
  -- the actual quantities
  let a : ℕ → ℝ := fun k => ricciTensor ((Q.seqAt_O5 s hs).obj (id k)).metric (Φ.map k x)
      (mfderiv ThreeModel ThreeModel (Φ.map k) x v) (mfderiv ThreeModel ThreeModel (Φ.map k) x v)
  let b : ℕ → ℝ := fun k => ((Q.seqAt_O5 s hs).obj (id k)).metric.inner (Φ.map k x)
      (mfderiv ThreeModel ThreeModel (Φ.map k) x v) (mfderiv ThreeModel ThreeModel (Φ.map k) x v)
  set A := ricciTensor (Q.metric s) x v v with hAdef
  set B := (Q.metric s).inner x v v with hBdef
  have hB0 : 0 ≤ B := metric_inner_self_nonneg (Q.metric s) x v
  have ha : Tendsto a atTop (𝓝 A) :=
    PDE.RicciFlow.Perelman.KappaSolutions.pointedRicci_tendsto_of_metricCG_canonical_domains
      C hcan x v
  have hb : Tendsto b atTop (𝓝 B) := by
    have href : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric := by
      intro k; rw [hcan k]; rfl
    apply Metric.tendsto_atTop.mpr
    intro e he
    obtain ⟨k0, hk0⟩ :=
      PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_full_ambient_quadratic_control
        C href {x} isCompact_singleton (e / (B + 1)) (by positivity)
    refine ⟨k0, fun k hk => ?_⟩
    have h1 := (hk0 k hk).2 x (mem_singleton x) v
    rw [Real.dist_eq]
    calc |b k - B| ≤ e / (B + 1) * B := h1
      _ < e := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]; nlinarith
  -- the defect inequality on the actual slices
  have hineq : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, |2 * a k + s⁻¹ * b k| ≤ ε * (s⁻¹ * b k) := by
    intro ε hε
    filter_upwards [hdef ε hε] with k hk
    set sl := Q.slice k s hs
    set V := mfderiv ThreeModel ThreeModel (Φ.map k) x v
    have hq := defect_quad_le_O5 sl.normalizedMetric (Φ.map k x) V
    have hbk : 0 ≤ b k := metric_inner_self_nonneg _ _ _
    have hnorm : sl.normalizedMetric.inner (Φ.map k x) V V = s⁻¹ * b k := by
      change (scaleMetric sl.time⁻¹ (inv_pos.mpr sl.positive) sl.metric).inner (Φ.map k x) V V =
        s⁻¹ * (scaleMetric (Q.times k)⁻¹ (inv_pos.mpr (Q.times_pos k)) sl.metric).inner (Φ.map k x) V V
      rw [scaleMetric_inner, scaleMetric_inner, Q.slice_time k s hs, mul_inv]
      ring
    have hric : ricciTensor sl.normalizedMetric (Φ.map k x) V V = a k := by
      change ricciTensor (scaleMetric sl.time⁻¹ (inv_pos.mpr sl.positive) sl.metric) (Φ.map k x) V V =
        ricciTensor (scaleMetric (Q.times k)⁻¹ (inv_pos.mpr (Q.times_pos k)) sl.metric) (Φ.map k x) V V
      rw [ricciTensor_scaleMetric, ricciTensor_scaleMetric]
    rw [hnorm, hric] at hq
    have hD : sSup (defectSet_O5 sl.normalizedMetric (Φ.map k x)) < ε := hk
    calc |2 * a k + s⁻¹ * b k| ≤ sSup (defectSet_O5 sl.normalizedMetric (Φ.map k x)) *
          (s⁻¹ * b k) := hq
      _ ≤ ε * (s⁻¹ * b k) :=
          mul_le_mul_of_nonneg_right hD.le (mul_nonneg (inv_pos.mpr hs0).le hbk)
  -- pass to the limit
  have hlim : ∀ ε : ℝ, 0 < ε → |2 * A + s⁻¹ * B| ≤ ε * (s⁻¹ * B) := by
    intro ε hε
    have ht : Tendsto (fun k => ε * (s⁻¹ * b k) - |2 * a k + s⁻¹ * b k|) atTop
        (𝓝 (ε * (s⁻¹ * B) - |2 * A + s⁻¹ * B|)) :=
      (tendsto_const_nhds.mul (tendsto_const_nhds.mul hb)).sub
        (((tendsto_const_nhds.mul ha).add (tendsto_const_nhds.mul hb)).abs)
    have h0 := ge_of_tendsto ht ((hineq ε hε).mono fun k hk => sub_nonneg.mpr hk)
    linarith
  have hzero : 2 * A + s⁻¹ * B = 0 := by
    have hle : |2 * A + s⁻¹ * B| ≤ 0 := by
      apply le_of_forall_pos_lt_add
      intro e he
      have hsB : 0 ≤ s⁻¹ * B := mul_nonneg (inv_pos.mpr hs0).le hB0
      have := hlim (e / (s⁻¹ * B + 1)) (by positivity)
      have h2 : e / (s⁻¹ * B + 1) * (s⁻¹ * B) < e := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]; nlinarith
      linarith
    exact abs_nonpos_iff.mp hle
  have : A = -(2 * s)⁻¹ * B := by
    rw [mul_inv]; linarith
  exact this

/-- **LTF01b (canonical form).** For an actual unscathed parabolic limit `Q` whose convergence at
time `s` is canonical, the centre statement C1 (`hcenter`) and the input V1a (`hseed`: a seed of
fixed constants at `Φ_j x` for late `j`, for every limit point `x`) give
`Ric = -(2 s)⁻¹ g` and `sec ≡ -(4 s)⁻¹` for `Q.metric s`.  No completeness of `Q` is used. -/
theorem ricci_of_center_O5
    (hcenter : ∀ (S : LatePointSequence_S13 F) (a v : ℝ), 0 < a → 0 < v →
      (∀ j, HasNormalizedSeed_S13 (S.slices j) (S.point j) a v) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, NormalizedRicciDefect_S13 (S.slices j) (S.point j) < ε)
    (Q : ActualUnscathedParabolicLimit_S13 F) (s : ℝ) (hs : s ∈ Q.timeInterval)
    (Φ : PointedRiemannianConvergenceMaps (Q.seqAt_O5 s hs) (Q.limitAt_O5 s) id)
    (C : MetricConvergenceData Φ)
    (hcan : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Φ k)
    (hseed : ∀ x : Q.Carrier, ∃ a v : ℝ, 0 < a ∧ 0 < v ∧
      ∀ᶠ j in atTop, HasNormalizedSeed_S13 (Q.slice j s hs) (Φ.map j x) a v) :
    RicciEqualsMetricMultiple_S13 (Q.metric s) (-(2 * s)⁻¹) ∧
      hasConstantSectionalCurvature (Q.metric s) (-(4 * s)⁻¹) := by
  have hs0 : 0 < s := Q.interval_pos hs
  have hric : RicciEqualsMetricMultiple_S13 (Q.metric s) (-(2 * s)⁻¹) := by
    intro x
    apply ricci_point_of_defect_O5 Q s hs Φ C hcan x
    intro ε hε
    obtain ⟨a, v, ha, hv, hx⟩ := hseed x
    obtain ⟨N, hN⟩ := eventually_atTop.mp hx
    let S' : LatePointSequence_S13 F :=
      { slices := fun j => Q.slice (j + N) s hs
        times_tendsto := by
          have h1 : Tendsto (fun j => Q.times (j + N)) atTop atTop :=
            Q.times_tendsto.comp (tendsto_add_atTop_nat N)
          refine (h1.atTop_mul_const hs0).congr fun j => ?_
          exact (Q.slice_time (j + N) s hs).symm
        point := fun j => Φ.map (j + N) x }
    have hseed' : ∀ j, HasNormalizedSeed_S13 (S'.slices j) (S'.point j) a v :=
      fun j => hN (j + N) (Nat.le_add_left N j)
    have h := hcenter S' a v ha hv hseed' ε hε
    obtain ⟨M, hM⟩ := eventually_atTop.mp h
    refine eventually_atTop.mpr ⟨M + N, fun j hj => ?_⟩
    have hjN : j - N + N = j := Nat.sub_add_cancel (by omega)
    have := hM (j - N) (by omega)
    simp only [S'] at this
    rw [hjN] at this
    exact this
  refine ⟨hric, ?_⟩
  have hc := ricciEq_constSec_O5 (Q.metric s) _ hric
  have he : -(2 * s)⁻¹ / 2 = -(4 * s)⁻¹ := by
    rw [neg_div, div_eq_mul_inv, ← mul_inv, show 2 * s * 2 = 4 * s by ring]
  rwa [he] at hc

end GC.LongTime.Ch12
