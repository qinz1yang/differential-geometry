import DifferentialGeometry.Geometry.Comparison.FiniteSoul.NormalFlowGradient
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.OutwardFieldApplications
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# The LFR46 field: radial near the soul, soul-outward, point-outward far away (lane CMS3-FLOW2, G2)

Blueprint LFR46 (A:28913–28946), restated per disposition D1 (same tube, `ℓ + δ < ε`, `δ < ℓ/3`,
profile positive on the outward zone and `1` on the seam). Data: LFR45.1 for a compact `S`, and the
SAME normal tube `(ε, ψ)` of S3-TUBE. Constants: `ℓ = ε/2`, `δ = ε/8`.

* `inner_add_smul_le_tube`: `g(αa + βb, αa + βb) ≤ α g(a,a) + β g(b,b)` for `α, β ≥ 0`, `α + β ≤ 1`.
* `exists_normalFlowField`: ONE field
  `X = θ(d_S) prof(d_S) ∇d_S + (1 − θ(d_S)) ((1 − χ) Y + χ Xf)` with
  - `prof(τ) = smoothTransition ((τ − ε/8)/(ε/4))`: `0` on `τ ≤ δ`, `1` on `τ ≥ ℓ − δ`, `> 0` on `τ > δ`;
  - `θ(τ) = smoothTransition ((3ε/4 − τ)/(ε/8))`: `1` on `τ ≤ ℓ + δ`, `0` on `τ ≥ 3ε/4 < ε`;
  - `Y` = S-PATCH of the LFR45.1 vectors on `{d_S ≥ ℓ + δ}`; `Xf` = POINT; `χ` a smooth cutoff, `0`
    on `B̄(p, A₁)`, `1` on `{d(p, ·) ≥ A₁ + 1}`.
  `X` is `C^(r−1)` (the gradient is read off the geodesic flow), `g(X, X) ≤ 4`, `X = prof(d_S)∇d_S` on
  `{0 < d_S ≤ ℓ + δ}` (so `X = ∇d_S` on the seam `(ℓ − δ, ℓ + δ)`), `X = 0` on `{d_S ≤ δ} ⊇ S`, strictly
  soul-outward on `{d_S ≥ ℓ/3}`, and the point margin `−1/4` for `d(p, q) ≥ A₂` (LFR46.2).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

omit [FiniteDimensional ℝ E] [I.Boundaryless]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M] in
/-- **Jensen for the squared length** with a zero weight: `g(αa + βb) ≤ α g(a) + β g(b)` when
`α, β ≥ 0` and `α + β ≤ 1`. -/
theorem inner_add_smul_le_tube {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (x : M)
    (a b : TangentSpace I x) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β ≤ 1) :
    g.inner x (α • a + β • b) (α • a + β • b) ≤ α * g.inner x a a + β * g.inner x b b := by
  have hexp : g.inner x (α • a + β • b) (α • a + β • b) =
      α * α * g.inner x a a + α * β * g.inner x a b + β * α * g.inner x b a +
        β * β * g.inner x b b := by
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
    ring
  have hsym : g.inner x b a = g.inner x a b := g.symm x b a
  have hnn : ∀ w : TangentSpace I x, 0 ≤ g.inner x w w := fun w => by
    by_cases hw : w = 0
    · rw [hw]; simp
    · exact (g.pos x w hw).le
  have hdiff := hnn (a - b)
  have hdexp : g.inner x (a - b) (a - b) =
      g.inner x a a - g.inner x a b - g.inner x b a + g.inner x b b := by
    simp only [map_sub, sub_apply]
    ring
  rw [hdexp, hsym] at hdiff
  rw [hexp, hsym]
  have ha := hnn a
  have hb := hnn b
  nlinarith [mul_nonneg hα hβ, mul_nonneg (mul_nonneg hα hβ) hdiff,
    mul_nonneg hα (sub_nonneg.mpr (show α ≤ 1 - β by linarith)),
    mul_nonneg hβ (sub_nonneg.mpr (show β ≤ 1 - α by linarith)),
    mul_nonneg (mul_nonneg hα (sub_nonneg.mpr (show β ≤ 1 - α by linarith))) ha,
    mul_nonneg (mul_nonneg hβ (sub_nonneg.mpr (show α ≤ 1 - β by linarith))) hb]

/-- The inner profile `prof(τ) = smoothTransition ((τ − ε/8)/(ε/4))`. -/
theorem normalFlowProfile_spec {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (fun τ : ℝ => Real.smoothTransition ((τ - ε / 8) / (ε / 4))) ∧
      (∀ τ, τ ≤ ε / 8 → Real.smoothTransition ((τ - ε / 8) / (ε / 4)) = 0) ∧
      (∀ τ, 3 * ε / 8 ≤ τ → Real.smoothTransition ((τ - ε / 8) / (ε / 4)) = 1) ∧
      (∀ τ, ε / 8 < τ → 0 < Real.smoothTransition ((τ - ε / 8) / (ε / 4))) ∧
      (∀ τ, 0 ≤ Real.smoothTransition ((τ - ε / 8) / (ε / 4)) ∧
        Real.smoothTransition ((τ - ε / 8) / (ε / 4)) ≤ 1) := by
  have hε4 : 0 < ε / 4 := by positivity
  refine ⟨Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _),
    fun τ hτ => Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (by linarith) hε4.le), fun τ hτ => Real.smoothTransition.one_of_one_le ?_,
    fun τ hτ => Real.smoothTransition.pos_of_pos (div_pos (by linarith) hε4),
    fun τ => ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩⟩
  rw [le_div_iff₀ hε4]
  linarith

/-- The seam cutoff `θ(τ) = smoothTransition ((3ε/4 − τ)/(ε/8))`. -/
theorem normalFlowCutoff_spec {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (fun τ : ℝ => Real.smoothTransition ((3 * ε / 4 - τ) / (ε / 8))) ∧
      (∀ τ, τ ≤ 5 * ε / 8 → Real.smoothTransition ((3 * ε / 4 - τ) / (ε / 8)) = 1) ∧
      (∀ τ, 3 * ε / 4 ≤ τ → Real.smoothTransition ((3 * ε / 4 - τ) / (ε / 8)) = 0) ∧
      (∀ τ, 0 ≤ Real.smoothTransition ((3 * ε / 4 - τ) / (ε / 8)) ∧
        Real.smoothTransition ((3 * ε / 4 - τ) / (ε / 8)) ≤ 1) := by
  have hε8 : 0 < ε / 8 := by positivity
  refine ⟨Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _),
    fun τ hτ => Real.smoothTransition.one_of_one_le ?_,
    fun τ hτ => Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (by linarith) hε8.le),
    fun τ => ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩⟩
  rw [le_div_iff₀ hε8]
  linarith

/-- **The LFR46 field** on the SAME tube (`ℓ = ε/2`, `δ = ε/8`). -/
theorem exists_normalFlowField [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {S : Set M} (hSc : IsCompact S) (hSne : S.Nonempty)
    (hout : ∀ q ∉ S, ∃ v : E, g.inner q v v = 1 ∧
      ∀ u ∈ g.finiteMinimizingDirectionsTo S q, g.inner q v u < 0)
    {ε : ℝ} (hε : 0 < ε) {ψ : M → TangentBundle I M}
    (hψs : ContMDiffOn I I.tangent ((r - 1 : ℕ∞) : ℕ∞ω) ψ {x | infDist x S < ε})
    (hψ : ∀ x, infDist x S < ε → ψ x ∈ normalSetFinite g S ∧ g.expMap (ψ x) = x ∧
      Real.sqrt (g.inner (ψ x).proj (ψ x).snd (ψ x).snd) = infDist x S)
    (hψexp : ∀ v ∈ normalSetFinite g S, Real.sqrt (g.inner v.proj v.snd v.snd) < ε →
      ψ (g.expMap v) = v ∧ infDist (g.expMap v) S = Real.sqrt (g.inner v.proj v.snd v.snd))
    (hdS : ContMDiffOn I 𝓘(ℝ, ℝ) ((r - 1 : ℕ∞) : ℕ∞ω) (fun x => infDist x S)
      {x | 0 < infDist x S ∧ infDist x S < ε})
    (p : M) :
    ∃ (X : (x : M) → TangentSpace I x) (A₂ : ℝ) (prof : ℝ → ℝ), 0 < A₂ ∧
      ContMDiff I I.tangent ((r - 1 : ℕ∞) : ℕ∞ω) (fun x => (⟨x, X x⟩ : TangentBundle I M)) ∧
      (∀ x, g.inner x (X x) (X x) ≤ 4) ∧
      (∀ q, A₂ ≤ dist p q → ∀ u ∈ g.finiteMinimizingDirectionsTo {p} q,
        g.inner q (X q) u ≤ -(1 / 4)) ∧
      (∀ q, ε / 6 ≤ infDist q S → ∀ u ∈ g.finiteMinimizingDirectionsTo S q,
        g.inner q (X q) u < 0) ∧
      (∀ q, 0 < infDist q S → infDist q S ≤ 5 * ε / 8 →
        X q = prof (infDist q S) • tubeGradField g S ψ q) ∧
      (∀ q, infDist q S ≤ ε / 8 → X q = 0) ∧
      ContDiff ℝ ∞ prof ∧ (∀ τ, τ ≤ ε / 8 → prof τ = 0) ∧ (∀ τ, 3 * ε / 8 ≤ τ → prof τ = 1) ∧
      (∀ τ, ε / 8 < τ → 0 < prof τ) ∧ (∀ τ, 0 ≤ prof τ ∧ prof τ ≤ 1) := by
  classical
  have : ProperSpace M := Manifold.properSpace_of_isRiemannianManifold I
  have : SigmaCompactSpace M := inferInstance
  set m : ℕ∞ω := ((r - 1 : ℕ∞) : ℕ∞ω) with hm
  have hm_top : m ≤ ((⊤ : ℕ∞) : ℕ∞ω) := WithTop.coe_le_coe.mpr le_top
  set prof : ℝ → ℝ := fun τ => Real.smoothTransition ((τ - ε / 8) / (ε / 4)) with hprofdef
  set θ : ℝ → ℝ := fun τ => Real.smoothTransition ((3 * ε / 4 - τ) / (ε / 8)) with hθdef
  have hPS := normalFlowProfile_spec hε
  have hCS := normalFlowCutoff_spec hε
  have hprofC : ContDiff ℝ ∞ prof := hPS.1
  have hprof0 : ∀ τ, τ ≤ ε / 8 → prof τ = 0 := hPS.2.1
  have hprof1 : ∀ τ, 3 * ε / 8 ≤ τ → prof τ = 1 := hPS.2.2.1
  have hprofpos : ∀ τ, ε / 8 < τ → 0 < prof τ := hPS.2.2.2.1
  have hprofI : ∀ τ, 0 ≤ prof τ ∧ prof τ ≤ 1 := hPS.2.2.2.2
  have hθC : ContDiff ℝ ∞ θ := hCS.1
  have hθ1 : ∀ τ, τ ≤ 5 * ε / 8 → θ τ = 1 := hCS.2.1
  have hθ0 : ∀ τ, 3 * ε / 4 ≤ τ → θ τ = 0 := hCS.2.2.1
  have hθI : ∀ τ, 0 ≤ θ τ ∧ θ τ ≤ 1 := hCS.2.2.2
  clear hPS hCS
  have hdc : Continuous (fun x => infDist x S) := continuous_infDist_pt S
  -- the soul-outward patch `Y` on `{d_S ≥ ℓ + δ}`
  set A : Set M := {x | 5 * ε / 8 ≤ infDist x S} with hAdef
  have hAc : IsClosed A := isClosed_le continuous_const hdc
  have hAS : ∀ x ∈ A, x ∉ S := fun x hx hxS => by
    have h0 : infDist x S = 0 := infDist_zero_of_mem hxS
    have : 5 * ε / 8 ≤ infDist x S := hx
    linarith
  set v : (x : M) → TangentSpace I x := fun x =>
    if h : x ∈ S then (0 : TangentSpace I x) else (hout x h).choose with hvdef
  have hvspec : ∀ x ∉ S, g.inner x (v x) (v x) = 1 ∧
      ∀ u ∈ g.finiteMinimizingDirectionsTo S x, g.inner x (v x) u < 0 := fun x hx => by
    have hvx : v x = (hout x hx).choose := dite_eq_right hx
    rw [hvx]
    exact (hout x hx).choose_spec
  obtain ⟨Y, hYs, hY4, O, -, hAO, hYout⟩ :=
    exists_contMDiff_outward_field_minimizingDirections g hr hnorm hSc.isClosed hAc (R := 2)
      (c := 0) two_pos v (fun x hx => by rw [(hvspec x (hAS x hx)).1]; norm_num)
      (fun x hx u hu => by rw [neg_zero]; exact (hvspec x (hAS x hx)).2 u hu)
  -- the point field and the far cutoff
  obtain ⟨A₀, A₁, hA₀, hA₀₁, hSball, Xf, hXfs, hXf4, -, hXfout⟩ :=
    exists_outward_field_two_targets_finite g hr hnorm hsec p hSc
  have hfarc : IsClosed {q : M | A₁ + 1 ≤ dist p q} :=
    isClosed_le continuous_const (continuous_const.dist continuous_id)
  have hdisj : Disjoint (closedBall p A₁) {q : M | A₁ + 1 ≤ dist p q} := by
    rw [Set.disjoint_left]
    intro x hx hx'
    rw [mem_closedBall, dist_comm] at hx
    change A₁ + 1 ≤ dist p x at hx'
    linarith
  obtain ⟨χ, hχ0, hχ1, hχI⟩ := exists_contMDiffMap_zero_one_of_isClosed I (n := ⊤)
    isClosed_closedBall hfarc hdisj
  set Yo : (x : M) → TangentSpace I x := fun x => (1 - χ x) • Y x + χ x • Xf x with hYodef
  have hYos : ContMDiff I I.tangent ∞ (fun x => (⟨x, Yo x⟩ : TangentBundle I M)) :=
    ((contMDiff_const.sub χ.contMDiff).smul_section hYs).add_section
      (χ.contMDiff.smul_section hXfs)
  have hYo4 : ∀ x, g.inner x (Yo x) (Yo x) < 4 := by
    intro x
    obtain ⟨h0, h1⟩ := hχI x
    have hle : g.inner x (Yo x) (Yo x) ≤
        (1 - χ x) * g.inner x (Y x) (Y x) + χ x * g.inner x (Xf x) (Xf x) :=
      inner_add_smul_le_tube g x (Y x) (Xf x) (sub_nonneg.mpr h1) h0 (by linarith)
    have hY := hY4 x
    have hX := hXf4 x
    norm_num at hY
    nlinarith [mul_le_mul_of_nonneg_left hY.le (sub_nonneg.mpr h1),
      mul_le_mul_of_nonneg_left hX.le h0]
  have hYoout : ∀ x ∈ A, ∀ u ∈ g.finiteMinimizingDirectionsTo S x, g.inner x (Yo x) u < 0 := by
    intro x hx u hu
    have hY : g.inner x (Y x) u < 0 := by
      have := hYout x (hAO hx) u hu
      rwa [neg_zero] at this
    have hlin : g.inner x (Yo x) u = (1 - χ x) * g.inner x (Y x) u + χ x * g.inner x (Xf x) u := by
      simp only [hYodef, map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
    rw [hlin]
    obtain ⟨h0, h1⟩ := hχI x
    rcases eq_or_lt_of_le h0 with hz | hpos
    · rw [← hz]
      simpa using hY
    · have hfar : A₁ ≤ dist p x := by
        by_contra hlt
        have : χ x = 0 := hχ0 (by rw [mem_closedBall, dist_comm]; exact (not_le.mp hlt).le)
        linarith
      have hX : g.inner x (Xf x) u ≤ -(1 / 4) := hXfout x hfar u (Or.inr hu)
      exact convex_combination_lt (sub_nonneg.mpr h1) h0 (by ring) hY (by linarith)
  -- the field
  set G : (x : M) → TangentSpace I x := tubeGradField g S ψ with hGdef
  set X : (x : M) → TangentSpace I x := fun x =>
    (θ (infDist x S) * prof (infDist x S)) • G x + (1 - θ (infDist x S)) • Yo x with hXdef
  have hXin : ∀ q, infDist q S ≤ 5 * ε / 8 → X q = prof (infDist q S) • G q := by
    intro q hq
    simp only [hXdef, hθ1 _ hq, one_mul, sub_self, zero_smul, add_zero]
  have hXzero : ∀ q, infDist q S ≤ ε / 8 → X q = 0 := by
    intro q hq
    rw [hXin q (by linarith), hprof0 _ hq, zero_smul]
  have hXout : ∀ q, 3 * ε / 4 ≤ infDist q S → X q = Yo q := by
    intro q hq
    simp only [hXdef, hθ0 _ hq, zero_mul, zero_smul, zero_add, sub_zero, one_smul]
  have hopen : IsOpen {x : M | 0 < infDist x S ∧ infDist x S < ε} :=
    (isOpen_lt continuous_const hdc).inter (isOpen_lt hdc continuous_const)
  have hGs := contMDiffOn_tubeGradField g hr hnorm hψs hψ hdS
  refine ⟨X, max (A₁ + 1) (A₀ + ε), prof, lt_max_of_lt_left (by linarith), ?_, ?_, ?_, ?_,
    fun q hq0 hq => hXin q hq, hXzero, hprofC, hprof0, hprof1, hprofpos, hprofI⟩
  · -- smoothness, by three overlapping regions
    intro x
    by_cases hx1 : infDist x S < ε / 8
    · have hz : ContMDiff I I.tangent m
          (fun y => (⟨y, (0 : TangentSpace I y)⟩ : TangentBundle I M)) :=
        Bundle.contMDiff_zeroSection ℝ (TangentSpace I : M → Type _)
      apply (hz x).congr_of_eventuallyEq
      filter_upwards [hdc.continuousAt (Iio_mem_nhds hx1)] with y hy
      rw [hXzero y (le_of_lt hy)]
    by_cases hx3 : 3 * ε / 4 < infDist x S
    · apply ((hYos.of_le hm_top) x).congr_of_eventuallyEq
      filter_upwards [hdc.continuousAt (Ioi_mem_nhds hx3)] with y hy
      rw [hXout y (le_of_lt hy)]
    · have hx0 : 0 < infDist x S := by linarith [hε]
      have hxε : infDist x S < ε := by linarith
      have hxU : x ∈ {x : M | 0 < infDist x S ∧ infDist x S < ε} := ⟨hx0, hxε⟩
      have hdx : ContMDiffAt I 𝓘(ℝ, ℝ) m (fun y => infDist y S) x :=
        (hdS x hxU).contMDiffAt (hopen.mem_nhds hxU)
      have hθx : ContMDiffAt I 𝓘(ℝ, ℝ) m (fun y => θ (infDist y S)) x :=
        (hθC.of_le hm_top).comp_contMDiffAt hdx
      have hprofx : ContMDiffAt I 𝓘(ℝ, ℝ) m (fun y => prof (infDist y S)) x :=
        (hprofC.of_le hm_top).comp_contMDiffAt hdx
      have hGx : ContMDiffAt I I.tangent m (fun y => (⟨y, G y⟩ : TangentBundle I M)) x :=
        (hGs x hxU).contMDiffAt (hopen.mem_nhds hxU)
      exact ((hθx.mul hprofx).smul_section hGx).add_section
        ((contMDiffAt_const.sub hθx).smul_section ((hYos.of_le hm_top) x))
  · -- the bound
    intro x
    obtain ⟨hθ0', hθ1'⟩ := hθI (infDist x S)
    obtain ⟨hp0, hp1⟩ := hprofI (infDist x S)
    have hα : 0 ≤ θ (infDist x S) * prof (infDist x S) := mul_nonneg hθ0' hp0
    have hαβ : θ (infDist x S) * prof (infDist x S) + (1 - θ (infDist x S)) ≤ 1 := by
      nlinarith [mul_nonneg hθ0' (sub_nonneg.mpr hp1)]
    have hle : g.inner x (X x) (X x) ≤
        θ (infDist x S) * prof (infDist x S) * g.inner x (G x) (G x) +
          (1 - θ (infDist x S)) * g.inner x (Yo x) (Yo x) :=
      inner_add_smul_le_tube g x (G x) (Yo x) hα (sub_nonneg.mpr hθ1') hαβ
    have hGG : θ (infDist x S) * prof (infDist x S) * g.inner x (G x) (G x) ≤
        θ (infDist x S) * prof (infDist x S) := by
      rcases eq_or_lt_of_le hα with h | h
      · rw [← h]; simp
      · have hx0 : 0 < infDist x S := by
          by_contra hle0
          have : prof (infDist x S) = 0 := hprof0 _ (by linarith [not_lt.mp hle0])
          rw [this, mul_zero] at h
          exact lt_irrefl _ h
        have hxε : infDist x S < ε := by
          by_contra hge
          have : θ (infDist x S) = 0 := hθ0 _ (by linarith [not_lt.mp hge])
          rw [this, zero_mul] at h
          exact lt_irrefl _ h
        rw [inner_tubeGradField_self g hr hnorm hψ hx0 hxε, mul_one]
    have hY := hYo4 x
    nlinarith [mul_le_mul_of_nonneg_left hY.le (sub_nonneg.mpr hθ1'), mul_nonneg hθ0' hp0]
  · -- the point margin (LFR46.2)
    intro q hq u hu
    have hq1 : A₁ + 1 ≤ dist p q := le_trans (le_max_left _ _) hq
    have hq2 : A₀ + ε ≤ dist p q := le_trans (le_max_right _ _) hq
    have hdq : ε ≤ infDist q S := by
      rw [le_infDist hSne]
      intro y hy
      have hy' : dist y p < A₀ := hSball hy
      have htri := dist_triangle p y q
      rw [dist_comm p y, dist_comm y q] at htri
      linarith
    rw [hXout q (by linarith)]
    have hχq : χ q = 1 := hχ1 hq1
    have hYoq : Yo q = Xf q := by
      simp only [hYodef, hχq, sub_self, zero_smul, zero_add, one_smul]
    rw [hYoq]
    exact hXfout q (by linarith) u (Or.inl hu)
  · -- soul-outward on `{d_S ≥ ℓ/3}`
    intro q hq u hu
    by_cases hq3 : 3 * ε / 4 ≤ infDist q S
    · rw [hXout q hq3]
      exact hYoout q (by change 5 * ε / 8 ≤ infDist q S; linarith) u hu
    · have hq0 : 0 < infDist q S := by linarith [hε]
      have hqε : infDist q S < ε := by linarith [not_le.mp hq3]
      have hG := inner_tubeGradField_le_neg_one g hr hnorm hψ hψexp hdS hq0 hqε hu
      by_cases hq5 : infDist q S ≤ 5 * ε / 8
      · rw [hXin q hq5]
        have hpos := hprofpos _ (by linarith : ε / 8 < infDist q S)
        rw [map_smul, smul_apply, smul_eq_mul]
        nlinarith
      · have hq5' : 5 * ε / 8 < infDist q S := not_le.mp hq5
        have hp1 : prof (infDist q S) = 1 := hprof1 _ (by linarith)
        have hlin : g.inner q (X q) u = θ (infDist q S) * g.inner q (G q) u +
            (1 - θ (infDist q S)) * g.inner q (Yo q) u := by
          simp only [hXdef, hp1, mul_one, map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
        rw [hlin]
        obtain ⟨h0, h1⟩ := hθI (infDist q S)
        exact convex_combination_lt h0 (sub_nonneg.mpr h1) (by ring) (by linarith)
          (hYoout q (by change 5 * ε / 8 ≤ infDist q S; linarith) u hu)

end DifferentialGeometry.Geometry.FiniteSoul
