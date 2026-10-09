import DifferentialGeometry.Geometry.Comparison.FiniteSoul.TransverseShiftParallelRegularity
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.TransverseShiftFrame
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.FiniteJacobiChartApplications
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.TransverseShiftInitial

/-!
# The Jacobi field of the transverse shift (lane CMS3-SHIFT, group G3)

For a geodesic `γ t = π φ_t p` and a `C^r` field `ξ` along it, `α(t, h) = π φ_h(γ t, ξ t)`
(`transverseShift`), and the variation field `J(h) = ∂ₜα(t₀, h)` (`transverseJacobi`) along the
transverse geodesic `σ(h) = α(t₀, h)`. For a field `W` parallel along `σ`:

* `hasDerivAt_transverseJacobi_pairing`: `j = g(J, W)` is differentiable and
  `(deriv j)' = −Rm(J, σ', σ', W)` (`finiteRm04`); proved in one chart around `σ(h₀)` from the chart
  identities of `FiniteJacobiChartApplications.lean`.
* `deriv_transverseJacobi_pairing_zero`: if `ξ` is parallel along `γ`, then `(deriv j)(0) = 0`
  (`D_h J(0) = D_t ξ = 0`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

open DifferentialGeometry.MetricKoszul (raisedKoszulOp)
open DifferentialGeometry.Analysis (coefficientRm04)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {r : ℕ∞}

local instance continuousDualEquiv_CMS3SHIFTj : DifferentialGeometry.ContinuousDualEquiv E :=
  IsCoercive.continuousDualEquivOfFiniteDimensional

local instance bilinNormedGroup_CMS3SHIFTj : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance bilinNormedSpace_CMS3SHIFTj : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- The variation field `J(h) = ∂ₜ α(t, h)` of the transverse shift at `z = (t, h)`. -/
def transverseJacobi {n : ℕ∞ω} (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (p : TangentBundle I M) (ξ : ℝ → E) (z : ℝ × ℝ) : TangentSpace I (transverseShift g p ξ z) :=
  mfderiv 𝓘(ℝ, ℝ) I (fun s => transverseShift g p ξ (s, z.2)) z.1 1

/-- The position of the transverse shift in the extended chart at `q`. -/
def transverseChartPos {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (p : TangentBundle I M)
    (ξ : ℝ → E) (q : M) (z : ℝ × ℝ) : E :=
  extChartAt I q (transverseShift g p ξ z)

/-- The `h`-velocity of the transverse shift in the tangent chart at `q`. -/
def transverseChartVel {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (p : TangentBundle I M)
    (ξ : ℝ → E) (q : M) (z : ℝ × ℝ) : E :=
  (extChartAt I.tangent (⟨q, 0⟩ : TangentBundle I M)
    (g.geodesicFlow (⟨(g.geodesicFlow p z.1).proj, ξ z.1⟩ : TangentBundle I M) z.2)).2

omit [I.Boundaryless] [T2Space M] in
theorem transverseSpeedSq_eq_inner_transverseJacobi {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (p : TangentBundle I M)
    (ξ : ℝ → E) (z : ℝ × ℝ) :
    transverseSpeedSq g p ξ z =
      g.inner (transverseShift g p ξ z) (transverseJacobi g p ξ z) (transverseJacobi g p ξ z) :=
  rfl

variable (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))

/-- **Chart data of the transverse shift** around a point whose image lies in the chart at `q`:
`C²` position and velocity, the geodesic chart equations in `h`, and the chart reading of `J`. -/
theorem transverseChart_data (hr : 2 ≤ r) (hdom : g.geodesicFlowDomain = univ)
    (p : TangentBundle I M) {ξ : ℝ → E}
    (hV : ∀ t, ContMDiffAt 𝓘(ℝ, ℝ) I.tangent r
      (fun t => (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M)) t)
    {z₀ : ℝ × ℝ} {q : M} (hq : transverseShift g p ξ z₀ ∈ (chartAt H q).source) :
    ContDiffAt ℝ 2 (transverseChartPos g p ξ q) z₀ ∧
      ContDiffAt ℝ 2 (transverseChartVel g p ξ q) z₀ ∧
      (∀ᶠ z in 𝓝 z₀, transverseShift g p ξ z ∈ (chartAt H q).source) ∧
      (∀ᶠ z in 𝓝 z₀, HasDerivAt (fun s => transverseChartPos g p ξ q (z.1, s))
        (transverseChartVel g p ξ q z) z.2) ∧
      (∀ᶠ z in 𝓝 z₀, HasDerivAt (fun s => transverseChartVel g p ξ q (z.1, s))
        (-(chartChristoffelFinite g q (transverseChartPos g p ξ q z) (transverseChartVel g p ξ q z)
          (transverseChartVel g p ξ q z))) z.2) ∧
      (∀ᶠ z in 𝓝 z₀, fderiv ℝ (transverseChartPos g p ξ q) z ((1 : ℝ), (0 : ℝ)) =
        mfderiv I 𝓘(ℝ, E) (extChartAt I q) (transverseShift g p ξ z) (transverseJacobi g p ξ z)) := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hr2 : (2 : ℕ∞ω) ≤ (r : ℕ∞ω) := by
    have h : ((2 : ℕ∞) : ℕ∞ω) ≤ (r : ℕ∞ω) := by exact_mod_cast hr
    simpa using h
  have hmem : ∀ v : TangentBundle I M × ℝ, v ∈ g.geodesicFlowDomain := fun v => by
    rw [hdom]; exact mem_univ v
  set Φ : ℝ × ℝ → TangentBundle I M := fun z =>
    g.geodesicFlow (⟨(g.geodesicFlow p z.1).proj, ξ z.1⟩ : TangentBundle I M) z.2 with hΦ
  set ψ := extChartAt I.tangent (⟨q, 0⟩ : TangentBundle I M) with hψ
  have hΦc : ∀ z, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I.tangent r Φ z := fun z =>
    contMDiffAt_transverseFlow hr1 g hdom p (hV z.1)
  have hFc : ∀ z, ContinuousAt (transverseShift g p ξ) z := fun z =>
    ((Bundle.contMDiff_proj (TangentSpace I)).contMDiffAt.comp z (hΦc z)).continuousAt
  have hev : ∀ᶠ z in 𝓝 z₀, transverseShift g p ξ z ∈ (chartAt H q).source :=
    (hFc z₀).preimage_mem_nhds ((chartAt H q).open_source.mem_nhds hq)
  have hsrc : ∀ z, transverseShift g p ξ z ∈ (chartAt H q).source →
      Φ z ∈ (chartAt (ModelProd H E) (⟨q, 0⟩ : TangentBundle I M)).source :=
    fun z hz => (TangentBundle.mem_chart_source_iff _ _).mpr hz
  have hψΦ : ∀ z, transverseShift g p ξ z ∈ (chartAt H q).source →
      ContDiffAt ℝ r (fun z => ψ (Φ z)) z := by
    intro z hz
    have h := (contMDiffAt_extChartAt' (I := I.tangent) (n := r) (hsrc z hz)).comp z (hΦc z)
    exact contMDiffAt_iff_contDiffAt.mp h
  have hfst : transverseChartPos g p ξ q = fun z => (ψ (Φ z)).1 := funext fun z =>
    (TangentBundle.extChartAt_tangent_apply_fst (⟨q, 0⟩ : TangentBundle I M)).symm
  have hsnd : transverseChartVel g p ξ q = fun z => (ψ (Φ z)).2 := rfl
  have hPosC : ∀ z, transverseShift g p ξ z ∈ (chartAt H q).source →
      ContDiffAt ℝ 2 (transverseChartPos g p ξ q) z := fun z hz => by
    rw [hfst]; exact ((hψΦ z hz).fst).of_le hr2
  have hVelC : ContDiffAt ℝ 2 (transverseChartVel g p ξ q) z₀ := by
    rw [hsnd]; exact ((hψΦ z₀ hq).snd).of_le hr2
  refine ⟨hPosC z₀ hq, hVelC, hev, ?_, ?_, ?_⟩
  · filter_upwards [hev] with z hz
    exact hasDerivAt_extChartAt_geodesicFlow hr1 g (hmem _) hz
  · filter_upwards [hev] with z hz
    have h := hasDerivAt_extChartAt_tangent_geodesicFlow hr1 g
      (hmem ((⟨(g.geodesicFlow p z.1).proj, ξ z.1⟩ : TangentBundle I M), z.2)) (q := q) hz
    unfold transverseChartPos transverseChartVel transverseShift
    exact h
  · filter_upwards [hev] with z hz
    have hF : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I (transverseShift g p ξ) z :=
      ((contMDiffAt_transverseShift g hr1 hdom p (hV z.1)).mdifferentiableAt
        (by exact_mod_cast (zero_lt_one.trans_le hr1).ne'))
    exact (fderiv_chart_comp_slice hF hz).1


/-- **The Jacobi pairing in one chart.** For `W` parallel along `σ(h) = α(t₀, h)` and `j = g(J, W)`:
`j` is differentiable at `h₀`, `(deriv j)' (h₀) = −Rm(J, σ', σ', W)`, and `(deriv j)(h₀)` is the chart
pairing `b(∂ₜV + Γ(V, ∂ₜY), W_q)` in the chart at `q = σ(h₀)`. -/
theorem hasDerivAt_transverseJacobi_pairing_chart (hr : 2 ≤ r) (hdom : g.geodesicFlowDomain = univ)
    (p : TangentBundle I M) {ξ : ℝ → E}
    (hV : ∀ t, ContMDiffAt 𝓘(ℝ, ℝ) I.tangent r
      (fun t => (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M)) t)
    (t₀ : ℝ) {W : ℝ → E}
    (hW : IsParallelAlongFinite g (fun h => (g.geodesicFlow
      (⟨(g.geodesicFlow p t₀).proj, ξ t₀⟩ : TangentBundle I M) h).proj) W univ) (h₀ : ℝ) :
    HasDerivAt (fun h => g.inner (transverseShift g p ξ (t₀, h)) (transverseJacobi g p ξ (t₀, h)) (W h))
        (deriv (fun h => g.inner (transverseShift g p ξ (t₀, h)) (transverseJacobi g p ξ (t₀, h))
          (W h)) h₀) h₀ ∧
      HasDerivAt (deriv (fun h => g.inner (transverseShift g p ξ (t₀, h))
          (transverseJacobi g p ξ (t₀, h)) (W h)))
        (-(finiteRm04 g (transverseShift g p ξ (t₀, h₀)) (transverseJacobi g p ξ (t₀, h₀))
          (g.geodesicFlow (⟨(g.geodesicFlow p t₀).proj, ξ t₀⟩ : TangentBundle I M) h₀).snd
          (g.geodesicFlow (⟨(g.geodesicFlow p t₀).proj, ξ t₀⟩ : TangentBundle I M) h₀).snd
          (W h₀))) h₀ ∧
      deriv (fun h => g.inner (transverseShift g p ξ (t₀, h)) (transverseJacobi g p ξ (t₀, h))
          (W h)) h₀ =
        chartCoeffFinite g (transverseShift g p ξ (t₀, h₀))
          (transverseChartPos g p ξ (transverseShift g p ξ (t₀, h₀)) (t₀, h₀))
          (fderiv ℝ (transverseChartVel g p ξ (transverseShift g p ξ (t₀, h₀))) (t₀, h₀)
              ((1 : ℝ), (0 : ℝ)) +
            chartChristoffelFinite g (transverseShift g p ξ (t₀, h₀))
              (transverseChartPos g p ξ (transverseShift g p ξ (t₀, h₀)) (t₀, h₀))
              (transverseChartVel g p ξ (transverseShift g p ξ (t₀, h₀)) (t₀, h₀))
              (fderiv ℝ (transverseChartPos g p ξ (transverseShift g p ξ (t₀, h₀))) (t₀, h₀)
                ((1 : ℝ), (0 : ℝ))))
          ((extChartAt I.tangent (⟨transverseShift g p ξ (t₀, h₀), 0⟩ : TangentBundle I M)
            (⟨transverseShift g p ξ (t₀, h₀), W h₀⟩ : TangentBundle I M)).2) := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hmem : ∀ v : TangentBundle I M × ℝ, v ∈ g.geodesicFlowDomain := fun v => by
    rw [hdom]; exact mem_univ v
  set p₁ : TangentBundle I M := ⟨(g.geodesicFlow p t₀).proj, ξ t₀⟩ with hp₁
  set q := transverseShift g p ξ (t₀, h₀) with hqdef
  set σ : ℝ → M := fun h => transverseShift g p ξ (t₀, h) with hσ
  set Pos := transverseChartPos g p ξ q with hPos
  set Vel := transverseChartVel g p ξ q with hVel
  set Wq : ℝ → E := fun h => (extChartAt I.tangent (⟨q, 0⟩ : TangentBundle I M)
    (⟨σ h, W h⟩ : TangentBundle I M)).2 with hWq
  set jW : ℝ → ℝ := fun h => g.inner (σ h) (transverseJacobi g p ξ (t₀, h)) (W h) with hjW
  set e₁ : ℝ × ℝ := ((1 : ℝ), (0 : ℝ)) with he₁
  set b := chartCoeffFinite g q with hb
  set A1 : ℝ → ℝ := fun s => b (Pos (t₀, s)) (fderiv ℝ Pos (t₀, s) e₁) (Wq s) with hA1
  set A2 : ℝ → ℝ := fun s => b (Pos (t₀, s))
    (fderiv ℝ Vel (t₀, s) e₁ + raisedKoszulOp (b (Pos (t₀, s))) (fderiv ℝ b (Pos (t₀, s)))
      (Vel (t₀, s)) (fderiv ℝ Pos (t₀, s) e₁)) (Wq s) with hA2
  -- the good set of times
  have hσc : Continuous σ := by
    have h := continuous_geodesicFlow_of_forall_mem hr1 g (p := p₁) (fun t => hmem _)
    exact (FiberBundle.continuous_proj E (TangentSpace I : M → Type _)).comp h
  set G : Set ℝ := σ ⁻¹' (chartAt H q).source with hG
  have hGo : IsOpen G := (chartAt H q).open_source.preimage hσc
  have hG₀ : h₀ ∈ G := mem_chart_source H q
  -- the parallel ODE of `W` in the chart
  have hWode : ∀ s ∈ G, HasDerivAt Wq
      (-(raisedKoszulOp (b (Pos (t₀, s))) (fderiv ℝ b (Pos (t₀, s))) (Vel (t₀, s)) (Wq s))) s := by
    intro s hs
    have h := (isParallelAlongFinite_geodesicFlow_iff hr1 (p := p₁) (fun τ _ => hmem _)
      (fun τ _ => uniqueDiffWithinAt_univ)).mp hW s (mem_univ s) q hs
    rw [hasDerivWithinAt_univ] at h
    exact h
  -- per-point chart computation
  have hpoint : ∀ s ∈ G, jW =ᶠ[𝓝 s] A1 ∧ HasDerivAt A1 (A2 s) s ∧
      HasDerivAt A2 (-(coefficientRm04 b (Pos (t₀, s)) (fderiv ℝ Pos (t₀, s) e₁) (Vel (t₀, s))
        (Vel (t₀, s)) (Wq s))) s := by
    intro s hs
    obtain ⟨hPC, hVC, hevS, hgY, hgV, hJq⟩ := transverseChart_data g hr hdom p hV (z₀ := (t₀, s)) hs
    obtain ⟨hbC, hbsymm, hbco⟩ := chartCoeffFinite_data hr1 g q
      ((extChartAt I q).map_source (by rw [extChartAt_source]; exact hs))
    have hcons := hasDerivAt_jacobi_pairing_of_geodesic_family (b := b) (Y := Pos) (V := Vel)
      (W := Wq) (t₀ := t₀) (h₀ := s) hbC hbsymm hbco hPC hVC hgY hgV (hWode s hs)
    refine ⟨?_, hcons.1, hcons.2⟩
    have hGs : G ∈ 𝓝 s := hGo.mem_nhds hs
    have hline : Tendsto (fun h : ℝ => ((t₀, h) : ℝ × ℝ)) (𝓝 s) (𝓝 (t₀, s)) :=
      ((continuous_const.prodMk continuous_id).tendsto s)
    filter_upwards [hGs, hline.eventually hJq] with h hh hJh
    have h1 := inner_eq_chartCoeffFinite g hh (transverseJacobi g p ξ (t₀, h)) (W h)
    have h2 := extChartAt_tangent_zero_snd_eq_mfderiv (I := I) q hh (W h)
    refine h1.trans ?_
    exact congrArg₂ (fun X Y => chartCoeffFinite g q (extChartAt I q (σ h)) X Y) hJh.symm h2.symm
  obtain ⟨hjA₀, hA1₀, hA2₀⟩ := hpoint h₀ hG₀
  have hj₀ : HasDerivAt jW (A2 h₀) h₀ := hA1₀.congr_of_eventuallyEq hjA₀
  have hderiv : deriv jW =ᶠ[𝓝 h₀] A2 := by
    filter_upwards [hGo.mem_nhds hG₀] with s hs
    obtain ⟨hjA, hA1, -⟩ := hpoint s hs
    exact (hA1.congr_of_eventuallyEq hjA).deriv
  refine ⟨hj₀.differentiableAt.hasDerivAt, ?_, hj₀.deriv⟩
  refine (hA2₀.congr_of_eventuallyEq hderiv).congr_deriv ?_
  -- identify the chart curvature with `finiteRm04`
  obtain ⟨-, -, -, -, -, hJq⟩ := transverseChart_data g hr hdom p hV (z₀ := (t₀, h₀)) hG₀
  have hq : σ h₀ ∈ (chartAt H q).source := hG₀
  have hR := finiteRm04_eq_chart hr1 g (q := q) (y := q) hq (transverseJacobi g p ξ (t₀, h₀))
    (g.geodesicFlow p₁ h₀).snd (g.geodesicFlow p₁ h₀).snd (W h₀)
  have hu : Vel (t₀, h₀) = mfderiv I 𝓘(ℝ, E) (extChartAt I q) q
      (g.geodesicFlow p₁ h₀).snd :=
    extChartAt_tangent_geodesicFlow_snd_eq g p₁ h₀ hq
  have hw : Wq h₀ = mfderiv I 𝓘(ℝ, E) (extChartAt I q) q (W h₀) :=
    extChartAt_tangent_zero_snd_eq_mfderiv (I := I) q hq (W h₀)
  have hJ0 := hJq.self_of_nhds
  rw [hR]
  congr 1
  rw [hJ0, hu, hw]
  rfl


/-- **Initial covariant derivative of the Jacobi field.** If `ξ` is parallel along `γ`, then
`D_h J(0) = D_t ξ = 0`, hence `(deriv j)(0) = 0` for every `W` parallel along `σ`. -/
theorem deriv_transverseJacobi_pairing_zero (hr : 2 ≤ r) (hdom : g.geodesicFlowDomain = univ)
    (p : TangentBundle I M) {ξ : ℝ → E}
    (hV : ∀ t, ContMDiffAt 𝓘(ℝ, ℝ) I.tangent r
      (fun t => (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M)) t)
    (hξ : IsParallelAlongFinite g (fun t => (g.geodesicFlow p t).proj) ξ univ)
    (t₀ : ℝ) {W : ℝ → E}
    (hW : IsParallelAlongFinite g (fun h => (g.geodesicFlow
      (⟨(g.geodesicFlow p t₀).proj, ξ t₀⟩ : TangentBundle I M) h).proj) W univ) :
    deriv (fun h => g.inner (transverseShift g p ξ (t₀, h)) (transverseJacobi g p ξ (t₀, h))
      (W h)) 0 = 0 := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hmem : ∀ v : TangentBundle I M × ℝ, v ∈ g.geodesicFlowDomain := fun v => by
    rw [hdom]; exact mem_univ v
  obtain ⟨-, -, hval⟩ := hasDerivAt_transverseJacobi_pairing_chart g hr hdom p hV t₀ hW 0
  rw [hval]
  set q := transverseShift g p ξ (t₀, 0) with hqdef
  set Pos := transverseChartPos g p ξ q with hPos
  set Vel := transverseChartVel g p ξ q with hVel
  set ψ := extChartAt I.tangent (⟨q, 0⟩ : TangentBundle I M) with hψ
  set e₁ : ℝ × ℝ := ((1 : ℝ), (0 : ℝ)) with he₁
  have hq0 : q = (g.geodesicFlow p t₀).proj := congrFun (transverseShift_zero g hr1 p ξ) t₀
  have hγq : (g.geodesicFlow p t₀).proj ∈ (chartAt H q).source := by
    rw [← hq0]; exact mem_chart_source H q
  have hPos0 : ∀ t, Pos (t, 0) = extChartAt I q (g.geodesicFlow p t).proj := fun t =>
    congrArg (extChartAt I q) (congrFun (transverseShift_zero g hr1 p ξ) t)
  have hVel0 : ∀ t, Vel (t, 0) =
      (ψ (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M)).2 := fun t => by
    change (ψ (g.geodesicFlow (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M) 0)).2 = _
    rw [g.geodesicFlow_zero hr1]
  obtain ⟨hPC, hVC, -, -, -, -⟩ := transverseChart_data g hr hdom p hV (z₀ := (t₀, 0))
    (mem_chart_source H q)
  have hline : HasDerivAt (fun t : ℝ => ((t, (0 : ℝ)) : ℝ × ℝ)) e₁ t₀ :=
    (hasDerivAt_id t₀).prodMk (hasDerivAt_const t₀ (0 : ℝ))
  -- `∂ₜV(t₀, 0) = −Γ(γ', ξ)` (ξ parallel)
  have hK1 : HasDerivAt (fun t => Vel (t, 0)) (fderiv ℝ Vel (t₀, 0) e₁) t₀ := by
    have h := ((hVC.differentiableAt (by norm_num)).hasFDerivAt).comp_hasDerivAt t₀ hline
    exact h
  have hK2 : HasDerivAt (fun t => Vel (t, 0))
      (-(chartChristoffelFinite g q (extChartAt I q (g.geodesicFlow p t₀).proj)
        (ψ (g.geodesicFlow p t₀)).2
        (ψ (⟨(g.geodesicFlow p t₀).proj, ξ t₀⟩ : TangentBundle I M)).2)) t₀ := by
    have h := (isParallelAlongFinite_geodesicFlow_iff hr1 (p := p) (fun τ _ => hmem _)
      (fun τ _ => uniqueDiffWithinAt_univ)).mp hξ t₀ (mem_univ t₀) q hγq
    rw [hasDerivWithinAt_univ] at h
    have hfun : (fun t => Vel (t, 0)) = fun τ =>
        (ψ (⟨(g.geodesicFlow p τ).proj, ξ τ⟩ : TangentBundle I M)).2 := funext hVel0
    rw [hfun]
    exact h
  -- `∂ₜY(t₀, 0) = γ'(t₀)`
  have hJ1 : HasDerivAt (fun t => Pos (t, 0)) (fderiv ℝ Pos (t₀, 0) e₁) t₀ := by
    have h := ((hPC.differentiableAt (by norm_num)).hasFDerivAt).comp_hasDerivAt t₀ hline
    exact h
  have hJ2 : HasDerivAt (fun t => Pos (t, 0)) (ψ (g.geodesicFlow p t₀)).2 t₀ := by
    have hfun : (fun t => Pos (t, 0)) = fun τ => extChartAt I q (g.geodesicFlow p τ).proj :=
      funext hPos0
    rw [hfun]
    exact hasDerivAt_extChartAt_geodesicFlow hr1 g (hmem _) hγq
  have hK := hK1.unique hK2
  have hJ := hJ1.unique hJ2
  -- symmetry of `Γ` at the base point
  have hx : extChartAt I q (g.geodesicFlow p t₀).proj ∈ (extChartAt I q).target :=
    (extChartAt I q).map_source (by rw [extChartAt_source]; exact hγq)
  obtain ⟨hbC, hbsymm, hbco⟩ := chartCoeffFinite_data hr1 g q hx
  obtain ⟨hΓsym, -, -⟩ := koszul_christoffel_data hbC hbsymm hbco
  have hzero : fderiv ℝ Vel (t₀, 0) e₁ + chartChristoffelFinite g q (Pos (t₀, 0)) (Vel (t₀, 0))
      (fderiv ℝ Pos (t₀, 0) e₁) = 0 := by
    rw [hK, hJ, hPos0 t₀, hVel0 t₀]
    rw [show chartChristoffelFinite g q (extChartAt I q (g.geodesicFlow p t₀).proj)
        (ψ (⟨(g.geodesicFlow p t₀).proj, ξ t₀⟩ : TangentBundle I M)).2
        (ψ (g.geodesicFlow p t₀)).2 =
      chartChristoffelFinite g q (extChartAt I q (g.geodesicFlow p t₀).proj)
        (ψ (g.geodesicFlow p t₀)).2
        (ψ (⟨(g.geodesicFlow p t₀).proj, ξ t₀⟩ : TangentBundle I M)).2 from
      hΓsym.self_of_nhds _ _]
    exact neg_add_cancel _
  rw [hzero, map_zero, zero_apply]

end DifferentialGeometry.Geometry.FiniteSoul
