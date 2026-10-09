import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EventStepGood_S70
import DifferentialGeometry.Geometry.Curvature.RiemannRicciNorm

set_option autoImplicit false

/-!
# CH12-S70 / G2a: vector defect `|2 t Ric + g| ≤ η g` gives `|Rm| ≤ 189 / t`

Polarisation: if `|Ric(V,V)| ≤ c g(V,V)` for all `V` at `x` (dimension 3), the components of `Ric` in a
`g`-orthonormal basis are `≤ c`, so `|Ric| ≤ 3 c` (`sqrt_normSq0S_le_card_of_component_bound`), and
`|Rm| ≤ 63 |Ric|` (`sqrt_normSq_metricRm04_le_ricci_three`).  With `c = (1 + η)/(2 t) ≤ 1 / t` this is the
`riemannNorm ≤ K0 / t` hypothesis (`K0 = 189`) of `tracked_survives_event_of_good_S70`.
-/

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u v

theorem abs_ricci_basis_le_of_quad_S70 {P : OrientedThreeStage.{u}} (g : P.Metric) (x : P.Carrier)
    {c : ℝ}
    (hq : ∀ V : TangentSpace ThreeModel x, |ricciTensor g x V V| ≤ c * g.inner x V V)
    {ι : Type} [DecidableEq ι] (e : Module.Basis ι ℝ (TangentSpace ThreeModel x))
    (hON : ∀ i j : ι, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) (i j : ι) :
    |ricciTensor g x (e i) (e j)| ≤ c := by
  by_cases hij : i = j
  · subst hij
    have h := hq (e i)
    simpa [hON] using h
  · have hsym := fun v w : TangentSpace ThreeModel x => ricciTensor_symm g x v w
    have hgs := fun v w : TangentSpace ThreeModel x => g.symm x v w
    have h1 := hq (e i + e j)
    have h2 := hq (e i - e j)
    have gij : g.inner x (e i) (e j) = 0 := by simp [hON, hij]
    have gji : g.inner x (e j) (e i) = 0 := by rw [← hgs, gij]
    have gii : g.inner x (e i) (e i) = 1 := by simp [hON]
    have gjj : g.inner x (e j) (e j) = 1 := by simp [hON]
    have gp : g.inner x (e i + e j) (e i + e j) = 2 := by
      simp [gij, gji, gii, gjj]; norm_num
    have gm : g.inner x (e i - e j) (e i - e j) = 2 := by
      simp [gij, gji, gii, gjj]; norm_num
    have rp : ricciTensor g x (e i + e j) (e i + e j) =
        ricciTensor g x (e i) (e i) + 2 * ricciTensor g x (e i) (e j) + ricciTensor g x (e j) (e j) := by
      simp only [map_add, add_apply]
      rw [hsym (e j) (e i)]; ring
    have rm : ricciTensor g x (e i - e j) (e i - e j) =
        ricciTensor g x (e i) (e i) - 2 * ricciTensor g x (e i) (e j) + ricciTensor g x (e j) (e j) := by
      simp only [map_sub, sub_apply]
      rw [hsym (e j) (e i)]; ring
    rw [gp] at h1
    rw [gm] at h2
    rw [rp] at h1
    rw [rm] at h2
    rw [abs_le] at h1 h2 ⊢
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

theorem sqrt_normSq0S_ricci_le_of_quad_S70 {P : OrientedThreeStage.{u}} (g : P.Metric)
    (x : P.Carrier) {c : ℝ} (hc : 0 ≤ c)
    (hq : ∀ V : TangentSpace ThreeModel x, |ricciTensor g x V V| ≤ c * g.inner x V V) :
    Real.sqrt (normSq0S g x 2 (metricRicci g x)) ≤ 3 * c := by
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis (I := ThreeModel) g x
  have hdim : Module.finrank ℝ (TangentSpace ThreeModel x) = 3 := finrank_euclideanSpace_fin
  have hinv : MetricInverseInBasis (I := ThreeModel) g x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace ThreeModel x)))) := by
    intro i j
    constructor <;> simp [identityInvMetric, diagonalInvMetric, hON]
  have h := sqrt_normSq0S_le_card_of_component_bound (I := ThreeModel) g x 2 basis hinv
    (metricRicci g x) c hc (fun slots => by
      rw [component0S_apply]
      have e1 : (fun a : Fin 2 => basis (slots a)) = vec2 (basis (slots 0)) (basis (slots 1)) := by
        funext a; fin_cases a <;> rfl
      rw [e1]
      change |metricRicciAt (I := ThreeModel) g x (vec2 (basis (slots 0)) (basis (slots 1)))| ≤ c
      rw [metricRicciAt_apply_eq_ricciTensor]
      exact abs_ricci_basis_le_of_quad_S70 g x hq basis hON _ _)
  have hcard : (Fintype.card (Fin 2 → Fin (Module.finrank ℝ (TangentSpace ThreeModel x))) : ℝ) = 9 := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, hdim]; norm_num
  rw [hcard] at h
  have h9 : Real.sqrt 9 = 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rwa [h9] at h

/-- `|Ric(V,V) + g(V,V)/(2t)| ≤ (η/(2t)) g(V,V)` for all `V` and `η ≤ 1` give `|Rm| ≤ 189 / t`. -/
theorem sqrt_normSq0S_rm_le_of_defect_S70 {P : OrientedThreeStage.{u}} (g : P.Metric)
    (x : P.Carrier) {t η : ℝ} (ht : 0 < t) (hη : η ≤ 1)
    (hdef : ∀ V : TangentSpace ThreeModel x,
      |2 * t * ricciTensor g x V V + g.inner x V V| ≤ η * g.inner x V V) :
    Real.sqrt (normSq0S g x 4 (metricRm04 g x)) ≤ 189 / t := by
  have hq : ∀ V : TangentSpace ThreeModel x, |ricciTensor g x V V| ≤ (1 / t) * g.inner x V V := by
    intro V
    have h1 := hdef V
    have hg : 0 ≤ g.inner x V V := metric_inner_self_nonneg _ _ _
    have h2 : |2 * t * ricciTensor g x V V| ≤ 2 * g.inner x V V := by
      have := abs_sub_abs_le_abs_sub (2 * t * ricciTensor g x V V) (-(g.inner x V V))
      rw [abs_neg, abs_of_nonneg hg] at this
      have h3 : |2 * t * ricciTensor g x V V - -g.inner x V V| = |2 * t * ricciTensor g x V V + g.inner x V V| := by
        rw [sub_neg_eq_add]
      nlinarith [h1, h3]
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * t)] at h2
    rw [show 1 / t * g.inner x V V = g.inner x V V / t by ring, le_div_iff₀ ht]
    nlinarith [h2]
  have hRic := sqrt_normSq0S_ricci_le_of_quad_S70 g x (by positivity) hq
  have hthree := sqrt_normSq_metricRm04_le_ricci_three g x finrank_euclideanSpace_fin
  calc Real.sqrt (normSq0S g x 4 (metricRm04 g x)) ≤ 63 * (3 * (1 / t)) := hthree.trans (by linarith)
    _ = 189 / t := by ring

/-- Flow form: the vector defect at `(t, z)` bounds `G.riemannNorm t z`. -/
theorem riemannNorm_le_of_defect_S70 {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)
    {t η : ℝ} (z : P.Carrier) (ht : 0 < t) (hη : η ≤ 1)
    (hdef : ∀ V : TangentSpace ThreeModel z,
      |2 * t * ricciTensor (G.flow.base.metric t) z V V + (G.flow.base.metric t).inner z V V| ≤
        η * (G.flow.base.metric t).inner z V V) :
    G.riemannNorm t z ≤ 189 / t :=
  sqrt_normSq0S_rm_le_of_defect_S70 (G.flow.base.metric t) z ht hη hdef

/-- **Closed step at an event time, defect form (no Riemann norm in the hypotheses).**  The Weak bound is
the vector LTF03 defect `≤ η ≤ 1` at every tracked point for times `[a', τ)`; `|Rm| ≤ 189/t` is derived. -/
theorem tracked_survives_event_of_defect_S70 (K : ObservedHistory.{u}) {i : Fin K.eventCount}
    {pr : CutoffParameters} (R : GeometricCutoffRecord K i pr) {Λ η : ℝ}
    (hΛ : 1 ≤ Λ) {a' : ℝ} (ha' : a' ∈ Ico (K.time i.castSucc) (K.time i.succ)) (ha0 : 0 < a')
    (hKΛ : 2 * (9 * 189) < Λ ^ 2)
    (hδ : ∀ j, R.delta j ≤ 1 / 8646) (hnom : ∀ h, Λ * R.nominalRadius h ≤ Real.sqrt a')
    {j0 : Fin (K.eventCount + 1)} (hle : j0 ≤ i.castSucc) {X : Type v}
    (J : X → (K.stage j0).Carrier) (B : Set X)
    (hY : IsPreconnected {z | ∃ x ∈ B, TrackedAt_S70 K hle J x z})
    (hV : IsOpen {z | ∃ x ∈ B, TrackedAt_S70 K hle J x z})
    (hη : η ≤ 1)
    (hdef : ∀ z ∈ {z | ∃ x ∈ B, TrackedAt_S70 K hle J x z}, ∀ t ∈ Ico a' (K.time i.succ),
      ∀ V : TangentSpace ThreeModel z,
        |2 * t * ricciTensor ((K.event i).incoming.flow.base.metric t) z V V +
            ((K.event i).incoming.flow.base.metric t).inner z V V| ≤
          η * ((K.event i).incoming.flow.base.metric t).inner z V V)
    {x₀ : X} (hx₀ : x₀ ∈ B) {z₀ : (K.stage i.castSucc).Carrier}
    (hz₀ : TrackedAt_S70 K hle J x₀ z₀) :
    ∃ E : PartialDiffeomorph ThreeModel ThreeModel
        (K.event i).incoming.terminalRegularOpen (K.stage i.succ).Carrier ∞,
      (∀ x ∈ B, ∀ z, TrackedAt_S70 K hle J x z →
        ∃ h : z ∈ (K.event i).incoming.terminalRegularRegion,
          (⟨z, h⟩ : (K.event i).incoming.terminalRegularOpen) ∈ E.source ∧
          TrackedAt_S70 K (hle.trans i.castSucc_lt_succ.le) J x (E ⟨z, h⟩)) ∧
      ∀ z ∈ E.source, ∀ v w : TangentSpace ThreeModel z,
        (K.event i).outputMetric.inner (E z)
          (mfderiv ThreeModel ThreeModel E z v) (mfderiv ThreeModel ThreeModel E z w) =
          (K.event i).terminal.metric.inner z v w :=
  tracked_survives_event_of_good_S70 K R hΛ ha' ha0 (by norm_num) hKΛ hδ hnom hle J B hY hV
    (fun z hz t ht => riemannNorm_le_of_defect_S70 _ z (ha0.trans_le ht.1) hη (hdef z hz t ht))
    hx₀ hz₀ hη (hdef z₀ ⟨x₀, hx₀, hz₀⟩ · ·)

end GC.LongTime.Ch12
