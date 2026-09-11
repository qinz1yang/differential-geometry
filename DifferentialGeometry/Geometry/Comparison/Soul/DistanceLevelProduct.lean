import DifferentialGeometry.Geometry.Comparison.Soul.DistanceEscape

set_option autoImplicit false
noncomputable section

open Bundle Filter Function Manifold Set
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry.Topology

section LevelProduct

variable {X : Type*} [TopologicalSpace X]

private theorem level_strict_shift
    (ϕ : Flow ℝ X) (f : X → ℝ) (R : ℝ)
    (hinc : ∀ x : X, R ≤ f x → ∀ t : ℝ, 0 < t → f x < f (ϕ t x))
    (x : X) (a z : ℝ) (haz : a < z) (ha : R ≤ f (ϕ a x)) :
    f (ϕ a x) < f (ϕ z x) := by
  have hh := hinc (ϕ a x) ha (z - a) (sub_pos.mpr haz)
  rwa [← ϕ.map_add, sub_add_cancel] at hh

private theorem level_le_shift
    (ϕ : Flow ℝ X) (f : X → ℝ) (R : ℝ)
    (hinc : ∀ x : X, R ≤ f x → ∀ t : ℝ, 0 < t → f x < f (ϕ t x))
    (x : X) (a z : ℝ) (haz : a ≤ z) (ha : R ≤ f (ϕ a x)) :
    f (ϕ a x) ≤ f (ϕ z x) := by
  rcases lt_or_eq_of_le haz with haz | rfl
  · exact (level_strict_shift ϕ f R hinc x a z haz ha).le
  · exact le_rfl

theorem existsUnique_levelTime_of_annular_growth
    (ϕ : Flow ℝ X) (f : X → ℝ) (hf : Continuous f) (R : ℝ)
    (hinc : ∀ x : X, R ≤ f x → ∀ t : ℝ, 0 < t → f x < f (ϕ t x))
    (hann : ∀ U : ℝ, ∃ c : ℝ, 0 < c ∧ ∀ (x : X) (a z : ℝ), a ≤ z →
      (∀ t ∈ Ioc a z, R ≤ f (ϕ t x) ∧ f (ϕ t x) ≤ U) →
      c * (z - a) ≤ f (ϕ z x) - f (ϕ a x))
    (x : X) (hx : R ≤ f x) (r : ℝ) (hr : R ≤ r) :
    ∃! t : ℝ, f (ϕ t x) = r := by
  obtain ⟨c, hc, hg⟩ := hann (max (f x) r)
  let A : ℝ := (|f x - r| + 1) / c
  have hA : 0 < A := div_pos (by positivity) hc
  have hcA : c * A = |f x - r| + 1 := by dsimp only [A]; field_simp
  have hright : r ≤ f (ϕ A x) := by
    by_contra h
    have hlt : f (ϕ A x) < r := lt_of_not_ge h
    have hh := hg x 0 A hA.le (by
      intro t ht
      have htR : R ≤ f (ϕ t x) := hx.trans (hinc x hx t ht.1).le
      have htA := level_le_shift ϕ f R hinc x t A ht.2 htR
      exact ⟨htR, htA.trans (hlt.le.trans (le_max_right _ _))⟩)
    rw [sub_zero, ϕ.map_zero_apply, hcA] at hh
    have hrightabs := neg_abs_le (f x - r)
    linarith only [hh, hlt, hrightabs]
  have hleft : f (ϕ (-A) x) ≤ r := by
    by_contra h
    have hgt : r < f (ϕ (-A) x) := lt_of_not_ge h
    have hleftR : R ≤ f (ϕ (-A) x) := hr.trans hgt.le
    have hh := hg x (-A) 0 (by linarith) (by
      intro t ht
      have htR : R ≤ f (ϕ t x) := hleftR.trans
        (level_strict_shift ϕ f R hinc x (-A) t ht.1 hleftR).le
      have ht0 := level_le_shift ϕ f R hinc x t 0 ht.2 htR
      rw [ϕ.map_zero_apply] at ht0
      exact ⟨htR, ht0.trans (le_max_left _ _)⟩)
    rw [zero_sub, neg_neg, ϕ.map_zero_apply, hcA] at hh
    have hleftabs := le_abs_self (f x - r)
    linarith only [hh, hgt, hleftabs]
  have hcont : Continuous (fun t : ℝ => f (ϕ t x)) :=
    hf.comp (ϕ.continuous continuous_id continuous_const)
  obtain ⟨t, _, ht⟩ := intermediate_value_Icc (by linarith : -A ≤ A)
    hcont.continuousOn ⟨hleft, hright⟩
  change f (ϕ t x) = r at ht
  refine ⟨t, ht, ?_⟩
  intro u hu
  rcases lt_trichotomy u t with hut | hut | htu
  · have hh := level_strict_shift ϕ f R hinc x u t hut (hu.symm ▸ hr)
    rw [hu, ht] at hh
    exact (lt_irrefl r hh).elim
  · exact hut
  · have hh := level_strict_shift ϕ f R hinc x t u htu (ht.symm ▸ hr)
    rw [hu, ht] at hh
    exact (lt_irrefl r hh).elim

theorem exists_levelProduct_of_annular_growth
    (ϕ : Flow ℝ X) (f : X → ℝ) (hf : Continuous f) (R : ℝ)
    (hinc : ∀ x : X, R ≤ f x → ∀ t : ℝ, 0 < t → f x < f (ϕ t x))
    (hann : ∀ U : ℝ, ∃ c : ℝ, 0 < c ∧ ∀ (x : X) (a z : ℝ), a ≤ z →
      (∀ t ∈ Ioc a z, R ≤ f (ϕ t x) ∧ f (ϕ t x) ≤ U) →
      c * (z - a) ≤ f (ϕ z x) - f (ϕ a x))
    (s : ℝ) (hs : R ≤ s) (T : Set ℝ) (hT : ∀ r ∈ T, R ≤ r) :
    ∃ e : {x : X | f x ∈ T} ≃ₜ {x : X | f x = s} × T,
      (∀ x, (e x).2.1 = f x.1) ∧
      ∀ (x : {x : X | f x = s}) (hsT : s ∈ T), (e.symm (x, ⟨s, hsT⟩)).1 = x.1 := by
  classical
  have hunique (x : X) (r : ℝ) (hr : R ≤ r) (a z : ℝ)
      (ha : f (ϕ a x) = r) (hz : f (ϕ z x) = r) : a = z := by
    rcases lt_trichotomy a z with haz | haz | hza
    · have hh := level_strict_shift ϕ f R hinc x a z haz (ha.symm ▸ hr)
      rw [ha, hz] at hh
      exact (lt_irrefl r hh).elim
    · exact haz
    · have hh := level_strict_shift ϕ f R hinc x z a hza (hz.symm ▸ hr)
      rw [ha, hz] at hh
      exact (lt_irrefl r hh).elim
  have hexists (x : {x : X | R ≤ f x}) (r : {r : ℝ | R ≤ r}) :
      ∃ t : ℝ, f (ϕ t x.1) = r.1 :=
    (existsUnique_levelTime_of_annular_growth ϕ f hf R hinc hann x.1 x.2 r.1 r.2).exists
  choose τ hτ using hexists
  have hbefore (x : {x : X | R ≤ f x}) (r : {r : ℝ | R ≤ r}) (a : ℝ)
      (ha : a < τ x r) : f (ϕ a x.1) < r.1 := by
    by_contra h
    have hge := le_of_not_gt h
    have hh := level_strict_shift ϕ f R hinc x.1 a (τ x r) ha (r.2.trans hge)
    rw [hτ] at hh
    exact (not_lt_of_ge hge) hh
  have hafter (x : {x : X | R ≤ f x}) (r : {r : ℝ | R ≤ r}) (z : ℝ)
      (hz : τ x r < z) : r.1 < f (ϕ z x.1) := by
    have hh := level_strict_shift ϕ f R hinc x.1 (τ x r) z hz ((hτ x r).symm ▸ r.2)
    rwa [hτ] at hh
  have hτc : Continuous (fun z : {x : X | R ≤ f x} × {r : ℝ | R ≤ r} => τ z.1 z.2) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    apply tendsto_order.mpr
    constructor
    · intro a ha
      have hdiff : Continuous (fun w : {x : X | R ≤ f x} × {r : ℝ | R ≤ r} =>
          w.2.1 - f (ϕ a w.1.1)) :=
        (continuous_subtype_val.comp continuous_snd).sub
          (hf.comp (ϕ.continuous continuous_const (continuous_subtype_val.comp continuous_fst)))
      have hpos := hdiff.continuousAt.eventually
        (lt_mem_nhds (sub_pos.mpr (hbefore z.1 z.2 a ha)))
      filter_upwards [hpos] with w hw
      by_contra h
      have hh := level_le_shift ϕ f R hinc w.1.1 (τ w.1 w.2) a (le_of_not_gt h)
        ((hτ w.1 w.2).symm ▸ w.2.2)
      rw [hτ] at hh
      linarith only [hw, hh]
    · intro z' hz'
      have hdiff : Continuous (fun w : {x : X | R ≤ f x} × {r : ℝ | R ≤ r} =>
          f (ϕ z' w.1.1) - w.2.1) :=
        (hf.comp (ϕ.continuous continuous_const (continuous_subtype_val.comp continuous_fst))).sub
          (continuous_subtype_val.comp continuous_snd)
      have hpos := hdiff.continuousAt.eventually
        (lt_mem_nhds (sub_pos.mpr (hafter z.1 z.2 z' hz')))
      filter_upwards [hpos] with w hw
      by_contra h
      have hw' : w.2.1 < f (ϕ z' w.1.1) := by linarith only [hw]
      have hh := level_le_shift ϕ f R hinc w.1.1 z' (τ w.1 w.2) (le_of_not_gt h)
        (w.2.2.trans hw'.le)
      rw [hτ] at hh
      exact (not_lt_of_ge hh) hw'
  let P : {x : X | R ≤ f x} → {r : ℝ | R ≤ r} → {x : X | R ≤ f x} :=
    fun x r => ⟨ϕ (τ x r) x.1, by change R ≤ f (ϕ (τ x r) x.1); rw [hτ]; exact r.2⟩
  have hPc : Continuous (fun z : {x : X | R ≤ f x} × {r : ℝ | R ≤ r} => P z.1 z.2) :=
    (ϕ.continuous hτc (continuous_subtype_val.comp continuous_fst)).subtype_mk _
  have hPval (x) (r) : f (P x r).1 = r.1 := hτ x r
  have hPself (x : {x : X | R ≤ f x}) : P x ⟨f x.1, x.2⟩ = x := by
    apply Subtype.ext
    have hh := hunique x.1 (f x.1) x.2 (τ x ⟨f x.1, x.2⟩) 0
      (hτ _ _) (by rw [ϕ.map_zero_apply])
    change ϕ (τ x ⟨f x.1, x.2⟩) x.1 = x.1
    rw [hh, ϕ.map_zero_apply]
  have hPcomp (x) (r u) : P (P x r) u = P x u := by
    apply Subtype.ext
    change ϕ (τ (P x r) u) (ϕ (τ x r) x.1) = ϕ (τ x u) x.1
    rw [← ϕ.map_add]
    congr 1
    apply hunique x.1 u.1 u.2
    · rw [ϕ.map_add]
      exact hτ (P x r) u
    · exact hτ x u
  let qs : {r : ℝ | R ≤ r} := ⟨s, hs⟩
  let A : {x : X | f x ∈ T} → {x : X | R ≤ f x} := fun x => ⟨x.1, hT _ x.2⟩
  let B : {x : X | f x = s} → {x : X | R ≤ f x} :=
    fun x => ⟨x.1, by change R ≤ f x.1; rw [x.2]; exact hs⟩
  let C : T → {r : ℝ | R ≤ r} := fun r => ⟨r.1, hT _ r.2⟩
  have hAc : Continuous A := continuous_subtype_val.subtype_mk _
  have hBc : Continuous B := continuous_subtype_val.subtype_mk _
  have hCc : Continuous C := continuous_subtype_val.subtype_mk _
  let e : {x : X | f x ∈ T} ≃ₜ {x : X | f x = s} × T := {
    toFun := fun x => (⟨(P (A x) qs).1, hPval _ _⟩, ⟨f x.1, x.2⟩)
    invFun := fun z => ⟨(P (B z.1) (C z.2)).1, by
      change f (P (B z.1) (C z.2)).1 ∈ T
      rw [hPval]
      exact z.2.2⟩
    left_inv := by
      intro x
      apply Subtype.ext
      change (P (P (A x) qs) ⟨f (A x).1, (A x).2⟩).1 = x.1
      rw [hPcomp, hPself]
    right_inv := by
      intro z
      apply Prod.ext
      · apply Subtype.ext
        change (P (P (B z.1) (C z.2)) qs).1 = z.1.1
        rw [hPcomp]
        have hqs : qs = ⟨f (B z.1).1, (B z.1).2⟩ := Subtype.ext z.1.2.symm
        rw [hqs, hPself]
      · apply Subtype.ext
        exact hPval _ _
    continuous_toFun :=
      ((continuous_subtype_val.comp (hPc.comp (hAc.prodMk continuous_const))).subtype_mk _).prodMk
        ((hf.comp continuous_subtype_val).subtype_mk _)
    continuous_invFun :=
      (continuous_subtype_val.comp (hPc.comp
        ((hBc.comp continuous_fst).prodMk (hCc.comp continuous_snd)))).subtype_mk (fun z => by
          change f (P (B z.1) (C z.2)).1 ∈ T
          rw [hPval]
          exact z.2.2) }
  refine ⟨e, fun _ => rfl, ?_⟩
  intro x hsT
  change (P (B x) (C ⟨s, hsT⟩)).1 = x.1
  have hcs : C ⟨s, hsT⟩ = ⟨f (B x).1, (B x).2⟩ := Subtype.ext x.2.symm
  rw [hcs, hPself]

end LevelProduct

section Riemannian

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

private theorem infDist_flow_growth_data
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {S : Set M} (hS : IsCompact S) (hSne : S.Nonempty)
    (V : (x : M) → TangentSpace I x)
    (hV : Continuous (fun x => (⟨x, V x⟩ : TangentBundle I M)))
    (ϕ : Flow ℝ M) (hϕ : ∀ q, IsMIntegralCurve (fun t => ϕ t q) V)
    {b : ℝ} (hb : 0 < b)
    (hout : ∀ q : M, b ≤ Metric.infDist q S → ∀ u : TangentSpace I q, g.inner q u u = 1 →
      intrinsicGeodesic g hEnorm q u (Metric.infDist q S) ∈ S → g.inner q (V q) u < 0) :
    (∀ q : M, b ≤ Metric.infDist q S → ∀ t : ℝ, 0 < t →
      Metric.infDist q S < Metric.infDist (ϕ t q) S) ∧
    (∀ R : ℝ, ∃ c : ℝ, 0 < c ∧ ∀ (q : M) (a z : ℝ), a ≤ z →
      (∀ t ∈ Ioc a z, b ≤ Metric.infDist (ϕ t q) S ∧ Metric.infDist (ϕ t q) S ≤ R) →
      c * (z - a) ≤ Metric.infDist (ϕ z q) S - Metric.infDist (ϕ a q) S) := by
  constructor
  · intro q hq t ht
    have hstart : b ≤ Metric.infDist (ϕ 0 q) S := by rwa [ϕ.map_zero_apply]
    have hm := infDist_strictMonoOn_of_outward_integralCurve g hEnorm hS hSne V hV (hϕ q)
      hb hout hstart
    have hh := hm (by change (0 : ℝ) ≤ 0; exact le_rfl) ht.le ht
    simpa only [ϕ.map_zero_apply] using hh
  · intro R
    obtain ⟨c, hc, hg⟩ := exists_infDist_annulus_growth_rate g hEnorm hS hSne V hV hb hout R
    exact ⟨c, hc, fun q a z haz hann => hg (fun t => ϕ t q) (hϕ q) a z haz hann⟩

theorem existsUnique_infDist_levelTime
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {S : Set M} (hS : IsCompact S) (hSne : S.Nonempty)
    (V : (x : M) → TangentSpace I x)
    (hV : Continuous (fun x => (⟨x, V x⟩ : TangentBundle I M)))
    (ϕ : Flow ℝ M) (hϕ : ∀ q, IsMIntegralCurve (fun t => ϕ t q) V)
    {b : ℝ} (hb : 0 < b)
    (hout : ∀ q : M, b ≤ Metric.infDist q S → ∀ u : TangentSpace I q, g.inner q u u = 1 →
      intrinsicGeodesic g hEnorm q u (Metric.infDist q S) ∈ S → g.inner q (V q) u < 0)
    (q : M) (hq : b ≤ Metric.infDist q S) (r : ℝ) (hr : b ≤ r) :
    ∃! t : ℝ, Metric.infDist (ϕ t q) S = r := by
  obtain ⟨hinc, hann⟩ := infDist_flow_growth_data g hEnorm hS hSne V hV ϕ hϕ hb hout
  exact existsUnique_levelTime_of_annular_growth ϕ (fun q => Metric.infDist q S)
    (Metric.continuous_infDist_pt S) b hinc hann q hq r hr

theorem exists_nonpos_infDist_levelTime
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {S : Set M} (hS : IsCompact S) (hSne : S.Nonempty)
    (V : (x : M) → TangentSpace I x)
    (hV : Continuous (fun x => (⟨x, V x⟩ : TangentBundle I M)))
    (ϕ : Flow ℝ M) (hϕ : ∀ q, IsMIntegralCurve (fun t => ϕ t q) V)
    {b : ℝ} (hb : 0 < b)
    (hout : ∀ q : M, b ≤ Metric.infDist q S → ∀ u : TangentSpace I q, g.inner q u u = 1 →
      intrinsicGeodesic g hEnorm q u (Metric.infDist q S) ∈ S → g.inner q (V q) u < 0)
    (q : M) (hq : b ≤ Metric.infDist q S) (r : ℝ) (hr : b ≤ r) (hrq : r ≤ Metric.infDist q S) :
    ∃ t : ℝ, t ≤ 0 ∧ Metric.infDist (ϕ t q) S = r ∧
      ∀ z : ℝ, Metric.infDist (ϕ z q) S = r → z = t := by
  obtain ⟨t, ht, hunique⟩ := existsUnique_infDist_levelTime g hEnorm hS hSne V hV ϕ hϕ hb hout q hq r hr
  refine ⟨t, ?_, ht, hunique⟩
  by_contra h
  have hinc := (infDist_flow_growth_data g hEnorm hS hSne V hV ϕ hϕ hb hout).1
  have hh := hinc q hq t (lt_of_not_ge h)
  rw [ht] at hh
  exact (not_lt_of_ge hrq) hh

theorem exists_infDist_levelProduct_of_flow
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {S : Set M} (hS : IsCompact S) (hSne : S.Nonempty)
    (V : (x : M) → TangentSpace I x)
    (hV : Continuous (fun x => (⟨x, V x⟩ : TangentBundle I M)))
    (ϕ : Flow ℝ M) (hϕ : ∀ q, IsMIntegralCurve (fun t => ϕ t q) V)
    {b : ℝ} (hb : 0 < b)
    (hout : ∀ q : M, b ≤ Metric.infDist q S → ∀ u : TangentSpace I q, g.inner q u u = 1 →
      intrinsicGeodesic g hEnorm q u (Metric.infDist q S) ∈ S → g.inner q (V q) u < 0)
    (s : ℝ) (hs : b ≤ s) (T : Set ℝ) (hT : ∀ r ∈ T, b ≤ r) :
    ∃ e : {q : M | Metric.infDist q S ∈ T} ≃ₜ {q : M | Metric.infDist q S = s} × T,
      (∀ q, (e q).2.1 = Metric.infDist q.1 S) ∧
      ∀ (q : {q : M | Metric.infDist q S = s}) (hsT : s ∈ T),
        (e.symm (q, ⟨s, hsT⟩)).1 = q.1 := by
  obtain ⟨hinc, hann⟩ := infDist_flow_growth_data g hEnorm hS hSne V hV ϕ hϕ hb hout
  exact exists_levelProduct_of_annular_growth ϕ (fun q => Metric.infDist q S)
    (Metric.continuous_infDist_pt S) b hinc hann s hs T hT

theorem exists_infDist_exteriorProduct
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {S : Set M} (hS : IsCompact S) (hSne : S.Nonempty)
    (V : Cₛ^∞⟮I; E, TangentSpace I⟯) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ q, g.inner q (V q) (V q) ≤ C ^ 2) {b : ℝ} (hb : 0 < b)
    (hout : ∀ q : M, b ≤ Metric.infDist q S → ∀ u : TangentSpace I q, g.inner q u u = 1 →
      intrinsicGeodesic g hEnorm q u (Metric.infDist q S) ∈ S → g.inner q (V q) u < 0) :
    ∃ e : {q : M | b ≤ Metric.infDist q S} ≃ₜ {q : M | Metric.infDist q S = b} × Ici b,
      (∀ q, (e q).2.1 = Metric.infDist q.1 S) ∧
      ∀ q : {q : M | Metric.infDist q S = b},
        (e.symm (q, ⟨b, by change b ≤ b; exact le_rfl⟩)).1 = q.1 := by
  have hcomplete := exists_globalIntegralCurve_of_bounded g hEnorm V C hC hbound
  let ϕ : Flow ℝ M := completeFieldFlow V hcomplete
  have hϕ : ∀ q, IsMIntegralCurve (fun t => ϕ t q) V := fun q => curveAt_integralCurve V hcomplete q
  obtain ⟨e, hheight, hbase⟩ := exists_infDist_levelProduct_of_flow g hEnorm hS hSne V
    V.contMDiff.continuous ϕ hϕ hb hout b le_rfl (Ici b) (fun _ hr => hr)
  exact ⟨e, hheight, fun q => hbase q (by change b ≤ b; exact le_rfl)⟩

end Riemannian

end DifferentialGeometry.Geometry.Topology
