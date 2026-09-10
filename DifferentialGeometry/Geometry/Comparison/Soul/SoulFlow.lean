import DifferentialGeometry.Geometry.Comparison.Soul.SoulAngles
import Mathlib.Dynamics.Flow

set_option autoImplicit false

noncomputable section

open Bundle Filter Function Manifold Set
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry.Topology

open DifferentialGeometry.Analysis.ODE

section CompleteFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem contMDiff_curveAt_joint
    (V : Cₛ^∞⟮I; E, TangentSpace I⟯)
    (hc : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ V) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun z : ℝ × M => curveAt V hc z.2 z.1) := by
  have hv1 := V.contMDiff.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by norm_num)
  have hs (t : ℝ) : ContMDiff I I ∞ (fun x : M => curveAt V hc x t) := by
    have hh := flow_slice_smooth V V.contMDiff (D := univ) isOpen_univ
      (a := -(|t| + 1)) (b := |t| + 1) (t₀ := 0) (by constructor <;> linarith [abs_nonneg t])
      (F := fun x s => curveAt V hc x s)
      (fun x _ => curveAt_zero V hc x)
      (fun x _ => (curveAt_integralCurve V hc x).continuous.continuousOn)
      (fun x _ s _ => curveAt_integralCurve V hc x s)
    exact contMDiffOn_univ.mp (hh t (by constructor <;> linarith [le_abs_self t, neg_abs_le t]))
  rintro ⟨t, x⟩
  obtain ⟨U, hU, hxU, ε, hε, Φ, hinit, hsm, hint⟩ :=
    local_flow_jointSmooth_and_integralCurve (I := I) (fun _ : ℝ => (V : (x : M) → TangentSpace I x))
      (V.contMDiff.comp contMDiff_snd) 0 (curveAt V hc x t)
  simp only [zero_sub, zero_add] at hsm hint
  have hagree (y : M) (hy : y ∈ U) (s : ℝ) (hs : s ∈ Ioo (-ε) ε) :
      curveAt V hc y s = Φ y s := by
    have hh := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
      (t₀ := 0) (a := -ε) (b := ε) (by constructor <;> linarith) hv1
      ((curveAt_integralCurve V hc y).isMIntegralCurveOn _)
      (show IsMIntegralCurveOn (Φ y) V (Ioo (-ε) ε) from
        fun s hs => (hint y hy s hs).hasMFDerivWithinAt)
      (by rw [curveAt_zero]; exact (hinit y hy).symm)
    exact hh hs
  let G : ℝ × M → ℝ × M := fun z => (z.1 - t, curveAt V hc z.2 t)
  have hG : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞ G :=
    (contMDiff_fst.sub contMDiff_const).prodMk ((hs t).comp contMDiff_snd)
  have hGmem : G (t, x) ∈ Ioo (-ε) ε ×ˢ U := by
    exact ⟨by simp only [G, sub_self, mem_Ioo]; constructor <;> linarith, hxU⟩
  have hΦat := (hsm (G (t, x)) hGmem).contMDiffAt
    ((isOpen_Ioo.prod hU).mem_nhds hGmem)
  have hcomp := hΦat.comp (t, x) hG.contMDiffAt
  have hnbd : ∀ᶠ z in 𝓝 (t, x), G z ∈ Ioo (-ε) ε ×ˢ U :=
    hG.continuous.continuousAt.eventually ((isOpen_Ioo.prod hU).mem_nhds hGmem)
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [hnbd] with z hz
  change curveAt V hc z.2 z.1 = Φ (curveAt V hc z.2 t) (z.1 - t)
  rw [← hagree _ hz.2 _ hz.1, ← curveAt_add V hv1 hc, add_sub_cancel]


def completeFieldFlow (V : Cₛ^∞⟮I; E, TangentSpace I⟯)
    (hc : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ V) : Flow ℝ M where
  toFun t x := curveAt V hc x t
  cont' := (contMDiff_curveAt_joint V hc).continuous
  map_add' s t x := by
    rw [add_comm s t]
    exact curveAt_add V (V.contMDiff.of_le (by norm_num)) hc x t s
  map_zero' := curveAt_zero V hc

end CompleteFlow

section LevelProduct

variable {X : Type*} [TopologicalSpace X]

theorem nonempty_levelProduct_of_escape
    (ϕ : Flow ℝ X) (f : X → ℝ) (hf : Continuous f) (R c : ℝ) (hc : 0 < c)
    (hg : ∀ x : X, R < f x → ∀ t : ℝ, 0 ≤ t → f x + c * t ≤ f (ϕ t x))
    (s : ℝ) (hs : R < s) (T : Set ℝ) (hT : ∀ r ∈ T, R < r) :
    Nonempty ({x : X | f x ∈ T} ≃ₜ {x : X | f x = s} × T) := by
  classical
  have hshift (x : X) (a b : ℝ) (hab : a ≤ b) (ha : R < f (ϕ a x)) :
      f (ϕ a x) + c * (b - a) ≤ f (ϕ b x) := by
    have hh := hg (ϕ a x) ha (b - a) (sub_nonneg.mpr hab)
    rwa [← ϕ.map_add, sub_add_cancel] at hh
  have hunique (x : X) (r : ℝ) (hr : R < r) (a b : ℝ)
      (ha : f (ϕ a x) = r) (hb : f (ϕ b x) = r) : a = b := by
    rcases lt_trichotomy a b with hab | hab | hba
    · have hh := hshift x a b hab.le (ha.symm ▸ hr)
      rw [ha, hb] at hh
      have := mul_pos hc (sub_pos.mpr hab)
      linarith
    · exact hab
    · have hh := hshift x b a hba.le (hb.symm ▸ hr)
      rw [ha, hb] at hh
      have := mul_pos hc (sub_pos.mpr hba)
      linarith
  have hexists (x : {x : X | R < f x}) (r : {r : ℝ | R < r}) :
      ∃ t : ℝ, f (ϕ t x.1) = r.1 := by
    let A : ℝ := (|f x.1 - r.1| + 1) / c
    have hA : 0 < A := div_pos (by positivity) hc
    have hcA : c * A = |f x.1 - r.1| + 1 := by dsimp only [A]; field_simp
    have hright : r.1 ≤ f (ϕ A x.1) := by
      have hh := hg x.1 x.2 A hA.le
      rw [hcA] at hh
      linarith [neg_abs_le (f x.1 - r.1)]
    have hleft : f (ϕ (-A) x.1) ≤ r.1 := by
      by_contra h
      have hgt : r.1 < f (ϕ (-A) x.1) := lt_of_not_ge h
      have hh := hg (ϕ (-A) x.1) (r.2.trans hgt) A hA.le
      rw [← ϕ.map_add, add_neg_cancel, ϕ.map_zero_apply, hcA] at hh
      linarith [le_abs_self (f x.1 - r.1)]
    have hcont : Continuous (fun t : ℝ => f (ϕ t x.1)) :=
      hf.comp (ϕ.continuous continuous_id continuous_const)
    obtain ⟨t, _, ht⟩ := intermediate_value_Icc (by linarith : -A ≤ A)
      hcont.continuousOn ⟨hleft, hright⟩
    exact ⟨t, ht⟩
  choose τ hτ using hexists
  have hbefore (x : {x : X | R < f x}) (r : {r : ℝ | R < r}) (a : ℝ)
      (ha : a < τ x r) : f (ϕ a x.1) < r.1 := by
    by_contra h
    have hh := hshift x.1 a (τ x r) ha.le (r.2.trans_le (le_of_not_gt h))
    rw [hτ] at hh
    have := mul_pos hc (sub_pos.mpr ha)
    linarith
  have hafter (x : {x : X | R < f x}) (r : {r : ℝ | R < r}) (b : ℝ)
      (hb : τ x r < b) : r.1 < f (ϕ b x.1) := by
    have hh := hshift x.1 (τ x r) b hb.le ((hτ x r).symm ▸ r.2)
    rw [hτ] at hh
    have := mul_pos hc (sub_pos.mpr hb)
    linarith
  have hτc : Continuous (fun z : {x : X | R < f x} × {r : ℝ | R < r} => τ z.1 z.2) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    apply tendsto_order.mpr
    constructor
    · intro a ha
      have hdiff : Continuous (fun w : {x : X | R < f x} × {r : ℝ | R < r} =>
          w.2.1 - f (ϕ a w.1.1)) :=
        (continuous_subtype_val.comp continuous_snd).sub
          (hf.comp (ϕ.continuous continuous_const (continuous_subtype_val.comp continuous_fst)))
      have hpos := hdiff.continuousAt.eventually
        (lt_mem_nhds (sub_pos.mpr (hbefore z.1 z.2 a ha)))
      filter_upwards [hpos] with w hw
      by_contra h
      have hh := hshift w.1.1 (τ w.1 w.2) a (le_of_not_gt h) ((hτ w.1 w.2).symm ▸ w.2.2)
      rw [hτ] at hh
      have := mul_nonneg hc.le (sub_nonneg.mpr (le_of_not_gt h))
      linarith
    · intro b hb
      have hdiff : Continuous (fun w : {x : X | R < f x} × {r : ℝ | R < r} =>
          f (ϕ b w.1.1) - w.2.1) :=
        (hf.comp (ϕ.continuous continuous_const (continuous_subtype_val.comp continuous_fst))).sub
          (continuous_subtype_val.comp continuous_snd)
      have hpos := hdiff.continuousAt.eventually
        (lt_mem_nhds (sub_pos.mpr (hafter z.1 z.2 b hb)))
      filter_upwards [hpos] with w hw
      by_contra h
      have hh := hshift w.1.1 b (τ w.1 w.2) (le_of_not_gt h)
        (w.2.2.trans (by linarith : w.2.1 < f (ϕ b w.1.1)))
      rw [hτ] at hh
      have := mul_nonneg hc.le (sub_nonneg.mpr (le_of_not_gt h))
      linarith
  let P : {x : X | R < f x} → {r : ℝ | R < r} → {x : X | R < f x} :=
    fun x r => ⟨ϕ (τ x r) x.1, by change R < f (ϕ (τ x r) x.1); rw [hτ]; exact r.2⟩
  have hPc : Continuous (fun z : {x : X | R < f x} × {r : ℝ | R < r} => P z.1 z.2) :=
    (ϕ.continuous hτc (continuous_subtype_val.comp continuous_fst)).subtype_mk _
  have hPval (x) (r) : f (P x r).1 = r.1 := hτ x r
  have hPself (x : {x : X | R < f x}) : P x ⟨f x.1, x.2⟩ = x := by
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
  let qs : {r : ℝ | R < r} := ⟨s, hs⟩
  let A : {x : X | f x ∈ T} → {x : X | R < f x} := fun x => ⟨x.1, hT _ x.2⟩
  let B : {x : X | f x = s} → {x : X | R < f x} :=
    fun x => ⟨x.1, by change R < f x.1; rw [x.2]; exact hs⟩
  let C : T → {r : ℝ | R < r} := fun r => ⟨r.1, hT _ r.2⟩
  have hAc : Continuous A := continuous_subtype_val.subtype_mk _
  have hBc : Continuous B := continuous_subtype_val.subtype_mk _
  have hCc : Continuous C := continuous_subtype_val.subtype_mk _
  refine ⟨{
    toFun := fun x => (⟨(P (A x) qs).1, hPval _ _⟩, ⟨f x.1, x.2⟩)
    invFun := fun z => ⟨(P (B z.1) (C z.2)).1, by
      change f (P (B z.1) (C z.2)).1 ∈ T
      rw [hPval]
      exact z.2.2⟩
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := ?_
    continuous_invFun := ?_ }⟩
  · intro x
    apply Subtype.ext
    change (P (P (A x) qs) ⟨f (A x).1, (A x).2⟩).1 = x.1
    rw [hPcomp, hPself]
  · intro z
    apply Prod.ext
    · apply Subtype.ext
      change (P (P (B z.1) (C z.2)) qs).1 = z.1.1
      rw [hPcomp]
      have hqs : qs = ⟨f (B z.1).1, (B z.1).2⟩ := Subtype.ext z.1.2.symm
      rw [hqs, hPself]
    · apply Subtype.ext
      exact hPval _ _
  · exact ((continuous_subtype_val.comp (hPc.comp (hAc.prodMk continuous_const))).subtype_mk _).prodMk
      ((hf.comp continuous_subtype_val).subtype_mk _)
  · exact (continuous_subtype_val.comp (hPc.comp
      ((hBc.comp continuous_fst).prodMk (hCc.comp continuous_snd)))).subtype_mk _

end LevelProduct

section Riemannian

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem distance_levelProduct_at_infinity
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M)) (p : M) :
    ∃ R : ℝ, 0 < R ∧ ∀ s : ℝ, R ≤ s → ∀ T : Set ℝ,
      (∀ r ∈ T, R ≤ r) →
      Nonempty ({q : M | dist p q ∈ T} ≃ₜ {q : M | dist p q = s} × T) := by
  obtain ⟨R₀, R₁, hR₀, hRR, V, hbound, _hzero, hout⟩ :=
    exists_smooth_outward_field_at_infinity (I := I) g hEnorm hsec p
  have hc := exists_globalIntegralCurve_of_bounded (I := I) g hEnorm V 2
    (by norm_num) (fun q => by convert! (hbound q).le using 1; norm_num)
  let ϕ : Flow ℝ M := completeFieldFlow V hc
  have hg : ∀ q : M, R₁ < dist p q → ∀ t : ℝ, 0 ≤ t →
      dist p q + (1 / 4 : ℝ) * t ≤ dist p (ϕ t q) := by
    intro q hq t ht
    have hh := escape_of_outward_integralCurve (I := I) g hEnorm p V
      (curveAt_integralCurve V hc q) (hR₀.trans hRR)
      (show 0 ≤ (1 / 4 : ℝ) by norm_num) hout (by rwa [curveAt_zero]) t ht
    rw [curveAt_zero] at hh
    change dist p q + (1 / 4 : ℝ) * t ≤ dist p (curveAt V hc q t)
    linarith [hh.2]
  refine ⟨R₁ + 1, by linarith, ?_⟩
  intro s hs T hT
  exact nonempty_levelProduct_of_escape ϕ (fun q => dist p q)
    (continuous_const.dist continuous_id) R₁ (1 / 4) (by norm_num) hg
    s (by linarith) T (fun r hr => by linarith [hT r hr])

theorem distance_shell_and_exterior_homeomorph
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M)) (p : M) :
    ∃ R : ℝ, 0 < R ∧ ∀ s : ℝ, R ≤ s →
      Nonempty ({q : M | s ≤ dist p q} ≃ₜ {q : M | dist p q = s} × Ici s) ∧
      ∀ s' : ℝ, s ≤ s' →
        Nonempty ({q : M | dist p q ∈ Icc s s'} ≃ₜ
          {q : M | dist p q = s} × Icc s s') := by
  obtain ⟨R, hR, hprod⟩ := distance_levelProduct_at_infinity (I := I) g hEnorm hsec p
  refine ⟨R, hR, ?_⟩
  intro s hs
  exact ⟨hprod s hs (Ici s) (fun r hr => hs.trans hr),
    fun s' _ => hprod s hs (Icc s s') (fun r hr => hs.trans hr.1)⟩


theorem distance_levels_homeomorphic_at_infinity
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M)) (p : M) :
    ∃ R : ℝ, 0 < R ∧ ∀ s s' : ℝ, R ≤ s → R ≤ s' →
      Nonempty ({q : M | dist p q = s} ≃ₜ {q : M | dist p q = s'}) := by
  obtain ⟨R, hR, hprod⟩ := distance_levelProduct_at_infinity (I := I) g hEnorm hsec p
  refine ⟨R, hR, ?_⟩
  intro s s' hs hs'
  obtain ⟨e⟩ := hprod s' hs' {s} (by intro r hr; simpa only [mem_singleton_iff.mp hr] using hs)
  have he : {q : M | dist p q = s} = {q : M | dist p q ∈ ({s} : Set ℝ)} := by
    ext q
    simp only [mem_ofPred_eq, mem_singleton_iff]
  exact ⟨((Homeomorph.setCongr he).trans e).trans (Homeomorph.prodUnique _ _)⟩

end Riemannian

end DifferentialGeometry.Geometry.Topology

end
