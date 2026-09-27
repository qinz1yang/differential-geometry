import DifferentialGeometry.Topology.Morse.RegularLevel.VectorField
import DifferentialGeometry.Analysis.ODE.Flow.CompactSupport

set_option autoImplicit false

open Set Manifold
open scoped Topology ContDiff
open DifferentialGeometry.Topology.Morse DifferentialGeometry.Analysis.ODE

noncomputable section

namespace DifferentialGeometry.Manifold.RegularLevel

variable {n : ℕ}

theorem exists_unitSpeed_near_compact_regularSet
    {f : MorseModel n → ℝ} (hf : ContDiff ℝ ∞ f)
    {K : Set (MorseModel n)} (hK : IsCompact K)
    (hr : ∀ x ∈ K, fderiv ℝ f x ≠ 0) :
    ∃ U : Set (MorseModel n), IsOpen U ∧ K ⊆ U ∧
      ∃ V : (x : MorseModel n) → TangentSpace 𝓘(ℝ, MorseModel n) x,
        ContMDiff 𝓘(ℝ, MorseModel n)
          (𝓘(ℝ, MorseModel n).prod 𝓘(ℝ, MorseModel n)) ∞
          (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, MorseModel n) (MorseModel n))) ∧
        IsCompact (tsupport V) ∧
        ∀ x ∈ U, (mfderiv 𝓘(ℝ, MorseModel n) 𝓘(ℝ, ℝ) f x) (V x) = (-1 : ℝ) := by
  have hregOpen : IsOpen {x | fderiv ℝ f x ≠ 0} :=
    isOpen_ne_fun (hf.continuous_fderiv (by norm_num)) continuous_const
  obtain ⟨U, hU, hKU, hcl, hUc⟩ :=
    exists_open_between_and_isCompact_closure hK hregOpen hr
  have hreg : ∀ x ∈ closure U, ¬ IsCriticalPointAt 𝓘(ℝ, MorseModel n) f x := by
    intro x hx hz
    apply hcl hx
    ext w
    have hw := DFunLike.congr_fun hz w
    rw [mfderiv_eq_fderiv] at hw
    exact hw
  obtain ⟨V, hV, hsupp, hdf, _⟩ :=
    exists_unitSpeedVectorField_on_compact 𝓘(ℝ, MorseModel n) f hf.contMDiff
      (closure U) hUc hreg
  exact ⟨U, hU, hKU, V, hV, hsupp, fun x hx => hdf x (subset_closure hx)⟩

private theorem exists_uniform_flow_time
    {E : Type*} [TopologicalSpace E]
    {F : E × ℝ → E} (hF : Continuous F) (hzero : ∀ x, F (x, 0) = x)
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K, ∀ t ∈ Icc (-ε) ε, F (x, t) ∈ U := by
  obtain ⟨A, B, _, hB, hKA, h0B, hAB⟩ := generalized_tube_lemma hK
    (isCompact_singleton (x := (0 : ℝ))) (hU.preimage hF)
    (by rintro ⟨x, t⟩ ⟨hx, ht⟩; simp only [mem_singleton_iff] at ht
        simpa [ht, hzero x] using hKU hx)
  obtain ⟨δ, hδ, hδB⟩ := Metric.mem_nhds_iff.mp
    (hB.mem_nhds (h0B (mem_singleton 0)))
  refine ⟨δ / 2, by linarith, ?_⟩
  intro x hx t ht
  apply hAB ⟨hKA hx, hδB ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
  constructor <;> linarith [ht.1, ht.2]

theorem value_curveAt_of_unitSpeed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (V : (x : M) → TangentSpace I x)
    (hc : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ V)
    {U : Set M} (hdf : ∀ x ∈ U, (mfderiv I 𝓘(ℝ, ℝ) f x) (V x) = (-1 : ℝ))
    {ε : ℝ} {x : M}
    (hstay : ∀ t ∈ Icc (-ε) ε, curveAt V hc x t ∈ U)
    {t : ℝ} (ht : t ∈ Icc (-ε) ε) :
    f (curveAt V hc x t) = f x - t := by
  have hε : 0 ≤ ε := by linarith [ht.1, ht.2]
  by_cases ht0 : 0 ≤ t
  · have h := f_eq_sub_of_integralCurve_on_set f hf V U hdf
      (curveAt_integralCurve V hc x) ht0
      (fun s hs => hstay s ⟨by linarith [hs.1], le_trans hs.2 ht.2⟩)
    simpa only [curveAt_zero] using h
  · have ht0 : t ≤ 0 := le_of_not_ge ht0
    have h := f_eq_sub_of_integralCurve_on_set f hf V U hdf
      ((curveAt_integralCurve V hc x).comp_add t) (neg_nonneg.mpr ht0)
      (fun s hs => hstay (s + t) ⟨by linarith [ht.1, hs.1], by linarith [hs.2]⟩)
    simp only [Function.comp_apply, neg_add_cancel, zero_add,
      curveAt_zero] at h
    linarith

theorem exists_transverseFlow_on_compact_regularSet
    {f : MorseModel n → ℝ} (hf : ContDiff ℝ ∞ f)
    {K : Set (MorseModel n)} (hK : IsCompact K)
    (hr : ∀ x ∈ K, fderiv ℝ f x ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ F : MorseModel n × ℝ → MorseModel n,
      ContDiff ℝ ∞ F ∧
      (∀ x, F (x, 0) = x) ∧
      (∀ x s t, F (F (x, s), t) = F (x, s + t)) ∧
      ∀ x ∈ K, ∀ t ∈ Icc (-ε) ε, f (F (x, t)) = f x - t := by
  obtain ⟨U, hU, hKU, V, hV, hsupp, hdf⟩ :=
    exists_unitSpeed_near_compact_regularSet hf hK hr
  let hc := exists_globalIntegralCurve_of_compactSupport V hV hsupp
  let F : MorseModel n × ℝ → MorseModel n := fun p => curveAt V hc p.1 p.2
  have hF : ContDiff ℝ ∞ F := by
    have h := contMDiff_globalFlow_joint_of_compactSupport V hV hsupp
    exact (h.comp (contDiff_snd.contMDiff.prodMk contDiff_fst.contMDiff)).contDiff
  have hzero : ∀ x, F (x, 0) = x := curveAt_zero V hc
  obtain ⟨ε, hε, hstay⟩ := exists_uniform_flow_time hF.continuous hzero hK hU hKU
  refine ⟨ε, hε, F, hF, hzero, ?_, ?_⟩
  · intro x s t
    exact (curveAt_add V (hV.of_le (by norm_num)) hc x s t).symm
  · intro x hx t ht
    exact value_curveAt_of_unitSpeed hf.contMDiff V hc hdf (hstay x hx) ht

theorem exists_flowCollar_of_compact_regularLevel
    {f : MorseModel n → ℝ} (hf : ContDiff ℝ ∞ f) (a : ℝ)
    (hK : IsCompact {x | f x = a})
    (hr : ∀ x, f x = a → fderiv ℝ f x ≠ 0) :
    ∃ r : ℝ, ∃ hr : 0 < r, ∃ U : TopologicalSpace.Opens (MorseModel n),
      ∃ F : MorseModel n × ℝ → MorseModel n, ContDiff ℝ ∞ F ∧
      ∃ e : ({x : MorseModel n // f x = a} × Ioo (-r) r) ≃ₜ U,
        (∀ p, (e p : MorseModel n) = F (p.1, p.2)) ∧
        (∀ y, ((e.symm y).1 : MorseModel n) = F (y, f y - a)) ∧
        (∀ y, ((e.symm y).2 : ℝ) = a - f y) ∧
        (∀ p, f (e p) = a - p.2) ∧
        ∀ x : {x : MorseModel n // f x = a},
          (e (x, ⟨0, by constructor <;> linarith⟩) : MorseModel n) = x := by
  have hregOpen : IsOpen {x | fderiv ℝ f x ≠ 0} :=
    isOpen_ne_fun (hf.continuous_fderiv (by norm_num)) continuous_const
  obtain ⟨W, hW, hKW, hcl, hWc⟩ :=
    exists_open_between_and_isCompact_closure hK hregOpen hr
  obtain ⟨ε, hε, F, hF, hzero, hadd, hvalue⟩ :=
    exists_transverseFlow_on_compact_regularSet hf hWc (fun x hx => hcl hx)
  obtain ⟨δ, hδ, hstay⟩ := exists_uniform_flow_time hF.continuous hzero hK hW hKW
  let r := min ε δ
  have hr : 0 < r := lt_min hε hδ
  have hrε : r ≤ ε := min_le_left _ _
  have hrδ : r ≤ δ := min_le_right _ _
  let U : TopologicalSpace.Opens (MorseModel n) :=
    ⟨W ∩ f ⁻¹' Ioo (a - r) (a + r), hW.inter (isOpen_Ioo.preimage hf.continuous)⟩
  have hlev : ∀ x : {x : MorseModel n // f x = a}, ∀ t : Ioo (-r) r,
      f (F (x, t)) = a - t := by
    intro x t
    rw [hvalue x (subset_closure (hKW x.2)) t
      ⟨by linarith [t.2.1], by linarith [t.2.2]⟩, x.2]
  have hforward : ∀ p : {x : MorseModel n // f x = a} × Ioo (-r) r,
      F (p.1, p.2) ∈ U := by
    rintro ⟨x, t⟩
    refine ⟨hstay x x.2 t ⟨by linarith [t.2.1], by linarith [t.2.2]⟩, ?_⟩
    change a - r < f (F (x, t)) ∧ f (F (x, t)) < a + r
    rw [hlev x t]
    constructor <;> linarith [t.2.1, t.2.2]
  have hback : ∀ y : U, f (F (y, f y - a)) = a := by
    intro y
    have hy := y.2.2
    change a - r < f y ∧ f y < a + r at hy
    rw [hvalue y (subset_closure y.2.1) (f y - a)
      ⟨by linarith [hy.1], by linarith [hy.2]⟩]
    ring
  let e : ({x : MorseModel n // f x = a} × Ioo (-r) r) ≃ₜ U :=
    { toFun := fun p => ⟨F (p.1, p.2), hforward p⟩
      invFun := fun y => (⟨F (y, f y - a), hback y⟩,
        ⟨a - f y, by
          have hy := y.2.2
          change a - r < f y ∧ f y < a + r at hy
          constructor <;> linarith [hy.1, hy.2]⟩)
      left_inv := by
        rintro ⟨x, t⟩
        apply Prod.ext
        · apply Subtype.ext
          change F (F (x, t), f (F (x, t)) - a) = x
          rw [hlev x t, hadd]
          rw [show (t : ℝ) + (a - t - a) = 0 by ring]
          exact hzero x
        · apply Subtype.ext
          change a - f (F (x, t)) = t
          rw [hlev x t]
          ring
      right_inv := by
        intro y
        apply Subtype.ext
        change F (F (y, f y - a), a - f y) = y
        rw [hadd]
        rw [show (f y - a) + (a - f y) = 0 by ring]
        exact hzero y
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact hF.continuous.comp
          ((continuous_subtype_val.comp continuous_fst).prodMk
            (continuous_subtype_val.comp continuous_snd))
      continuous_invFun := by
        apply Continuous.prodMk
        · apply Continuous.subtype_mk
          exact hF.continuous.comp
            (continuous_subtype_val.prodMk
              ((hf.continuous.comp continuous_subtype_val).sub continuous_const))
        · apply Continuous.subtype_mk
          exact continuous_const.sub (hf.continuous.comp continuous_subtype_val) }
  refine ⟨r, hr, U, F, hF, e, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun p => hlev p.1 p.2, ?_⟩
  intro x
  exact hzero x

end DifferentialGeometry.Manifold.RegularLevel
