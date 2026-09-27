/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Morse.ConnectingOrbit
import DifferentialGeometry.Topology.Morse.CriticalPoints
import DifferentialGeometry.Topology.Diffeomorph.Flow
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.Compact

open Set Filter Function
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Topology.Morse (IsCriticalPointAt)

namespace DifferentialGeometry.Morse

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  {f : M → ℝ} {v : (x : M) → TangentSpace I x}

private theorem antitoneOn_compactSupportFlow
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hv : ContMDiff I I.tangent ∞ (fun x => (v x : TangentBundle I M)))
    (hvc : HasCompactSupport v) {K : Set M} {x : M}
    (hstay : ∀ t, 0 ≤ t → Diffeomorph.compactSupportFlow v hv hvc t x ∈ K)
    (hdesc : ∀ y ∈ K, ¬ IsCriticalPointAt I f y → mvfderiv I f y (v y) < 0) :
    AntitoneOn (fun t => f (Diffeomorph.compactSupportFlow v hv hvc t x)) (Ici 0) := by
  let Φ := Diffeomorph.compactSupportFlow v hv hvc
  have hd (t : ℝ) := hasDerivAt_df_comp_integralCurve f hf v
    (Diffeomorph.isMIntegralCurve_compactSupportFlow v hv hvc x) t
  have hcont : Continuous (fun t => f (Φ t x)) :=
    hf.continuous.comp (Diffeomorph.isMIntegralCurve_compactSupportFlow v hv hvc x).continuous
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0) hcont.continuousOn
    (fun t _ => (hd t).differentiableAt.differentiableWithinAt)
  intro t ht
  change deriv (f ∘ fun s => Diffeomorph.compactSupportFlow v hv hvc s x) t ≤ 0
  rw [(hd t).deriv]
  by_cases hc : IsCriticalPointAt I f (Φ t x)
  · change mfderiv I 𝓘(ℝ, ℝ) f (Φ t x) = 0 at hc
    change mvfderiv I f (Φ t x) (v (Φ t x)) ≤ 0
    simp only [mvfderiv, hc, ContinuousLinearMap.comp_apply,
      zero_apply, map_zero, le_refl]
  · exact (hdesc _ (hstay t (interior_subset ht)) hc).le

private theorem exists_limit_compactSupportFlow
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hv : ContMDiff I I.tangent ∞ (fun x => (v x : TangentBundle I M)))
    (hvc : HasCompactSupport v) {K : Set M} (hK : IsCompact K) {x : M}
    (hstay : ∀ t, 0 ≤ t → Diffeomorph.compactSupportFlow v hv hvc t x ∈ K)
    (hdesc : ∀ y ∈ K, ¬ IsCriticalPointAt I f y → mvfderiv I f y (v y) < 0) :
    ∃ c : ℝ, Tendsto (fun t => f (Diffeomorph.compactSupportFlow v hv hvc t x))
      atTop (𝓝 c) := by
  let Φ := Diffeomorph.compactSupportFlow v hv hvc
  let h : ℝ → ℝ := fun t => f (Φ (max t 0) x)
  have hanti : Antitone h := fun s t hst =>
    antitoneOn_compactSupportFlow hf hv hvc hstay hdesc
      (by change 0 ≤ max s 0; exact le_max_right _ _)
      (by change 0 ≤ max t 0; exact le_max_right _ _) (max_le_max_right _ hst)
  have hbdd : BddBelow (range h) := (hK.bddBelow_image hf.continuous.continuousOn).mono (by
    rintro y ⟨t, rfl⟩
    exact mem_image_of_mem f (hstay (max t 0) (le_max_right _ _)))
  refine ⟨⨅ t, h t, (tendsto_atTop_ciInf hanti hbdd).congr' ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  simp only [h, Φ, max_eq_left ht]

theorem isCriticalPointAt_of_mapClusterPt_compactSupportFlow
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hv : ContMDiff I I.tangent ∞ (fun x => (v x : TangentBundle I M)))
    (hvc : HasCompactSupport v) {K : Set M} (hK : IsCompact K) {x y : M}
    (hstay : ∀ t, 0 ≤ t → Diffeomorph.compactSupportFlow v hv hvc t x ∈ K)
    (hdesc : ∀ z ∈ K, ¬ IsCriticalPointAt I f z → mvfderiv I f z (v z) < 0)
    (hy : MapClusterPt y atTop (fun t => Diffeomorph.compactSupportFlow v hv hvc t x)) :
    IsCriticalPointAt I f y := by
  let Φ := Diffeomorph.compactSupportFlow v hv hvc
  obtain ⟨c, hc⟩ := exists_limit_compactSupportFlow hf hv hvc hK hstay hdesc
  have hyK : y ∈ K := hK.isClosed.mem_of_mapClusterPt hy (by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact hstay t ht)
  have hlevel (t : ℝ) : f (Φ t y) = c := by
    have hcluster : MapClusterPt (f (Φ t y)) atTop (fun s => f (Φ t (Φ s x))) :=
      MapClusterPt.continuousAt_comp (f := fun z => f (Φ t z))
        (hf.continuous.comp (Φ t).continuous).continuousAt hy
    have hshift : Tendsto (fun s : ℝ => s + t) atTop atTop := by
      apply tendsto_atTop.2
      intro b
      filter_upwards [eventually_ge_atTop (b - t)] with s hs
      linarith
    have hadd (s : ℝ) : Φ t (Φ s x) = Φ (s + t) x :=
      (DFunLike.congr_fun (Diffeomorph.compactSupportFlow_add v hv hvc s t) x).symm
    have htend : Tendsto (fun s => f (Φ t (Φ s x))) atTop (𝓝 c) := by
      simpa only [hadd, Φ, comp_def] using hc.comp hshift
    exact eq_of_nhds_neBot (hcluster.clusterPt.mono htend)
  have hd := hasDerivAt_df_comp_integralCurve f hf v
    (Diffeomorph.isMIntegralCurve_compactSupportFlow v hv hvc y) 0
  have hzero : mvfderiv I f y (v y) = 0 := by
    have heq : (fun t => f (Φ t y)) = fun _ => c := funext hlevel
    have hz : deriv (fun t => f (Φ t y)) 0 = 0 := by rw [heq]; exact deriv_const _ _
    have hzv : mvfderiv I f (Φ 0 y) (v (Φ 0 y)) = 0 := hd.deriv.symm.trans hz
    have hφ0 : Φ 0 y = y :=
      DFunLike.congr_fun (Diffeomorph.compactSupportFlow_zero v hv hvc) y
    exact (congrArg (fun z => mvfderiv I f z (v z)) hφ0).symm.trans hzv
  by_contra hyc
  exact (hdesc y hyK hyc).ne hzero

theorem tendsto_compactSupportFlow_of_unique_critical_point
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hv : ContMDiff I I.tangent ∞ (fun x => (v x : TangentBundle I M)))
    (hvc : HasCompactSupport v) {K : Set M} (hK : IsCompact K) {x q : M}
    (hstay : ∀ t, 0 ≤ t → Diffeomorph.compactSupportFlow v hv hvc t x ∈ K)
    (hdesc : ∀ y ∈ K, ¬ IsCriticalPointAt I f y → mvfderiv I f y (v y) < 0)
    (hcrit : ∀ y ∈ K, f y ≤ f x → IsCriticalPointAt I f y → y = q) :
    Tendsto (fun t => Diffeomorph.compactSupportFlow v hv hvc t x) atTop (𝓝 q) := by
  let Φ := Diffeomorph.compactSupportFlow v hv hvc
  have hanti := antitoneOn_compactSupportFlow hf hv hvc hstay hdesc
  apply hK.tendsto_nhds_of_unique_mapClusterPt (by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact hstay t ht)
  intro y hy hcluster
  apply hcrit y hy
  · apply (isClosed_le hf.continuous continuous_const).mem_of_mapClusterPt hcluster
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have hle := hanti (by simp : (0 : ℝ) ∈ Ici 0) ht ht
    have hφ0 : Φ 0 x = x :=
      DFunLike.congr_fun (Diffeomorph.compactSupportFlow_zero v hv hvc) x
    exact hle.trans_eq (congrArg f hφ0)
  · exact isCriticalPointAt_of_mapClusterPt_compactSupportFlow hf hv hvc hK hstay hdesc hcluster

theorem exists_forward_exit_of_unique_descending_connection
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {w : (x : M) → TangentSpace I x}
    (hw : ContMDiff I I.tangent ∞ (fun x => (w x : TangentBundle I M)))
    (hwc : HasCompactSupport w) {K : Set M} (hK : IsCompact K) {p q x : M}
    (hwp : w p = 0) (hwq : w q = 0)
    (hagree : ∀ y ∈ K, w y = v y)
    (hdesc : ∀ y ∈ K, ¬ IsCriticalPointAt I f y → mvfderiv I f y (v y) < 0)
    (hcrit : ∀ y ∈ K, IsCriticalPointAt I f y → y = p ∨ y = q)
    {γ : ℝ → M}
    (hunique : ∀ η, IsDescendingConnection I f v p q η → ∃ d : ℝ, η = γ ∘ (· + d))
    (hx : f q < f x ∧ f x < f p) (hxγ : x ∉ range γ)
    (hback : Tendsto (fun t => Diffeomorph.compactSupportFlow w hw hwc t x) atBot (𝓝 p))
    (hpast : ∀ t, t ≤ 0 → Diffeomorph.compactSupportFlow w hw hwc t x ∈ K) :
    ∃ t : ℝ, 0 < t ∧ Diffeomorph.compactSupportFlow w hw hwc t x ∉ K := by
  let Φ := Diffeomorph.compactSupportFlow w hw hwc
  let η : ℝ → M := fun t => Φ t x
  by_contra hn
  push Not at hn
  have hstay (t : ℝ) (ht : 0 ≤ t) : Φ t x ∈ K := by
    rcases lt_or_eq_of_le ht with ht | rfl
    · exact hn t ht
    · exact hpast 0 le_rfl
  have hall (t : ℝ) : η t ∈ K := by
    rcases le_total 0 t with ht | ht
    · exact hstay t ht
    · exact hpast t ht
  have hdescw (y : M) (hy : y ∈ K) (hc : ¬ IsCriticalPointAt I f y) :
      mvfderiv I f y (w y) < 0 := by
    rw [hagree y hy]
    exact hdesc y hy hc
  have hlim : Tendsto η atTop (𝓝 q) := by
    apply tendsto_compactSupportFlow_of_unique_critical_point hf hw hwc hK hstay hdescw
    intro y hy hfy hcy
    rcases hcrit y hy hcy with rfl | hq
    · exact (not_le_of_gt hx.2 hfy).elim
    · exact hq
  have hregular (t : ℝ) : ¬ IsCriticalPointAt I f (η t) := by
    intro hc
    rcases hcrit _ (hall t) hc with hp | hq
    · have hfix : Φ t p = p :=
        Diffeomorph.compactSupportFlow_apply_eq_self_of_eq_zero w hw hwc hwp t
      have hxp : x = p := (Φ t).injective (hp.trans hfix.symm)
      exact (ne_of_lt hx.2) (congrArg f hxp)
    · have hfix : Φ t q = q :=
        Diffeomorph.compactSupportFlow_apply_eq_self_of_eq_zero w hw hwc hwq t
      have hxq : x = q := (Φ t).injective (hq.trans hfix.symm)
      exact (ne_of_lt hx.1) (congrArg f hxq).symm
  have hcurve : IsMIntegralCurve η v := by
    intro t
    have hd := Diffeomorph.isMIntegralCurve_compactSupportFlow w hw hwc x t
    rw [hagree _ (hall t)] at hd
    exact hd
  have hconnection : IsDescendingConnection I f v p q η :=
    ⟨hcurve, hback, hlim, fun t => hdesc _ (hall t) (hregular t)⟩
  obtain ⟨d, hd⟩ := hunique η hconnection
  apply hxγ
  refine ⟨d, ?_⟩
  have hz : η 0 = x := DFunLike.congr_fun
    (Diffeomorph.compactSupportFlow_zero w hw hwc) x
  have hη0 : η 0 = γ d := by simpa only [comp_apply, zero_add] using congr_fun hd 0
  exact hη0.symm.trans hz

theorem compactSupportFlow_preserves_sublevel_of_deriv_neg
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hv : ContMDiff I I.tangent ∞ (fun x => (v x : TangentBundle I M)))
    (hvc : HasCompactSupport v) {c : ℝ}
    (hlevel : ∀ y, f y = c → mvfderiv I f y (v y) < 0)
    {x : M} (hx : f x ≤ c) {t : ℝ} (ht : 0 ≤ t) :
    f (Diffeomorph.compactSupportFlow v hv hvc t x) ≤ c := by
  let Φ := Diffeomorph.compactSupportFlow v hv hvc
  let h : ℝ → ℝ := fun s => f (Φ s x)
  have hd (s : ℝ) : HasDerivAt h (mvfderiv I f (Φ s x) (v (Φ s x))) s :=
    hasDerivAt_df_comp_integralCurve f hf v
      (Diffeomorph.isMIntegralCurve_compactSupportFlow v hv hvc x) s
  have h0 : h 0 ≤ c := by
    have hz : Φ 0 x = x :=
      DFunLike.congr_fun (Diffeomorph.compactSupportFlow_zero v hv hvc) x
    exact (congrArg f hz).le.trans hx
  have hcont : Continuous h := hf.continuous.comp
    (Diffeomorph.isMIntegralCurve_compactSupportFlow v hv hvc x).continuous
  exact image_le_of_deriv_right_lt_deriv_boundary hcont.continuousOn
    (fun s _ => (hd s).hasDerivWithinAt) h0
    (fun s => hasDerivAt_const s c)
    (fun s _ hs => hlevel (Φ s x) hs) ⟨ht, le_rfl⟩

theorem exists_first_level_time_of_unique_descending_connection
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {w : (x : M) → TangentSpace I x}
    (hw : ContMDiff I I.tangent ∞ (fun x => (w x : TangentBundle I M)))
    (hwc : HasCompactSupport w) {p q x : M} {a : ℝ}
    (ha : a < f q) (hK : IsCompact (f ⁻¹' Icc a (f p)))
    (hwp : w p = 0) (hwq : w q = 0)
    (hagree : ∀ y ∈ f ⁻¹' Icc a (f p), w y = v y)
    (hdesc : ∀ y ∈ f ⁻¹' Icc a (f p),
      ¬ IsCriticalPointAt I f y → mvfderiv I f y (v y) < 0)
    (hcrit : ∀ y ∈ f ⁻¹' Icc a (f p), IsCriticalPointAt I f y → y = p ∨ y = q)
    {γ : ℝ → M}
    (hunique : ∀ η, IsDescendingConnection I f v p q η → ∃ d : ℝ, η = γ ∘ (· + d))
    (hx : f q < f x ∧ f x < f p) (hxγ : x ∉ range γ)
    (hback : Tendsto (fun t => Diffeomorph.compactSupportFlow w hw hwc t x) atBot (𝓝 p))
    (hpast : ∀ t, t ≤ 0 → Diffeomorph.compactSupportFlow w hw hwc t x ∈
      f ⁻¹' Icc a (f p)) :
    ∃ T : ℝ, 0 < T ∧
      f (Diffeomorph.compactSupportFlow w hw hwc T x) = a ∧
      (∀ t ∈ Icc (0 : ℝ) T, Diffeomorph.compactSupportFlow w hw hwc t x ∈
        f ⁻¹' Icc a (f p)) ∧
      IsMIntegralCurveOn (fun t => Diffeomorph.compactSupportFlow w hw hwc t x) v (Icc 0 T) ∧
      StrictAntiOn (fun t => f (Diffeomorph.compactSupportFlow w hw hwc t x)) (Icc 0 T) := by
  let Φ := Diffeomorph.compactSupportFlow w hw hwc
  let η : ℝ → M := fun t => Φ t x
  let h : ℝ → ℝ := f ∘ η
  have h0 : h 0 = f x := congrArg f
    (DFunLike.congr_fun (Diffeomorph.compactSupportFlow_zero w hw hwc) x)
  have hcontinuous : Continuous h := hf.continuous.comp
    (Diffeomorph.isMIntegralCurve_compactSupportFlow w hw hwc x).continuous
  obtain ⟨c, hxc, hcp⟩ := exists_between hx.2
  have hac : a < c := ha.trans (hx.1.trans hxc)
  have hbound {t : ℝ} (ht : 0 ≤ t) : h t ≤ c := by
    apply compactSupportFlow_preserves_sublevel_of_deriv_neg hf hw hwc _ hxc.le ht
    intro y hy
    have hyK : y ∈ f ⁻¹' Icc a (f p) := by
      change a ≤ f y ∧ f y ≤ f p
      rw [hy]
      exact ⟨hac.le, hcp.le⟩
    rw [hagree y hyK]
    apply hdesc y hyK
    intro hc
    rcases hcrit y hyK hc with rfl | rfl
    · exact hcp.ne hy.symm
    · exact (hx.1.trans hxc).ne hy
  obtain ⟨b, hb, hout⟩ := exists_forward_exit_of_unique_descending_connection hf hw hwc hK
    hwp hwq hagree hdesc hcrit hunique hx hxγ hback hpast
  have hbvalue : h b < a := by
    have hbupper := (hbound hb.le).trans hcp.le
    exact lt_of_not_ge (fun hba => hout ⟨hba, hbupper⟩)
  have hnonempty : (Icc (0 : ℝ) b ∩ h ⁻¹' {a}).Nonempty := by
    obtain ⟨t, ht, heq⟩ := intermediate_value_Icc' hb.le hcontinuous.continuousOn
      (show a ∈ Icc (h b) (h 0) from ⟨hbvalue.le, by rw [h0]; exact (ha.trans hx.1).le⟩)
    exact ⟨t, ht, heq⟩
  have htimes : IsCompact (Icc (0 : ℝ) b ∩ h ⁻¹' {a}) :=
    isCompact_Icc.inter_right (isClosed_singleton.preimage hcontinuous)
  obtain ⟨T, hT, hmin⟩ := htimes.exists_isMinOn hnonempty continuous_id.continuousOn
  have hTa : h T = a := hT.2
  have hTpos : 0 < T := by
    have hz : T ≠ 0 := by
      intro he
      have hh : f x = a := h0.symm.trans (he ▸ hTa)
      exact (ha.trans hx.1).ne hh.symm
    exact lt_of_le_of_ne hT.1.1 hz.symm
  have hstay {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : η t ∈ f ⁻¹' Icc a (f p) := by
    refine ⟨?_, (hbound ht.1).trans hcp.le⟩
    by_contra hl
    have hlt : h t < a := lt_of_not_ge hl
    obtain ⟨u, hu, hua⟩ := intermediate_value_Icc' ht.1 hcontinuous.continuousOn
      (show a ∈ Icc (h t) (h 0) from ⟨hlt.le, by rw [h0]; exact (ha.trans hx.1).le⟩)
    have hTu : T ≤ u := hmin ⟨⟨hu.1, hu.2.trans (ht.2.trans hT.1.2)⟩, hua⟩
    have heq : t = T := le_antisymm ht.2 (hTu.trans hu.2)
    exact hlt.ne (heq ▸ hTa)
  have hregular (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : ¬ IsCriticalPointAt I f (η t) := by
    intro hc
    rcases hcrit _ (hstay ht) hc with hp | hq
    · have hfix : Φ t p = p :=
        Diffeomorph.compactSupportFlow_apply_eq_self_of_eq_zero w hw hwc hwp t
      have hxp : x = p := (Φ t).injective (hp.trans hfix.symm)
      exact (ne_of_lt hx.2) (congrArg f hxp)
    · have hfix : Φ t q = q :=
        Diffeomorph.compactSupportFlow_apply_eq_self_of_eq_zero w hw hwc hwq t
      have hxq : x = q := (Φ t).injective (hq.trans hfix.symm)
      exact (ne_of_lt hx.1) (congrArg f hxq).symm
  have hd (t : ℝ) : HasDerivAt h (mvfderiv I f (η t) (w (η t))) t :=
    hasDerivAt_df_comp_integralCurve f hf w
      (Diffeomorph.isMIntegralCurve_compactSupportFlow w hw hwc x) t
  refine ⟨T, hTpos, hTa, fun t ht => hstay ht, ?_, ?_⟩
  · intro t ht
    have hder := Diffeomorph.isMIntegralCurve_compactSupportFlow w hw hwc x t
    rw [hagree _ (hstay ht)] at hder
    exact hder.hasMFDerivWithinAt
  · apply strictAntiOn_of_deriv_neg (convex_Icc 0 T) hcontinuous.continuousOn
    intro t ht
    have htc := interior_subset ht
    have hd' : deriv h t = mvfderiv I f (η t) (w (η t)) := (hd t).deriv
    change deriv h t < 0
    rw [hd', hagree _ (hstay htc)]
    exact hdesc _ (hstay htc) (hregular t htc)

theorem exists_first_level_time_in_compact_sublevel
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {B : M → ℝ}
    (hB : ContMDiff I 𝓘(ℝ, ℝ) ∞ B)
    {w : (x : M) → TangentSpace I x}
    (hw : ContMDiff I I.tangent ∞ (fun x => (w x : TangentBundle I M)))
    (hwc : HasCompactSupport w) {p q x : M} {a c : ℝ}
    (ha : a < f q) (hK : IsCompact {y | a ≤ f y ∧ B y ≤ c})
    (hwp : w p = 0) (hwq : w q = 0)
    (hagree : ∀ y, a ≤ f y → B y ≤ c → w y = v y)
    (hinward : ∀ y, a ≤ f y → B y = c → mvfderiv I B y (v y) < 0)
    (hdesc : ∀ y, a ≤ f y → B y ≤ c →
      ¬ IsCriticalPointAt I f y → mvfderiv I f y (v y) < 0)
    (hcrit : ∀ y, a ≤ f y → B y ≤ c → IsCriticalPointAt I f y → y = p ∨ y = q)
    {γ : ℝ → M}
    (hunique : ∀ η, IsDescendingConnection I f v p q η → ∃ d : ℝ, η = γ ∘ (· + d))
    (hx : f q < f x ∧ f x < f p) (hxB : B x ≤ c) (hxγ : x ∉ range γ)
    (hback : Tendsto (fun t => Diffeomorph.compactSupportFlow w hw hwc t x) atBot (𝓝 p))
    (hpast : ∀ t, t ≤ 0 →
      a ≤ f (Diffeomorph.compactSupportFlow w hw hwc t x) ∧
      B (Diffeomorph.compactSupportFlow w hw hwc t x) ≤ c) :
    ∃ T : ℝ, 0 < T ∧
      f (Diffeomorph.compactSupportFlow w hw hwc T x) = a ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        a ≤ f (Diffeomorph.compactSupportFlow w hw hwc t x) ∧
        B (Diffeomorph.compactSupportFlow w hw hwc t x) ≤ c) ∧
      IsMIntegralCurveOn (fun t => Diffeomorph.compactSupportFlow w hw hwc t x) v (Icc 0 T) ∧
      StrictAntiOn (fun t => f (Diffeomorph.compactSupportFlow w hw hwc t x)) (Icc 0 T) := by
  let Φ := Diffeomorph.compactSupportFlow w hw hwc
  let η : ℝ → M := fun t => Φ t x
  let h : ℝ → ℝ := f ∘ η
  have h0 : h 0 = f x := congrArg f
    (DFunLike.congr_fun (Diffeomorph.compactSupportFlow_zero w hw hwc) x)
  have hcontinuous : Continuous h := hf.continuous.comp
    (Diffeomorph.isMIntegralCurve_compactSupportFlow w hw hwc x).continuous
  have hbounded {t : ℝ} (ht : 0 ≤ t) (hlower : ∀ s ∈ Icc (0 : ℝ) t, a ≤ h s) :
      B (η t) ≤ c := by
    have hd (s : ℝ) : HasDerivAt (B ∘ η) (mvfderiv I B (η s) (w (η s))) s :=
      hasDerivAt_df_comp_integralCurve B hB w
        (Diffeomorph.isMIntegralCurve_compactSupportFlow w hw hwc x) s
    apply image_le_of_deriv_right_lt_deriv_boundary
      (hB.continuous.comp
        (Diffeomorph.isMIntegralCurve_compactSupportFlow w hw hwc x).continuous).continuousOn
      (fun s _ => (hd s).hasDerivWithinAt) _ (fun s => hasDerivAt_const s c) _ ⟨ht, le_rfl⟩
    · have hz : η 0 = x :=
        DFunLike.congr_fun (Diffeomorph.compactSupportFlow_zero w hw hwc) x
      exact (congrArg B hz).le.trans hxB
    · intro s hs heq
      have ha' := hlower s (Ico_subset_Icc_self hs)
      rw [hagree _ ha' heq.le]
      exact hinward _ ha' heq
  obtain ⟨b, hb, hbvalue⟩ : ∃ b : ℝ, 0 < b ∧ h b ≤ a := by
    by_contra hn
    push Not at hn
    have hlower (t : ℝ) (ht : 0 ≤ t) : a ≤ h t := by
      rcases lt_or_eq_of_le ht with ht | rfl
      · exact (hn t ht).le
      · rw [h0]
        exact (ha.trans hx.1).le
    obtain ⟨t, ht, hout⟩ := exists_forward_exit_of_unique_descending_connection hf hw hwc hK
      hwp hwq (fun y hy => hagree y hy.1 hy.2)
      (fun y hy => hdesc y hy.1 hy.2) (fun y hy => hcrit y hy.1 hy.2)
      hunique hx hxγ hback hpast
    exact hout ⟨hlower t ht.le, hbounded ht.le (fun s hs => hlower s hs.1)⟩
  have hnonempty : (Icc (0 : ℝ) b ∩ h ⁻¹' {a}).Nonempty := by
    obtain ⟨t, ht, heq⟩ := intermediate_value_Icc' hb.le hcontinuous.continuousOn
      (show a ∈ Icc (h b) (h 0) from ⟨hbvalue, by rw [h0]; exact (ha.trans hx.1).le⟩)
    exact ⟨t, ht, heq⟩
  have htimes : IsCompact (Icc (0 : ℝ) b ∩ h ⁻¹' {a}) :=
    isCompact_Icc.inter_right (isClosed_singleton.preimage hcontinuous)
  obtain ⟨T, hT, hmin⟩ := htimes.exists_isMinOn hnonempty continuous_id.continuousOn
  have hTa : h T = a := hT.2
  have hTpos : 0 < T := by
    have hz : T ≠ 0 := by
      intro he
      have hh : f x = a := h0.symm.trans (he ▸ hTa)
      exact (ha.trans hx.1).ne hh.symm
    exact lt_of_le_of_ne hT.1.1 hz.symm
  have hlower {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : a ≤ h t := by
    by_contra hl
    have hlt : h t < a := lt_of_not_ge hl
    obtain ⟨u, hu, hua⟩ := intermediate_value_Icc' ht.1 hcontinuous.continuousOn
      (show a ∈ Icc (h t) (h 0) from ⟨hlt.le, by rw [h0]; exact (ha.trans hx.1).le⟩)
    have hTu : T ≤ u := hmin ⟨⟨hu.1, hu.2.trans (ht.2.trans hT.1.2)⟩, hua⟩
    have heq : t = T := le_antisymm ht.2 (hTu.trans hu.2)
    exact hlt.ne (heq ▸ hTa)
  have hstay {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
      a ≤ f (η t) ∧ B (η t) ≤ c :=
    ⟨hlower ht, hbounded ht.1 (fun s hs => hlower ⟨hs.1, hs.2.trans ht.2⟩)⟩
  have hregular (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : ¬ IsCriticalPointAt I f (η t) := by
    intro hc
    rcases hcrit _ (hstay ht).1 (hstay ht).2 hc with hp | hq
    · have hfix : Φ t p = p :=
        Diffeomorph.compactSupportFlow_apply_eq_self_of_eq_zero w hw hwc hwp t
      have hxp : x = p := (Φ t).injective (hp.trans hfix.symm)
      exact (ne_of_lt hx.2) (congrArg f hxp)
    · have hfix : Φ t q = q :=
        Diffeomorph.compactSupportFlow_apply_eq_self_of_eq_zero w hw hwc hwq t
      have hxq : x = q := (Φ t).injective (hq.trans hfix.symm)
      exact (ne_of_lt hx.1) (congrArg f hxq).symm
  have hd (t : ℝ) : HasDerivAt h (mvfderiv I f (η t) (w (η t))) t :=
    hasDerivAt_df_comp_integralCurve f hf w
      (Diffeomorph.isMIntegralCurve_compactSupportFlow w hw hwc x) t
  refine ⟨T, hTpos, hTa, fun t ht => hstay ht, ?_, ?_⟩
  · intro t ht
    have hder := Diffeomorph.isMIntegralCurve_compactSupportFlow w hw hwc x t
    rw [hagree _ (hstay ht).1 (hstay ht).2] at hder
    exact hder.hasMFDerivWithinAt
  · apply strictAntiOn_of_deriv_neg (convex_Icc 0 T) hcontinuous.continuousOn
    intro t ht
    have htc := interior_subset ht
    change deriv h t < 0
    rw [(hd t).deriv, hagree _ (hstay htc).1 (hstay htc).2]
    exact hdesc _ (hstay htc).1 (hstay htc).2 (hregular t htc)

end DifferentialGeometry.Morse
