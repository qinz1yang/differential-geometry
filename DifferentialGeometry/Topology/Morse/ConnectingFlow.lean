/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Morse.ConnectingOrbit
import DifferentialGeometry.Topology.Manifold.CompactSectionExtension
import DifferentialGeometry.Topology.Diffeomorph.Flow
import DifferentialGeometry.Analysis.Calculus.Inverse.ParameterizedInverse
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! Supported transport of level arcs along the original descending vector field. -/

open Set Filter Function
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Morse

private theorem exists_interval_thickening {a b : ℝ} (hab : a ≤ b)
    {U : Set ℝ} (hU : IsOpen U) (hsub : Icc a b ⊆ U) :
    ∃ l u : ℝ, l < a ∧ b < u ∧ Ioo l u ⊆ U := by
  obtain ⟨l, a', ⟨hla, haa'⟩, hl⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds (hsub ⟨le_rfl, hab⟩))
  obtain ⟨b', u, ⟨hb'b, hbu⟩, hu⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds (hsub ⟨hab, le_rfl⟩))
  refine ⟨l, u, hla, hbu, ?_⟩
  intro t ht
  by_cases hta : t < a
  · exact hl ⟨ht.1, hta.trans haa'⟩
  by_cases hbt : b < t
  · exact hu ⟨hb'b.trans hbt, ht.2⟩
  exact hsub ⟨le_of_not_gt hta, le_of_not_gt hbt⟩

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M] [T2Space M]

private theorem exists_supported_cutoff {K O : Set M} (hK : IsCompact K)
    (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ β : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ β ∧ HasCompactSupport β ∧
      tsupport β ⊆ O ∧ β =ᶠ[𝓝ˢ K] 1 := by
  classical
  obtain ⟨t, b, hb⟩ :=
    DifferentialGeometry.Topology.exists_finite_smoothBumpCovering_of_isCompact (I := I)
      hK (fun _ => O) (fun x hx => hO.mem_nhds (hKO hx))
  let β : M → ℝ := fun x => 1 - ∏ i : t, (1 - b i x)
  have hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β := by
    apply contMDiff_const.sub
    exact contMDiff_finsetProd fun i _ => contMDiff_const.sub (b i).contMDiff
  have hc : IsCompact (⋃ i : t, tsupport (b i)) :=
    isCompact_iUnion fun i => (b i).hasCompactSupport
  have hs : tsupport β ⊆ ⋃ i : t, tsupport (b i) := by
    apply closure_minimal ?_ hc.isClosed
    intro x hx
    by_contra hn
    have hz (i : t) : b i x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hi => hn (mem_iUnion.mpr ⟨i, hi⟩))
    exact hx (by simp [β, hz])
  refine ⟨β, hβ, hc.of_isClosed_subset (isClosed_tsupport β) hs, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hs hx)
    exact (hb i).2 hi
  · apply eventually_nhdsSet_iff_forall.mpr
    intro x hx
    filter_upwards [b.eventuallyEq_one x hx] with y hy
    have hz : ∏ i : t, (1 - b i y) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ (b.ind x hx)) (by rw [hy]; simp)
    simp only [β, hz, sub_zero, Pi.one_apply]

variable [I.Boundaryless]

theorem exists_descending_flow_tube {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent ∞ (fun x => (v x : TangentBundle I M)))
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ v) {a b : ℝ} (hab : a < b)
    (hnegative : ∀ t ∈ Icc a b, mvfderiv I f (γ t) (v (γ t)) < 0)
    {O : Set M} (hO : IsOpen O) (hγO : γ '' Icc a b ⊆ O) :
    ∃ (w : (x : M) → TangentSpace I x)
      (hw : ContMDiff I I.tangent ∞ (fun x => (w x : TangentBundle I M)))
      (hwc : HasCompactSupport w), tsupport w ⊆ O ∧
      ∃ U V : Set M, ∃ l u : ℝ,
        IsOpen U ∧ IsOpen V ∧ γ '' Icc a b ⊆ U ∧ U ⊆ O ∧ γ a ∈ V ∧
        l < 0 ∧ b - a < u ∧
        (∀ x ∈ U, w x = v x ∧ mvfderiv I f x (v x) < 0) ∧
        (∀ t ∈ Icc (0 : ℝ) (b - a),
          Diffeomorph.compactSupportFlow w hw hwc t (γ a) = γ (t + a)) ∧
        ∀ t ∈ Ioo l u, ∀ x ∈ V, Diffeomorph.compactSupportFlow w hw hwc t x ∈ U := by
  let K := γ '' Icc a b
  have hK : IsCompact K := isCompact_Icc.image hγ.continuous
  obtain ⟨β, hβ, hβc, hβO, hone⟩ := exists_supported_cutoff (I := I) hK hO hγO
  obtain ⟨N, hN, hKN, hNone⟩ := eventually_nhdsSet_iff_exists.mp hone
  have hr : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => mvfderiv I f x (v x)) := by
    exact (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ)).comp
      ((hf.contMDiff_tangentMap (m := ∞) (by simp)).comp hv)
  let U := N ∩ O ∩ {x | mvfderiv I f x (v x) < 0}
  have hU : IsOpen U := (hN.inter hO).inter (isOpen_lt hr.continuous continuous_const)
  have hKU : K ⊆ U := by
    rintro x ⟨t, ht, rfl⟩
    exact ⟨⟨hKN ⟨t, ht, rfl⟩, hγO ⟨t, ht, rfl⟩⟩, hnegative t ht⟩
  let w : (x : M) → TangentSpace I x := fun x => β x • v x
  have hw : ContMDiff I I.tangent ∞ (fun x => (w x : TangentBundle I M)) :=
    hβ.smul_section hv
  have hs : tsupport w ⊆ tsupport β := tsupport_smul_subset_left β v
  have hwc : HasCompactSupport w := hβc.of_isClosed_subset (isClosed_tsupport w) hs
  have hsame (x : M) (hx : x ∈ U) : w x = v x := by
    change β x • v x = v x
    rw [show β x = 1 from hNone x hx.1.1, one_smul]
  let Φ := Diffeomorph.compactSupportFlow w hw hwc
  have hΦ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => Φ p.1 p.2) :=
    Diffeomorph.contMDiff_compactSupportFlow w hw hwc
  have hz (x : M) : Φ 0 x = x :=
    DFunLike.congr_fun (Diffeomorph.compactSupportFlow_zero w hw hwc) x
  obtain ⟨α, upper, hα, hupper, hstay⟩ := exists_interval_thickening hab.le
    (hU.preimage hγ.continuous) (fun t ht => hKU ⟨t, ht, rfl⟩)
  have hcurve : IsMIntegralCurveOn (fun t => γ (t + a)) w (Ioo (α - a) (upper - a)) := by
    intro t ht
    have hmem : γ (t + a) ∈ U := hstay ⟨by linarith [ht.1], by linarith [ht.2]⟩
    rw [hsame _ hmem]
    exact ((hγ.comp_add a) t).hasMFDerivWithinAt
  have hagree : EqOn (fun t => Φ t (γ a)) (fun t => γ (t + a))
      (Ioo (α - a) (upper - a)) :=
    isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
      (show (0 : ℝ) ∈ Ioo (α - a) (upper - a) from ⟨by linarith, by linarith⟩)
      (hw.of_le (by simp))
      ((Diffeomorph.isMIntegralCurve_compactSupportFlow w hw hwc (γ a)).isMIntegralCurveOn _)
      hcurve (by simpa only [zero_add] using hz (γ a))
  have hcentral (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (b - a)) : Φ t (γ a) = γ (t + a) :=
    hagree ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨W, V, hW, hV, hIW, haV, htube⟩ :=
    generalized_tube_lemma (isCompact_Icc : IsCompact (Icc (0 : ℝ) (b - a)))
      (isCompact_singleton : IsCompact ({γ a} : Set M)) (hU.preimage hΦ.continuous) (by
        rintro ⟨t, x⟩ ⟨ht, rfl⟩
        change Φ t (γ a) ∈ U
        rw [hcentral t ht]
        exact hKU ⟨t + a, ⟨by linarith [ht.1], by linarith [ht.2]⟩, rfl⟩)
  obtain ⟨l, u, hl, hu, hlu⟩ := exists_interval_thickening (by linarith : 0 ≤ b - a) hW hIW
  exact ⟨w, hw, hwc, hs.trans hβO, U, V, l, u, hU, hV, hKU,
    fun _ hx => hx.1.2, haV (mem_singleton _), hl, hu,
    fun x hx => ⟨hsame x hx, hx.2⟩, hcentral,
    fun t ht x hx => htube (show (t, x) ∈ W ×ˢ V from ⟨hlu ht, hx⟩)⟩

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [I.Boundaryless] in
private theorem flow_strip_injOn {S : Set ℝ} {A : ℝ → M} {τ : ℝ → ℝ}
    {f : M → ℝ} {c : ℝ} (Φ : ℝ → Diffeomorph I I M M ∞)
    (hz : ∀ x, Φ 0 x = x) (hadd : ∀ s t x, Φ (s + t) x = Φ t (Φ s x))
    (hA : InjOn A S) (hlevel : ∀ x ∈ S, f (A x) = c)
    (hτ : ∀ x ∈ S, 0 < τ x)
    (hanti : ∀ x ∈ S, StrictAntiOn (fun t => f (Φ t (A x))) (Icc 0 (τ x))) :
    InjOn (fun p : ℝ × ℝ => Φ (p.2 * τ p.1) (A p.1)) (S ×ˢ Icc 0 1) := by
  have htime (p : ℝ × ℝ) (hp : p ∈ S ×ˢ Icc 0 1) :
      p.2 * τ p.1 ∈ Icc 0 (τ p.1) :=
    ⟨mul_nonneg hp.2.1 (hτ p.1 hp.1).le,
      by simpa only [one_mul] using mul_le_mul_of_nonneg_right hp.2.2 (hτ p.1 hp.1).le⟩
  have horder (p q : ℝ × ℝ) (hp : p ∈ S ×ˢ Icc 0 1) (hq : q ∈ S ×ˢ Icc 0 1)
      (heq : Φ (p.2 * τ p.1) (A p.1) = Φ (q.2 * τ q.1) (A q.1))
      (hle : p.2 * τ p.1 ≤ q.2 * τ q.1) : p = q := by
    let s := p.2 * τ p.1
    let t := q.2 * τ q.1
    have hback : A p.1 = Φ (t - s) (A q.1) := by
      have hh := congrArg (fun x => Φ (-s) x) heq
      change Φ (-s) (Φ s (A p.1)) = Φ (-s) (Φ t (A q.1)) at hh
      rw [← hadd, ← hadd, add_neg_cancel, hz] at hh
      simpa only [sub_eq_add_neg] using hh
    have hdiff : t - s ∈ Icc 0 (τ q.1) :=
      ⟨sub_nonneg.mpr hle, by linarith [(htime p hp).1, (htime q hq).2]⟩
    have hzero : (0 : ℝ) ∈ Icc 0 (τ q.1) := ⟨le_rfl, (hτ q.1 hq.1).le⟩
    have hd : t - s = 0 := by
      apply (hanti q.1 hq.1).injOn hdiff hzero
      change f (Φ (t - s) (A q.1)) = f (Φ 0 (A q.1))
      rw [← hback, hz, hlevel p.1 hp.1, hlevel q.1 hq.1]
    have heA : A p.1 = A q.1 := by simpa only [hd, hz] using hback
    have hpq := hA hp.1 hq.1 heA
    apply Prod.ext hpq
    apply mul_right_cancel₀ (ne_of_gt (hτ q.1 hq.1))
    rw [← hpq]
    dsimp [s, t] at hd
    rw [hpq] at hd ⊢
    linarith
  intro p hp q hq heq
  rcases le_total (p.2 * τ p.1) (q.2 * τ q.1) with hle | hle
  · exact horder p q hp hq heq hle
  · exact (horder q p hq hp heq.symm hle).symm

theorem exists_descending_arc_transport {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent ∞ (fun x => (v x : TangentBundle I M)))
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ v) {a b : ℝ} (hab : a < b)
    (hnegative : ∀ t ∈ Icc a b, mvfderiv I f (γ t) (v (γ t)) < 0)
    {O N : Set M} (hO : IsOpen O) (hγO : γ '' Icc a b ⊆ O)
    (hN : IsOpen N) (hbN : γ b ∈ N)
    {A : ℝ → M} {S : Set ℝ} (hS : IsOpen S)
    (hA : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ A S) (hAinj : InjOn A S)
    {s₀ : ℝ} (hs₀ : s₀ ∈ S) (hA₀ : A s₀ = γ a)
    (hlevel : ∀ s ∈ S, f (A s) = f (γ a)) :
    ∃ (w : (x : M) → TangentSpace I x)
      (hw : ContMDiff I I.tangent ∞ (fun x => (w x : TangentBundle I M)))
      (hwc : HasCompactSupport w), tsupport w ⊆ O ∧
      ∃ δ : ℝ, 0 < δ ∧ Icc (s₀ - δ) (s₀ + δ) ⊆ S ∧
      ∃ τ : ℝ → ℝ, ContDiffOn ℝ ∞ τ (Icc (s₀ - δ) (s₀ + δ)) ∧ τ s₀ = b - a ∧
        (∀ s ∈ Icc (s₀ - δ) (s₀ + δ), 0 < τ s) ∧
        let Φ := Diffeomorph.compactSupportFlow w hw hwc
        let F : ℝ × ℝ → M := fun z => Φ (z.2 * τ z.1) (A z.1)
        ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞ F
          (Icc (s₀ - δ) (s₀ + δ) ×ˢ Icc 0 1) ∧
        Topology.IsClosedEmbedding
          (fun z : Icc (s₀ - δ) (s₀ + δ) × Icc (0 : ℝ) 1 => F (z.1, z.2)) ∧
        (∀ s ∈ Icc (s₀ - δ) (s₀ + δ), F (s, 0) = A s ∧
          F (s, 1) ∈ N ∩ f ⁻¹' {f (γ b)}) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, F (s₀, t) = γ (t * (b - a) + a)) ∧
        (∀ z ∈ Icc (s₀ - δ) (s₀ + δ) ×ˢ Icc 0 1, F z ∈ O) ∧
        ∀ s ∈ Icc (s₀ - δ) (s₀ + δ), ∀ t ∈ Icc (0 : ℝ) (τ s),
          mvfderiv I f (Φ t (A s)) (v (Φ t (A s))) < 0 ∧
          HasMFDerivAt 𝓘(ℝ, ℝ) I (fun t => Φ t (A s)) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight (v (Φ t (A s)))) := by
  obtain ⟨w, hw, hwc, hwO, U, V, l, u, hU, hV, _, hUO, haV, hl, hu,
    hsame, hcentral, htube⟩ := exists_descending_flow_tube hf hv hγ hab hnegative hO hγO
  let Φ := Diffeomorph.compactSupportFlow w hw hwc
  have hΦ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => Φ p.1 p.2) :=
    Diffeomorph.contMDiff_compactSupportFlow w hw hwc
  have hz (x : M) : Φ 0 x = x :=
    DFunLike.congr_fun (Diffeomorph.compactSupportFlow_zero w hw hwc) x
  have hadd (s t : ℝ) (x : M) : Φ (s + t) x = Φ t (Φ s x) :=
    DFunLike.congr_fun (Diffeomorph.compactSupportFlow_add w hw hwc s t) x
  let d := b - a
  have hd : 0 < d := sub_pos.mpr hab
  have hhit : Φ d (A s₀) = γ b := by
    rw [hA₀, hcentral d ⟨hd.le, le_rfl⟩]
    simp only [d, sub_add_cancel]
  let H : ℝ × ℝ → ℝ := fun p => f (Φ p.2 (A p.1))
  have hH : ContDiffOn ℝ ∞ H (S ×ˢ univ) := by
    apply contMDiffOn_iff_contDiffOn.mp
    exact hf.comp_contMDiffOn (hΦ.comp_contMDiffOn
      (contDiffOn_snd.contMDiffOn.prodMk (hA.comp contDiffOn_fst.contMDiffOn
        (fun (p : ℝ × ℝ) (hp : p ∈ S ×ˢ univ) => hp.1))))
  have hp : (s₀, d) ∈ S ×ˢ (univ : Set ℝ) := ⟨hs₀, mem_univ _⟩
  have hvertical : fderiv ℝ H (s₀, d) (0, 1) ≠ 0 := by
    have hd₁ := DifferentialGeometry.Analysis.ODE.hasDerivAt_df_comp_integralCurve f hf w
      (Diffeomorph.isMIntegralCurve_compactSupportFlow w hw hwc (A s₀)) d
    have hd₂ : HasDerivAt (fun t => H (s₀, t)) (fderiv ℝ H (s₀, d) (0, 1)) d :=
      ((hH.contDiffAt ((hS.prod isOpen_univ).mem_nhds hp)).differentiableAt
        (by simp)).hasFDerivAt.comp_hasDerivAt d
        ((hasDerivAt_const d s₀).prodMk (hasDerivAt_id d))
    have hr : mvfderiv I f (Φ d (A s₀)) (w (Φ d (A s₀))) < 0 := by
      rw [(hsame _ (htube d ⟨by linarith, hu⟩ (A s₀) (hA₀ ▸ haV))).1, hhit]
      exact hnegative b ⟨hab.le, le_rfl⟩
    exact (hd₂.unique hd₁).trans_ne (ne_of_lt hr)
  obtain ⟨e, hep, _, _, hei, he, hparam⟩ :=
    DifferentialGeometry.Analysis.exists_localInverse_preserving_parameter hH
      (hS.prod isOpen_univ) hp hvertical
  let c := f (γ b)
  have hepval : e (s₀, d) = (s₀, c) := by rw [he]; exact Prod.ext rfl (congrArg f hhit)
  have htarg : (s₀, c) ∈ e.target := hepval ▸ e.map_source hep
  let τ : ℝ → ℝ := fun s => (e.symm (s, c)).2
  have hτ₀ : τ s₀ = d := by
    have hh := congrArg Prod.snd (e.left_inv hep)
    rw [hepval] at hh
    exact hh
  have hτat : ContDiffAt ℝ ∞ τ s₀ := by
    change ContDiffAt ℝ ∞ (fun s => (e.symm (s, c)).2) s₀
    exact ((hei.contDiffAt (e.open_target.mem_nhds htarg)).comp s₀
      (contDiffAt_id.prodMk contDiffAt_const)).snd
  have hend : Φ (τ s₀) (A s₀) = γ b := by rw [hτ₀]; exact hhit
  have hBcont : ContinuousAt (fun s => Φ (τ s) (A s)) s₀ :=
    hΦ.continuous.continuousAt.comp
      (hτat.continuousAt.prodMk (hA.contMDiffAt (hS.mem_nhds hs₀)).continuousAt)
  have hnear : ∀ᶠ s in 𝓝 s₀,
      s ∈ S ∧ (s, c) ∈ e.target ∧ A s ∈ V ∧ τ s ∈ Ioo 0 u ∧ Φ (τ s) (A s) ∈ N := by
    filter_upwards [hS.mem_nhds hs₀,
      (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
        (e.open_target.mem_nhds htarg),
      (hA.contMDiffAt (hS.mem_nhds hs₀)).continuousAt.preimage_mem_nhds
        (hV.mem_nhds (hA₀ ▸ haV)),
      hτat.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds
        (show τ s₀ ∈ Ioo 0 u by rw [hτ₀]; exact ⟨hd, hu⟩)),
      hBcont.preimage_mem_nhds (hN.mem_nhds (hend ▸ hbN))] with s hs heS hAs hτs hNs
    exact ⟨hs, heS, hAs, hτs, hNs⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let δ := r / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let J := Icc (s₀ - δ) (s₀ + δ)
  have hJ (s : ℝ) (hs : s ∈ J) :
      s ∈ S ∧ (s, c) ∈ e.target ∧ A s ∈ V ∧ τ s ∈ Ioo 0 u ∧ Φ (τ s) (A s) ∈ N := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    dsimp [J, δ] at hs
    constructor <;> linarith [hs.1, hs.2]
  have hτ : ContDiffOn ℝ ∞ τ J := by
    intro s hs
    change ContDiffWithinAt ℝ ∞ (fun s => (e.symm (s, c)).2) J s
    exact (((hei.contDiffAt (e.open_target.mem_nhds (hJ s hs).2.1)).comp s
      (contDiffAt_id.prodMk contDiffAt_const)).snd).contDiffWithinAt
  have hroot (s : ℝ) (hs : s ∈ J) : f (Φ (τ s) (A s)) = c := by
    have hh := hparam (s, c) (hJ s hs).2.1
    have heq : (s, τ s) = e.symm (s, c) := Prod.ext hh.1.symm rfl
    exact (congrArg H heq).trans hh.2
  have hstay (s : ℝ) (hs : s ∈ J) (t : ℝ) (ht : t ∈ Icc 0 (τ s)) : Φ t (A s) ∈ U :=
    htube t ⟨hl.trans_le ht.1, ht.2.trans_lt (hJ s hs).2.2.2.1.2⟩ (A s) (hJ s hs).2.2.1
  have hanti (s : ℝ) (hs : s ∈ J) :
      StrictAntiOn (fun t => f (Φ t (A s))) (Icc 0 (τ s)) := by
    have hd' (t : ℝ) := DifferentialGeometry.Analysis.ODE.hasDerivAt_df_comp_integralCurve f hf w
      (Diffeomorph.isMIntegralCurve_compactSupportFlow w hw hwc (A s)) t
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (fun t _ => (hd' t).continuousAt.continuousWithinAt)
    intro t ht
    rw [(hd' t).deriv]
    have hh := hsame _ (hstay s hs t (interior_subset ht))
    change mvfderiv I f (Φ t (A s)) (w (Φ t (A s))) < 0
    rw [hh.1]
    exact hh.2
  let F : ℝ × ℝ → M := fun z => Φ (z.2 * τ z.1) (A z.1)
  have hF : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞ F (J ×ˢ Icc 0 1) := by
    exact hΦ.comp_contMDiffOn
      ((contMDiffOn_snd.mul (hτ.contMDiffOn.comp contMDiffOn_fst (fun _ hz => hz.1))).prodMk
        (hA.comp contMDiffOn_fst (fun z hz => (hJ z.1 hz.1).1)))
  have hinj : InjOn F (J ×ˢ Icc 0 1) := flow_strip_injOn Φ hz hadd
    (hAinj.mono (fun s hs => (hJ s hs).1)) (fun s hs => hlevel s (hJ s hs).1)
    (fun s hs => (hJ s hs).2.2.2.1.1) hanti
  have hemb : Topology.IsClosedEmbedding
      (fun z : J × Icc (0 : ℝ) 1 => F (z.1, z.2)) := by
    have hc : Continuous (fun z : J × Icc (0 : ℝ) 1 => F (z.1, z.2)) :=
      hF.continuousOn.comp_continuous
        ((continuous_subtype_val.comp continuous_fst).prodMk
          (continuous_subtype_val.comp continuous_snd)) (fun z => ⟨z.1.2, z.2.2⟩)
    apply hc.isClosedEmbedding
    intro z z' heq
    have hh := hinj ⟨z.1.2, z.2.2⟩ ⟨z'.1.2, z'.2.2⟩ heq
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hh)) (Subtype.ext (congrArg Prod.snd hh))
  refine ⟨w, hw, hwc, hwO, δ, hδ, (fun s hs => (hJ s hs).1), τ, hτ, hτ₀,
    (fun s hs => (hJ s hs).2.2.2.1.1), hF, hemb, ?_, ?_, ?_, ?_⟩
  · intro s hs
    constructor
    · change Φ (0 * τ s) (A s) = A s
      rw [zero_mul, hz]
    · change Φ (1 * τ s) (A s) ∈ N ∩ f ⁻¹' {f (γ b)}
      rw [one_mul]
      exact ⟨(hJ s hs).2.2.2.2, hroot s hs⟩
  · intro t ht
    change Φ (t * τ s₀) (A s₀) = _
    rw [hτ₀, hA₀]
    apply hcentral
    exact ⟨mul_nonneg ht.1 hd.le,
      by simpa only [one_mul] using mul_le_mul_of_nonneg_right ht.2 hd.le⟩
  · intro z hz'
    exact hUO (hstay z.1 hz'.1 (z.2 * τ z.1)
      ⟨mul_nonneg hz'.2.1 (hJ z.1 hz'.1).2.2.2.1.1.le,
        by simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hz'.2.2 (hJ z.1 hz'.1).2.2.2.1.1.le⟩)
  · intro s hs t ht
    refine ⟨(hsame _ (hstay s hs t ht)).2, ?_⟩
    rw [← (hsame _ (hstay s hs t ht)).1]
    exact Diffeomorph.isMIntegralCurve_compactSupportFlow w hw hwc (A s) t

end DifferentialGeometry.Morse
