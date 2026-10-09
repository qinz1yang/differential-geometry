import DifferentialGeometry.Geometry.Exponential.FiniteMetric.RadialLength
import Mathlib.Geometry.Manifold.Riemannian.Basic

/-!
# Normal balls of a finite-regularity metric

Let `e` agree with `exp_x` on the `g_x`-ball of radius `ρ > 0`, with `C^r` inverse (`2 ≤ r`). Then
`dist x (e v) = |v|_{g_x}` and `e.target` is the metric ball of radius `ρ`
(`expChart_dist_eq_and_target_eq_ball`): the radial geodesics have length `|v|` (speed
conservation) and every curve leaving a smaller normal ball is long (radial length bound).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter MeasureTheory Metric
open scoped Manifold ContDiff Topology ENNReal

namespace Bundle.ContMDiffRiemannianMetric

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  {r : ℕ∞} (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))

/-- The radial geodesic has length `|v|`: `dist x (exp_x v) ≤ |v|`. -/
theorem dist_expMap_le (hr : 1 ≤ r)
    (hnorm : ∀ (y : M) (w : TangentSpace I y), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (x : M) (v : E)
    (hv : ∀ t ∈ Icc (0 : ℝ) 1, ((⟨x, v⟩ : TangentBundle I M), t) ∈ g.geodesicFlowDomain) :
    dist x (g.expMap (⟨x, v⟩ : TangentBundle I M)) ≤ Real.sqrt (g.inner x v v) := by
  set γ : ℝ → M := fun t => (g.geodesicFlow (⟨x, v⟩ : TangentBundle I M) t).proj with hγ
  have hγc : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 1) := by
    intro t ht
    have hflow := (g.contMDiffOn_geodesicFlow hr).contMDiffAt
      ((g.isOpen_geodesicFlowDomain hr).mem_nhds (hv t ht))
    have hin : ContMDiffAt 𝓘(ℝ, ℝ) (I.tangent.prod 𝓘(ℝ, ℝ)) r
        (fun s : ℝ => ((⟨x, v⟩ : TangentBundle I M), s)) t :=
      contMDiffAt_const.prodMk contMDiffAt_id
    have h := (Bundle.contMDiff_proj (TangentSpace I)).contMDiffAt.comp t (hflow.comp t hin)
    exact (h.of_le (by exact_mod_cast hr)).contMDiffWithinAt
  have h0 : γ 0 = x := by simp only [hγ, g.geodesicFlow_zero hr]
  have hle := Manifold.riemannianEDist_le_pathELength (I := I) hγc h0 rfl zero_le_one
  rw [← IsRiemannianManifold.out (I := I)] at hle
  have hlen : Manifold.pathELength I γ 0 1 = ENNReal.ofReal (Real.sqrt (g.inner x v v)) := by
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
    have hconst : ∀ t ∈ Ioo (0 : ℝ) 1,
        ‖mfderiv 𝓘(ℝ, ℝ) I γ t 1‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)) := by
      intro t ht
      have htD := hv t (Ioo_subset_Icc_self ht)
      rw [(g.hasMFDerivAt_geodesicFlow_proj hr htD).mfderiv, hnorm]
      have hsp := g.inner_geodesicFlow_eq hr _ t htD
      congr 2
      change g.inner (γ t) (((1 : ℝ →L[ℝ] ℝ) 1) • (g.geodesicFlow (⟨x, v⟩ : TangentBundle I M) t).snd)
        (((1 : ℝ →L[ℝ] ℝ) 1) • (g.geodesicFlow (⟨x, v⟩ : TangentBundle I M) t).snd) = _
      rw [one_apply_eq_self, one_smul]
      exact hsp
    rw [setLIntegral_congr_fun measurableSet_Ioo hconst]
    simp
  rw [hlen, edist_dist] at hle
  exact (ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg _)).mp hle

omit [IsRiemannianManifold I M] in
/-- **First exit from a normal ball.** A `C¹` curve from `x` of length `< ρ'` (with `ρ' < ρ`)
stays inside the `g_x`-ball of radius `ρ'` of a chart agreeing with `exp_x`. -/
theorem mem_expChart_of_pathELength_lt (hr : 2 ≤ r)
    (hnorm : ∀ (y : M) (w : TangentSpace I y), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    {x : M} {ρ : ℝ} (e : OpenPartialHomeomorph E M)
    (hsrc : e.source = {v : E | g.inner x v v < ρ ^ 2})
    (hexp : ∀ v ∈ e.source, (⟨x, v⟩ : TangentBundle I M) ∈ g.expDomain ∧
      e v = g.expMap (⟨x, v⟩ : TangentBundle I M))
    (hsymm : ContMDiffOn I 𝓘(ℝ, E) r e.symm e.target)
    {ρ' : ℝ} (hρ'0 : 0 < ρ') (hρ' : ρ' < ρ)
    {γ : ℝ → M} {a b : ℝ} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b)) (hγa : γ a = x)
    (hlen : Manifold.pathELength I γ a b < ENNReal.ofReal ρ') :
    ∀ t ∈ Icc a b, γ t ∈ e.target ∧ g.inner x (e.symm (γ t)) (e.symm (γ t)) < ρ' ^ 2 := by
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have hρ2 : ρ' ^ 2 < ρ ^ 2 := by nlinarith
  have hg0 : g.inner x (0 : TangentSpace I x) (0 : TangentSpace I x) = 0 := by simp
  have h0src : (0 : E) ∈ e.source := by
    rw [hsrc]
    change g.inner x (0 : TangentSpace I x) (0 : TangentSpace I x) < ρ ^ 2
    rw [hg0]
    exact pow_pos (hρ'0.trans hρ') 2
  have he0 : e 0 = x := by
    rw [(hexp 0 h0src).2]
    exact g.expMap_zero hr1 x
  set Bo : Set E := {v : E | g.inner x v v < ρ' ^ 2} with hBo
  set Bc : Set E := {v : E | g.inner x v v ≤ ρ' ^ 2} with hBc
  have hcont : Continuous fun v : E => g.inner x v v :=
    (g.inner x : E →L[ℝ] E →L[ℝ] ℝ).continuous.clm_apply continuous_id
  have hBc_src : Bc ⊆ e.source := fun v hv => by
    rw [hsrc]
    exact lt_of_le_of_lt hv hρ2
  have hBoBc : Bo ⊆ Bc := fun v (hv : g.inner x v v < ρ' ^ 2) =>
    (le_of_lt hv : g.inner x v v ≤ ρ' ^ 2)
  have hBo_open : IsOpen Bo := isOpen_lt hcont continuous_const
  have hBc_compact : IsCompact Bc := by
    obtain ⟨c, hc, hcoer⟩ := ContinuousLinearMap.isCoercive_of_posDef (F := E)
      (g.inner x : E →L[ℝ] E →L[ℝ] ℝ) (fun v hv => g.pos x v hv)
    have : ProperSpace E := FiniteDimensional.proper_rclike ℝ E
    apply Metric.isCompact_of_isClosed_isBounded (isClosed_le hcont continuous_const)
    rw [Metric.isBounded_iff_subset_closedBall (0 : E)]
    refine ⟨ρ' / Real.sqrt c, fun v hv => ?_⟩
    rw [mem_closedBall, dist_zero_right, le_div_iff₀ (Real.sqrt_pos.mpr hc)]
    have h1 := hcoer v
    have h2 : c * ‖v‖ ^ 2 ≤ ρ' ^ 2 :=
      calc c * ‖v‖ ^ 2 = c * ‖v‖ * ‖v‖ := by ring
        _ ≤ g.inner x v v := h1
        _ ≤ ρ' ^ 2 := (hv : g.inner x v v ≤ ρ' ^ 2)
    have h3 : (‖v‖ * Real.sqrt c) ^ 2 ≤ ρ' ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hc.le]
      linarith
    exact (pow_le_pow_iff_left₀ (by positivity) hρ'0.le (by norm_num)).mp h3
  set O := e '' Bo with hOdef
  set K := e '' Bc with hKdef
  have hO : IsOpen O := e.isOpen_image_of_subset_source hBo_open (hBoBc.trans hBc_src)
  have hK : IsClosed K :=
    (hBc_compact.image_of_continuousOn (e.continuousOn.mono hBc_src)).isClosed
  have hOK : O ⊆ K := Set.image_mono hBoBc
  have hKt : K ⊆ e.target := by
    rintro _ ⟨v, hv, rfl⟩
    exact e.map_source (hBc_src hv)
  have hmemO : ∀ y ∈ e.target, y ∈ O ↔ g.inner x (e.symm y) (e.symm y) < ρ' ^ 2 := by
    intro y hy
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [e.left_inv (hBc_src (hBoBc hv))]
      exact hv
    · intro h
      exact ⟨e.symm y, h, e.right_inv hy⟩
  have h0Bo : (0 : E) ∈ Bo := by
    change g.inner x (0 : TangentSpace I x) (0 : TangentSpace I x) < ρ' ^ 2
    rw [hg0]
    exact pow_pos hρ'0 2
  have haO : γ a ∈ O := by
    rw [hγa, ← he0]
    exact mem_image_of_mem e h0Bo
  suffices hall : ∀ t ∈ Icc a b, γ t ∈ O by
    intro t ht
    have h := hall t ht
    exact ⟨hKt (hOK h), (hmemO _ (hKt (hOK h))).mp h⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨t₁, ht₁, ht₁O⟩ := hcon
  set S := Icc a b ∩ γ ⁻¹' Oᶜ with hSdef
  have hS : IsClosed S :=
    hγ.continuousOn.preimage_isClosed_of_isClosed isClosed_Icc hO.isClosed_compl
  have hSne : S.Nonempty := ⟨t₁, ht₁, ht₁O⟩
  have hSbdd : BddBelow S := ⟨a, fun s hs => hs.1.1⟩
  set τ := sInf S with hτdef
  have hτS : τ ∈ S := hS.csInf_mem hSne hSbdd
  have hbefore : ∀ s ∈ Icc a b, s < τ → γ s ∈ O := by
    intro s hs hlt
    by_contra h
    exact absurd (csInf_le hSbdd ⟨hs, h⟩) (not_le.mpr hlt)
  have haτ : a < τ := lt_of_le_of_ne hτS.1.1 (fun h => hτS.2 (h ▸ haO))
  have hτK : γ τ ∈ K := by
    have hcw : ContinuousWithinAt γ (Ico a τ) τ :=
      (hγ.continuousOn τ hτS.1).mono (fun s hs => ⟨hs.1, hs.2.le.trans hτS.1.2⟩)
    have hcl : τ ∈ closure (Ico a τ) := by
      rw [closure_Ico haτ.ne]
      exact right_mem_Icc.mpr haτ.le
    have h := hcw.mem_closure_image hcl
    refine closure_minimal ?_ hK h
    rintro _ ⟨s, hs, rfl⟩
    exact hOK (hbefore s ⟨hs.1, hs.2.le.trans hτS.1.2⟩ hs.2)
  have hmaps : MapsTo γ (Icc a τ) e.target := by
    intro s hs
    rcases eq_or_lt_of_le hs.2 with h | h
    · rw [h]
      exact hKt hτK
    · exact hKt (hOK (hbefore s ⟨hs.1, h.le.trans hτS.1.2⟩ h))
  have hrad := g.ofReal_sub_le_pathELength_of_expChart hr hnorm e hexp hsymm haτ.le
    (hγ.mono (Icc_subset_Icc le_rfl hτS.1.2)) hmaps
  have hsa : e.symm (γ a) = 0 := by
    rw [hγa, ← he0, e.left_inv h0src]
  have hsτ : g.inner x (e.symm (γ τ)) (e.symm (γ τ)) = ρ' ^ 2 := by
    have hle : g.inner x (e.symm (γ τ)) (e.symm (γ τ)) ≤ ρ' ^ 2 := by
      obtain ⟨v, hv, hvτ⟩ := hτK
      rw [← hvτ, e.left_inv (hBc_src hv)]
      exact hv
    have hnlt : ¬ g.inner x (e.symm (γ τ)) (e.symm (γ τ)) < ρ' ^ 2 :=
      fun h => hτS.2 ((hmemO _ (hKt hτK)).mpr h)
    exact le_antisymm hle (not_lt.mp hnlt)
  rw [hsa, hsτ, Real.sqrt_sq hρ'0.le] at hrad
  have hz : Real.sqrt (g.inner x (0 : E) (0 : E)) = 0 := by
    rw [show g.inner x (0 : E) (0 : E) = 0 from hg0, Real.sqrt_zero]
  rw [hz, sub_zero] at hrad
  have hmono := Manifold.pathELength_mono (I := I) (γ := γ) (le_refl a) hτS.1.2
  exact absurd (hrad.trans hmono) (not_le.mpr hlen)

/-- **Normal balls.** A chart agreeing with `exp_x` on the `g_x`-ball of radius `ρ > 0`, with `C^r`
inverse, has the metric ball of radius `ρ` as target, and `dist x (e v) = |v|_{g_x}`. -/
theorem expChart_target_eq_ball_and_dist_eq (hr : 2 ≤ r)
    (hnorm : ∀ (y : M) (w : TangentSpace I y), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    {x : M} {ρ : ℝ} (hρ : 0 < ρ) (e : OpenPartialHomeomorph E M)
    (hsrc : e.source = {v : E | g.inner x v v < ρ ^ 2})
    (hexp : ∀ v ∈ e.source, (⟨x, v⟩ : TangentBundle I M) ∈ g.expDomain ∧
      e v = g.expMap (⟨x, v⟩ : TangentBundle I M))
    (hsymm : ContMDiffOn I 𝓘(ℝ, E) r e.symm e.target) :
    e.target = ball x ρ ∧ ∀ v ∈ e.source, dist x (e v) = Real.sqrt (g.inner x v v) := by
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  -- curves of small length from `x`
  have hcurve : ∀ y : M, ∀ ρ' : ℝ, 0 < ρ' → ρ' < ρ → dist x y < ρ' →
      y ∈ e.target ∧ g.inner x (e.symm y) (e.symm y) < ρ' ^ 2 := by
    intro y ρ' hρ'0 hρ' hd
    have hlt : Manifold.riemannianEDist I x y < ENNReal.ofReal ρ' := by
      rw [← IsRiemannianManifold.out (I := I), edist_dist]
      exact (ENNReal.ofReal_lt_ofReal_iff hρ'0).mpr hd
    obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hlt
    have h := g.mem_expChart_of_pathELength_lt hr hnorm e hsrc hexp hsymm hρ'0 hρ' hγ hγ0 hlen
      1 (right_mem_Icc.mpr zero_le_one)
    rwa [hγ1] at h
  have hdist : ∀ v ∈ e.source, dist x (e v) = Real.sqrt (g.inner x v v) := by
    intro v hv
    have hv' : g.inner x v v < ρ ^ 2 := by rw [hsrc] at hv; exact hv
    apply le_antisymm
    · rw [(hexp v hv).2]
      apply g.dist_expMap_le hr1 hnorm x v
      intro t ht
      apply (mem_expDomain_smul_iff hr1).mp
      apply (hexp _ _).1
      rw [hsrc]
      change g.inner x (t • v) (t • v) < ρ ^ 2
      have hquad : ∀ B : E →L[ℝ] E →L[ℝ] ℝ, B (t • v) (t • v) = t ^ 2 * B v v := by
        intro B
        simp only [map_smul, smul_apply, smul_eq_mul]
        ring
      have h1 : g.inner x (t • v) (t • v) = t ^ 2 * g.inner x v v := hquad (g.inner x)
      rw [h1]
      have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
      have hgn : 0 ≤ g.inner x v v := g.inner_self_nonneg' x v
      nlinarith
    · by_contra hcon
      push Not at hcon
      set s₀ := Real.sqrt (g.inner x v v)
      have hs₀ : s₀ < ρ := (Real.sqrt_lt' hρ).mpr hv'
      set ρ' := (dist x (e v) + s₀) / 2
      have hρ'0 : 0 < ρ' := by
        have := dist_nonneg (x := x) (y := e v)
        change 0 < (dist x (e v) + s₀) / 2
        linarith
      have h := hcurve (e v) ρ' hρ'0 (by change (dist x (e v) + s₀) / 2 < ρ; linarith)
        (by change dist x (e v) < (dist x (e v) + s₀) / 2; linarith)
      rw [e.left_inv hv] at h
      have h2 : s₀ < ρ' := (Real.sqrt_lt' hρ'0).mpr h.2
      change s₀ < (dist x (e v) + s₀) / 2 at h2
      linarith
  refine ⟨?_, hdist⟩
  ext y
  constructor
  · intro hy
    rw [mem_ball, dist_comm, ← e.right_inv hy, hdist _ (e.map_target hy)]
    have h := e.map_target hy
    rw [hsrc] at h
    exact (Real.sqrt_lt' hρ).mpr h
  · intro hy
    rw [mem_ball, dist_comm] at hy
    set ρ' := (dist x y + ρ) / 2
    have hρ'0 : 0 < ρ' := by
      have := dist_nonneg (x := x) (y := y)
      change 0 < (dist x y + ρ) / 2
      linarith
    exact (hcurve y ρ' hρ'0 (by change (dist x y + ρ) / 2 < ρ; linarith)
      (by change dist x y < (dist x y + ρ) / 2; linarith)).1

end Bundle.ContMDiffRiemannianMetric
