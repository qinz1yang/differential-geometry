import DifferentialGeometry.Analysis.ODE.GeodesicLimits.ChristoffelLimit
import DifferentialGeometry.Analysis.ODE.Stability.Tube
import DifferentialGeometry.Analysis.Calculus.Compactness.Lipschitz
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# CM4.c: continuous dependence on a `C⁰`-converging field with a Lipschitz limit

Binding kernel of the geodesic-limit package (lane CM-L; design item G5; blueprint LC50, A:22511, and
LFR18, A:26261). The approximating fields need not be Lipschitz uniformly: under `C¹` convergence of
metrics the Christoffel symbols converge only in `C⁰`. Grönwall is run with the Lipschitz constant of
the LIMIT field on a compact tube around the limit trajectory; the approximants cannot leave the tube
(first-exit argument), so no confinement hypothesis on them is needed, and the WHOLE sequence
converges (no subsequence).

* `tendstoUniformlyOn_of_tendsto_of_lipschitzOnWith_limit`: autonomous fields on a normed space.
* `tendstoUniformlyOn_of_christoffel_tendsto`: the geodesic form (`Γ i → ΓInf` uniformly on compact
  subsets of an open `U`, `ΓInf` of class `C¹` on `U`): position and velocity converge uniformly.

The tree's `integralCurve_tendstoUniformlyOn_of_limit_tube` (`Analysis/ODE/Stability/Tube.lean`) is
the twin with Lipschitz constants of the approximating fields.
-/

set_option autoImplicit false

noncomputable section

open Filter Set Topology Metric
open scoped NNReal

namespace DifferentialGeometry.Analysis.ODE.GeodesicLimits

theorem exists_pos_gronwallBound_lt_of_pos (L T R : ℝ) (hR : 0 < R) :
    ∃ θ : ℝ, 0 < θ ∧ θ < R ∧ gronwallBound θ L θ T < R := by
  let e : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have he : Tendsto e atTop (𝓝 0) := by
    simpa [e] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hbound : Tendsto (fun n => gronwallBound (e n) L (e n) T) atTop (𝓝 0) :=
    (DifferentialGeometry.Analysis.ODE.tendsto_gronwallBound_zero_zero L T).comp
      (he.prodMk_nhds he)
  obtain ⟨n, hnBound, hnSmall⟩ :=
    ((Metric.tendsto_nhds.mp hbound R hR).and (Metric.tendsto_nhds.mp he R hR)).exists
  have hen : 0 < e n := by
    dsimp [e]
    positivity
  refine ⟨e n, hen, ?_, ?_⟩
  · simpa [Real.dist_eq, abs_of_pos hen] using hnSmall
  · exact (le_abs_self _).trans_lt (by simpa [Real.dist_eq] using hnBound)

/-- **Continuous dependence with a Lipschitz limit field.** Solutions of `z' = v i z` on `[a,b]` whose
initial values converge to that of a solution of `z' = vInf z` converge uniformly on `[a,b]`, provided
`vInf` is Lipschitz and `v i → vInf` uniformly on a closed `r`-tube around the limit trajectory. -/
theorem tendstoUniformlyOn_of_tendsto_of_lipschitzOnWith_limit
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {a b r : ℝ} (hr : 0 < r)
    {v : ℕ → X → X} {vInf : X → X} {z : ℕ → ℝ → X} {zInf : ℝ → X}
    (hz : ∀ i, ∀ t ∈ Icc a b, HasDerivWithinAt (z i) (v i (z i t)) (Icc a b) t)
    (hzInf : ∀ t ∈ Icc a b, HasDerivWithinAt zInf (vInf (zInf t)) (Icc a b) t)
    {L : ℝ≥0} (hLip : LipschitzOnWith L vInf (cthickening r (zInf '' Icc a b)))
    (hconv : TendstoUniformlyOn v vInf atTop (cthickening r (zInf '' Icc a b)))
    (hinit : Tendsto (fun i => z i a) atTop (𝓝 (zInf a))) :
    TendstoUniformlyOn z zInf atTop (Icc a b) := by
  rcases lt_or_ge b a with hba | hab
  · rw [Icc_eq_empty_of_lt hba]
    exact tendstoUniformlyOn_empty
  set S := cthickening r (zInf '' Icc a b) with hS
  have hmemS : ∀ s ∈ Icc a b, ∀ x : X, dist x (zInf s) ≤ r → x ∈ S := fun s hs x hx =>
    mem_cthickening_of_dist_le x (zInf s) r _ (mem_image_of_mem zInf hs) hx
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set R : ℝ := min r ε with hRdef
  have hR : 0 < R := lt_min hr hε
  obtain ⟨θ, hθ, hθR, hgb⟩ := exists_pos_gronwallBound_lt_of_pos (L : ℝ) (b - a) R hR
  filter_upwards [Metric.tendsto_nhds.mp hinit θ hθ,
    Metric.tendstoUniformlyOn_iff.mp hconv θ hθ] with i hi hv t ht
  let d : ℝ → ℝ := fun s => dist (z i s) (zInf s)
  have hzc : ContinuousOn (z i) (Icc a b) := fun s hs => (hz i s hs).continuousWithinAt
  have hzInfc : ContinuousOn zInf (Icc a b) := fun s hs => (hzInf s hs).continuousWithinAt
  have hdc : ContinuousOn d (Icc a b) := continuous_dist.comp_continuousOn (hzc.prodMk hzInfc)
  have hda : d a < R := hi.trans hθR
  have hdlt : ∀ s ∈ Icc a b, d s < R := by
    intro s hs
    by_contra hnot
    obtain ⟨τ, hτ, hτeq, hτbefore⟩ :=
      DifferentialGeometry.Analysis.ODE.exists_first_hit_Icc hab hdc hda ⟨s, hs, le_of_not_gt hnot⟩
    have hsub : ∀ u ∈ Ico a τ, u ∈ Icc a b := fun u hu => ⟨hu.1, (hu.2.le).trans hτ.2⟩
    have hsubIco : ∀ u ∈ Ico a τ, u ∈ Ico a b := fun u hu => ⟨hu.1, hu.2.trans_le hτ.2⟩
    have hIcc : Icc a τ ⊆ Icc a b := fun u hu => ⟨hu.1, hu.2.trans hτ.2⟩
    have hin : ∀ u ∈ Ico a τ, z i u ∈ S := fun u hu =>
      hmemS u (hsub u hu) _ ((hτbefore u (Ico_subset_Icc_self hu)).trans (min_le_left r ε))
    have hcompare := dist_le_of_approx_trajectories_ODE_of_mem
      (v := fun _ => vInf) (s := fun _ => S) (K := L) (f := zInf) (g := z i)
      (f' := fun u => vInf (zInf u)) (g' := fun u => v i (z i u))
      (a := a) (b := τ) (εf := 0) (εg := θ) (δ := θ)
      (fun _ _ => hLip) (hzInfc.mono hIcc)
      (fun u hu => (hzInf u (hsub u hu)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem (hsubIco u hu)))
      (fun u _ => by simp)
      (fun u hu => hmemS u (hsub u hu) _ (by simpa using hr.le))
      (hzc.mono hIcc)
      (fun u hu => (hz i u (hsub u hu)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem (hsubIco u hu)))
      (fun u hu => by rw [dist_comm]; exact (hv _ (hin u hu)).le)
      hin (by rw [dist_comm]; exact hi.le) τ ⟨hτ.1, le_rfl⟩
    have hmono : gronwallBound θ (L : ℝ) (0 + θ) (τ - a) ≤ gronwallBound θ (L : ℝ) θ (b - a) := by
      rw [zero_add]
      exact gronwallBound_mono hθ.le hθ.le L.coe_nonneg (sub_le_sub_right hτ.2 a)
    have hdτ : d τ ≤ gronwallBound θ (L : ℝ) (0 + θ) (τ - a) := by
      simpa only [d, dist_comm] using hcompare
    linarith
  calc dist (zInf t) (z i t) = d t := dist_comm _ _
    _ < R := hdlt t ht
    _ ≤ ε := min_le_right r ε

/-- Under the sup metric of a product, the first component of a point of the closed `r`-thickening of
`(c, c') '' s` lies in the closed `r`-thickening of `c '' s`. -/
theorem fst_mem_cthickening_image {α F G : Type*} [PseudoMetricSpace F] [PseudoMetricSpace G]
    {c : α → F} {c' : α → G} {s : Set α} {r : ℝ} {q : F × G}
    (hq : q ∈ cthickening r ((fun t => (c t, c' t)) '' s)) : q.1 ∈ cthickening r (c '' s) := by
  rw [mem_cthickening_iff] at hq ⊢
  refine le_trans (Metric.le_infEDist.2 fun y hy => ?_) hq
  obtain ⟨t, ht, rfl⟩ := hy
  calc Metric.infEDist q.1 (c '' s) ≤ edist q.1 (c t) :=
        Metric.infEDist_le_edist_of_mem (mem_image_of_mem c ht)
    _ ≤ edist q (c t, c' t) := by rw [Prod.edist_eq]; exact le_max_left _ _

/-- **CM4.c, geodesic form.** Let `Γ i → ΓInf` uniformly on compact subsets of an open `U ⊆ F`, with
`ΓInf` of class `C¹` on `U` (a `C²` limit metric). If `(c, c')` solves the limit geodesic equation on
`[a,b]` inside `U` and solutions `(γ i, γ' i)` of the `Γ i`-equations have converging initial data,
then positions and velocities converge uniformly on `[a,b]` (whole sequence). -/
theorem tendstoUniformlyOn_of_christoffel_tendsto
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {U : Set F} (hU : IsOpen U) (Γ : ℕ → F → F →L[ℝ] F →L[ℝ] F)
    (ΓInf : F → F →L[ℝ] F →L[ℝ] F) (hΓInf : ContDiffOn ℝ 1 ΓInf U)
    (hconv : ∀ C : Set F, IsCompact C → C ⊆ U → TendstoUniformlyOn Γ ΓInf atTop C)
    {a b : ℝ} (c c' : ℝ → F) (hcU : ∀ t ∈ Icc a b, c t ∈ U)
    (hc : ∀ t ∈ Icc a b, HasDerivWithinAt c (c' t) (Icc a b) t)
    (hc' : ∀ t ∈ Icc a b, HasDerivWithinAt c' (-(ΓInf (c t) (c' t) (c' t))) (Icc a b) t)
    (γ γ' : ℕ → ℝ → F)
    (hvel : ∀ i, ∀ t ∈ Icc a b, HasDerivWithinAt (γ i) (γ' i t) (Icc a b) t)
    (hacc : ∀ i, ∀ t ∈ Icc a b,
      HasDerivWithinAt (γ' i) (-(Γ i (γ i t) (γ' i t) (γ' i t))) (Icc a b) t)
    (h0 : Tendsto (fun i => γ i a) atTop (𝓝 (c a)))
    (h0' : Tendsto (fun i => γ' i a) atTop (𝓝 (c' a))) :
    TendstoUniformlyOn γ c atTop (Icc a b) ∧ TendstoUniformlyOn γ' c' atTop (Icc a b) := by
  let zInf : ℝ → F × F := fun t => (c t, c' t)
  let z : ℕ → ℝ → F × F := fun i t => (γ i t, γ' i t)
  let vInf : F × F → F × F := fun q => (q.2, -(ΓInf q.1 q.2 q.2))
  let v : ℕ → F × F → F × F := fun i q => (q.2, -(Γ i q.1 q.2 q.2))
  have hcc : ContinuousOn c (Icc a b) := fun t ht => (hc t ht).continuousWithinAt
  have hc'c : ContinuousOn c' (Icc a b) := fun t ht => (hc' t ht).continuousWithinAt
  have himg : IsCompact (zInf '' Icc a b) := isCompact_Icc.image_of_continuousOn (hcc.prodMk hc'c)
  have hcimg : IsCompact (c '' Icc a b) := isCompact_Icc.image_of_continuousOn hcc
  obtain ⟨r, hr, hrU⟩ := hcimg.exists_cthickening_subset_open hU
    (by rintro _ ⟨t, ht, rfl⟩; exact hcU t ht)
  have hK₁ : IsCompact (cthickening r (c '' Icc a b)) := hcimg.cthickening
  have hS : IsCompact (cthickening r (zInf '' Icc a b)) := himg.cthickening
  have hSfst : ∀ q ∈ cthickening r (zInf '' Icc a b), q.1 ∈ cthickening r (c '' Icc a b) :=
    fun q hq => fst_mem_cthickening_image hq
  have hSU : cthickening r (zInf '' Icc a b) ⊆ U ×ˢ (univ : Set F) :=
    fun q hq => ⟨hrU (hSfst q hq), mem_univ _⟩
  have hvInf : ContDiffOn ℝ 1 vInf (U ×ˢ (univ : Set F)) :=
    contDiffOn_snd.prodMk (((hΓInf.comp contDiffOn_fst (fun q hq => hq.1)).clm_apply
      contDiffOn_snd).clm_apply contDiffOn_snd).neg
  obtain ⟨L, hL⟩ := hvInf.exists_lipschitzOnWith_of_isCompact (hU.prod isOpen_univ) hS hSU
  -- uniform convergence of the phase fields on the tube
  have hconvM : ∀ ε > 0, ∀ᶠ n in atTop, ∀ x ∈ cthickening r (c '' Icc a b),
      dist (ΓInf x) (Γ n x) < ε :=
    (Metric.tendstoUniformlyOn_iff (F := Γ) (f := ΓInf) (p := atTop)
      (s := cthickening r (c '' Icc a b))).mp (hconv _ hK₁ hrU)
  have h1 := (Metric.tendstoUniformlyOn_iff (F := fun i (q : F × F) => Γ i q.1)
    (f := fun q => ΓInf q.1) (p := atTop) (s := cthickening r (zInf '' Icc a b))).mpr
    fun ε hε => (hconvM ε hε).mono fun i hi q hq => hi q.1 (hSfst q hq)
  have h2 := (Metric.tendstoUniformlyOn_iff (F := fun (_ : ℕ) (q : F × F) => q.2)
    (f := fun q => q.2) (p := atTop) (s := cthickening r (zInf '' Icc a b))).mpr
    fun ε hε => Eventually.of_forall fun i q _ => by simpa using hε
  have hpair := tendstoUniformlyOn_prodMk h1 h2
  have hΓc : ContinuousOn ΓInf (cthickening r (c '' Icc a b)) :=
    (hΓInf.continuousOn).mono hrU
  have hcpt : IsCompact ((ΓInf '' cthickening r (c '' Icc a b)) ×ˢ
      (Prod.snd '' cthickening r (zInf '' Icc a b))) :=
    (hK₁.image_of_continuousOn hΓc).prod (hS.image continuous_snd)
  let Ψ : (F →L[ℝ] F →L[ℝ] F) × F → F × F := fun q => (q.2, -(q.1 q.2 q.2))
  have hΨ : Continuous Ψ :=
    continuous_snd.prodMk ((continuous_fst.clm_apply continuous_snd).clm_apply continuous_snd).neg
  have hvconv : TendstoUniformlyOn v vInf atTop (cthickening r (zInf '' Icc a b)) :=
    hpair.comp_continuousAt_of_isCompact (Ψ := Ψ) hcpt
      (fun q hq => Set.mk_mem_prod (mem_image_of_mem ΓInf (hSfst q hq)) (mem_image_of_mem _ hq))
      (fun y _ => hΨ.continuousAt)
  have hz_conv : TendstoUniformlyOn z zInf atTop (Icc a b) :=
    tendstoUniformlyOn_of_tendsto_of_lipschitzOnWith_limit (v := v) (vInf := vInf) (z := z)
      (zInf := zInf) hr
      (fun i t ht => HasDerivWithinAt.prodMk (hvel i t ht) (hacc i t ht))
      (fun t ht => HasDerivWithinAt.prodMk (hc t ht) (hc' t ht)) hL hvconv (h0.prodMk_nhds h0')
  exact ⟨uniformContinuous_fst.comp_tendstoUniformlyOn hz_conv,
    uniformContinuous_snd.comp_tendstoUniformlyOn hz_conv⟩

end DifferentialGeometry.Analysis.ODE.GeodesicLimits
