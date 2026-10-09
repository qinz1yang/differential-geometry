import DifferentialGeometry.Analysis.Calculus.Compactness.SmoothMap

/-!
# Finite-order Arzelà–Ascoli extraction for metric coefficients

Proof of the finite-order extraction stated (with `sorry`) in
`DifferentialGeometry/Analysis/Calculus/Compactness/FiniteOrder.lean` (blueprint LFR14, step 2).
This file does not import `FiniteOrder.lean`; the statement is reproduced verbatim as
`exists_bilinear_form_limit_subsequence_of_bounded_derivatives_proved`.

The argument is the finite-order version of `exists_cInf_subseq_on` (`SmoothMap.lean`): the
jets of order `r < K` are restricted to `U`, are equicontinuous by the bound on the jet of
order `r + 1 ≤ K`, and are pointwise bounded; Arzelà–Ascoli and Tychonoff give one subsequence
along which every jet of order `< K` converges locally uniformly on `U`, and the limit jets form
a Taylor series up to order `K - 1`.
-/

set_option autoImplicit false

noncomputable section
open Filter Topology

namespace DifferentialGeometry.CheegerGromovCompactness

section FiniteOrderMap

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Finite-order version of `exists_iteratedFDeriv_bound_of_eventually_bounded`: for maps of
class `C^K` on an open set, eventual bounds on the derivatives of order `≤ K` on compact subsets
are bounds for all indices. -/
theorem exists_iteratedFDeriv_bound_of_eventually_bounded_of_le
    {K : ℕ} {U : Set E} (hU : IsOpen U) {Φ : ℕ → E → F}
    (hΦ : ∀ k, ContDiffOn ℝ (K : WithTop ℕ∞) (Φ k) U)
    (hbdd : ∀ r : ℕ, r ≤ K → ∀ S : Set E, IsCompact S → S ⊆ U →
      ∃ M : ℝ, ∀ᶠ k in atTop, ∀ x ∈ S, ‖iteratedFDeriv ℝ r (Φ k) x‖ ≤ M) :
    ∀ r : ℕ, r ≤ K → ∀ S : Set E, IsCompact S → S ⊆ U →
      ∃ M : ℝ, ∀ k : ℕ, ∀ x ∈ S, ‖iteratedFDeriv ℝ r (Φ k) x‖ ≤ M := by
  classical
  intro r hr S hS hSU
  obtain ⟨M, hM⟩ := hbdd r hr S hS hSU
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hM
  have hfin : ∀ k : ℕ, ∃ Mₖ : ℝ, ∀ x ∈ S, ‖iteratedFDeriv ℝ r (Φ k) x‖ ≤ Mₖ := fun k => by
    obtain ⟨Mₖ, hMₖ⟩ := hS.exists_bound_of_continuousOn
      (((hΦ k).continuousOn_iteratedFDerivWithin (by exact_mod_cast hr)
        hU.uniqueDiffOn).mono hSU)
    exact ⟨Mₖ, fun x hx => by
      rw [← iteratedFDerivWithin_of_isOpen r hU (hSU hx)]
      exact hMₖ x hx⟩
  choose Mₖ hMₖ using hfin
  let T : Finset ℝ := (Finset.range (k₀ + 1)).image Mₖ
  have hTne : T.Nonempty :=
    ⟨Mₖ 0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.succ_pos k₀), rfl⟩⟩
  refine ⟨max M (T.max' hTne), fun k x hx => ?_⟩
  rcases lt_or_ge k (k₀ + 1) with hk | hk
  · have hm : Mₖ k ∈ T := Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩
    exact (hMₖ k x hx).trans
      ((Finset.le_max' T (Mₖ k) hm).trans (le_max_right M (T.max' hTne)))
  · exact (hk₀ k (Nat.le_of_succ_le hk) x hx).trans (le_max_left M (T.max' hTne))

omit [FiniteDimensional ℝ F] in
/-- The restrictions to `U` of the jets of order `r` of a family of `C^K` maps, `r + 1 ≤ K`,
are equicontinuous when the jets of order `r + 1` are bounded on compact subsets of `U`. -/
theorem equicontinuous_iteratedFDerivWithin_of_succ_le
    {K : ℕ} {U : Set E} (hU : IsOpen U) (Φ : ℕ → E → F)
    (hΦ : ∀ k, ContDiffOn ℝ (K : WithTop ℕ∞) (Φ k) U)
    {r : ℕ} (hr : r + 1 ≤ K)
    (hbdd : ∀ S : Set E, IsCompact S → S ⊆ U →
        ∃ M : ℝ, ∀ k : ℕ, ∀ x ∈ S, ‖iteratedFDerivWithin ℝ (r + 1) (Φ k) U x‖ ≤ M) :
    Equicontinuous
      (fun k => fun x : U => iteratedFDerivWithin ℝ r (Φ k) U (x : E)) := by
  intro x₀
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  obtain ⟨ρ, hρpos, hρU⟩ := Metric.isOpen_iff.mp hU (x₀ : E) x₀.2
  have hsub : Metric.closedBall (x₀ : E) (ρ / 2) ⊆ U := by
    intro y hy
    apply hρU
    rw [Metric.mem_ball]
    rw [Metric.mem_closedBall] at hy
    linarith
  obtain ⟨M, hM⟩ := hbdd (Metric.closedBall (x₀ : E) (ρ / 2)) (isCompact_closedBall _ _) hsub
  have hM₀ : (0 : ℝ) ≤ max M 0 := le_max_right M 0
  have hrK : ((r : ℕ) : WithTop ℕ∞) < (K : WithTop ℕ∞) := by
    exact_mod_cast Nat.lt_of_succ_le hr
  refine ⟨min (ρ / 2) (ε / (max M 0 + 1)),
    lt_min (by positivity) (by positivity), fun x hx k => ?_⟩
  rw [Subtype.dist_eq] at hx
  have hxsub : (x : E) ∈ Metric.closedBall (x₀ : E) (ρ / 2) :=
    Metric.mem_closedBall.mpr (le_of_lt (lt_of_lt_of_le hx (min_le_left _ _)))
  have hx₀sub : (x₀ : E) ∈ Metric.closedBall (x₀ : E) (ρ / 2) :=
    Metric.mem_closedBall_self (by positivity)
  have hlip :
      ‖iteratedFDerivWithin ℝ r (Φ k) U (x : E) -
          iteratedFDerivWithin ℝ r (Φ k) U (x₀ : E)‖
        ≤ max M 0 * ‖(x : E) - (x₀ : E)‖ := by
    refine Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f' := fun y => (iteratedFDerivWithin ℝ (r + 1) (Φ k) U y).curryLeft)
      (fun y hy => ?_) (fun y hy => ?_)
      (convex_closedBall _ _) hx₀sub hxsub
    · exact (((hΦ k).ftaylorSeriesWithin hU.uniqueDiffOn).fderivWithin r hrK y
        (hsub hy)).mono hsub
    · rw [ContinuousMultilinearMap.curryLeft_norm]
      exact (hM k y hy).trans (le_max_left M 0)
  rw [dist_eq_norm, norm_sub_rev]
  calc
    ‖iteratedFDerivWithin ℝ r (Φ k) U (x : E) -
          iteratedFDerivWithin ℝ r (Φ k) U (x₀ : E)‖
        ≤ max M 0 * ‖(x : E) - (x₀ : E)‖ := hlip
    _ ≤ max M 0 * (ε / (max M 0 + 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ hM₀
        rw [← dist_eq_norm]
        exact le_of_lt (lt_of_lt_of_le hx (min_le_right _ _))
    _ < (max M 0 + 1) * (ε / (max M 0 + 1)) :=
        mul_lt_mul_of_pos_right (lt_add_one _) (by positivity)
    _ = ε := by field_simp

/-- Finite-order Arzelà–Ascoli extraction on an open set: a sequence of `C^K` maps (`1 ≤ K`)
whose derivatives of order `≤ K` are bounded on every compact subset of `U` (uniformly in the
index) has a subsequence converging in `C^{K-1}` on every compact subset of `U` to a map of
class `C^{K-1}` on `U`. -/
theorem exists_cP_subseq_on_of_le
    (K : ℕ) (hK : 1 ≤ K) {U : Set E} (hU : IsOpen U) (Φ : ℕ → E → F)
    (hΦ : ∀ k, ContDiffOn ℝ (K : WithTop ℕ∞) (Φ k) U)
    (hbdd : ∀ r : ℕ, r ≤ K → ∀ S : Set E, IsCompact S → S ⊆ U →
        ∃ M : ℝ, ∀ k : ℕ, ∀ x ∈ S, ‖iteratedFDeriv ℝ r (Φ k) x‖ ≤ M) :
    ∃ (φ : ℕ → ℕ) (Φinf : E → F),
      StrictMono φ ∧ ContDiffOn ℝ ((K - 1 : ℕ) : WithTop ℕ∞) Φinf U ∧
        ∀ S : Set E, IsCompact S → S ⊆ U →
          MapCPConvergenceOn S (K - 1) (fun k => Φ (φ k)) Φinf := by
  classical
  have : LocallyCompactSpace U := hU.locallyCompactSpace
  have hbddW : ∀ r : ℕ, r ≤ K → ∀ S : Set E, IsCompact S → S ⊆ U →
      ∃ M : ℝ, ∀ k : ℕ, ∀ x ∈ S, ‖iteratedFDerivWithin ℝ r (Φ k) U x‖ ≤ M := by
    intro r hr S hS hSU
    obtain ⟨M, hM⟩ := hbdd r hr S hS hSU
    exact ⟨M, fun k x hx => by
      rw [iteratedFDerivWithin_of_isOpen r hU (hSU hx)]; exact hM k x hx⟩
  -- the jets of order `r < K`, restricted to `U`; the jets of order `≥ K` are replaced by `0`
  let jet : (r : ℕ) → ℕ → U → ContinuousMultilinearMap ℝ (fun _ : Fin r => E) F :=
    fun r k x => if r < K then iteratedFDerivWithin ℝ r (Φ k) U (x : E) else 0
  have hjet_cont : ∀ r k, Continuous (jet r k) := by
    intro r k
    by_cases hr : r < K
    · simp only [jet, ite_eq_left hr]
      exact ((hΦ k).continuousOn_iteratedFDerivWithin (by exact_mod_cast hr.le)
        hU.uniqueDiffOn).comp_continuous continuous_subtype_val (fun x => x.2)
    · simp only [jet, ite_eq_right hr]
      exact continuous_const
  let Fb : (r : ℕ) → ℕ → C(U, ContinuousMultilinearMap ℝ (fun _ : Fin r => E) F) :=
    fun r k => ⟨jet r k, hjet_cont r k⟩
  have hFb : ∀ (r k : ℕ) (x : U), r < K →
      Fb r k x = iteratedFDerivWithin ℝ r (Φ k) U (x : E) := by
    intro r k x hr
    change jet r k x = _
    simp only [jet, ite_eq_left hr]
  have hequi : ∀ r : ℕ,
      Equicontinuous (fun k => (Fb r k : U → ContinuousMultilinearMap ℝ (fun _ : Fin r => E) F)) := by
    intro r
    by_cases hr : r < K
    · have heq : (fun k => (Fb r k : U → ContinuousMultilinearMap ℝ (fun _ : Fin r => E) F)) =
          fun k => fun x : U => iteratedFDerivWithin ℝ r (Φ k) U (x : E) :=
        funext fun k => funext fun x => hFb r k x hr
      rw [heq]
      exact equicontinuous_iteratedFDerivWithin_of_succ_le hU Φ hΦ hr
        (fun S hS hSU => hbddW (r + 1) hr S hS hSU)
    · intro x₀
      rw [Metric.equicontinuousAt_iff]
      intro ε hε
      refine ⟨1, one_pos, fun x _ k => ?_⟩
      change dist (jet r k x₀) (jet r k x) < ε
      simp only [jet, ite_eq_right hr, dist_self]
      exact hε
  have hptw : ∀ (r : ℕ) (x : U), ∃ M : ℝ, ∀ k : ℕ, ‖Fb r k x‖ ≤ M := by
    intro r x
    by_cases hr : r < K
    · obtain ⟨M, hM⟩ := hbddW r hr.le {(x : E)} isCompact_singleton
        (Set.singleton_subset_iff.mpr x.2)
      exact ⟨M, fun k => by rw [hFb r k x hr]; exact hM k (x : E) rfl⟩
    · refine ⟨0, fun k => ?_⟩
      change ‖jet r k x‖ ≤ 0
      simp only [jet, ite_eq_right hr, norm_zero, le_refl]
  have hcpt : ∀ r : ℕ, IsCompact (closure (Set.range (Fb r))) := by
    intro r
    have := cmm_finiteDimensional (E := E) (F := F) r
    exact arzelaAscoli_isCompact_closure (Fb r) (hequi r) (hptw r)
  have : ∀ r : ℕ, CompactSpace (closure (Set.range (Fb r))) :=
    fun r => isCompact_iff_compactSpace.mp (hcpt r)
  set xseq : ℕ → Π r : ℕ, closure (Set.range (Fb r)) :=
    fun k r => ⟨Fb r k, subset_closure ⟨k, rfl⟩⟩ with hxseq
  obtain ⟨a, -, φ, hφ, ha⟩ :=
    (isCompact_univ :
        IsCompact (Set.univ : Set (Π r : ℕ, closure (Set.range (Fb r))))).tendsto_subseq
      (x := xseq) (fun k => Set.mem_univ _)
  set G : (r : ℕ) → C(U, ContinuousMultilinearMap ℝ (fun _ : Fin r => E) F) :=
    fun r => (a r : C(U, _)) with hG
  have hGconv : ∀ r : ℕ, Tendsto (fun k => Fb r (φ k)) atTop (𝓝 (G r)) := by
    intro r
    have h1 : Tendsto (fun k => xseq (φ k) r) atTop (𝓝 (a r)) := (tendsto_pi_nhds.mp ha) r
    have h2 := (continuous_subtype_val.tendsto (a r)).comp h1
    simpa [hxseq, hG, Function.comp] using! h2
  have hGuniform : ∀ r : ℕ, ∀ S : Set U, IsCompact S →
      TendstoUniformlyOn (fun k => ⇑(Fb r (φ k))) (⇑(G r)) atTop S :=
    fun r => ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp (hGconv r)
  let Gext : (r : ℕ) → E → ContinuousMultilinearMap ℝ (fun _ : Fin r => E) F :=
    fun r x => if h : x ∈ U then (G r) ⟨x, h⟩ else 0
  have hGext : ∀ (r : ℕ) (x : E) (hx : x ∈ U), Gext r x = (G r) ⟨x, hx⟩ :=
    fun r x hx => dite_eq_left hx
  let Φinf : E → F := fun x => (Gext 0 x).curry0
  have hGuniformE : ∀ r : ℕ, r < K → ∀ S : Set E, IsCompact S → S ⊆ U →
      TendstoUniformlyOn (fun k => iteratedFDerivWithin ℝ r (Φ (φ k)) U)
        (Gext r) atTop S := by
    intro r hr S hS hSU
    have hSsub : IsCompact (Subtype.val ⁻¹' S : Set U) := by
      rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, Set.inter_eq_right.mpr hSU]
      exact hS
    have hsub := hGuniform r (Subtype.val ⁻¹' S) hSsub
    rw [Metric.tendstoUniformlyOn_iff] at hsub ⊢
    intro ε hε
    filter_upwards [hsub ε hε] with k hk x hx
    have hxU : x ∈ U := hSU hx
    have hkx := hk ⟨x, hxU⟩ hx
    rwa [show (G r) ⟨x, hxU⟩ = Gext r x from (hGext r x hxU).symm, hFb r (φ k) ⟨x, hxU⟩ hr]
      at hkx
  have hGderiv : ∀ (r : ℕ), r + 1 < K → ∀ x₀ : E, x₀ ∈ U →
      HasFDerivAt (Gext r) ((Gext (r + 1) x₀).curryLeft) x₀ := by
    intro r hr x₀ hx₀
    obtain ⟨ρ, hρpos, hρU⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
    have hball2U : Metric.closedBall x₀ (ρ / 2) ⊆ U := fun y hy => by
      apply hρU; rw [Metric.mem_ball]; rw [Metric.mem_closedBall] at hy; linarith
    have hballU : Metric.ball x₀ (ρ / 2) ⊆ U :=
      fun y hy => hball2U (Metric.ball_subset_closedBall hy)
    have hrK : ((r : ℕ) : WithTop ℕ∞) < (K : WithTop ℕ∞) := by
      exact_mod_cast (Nat.lt_succ_self r).trans hr
    have hf' : TendstoUniformlyOn
        (fun k y => (iteratedFDerivWithin ℝ (r + 1) (Φ (φ k)) U y).curryLeft)
        (fun y => (Gext (r + 1) y).curryLeft) atTop (Metric.ball x₀ (ρ / 2)) := by
      have h2 := ((continuousMultilinearCurryLeftEquiv ℝ
          (fun _ : Fin (r + 1) => E) F).isometry.uniformContinuous).comp_tendstoUniformlyOn
        ((hGuniformE (r + 1) hr (Metric.closedBall x₀ (ρ / 2)) (isCompact_closedBall _ _)
            hball2U).mono Metric.ball_subset_closedBall)
      simpa [Function.comp_def] using! h2
    have hfd : ∀ k : ℕ, ∀ y ∈ Metric.ball x₀ (ρ / 2),
        HasFDerivAt (iteratedFDerivWithin ℝ r (Φ (φ k)) U)
          ((iteratedFDerivWithin ℝ (r + 1) (Φ (φ k)) U y).curryLeft) y := fun k y hy =>
      (((hΦ (φ k)).ftaylorSeriesWithin hU.uniqueDiffOn).fderivWithin r hrK y
        (hballU hy)).hasFDerivAt (hU.mem_nhds (hballU hy))
    have hfg : ∀ y ∈ Metric.ball x₀ (ρ / 2),
        Tendsto (fun k => iteratedFDerivWithin ℝ r (Φ (φ k)) U y) atTop (𝓝 (Gext r y)) :=
      fun y hy => (hGuniformE r ((Nat.lt_succ_self r).trans hr) {y} isCompact_singleton
        (Set.singleton_subset_iff.mpr (hballU hy))).tendsto_at rfl
    exact hasFDerivAt_of_tendstoUniformlyOn Metric.isOpen_ball hf' hfd hfg
      (Metric.mem_ball_self (by positivity))
  have hcontGext : ∀ m : ℕ, ContinuousOn (Gext m) U := by
    intro m
    rw [continuousOn_iff_continuous_domRestrict]
    have he : Set.domRestrict U (Gext m) = ⇑(G m) := by
      funext x
      exact hGext m (x : E) x.2
    rw [he]; exact (G m).continuous
  have htaylor : HasFTaylorSeriesUpToOn ((K - 1 : ℕ) : WithTop ℕ∞) Φinf
      (fun y r => Gext r y) U := by
    refine ⟨fun _ _ => rfl, fun m hm x hx => ?_, fun m _ => hcontGext m⟩
    have hm' : m < K - 1 := by exact_mod_cast hm
    exact (hGderiv m (by omega) x hx).hasFDerivWithinAt
  have hsmooth : ContDiffOn ℝ ((K - 1 : ℕ) : WithTop ℕ∞) Φinf U := htaylor.contDiffOn
  have hid : ∀ r : ℕ, r ≤ K - 1 → ∀ x ∈ U, iteratedFDerivWithin ℝ r Φinf U x = Gext r x :=
    fun r hr x hx =>
      (htaylor.eq_iteratedFDerivWithin_of_uniqueDiffOn (by exact_mod_cast hr)
        hU.uniqueDiffOn hx).symm
  refine ⟨φ, Φinf, hφ, hsmooth, ?_⟩
  intro S hS hSU ε hε
  have key : ∀ r : ℕ, r ≤ K - 1 → ∀ᶠ k in atTop, ∀ x ∈ S,
      mapDerivNorm r (Φ (φ k)) Φinf x ≤ ε := by
    intro r hr
    have huniform := hGuniformE r (by omega) S hS hSU
    rw [Metric.tendstoUniformlyOn_iff] at huniform
    filter_upwards [huniform ε hε] with k hk x hx
    have hxU : x ∈ U := hSU hx
    have e1 : iteratedFDeriv ℝ r (fun y => Φ (φ k) y - Φinf y) x
        = iteratedFDerivWithin ℝ r (fun y => Φ (φ k) y - Φinf y) U x :=
      (iteratedFDerivWithin_of_isOpen r hU hxU).symm
    have e2 : iteratedFDerivWithin ℝ r (fun y => Φ (φ k) y - Φinf y) U x
        = iteratedFDerivWithin ℝ r (Φ (φ k)) U x - iteratedFDerivWithin ℝ r Φinf U x :=
      iteratedFDerivWithin_sub_apply
        (((hΦ (φ k)).contDiffWithinAt hxU).of_le (by exact_mod_cast (by omega : r ≤ K)))
        ((hsmooth.contDiffWithinAt hxU).of_le (by exact_mod_cast hr))
        hU.uniqueDiffOn hxU
    rw [mapDerivNorm, e1, e2, hid r hr x hxU, ← dist_eq_norm, dist_comm]
    exact le_of_lt (hk x hx)
  have hfin : ∀ᶠ k in atTop, ∀ r ∈ Set.Iic (K - 1), ∀ x ∈ S,
      mapDerivNorm r (Φ (φ k)) Φinf x ≤ ε :=
    (Set.finite_Iic (K - 1)).eventually_all.2 (fun r hr => key r (Set.mem_Iic.mp hr))
  obtain ⟨k0, hk0⟩ := eventually_atTop.mp hfin
  exact ⟨k0, fun k hk r hr x hx => hk0 k hk r (Set.mem_Iic.mpr hr) x hx⟩

end FiniteOrderMap

section BilinearForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Finite-order extraction for symmetric, uniformly elliptic bilinear-form fields, without the
positivity hypothesis on the lower ellipticity constant (which the extraction does not use). -/
theorem exists_bilinear_form_limit_subsequence_of_bounded_derivatives_of_le
    (K : ℕ) (hK : 1 ≤ K) {U : Set E} (hU : IsOpen U)
    (g : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ)
    (hg : ∀ i, ContDiffOn ℝ (K : WithTop ℕ∞) (g i) U)
    (hjets : ∀ q : ℕ, q ≤ K → ∀ S : Set E, IsCompact S → S ⊆ U →
      ∃ C : ℝ, ∀ᶠ i in atTop, ∀ x ∈ S, ‖iteratedFDeriv ℝ q (g i) x‖ ≤ C)
    (lower upper : ℝ)
    (hsymm : ∀ i x, x ∈ U → ∀ v w, g i x v w = g i x w v)
    (helliptic : ∀ i x, x ∈ U → ∀ v,
      lower * ‖v‖ ^ 2 ≤ g i x v v ∧ g i x v v ≤ upper * ‖v‖ ^ 2) :
    ∃ (φ : ℕ → ℕ) (gLimit : E → E →L[ℝ] E →L[ℝ] ℝ),
      StrictMono φ ∧ ContDiffOn ℝ ((K - 1 : ℕ) : WithTop ℕ∞) gLimit U ∧
      (∀ S : Set E, IsCompact S → S ⊆ U →
        MapCPConvergenceOn S (K - 1) (fun i => g (φ i)) gLimit) ∧
      (∀ x ∈ U, ∀ v w, gLimit x v w = gLimit x w v) ∧
      (∀ x ∈ U, ∀ v,
        lower * ‖v‖ ^ 2 ≤ gLimit x v v ∧ gLimit x v v ≤ upper * ‖v‖ ^ 2) := by
  obtain ⟨φ, gLimit, hφ, hsmooth, hconv⟩ :=
    exists_cP_subseq_on_of_le K hK hU g hg
      (exists_iteratedFDeriv_bound_of_eventually_bounded_of_le hU hg hjets)
  have htend : ∀ x ∈ U, Tendsto (fun k => g (φ k) x) atTop (𝓝 (gLimit x)) := by
    intro x hx
    have h := tendstoUniformlyOn_of_cPConvergence
      ((hconv {x} isCompact_singleton (Set.singleton_subset_iff.mpr hx)).mono_order
        (Nat.zero_le _))
    exact h.tendsto_at rfl
  refine ⟨φ, gLimit, hφ, hsmooth, hconv, fun x hx v w => ?_, fun x hx v => ?_⟩
  · have hvw : Continuous (fun c : E →L[ℝ] E →L[ℝ] ℝ => c v w) := by fun_prop
    have hwv : Continuous (fun c : E →L[ℝ] E →L[ℝ] ℝ => c w v) := by fun_prop
    have h1 : Tendsto (fun k => g (φ k) x v w) atTop (𝓝 (gLimit x v w)) :=
      (hvw.tendsto (gLimit x)).comp (htend x hx)
    have h2 : Tendsto (fun k => g (φ k) x w v) atTop (𝓝 (gLimit x w v)) :=
      (hwv.tendsto (gLimit x)).comp (htend x hx)
    exact tendsto_nhds_unique h1
      (h2.congr fun k => (hsymm (φ k) x hx v w).symm)
  · have hvv : Continuous (fun c : E →L[ℝ] E →L[ℝ] ℝ => c v v) := by fun_prop
    have h : Tendsto (fun k => g (φ k) x v v) atTop (𝓝 (gLimit x v v)) :=
      (hvv.tendsto (gLimit x)).comp (htend x hx)
    exact ⟨ge_of_tendsto h (Eventually.of_forall fun k => (helliptic (φ k) x hx v).1),
      le_of_tendsto h (Eventually.of_forall fun k => (helliptic (φ k) x hx v).2)⟩

-- `hlower` is part of the mandated drop-in signature but is not needed by the proof; the
-- unused-variable syntax linter is silenced for this one declaration only.
set_option linter.unusedVariables false in
/-- **LFR14, step 2** (finite-order Arzelà–Ascoli for metric coefficients). Verbatim statement of
`exists_bilinear_form_limit_subsequence_of_bounded_derivatives` in `FiniteOrder.lean` (same
binders, names and order), so that its `sorry` can be replaced by
`exact exists_bilinear_form_limit_subsequence_of_bounded_derivatives_proved K hK hU g hg hjets
  lower upper hlower hsymm helliptic`.
The binders `[CompleteSpace E]` and `hlower` are kept only for this signature identity; the
content is `exists_bilinear_form_limit_subsequence_of_bounded_derivatives_of_le`, which needs
neither. -/
@[nolint unusedArguments]
theorem exists_bilinear_form_limit_subsequence_of_bounded_derivatives_proved
    [CompleteSpace E]
    (K : ℕ) (hK : 1 ≤ K) {U : Set E} (hU : IsOpen U)
    (g : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ)
    (hg : ∀ i, ContDiffOn ℝ (K : WithTop ℕ∞) (g i) U)
    (hjets : ∀ q : ℕ, q ≤ K → ∀ S : Set E, IsCompact S → S ⊆ U →
      ∃ C : ℝ, ∀ᶠ i in atTop, ∀ x ∈ S, ‖iteratedFDeriv ℝ q (g i) x‖ ≤ C)
    (lower upper : ℝ) (hlower : 0 < lower)
    (hsymm : ∀ i x, x ∈ U → ∀ v w, g i x v w = g i x w v)
    (helliptic : ∀ i x, x ∈ U → ∀ v,
      lower * ‖v‖ ^ 2 ≤ g i x v v ∧ g i x v v ≤ upper * ‖v‖ ^ 2) :
    ∃ (φ : ℕ → ℕ) (gLimit : E → E →L[ℝ] E →L[ℝ] ℝ),
      StrictMono φ ∧ ContDiffOn ℝ ((K - 1 : ℕ) : WithTop ℕ∞) gLimit U ∧
      (∀ S : Set E, IsCompact S → S ⊆ U →
        MapCPConvergenceOn S (K - 1) (fun i => g (φ i)) gLimit) ∧
      (∀ x ∈ U, ∀ v w, gLimit x v w = gLimit x w v) ∧
      (∀ x ∈ U, ∀ v,
        lower * ‖v‖ ^ 2 ≤ gLimit x v v ∧ gLimit x v v ≤ upper * ‖v‖ ^ 2) :=
  exists_bilinear_form_limit_subsequence_of_bounded_derivatives_of_le K hK hU g hg hjets
    lower upper hsymm helliptic

end BilinearForm

end DifferentialGeometry.CheegerGromovCompactness
