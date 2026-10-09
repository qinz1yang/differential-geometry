import DifferentialGeometry.Analysis.Calculus.Compactness.SmoothMap

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Topology

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
private theorem equicontOn_finite_iteratedFDerivWithin
    {U : Set E} (hU : IsOpen U) (p : ℕ) (Φ : ℕ → E → F)
    (hΦ : ∀ k, ContDiffOn ℝ ((p + 1 : ℕ) : WithTop ℕ∞) (Φ k) U)
    (hbdd : ∀ r : ℕ, r ≤ p + 1 → ∀ K : Set E, IsCompact K → K ⊆ U →
        ∃ M : ℝ, ∀ k : ℕ, ∀ x ∈ K, ‖iteratedFDerivWithin ℝ r (Φ k) U x‖ ≤ M)
    (r : ℕ) (hr : r ≤ p) :
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
  obtain ⟨M, hM⟩ :=
    hbdd (r + 1) (Nat.add_le_add_right hr 1) (Metric.closedBall (x₀ : E) (ρ / 2))
      (isCompact_closedBall _ _) hsub
  have hM₀ : (0 : ℝ) ≤ max M 0 := le_max_right M 0
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
    · exact (((hΦ k).ftaylorSeriesWithin hU.uniqueDiffOn).fderivWithin r
        (by exact_mod_cast Nat.lt_succ_of_le hr) y (hsub hy)).mono hsub
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

theorem exists_finite_order_subseq_on
    {U : Set E} (hU : IsOpen U) (p : ℕ) (Φ : ℕ → E → F)
    (hΦ : ∀ k, ContDiffOn ℝ ((p + 1 : ℕ) : WithTop ℕ∞) (Φ k) U)
    (hbdd : ∀ r : ℕ, r ≤ p + 1 → ∀ K : Set E, IsCompact K → K ⊆ U →
        ∃ M : ℝ, ∀ k : ℕ, ∀ x ∈ K, ‖iteratedFDeriv ℝ r (Φ k) x‖ ≤ M) :
    ∃ (φ : ℕ → ℕ) (Φinf : E → F),
      StrictMono φ ∧ ContDiffOn ℝ (p : WithTop ℕ∞) Φinf U ∧
        ∀ K : Set E, IsCompact K → K ⊆ U →
          MapCPConvergenceOn K p (fun k => Φ (φ k)) Φinf := by
  classical
  have : LocallyCompactSpace U := hU.locallyCompactSpace
  have hbddW : ∀ r : ℕ, r ≤ p + 1 → ∀ K : Set E, IsCompact K → K ⊆ U →
      ∃ M : ℝ, ∀ k : ℕ, ∀ x ∈ K, ‖iteratedFDerivWithin ℝ r (Φ k) U x‖ ≤ M := by
    intro r hr K hK hKU
    obtain ⟨M, hM⟩ := hbdd r hr K hK hKU
    exact ⟨M, fun k x hx => by
      rw [iteratedFDerivWithin_of_isOpen r hU (hKU hx)]; exact hM k x hx⟩
  let Fb : (r : ℕ) → ℕ → C(U, ContinuousMultilinearMap ℝ (fun _ : Fin r => E) F) :=
    fun r k => if hr : r ≤ p then
      ⟨fun x => iteratedFDerivWithin ℝ r (Φ k) U (x : E),
        ((hΦ k).continuousOn_iteratedFDerivWithin
          (by exact_mod_cast hr.trans (Nat.le_succ p)) hU.uniqueDiffOn).comp_continuous
            continuous_subtype_val (fun x => x.2)⟩ else 0
  have hFb : ∀ r, r ≤ p → ∀ k, ∀ x : U,
      Fb r k x = iteratedFDerivWithin ℝ r (Φ k) U (x : E) := by
    intro r hr k x
    simp only [Fb, dite_eq_left hr, ContinuousMap.coe_mk]
  have hcpt : ∀ r : ℕ, IsCompact (closure (Set.range (Fb r))) := by
    intro r
    by_cases hr : r ≤ p
    · have := cmm_finiteDimensional (E := E) (F := F) r
      refine arzelaAscoli_isCompact_closure (Fb r) ?_ (fun x => ?_)
      · simpa only [Fb, dite_eq_left hr] using!
          equicontOn_finite_iteratedFDerivWithin hU p Φ hΦ hbddW r hr
      · obtain ⟨M, hM⟩ := hbddW r (hr.trans (Nat.le_succ p)) {(x : E)}
          isCompact_singleton (Set.singleton_subset_iff.mpr x.2)
        exact ⟨M, fun k => by rw [hFb r hr]; exact hM k (x : E) rfl⟩
    · simpa only [Fb, dite_eq_right hr, Set.range_const, closure_singleton] using
        (isCompact_singleton : IsCompact ({0} : Set C(U, _)))
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
  have hGuniform : ∀ r : ℕ, ∀ K : Set U, IsCompact K →
      TendstoUniformlyOn (fun k => ⇑(Fb r (φ k))) (⇑(G r)) atTop K :=
    fun r => ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp (hGconv r)
  let Gext : (r : ℕ) → E → ContinuousMultilinearMap ℝ (fun _ : Fin r => E) F :=
    fun r x => if h : x ∈ U then (G r) ⟨x, h⟩ else 0
  have hGext : ∀ (r : ℕ) (x : E) (hx : x ∈ U), Gext r x = (G r) ⟨x, hx⟩ :=
    fun r x hx => dite_eq_left hx
  let Φinf : E → F := fun x => (Gext 0 x).curry0
  have hGuniformE : ∀ r : ℕ, r ≤ p → ∀ K : Set E, IsCompact K → K ⊆ U →
      TendstoUniformlyOn (fun k => iteratedFDerivWithin ℝ r (Φ (φ k)) U)
        (Gext r) atTop K := by
    intro r hr K hK hKU
    have hKsub : IsCompact (Subtype.val ⁻¹' K : Set U) := by
      rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, Set.inter_eq_right.mpr hKU]
      exact hK
    have hsub := hGuniform r (Subtype.val ⁻¹' K) hKsub
    rw [Metric.tendstoUniformlyOn_iff] at hsub ⊢
    intro ε hε
    filter_upwards [hsub ε hε] with k hk x hx
    have hxU : x ∈ U := hKU hx
    have hkx := hk ⟨x, hxU⟩ hx
    rw [hFb r hr] at hkx
    rwa [show (G r) ⟨x, hxU⟩ = Gext r x from (hGext r x hxU).symm] at hkx
  have hGderiv : ∀ (r : ℕ), r < p → ∀ (x₀ : E), x₀ ∈ U →
      HasFDerivAt (Gext r) ((Gext (r + 1) x₀).curryLeft) x₀ := by
    intro r hr x₀ hx₀
    obtain ⟨ρ, hρpos, hρU⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
    have hball2U : Metric.closedBall x₀ (ρ / 2) ⊆ U := fun y hy => by
      apply hρU; rw [Metric.mem_ball]; rw [Metric.mem_closedBall] at hy; linarith
    have hballU : Metric.ball x₀ (ρ / 2) ⊆ U :=
      fun y hy => hball2U (Metric.ball_subset_closedBall hy)
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
      (((hΦ (φ k)).ftaylorSeriesWithin hU.uniqueDiffOn).fderivWithin r
        (by exact_mod_cast hr.trans (Nat.lt_succ_self p)) y (hballU hy)).hasFDerivAt
          (hU.mem_nhds (hballU hy))
    have hfg : ∀ y ∈ Metric.ball x₀ (ρ / 2),
        Tendsto (fun k => iteratedFDerivWithin ℝ r (Φ (φ k)) U y) atTop (𝓝 (Gext r y)) :=
      fun y hy => (hGuniformE r hr.le {y} isCompact_singleton
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
  have htaylor : HasFTaylorSeriesUpToOn (p : WithTop ℕ∞) Φinf (fun y r => Gext r y) U :=
    ⟨fun _ _ => rfl, fun m hm x hx => (hGderiv m (by exact_mod_cast hm) x hx).hasFDerivWithinAt,
      fun m _ => hcontGext m⟩
  have hsmooth : ContDiffOn ℝ (p : WithTop ℕ∞) Φinf U := htaylor.contDiffOn
  have hid : ∀ (r : ℕ), r ≤ p → ∀ x ∈ U, iteratedFDerivWithin ℝ r Φinf U x = Gext r x :=
    fun r hr x hx =>
      (htaylor.eq_iteratedFDerivWithin_of_uniqueDiffOn (by exact_mod_cast hr)
        hU.uniqueDiffOn hx).symm
  refine ⟨φ, Φinf, hφ, hsmooth, ?_⟩
  intro K hK hKU ε hε
  have key : ∀ r : ℕ, r ≤ p → ∀ᶠ k in atTop, ∀ x ∈ K,
      mapDerivNorm r (Φ (φ k)) Φinf x ≤ ε := by
    intro r hr
    have huniform := hGuniformE r hr K hK hKU
    rw [Metric.tendstoUniformlyOn_iff] at huniform
    filter_upwards [huniform ε hε] with k hk x hx
    have hxU : x ∈ U := hKU hx
    have e1 : iteratedFDeriv ℝ r (fun y => Φ (φ k) y - Φinf y) x
        = iteratedFDerivWithin ℝ r (fun y => Φ (φ k) y - Φinf y) U x :=
      (iteratedFDerivWithin_of_isOpen r hU hxU).symm
    have e2 : iteratedFDerivWithin ℝ r (fun y => Φ (φ k) y - Φinf y) U x
        = iteratedFDerivWithin ℝ r (Φ (φ k)) U x - iteratedFDerivWithin ℝ r Φinf U x :=
      iteratedFDerivWithin_sub_apply
        (((hΦ (φ k)).contDiffWithinAt hxU).of_le
          (by exact_mod_cast hr.trans (Nat.le_succ p)))
        ((hsmooth.contDiffWithinAt hxU).of_le (by exact_mod_cast hr))
        hU.uniqueDiffOn hxU
    rw [mapDerivNorm, e1, e2, hid r hr x hxU, ← dist_eq_norm, dist_comm]
    exact le_of_lt (hk x hx)
  have hfin : ∀ᶠ k in atTop, ∀ r ∈ Set.Iic p, ∀ x ∈ K,
      mapDerivNorm r (Φ (φ k)) Φinf x ≤ ε :=
    (Set.finite_Iic p).eventually_all.2 (fun r hr => key r (Set.mem_Iic.mp hr))
  obtain ⟨k0, hk0⟩ := eventually_atTop.mp hfin
  exact ⟨k0, fun k hk r hr x hx => hk0 k hk r (Set.mem_Iic.mpr hr) x hx⟩


omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem finite_order_bound_of_eventually_bounded
    {U : Set E} (hU : IsOpen U) (p : ℕ) (Φ : ℕ → E → F)
    (hΦ : ∀ k, ContDiffOn ℝ (p : WithTop ℕ∞) (Φ k) U)
    (r : ℕ) (hr : r ≤ p) {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U)
    (hbdd : ∃ M : ℝ, ∀ᶠ k in atTop, ∀ x ∈ K, ‖iteratedFDeriv ℝ r (Φ k) x‖ ≤ M) :
    ∃ M : ℝ, ∀ k : ℕ, ∀ x ∈ K, ‖iteratedFDeriv ℝ r (Φ k) x‖ ≤ M := by
  classical
  obtain ⟨M, hM⟩ := hbdd
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hM
  have hfin : ∀ k : ℕ, ∃ Mₖ : ℝ,
      ∀ x ∈ K, ‖iteratedFDeriv ℝ r (Φ k) x‖ ≤ Mₖ := fun k => by
    obtain ⟨Mₖ, hMₖ⟩ := hK.exists_bound_of_continuousOn
      (((hΦ k).continuousOn_iteratedFDerivWithin (by exact_mod_cast hr)
        hU.uniqueDiffOn).mono hKU)
    exact ⟨Mₖ, fun x hx => by
      rw [← iteratedFDerivWithin_of_isOpen r hU (hKU hx)]
      exact hMₖ x hx⟩
  choose Mₖ hMₖ using hfin
  let S : Finset ℝ := (Finset.range (k₀ + 1)).image Mₖ
  have hSne : S.Nonempty :=
    ⟨Mₖ 0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.succ_pos k₀), rfl⟩⟩
  refine ⟨max M (S.max' hSne), fun k x hx => ?_⟩
  rcases lt_or_ge k (k₀ + 1) with hk | hk
  · have hm : Mₖ k ∈ S := Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩
    exact (hMₖ k x hx).trans
      ((Finset.le_max' S (Mₖ k) hm).trans (le_max_right M (S.max' hSne)))
  · exact (hk₀ k (Nat.le_of_succ_le hk) x hx).trans (le_max_left M (S.max' hSne))

theorem exists_finite_order_subseq_on_of_eventually_bounded
    {U : Set E} (hU : IsOpen U) (p : ℕ) (Φ : ℕ → E → F)
    (hΦ : ∀ k, ContDiffOn ℝ ((p + 1 : ℕ) : WithTop ℕ∞) (Φ k) U)
    (hbdd : ∀ r : ℕ, r ≤ p + 1 → ∀ K : Set E, IsCompact K → K ⊆ U →
      ∃ M : ℝ, ∀ᶠ k in atTop, ∀ x ∈ K, ‖iteratedFDeriv ℝ r (Φ k) x‖ ≤ M) :
    ∃ (φ : ℕ → ℕ) (Φinf : E → F),
      StrictMono φ ∧ ContDiffOn ℝ (p : WithTop ℕ∞) Φinf U ∧
        ∀ K : Set E, IsCompact K → K ⊆ U →
          MapCPConvergenceOn K p (fun k => Φ (φ k)) Φinf :=
  exists_finite_order_subseq_on hU p Φ hΦ fun r hr K hK hKU =>
    finite_order_bound_of_eventually_bounded hU (p + 1) Φ hΦ r hr hK hKU (hbdd r hr K hK hKU)

theorem exists_finite_order_bilinear_form_limit_subsequence
    {U : Set E} (hU : IsOpen U) (p : ℕ)
    (g : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ)
    (hg : ∀ i, ContDiffOn ℝ ((p + 1 : ℕ) : WithTop ℕ∞) (g i) U)
    (hjets : ∀ q : ℕ, q ≤ p + 1 → ∀ S : Set E, IsCompact S → S ⊆ U →
      ∃ C : ℝ, ∀ᶠ i in atTop, ∀ x ∈ S, ‖iteratedFDeriv ℝ q (g i) x‖ ≤ C)
    (lower upper : ℝ)
    (hsymm : ∀ i x, x ∈ U → ∀ v w, g i x v w = g i x w v)
    (helliptic : ∀ i x, x ∈ U → ∀ v,
      lower * ‖v‖ ^ 2 ≤ g i x v v ∧ g i x v v ≤ upper * ‖v‖ ^ 2) :
    ∃ (φ : ℕ → ℕ) (gLimit : E → E →L[ℝ] E →L[ℝ] ℝ),
      StrictMono φ ∧ ContDiffOn ℝ (p : WithTop ℕ∞) gLimit U ∧
      (∀ S : Set E, IsCompact S → S ⊆ U →
        MapCPConvergenceOn S p (fun i => g (φ i)) gLimit) ∧
      (∀ x ∈ U, ∀ v w, gLimit x v w = gLimit x w v) ∧
      (∀ x ∈ U, ∀ v,
        lower * ‖v‖ ^ 2 ≤ gLimit x v v ∧ gLimit x v v ≤ upper * ‖v‖ ^ 2) := by
  obtain ⟨φ, gLimit, hφ, hregular, hconv⟩ :=
    exists_finite_order_subseq_on_of_eventually_bounded hU p g hg hjets
  have htend : ∀ x ∈ U, Tendsto (fun i => g (φ i) x) atTop (𝓝 (gLimit x)) := by
    intro x hx
    exact (tendstoUniformlyOn_of_cPConvergence
      ((hconv {x} isCompact_singleton (Set.singleton_subset_iff.mpr hx)).mono_order
        (Nat.zero_le p))).tendsto_at rfl
  have heval : ∀ x ∈ U, ∀ v w,
      Tendsto (fun i => g (φ i) x v w) atTop (𝓝 (gLimit x v w)) := by
    intro x hx v w
    have hcontinuous : Continuous (fun c : E →L[ℝ] E →L[ℝ] ℝ => c v w) := by fun_prop
    exact (hcontinuous.tendsto _).comp (htend x hx)
  refine ⟨φ, gLimit, hφ, hregular, hconv, ?_, ?_⟩
  · intro x hx v w
    exact tendsto_nhds_unique (heval x hx v w)
      ((heval x hx w v).congr' (Eventually.of_forall fun i => (hsymm (φ i) x hx v w).symm))
  · intro x hx v
    exact ⟨ge_of_tendsto (heval x hx v v)
      (Eventually.of_forall fun i => (helliptic (φ i) x hx v).1),
      le_of_tendsto (heval x hx v v)
        (Eventually.of_forall fun i => (helliptic (φ i) x hx v).2)⟩

end DifferentialGeometry.CheegerGromovCompactness
