import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.GlobalClosedManifold

/-!
# Full-interval flow of a globally smooth field on a closed manifold

The short-horizon flow engine `global_flow_jointContMDiffOn_on_closed_manifold` produces, anchored
at any time `t₀`, a jointly-`C∞` bare-velocity flow on a small window `Ioo (t₀ - T) (t₀ + T)`.
This file chains those windows into a single flow valid on *any* prescribed interval, by gluing a
freshly anchored window onto a running flow along the integral-curve uniqueness
`bare_integral_flow_eqOn_of_jointC1`.

The headline `global_flow_full_interval_on_closed_manifold` produces, for a globally jointly-`C∞`
field `X`, a flow `Φ : ℝ → M → M` with `Φ 0 = id`, jointly `C∞` on an open interval containing
`[0, T]`, and carrying the bare velocity `X t (Φ t x)` there.
-/

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle
open scoped Manifold Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [CompleteSpace E] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M]

omit [CompactSpace M] [I.Boundaryless] in
/-- **One chaining step.** Suppose `Φ` is a flow valid on `Ioo lo hi`: it fixes the basepoint at
time `0`, is jointly `C∞` on `Ioo lo hi ×ˢ univ`, and carries the bare velocity of `X`.  Suppose
further that, anchored at some interior time `t₁ ∈ Ioo lo hi`, a window flow `Ψ : M → ℝ → M` of `X`
fixes its anchor (`Ψ p t₁ = p`), is jointly `C∞` on `Ioo (t₁ - r) (t₁ + r) ×ˢ univ`, and carries
the bare velocity there.  Then the glued flow

  `Φ' s x := if s < t₁ then Φ s x else Ψ (Φ t₁ x) s`

is valid on the longer interval `Ioo lo (t₁ + r)`, and agrees with `Φ` on `Ioo lo hi`.

The agreement on the overlap `Ioo (t₁ - r) hi` is integral-curve uniqueness
(`bare_integral_flow_eqOn_of_jointC1`): both `s ↦ Φ s x` and `s ↦ Ψ (Φ t₁ x) s` are bare integral
curves of `X` through the common point `Φ t₁ x` at time `t₁`.  Joint smoothness of the second piece
is `Ψ`'s smoothness pre-composed with the smooth map `(s, x) ↦ (s, Φ t₁ x)`; across the seam the
two pieces agree on a neighbourhood, so the glued map is locally one smooth piece. -/
theorem flowValid_chain_step
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hXC1 : AutonomizedFieldJointC1 (I := I) X)
    (Φ : ℝ → M → M) {lo hi : ℝ}
    (hΦ0 : ∀ x : M, Φ 0 x = x)
    (hΦsm : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2)
      (Set.Ioo lo hi ×ˢ (Set.univ : Set M)))
    (hΦbare : ∀ t ∈ Set.Ioo lo hi, ∀ x : M,
      HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x))))
    {t₁ r : ℝ} (ht₁ : t₁ ∈ Set.Ioo lo hi) (h0t₁ : 0 < t₁) (hr : 0 < r)
    (hext : hi ≤ t₁ + r)
    (Ψ : M → ℝ → M)
    (hΨ0 : ∀ p : M, Ψ p t₁ = p)
    (hΨsm : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Ψ q.2 q.1)
      (Set.Ioo (t₁ - r) (t₁ + r) ×ˢ (Set.univ : Set M)))
    (hΨbare : ∀ p : M, ∀ t ∈ Set.Ioo (t₁ - r) (t₁ + r),
      HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Ψ p s) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Ψ p t)))) :
    ∃ Φ' : ℝ → M → M,
      (∀ x : M, Φ' 0 x = x) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ' q.1 q.2)
        (Set.Ioo lo (t₁ + r) ×ˢ (Set.univ : Set M)) ∧
      (∀ t ∈ Set.Ioo lo (t₁ + r), ∀ x : M,
        HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ' s x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ' t x)))) ∧
      (∀ s ∈ Set.Ioo lo hi, ∀ x : M, Φ' s x = Φ s x) := by
  classical
  set Φ' : ℝ → M → M := fun s x => if s < t₁ then Φ s x else Ψ (Φ t₁ x) s with hΦ'_def
  have hlo_t₁ : lo < t₁ := ht₁.1
  have ht₁_hi : t₁ < hi := ht₁.2
  set a₀ : ℝ := max lo (t₁ - r) with ha₀
  have ha₀_lt_t₁ : a₀ < t₁ := max_lt hlo_t₁ (by linarith)
  have ha₀_ge_lo : lo ≤ a₀ := le_max_left _ _
  have ha₀_ge : t₁ - r ≤ a₀ := le_max_right _ _
  -- The reverse window flow `s ↦ Ψ (Φ t₁ x) s` carries the bare velocity of `X`.
  have hΨcurve_bare : ∀ x : M, ∀ t ∈ Set.Ioo (t₁ - r) (t₁ + r),
      HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Ψ (Φ t₁ x) s) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Ψ (Φ t₁ x) t))) :=
    fun x t ht => hΨbare (Φ t₁ x) t ht
  -- Overlap: on `Ioo a₀ hi`, the running flow `Φ` and the reverse window agree.
  have hoverlap : ∀ x : M, ∀ s ∈ Set.Ioo a₀ hi, Φ s x = Ψ (Φ t₁ x) s := by
    intro x
    have ht₁_a₀hi : t₁ ∈ Set.Ioo a₀ hi := ⟨ha₀_lt_t₁, ht₁_hi⟩
    have hΦbare' : ∀ t ∈ Set.Ioo a₀ hi,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x) (Set.Ioo a₀ hi) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x))) := by
      intro t ht
      have htmem : t ∈ Set.Ioo lo hi :=
        ⟨lt_of_le_of_lt ha₀_ge_lo ht.1, ht.2⟩
      exact (hΦbare t htmem x).hasMFDerivWithinAt
    have hΨbare' : ∀ t ∈ Set.Ioo a₀ hi,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Ψ (Φ t₁ x) s) (Set.Ioo a₀ hi) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Ψ (Φ t₁ x) t))) := by
      intro t ht
      have htmem : t ∈ Set.Ioo (t₁ - r) (t₁ + r) :=
        ⟨lt_of_le_of_lt ha₀_ge ht.1, lt_of_lt_of_le ht.2 hext⟩
      exact (hΨcurve_bare x t htmem).hasMFDerivWithinAt
    have hstart : Φ t₁ x = Ψ (Φ t₁ x) t₁ := (hΨ0 (Φ t₁ x)).symm
    exact bare_integral_flow_eqOn_of_jointC1 (a := a₀) (b := hi) (t₀ := t₁)
      X hXC1 (fun s _ => Φ s x) (fun s _ => Ψ (Φ t₁ x) s) x x ht₁_a₀hi
      hΦbare' hΨbare' hstart
  -- On the window `Ioo a₀ (t₁ + r) ×ˢ univ`, the glued flow equals the smooth reverse window.
  have hΦ'_eq_Ψ : ∀ s ∈ Set.Ioo a₀ (t₁ + r), ∀ x : M, Φ' s x = Ψ (Φ t₁ x) s := by
    intro s hs x
    by_cases hlt : s < t₁
    · simp only [hΦ'_def, if_pos hlt]
      exact hoverlap x s ⟨hs.1, lt_trans hlt ht₁_hi⟩
    · simp only [hΦ'_def, if_neg hlt]
  -- On `Ioo lo t₁`, the glued flow equals the running flow.
  have hΦ'_eq_Φ_left : ∀ s ∈ Set.Ioo lo t₁, ∀ x : M, Φ' s x = Φ s x := by
    intro s hs x
    simp only [hΦ'_def, if_pos hs.2]
  have hΨsm' : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Ψ (Φ t₁ q.2) q.1)
      (Set.Ioo (t₁ - r) (t₁ + r) ×ˢ (Set.univ : Set M)) := by
    have hΦt₁ : ContMDiff I I ∞ (fun x : M => Φ t₁ x) := by
      intro x
      have hmem : ((t₁, x) : ℝ × M) ∈ Set.Ioo lo hi ×ˢ (Set.univ : Set M) :=
        ⟨ht₁, Set.mem_univ _⟩
      have hxsm : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2)
          (Set.Ioo lo hi ×ˢ (Set.univ : Set M)) (t₁, x) := hΦsm _ hmem
      have hpair : ContMDiffAt I (𝓘(ℝ, ℝ).prod I) ∞ (fun y : M => ((t₁, y) : ℝ × M)) x :=
        (contMDiffAt_const).prodMk contMDiffAt_id
      have hmaps : Set.MapsTo (fun y : M => ((t₁, y) : ℝ × M)) (Set.univ : Set M)
          (Set.Ioo lo hi ×ˢ (Set.univ : Set M)) := fun y _ => ⟨ht₁, Set.mem_univ _⟩
      have := (hxsm.comp x hpair.contMDiffWithinAt hmaps)
      simpa using this.contMDiffAt (by
        exact Filter.univ_mem)
    have hg : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
        (fun q : ℝ × M => ((q.1, Φ t₁ q.2) : ℝ × M)) :=
      contMDiff_fst.prodMk (hΦt₁.comp contMDiff_snd)
    have hcomp := hΨsm.comp (hg.contMDiffOn (s := Set.Ioo (t₁ - r) (t₁ + r) ×ˢ (Set.univ : Set M)))
      (fun q hq => by exact ⟨hq.1, Set.mem_univ _⟩)
    refine hcomp.congr ?_
    intro q hq
    rfl
  refine ⟨Φ', ?_, ?_, ?_, ?_⟩
  · intro x
    have h0 : (0 : ℝ) < t₁ := h0t₁
    simp only [hΦ'_def, if_pos h0]
    exact hΦ0 x
  · -- Joint smoothness on `Ioo lo (t₁ + r) ×ˢ univ`.
    intro q hq
    obtain ⟨hq1, _⟩ := hq
    by_cases hlt : q.1 < t₁
    · -- near a left point, `Φ' = Φ`
      have hWopen : IsOpen (Set.Ioo lo t₁ ×ˢ (Set.univ : Set M)) := isOpen_Ioo.prod isOpen_univ
      have hqW : q ∈ Set.Ioo lo t₁ ×ˢ (Set.univ : Set M) := ⟨⟨hq1.1, hlt⟩, Set.mem_univ _⟩
      have hΦW : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2)
          (Set.Ioo lo t₁ ×ˢ (Set.univ : Set M)) q :=
        (hΦsm.mono (Set.prod_mono (Set.Ioo_subset_Ioo_right (le_of_lt ht₁_hi)) (subset_refl _))) q hqW
      have hcongr : ∀ q' ∈ Set.Ioo lo t₁ ×ˢ (Set.univ : Set M),
          (fun q : ℝ × M => Φ' q.1 q.2) q' = (fun q : ℝ × M => Φ q.1 q.2) q' := by
        rintro ⟨s, x⟩ ⟨hs, _⟩
        exact hΦ'_eq_Φ_left s hs x
      have hWnhds : Set.Ioo lo t₁ ×ˢ (Set.univ : Set M) ∈
          𝓝[Set.Ioo lo (t₁ + r) ×ˢ (Set.univ : Set M)] q :=
        mem_nhdsWithin_of_mem_nhds (hWopen.mem_nhds hqW)
      have hΦ'W : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ' q.1 q.2)
          (Set.Ioo lo t₁ ×ˢ (Set.univ : Set M)) q := by
        refine hΦW.congr_of_eventuallyEq ?_ (hcongr q hqW)
        filter_upwards [self_mem_nhdsWithin] with q' hq' using hcongr q' hq'
      exact hΦ'W.mono_of_mem_nhdsWithin hWnhds
    · -- near a right point (`q.1 ≥ t₁`), `Φ' = Ψ(Φt₁·)`
      have hq1_a₀ : a₀ < q.1 := lt_of_lt_of_le ha₀_lt_t₁ (not_lt.mp hlt)
      have hWopen : IsOpen (Set.Ioo a₀ (t₁ + r) ×ˢ (Set.univ : Set M)) :=
        isOpen_Ioo.prod isOpen_univ
      have hqW : q ∈ Set.Ioo a₀ (t₁ + r) ×ˢ (Set.univ : Set M) :=
        ⟨⟨hq1_a₀, hq1.2⟩, Set.mem_univ _⟩
      have hsubΨ : Set.Ioo a₀ (t₁ + r) ×ˢ (Set.univ : Set M) ⊆
          Set.Ioo (t₁ - r) (t₁ + r) ×ˢ (Set.univ : Set M) :=
        Set.prod_mono (Set.Ioo_subset_Ioo_left ha₀_ge) (subset_refl _)
      have hΨW : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Ψ (Φ t₁ q.2) q.1)
          (Set.Ioo a₀ (t₁ + r) ×ˢ (Set.univ : Set M)) q :=
        (hΨsm'.mono hsubΨ) q hqW
      have hcongr : ∀ q' ∈ Set.Ioo a₀ (t₁ + r) ×ˢ (Set.univ : Set M),
          (fun q : ℝ × M => Φ' q.1 q.2) q' = (fun q : ℝ × M => Ψ (Φ t₁ q.2) q.1) q' := by
        rintro ⟨s, x⟩ ⟨hs, _⟩
        exact hΦ'_eq_Ψ s hs x
      have hWnhds : Set.Ioo a₀ (t₁ + r) ×ˢ (Set.univ : Set M) ∈
          𝓝[Set.Ioo lo (t₁ + r) ×ˢ (Set.univ : Set M)] q :=
        mem_nhdsWithin_of_mem_nhds (hWopen.mem_nhds hqW)
      have hΦ'W : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ' q.1 q.2)
          (Set.Ioo a₀ (t₁ + r) ×ˢ (Set.univ : Set M)) q := by
        refine hΨW.congr_of_eventuallyEq ?_ (hcongr q hqW)
        filter_upwards [self_mem_nhdsWithin] with q' hq' using hcongr q' hq'
      exact hΦ'W.mono_of_mem_nhdsWithin hWnhds
  · -- Bare velocity on `Ioo lo (t₁ + r)`.
    intro t ht x
    by_cases hlt : t < t₁
    · have hev : (fun s : ℝ => Φ' s x) =ᶠ[𝓝 t] (fun s : ℝ => Φ s x) := by
        have hmem : Set.Iio t₁ ∈ 𝓝 t := isOpen_Iio.mem_nhds hlt
        filter_upwards [hmem] with s hs
        simp only [hΦ'_def, if_pos (Set.mem_Iio.mp hs)]
      have hΦ't : Φ' t x = Φ t x := by simp only [hΦ'_def, if_pos hlt]
      have htmem : t ∈ Set.Ioo lo hi := ⟨ht.1, lt_trans hlt ht₁_hi⟩
      rw [hΦ't]
      exact (hΦbare t htmem x).congr_of_eventuallyEq hev
    · have hq1_a₀ : a₀ < t := lt_of_lt_of_le ha₀_lt_t₁ (not_lt.mp hlt)
      have hev : (fun s : ℝ => Φ' s x) =ᶠ[𝓝 t] (fun s : ℝ => Ψ (Φ t₁ x) s) := by
        have hmem : Set.Ioo a₀ (t₁ + r) ∈ 𝓝 t := isOpen_Ioo.mem_nhds ⟨hq1_a₀, ht.2⟩
        filter_upwards [hmem] with s hs
        exact hΦ'_eq_Ψ s hs x
      have hΦ't : Φ' t x = Ψ (Φ t₁ x) t := hΦ'_eq_Ψ t ⟨hq1_a₀, ht.2⟩ x
      have htmem : t ∈ Set.Ioo (t₁ - r) (t₁ + r) := ⟨lt_of_le_of_lt ha₀_ge hq1_a₀, ht.2⟩
      rw [hΦ't]
      exact (hΨcurve_bare x t htmem).congr_of_eventuallyEq hev
  · intro s hs x
    by_cases hlt : s < t₁
    · simp only [hΦ'_def, if_pos hlt]
    · simp only [hΦ'_def, if_neg hlt]
      have hsmem : s ∈ Set.Ioo a₀ hi :=
        ⟨lt_of_lt_of_le ha₀_lt_t₁ (not_lt.mp hlt), hs.2⟩
      exact (hoverlap x s hsmem).symm

/-- A two-sided smooth bump on the closed interval `[lo, hi]`: it equals `1` on `Icc lo hi`
(indeed on the open `Ioo (lo - 1) (hi + 1)`) and vanishes outside `Icc (lo - 2) (hi + 2)`,
built from `Real.smoothTransition`.  Used to cut a globally smooth field down to one with
compact time support that still agrees with the original on `[lo, hi]`. -/
private noncomputable def fullIntervalBump (lo hi : ℝ) (s : ℝ) : ℝ :=
  Real.smoothTransition (s - (lo - 2)) * Real.smoothTransition ((hi + 2) - s)

private theorem fullIntervalBump_contDiff (lo hi : ℝ) :
    ContDiff ℝ ∞ (fullIntervalBump lo hi) := by
  unfold fullIntervalBump
  exact (Real.smoothTransition.contDiff.comp (by fun_prop)).mul
    (Real.smoothTransition.contDiff.comp (by fun_prop))

private theorem fullIntervalBump_eq_one (lo hi s : ℝ) (hs : s ∈ Set.Icc lo hi) :
    fullIntervalBump lo hi s = 1 := by
  unfold fullIntervalBump
  rw [Real.smoothTransition.one_of_one_le (by linarith [hs.1]),
    Real.smoothTransition.one_of_one_le (by linarith [hs.2]), mul_one]

private theorem fullIntervalBump_eq_zero (lo hi s : ℝ)
    (hs : s ∉ Set.Icc (lo - 2) (hi + 2)) : fullIntervalBump lo hi s = 0 := by
  unfold fullIntervalBump
  rw [Set.mem_Icc, not_and_or] at hs
  rcases hs with hlo | hhi
  · have : s < lo - 2 := lt_of_not_ge hlo
    rw [Real.smoothTransition.zero_of_nonpos (by linarith : s - (lo - 2) ≤ 0), zero_mul]
  · have : hi + 2 < s := lt_of_not_ge hhi
    rw [Real.smoothTransition.zero_of_nonpos (by linarith : (hi + 2) - s ≤ 0), mul_zero]

omit [FiniteDimensional ℝ E] [CompactSpace M] [CompleteSpace E] [BoundarylessManifold I M]
  [I.Boundaryless] [T2Space M] in
/-- The cut-off field `X̃ s x = fullIntervalBump lo hi s • X s x` is globally `C∞` whenever the
geometric field `X` is.  The fibre coordinate of a tangent-bundle trivialization is fibre-linear,
so the scalar commutes through it, reducing the goal to `ContMDiffAt.smul` of the (smooth) scalar
with the (smooth) fibre coordinate of `X`. -/
private theorem cutoffField_contMDiff
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)))
    (lo hi : ℝ) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M =>
        (TotalSpace.mk' E q.2 (fullIntervalBump lo hi q.1 • X q.1 q.2) : TangentBundle I M)) := by
  have hbump : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => fullIntervalBump lo hi q.1) :=
    (fullIntervalBump_contDiff lo hi).contMDiff.comp contMDiff_fst
  intro q₀
  have hXat := hX q₀
  rw [Bundle.contMDiffAt_totalSpace] at hXat ⊢
  obtain ⟨hXproj, hXfib⟩ := hXat
  refine ⟨hXproj, ?_⟩
  set e := trivializationAt E (TangentSpace I) q₀.2 with he
  have hfib := (hbump q₀).smul hXfib
  have hmem : e.baseSet ∈ nhds q₀.2 :=
    e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' q₀.2)
  have hpre : (fun q : ℝ × M => q.2) ⁻¹' e.baseSet ∈ nhds q₀ :=
    (continuous_snd.continuousAt) hmem
  refine hfib.congr_of_eventuallyEq ?_
  filter_upwards [hpre] with x hx
  simpa using (e.linear ℝ hx).2 (fullIntervalBump lo hi x.1) (X x.1 x.2)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [CompactSpace M] [CompleteSpace E]
  [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] in
/-- Where the field `Xt` vanishes along the straight line `s ↦ (pt.1 + s, pt.2)`, that line is an
integral curve of the autonomised field `autonomizedFlowVF Xt` (its velocity is `(1, 0)`).  Used
for points outside the compact time-support slab of a cut-off field. -/
private theorem trivialLine_isMIntegralCurveOn
    (Xt : ℝ → ∀ x : M, TangentSpace I x) (pt : ℝ × M) (S : Set ℝ)
    (hzero : ∀ s ∈ S, Xt (pt.1 + s) pt.2 = 0) :
    IsMIntegralCurveOn (fun s : ℝ => (pt.1 + s, pt.2)) (autonomizedFlowVF Xt) S := by
  intro t ht
  have htime : HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => pt.1 + s) S t
      (1 : ℝ →L[ℝ] ℝ) := by
    have h1 := hasMFDerivWithinAt_const (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) pt.1 S t
    have h2 := hasMFDerivWithinAt_id (I := 𝓘(ℝ, ℝ)) S t
    have h3 := h1.add h2
    have hfun : ((fun _ : ℝ => pt.1) + id) = (fun s : ℝ => pt.1 + s) := by funext s; simp
    rw [hfun] at h3
    refine h3.congr_mfderiv ?_
    apply ContinuousLinearMap.ext; intro x
    change (0 : ℝ →L[ℝ] ℝ) x + ContinuousLinearMap.id ℝ ℝ x = (1 : ℝ →L[ℝ] ℝ) x
    simp
  have hsnd : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun _ : ℝ => pt.2) S t
      (0 : TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ] TangentSpace I pt.2) :=
    hasMFDerivWithinAt_const (I := 𝓘(ℝ, ℝ)) (I' := I) pt.2 S t
  have hprod := htime.prodMk hsnd
  have hCLM : ((1 : ℝ →L[ℝ] ℝ).smulRight (autonomizedFlowVF Xt (pt.1 + t, pt.2)))
      = (1 : ℝ →L[ℝ] ℝ).prod (0 : TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ] TangentSpace I pt.2) := by
    apply ContinuousLinearMap.ext; intro r; apply Prod.ext
    · change r • (1 : ℝ) = r; simp
    · change r • Xt (pt.1 + t) pt.2 = (0 : TangentSpace I pt.2)
      rw [hzero t ht, smul_zero]
  rw [hCLM]; exact hprod

omit [CompactSpace M] in
/-- **Local existence uniform over a neighbourhood of starting points.** Applying the manifold
local-flow theorem `local_flow_jointSmooth_and_integralCurve` to the *autonomous* field
`autonomizedFlowVF Xt` on the product manifold `ℝ × M`, every point `pt : ℝ × M` has an open
neighbourhood `U ∋ pt` and a window radius `T > 0` such that every `q ∈ U` carries an integral
curve of `autonomizedFlowVF Xt` on `Ioo (-T) T` through `q` at parameter `0`. -/
private theorem autonomized_localUniform_curve
    (Xt : ℝ → ∀ x : M, TangentSpace I x)
    (hXt : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (Xt q.1 q.2) : TangentBundle I M)))
    (pt : ℝ × M) :
    ∃ (U : Set (ℝ × M)) (_ : IsOpen U) (_ : pt ∈ U) (T : ℝ) (_ : 0 < T),
      ∀ q ∈ U, ∃ γ : ℝ → ℝ × M, γ 0 = q ∧
        IsMIntegralCurveOn γ (autonomizedFlowVF Xt) (Set.Ioo (-T) T) := by
  have hsm : ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod I))
      ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ × E)) ∞
      (fun q' : ℝ × (ℝ × M) =>
        (TotalSpace.mk' (ℝ × E) q'.2
          ((fun (_ : ℝ) (q : ℝ × M) => autonomizedFlowVF Xt q) q'.1 q'.2) :
          TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) :=
    (autonomizedFlowVF_section_contMDiff Xt hXt).comp contMDiff_snd
  obtain ⟨U, hU_open, hpt_U, T, hT_pos, Ψ, hΨinit, _hΨsm, hΨbare⟩ :=
    local_flow_jointSmooth_and_integralCurve
      (I := 𝓘(ℝ, ℝ).prod I) (M := ℝ × M)
      (fun (_ : ℝ) (q : ℝ × M) => autonomizedFlowVF Xt q) hsm 0 pt
  refine ⟨U, hU_open, hpt_U, T, hT_pos, fun q hq => ⟨fun s => Ψ q s, ?_, ?_⟩⟩
  · have := hΨinit q hq; simpa using this
  · intro t ht
    exact (hΨbare q hq t (by simpa using ht)).hasMFDerivWithinAt

omit [CompactSpace M] in
/-- **Local jointly-smooth flow uniform over a neighbourhood of starting points.** The
smoothness-retaining companion of `autonomized_localUniform_curve`: applying the manifold
local-flow theorem `local_flow_jointSmooth_and_integralCurve` to the *autonomous* field
`autonomizedFlowVF Xt` on `ℝ × M`, every point `pt : ℝ × M` has an open neighbourhood `U ∋ pt`
and a window radius `T > 0` carrying a flow `Ψ : (ℝ × M) → ℝ → (ℝ × M)` fixing each anchor at
parameter `0`, *jointly* `C∞` in `(parameter, point)` on `Ioo (-T) T ×ˢ U`, and an integral curve
of `autonomizedFlowVF Xt` through every `q ∈ U`. -/
private theorem autonomized_localUniform_jointSmooth
    (Xt : ℝ → ∀ x : M, TangentSpace I x)
    (hXt : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (Xt q.1 q.2) : TangentBundle I M)))
    (pt : ℝ × M) :
    ∃ (U : Set (ℝ × M)) (_ : IsOpen U) (_ : pt ∈ U) (T : ℝ) (_ : 0 < T)
      (Ψ : (ℝ × M) → ℝ → (ℝ × M)),
      (∀ q ∈ U, Ψ q 0 = q) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod I)) (𝓘(ℝ, ℝ).prod I) ∞
        (fun b : ℝ × (ℝ × M) => Ψ b.2 b.1) (Set.Ioo (-T) T ×ˢ U) ∧
      (∀ q ∈ U, IsMIntegralCurveOn (fun s : ℝ => Ψ q s) (autonomizedFlowVF Xt) (Set.Ioo (-T) T)) := by
  have hsm : ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod I))
      ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ × E)) ∞
      (fun q' : ℝ × (ℝ × M) =>
        (TotalSpace.mk' (ℝ × E) q'.2
          ((fun (_ : ℝ) (q : ℝ × M) => autonomizedFlowVF Xt q) q'.1 q'.2) :
          TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) :=
    (autonomizedFlowVF_section_contMDiff Xt hXt).comp contMDiff_snd
  obtain ⟨U, hU_open, hpt_U, T, hT_pos, Ψ, hΨinit, hΨsm, hΨbare⟩ :=
    local_flow_jointSmooth_and_integralCurve
      (I := 𝓘(ℝ, ℝ).prod I) (M := ℝ × M)
      (fun (_ : ℝ) (q : ℝ × M) => autonomizedFlowVF Xt q) hsm 0 pt
  refine ⟨U, hU_open, hpt_U, T, hT_pos, Ψ, hΨinit, ?_, fun q hq t ht => ?_⟩
  · have hwin : Set.Ioo (-T) T ×ˢ U = Set.Ioo ((0 : ℝ) - T) (0 + T) ×ˢ U := by
      rw [zero_sub, zero_add]
    rw [hwin]; exact hΨsm
  · exact (hΨbare q hq t (by simpa using ht)).hasMFDerivWithinAt

/-- **Uniform-radius jointly-smooth local flow over the time slab.** The smoothness-retaining
companion of `autonomized_uniform_localExistence`: a single radius `ε > 0` such that *every* point
`pt : ℝ × M` whose time coordinate lies in the slab `Icc (lo - 3) (hi + 3)` carries an open
neighbourhood and a flow of `autonomizedFlowVF Xt` that is jointly `C∞` in `(parameter, point)` on
`Ioo (-ε) ε ×ˢ U`, fixes each anchor at parameter `0`, and is an integral curve through every point
of `U`.  Obtained from a finite subcover of the compact slab `Icc (lo - 3) (hi + 3) ×ˢ univ` by the
neighbourhood windows of `autonomized_localUniform_jointSmooth`, taking `ε` the (positive) infimum
of the finitely many window radii.  This is the uniform smooth-dependence window propagated below
to spatial smoothness of the flow slices. -/
private theorem autonomized_uniform_jointSmoothWindow
    (Xt : ℝ → ∀ x : M, TangentSpace I x)
    (hXt : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (Xt q.1 q.2) : TangentBundle I M)))
    (lo hi : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ pt : ℝ × M, pt.1 ∈ Set.Icc (lo - 3) (hi + 3) →
      ∃ (U : Set (ℝ × M)) (_ : IsOpen U) (_ : pt ∈ U) (Ψ : (ℝ × M) → ℝ → (ℝ × M)),
        (∀ q ∈ U, Ψ q 0 = q) ∧
        ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod I)) (𝓘(ℝ, ℝ).prod I) ∞
          (fun b : ℝ × (ℝ × M) => Ψ b.2 b.1) (Set.Ioo (-ε) ε ×ˢ U) ∧
        (∀ q ∈ U, IsMIntegralCurveOn (fun s : ℝ => Ψ q s) (autonomizedFlowVF Xt)
          (Set.Ioo (-ε) ε)) := by
  classical
  choose Uwin hUopen hUmem Twin hTpos Ψwin hΨ0 hΨsm hΨcurve using
    autonomized_localUniform_jointSmooth Xt hXt
  have hK : IsCompact (Set.Icc (lo - 3) (hi + 3) ×ˢ (Set.univ : Set M)) :=
    isCompact_Icc.prod isCompact_univ
  have hcover : (Set.Icc (lo - 3) (hi + 3) ×ˢ (Set.univ : Set M)) ⊆ ⋃ pt, Uwin pt :=
    fun x _ => Set.mem_iUnion.mpr ⟨x, hUmem x⟩
  obtain ⟨sf, hsf⟩ := hK.elim_finite_subcover Uwin hUopen hcover
  set ε : ℝ := if h : sf.Nonempty then sf.inf' h Twin else 1 with hε_def
  have hε_pos : 0 < ε := by
    rw [hε_def]; split
    · next h => rw [Finset.lt_inf'_iff]; exact fun pt _ => hTpos pt
    · exact one_pos
  have hε_le : ∀ pt ∈ sf, ε ≤ Twin pt := by
    intro pt hpt; rw [hε_def]; split
    · next h => exact Finset.inf'_le _ hpt
    · next h => exact absurd ⟨pt, hpt⟩ h
  refine ⟨ε, hε_pos, fun pt hpt_slab => ?_⟩
  have hpt_K : pt ∈ Set.Icc (lo - 3) (hi + 3) ×ˢ (Set.univ : Set M) :=
    ⟨hpt_slab, Set.mem_univ _⟩
  have hmem := hsf hpt_K
  rw [Set.mem_iUnion₂] at hmem
  obtain ⟨pti, hpti_sf, hpt_Ui⟩ := hmem
  have hwin_sub : Set.Ioo (-ε) ε ⊆ Set.Ioo (-Twin pti) (Twin pti) :=
    Set.Ioo_subset_Ioo (by linarith [hε_le pti hpti_sf]) (hε_le pti hpti_sf)
  refine ⟨Uwin pti, hUopen pti, hpt_Ui, Ψwin pti, hΨ0 pti, ?_, fun q hq => ?_⟩
  · exact (hΨsm pti).mono (Set.prod_mono hwin_sub (subset_refl _))
  · exact (hΨcurve pti q hq).mono hwin_sub

/-- **Uniform-radius local existence on `ℝ × M`.** For a cut-off field `Xt` that vanishes outside
the compact time slab `Icc (lo - 2) (hi + 2)`, there is a single radius `ε > 0` such that *every*
point of `ℝ × M` carries an integral curve of `autonomizedFlowVF Xt` on `Ioo (-ε) ε`.  Over the
compact slab `Icc (lo - 3) (hi + 3) ×ˢ univ` a finite subcover by the neighbourhood windows of
`autonomized_localUniform_curve` gives a uniform radius; outside the slab the field vanishes along
the straight line, which is a global integral curve.  This is the uniform-time hypothesis consumed
by Mathlib's `exists_isMIntegralCurve_of_isMIntegralCurveOn`. -/
private theorem autonomized_uniform_localExistence
    (Xt : ℝ → ∀ x : M, TangentSpace I x)
    (hXt : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (Xt q.1 q.2) : TangentBundle I M)))
    (lo hi : ℝ)
    (hvanish : ∀ s : ℝ, s ∉ Set.Icc (lo - 2) (hi + 2) → ∀ x : M, Xt s x = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ pt : ℝ × M, ∃ γ : ℝ → ℝ × M, γ 0 = pt ∧
      IsMIntegralCurveOn γ (autonomizedFlowVF Xt) (Set.Ioo (-ε) ε) := by
  classical
  choose Uwin hUopen hUmem Twin hTpos hwin using autonomized_localUniform_curve Xt hXt
  have hK : IsCompact (Set.Icc (lo - 3) (hi + 3) ×ˢ (Set.univ : Set M)) :=
    isCompact_Icc.prod isCompact_univ
  have hcover : (Set.Icc (lo - 3) (hi + 3) ×ˢ (Set.univ : Set M)) ⊆ ⋃ pt, Uwin pt :=
    fun x _ => Set.mem_iUnion.mpr ⟨x, hUmem x⟩
  obtain ⟨sf, hsf⟩ := hK.elim_finite_subcover Uwin hUopen hcover
  set T₀ : ℝ := if h : sf.Nonempty then sf.inf' h Twin else 1 with hT₀
  have hT₀_pos : 0 < T₀ := by
    rw [hT₀]; split
    · next h => rw [Finset.lt_inf'_iff]; exact fun pt _ => hTpos pt
    · exact one_pos
  have hT₀_le : ∀ pt ∈ sf, T₀ ≤ Twin pt := by
    intro pt hpt; rw [hT₀]; split
    · next h => exact Finset.inf'_le _ hpt
    · next h => exact absurd ⟨pt, hpt⟩ h
  refine ⟨min 1 T₀, lt_min one_pos hT₀_pos, fun pt => ?_⟩
  by_cases hpt_slab : pt.1 ∈ Set.Icc (lo - 3) (hi + 3)
  · have hpt_K : pt ∈ Set.Icc (lo - 3) (hi + 3) ×ˢ (Set.univ : Set M) :=
      ⟨hpt_slab, Set.mem_univ _⟩
    have hmem := hsf hpt_K
    rw [Set.mem_iUnion₂] at hmem
    obtain ⟨pti, hpti_sf, hpt_Ui⟩ := hmem
    obtain ⟨γ, hγ0, hγcurve⟩ := hwin pti pt hpt_Ui
    refine ⟨γ, hγ0, hγcurve.mono ?_⟩
    have hle : min 1 T₀ ≤ Twin pti := le_trans (min_le_right _ _) (hT₀_le pti hpti_sf)
    exact Set.Ioo_subset_Ioo (by linarith) (by linarith)
  · refine ⟨fun s => (pt.1 + s, pt.2), by simp, ?_⟩
    apply trivialLine_isMIntegralCurveOn Xt pt
    intro s hs
    apply hvanish (pt.1 + s) ?_ pt.2
    rw [Set.mem_Ioo] at hs
    rw [Set.mem_Icc]
    rw [Set.mem_Icc, not_and_or] at hpt_slab
    have hs1 : |s| < 1 := lt_of_lt_of_le (abs_lt.mpr ⟨hs.1, hs.2⟩) (min_le_left _ _)
    rw [abs_lt] at hs1
    rintro ⟨hle1, hle2⟩
    rcases hpt_slab with hlow | hhigh
    · have : pt.1 < lo - 3 := lt_of_not_ge hlow
      linarith [hs1.1]
    · have : hi + 3 < pt.1 := lt_of_not_ge hhigh
      linarith [hs1.2]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [CompactSpace M] [CompleteSpace E]
  [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] in
/-- The time component of a *global* integral curve `c` of `autonomizedFlowVF Xt` whose value at
`0` has first coordinate `0` is the identity `(c s).1 = s`: the first component of the autonomised
velocity is the constant `1`, so `(c ·).1` solves `φ' = 1, φ 0 = 0`. -/
private theorem autonomized_time_comp_eq_self
    (Xt : ℝ → ∀ x : M, TangentSpace I x) (c : ℝ → ℝ × M)
    (hc : IsMIntegralCurve c (autonomizedFlowVF Xt)) (h0 : (c 0).1 = 0) :
    ∀ s, (c s).1 = s := by
  have hderiv : ∀ s, HasDerivAt (fun u => (c u).1) (1 : ℝ) s :=
    fun s => autonomizedFlow_fst_hasDerivAt Xt c s (hc s)
  intro s
  have hconst : ∀ u : ℝ, HasDerivAt (fun w => (c w).1 - w) (0 : ℝ) u :=
    fun u => by simpa using (hderiv u).sub (hasDerivAt_id u)
  have hkey : (fun w => (c w).1 - w) s = (fun w => (c w).1 - w) 0 :=
    is_const_of_deriv_eq_zero (fun u => (hconst u).differentiableAt) (fun u => (hconst u).deriv) s 0
  simp only at hkey; rw [h0] at hkey; linarith

omit [FiniteDimensional ℝ E] [CompactSpace M] [CompleteSpace E] [I.Boundaryless] in
/-- **Global bare flow of a globally `C∞` field, from uniform-radius local existence.** Given a
field `Xt` with jointly-`C¹` autonomisation and a uniform local-existence radius `ε`, Mathlib's
`exists_isMIntegralCurve_of_isMIntegralCurveOn` upgrades the local curves to *global* integral
curves of `autonomizedFlowVF Xt`; choosing the one through `(0, x)` and taking its spatial
component yields a flow `Φ` with `Φ 0 = id` carrying the bare velocity `Xt t (Φ t x)` at *every*
time `t : ℝ`.  (Joint smoothness in `(t, x)` is *not* produced here — that is a separate
obligation; see the headline.) -/
private theorem global_bareFlow_of_uniform_localExistence
    (Xt : ℝ → ∀ x : M, TangentSpace I x)
    (hXtC1 : AutonomizedFieldJointC1 (I := I) Xt)
    {ε : ℝ} (hε : 0 < ε)
    (huniform : ∀ pt : ℝ × M, ∃ γ : ℝ → ℝ × M, γ 0 = pt ∧
      IsMIntegralCurveOn γ (autonomizedFlowVF Xt) (Set.Ioo (-ε) ε)) :
    ∃ Φ : ℝ → M → M, (∀ x, Φ 0 x = x) ∧
      (∀ t : ℝ, ∀ x : M, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ s x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Xt t (Φ t x)))) := by
  classical
  have hglobal := fun pt : ℝ × M =>
    exists_isMIntegralCurve_of_isMIntegralCurveOn (v := autonomizedFlowVF Xt)
      (fun p => hXtC1 p) hε huniform pt
  choose c hc0 hc using fun x : M => hglobal ((0 : ℝ), x)
  refine ⟨fun s x => (c x s).2, fun x => by simp [hc0 x], ?_⟩
  intro t x
  have htime : ∀ s, (c x s).1 = s :=
    autonomized_time_comp_eq_self Xt (c x) (hc x) (by rw [hc0 x])
  have hsnd := autonomizedFlow_snd_hasMFDerivAt Xt (c x) t (hc x t)
  rw [htime t] at hsnd
  exact hsnd

/-- **Spatial smoothness of the flow slices, on the slab.** For the global bare flow `Φ` of a
globally-`C∞` cut-off field `Xt` (with `Φ 0 = id` and the bare velocity at *every* time), each
slice `Φ s : M → M` with `s ∈ Icc (lo - 1) (hi + 1)` is smooth.

The argument propagates spatial smoothness from the smooth slice `Φ 0 = id` along the connected
interval, using the *uniform* smooth-dependence window `ε` of `autonomized_uniform_jointSmoothWindow`.
Fix `x₀`.  The key local step (`hstep`): if `Φ s₀` is smooth at `x₀` and `s₀` lies in the slab, then
for every `s` with `|s - s₀| < ε` the slice `Φ s` is smooth at `x₀` — because near `x₀`,
`Φ s = (q ↦ Ψ q (s - s₀)).2 ∘ (x ↦ (s₀, Φ s₀ x))`, a composition of the jointly-smooth local
autonomised flow `Ψ` (anchored at `(s₀, Φ s₀ x₀)`) with the smooth map `x ↦ (s₀, Φ s₀ x)`; the
agreement is integral-curve uniqueness on `ℝ × M` (the autonomisation lift of `Φ` and the local flow
are both integral curves through `(s₀, Φ s₀ x)`, related by the time-shift `comp_add`).  Both the
"forward" (set open) and "backward" (set closed) halves of the connectedness argument
(`IsPreconnected.subset_of_closure_inter_subset` on `isPreconnected_Icc`) are instances of `hstep`,
so no invertibility of the flow slices is needed. -/
private theorem cutoffFlow_slice_contMDiff
    (Xt : ℝ → ∀ x : M, TangentSpace I x)
    (hXt_sm : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (Xt q.1 q.2) : TangentBundle I M)))
    (hXtC1 : AutonomizedFieldJointC1 (I := I) Xt)
    (Φ : ℝ → M → M) (hΦ0 : ∀ x : M, Φ 0 x = x)
    (hΦbare : ∀ t : ℝ, ∀ x : M, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ s x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Xt t (Φ t x))))
    (lo hi : ℝ) (hlo : lo ≤ 0) (hhi : 0 ≤ hi) :
    ∀ s ∈ Set.Icc (lo - 1) (hi + 1), ContMDiff I I ∞ (Φ s) := by
  classical
  obtain ⟨ε, hε_pos, hwin⟩ := autonomized_uniform_jointSmoothWindow Xt hXt_sm lo hi
  set ε' : ℝ := min ε 1 with hε'_def
  have hε'_pos : 0 < ε' := lt_min hε_pos one_pos
  have hε'_le_ε : ε' ≤ ε := min_le_left _ _
  have hε'_le_one : ε' ≤ 1 := min_le_right _ _
  -- Each `cx : u ↦ (u, Φ u x)` is a global integral curve of the autonomised field.
  have hcx : ∀ x : M, IsMIntegralCurve (fun u : ℝ => (u, Φ u x)) (autonomizedFlowVF Xt) := by
    intro x t
    have h := autonomizedLift_hasMFDerivWithinAt Xt (fun u : ℝ => Φ u x) Set.univ t
      (hΦbare t x).hasMFDerivWithinAt
    exact h.hasMFDerivAt Filter.univ_mem
  -- Reduce to pointwise spatial smoothness at each `x₀`.
  intro s₀_target hmem_target x₀
  -- The local propagation step.
  have hstep : ∀ s₀ : ℝ, s₀ ∈ Set.Icc (lo - 3) (hi + 3) →
      ContMDiffAt I I ∞ (Φ s₀) x₀ →
      ∀ s : ℝ, |s - s₀| < ε' → ContMDiffAt I I ∞ (Φ s) x₀ := by
    intro s₀ hs₀_slab hΦs₀ s hss₀
    obtain ⟨U, hU_open, hpt_U, Ψ, hΨ0, hΨsm, hΨcurve⟩ := hwin (s₀, Φ s₀ x₀) hs₀_slab
    have hτ_mem : (s - s₀) ∈ Set.Ioo (-ε) ε := by
      rw [Set.mem_Ioo, ← abs_lt]; exact lt_of_lt_of_le hss₀ hε'_le_ε
    -- The candidate `g x = (Ψ (s₀, Φ s₀ x) (s - s₀)).2`, smooth at `x₀`.
    set ι : M → ℝ × M := fun x => (s₀, Φ s₀ x) with hι_def
    have hι_smooth : ContMDiffAt I (𝓘(ℝ, ℝ).prod I) ∞ ι x₀ :=
      contMDiffAt_const.prodMk hΦs₀
    have hι_x₀ : ι x₀ = (s₀, Φ s₀ x₀) := rfl
    have hslice : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
        (fun q : ℝ × M => Ψ q (s - s₀)) (s₀, Φ s₀ x₀) := by
      have hprepend : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod I)) ∞
          (fun q : ℝ × M => ((s - s₀, q) : ℝ × (ℝ × M))) (s₀, Φ s₀ x₀) :=
        contMDiffAt_const.prodMk contMDiffAt_id
      have hmem_prod : ((s - s₀, (s₀, Φ s₀ x₀)) : ℝ × (ℝ × M)) ∈ Set.Ioo (-ε) ε ×ˢ U :=
        ⟨hτ_mem, hpt_U⟩
      have hopen_prod : IsOpen (Set.Ioo (-ε) ε ×ˢ U) := isOpen_Ioo.prod hU_open
      have hΨsm_at : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod I)) (𝓘(ℝ, ℝ).prod I) ∞
          (fun b : ℝ × (ℝ × M) => Ψ b.2 b.1) (Set.Ioo (-ε) ε ×ˢ U)
          (s - s₀, (s₀, Φ s₀ x₀)) := hΨsm _ hmem_prod
      have hΨsm_contMDiffAt : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod I)) (𝓘(ℝ, ℝ).prod I) ∞
          (fun b : ℝ × (ℝ × M) => Ψ b.2 b.1) (s - s₀, (s₀, Φ s₀ x₀)) :=
        hΨsm_at.contMDiffAt (hopen_prod.mem_nhds hmem_prod)
      exact hΨsm_contMDiffAt.comp (s₀, Φ s₀ x₀) hprepend
    have hg_smooth : ContMDiffAt I I ∞ (fun x : M => (Ψ (s₀, Φ s₀ x) (s - s₀)).2) x₀ := by
      have h1 : ContMDiffAt I (𝓘(ℝ, ℝ).prod I) ∞
          (fun x : M => Ψ (ι x) (s - s₀)) x₀ :=
        (hι_x₀ ▸ hslice).comp x₀ hι_smooth
      exact contMDiffAt_snd.comp x₀ h1
    -- Eventual agreement `g = Φ s` near `x₀`, by integral-curve uniqueness.
    have heq : (fun x : M => (Ψ (s₀, Φ s₀ x) (s - s₀)).2) =ᶠ[nhds x₀] Φ s := by
      have hW : (fun x : M => (s₀, Φ s₀ x)) ⁻¹' U ∈ nhds x₀ := by
        have hcont : ContinuousAt (fun x : M => (s₀, Φ s₀ x)) x₀ := hι_smooth.continuousAt
        exact hcont.preimage_mem_nhds (hU_open.mem_nhds hpt_U)
      filter_upwards [hW] with x hx
      have hqU : (s₀, Φ s₀ x) ∈ U := hx
      -- The local flow from `(s₀, Φ s₀ x)` and the shifted lift of `Φ` agree on `Ioo (-ε) ε`.
      have hΨq : IsMIntegralCurveOn (fun u : ℝ => Ψ (s₀, Φ s₀ x) u)
          (autonomizedFlowVF Xt) (Set.Ioo (-ε) ε) := hΨcurve (s₀, Φ s₀ x) hqU
      have hshift : IsMIntegralCurveOn (fun u : ℝ => (u + s₀, Φ (u + s₀) x))
          (autonomizedFlowVF Xt) (Set.Ioo (-ε) ε) :=
        ((hcx x).comp_add s₀).isMIntegralCurveOn (Set.Ioo (-ε) ε)
      have hstart : (fun u : ℝ => Ψ (s₀, Φ s₀ x) u) 0
          = (fun u : ℝ => (u + s₀, Φ (u + s₀) x)) 0 := by
        simp only [hΨ0 (s₀, Φ s₀ x) hqU, zero_add]
      have h0mem : (0 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨by linarith, hε_pos⟩
      have hv : ContMDiff (𝓘(ℝ, ℝ).prod I) ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ × E)) 1
          (fun p : ℝ × M =>
            (⟨p, autonomizedFlowVF Xt p⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) :=
        fun p => hXtC1 p
      have heqOn := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
        h0mem hv hΨq hshift hstart
      have hatτ := heqOn hτ_mem
      have : Ψ (s₀, Φ s₀ x) (s - s₀) = (s - s₀ + s₀, Φ (s - s₀ + s₀) x) := hatτ
      rw [this]
      simp only [sub_add_cancel]
    exact hg_smooth.congr_of_eventuallyEq heq.symm
  -- Connectedness: the good set contains `Icc (lo - 1) (hi + 1)`.
  set u : Set ℝ := {s : ℝ | ContMDiffAt I I ∞ (Φ s) x₀} ∩ Set.Ioo (lo - 2) (hi + 2) with hu_def
  have hslab_sub : Set.Ioo (lo - 2 : ℝ) (hi + 2) ⊆ Set.Icc (lo - 3) (hi + 3) :=
    fun t ht => ⟨le_of_lt (by linarith [ht.1]), le_of_lt (by linarith [ht.2])⟩
  have hu_open : IsOpen u := by
    rw [isOpen_iff_mem_nhds]
    rintro s ⟨hs_smooth, hs_int⟩
    have hs_slab : s ∈ Set.Icc (lo - 3) (hi + 3) := hslab_sub hs_int
    have hball : Set.Ioo (s - ε') (s + ε') ∩ Set.Ioo (lo - 2) (hi + 2) ⊆ u := by
      rintro s' ⟨hs'_ball, hs'_int⟩
      refine ⟨?_, hs'_int⟩
      have hdist : |s' - s| < ε' := by rw [abs_lt]; constructor <;> [linarith [hs'_ball.1]; linarith [hs'_ball.2]]
      exact hstep s hs_slab hs_smooth s' hdist
    refine Filter.mem_of_superset (Filter.inter_mem ?_ ?_) hball
    · exact isOpen_Ioo.mem_nhds ⟨by linarith [hε'_pos], by linarith [hε'_pos]⟩
    · exact isOpen_Ioo.mem_nhds hs_int
  have h0_u : (0 : ℝ) ∈ Set.Icc (lo - 1 : ℝ) (hi + 1) ∩ u := by
    refine ⟨⟨by linarith, by linarith⟩, ?_, ⟨by linarith, by linarith⟩⟩
    change ContMDiffAt I I ∞ (Φ 0) x₀
    have hΦ0_eq : Φ 0 = (id : M → M) := funext hΦ0
    rw [hΦ0_eq]; exact contMDiffAt_id
  have hclosed : closure u ∩ Set.Icc (lo - 1 : ℝ) (hi + 1) ⊆ u := by
    rintro sstar ⟨hsstar_cl, hsstar_Icc⟩
    have hsstar_int : sstar ∈ Set.Ioo (lo - 2 : ℝ) (hi + 2) :=
      ⟨by linarith [hsstar_Icc.1], by linarith [hsstar_Icc.2]⟩
    -- A point of `u` within `ε'` of `sstar`.
    have hnhd : Set.Ioo (sstar - ε') (sstar + ε') ∩ Set.Ioo (lo - 2) (hi + 2) ∈ nhds sstar :=
      Filter.inter_mem
        (isOpen_Ioo.mem_nhds ⟨by linarith [hε'_pos], by linarith [hε'_pos]⟩)
        (isOpen_Ioo.mem_nhds hsstar_int)
    obtain ⟨sn, ⟨hsn_ball, _hsn_int⟩, hsn_smooth, _hsn_int2⟩ :=
      mem_closure_iff_nhds.mp hsstar_cl _ hnhd
    have hsn_slab : sn ∈ Set.Icc (lo - 3) (hi + 3) := hslab_sub _hsn_int
    have hdist : |sstar - sn| < ε' := by
      rw [abs_lt]; constructor <;> [linarith [hsn_ball.2]; linarith [hsn_ball.1]]
    exact ⟨hstep sn hsn_slab hsn_smooth sstar hdist, hsstar_int⟩
  have hsub : Set.Icc (lo - 1 : ℝ) (hi + 1) ⊆ u :=
    isPreconnected_Icc.subset_of_closure_inter_subset hu_open ⟨0, h0_u⟩ hclosed
  exact (hsub hmem_target).1

/-- **Joint smoothness of the full-interval flow.** For the global bare flow `Φ` of a globally-`C∞`
cut-off field `Xt` (with `Φ 0 = id` and the bare velocity at *every* time), the map
`(s, x) ↦ Φ s x` is jointly `C∞` on `Ioo lo hi ×ˢ univ`.

At each `(s₀, x₀)` the flow equals, on a whole neighbourhood in `ℝ × M`, the candidate
`(s, x) ↦ (Ψ (s₀, Φ s₀ x) (s - s₀)).2`, where `Ψ` is the uniform-window jointly-smooth local
autonomised flow anchored at `(s₀, Φ s₀ x₀)` (`autonomized_uniform_jointSmoothWindow`).  The
candidate is jointly smooth there because it is the composition of the jointly-smooth `Ψ` with
`(s, x) ↦ (s - s₀, (s₀, Φ s₀ x))` — and the inner slice `x ↦ Φ s₀ x` is smooth by
`cutoffFlow_slice_contMDiff`.  The agreement is the same integral-curve-uniqueness identity used in
the slice lemma (the autonomisation lift of `Φ` and `Ψ` are integral curves through `(s₀, Φ s₀ x)`,
related by the time-shift `comp_add`). -/
private theorem cutoffFlow_jointContMDiffOn
    (Xt : ℝ → ∀ x : M, TangentSpace I x)
    (hXt_sm : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (Xt q.1 q.2) : TangentBundle I M)))
    (hXtC1 : AutonomizedFieldJointC1 (I := I) Xt)
    (Φ : ℝ → M → M) (hΦ0 : ∀ x : M, Φ 0 x = x)
    (hΦbare : ∀ t : ℝ, ∀ x : M, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ s x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Xt t (Φ t x))))
    (lo hi : ℝ) (hlo : lo ≤ 0) (hhi : 0 ≤ hi) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2)
      (Set.Ioo lo hi ×ˢ (Set.univ : Set M)) := by
  classical
  obtain ⟨ε, hε_pos, hwin⟩ := autonomized_uniform_jointSmoothWindow Xt hXt_sm lo hi
  have hslice := cutoffFlow_slice_contMDiff Xt hXt_sm hXtC1 Φ hΦ0 hΦbare lo hi hlo hhi
  have hcx : ∀ x : M, IsMIntegralCurve (fun u : ℝ => (u, Φ u x)) (autonomizedFlowVF Xt) := by
    intro x t
    have h := autonomizedLift_hasMFDerivWithinAt Xt (fun u : ℝ => Φ u x) Set.univ t
      (hΦbare t x).hasMFDerivWithinAt
    exact h.hasMFDerivAt Filter.univ_mem
  intro q₀ hq₀
  obtain ⟨hs₀_mem, _⟩ := hq₀
  set s₀ : ℝ := q₀.1 with hs₀_def
  set x₀ : M := q₀.2 with hx₀_def
  have hs₀_slab : s₀ ∈ Set.Icc (lo - 3) (hi + 3) :=
    ⟨le_of_lt (by linarith [hs₀_mem.1]), le_of_lt (by linarith [hs₀_mem.2])⟩
  have hs₀_slice : s₀ ∈ Set.Icc (lo - 1 : ℝ) (hi + 1) :=
    ⟨le_of_lt (by linarith [hs₀_mem.1]), le_of_lt (by linarith [hs₀_mem.2])⟩
  have hΦs₀ : ContMDiff I I ∞ (Φ s₀) := hslice s₀ hs₀_slice
  obtain ⟨U, hU_open, hpt_U, Ψ, hΨ0, hΨsm, hΨcurve⟩ := hwin (s₀, Φ s₀ x₀) hs₀_slab
  -- The candidate, jointly smooth at `q₀`.
  set g : ℝ × M → M := fun q => (Ψ (s₀, Φ s₀ q.2) (q.1 - s₀)).2 with hg_def
  have hι2 : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (fun q : ℝ × M => ((s₀, Φ s₀ q.2) : ℝ × M)) q₀ :=
    contMDiffAt_const.prodMk ((hΦs₀ x₀).comp q₀ contMDiffAt_snd)
  have hinner : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod I)) ∞
      (fun q : ℝ × M => ((q.1 - s₀, (s₀, Φ s₀ q.2)) : ℝ × (ℝ × M))) q₀ := by
    have h1 : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => q.1 - s₀) q₀ :=
      ((contDiff_id.sub contDiff_const).contMDiff.contMDiffAt).comp q₀ contMDiffAt_fst
    exact h1.prodMk hι2
  have hτ_mem : (0 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨by linarith, hε_pos⟩
  have hinner_pt : (fun q : ℝ × M => ((q.1 - s₀, (s₀, Φ s₀ q.2)) : ℝ × (ℝ × M))) q₀
      = (0, (s₀, Φ s₀ x₀)) := by
    simp only [hs₀_def, hx₀_def, sub_self]
  have hΨ_at : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod I)) (𝓘(ℝ, ℝ).prod I) ∞
      (fun b : ℝ × (ℝ × M) => Ψ b.2 b.1) (0, (s₀, Φ s₀ x₀)) := by
    have hmem_prod : ((0, (s₀, Φ s₀ x₀)) : ℝ × (ℝ × M)) ∈ Set.Ioo (-ε) ε ×ˢ U :=
      ⟨hτ_mem, hpt_U⟩
    have hopen_prod : IsOpen (Set.Ioo (-ε) ε ×ˢ U) := isOpen_Ioo.prod hU_open
    exact (hΨsm _ hmem_prod).contMDiffAt (hopen_prod.mem_nhds hmem_prod)
  have hg_smooth : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞ g q₀ := by
    have hcomp : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
        (fun q : ℝ × M => Ψ (s₀, Φ s₀ q.2) (q.1 - s₀)) q₀ :=
      (hinner_pt ▸ hΨ_at).comp q₀ hinner
    exact contMDiffAt_snd.comp q₀ hcomp
  -- Eventual agreement `g = (fun q => Φ q.1 q.2)` near `q₀`.
  have heq : g =ᶠ[nhds q₀] (fun q : ℝ × M => Φ q.1 q.2) := by
    have hWmem : (fun q : ℝ × M => (s₀, Φ s₀ q.2)) ⁻¹' U ∈ nhds q₀ := by
      have hcont : ContinuousAt (fun q : ℝ × M => (s₀, Φ s₀ q.2)) q₀ := hι2.continuousAt
      exact hcont.preimage_mem_nhds (hU_open.mem_nhds (by simpa [hx₀_def] using hpt_U))
    have hτmem : (fun q : ℝ × M => q.1 - s₀) ⁻¹' Set.Ioo (-ε) ε ∈ nhds q₀ := by
      have hcont : ContinuousAt (fun q : ℝ × M => q.1 - s₀) q₀ :=
        (continuous_fst.sub continuous_const).continuousAt
      refine hcont.preimage_mem_nhds (isOpen_Ioo.mem_nhds ?_)
      simp only [hs₀_def, sub_self]; exact hτ_mem
    filter_upwards [hWmem, hτmem] with q hqU hqτ
    have hqU' : (s₀, Φ s₀ q.2) ∈ U := hqU
    have hqτ' : (q.1 - s₀) ∈ Set.Ioo (-ε) ε := hqτ
    have hΨq : IsMIntegralCurveOn (fun u : ℝ => Ψ (s₀, Φ s₀ q.2) u)
        (autonomizedFlowVF Xt) (Set.Ioo (-ε) ε) := hΨcurve (s₀, Φ s₀ q.2) hqU'
    have hshift : IsMIntegralCurveOn (fun u : ℝ => (u + s₀, Φ (u + s₀) q.2))
        (autonomizedFlowVF Xt) (Set.Ioo (-ε) ε) :=
      ((hcx q.2).comp_add s₀).isMIntegralCurveOn (Set.Ioo (-ε) ε)
    have hstart : (fun u : ℝ => Ψ (s₀, Φ s₀ q.2) u) 0
        = (fun u : ℝ => (u + s₀, Φ (u + s₀) q.2)) 0 := by
      simp only [hΨ0 (s₀, Φ s₀ q.2) hqU', zero_add]
    have h0mem : (0 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨by linarith, hε_pos⟩
    have hv : ContMDiff (𝓘(ℝ, ℝ).prod I) ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ × E)) 1
        (fun p : ℝ × M =>
          (⟨p, autonomizedFlowVF Xt p⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) :=
      fun p => hXtC1 p
    have heqOn := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
      h0mem hv hΨq hshift hstart
    have hatτ := heqOn hqτ'
    change (Ψ (s₀, Φ s₀ q.2) (q.1 - s₀)).2 = Φ q.1 q.2
    have hval : Ψ (s₀, Φ s₀ q.2) (q.1 - s₀) = (q.1 - s₀ + s₀, Φ (q.1 - s₀ + s₀) q.2) := hatτ
    rw [hval]
    simp only [sub_add_cancel]
  exact (hg_smooth.congr_of_eventuallyEq heq.symm).contMDiffWithinAt

/-- **Full-interval flow of a globally smooth field on a closed manifold.**

For a globally jointly-`C∞` time-dependent field `X` on a closed manifold and any horizon
`T > 0`, there is a flow `Φ : ℝ → M → M` with `Φ 0 = id`, jointly `C∞` on an open interval
`Ioo lo hi ⊇ [0, T]` (with `lo < 0 < T < hi`), carrying the bare velocity `X t (Φ t x)`.

The construction (`lo := -1`, `hi := T + 1`) cuts `X` down to the field
`X̃ s x = fullIntervalBump (-1) (T+1) s • X s x`, which is globally `C∞` (`cutoffField_contMDiff`),
agrees with `X` on `[lo, hi]` (`fullIntervalBump_eq_one`), and has compact time support
(`fullIntervalBump_eq_zero`).  Applying the manifold local-flow theorem to the *autonomous* field
`(1, X̃)` on `ℝ × M`, a finite subcover of the compact slab `Icc (lo-3) (hi+3) ×ˢ univ` plus the
trivial straight-line curve outside it gives a uniform local-existence radius
(`autonomized_uniform_localExistence`); Mathlib's `exists_isMIntegralCurve_of_isMIntegralCurveOn`
then upgrades to global integral curves, whose spatial components form a flow `Φ` with `Φ 0 = id`
and the bare velocity `X̃ t (Φ t x) = X t (Φ t x)` on `[lo, hi]`
(`global_bareFlow_of_uniform_localExistence`).

The *joint* smoothness `ContMDiffOn … (Ioo lo hi ×ˢ univ)` is `cutoffFlow_jointContMDiffOn`.  Since
the cut-off field `X̃` is *globally* `C∞` (unlike a field that is only `C⁰` at `t = 0`), smooth
dependence on initial conditions genuinely holds: the finite subcover of the compact time slab gives
a *uniform-over-time* smooth-dependence window `ε` (`autonomized_uniform_jointSmoothWindow`), along
which spatial smoothness of the flow slices propagates from `Φ 0 = id` by a connectedness argument
(`cutoffFlow_slice_contMDiff`); near each `(s₀, x₀)` the flow then equals the jointly-smooth local
autonomised flow pre-composed with the smooth slice `Φ s₀`, the agreement being integral-curve
uniqueness on `ℝ × M`.  The whole theorem is proven sorry-free. -/
theorem global_flow_full_interval_on_closed_manifold
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hX : ContMDiff (𝓘(ℝ,ℝ).prod I) (I.prod 𝓘(ℝ,E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)))
    (T : ℝ) (hT : 0 < T) :
    ∃ (Φ : ℝ → M → M) (lo hi : ℝ), lo < 0 ∧ T < hi ∧ (∀ x, Φ 0 x = x) ∧
      ContMDiffOn (𝓘(ℝ,ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2) (Set.Ioo lo hi ×ˢ Set.univ) ∧
      (∀ t ∈ Set.Ioo lo hi, ∀ x : M, HasMFDerivAt 𝓘(ℝ,ℝ) I (fun s => Φ s x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x)))) := by
  set Xt : ℝ → ∀ x : M, TangentSpace I x :=
    fun s x => fullIntervalBump (-1) (T + 1) s • X s x with hXt_def
  have hXt_sm : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (Xt q.1 q.2) : TangentBundle I M)) :=
    cutoffField_contMDiff X hX (-1) (T + 1)
  have hXtC1 : AutonomizedFieldJointC1 (I := I) Xt :=
    autonomizedFieldJointC1_of_contMDiff Xt hXt_sm
  have hXt_eq : ∀ s ∈ Set.Icc (-1 : ℝ) (T + 1), ∀ x : M, Xt s x = X s x := by
    intro s hs x
    rw [hXt_def]
    simp only [fullIntervalBump_eq_one (-1) (T + 1) s hs, one_smul]
  have hvanish : ∀ s : ℝ, s ∉ Set.Icc (-1 - 2 : ℝ) (T + 1 + 2) → ∀ x : M, Xt s x = 0 := by
    intro s hs x
    rw [hXt_def]
    simp only [fullIntervalBump_eq_zero (-1) (T + 1) s hs, zero_smul]
  obtain ⟨ε, hε, huniform⟩ :=
    autonomized_uniform_localExistence Xt hXt_sm (-1) (T + 1) hvanish
  obtain ⟨Φ, hΦ0, hΦbare⟩ :=
    global_bareFlow_of_uniform_localExistence Xt hXtC1 hε huniform
  refine ⟨Φ, -1, T + 1, by norm_num, by linarith, hΦ0, ?_, ?_⟩
  · exact cutoffFlow_jointContMDiffOn Xt hXt_sm hXtC1 Φ hΦ0 hΦbare (-1) (T + 1)
      (by norm_num) (by linarith)
  · intro t ht x
    have htIcc : t ∈ Set.Icc (-1 : ℝ) (T + 1) := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hb := hΦbare t x
    rw [hXt_eq t htIcc (Φ t x)] at hb
    exact hb

/-- **Spatial smoothness of the autonomous-flow slices from an arbitrary anchor time.** The
companion of `cutoffFlow_slice_contMDiff` that does *not* fix the anchor at `0`: for the global
autonomous flow `ψ` of a globally-`C∞` cut-off field `Xt` on `ℝ × M` (each `ψ p` a global integral
curve fixing `p` at parameter `0`, with time-coordinate `(ψ p u).1 = p.1 + u`), the spatial-slice
map `x ↦ ψ (σ, x) a` is smooth at `x₀` whenever `σ` and `σ + a` keep the closed segment between
`0` and `a` inside the smooth-dependence slab.

The argument is the connectedness propagation of `cutoffFlow_slice_contMDiff` carried out in the
parameter `b ∈ uIcc 0 a` (so it works for both forward `a > 0` and backward `a < 0`).  Seed at
`b = 0`, where `ψ (σ, x) 0 = (σ, x)` is smooth in `x`.  The local step: near `x₀`,
`ψ (σ, x) b = Ψ_win (ψ (σ, x) b₀) (b - b₀)`, the jointly-smooth uniform local autonomised flow
`Ψ_win` (`autonomized_uniform_jointSmoothWindow`) anchored at `ψ (σ, x₀) b₀` pre-composed with the
smooth map `x ↦ ψ (σ, x) b₀`; the agreement is integral-curve uniqueness on `ℝ × M` (the global
curve `u ↦ ψ (σ, x) u` time-shifted by `comp_add` and the local flow both pass through
`ψ (σ, x) b₀` at parameter `0`).  No invertibility of the slices is used. -/
private theorem autonomizedFlow_slice_contMDiff
    (Xt : ℝ → ∀ x : M, TangentSpace I x)
    (hXt_sm : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (Xt q.1 q.2) : TangentBundle I M)))
    (hXtC1 : AutonomizedFieldJointC1 (I := I) Xt)
    (ψ : (ℝ × M) → ℝ → (ℝ × M))
    (hψ0 : ∀ p : ℝ × M, ψ p 0 = p)
    (hψcurve : ∀ p : ℝ × M, IsMIntegralCurve (ψ p) (autonomizedFlowVF Xt))
    (hψtime : ∀ (p : ℝ × M) (u : ℝ), (ψ p u).1 = p.1 + u)
    (lo hi : ℝ) (σ : ℝ) (a : ℝ)
    (hseg : ∀ b ∈ Set.Ioo (min (0 : ℝ) a - 1) (max (0 : ℝ) a + 1),
      σ + b ∈ Set.Icc (lo - 3) (hi + 3)) :
    ContMDiff I (𝓘(ℝ, ℝ).prod I) ∞ (fun x : M => ψ (σ, x) a) := by
  classical
  obtain ⟨ε, hε_pos, hwin⟩ := autonomized_uniform_jointSmoothWindow Xt hXt_sm lo hi
  set ε' : ℝ := min ε 1 with hε'_def
  have hε'_pos : 0 < ε' := lt_min hε_pos one_pos
  have hε'_le_ε : ε' ≤ ε := min_le_left _ _
  intro x₀
  -- The local propagation step in the parameter `b`.
  have hstep : ∀ b₀ : ℝ, σ + b₀ ∈ Set.Icc (lo - 3) (hi + 3) →
      ContMDiffAt I (𝓘(ℝ, ℝ).prod I) ∞ (fun x : M => ψ (σ, x) b₀) x₀ →
      ∀ b : ℝ, |b - b₀| < ε' → ContMDiffAt I (𝓘(ℝ, ℝ).prod I) ∞ (fun x : M => ψ (σ, x) b) x₀ := by
    intro b₀ hb₀_slab hψb₀ b hbb₀
    have hb₀_slab' : (ψ (σ, x₀) b₀).1 ∈ Set.Icc (lo - 3) (hi + 3) := by
      rw [hψtime (σ, x₀) b₀]; exact hb₀_slab
    obtain ⟨U, hU_open, hpt_U, Ψw, hΨw0, hΨwsm, hΨwcurve⟩ := hwin (ψ (σ, x₀) b₀) hb₀_slab'
    have hτ_mem : (b - b₀) ∈ Set.Ioo (-ε) ε := by
      rw [Set.mem_Ioo, ← abs_lt]; exact lt_of_lt_of_le hbb₀ hε'_le_ε
    -- The candidate `g x = Ψw (ψ (σ, x) b₀) (b - b₀)`, smooth at `x₀`.
    set ι : M → ℝ × M := fun x => ψ (σ, x) b₀ with hι_def
    have hι_x₀ : ι x₀ = ψ (σ, x₀) b₀ := rfl
    have hslice : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
        (fun q : ℝ × M => Ψw q (b - b₀)) (ψ (σ, x₀) b₀) := by
      have hprepend : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod I)) ∞
          (fun q : ℝ × M => ((b - b₀, q) : ℝ × (ℝ × M))) (ψ (σ, x₀) b₀) :=
        contMDiffAt_const.prodMk contMDiffAt_id
      have hmem_prod : ((b - b₀, ψ (σ, x₀) b₀) : ℝ × (ℝ × M)) ∈ Set.Ioo (-ε) ε ×ˢ U :=
        ⟨hτ_mem, hpt_U⟩
      have hopen_prod : IsOpen (Set.Ioo (-ε) ε ×ˢ U) := isOpen_Ioo.prod hU_open
      have hΨwsm_at : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod I)) (𝓘(ℝ, ℝ).prod I) ∞
          (fun bb : ℝ × (ℝ × M) => Ψw bb.2 bb.1) (Set.Ioo (-ε) ε ×ˢ U)
          (b - b₀, ψ (σ, x₀) b₀) := hΨwsm _ hmem_prod
      have hΨwsm_contMDiffAt : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod I)) (𝓘(ℝ, ℝ).prod I) ∞
          (fun bb : ℝ × (ℝ × M) => Ψw bb.2 bb.1) (b - b₀, ψ (σ, x₀) b₀) :=
        hΨwsm_at.contMDiffAt (hopen_prod.mem_nhds hmem_prod)
      exact hΨwsm_contMDiffAt.comp (ψ (σ, x₀) b₀) hprepend
    have hg_smooth : ContMDiffAt I (𝓘(ℝ, ℝ).prod I) ∞
        (fun x : M => Ψw (ψ (σ, x) b₀) (b - b₀)) x₀ :=
      (hι_x₀ ▸ hslice).comp x₀ hψb₀
    -- Eventual agreement `g = (fun x => ψ (σ, x) b)` near `x₀`, by integral-curve uniqueness.
    have heq : (fun x : M => Ψw (ψ (σ, x) b₀) (b - b₀)) =ᶠ[nhds x₀] (fun x : M => ψ (σ, x) b) := by
      have hW : (fun x : M => ψ (σ, x) b₀) ⁻¹' U ∈ nhds x₀ := by
        have hcont : ContinuousAt (fun x : M => ψ (σ, x) b₀) x₀ := hψb₀.continuousAt
        exact hcont.preimage_mem_nhds (hU_open.mem_nhds hpt_U)
      filter_upwards [hW] with x hx
      have hqU : ψ (σ, x) b₀ ∈ U := hx
      have hΨwq : IsMIntegralCurveOn (fun u : ℝ => Ψw (ψ (σ, x) b₀) u)
          (autonomizedFlowVF Xt) (Set.Ioo (-ε) ε) := hΨwcurve (ψ (σ, x) b₀) hqU
      have hshift : IsMIntegralCurveOn (fun u : ℝ => ψ (σ, x) (u + b₀))
          (autonomizedFlowVF Xt) (Set.Ioo (-ε) ε) :=
        ((hψcurve (σ, x)).comp_add b₀).isMIntegralCurveOn (Set.Ioo (-ε) ε)
      have hstart : (fun u : ℝ => Ψw (ψ (σ, x) b₀) u) 0
          = (fun u : ℝ => ψ (σ, x) (u + b₀)) 0 := by
        simp only [hΨw0 (ψ (σ, x) b₀) hqU, zero_add]
      have h0mem : (0 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨by linarith, hε_pos⟩
      have hv : ContMDiff (𝓘(ℝ, ℝ).prod I) ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ × E)) 1
          (fun p : ℝ × M =>
            (⟨p, autonomizedFlowVF Xt p⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) :=
        fun p => hXtC1 p
      have heqOn := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
        h0mem hv hΨwq hshift hstart
      have hatτ := heqOn hτ_mem
      have hval : Ψw (ψ (σ, x) b₀) (b - b₀) = ψ (σ, x) (b - b₀ + b₀) := hatτ
      rw [hval]
      simp only [sub_add_cancel]
    exact hg_smooth.congr_of_eventuallyEq heq.symm
  -- Connectedness in `b` over the unordered interval `[[0, a]]`: the good set contains `a`.
  set W : Set ℝ := Set.Ioo (min (0 : ℝ) a - 1) (max (0 : ℝ) a + 1) with hW_def
  have hWopen : IsOpen W := isOpen_Ioo
  have huIcc_sub : Set.uIcc (0 : ℝ) a ⊆ W := by
    intro b hb
    rw [Set.mem_uIcc] at hb
    rw [hW_def, Set.mem_Ioo]
    have hmin : min (0 : ℝ) a ≤ b := by
      rw [min_le_iff]; rcases hb with hb | hb
      · exact Or.inl hb.1
      · exact Or.inr hb.1
    have hmax : b ≤ max (0 : ℝ) a := by
      rw [le_max_iff]; rcases hb with hb | hb
      · exact Or.inr hb.2
      · exact Or.inl hb.2
    exact ⟨by linarith, by linarith⟩
  set u : Set ℝ :=
    {b : ℝ | ContMDiffAt I (𝓘(ℝ, ℝ).prod I) ∞ (fun x : M => ψ (σ, x) b) x₀} ∩ W with hu_def
  have hu_open : IsOpen u := by
    rw [isOpen_iff_mem_nhds]
    rintro b ⟨hb_smooth, hb_int⟩
    have hb_slab : σ + b ∈ Set.Icc (lo - 3) (hi + 3) := hseg b hb_int
    have hball : Set.Ioo (b - ε') (b + ε') ∩ W ⊆ u := by
      rintro b' ⟨hb'_ball, hb'_int⟩
      refine ⟨?_, hb'_int⟩
      have hdist : |b' - b| < ε' := by
        rw [abs_lt]; constructor <;> [linarith [hb'_ball.1]; linarith [hb'_ball.2]]
      exact hstep b hb_slab hb_smooth b' hdist
    refine Filter.mem_of_superset (Filter.inter_mem ?_ ?_) hball
    · exact isOpen_Ioo.mem_nhds ⟨by linarith [hε'_pos], by linarith [hε'_pos]⟩
    · exact hWopen.mem_nhds hb_int
  -- The map at `b = 0` is `x ↦ (σ, x)`, smooth.
  have h0_smooth : ContMDiffAt I (𝓘(ℝ, ℝ).prod I) ∞ (fun x : M => ψ (σ, x) 0) x₀ := by
    have hcongr : (fun x : M => ψ (σ, x) 0) = (fun x : M => ((σ, x) : ℝ × M)) := by
      funext x; rw [hψ0 (σ, x)]
    rw [hcongr]; exact contMDiffAt_const.prodMk contMDiffAt_id
  have h0_u : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) a ∩ u :=
    ⟨Set.left_mem_uIcc, h0_smooth, huIcc_sub Set.left_mem_uIcc⟩
  have hclosed : closure u ∩ Set.uIcc (0 : ℝ) a ⊆ u := by
    rintro bstar ⟨hbstar_cl, hbstar_uIcc⟩
    have hbstar_W : bstar ∈ W := huIcc_sub hbstar_uIcc
    have hbstar_slab : σ + bstar ∈ Set.Icc (lo - 3) (hi + 3) := hseg bstar hbstar_W
    have hnhd : Set.Ioo (bstar - ε') (bstar + ε') ∩ W ∈ nhds bstar :=
      Filter.inter_mem
        (isOpen_Ioo.mem_nhds ⟨by linarith [hε'_pos], by linarith [hε'_pos]⟩)
        (hWopen.mem_nhds hbstar_W)
    obtain ⟨bn, ⟨hbn_ball, hbn_W⟩, hbn_smooth, _⟩ :=
      mem_closure_iff_nhds.mp hbstar_cl _ hnhd
    have hbn_slab : σ + bn ∈ Set.Icc (lo - 3) (hi + 3) := hseg bn hbn_W
    have hdist : |bstar - bn| < ε' := by
      rw [abs_lt]; constructor <;> [linarith [hbn_ball.2]; linarith [hbn_ball.1]]
    exact ⟨hstep bn hbn_slab hbn_smooth bstar hdist, hbstar_W⟩
  have hsub : Set.uIcc (0 : ℝ) a ⊆ u :=
    isPreconnected_uIcc.subset_of_closure_inter_subset hu_open ⟨0, h0_u⟩ hclosed
  exact (hsub Set.right_mem_uIcc).1

/-- **Full-interval flow with its reverse on a closed manifold.**

The reverse-flow strengthening of `global_flow_full_interval_on_closed_manifold`: for a globally
jointly-`C∞` field `X` on a closed manifold and any horizon `T > 0`, the full-interval flow `Φ`
(with `Φ 0 = id`, jointly `C∞` on `Ioo lo hi ⊇ [0, T]`, carrying the bare velocity `X t (Φ t x)`)
comes with a reverse flow `Ψ` that is smooth in each slice `Ψ t` (for `0 < t < hi`) and is the
two-sided inverse of `Φ` on `[0, hi)`: `Ψ s (Φ s x) = x` and `Φ s (Ψ s x) = x`.

The reverse is the genuine **group inverse** of the *autonomous* flow on `ℝ × M`, not the flow of
`-X` (which only inverts for autonomous fields).  The cut-off field `Xt` (as in the headline) has a
global integral-curve flow `ψ : (ℝ × M) → ℝ → (ℝ × M)` of the autonomised field
`autonomizedFlowVF Xt` (built from `exists_isMIntegralCurve_of_isMIntegralCurveOn` through *every*
point); `ψ` is a one-parameter group `ψ p (a + b) = ψ (ψ p a) b` (integral-curve uniqueness
`isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless`) whose time coordinate advances by the
parameter `(ψ p u).1 = p.1 + u`.  Setting `Φ s x := (ψ (0, x) s).2` (matching the headline flow,
since both lift to integral curves through `(0, x)`) and `Ψ s x := (ψ (s, x) (-s)).2`, the
mutual-inverse identities are the group law evaluated at `s + (-s) = 0` and `(-s) + s = 0`, after
identifying `ψ (0, x) s = (s, Φ s x)` and `ψ (s, x) (-s) = (0, Ψ s x)` via the time-coordinate.
Slice smoothness of `Ψ t` is `autonomizedFlow_slice_contMDiff` (the anchor-free companion of
`cutoffFlow_slice_contMDiff`) applied at start time `σ = t`, reverse time `a = -t`. -/
theorem global_flow_full_interval_with_reverse_on_closed_manifold
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hX : ContMDiff (𝓘(ℝ,ℝ).prod I) (I.prod 𝓘(ℝ,E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)))
    (T : ℝ) (hT : 0 < T) :
    ∃ (Φ Ψ : ℝ → M → M) (lo hi : ℝ), lo < 0 ∧ T < hi ∧ (∀ x, Φ 0 x = x) ∧
      ContMDiffOn (𝓘(ℝ,ℝ).prod I) I ∞ (fun q => Φ q.1 q.2) (Set.Ioo lo hi ×ˢ Set.univ) ∧
      (∀ t ∈ Set.Ioo lo hi, ∀ x, HasMFDerivAt 𝓘(ℝ,ℝ) I (fun s => Φ s x) t
        ((1:ℝ→L[ℝ]ℝ).smulRight (X t (Φ t x)))) ∧
      (∀ t, 0 < t → t < hi → ContMDiff I I ∞ (Ψ t)) ∧
      (∀ s ∈ Set.Ico (0:ℝ) hi, ∀ x, Ψ s (Φ s x) = x) ∧
      (∀ s ∈ Set.Ico (0:ℝ) hi, ∀ x, Φ s (Ψ s x) = x) := by
  classical
  set Xt : ℝ → ∀ x : M, TangentSpace I x :=
    fun s x => fullIntervalBump (-1) (T + 1) s • X s x with hXt_def
  have hXt_sm : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (Xt q.1 q.2) : TangentBundle I M)) :=
    cutoffField_contMDiff X hX (-1) (T + 1)
  have hXtC1 : AutonomizedFieldJointC1 (I := I) Xt :=
    autonomizedFieldJointC1_of_contMDiff Xt hXt_sm
  have hXt_eq : ∀ s ∈ Set.Icc (-1 : ℝ) (T + 1), ∀ x : M, Xt s x = X s x := by
    intro s hs x
    rw [hXt_def]
    simp only [fullIntervalBump_eq_one (-1) (T + 1) s hs, one_smul]
  have hvanish : ∀ s : ℝ, s ∉ Set.Icc (-1 - 2 : ℝ) (T + 1 + 2) → ∀ x : M, Xt s x = 0 := by
    intro s hs x
    rw [hXt_def]
    simp only [fullIntervalBump_eq_zero (-1) (T + 1) s hs, zero_smul]
  obtain ⟨ε, hε, huniform⟩ :=
    autonomized_uniform_localExistence Xt hXt_sm (-1) (T + 1) hvanish
  have hv : ContMDiff (𝓘(ℝ, ℝ).prod I) ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ × E)) 1
      (fun p : ℝ × M =>
        (⟨p, autonomizedFlowVF Xt p⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) :=
    fun p => hXtC1 p
  -- The global autonomous flow `ψ` on `ℝ × M`.
  choose ψ hψ0 hψcurve using fun p : ℝ × M =>
    exists_isMIntegralCurve_of_isMIntegralCurveOn (v := autonomizedFlowVF Xt) hv hε huniform p
  -- The time coordinate advances by the parameter.
  have hψtime : ∀ (p : ℝ × M) (u : ℝ), (ψ p u).1 = p.1 + u := by
    intro p
    have hderiv : ∀ s, HasDerivAt (fun w => (ψ p w).1) (1 : ℝ) s :=
      fun s => autonomizedFlow_fst_hasDerivAt Xt (ψ p) s (hψcurve p s)
    have hconst : ∀ w : ℝ, HasDerivAt (fun w => (ψ p w).1 - w) (0 : ℝ) w :=
      fun w => by simpa using (hderiv w).sub (hasDerivAt_id w)
    intro u
    have hkey : (fun w => (ψ p w).1 - w) u = (fun w => (ψ p w).1 - w) 0 :=
      is_const_of_deriv_eq_zero (fun w => (hconst w).differentiableAt)
        (fun w => (hconst w).deriv) u 0
    simp only at hkey
    rw [hψ0 p] at hkey
    simp only [sub_zero] at hkey
    linarith [hkey]
  -- One-parameter group law, via global integral-curve uniqueness.
  have hgroup : ∀ (p : ℝ × M) (a b : ℝ), ψ p (a + b) = ψ (ψ p a) b := by
    intro p a b
    have hcurve1 : IsMIntegralCurve (ψ p ∘ (· + a)) (autonomizedFlowVF Xt) :=
      (hψcurve p).comp_add a
    have hstart : (ψ p ∘ (· + a)) 0 = ψ (ψ p a) 0 := by
      simp only [Function.comp_apply, zero_add, hψ0 (ψ p a)]
    have heq : (ψ p ∘ (· + a)) = ψ (ψ p a) :=
      isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0) hv hcurve1 (hψcurve (ψ p a)) hstart
    have hb := congrFun heq b
    simp only [Function.comp_apply] at hb
    rw [add_comm a b]
    exact hb
  -- The forward flow `Φ` and the reverse flow `Ψ`.
  set Φ : ℝ → M → M := fun s x => (ψ (0, x) s).2 with hΦ_def
  set Ψ : ℝ → M → M := fun s x => (ψ (s, x) (-s)).2 with hΨ_def
  have hΦ0 : ∀ x : M, Φ 0 x = x := by
    intro x; simp only [hΦ_def, hψ0 (0, x)]
  -- `ψ (0, x) s = (s, Φ s x)`.
  have hψ0x : ∀ (s : ℝ) (x : M), ψ (0, x) s = (s, Φ s x) := by
    intro s x
    apply Prod.ext
    · rw [hψtime (0, x) s]; simp
    · rfl
  -- Bare velocity at every time.
  have hΦbare : ∀ t : ℝ, ∀ x : M, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ s x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Xt t (Φ t x))) := by
    intro t x
    have hsnd := autonomizedFlow_snd_hasMFDerivAt Xt (ψ (0, x)) t (hψcurve (0, x) t)
    have ht1 : (ψ (0, x) t).1 = t := by rw [hψtime (0, x) t]; simp
    rw [ht1] at hsnd
    exact hsnd
  refine ⟨Φ, Ψ, -1, T + 1, by norm_num, by linarith, hΦ0, ?_, ?_, ?_, ?_, ?_⟩
  · -- Joint smoothness of `Φ`.
    exact cutoffFlow_jointContMDiffOn Xt hXt_sm hXtC1 Φ hΦ0 hΦbare (-1) (T + 1)
      (by norm_num) (by linarith)
  · -- Bare velocity of `Φ` against the genuine field `X` on `Ioo (-1) (T+1)`.
    intro t ht x
    have htIcc : t ∈ Set.Icc (-1 : ℝ) (T + 1) := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hb := hΦbare t x
    rw [hXt_eq t htIcc (Φ t x)] at hb
    exact hb
  · -- Slice smoothness of the reverse flow `Ψ t`, for `0 < t < T + 1`.
    intro t ht0 hthi
    have hseg : ∀ b ∈ Set.Ioo (min (0 : ℝ) (-t) - 1) (max (0 : ℝ) (-t) + 1),
        t + b ∈ Set.Icc ((-1 : ℝ) - 3) ((T + 1) + 3) := by
      have hmin : min (0 : ℝ) (-t) = -t := min_eq_right (by linarith)
      have hmax : max (0 : ℝ) (-t) = 0 := max_eq_left (by linarith)
      rw [hmin, hmax]
      intro b hb
      rw [Set.mem_Ioo] at hb
      rw [Set.mem_Icc]
      exact ⟨by linarith [hb.1], by linarith [hb.2]⟩
    have hslice := autonomizedFlow_slice_contMDiff Xt hXt_sm hXtC1 ψ hψ0 hψcurve hψtime
      (-1) (T + 1) t (-t) hseg
    have hΨeq : Ψ t = (fun x : M => (ψ (t, x) (-t)).2) := by
      funext x; rw [hΨ_def]
    rw [hΨeq]
    exact contMDiff_snd.comp hslice
  · -- `Ψ s (Φ s x) = x` on `Ico 0 (T + 1)`.
    intro s _ x
    have hstep1 : Ψ s (Φ s x) = (ψ (ψ (0, x) s) (-s)).2 := by
      rw [hΨ_def]; rw [hψ0x s x]
    rw [hstep1, ← hgroup (0, x) s (-s)]
    simp only [add_neg_cancel, hψ0 (0, x)]
  · -- `Φ s (Ψ s x) = x` on `Ico 0 (T + 1)`.
    intro s _ x
    have hψsx : ψ (s, x) (-s) = (0, Ψ s x) := by
      apply Prod.ext
      · rw [hψtime (s, x) (-s)]; simp
      · rfl
    have hstep1 : Φ s (Ψ s x) = (ψ (ψ (s, x) (-s)) s).2 := by
      rw [hΦ_def]; rw [hψsx]
    rw [hstep1, ← hgroup (s, x) (-s) s]
    simp only [neg_add_cancel, hψ0 (s, x)]

end DifferentialGeometry.PDE.RicciFlow.ODE
