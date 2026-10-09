import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA4

/-!
# Power decay for a nonnegative heat subsolution along a positively curved surface flow

Chapter 7, packet P8, surface lemma U1, route (a), step a5.2 (potential gauge, design D18 (ii′)).
Along a Ricci flow `S` on `[0, T)` with `T ≤ T*`, let `u ≥ 0` be jointly smooth on `(0, T) × M` with
`∂ₜ u ≤ Δ u + (2 / (T* - t) - 2 R) u`, and suppose `R · 2 (T* - t) ≥ c`. Then
`surfaceFlow_le_rpow_of_heat_subsolution`: for every `t₀ ∈ (0, T)` there is `C` with
`(T* - t)² u(t, x) ≤ C (T* - t)^c` on `[t₀, T)`.

On `[t₀, t]` the potential satisfies `(2 / (T* - s) - 2 R) u ≤ ((2 - c) / (T* - s)) u`, and the
barrier `K (T* - s)^(c - 2)` solves the linear ODE `b' = ((2 - c) / (T* - s)) b`; the weak maximum
principle with ODE comparison (`scalar_weak_maximum_principle_ode_compare_subsolution_of_heat_pot`)
on the shifted interval `[0, t - t₀]` gives `u ≤ b`. Applied to `u = |M|²` for the traceless
Hessian `M` of the potential, this is the decay `|M|_ĝ ≤ C e^{-c s}` of review 17 §5.2.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.PDE.RicciFlow
open Filter Topology Set
open scoped Manifold ContDiff

namespace GC.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M]
  {T : ℝ} {hT : 0 < T}

theorem rpowBarrier_hasDerivAt {Tst p K s : ℝ} (hs : s < Tst) :
    HasDerivAt (fun r : ℝ => K * (Tst - r) ^ p)
      ((-p) / (Tst - s) * (K * (Tst - s) ^ p)) s := by
  have hpos : 0 < Tst - s := sub_pos.mpr hs
  have hd : HasDerivAt (fun r : ℝ => Tst - r) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub Tst
  have h := (hd.rpow_const (p := p) (Or.inl hpos.ne')).const_mul K
  convert h using 1
  rw [Real.rpow_sub_one hpos.ne']
  field_simp

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [CompactSpace M] in
theorem contMDiff_slice_of_contMDiffOn {u : ℝ → M → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => u q.1 q.2) (U ×ˢ univ))
    {t : ℝ} (ht : t ∈ U) : ContMDiff I 𝓘(ℝ, ℝ) ∞ (u t) := by
  intro x
  have hat : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => u q.1 q.2) (t, x) :=
    hu.contMDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨ht, mem_univ x⟩)
  have hpair : ContMDiffAt I (𝓘(ℝ, ℝ).prod I) ∞ (fun y : M => (t, y)) x :=
    contMDiffAt_const.prodMk contMDiffAt_id
  exact hat.comp x hpair

omit [T2Space M] in
theorem surfaceFlow_le_rpow_of_heat_subsolution [Nonempty M]
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    {Tst c : ℝ} (hTT : T ≤ Tst) (u : ℝ → M → ℝ)
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => u q.1 q.2) (Ioo 0 T ×ˢ univ))
    (hnonneg : ∀ t ∈ Ioo 0 T, ∀ x, 0 ≤ u t x)
    (hevol : ∀ t ∈ Ioo 0 T, ∀ x, ∃ d : ℝ, HasDerivAt (fun s => u s x) d t ∧
      d ≤ laplacianAt (flowG S) t (u t) x + (2 / (Tst - t) - 2 * S.scalar t x) * u t x)
    (hlow : ∀ t ∈ Ioo 0 T, ∀ x, c ≤ S.scalar t x * (2 * (Tst - t)))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 T) :
    ∃ C : ℝ, ∀ t ∈ Ico t₀ T, ∀ x, (Tst - t) ^ 2 * u t x ≤ C * (Tst - t) ^ c := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hslice : ∀ t ∈ Ioo 0 T, ContMDiff I 𝓘(ℝ, ℝ) ∞ (u t) := fun t ht =>
    contMDiff_slice_of_contMDiffOn isOpen_Ioo hu ht
  obtain ⟨xm, -, hxm⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty (α := M))
    (hslice t₀ ht₀).continuous.continuousOn
  set K₀ := max (u t₀ xm) 0 with hK₀
  have hK₀nn : 0 ≤ K₀ := le_max_right _ _
  have hu₀ : ∀ x, u t₀ x ≤ K₀ := fun x => (hxm (mem_univ x)).trans (le_max_left _ _)
  have hgap₀ : 0 < Tst - t₀ := by linarith [ht₀.2]
  set K₁ := K₀ * (Tst - t₀) ^ (2 - c) with hK₁
  refine ⟨K₁, fun t ht x => ?_⟩
  have hgap : 0 < Tst - t := by linarith [ht.2]
  let V : ℝ → M → ℝ := fun s y => 2 / (Tst - s) - 2 * S.scalar s y
  suffices hmain : u t x ≤ K₁ * (Tst - t) ^ (c - 2) by
    have hsq : (Tst - t) ^ 2 * (Tst - t) ^ (c - 2) = (Tst - t) ^ c := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hgap]
      norm_num
    calc (Tst - t) ^ 2 * u t x ≤ (Tst - t) ^ 2 * (K₁ * (Tst - t) ^ (c - 2)) :=
          mul_le_mul_of_nonneg_left hmain (by positivity)
      _ = K₁ * (Tst - t) ^ c := by rw [← hsq]; ring
  rcases ht.1.eq_or_lt with h0 | htt
  · rw [← h0, hK₁, mul_assoc, ← Real.rpow_add hgap₀]
    norm_num
    exact hu₀ x
  have hsub : IsHeatPotSubsolutionOn (RealTimeInterval.closed t₀ t htt.le) (flowG S) V u :=
    { jointSmooth := hu.mono (prod_mono (fun s hs =>
        (⟨ht₀.1.trans hs.1, hs.2.trans ht.2⟩ : s ∈ Ioo 0 T)) le_rfl)
      jointCont := hu.continuousOn.mono (prod_mono (fun s hs =>
        (⟨ht₀.1.trans_le hs.1, hs.2.trans_lt ht.2⟩ : s ∈ Ioo 0 T)) le_rfl)
      sliceSmooth := fun s hs => hslice s ⟨ht₀.1.trans_le hs.1, hs.2.trans_lt ht.2⟩
      timeDiff := fun s hs y => by
        obtain ⟨d, hd, -⟩ := hevol s ⟨ht₀.1.trans hs.1, hs.2.trans ht.2⟩ y
        exact hd.differentiableAt
      equation_le := fun s hs y => by
        obtain ⟨d, hd, hle⟩ := hevol s ⟨ht₀.1.trans hs.1, hs.2.trans ht.2⟩ y
        rw [hd.deriv]
        exact hle }
  have hT' : (0 : ℝ) ≤ t - t₀ := sub_nonneg.mpr htt.le
  have hsh := isHeatPotSubsolutionOn_timeShift_flowG
    (Dsub' := RealTimeInterval.closed 0 (t - t₀) hT') S V u t₀ hsub
    (fun s hs => (⟨by linarith [hs.1], by linarith [hs.2]⟩ : s + t₀ ∈ Icc t₀ t))
    (fun s hs => (⟨by linarith [hs.1], by linarith [hs.2]⟩ : s + t₀ ∈ Ioo t₀ t))
  let b : ℝ → ℝ := fun s => K₁ * (Tst - t₀ - s) ^ (c - 2)
  let F : ℝ → ℝ → ℝ := fun β s => (2 - c) / (Tst - t₀ - s) * β
  have hden : ∀ s ∈ Icc 0 (t - t₀), Tst - t ≤ Tst - t₀ - s := fun s hs => by linarith [hs.2]
  have hb_deriv : ∀ s ∈ Icc 0 (t - t₀), HasDerivAt b (F (b s) s) s := by
    intro s hs
    have hlt : s < Tst - t₀ := by linarith [hden s hs]
    have h := rpowBarrier_hasDerivAt (Tst := Tst - t₀) (p := c - 2) (K := K₁) hlt
    convert h using 1
    simp only [F, b]
    ring
  set L : NNReal := Real.toNNReal (|2 - c| / (Tst - t)) with hL
  have hcmp := scalar_weak_maximum_principle_ode_compare_subsolution_of_heat_pot
    (flowG (S.timeShift t₀)) (t - t₀) hT' (fun s y => u (s + t₀) y) b F L
    (fun s y => V (s + t₀) y) hsh
    (fun s hs => (hb_deriv s hs).continuousAt.continuousWithinAt)
    (fun s hs _ => (hb_deriv s hs).differentiableAt.differentiableWithinAt)
    (fun s hs y => by
      have hτ : s + t₀ ∈ Ioo 0 T := ⟨by linarith [hs.1, ht₀.1], by linarith [hs.2, ht.2]⟩
      have hpos : 0 < Tst - t₀ - s := by linarith [hden s hs]
      have hR := hlow (s + t₀) hτ y
      have hu0 := hnonneg (s + t₀) hτ y
      simp only [V, F]
      have heq : Tst - (s + t₀) = Tst - t₀ - s := by ring
      rw [heq] at hR ⊢
      have h2R : c / (Tst - t₀ - s) ≤ 2 * S.scalar (s + t₀) y := by
        rw [div_le_iff₀ hpos]
        linarith
      have : 2 / (Tst - t₀ - s) - 2 * S.scalar (s + t₀) y ≤ (2 - c) / (Tst - t₀ - s) := by
        rw [sub_div]
        linarith
      exact mul_le_mul_of_nonneg_right this hu0)
    (fun s hs hs0 => (hb_deriv s hs).hasDerivWithinAt.derivWithin
      ((uniqueDiffOn_Icc (lt_of_lt_of_le hs0 hs.2)) s hs))
    (fun y => by
      change u (0 + t₀) y ≤ K₁ * (Tst - t₀ - 0) ^ (c - 2)
      rw [zero_add, sub_zero, hK₁, mul_assoc, ← Real.rpow_add hgap₀]
      norm_num
      exact hu₀ y)
    (fun s hs => by
      rw [lipschitzOnWith_iff_dist_le_mul]
      intro β _ β' _
      have hpos : 0 < Tst - t₀ - s := by linarith [hden s hs]
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
      simp only [F]
      rw [← mul_sub, abs_mul, abs_div, abs_of_pos hpos]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      exact div_le_div_of_nonneg_left (abs_nonneg _) hgap (hden s hs))
  have h := hcmp (t - t₀) ⟨hT', le_rfl⟩ x
  change u (t - t₀ + t₀) x ≤ K₁ * (Tst - t₀ - (t - t₀)) ^ (c - 2) at h
  rwa [sub_add_cancel, show Tst - t₀ - (t - t₀) = Tst - t by ring] at h

end GC.Geometry
