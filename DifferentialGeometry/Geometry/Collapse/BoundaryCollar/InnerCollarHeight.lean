import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarHeightTransversal
import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.InnerCollarProduct
import DifferentialGeometry.Topology.Manifold.Boundary.DefiningFunction

/-!
# Analytic data for the inner collar (F-e, row E6(i): inputs)

* `mfderiv_cutoffBlend_pos`: the blend `h + φ(ρ) (ρ - c - h)` increases along `v` when `h` and `ρ`
  do, `φ` is a nonincreasing cutoff with values in `[0, 1]` and `ρ - c - h ≤ 0`.
* `CompactCarrier.exists_boundary_definingFunction`: a carrier with a boundary point carries a
  smooth `ρ ≥ 0` vanishing exactly on `∂W` and a smooth field `V`, inward at `∂W`, with `dρ(V) = 1`
  on an open neighbourhood of `∂W` (`exists_global_boundary_definingFunction` on the half-space
  model).
* `CuspEmbedding.exists_collar_subset`: an open set containing `X` contains a uniform collar
  `e (z ≤ s₀)`.
* `exists_sqrt_inner_le_of_contMDiff`: a smooth field on a compact manifold has bounded length.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Geometry.Collapse

universe u

section Blend

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- The blend `h + φ(ρ) (ρ - c - h)` increases along `v` when `h` and `ρ` do, `φ` is a
nonincreasing cutoff with values in `[0, 1]` and `ρ - c - h ≤ 0`. -/
theorem mfderiv_cutoffBlend_pos {h ρ : M → ℝ} {φ : ℝ → ℝ} {c : ℝ} {y : M}
    {v : TangentSpace I y}
    (hh : MDifferentiableAt I 𝓘(ℝ, ℝ) h y) (hρ : MDifferentiableAt I 𝓘(ℝ, ℝ) ρ y)
    (hφ : DifferentiableAt ℝ φ (ρ y)) (hφ0 : 0 ≤ φ (ρ y)) (hφ1 : φ (ρ y) ≤ 1)
    (hφ' : deriv φ (ρ y) ≤ 0) (hD : ρ y - c - h y ≤ 0)
    (hhv : 0 < (show ℝ from mfderiv I 𝓘(ℝ, ℝ) h y v))
    (hρv : 0 < (show ℝ from mfderiv I 𝓘(ℝ, ℝ) ρ y v)) :
    0 < (show ℝ from
      mfderiv I 𝓘(ℝ, ℝ) (fun y => h y + φ (ρ y) * (ρ y - c - h y)) y v) := by
  set Lh : E →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) h y with hLh
  set Lρ : E →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) ρ y with hLρ
  have hh' : HasMFDerivAt I 𝓘(ℝ, ℝ) h y Lh := hh.hasMFDerivAt
  have hρ' : HasMFDerivAt I 𝓘(ℝ, ℝ) ρ y Lρ := hρ.hasMFDerivAt
  have hcst : ∀ k : ℝ, HasMFDerivAt I 𝓘(ℝ, ℝ) (fun _ : M => k) y (0 : E →L[ℝ] ℝ) :=
    fun k => hasMFDerivAt_const k y
  set Lφ : E →L[ℝ] ℝ :=
    (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv φ (ρ y))).comp Lρ with hLφ
  have hφρ : HasMFDerivAt I 𝓘(ℝ, ℝ) (fun y => φ (ρ y)) y Lφ :=
    hφ.hasDerivAt.hasFDerivAt.hasMFDerivAt.comp y hρ'
  have hD' : HasMFDerivAt I 𝓘(ℝ, ℝ) (fun y => ρ y - c - h y) y ((Lρ - 0 - Lh : E →L[ℝ] ℝ)) :=
    (hρ'.sub (hcst c)).sub hh'
  have hall : HasMFDerivAt I 𝓘(ℝ, ℝ) (fun y => h y + φ (ρ y) * (ρ y - c - h y)) y
      ((Lh + (φ (ρ y) • (Lρ - 0 - Lh) + (ρ y - c - h y) • Lφ) : E →L[ℝ] ℝ)) :=
    hh'.add (hφρ.mul hD')
  change 0 < (show ℝ from mfderiv I 𝓘(ℝ, ℝ)
    (fun y => h y + φ (ρ y) * (ρ y - c - h y)) y v)
  rw [hall.mfderiv]
  change 0 < Lh v at hhv
  change 0 < Lρ v at hρv
  have hval : ∀ w : E,
      ((Lh + (φ (ρ y) • (Lρ - 0 - Lh) + (ρ y - c - h y) • Lφ)) : E →L[ℝ] ℝ) w =
      Lh w + (φ (ρ y) * (Lρ w - Lh w) + (ρ y - c - h y) * (deriv φ (ρ y) * Lρ w)) := by
    intro w
    simp only [sub_zero, hLφ, FunLike.coe_add, FunLike.coe_smul, FunLike.coe_sub,
      Pi.add_apply, Pi.smul_apply, Pi.sub_apply, ContinuousLinearMap.coe_comp, comp_apply,
      ContinuousLinearMap.smulRight_apply, smul_eq_mul, one_apply_eq_self]
    ring
  change 0 < ((Lh + (φ (ρ y) • (Lρ - 0 - Lh) + (ρ y - c - h y) • Lφ)) : E →L[ℝ] ℝ) v
  rw [hval v]
  have hcross : 0 ≤ (ρ y - c - h y) * (deriv φ (ρ y) * Lρ v) :=
    mul_nonneg_of_nonpos_of_nonpos hD (mul_nonpos_of_nonpos_of_nonneg hφ' hρv.le)
  set m : ℝ := min (Lh v) (Lρ v) with hm
  have hm0 : 0 < m := lt_min hhv hρv
  have hm1 : m ≤ Lh v := min_le_left _ _
  have hm2 : m ≤ Lρ v := min_le_right _ _
  nlinarith [mul_nonneg (sub_nonneg.mpr hφ1) (sub_nonneg.mpr hm1),
    mul_nonneg hφ0 (sub_nonneg.mpr hm2)]

end Blend

/-- A carrier with a boundary point carries a smooth boundary defining function `ρ` and a smooth
field `V`, inward at `∂W`, with `dρ(V) = 1` on an open neighbourhood `O` of `∂W`. -/
theorem CompactCarrier.exists_boundary_definingFunction (W : CompactCarrier.{u})
    (hb : ∃ y : W.Carrier, W.model.IsBoundaryPoint y) :
    ∃ (ρ : W.Carrier → ℝ) (O : Set W.Carrier), IsOpen O ∧ ContMDiff W.model 𝓘(ℝ, ℝ) ∞ ρ ∧
      (∀ x, 0 ≤ ρ x) ∧ (∀ x, ρ x = 0 ↔ W.model.IsBoundaryPoint x) ∧
      (∀ x, W.model.IsBoundaryPoint x → x ∈ O) ∧
      ∃ V : (y : W.Carrier) → TangentSpace W.model y,
        ContMDiff W.model W.model.tangent ∞
          (fun y => (⟨y, V y⟩ : TangentBundle W.model W.Carrier)) ∧
        (∀ y ∈ O, mfderiv W.model 𝓘(ℝ, ℝ) ρ y (V y) = (1 : ℝ)) ∧
        ∀ y, W.model.IsBoundaryPoint y → 0 < (show EuclideanSpace ℝ (Fin 3) from V y) 0 := by
  cases W with
  | mk k M orientation =>
    cases k with
    | closed =>
      exfalso
      obtain ⟨(y : M), hy⟩ := hb
      have hh := ModelWithCorners.Boundaryless.boundary_eq_empty (I := 𝓡 3) (M := M)
      have hy' : y ∈ (𝓡 3).boundary M := hy
      rw [hh] at hy'
      exact hy'
    | withBoundary =>
      have hB : IsCompact ((𝓡∂ 3).boundary M) :=
        ((𝓡∂ 3).isClosed_boundary (n := ∞) (by simp)).isCompact
      obtain ⟨r, O, hr, hrn, hr0, -, hBO, V, hV, -, hunit, hpos⟩ :=
        DifferentialGeometry.Manifold.Boundary.exists_global_boundary_definingFunction hB
      exact ⟨r, O, O.isOpen, hr, hrn, hr0, fun x hx => hBO hx, V, hV, hunit,
        fun y hy => hpos ⟨y, hy⟩⟩

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
  {X : Set W.Carrier}

/-- **A uniform collar inside an open neighbourhood of `X`.** -/
theorem CuspEmbedding.exists_collar_subset (e : CuspEmbedding W g K δ X) {O : Set W.Carrier}
    (hO : IsOpen O) (hXO : X ⊆ O) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 ∧ ∀ p : CuspHalfSpace, p.2.val 0 ≤ s₀ → e.toFun p ∈ O := by
  set φ : Torus × ℝ → W.Carrier := fun q => e.toFun (q.1, halfSpaceOneLift q.2) with hφdef
  set D₀ : Set (Torus × ℝ) := univ ×ˢ Icc (0 : ℝ) 1 with hD₀
  have hD₀c : IsCompact D₀ := isCompact_univ.prod isCompact_Icc
  have hmem : ∀ q ∈ D₀, ((q.1, halfSpaceOneLift q.2) : CuspHalfSpace) ∈ cuspDomain := by
    intro q hq
    change (halfSpaceOneLift q.2).1 0 < cuspDepth
    rw [halfSpaceOneLift_val_zero, max_eq_left hq.2.1]
    exact hq.2.2.trans_lt (by norm_num [cuspDepth])
  have hφc : ContinuousOn φ D₀ :=
    e.contMDiffOn.continuousOn.comp
      (contMDiffOn_cuspVertical.continuousOn.mono (prod_mono subset_rfl fun s hs => hs.1))
      hmem
  have hlift0 : halfSpaceOneLift 0 = halfZero := by
    apply Subtype.ext
    ext i
    fin_cases i
    simp [halfSpaceOneLift_val_zero, halfZero, halfPoint]
  have hφ0 : ∀ x : Torus, φ (x, 0) ∈ O := by
    intro x
    change e.toFun (x, halfSpaceOneLift 0) ∈ O
    rw [hlift0]
    exact hXO ((Set.ext_iff.mp e.boundary_image _).mp ⟨x, rfl⟩)
  set Kbad : Set (Torus × ℝ) := D₀ ∩ φ ⁻¹' Oᶜ with hKbad
  have hKc : IsCompact Kbad := hD₀c.of_isClosed_subset
    (hφc.preimage_isClosed_of_isClosed hD₀c.isClosed hO.isClosed_compl) inter_subset_left
  have hfinal : ∀ s₀ : ℝ, s₀ ≤ 1 → (∀ q ∈ Kbad, s₀ < q.2) →
      ∀ p : CuspHalfSpace, p.2.val 0 ≤ s₀ → e.toFun p ∈ O := by
    intro s₀ hs₀ hK p hp
    by_contra hpO
    have hq : (p.1, p.2.val 0) ∈ Kbad := by
      refine ⟨⟨mem_univ _, p.2.2, hp.trans hs₀⟩, ?_⟩
      change e.toFun (p.1, halfSpaceOneLift (p.2.val 0)) ∈ Oᶜ
      rw [halfSpaceOneLift_val_zero_self]
      exact hpO
    exact absurd (hK _ hq) (not_lt.mpr hp)
  rcases Kbad.eq_empty_or_nonempty with hE | hNE
  · refine ⟨1, one_pos, le_rfl, hfinal 1 le_rfl fun q hq => ?_⟩
    rw [hE] at hq
    exact hq.elim
  · obtain ⟨q₀, hq₀, hmin⟩ := hKc.exists_isMinOn hNE continuous_snd.continuousOn
    have hq₀pos : 0 < q₀.2 := by
      rcases hq₀.1.2.1.lt_or_eq with h | h
      · exact h
      · exfalso
        have hq₀eq : q₀ = (q₀.1, 0) := Prod.ext rfl h.symm
        have h2 := hq₀.2
        rw [hq₀eq] at h2
        exact h2 (hφ0 q₀.1)
    refine ⟨min (q₀.2 / 2) 1, lt_min (half_pos hq₀pos) one_pos, min_le_right _ _,
      hfinal _ (min_le_right _ _) fun q hq => ?_⟩
    have h1 : q₀.2 ≤ q.2 := hmin hq
    have h2 : min (q₀.2 / 2) 1 ≤ q₀.2 / 2 := min_le_left _ _
    linarith

/-- A smooth vector field on a compact manifold has bounded length. -/
theorem exists_sqrt_inner_le_of_contMDiff {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M] (g : SmoothRiemannianMetric I M)
    {V : (y : M) → TangentSpace I y}
    (hV : ContMDiff I I.tangent ∞ (fun y => (⟨y, V y⟩ : TangentBundle I M))) :
    ∃ C : ℝ, ∀ y, Real.sqrt (g.inner y (V y) (V y)) ≤ C := by
  have happ : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun m : M => (⟨m, g.inner m (V m) (V m)⟩ : TotalSpace ℝ (Bundle.Trivial M ℝ))) :=
    ContMDiff.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ) (b := id) g.contMDiff hV hV
  have hc : Continuous fun m : M => g.inner m (V m) (V m) := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    have hpx := happ x
    rw [Bundle.contMDiffAt_totalSpace] at hpx
    exact hpx.2.continuousAt
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (Real.continuous_sqrt.comp hc).continuousOn
  exact ⟨C, fun y => (le_abs_self _).trans ((Real.norm_eq_abs _).symm.trans_le
    (hC y (mem_univ y)))⟩

end DifferentialGeometry.Geometry.Collapse
