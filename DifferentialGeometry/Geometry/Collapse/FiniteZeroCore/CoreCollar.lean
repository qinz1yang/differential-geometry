import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.CoreBoundary
import DifferentialGeometry.Geometry.Collapse.SublevelCore.OpenDiskBundle

/-!
# The radial collar of a closed core (item (5) of review 43's checklist)

A closed source core `A` that an ambient partial diffeomorphism `Ψ` carries onto a disc core
`D_T = {‖(D⁻¹ x).2‖ ≤ T}` of a carrier `D : TotalSpace F V ≃ N` has the radial collar
`κ (t, z) = Ψ⁻¹ (D ⟨z.proj, t z.2⟩)`:

* `κ` is smooth on the open set where it is defined (`contMDiff_totalSpace_smul`);
* on `(0, T] × S(V)` (`S(V)` the unit sphere bundle) it is injective, lands in `A`, and it reaches
  every point of `A` off the soul `Ψ⁻¹ D(0-section)`;
* `κ (t, z)` lies on the boundary `frontier A` exactly when `t = T`.

`(T/2, T] × S(V)` is therefore a collar of `∂A` in `A` (`core_radial_collar`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Bundle Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

variable {EB F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]

/-- **The radial collar of a closed core.** If `Ψ : M ⇀ N` carries `A ⊆ dom Ψ` onto the disc core
`D_T` of `D : TotalSpace F V ≃ N` (with its frontier the top level), then `κ (t, z) = Ψ⁻¹ (D ⟨z.proj, t z.2⟩)` is smooth where
defined, maps `(0, T] × S(V)` injectively into `A` and onto `A` minus the soul, and `κ (t, z) ∈ ∂A`
iff `t = T`. -/
theorem core_radial_collar (D : Diffeomorph (IB.prod 𝓘(ℝ, F)) I (TotalSpace F V) N ∞)
    (Ψ : PartialDiffeomorph I I M N ∞) {A : Set M} {T : ℝ} (hAs : A ⊆ Ψ.source)
    (hΨA : Ψ '' A = {x | ‖(D.symm x).2‖ ≤ T}) (hAc : IsClosed A)
    (hcl : IsClosed {x : N | ‖(D.symm x).2‖ ≤ T})
    (hfr : frontier {x : N | ‖(D.symm x).2‖ ≤ T} = {x : N | ‖(D.symm x).2‖ = T}) :
    let κ : ℝ × TotalSpace F V → M := fun p => Ψ.symm (D ⟨p.2.proj, p.1 • p.2.2⟩)
    ContMDiffOn (𝓘(ℝ, ℝ).prod (IB.prod 𝓘(ℝ, F))) I ∞ κ
        {p | D ⟨p.2.proj, p.1 • p.2.2⟩ ∈ Ψ.target} ∧
      (∀ t ∈ Ioc (0 : ℝ) T, ∀ z : TotalSpace F V, ‖z.2‖ = 1 → κ (t, z) ∈ A) ∧
      (∀ t₁ ∈ Ioc (0 : ℝ) T, ∀ t₂ ∈ Ioc (0 : ℝ) T, ∀ z₁ z₂ : TotalSpace F V, ‖z₁.2‖ = 1 →
        ‖z₂.2‖ = 1 → κ (t₁, z₁) = κ (t₂, z₂) → t₁ = t₂ ∧ z₁ = z₂) ∧
      (∀ x ∈ A, (D.symm (Ψ x)).2 ≠ 0 → ∃ t ∈ Ioc (0 : ℝ) T, ∃ z : TotalSpace F V,
        ‖z.2‖ = 1 ∧ κ (t, z) = x) ∧
      (∀ t ∈ Ioc (0 : ℝ) T, ∀ z : TotalSpace F V, ‖z.2‖ = 1 → (κ (t, z) ∈ frontier A ↔ t = T)) := by
  intro κ
  -- the radial value of `κ`
  have hrad : ∀ (t : ℝ) (z : TotalSpace F V), 0 ≤ t → ‖z.2‖ = 1 →
      ‖(D.symm (D ⟨z.proj, t • z.2⟩)).2‖ = t := by
    intro t z ht hz
    rw [D.symm_apply_apply]
    change ‖t • z.2‖ = t
    rw [norm_smul, hz, mul_one, Real.norm_eq_abs, abs_of_nonneg ht]
  have hcore : ∀ t ∈ Ioc (0 : ℝ) T, ∀ z : TotalSpace F V, ‖z.2‖ = 1 →
      D ⟨z.proj, t • z.2⟩ ∈ Ψ '' A := by
    intro t ht z hz
    rw [hΨA]
    change ‖(D.symm (D ⟨z.proj, t • z.2⟩)).2‖ ≤ T
    rw [hrad t z ht.1.le hz]
    exact ht.2
  have hmemA : ∀ y ∈ Ψ '' A, Ψ.symm y ∈ A := by
    rintro _ ⟨x, hx, rfl⟩
    change Ψ.toPartialEquiv.symm (Ψ.toPartialEquiv x) ∈ A
    rw [Ψ.toPartialEquiv.left_inv (hAs hx)]
    exact hx
  have hAimg : ∀ t ∈ Ioc (0 : ℝ) T, ∀ z : TotalSpace F V, ‖z.2‖ = 1 → κ (t, z) ∈ A :=
    fun t ht z hz => hmemA _ (hcore t ht z hz)
  have htgt : ∀ y ∈ Ψ '' A, y ∈ Ψ.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact Ψ.toPartialEquiv.map_source (hAs hx)
  have hΨκ : ∀ t ∈ Ioc (0 : ℝ) T, ∀ z : TotalSpace F V, ‖z.2‖ = 1 →
      Ψ (κ (t, z)) = D ⟨z.proj, t • z.2⟩ := fun t ht z hz =>
    Ψ.toPartialEquiv.right_inv (htgt _ (hcore t ht z hz))
  refine ⟨?_, hAimg, ?_, ?_, ?_⟩
  · -- smoothness
    have hs : ContMDiff (𝓘(ℝ, ℝ).prod (IB.prod 𝓘(ℝ, F))) I ∞
        (fun p : ℝ × TotalSpace F V => D ⟨p.2.proj, p.1 • p.2.2⟩) :=
      D.contMDiff.comp contMDiff_totalSpace_smul
    exact Ψ.symm.contMDiffOn.comp hs.contMDiffOn fun p hp => hp
  · intro t₁ ht₁ t₂ ht₂ z₁ z₂ hz₁ hz₂ heq
    have h1 := hΨκ t₁ ht₁ z₁ hz₁
    have h2 := hΨκ t₂ ht₂ z₂ hz₂
    rw [heq] at h1
    have hD : (⟨z₁.proj, t₁ • z₁.2⟩ : TotalSpace F V) = ⟨z₂.proj, t₂ • z₂.2⟩ :=
      D.injective (h1.symm.trans h2)
    have ht : t₁ = t₂ := by
      have := congrArg (fun w : TotalSpace F V => ‖w.2‖) hD
      simp only at this
      rw [norm_smul, norm_smul, hz₁, hz₂, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos ht₁.1, abs_of_pos ht₂.1] at this
      simpa using this
    subst ht
    refine ⟨rfl, ?_⟩
    have hproj : z₁.proj = z₂.proj := by
      have h := congrArg TotalSpace.proj hD
      exact h
    rcases z₁ with ⟨b₁, v₁⟩
    rcases z₂ with ⟨b₂, v₂⟩
    simp only at hproj
    subst hproj
    have hv := TotalSpace.mk_inj.mp hD
    have hv' : v₁ = v₂ := by
      have := congrArg (fun w => t₁⁻¹ • w) hv
      simpa [smul_smul, inv_mul_cancel₀ ht₁.1.ne'] using this
    rw [hv']
  · intro x hx hne
    set w := D.symm (Ψ x) with hw
    have hwT : ‖w.2‖ ≤ T := by
      have : Ψ x ∈ Ψ '' A := mem_image_of_mem _ hx
      rw [hΨA] at this
      exact this
    have hwpos : 0 < ‖w.2‖ := norm_pos_iff.mpr hne
    refine ⟨‖w.2‖, ⟨hwpos, hwT⟩, ⟨w.proj, ‖w.2‖⁻¹ • w.2⟩, ?_, ?_⟩
    · change ‖‖w.2‖⁻¹ • w.2‖ = 1
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hwpos.ne']
    · change Ψ.symm (D ⟨w.proj, ‖w.2‖ • ‖w.2‖⁻¹ • w.2⟩) = x
      rw [smul_smul, mul_inv_cancel₀ hwpos.ne', one_smul]
      change Ψ.symm (D (D.symm (Ψ x))) = x
      rw [D.apply_symm_apply]
      exact Ψ.toPartialEquiv.left_inv (hAs hx)
  · intro t ht z hz
    have himg := partialDiffeomorph_image_frontier_of_subset_source Ψ hAc hAs (hΨA ▸ hcl)
    rw [hΨA, hfr] at himg
    constructor
    · intro hfrA
      have : Ψ (κ (t, z)) ∈ Ψ '' frontier A := mem_image_of_mem _ hfrA
      rw [himg, hΨκ t ht z hz] at this
      have h := hrad t z ht.1.le hz
      change ‖(D.symm (D ⟨z.proj, t • z.2⟩)).2‖ = T at this
      rw [h] at this
      exact this
    · intro htT
      have hy : D ⟨z.proj, t • z.2⟩ ∈ {x : N | ‖(D.symm x).2‖ = T} := by
        change ‖(D.symm (D ⟨z.proj, t • z.2⟩)).2‖ = T
        rw [hrad t z ht.1.le hz, htT]
      rw [← himg] at hy
      obtain ⟨x, hxfr, hxy⟩ := hy
      have hxA : x ∈ A := hAc.frontier_subset hxfr
      have : κ (t, z) = x := by
        change Ψ.symm (D ⟨z.proj, t • z.2⟩) = x
        rw [← hxy]
        exact Ψ.toPartialEquiv.left_inv (hAs hxA)
      rw [this]
      exact hxfr

end DifferentialGeometry.Geometry.Collapse
