import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphTrans
import DifferentialGeometry.Topology.OpenPartialHomeomorph.Images

/-!
# LC61 kernel: the open ball has the smooth type of the interior of the model core

Master207A, A:23460 (LC61), noncompact branch, the differential-topology composition. In the
setting of LC57 at a fixed scale:
* `Φ : N ⇀ M` is the (original) model embedding, defined on a neighbourhood of the model core
  `D ⊆ N`;
* `H₁` is an ambient diffeomorphism of `M` with `H₁ (Φ D) = A` (LC51/LC48: the core is carried onto
  the radial sublevel `A = {η ≤ ρ}`);
* `J : int A ≃ B` is LC60's diffeomorphism of open sets onto the open distance ball `B`;
* `K₁` is an ambient diffeomorphism of `N` with `K₁ D = D_u` (LC55: the core is isotopic to the
  constant-height normal-flow core `D_u = {u ≤ ρ'}`).
Then `int D_u ≃ B` as open sets: `Ψ = J ∘ H₁ ∘ Φ ∘ K₁⁻¹`. The only topology used is that partial
homeomorphisms and homeomorphisms commute with interiors of subsets of their sources.
-/

set_option autoImplicit false

noncomputable section

open Set Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The restriction of a partial diffeomorphism to an open subset of its source. -/
theorem exists_partialDiffeomorph_restrict {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} {M' : Type*}
    [TopologicalSpace M'] [ChartedSpace H' M'] (Φ : PartialDiffeomorph I I' N M' ∞) {O : Set N}
    (hO : IsOpen O) (hOs : O ⊆ Φ.source) :
    ∃ Φ₀ : PartialDiffeomorph I I' N M' ∞, Φ₀.source = O ∧ Φ₀.target = Φ '' O ∧
      ∀ x, Φ₀ x = Φ x := by
  let e := Φ.toOpenPartialHomeomorph.restrOpen O hO
  have hes : e.source = O := by
    change Φ.source ∩ O = O
    exact inter_eq_right.mpr hOs
  have het : e.target = Φ '' O := by
    rw [← e.image_source_eq_target, hes]
    rfl
  refine ⟨{ toPartialEquiv := e.toPartialEquiv
            open_source := e.open_source
            open_target := e.open_target
            contMDiffOn_toFun := Φ.contMDiffOn_toFun.mono fun x hx => (hx : x ∈ e.source).1
            contMDiffOn_invFun := Φ.contMDiffOn_invFun.mono fun y hy => (hy : y ∈ e.target).1 },
    hes, het, fun x => rfl⟩

/-- **LC61 kernel** (master207A, A:23460, noncompact branch). If the model core `D` lies in the
source of the model embedding `Φ`, an ambient diffeomorphism `H₁` of `M` carries `Φ D` onto `A`,
`J` is a diffeomorphism of open sets from `int A` onto `B`, and an ambient diffeomorphism `K₁` of
`N` carries `D` onto `D_u`, then `int D_u` and `B` are diffeomorphic open sets:
`Ψ = J ∘ H₁ ∘ Φ ∘ K₁⁻¹`. -/
theorem exists_partialDiffeomorph_interior_of_core_isotopies
    (Φ : PartialDiffeomorph I I N M ∞) {D : Set N} (hD : D ⊆ Φ.source)
    (H₁ : Diffeomorph I I M M ∞) {A : Set M} (hA : H₁ '' (Φ '' D) = A)
    (J : PartialDiffeomorph I I M M ∞) {B : Set M} (hJs : J.source = interior A)
    (hJt : J.target = B) (K₁ : Diffeomorph I I N N ∞) {Du : Set N} (hK : K₁ '' D = Du) :
    ∃ Ψ : PartialDiffeomorph I I N M ∞, Ψ.source = interior Du ∧ Ψ.target = B ∧
      ∀ x ∈ interior Du, Ψ x = J (H₁ (Φ (K₁.symm x))) := by
  obtain ⟨Φ₀, hΦ₀s, hΦ₀t, hΦ₀⟩ :=
    exists_partialDiffeomorph_restrict Φ isOpen_interior (interior_subset.trans hD)
  -- `H₁ (Φ (int D)) = int A`
  have hΦint : Φ '' interior D = interior (Φ '' D) :=
    Φ.toOpenPartialHomeomorph.image_interior_of_subset_source hD
  have hAint : H₁ '' (Φ '' interior D) = interior A := by
    rw [hΦint, ← hA]
    exact H₁.toHomeomorph.image_interior _
  have hKint : K₁ '' interior D = interior Du := by
    rw [← hK]
    exact K₁.toHomeomorph.image_interior _
  let X := H₁.toPartialDiffeomorph.trans J
  have hXs : X.source = H₁ ⁻¹' interior A := by
    rw [PartialDiffeomorph.trans_source, ← hJs]
    exact univ_inter _
  have hXt : X.target = B := by
    rw [← hJt]
    ext y
    exact ⟨fun h => h.1, fun h => ⟨h, mem_univ _⟩⟩
  let Y := Φ₀.trans X
  have hYs : Y.source = interior D := by
    rw [PartialDiffeomorph.trans_source, hΦ₀s, hXs]
    refine inter_eq_left.mpr fun x hx => ?_
    change H₁ (Φ₀ x) ∈ interior A
    rw [hΦ₀, ← hAint]
    exact ⟨Φ x, ⟨x, hx, rfl⟩, rfl⟩
  have hYt : Y.target = B := by
    rw [← hXt]
    ext y
    refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    change H₁.symm (J.symm y) ∈ Φ₀.target
    have hJy : J.symm y ∈ interior A := by
      rw [← hJs]
      have hy : y ∈ J.target := h.1
      exact J.toPartialEquiv.map_target hy
    rw [← hAint] at hJy
    obtain ⟨z, hz, hzy⟩ := hJy
    rw [hΦ₀t, ← hzy, Diffeomorph.symm_apply_apply]
    exact hz
  refine ⟨K₁.symm.toPartialDiffeomorph.trans Y, ?_, ?_, fun x _ => ?_⟩
  · rw [PartialDiffeomorph.trans_source, hYs, ← hKint]
    ext x
    constructor
    · rintro ⟨-, hx⟩
      exact ⟨K₁.symm x, hx, K₁.apply_symm_apply x⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨mem_univ _, ?_⟩
      change K₁.symm (K₁ z) ∈ interior D
      rwa [K₁.symm_apply_apply]
  · rw [← hYt]
    ext y
    exact ⟨fun h => h.1, fun h => ⟨h, mem_univ _⟩⟩
  · change J (H₁ (Φ₀ (K₁.symm x))) = _
    rw [hΦ₀]

end DifferentialGeometry.Geometry.Collapse
