import DifferentialGeometry.Topology.Manifold.RegularLevel.HalfSpaceSliceCharts
import Mathlib.Geometry.Manifold.Immersion

/-!
# Half-space slice manifolds: the inclusion is an immersion

Lane FC39-G-ARC (A3/A4 of external draft 58 §四). Companion of `HalfSpaceSlice.lean`: for the
slice charted space `sliceChartedSpace P Bd hP` on `{x // P x}` inside a manifold `M` modelled on
a normed space `E'` (self model),

* `sliceChart_mem_maximalAtlas_GARC`: EVERY slice chart (not only the chosen ones) lies in the
  maximal atlas of `{x // P x}`;
* `slice_isImmersionAtOfComplement_val_GARC`: at a point lying in a slice chart `Φ` whose first
  coordinate is positive on its whole source, the inclusion is an immersion with complement `F`:
  the code chart is `Φ` followed by `q ↦ L (q₁ - c e₀, q₂)` (an open partial homeomorphism onto an
  open subset of `E'`, because `q₁` stays in the open half-space), in which the inclusion reads
  `u ↦ L (u, 0)`;
* `slice_isImmersionOfComplement_val_GARC`: the global form when such charts exist at every point.
-/

set_option autoImplicit false
noncomputable section
open Set Function Filter Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Manifold.RegularLevel

section Immersion

variable {d : ℕ} {E' M F : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace M] [ChartedSpace E' M] [IsManifold 𝓘(ℝ, E') ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (P Bd : M → Prop)
  (hP : ∀ x, P x → ∃ p : PartialDiffeomorph 𝓘(ℝ, E') ((𝓡∂ (d + 1)).prod 𝓘(ℝ, F)) M
        (EuclideanHalfSpace (d + 1) × F) ∞ × ℝ,
      0 ≤ p.2 ∧ x ∈ p.1.source ∧
      (∀ y ∈ p.1.source, P y ↔ ((p.1 y).2 = 0 ∧ p.2 ≤ (p.1 y).1.1 0)) ∧
      ((p.1 x).1.1 0 = p.2 ↔ Bd x))

omit [IsManifold 𝓘(ℝ, E') ∞ M] in
theorem sliceChart_mem_maximalAtlas_GARC
    (Φ : PartialDiffeomorph 𝓘(ℝ, E') ((𝓡∂ (d + 1)).prod 𝓘(ℝ, F)) M
      (EuclideanHalfSpace (d + 1) × F) ∞)
    {c : ℝ} (hc : 0 ≤ c) (hΦ : ∀ y ∈ Φ.source, P y ↔ ((Φ y).2 = 0 ∧ c ≤ (Φ y).1.1 0))
    (x₀ : {x // P x}) :
    letI := sliceChartedSpace P Bd hP
    sliceChart P Φ hc hΦ x₀ ∈ IsManifold.maximalAtlas (𝓡∂ (d + 1)) ∞ {x // P x} := by
  let _ := sliceChartedSpace P Bd hP
  have _ := slice_isManifold P Bd hP
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · have hv : ContMDiffOn (𝓡∂ (d + 1)) ((𝓡∂ (d + 1)).prod 𝓘(ℝ, F)) ∞
        (fun y : {x // P x} => Φ y.1) (Subtype.val ⁻¹' Φ.source) :=
      Φ.contMDiffOn.comp (slice_contMDiff_val P Bd hP).contMDiffOn (fun y hy => hy)
    refine (contMDiffOn_sliceUnshift (d := d) c).comp (contMDiff_fst.comp_contMDiffOn hv) ?_
    intro y hy
    exact ((hΦ y.1 hy).mp y.2).2
  · intro w hw
    have hw' : (sliceShift d c w, (0 : F)) ∈ Φ.target := hw
    rw [slice_contMDiffWithinAt_iff hP le_rfl]
    have hk : ContMDiff (𝓡∂ (d + 1)) ((𝓡∂ (d + 1)).prod 𝓘(ℝ, F)) ∞
        (fun w => (sliceShift d c w, (0 : F))) :=
      (contMDiff_sliceShift hc).prodMk contMDiff_const
    have h1 : ContMDiffWithinAt (𝓡∂ (d + 1)) 𝓘(ℝ, E') ∞
        (fun w => Φ.symm (sliceShift d c w, (0 : F)))
        ((sliceChart P Φ hc hΦ x₀).target) w :=
      (Φ.symm.contMDiffOn.comp hk.contMDiffOn (fun w hw => hw)) w hw
    refine h1.congr (fun w' hw' => ?_) ?_
    · exact sliceChartInv_val P Φ hc hΦ x₀ hw'
    · exact sliceChartInv_val P Φ hc hΦ x₀ hw'

/-- **The slice inclusion is an immersion at every point where a slice chart with positive first
coordinate is available** (the code chart is the slice chart followed by `q ↦ L (q₁ - c e₀, q₂)`). -/
theorem slice_isImmersionAtOfComplement_val_GARC
    (L : (EuclideanSpace ℝ (Fin (d + 1)) × F) ≃L[ℝ] E') (x : {x // P x})
    (Φ : PartialDiffeomorph 𝓘(ℝ, E') ((𝓡∂ (d + 1)).prod 𝓘(ℝ, F)) M
      (EuclideanHalfSpace (d + 1) × F) ∞)
    {c : ℝ} (hc : 0 ≤ c) (hΦ : ∀ y ∈ Φ.source, P y ↔ ((Φ y).2 = 0 ∧ c ≤ (Φ y).1.1 0))
    (hx : x.1 ∈ Φ.source) (hpos : ∀ y ∈ Φ.source, 0 < (Φ y).1.1 0) :
    letI := sliceChartedSpace P Bd hP
    IsImmersionAtOfComplement F (𝓡∂ (d + 1)) 𝓘(ℝ, E') ∞ (Subtype.val : {x // P x} → M) x := by
  let _ := sliceChartedSpace P Bd hP
  let ψ : PartialDiffeomorph 𝓘(ℝ, E') 𝓘(ℝ, E') M E' ∞ :=
    Φ.trans ((sliceHalfSpaceProd (d := d) F).symm.trans
      (sliceAffine L (-L (c • EuclideanSpace.single 0 1, 0))).toPartialDiffeomorph)
  have hψ : ∀ y ∈ Φ.source, ψ y = L ((Φ y).1.1 - c • EuclideanSpace.single 0 1, (Φ y).2) := by
    intro y _
    change L ((Φ y).1.1, (Φ y).2) + -L (c • EuclideanSpace.single 0 1, 0) = _
    rw [← map_neg, ← map_add]
    congr 1
    ext <;> simp [sub_eq_add_neg]
  have hψsource : ψ.source = Φ.source := by
    apply Subset.antisymm
    · intro y hy
      exact hy.1
    · intro y hy
      exact ⟨hy, hpos y hy, mem_univ _⟩
  refine IsImmersionAtOfComplement.mk_of_charts L (sliceChart P Φ hc hΦ x)
    ψ.toOpenPartialHomeomorph hx (hψsource ▸ hx)
    (sliceChart_mem_maximalAtlas_GARC P Bd hP Φ hc hΦ x) ?_ ?_ ?_
  · apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
    · exact ψ.contMDiffOn
    · exact ψ.symm.contMDiffOn
  · intro y hy
    change y.1 ∈ ψ.source
    rw [hψsource]
    exact hy
  · intro y hy
    obtain ⟨hy2, hy1⟩ := hy
    set w : EuclideanHalfSpace (d + 1) := (𝓡∂ (d + 1)).symm y with hwdef
    have hw : (sliceShift d c w, (0 : F)) ∈ Φ.target := hy1
    have hwy : w.1 = y := (𝓡∂ (d + 1)).right_inv (by rwa [← ModelWithCorners.target_eq])
    have hinv : (((sliceChart P Φ hc hΦ x).extend (𝓡∂ (d + 1))).symm y : M) =
        Φ.symm (sliceShift d c w, 0) := by
      rw [OpenPartialHomeomorph.extend_coe_symm]
      exact sliceChartInv_val P Φ hc hΦ x hw
    change ψ (((sliceChart P Φ hc hΦ x).extend (𝓡∂ (d + 1))).symm y : M) = L (y, 0)
    rw [hinv]
    refine (hψ _ (Φ.map_target hw)).trans ?_
    have hr : Φ (Φ.symm (sliceShift d c w, (0 : F))) = (sliceShift d c w, 0) := Φ.right_inv hw
    erw [hr]
    congr 1
    refine Prod.ext ?_ rfl
    change (sliceShift d c w).1 - c • EuclideanSpace.single 0 1 = y
    rw [sliceShift_val hc w, hwy, add_sub_cancel_right]

/-- **The slice inclusion is an immersion** when a slice chart with positive first coordinate is
available at every point (one complement `F` for all points). -/
theorem slice_isImmersionOfComplement_val_GARC
    (L : (EuclideanSpace ℝ (Fin (d + 1)) × F) ≃L[ℝ] E')
    (hP' : ∀ x, P x → ∃ p : PartialDiffeomorph 𝓘(ℝ, E') ((𝓡∂ (d + 1)).prod 𝓘(ℝ, F)) M
        (EuclideanHalfSpace (d + 1) × F) ∞ × ℝ,
      0 ≤ p.2 ∧ x ∈ p.1.source ∧
      (∀ y ∈ p.1.source, P y ↔ ((p.1 y).2 = 0 ∧ p.2 ≤ (p.1 y).1.1 0)) ∧
      ∀ y ∈ p.1.source, 0 < (p.1 y).1.1 0) :
    letI := sliceChartedSpace P Bd hP
    IsImmersionOfComplement F (𝓡∂ (d + 1)) 𝓘(ℝ, E') ∞ (Subtype.val : {x // P x} → M) := by
  let _ := sliceChartedSpace P Bd hP
  intro x
  obtain ⟨p, hc, hx, hΦ, hpos⟩ := hP' x.1 x.2
  exact slice_isImmersionAtOfComplement_val_GARC P Bd hP L x p.1 hc hΦ hx hpos

end Immersion

end DifferentialGeometry.Manifold.RegularLevel
