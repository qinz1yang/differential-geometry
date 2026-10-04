import DifferentialGeometry.Geometry.Comparison.Soul.EmbeddedSliceManifold
import DifferentialGeometry.Topology.Manifold.ContMDiff.OpenSubtype
import DifferentialGeometry.Topology.Manifold.RegularLevel.Coordinates

/-!
# Embedded slices: corestriction at every order and local regular zero sets (W-SUB, K1)

Foundation of the smooth replacement of a compact `C^k` hypersurface (blueprint LFR47, design risk R7,
external review of the finite soul §8). The output hypersurface is an `IsEmbeddedSlice`
(`Geometry/Comparison/Soul/EmbeddedSlice.lean`), the interface of the smooth soul toolkit.

* `embeddedSlice_contMDiff_corestrict`: a `C^n` map into the ambient manifold with values in an
  embedded slice is `C^n` into the slice with its charted space `embeddedSliceChartedSpace`
  (the existing `embeddedSlice_corestrict_contMDiff` is the case `n = ∞`). Route: a smooth local
  retraction `c.symm ∘ π_A ∘ c` onto the slice from a slice chart `(c, A)`, corestricted by the
  `∞` lemma on an open subset.
* `isEmbeddedSlice_of_forall_regular_zero`: a set that is, near each of its points, the zero set of
  a smooth function with nonzero differential at that point is an embedded slice of codimension
  one (product coordinates `exists_product_coordinates_of_contMDiffOn`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Manifold.SmoothHypersurface

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- An affine projection of `E` onto an affine subspace: smooth, with values in the subspace and
fixing its points. -/
theorem exists_affine_retraction (A : AffineSubspace ℝ E) {a₀ : E} (ha₀ : a₀ ∈ A) :
    ∃ π : E → E, ContDiff ℝ ∞ π ∧ (∀ z, π z ∈ A) ∧ ∀ z ∈ A, π z = z := by
  obtain ⟨K', hK'⟩ := A.direction.exists_isCompl
  let P : E →L[ℝ] E := LinearMap.toContinuousLinearMap (A.direction.projection K' hK')
  refine ⟨fun z => P (z - a₀) + a₀, (P.contDiff.comp (contDiff_id.sub contDiff_const)).add
    contDiff_const, fun z => ?_, fun z hz => ?_⟩
  · exact AffineSubspace.vadd_mem_of_mem_direction
      (Submodule.projection_apply_mem hK' (z - a₀)) ha₀
  · have hmem : z - a₀ ∈ A.direction := A.vsub_mem_direction hz ha₀
    change A.direction.projection K' hK' (z - a₀) + a₀ = z
    rw [Submodule.projection_apply_of_mem_left hK' hmem, sub_add_cancel]

/-- A smooth local retraction onto an embedded slice near each of its points: an open `W ∋ p` and a
map `r`, smooth on `W`, with values in the slice on `W` and fixing the points of the slice in `W`. -/
theorem exists_local_retraction {Ŝ : Set M} {d : ℕ} (hS : IsEmbeddedSlice I d Ŝ) {p : M}
    (hp : p ∈ Ŝ) :
    ∃ W : Set M, IsOpen W ∧ p ∈ W ∧ ∃ r : M → M, ContMDiffOn I I ∞ r W ∧
      (∀ y ∈ W, r y ∈ Ŝ) ∧ ∀ y ∈ W, y ∈ Ŝ → r y = y := by
  obtain ⟨c, A, -, hpc, -, himage⟩ := hS p hp
  have hpA : c p ∈ A := (himage.apply_mem_iff hpc).2 hp
  obtain ⟨π, hπ, hπA, hπfix⟩ := exists_affine_retraction A hpA
  have hcont : ContinuousOn (fun y => π (c y)) c.source :=
    hπ.continuous.comp_continuousOn c.contMDiffOn_toFun.continuousOn
  refine ⟨c.source ∩ (fun y => π (c y)) ⁻¹' c.target,
    hcont.isOpen_inter_preimage c.open_source c.open_target, ⟨hpc, ?_⟩,
    fun y => c.symm (π (c y)), ?_, ?_, ?_⟩
  · change π (c p) ∈ c.target
    rw [hπfix _ hpA]
    exact c.map_source hpc
  · have h1 : ContMDiffOn I 𝓘(ℝ, E) ∞ (fun y => π (c y)) c.source :=
      hπ.contMDiff.comp_contMDiffOn c.contMDiffOn_toFun
    exact c.contMDiffOn_invFun.comp (h1.mono inter_subset_left) (fun y hy => hy.2)
  · intro y hy
    exact (himage.symm_apply_mem_iff hy.2).2 (hπA _)
  · intro y hy hyS
    change c.symm (π (c y)) = y
    rw [hπfix _ ((himage.apply_mem_iff hy.1).2 hyS)]
    exact c.left_inv hy.1

/-- **K1a: corestriction into an embedded slice at every finite or smooth order.** -/
theorem embeddedSlice_contMDiff_corestrict {Ŝ : Set M} {d : ℕ} (hS : IsEmbeddedSlice I d Ŝ)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {X : Type*} [TopologicalSpace X] [ChartedSpace G X] {n : ℕ∞}
    (g : X → M) (hg : ContMDiff J I n g) (hmem : ∀ x, g x ∈ Ŝ) :
    let _ := embeddedSliceChartedSpace hS
    ContMDiff J 𝓘(ℝ, Fin d → ℝ) n (fun x => (⟨g x, hmem x⟩ : Ŝ)) := by
  let _ := embeddedSliceChartedSpace hS
  change ContMDiff J 𝓘(ℝ, Fin d → ℝ) n (fun x => (⟨g x, hmem x⟩ : Ŝ))
  intro x₀
  obtain ⟨W, hW, hpW, r, hr, hrS, hrfix⟩ := exists_local_retraction hS (hmem x₀)
  let Wo : TopologicalSpace.Opens M := ⟨W, hW⟩
  have hr0 : ContMDiff I I ∞ (fun y : Wo => r y) :=
    hr.comp_contMDiff contMDiff_subtype_val (fun y => y.2)
  have hρ := embeddedSlice_corestrict_contMDiff hS (fun y : Wo => r y) hr0 (fun y => hrS y y.2)
  classical
  let κ : X → Wo := fun x => if h : g x ∈ W then ⟨g x, h⟩ else ⟨g x₀, hpW⟩
  have hnhds : g ⁻¹' W ∈ 𝓝 x₀ := hg.continuous.continuousAt.preimage_mem_nhds (hW.mem_nhds hpW)
  have hκval : (Subtype.val ∘ κ) =ᶠ[𝓝 x₀] g := by
    filter_upwards [hnhds] with x hx
    simp only [comp_apply, κ, dite_eq_left (show g x ∈ W from hx)]
  have hκ : ContMDiffAt J I n κ x₀ :=
    (DifferentialGeometry.Manifold.contMDiffAt_subtypeVal_comp_iff Wo κ x₀).mp
      ((hg x₀).congr_of_eventuallyEq hκval)
  have hρn : ContMDiff I 𝓘(ℝ, Fin d → ℝ) n
      (fun y : Wo => (⟨r y, hrS y y.2⟩ : Ŝ)) := hρ.of_le (by exact_mod_cast le_top)
  have hcomp := (hρn (κ x₀)).comp x₀ hκ
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [hnhds] with x hx
  apply Subtype.ext
  simp only [comp_apply, κ, dite_eq_left (show g x ∈ W from hx)]
  exact (hrfix (g x) hx (hmem x)).symm

/-- **K1b: local regular zero sets are embedded slices of codimension one.** -/
theorem isEmbeddedSlice_of_forall_regular_zero [I.Boundaryless] [IsManifold I ∞ M] {d : ℕ}
    (hdim : Module.finrank ℝ E = d + 1) {Ŝ : Set M}
    (h : ∀ x ∈ Ŝ, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ g : M → ℝ,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ g U ∧ (∀ y ∈ U, y ∈ Ŝ ↔ g y = 0) ∧
        mfderiv I 𝓘(ℝ, ℝ) g x ≠ 0) :
    IsEmbeddedSlice I d Ŝ := by
  intro x hx
  obtain ⟨U, hU, hxU, g, hg, hiff, hreg⟩ := h x hx
  obtain ⟨Φ, hxΦ, hΦU, hΦg⟩ :=
    DifferentialGeometry.Manifold.RegularLevel.exists_product_coordinates_of_contMDiffOn
      (m := d) I hdim hU hg hxU hreg
  have hdim' : Module.finrank ℝ (ℝ × EuclideanSpace ℝ (Fin d)) = Module.finrank ℝ E := by
    rw [Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin, hdim, add_comm]
  let L : (ℝ × EuclideanSpace ℝ (Fin d)) ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq hdim'
  let D : Diffeomorph (𝓘(ℝ, ℝ).prod (𝓡 d)) 𝓘(ℝ, E) (ℝ × EuclideanSpace ℝ (Fin d)) E ∞ :=
    { toEquiv := L.toEquiv
      contMDiff_toFun := by
        rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
        exact L.contDiff.contMDiff
      contMDiff_invFun := by
        rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
        exact L.symm.contDiff.contMDiff }
  let c := Φ.trans D.toPartialDiffeomorph
  let ℓ : E →ₗ[ℝ] ℝ := (LinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin d))) ∘ₗ
    (L.symm : E →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin d))).toLinearMap
  have hℓ : ∀ w, ℓ (L w) = w.1 := fun w => by
    change (L.symm (L w)).1 = w.1
    rw [L.symm_apply_apply]
  have hsurj : LinearMap.range ℓ = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro t
    exact ⟨L (t, 0), by rw [hℓ]⟩
  have hker : Module.finrank ℝ (LinearMap.ker ℓ) = d := by
    have h1 := LinearMap.finrank_range_add_finrank_ker ℓ
    rw [hsurj, finrank_top, Module.finrank_self, hdim] at h1
    omega
  refine ⟨c, (LinearMap.ker ℓ).toAffineSubspace, inferInstance, ⟨hxΦ, mem_univ _⟩,
    ?_, ?_⟩
  · rw [Submodule.toAffineSubspace_direction]
    exact hker
  · intro y hy
    have hyΦ : y ∈ Φ.source := hy.1
    change L (Φ y) ∈ (LinearMap.ker ℓ).toAffineSubspace ↔ y ∈ Ŝ
    rw [Submodule.mem_toAffineSubspace, LinearMap.mem_ker, hℓ, hΦg y hyΦ]
    exact (hiff y (hΦU hyΦ)).symm

end DifferentialGeometry.Topology.Manifold.SmoothHypersurface
