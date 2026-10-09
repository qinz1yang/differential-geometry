import DifferentialGeometry.Topology.Manifold.Boundary.SmoothMap
import DifferentialGeometry.Topology.Manifold.SmoothApproximation.Boundary.Collar.Projection
import DifferentialGeometry.Topology.InvarianceOfDomainManifold
import DifferentialGeometry.Topology.Compactness.Nonvanishing

/-!
# Helpers for the collar straightening

* `Diffeomorph.boundaryRestrict`: a `C^k` diffeomorphism (`1 ≤ k`) of manifolds with boundary
  restricts to a `C^k` diffeomorphism of the boundaries (as boundaryless manifolds);
* `exists_pos_forall_le_mem_of_boundary_subset`: a property holding on an open neighbourhood of
  the boundary of a compact manifold holds on a sublevel `{r ≤ η}` of a defining function;
* `isOpen_image_of_injOn_interior`: invariance of domain on the interior: a continuous map,
  injective on an open set of interior points, has open image.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

namespace DifferentialGeometry.Topology.Manifold.SmoothApproximation

variable {n : ℕ}
  {A : Type*} [TopologicalSpace A] [ChartedSpace (EuclideanHalfSpace (n + 1)) A]
  [IsManifold (𝓡∂ (n + 1)) ∞ A]
  {B : Type*} [TopologicalSpace B] [ChartedSpace (EuclideanHalfSpace (n + 1)) B]
  [IsManifold (𝓡∂ (n + 1)) ∞ B]

omit [IsManifold (𝓡∂ (n + 1)) ∞ A] [IsManifold (𝓡∂ (n + 1)) ∞ B] in
theorem Diffeomorph.isBoundaryPoint_apply_iff {k : ℕ∞ω} (hk : 1 ≤ k)
    (h : A ≃ₘ^k⟮𝓡∂ (n + 1), 𝓡∂ (n + 1)⟯ B) {x : A} :
    (𝓡∂ (n + 1)).IsBoundaryPoint (h x) ↔ (𝓡∂ (n + 1)).IsBoundaryPoint x :=
  (((h.isLocalDiffeomorph x).isBoundaryPoint_iff
    (lt_of_lt_of_le zero_lt_one hk).ne')).symm

/-- The restriction of a `C^k` diffeomorphism (`1 ≤ k ≤ ∞`) to the boundaries. -/
def Diffeomorph.boundaryRestrict {k : ℕ∞ω} (hk : 1 ≤ k) (hk' : k ≤ ∞)
    (h : A ≃ₘ^k⟮𝓡∂ (n + 1), 𝓡∂ (n + 1)⟯ B) :
    BoundaryManifold (𝓡∂ (n + 1)) A ≃ₘ^k⟮HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1)),
      HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))⟯ BoundaryManifold (𝓡∂ (n + 1)) B where
  toFun p := ⟨h p, (Diffeomorph.isBoundaryPoint_apply_iff hk h (x := p)).mpr p.2⟩
  invFun q := ⟨h.symm q, by
    have h1 := (Diffeomorph.isBoundaryPoint_apply_iff hk h (x := h.symm q)).mp
    rw [h.apply_symm_apply] at h1
    exact h1 q.2⟩
  left_inv p := Subtype.ext (h.symm_apply_apply p.1)
  right_inv q := Subtype.ext (h.apply_symm_apply q.1)
  contMDiff_toFun := by
    refine (DifferentialGeometry.Manifold.Boundary.contMDiff_boundary_iff hk').mpr ?_
    exact h.contMDiff.comp ((boundaryInclusion_contMDiff (I := 𝓡∂ (n + 1)) (M := A)).of_le hk')
  contMDiff_invFun := by
    refine (DifferentialGeometry.Manifold.Boundary.contMDiff_boundary_iff hk').mpr ?_
    exact h.symm.contMDiff.comp
      ((boundaryInclusion_contMDiff (I := 𝓡∂ (n + 1)) (M := B)).of_le hk')

@[simp]
theorem Diffeomorph.boundaryRestrict_apply_coe {k : ℕ∞ω} (hk : 1 ≤ k) (hk' : k ≤ ∞)
    (h : A ≃ₘ^k⟮𝓡∂ (n + 1), 𝓡∂ (n + 1)⟯ B) (p : BoundaryManifold (𝓡∂ (n + 1)) A) :
    (Diffeomorph.boundaryRestrict hk hk' h p : B) = h p :=
  rfl

omit [IsManifold (𝓡∂ (n + 1)) ∞ A] in
/-- A property holding on an open neighbourhood `O` of the boundary of a compact manifold holds on
a sublevel `{r ≤ η}`, `η > 0`, of any continuous `r` vanishing exactly on the boundary. -/
theorem exists_pos_forall_le_mem_of_boundary_subset [CompactSpace A] {r : A → ℝ}
    (hr : Continuous r) (hrzero : ∀ x, r x = 0 ↔ (𝓡∂ (n + 1)).IsBoundaryPoint x) {O : Set A}
    (hO : IsOpen O) (hbO : (𝓡∂ (n + 1)).boundary A ⊆ O) :
    ∃ η > 0, ∀ x, |r x| ≤ η → x ∈ O := by
  obtain ⟨η, hη, hηr⟩ := DifferentialGeometry.Topology.exists_pos_lt_norm_of_isCompact
    hO.isClosed_compl.isCompact hr.continuousOn
    (fun x hx hz => hx (hbO ((hrzero x).mp hz)))
  refine ⟨η / 2, half_pos hη, fun x hx => ?_⟩
  by_contra hxO
  have h := hηr x hxO
  rw [Real.norm_eq_abs] at h
  linarith

omit [IsManifold (𝓡∂ (n + 1)) ∞ A] [IsManifold (𝓡∂ (n + 1)) ∞ B] in
/-- **Invariance of domain on the interior.** -/
theorem isOpen_image_of_injOn_interior {f : A → B} {W : Set A} (hW : IsOpen W)
    (hf : ContinuousOn f W) (hinj : InjOn f W)
    (hWi : ∀ x ∈ W, (𝓡∂ (n + 1)).IsInteriorPoint x) : IsOpen (f '' W) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x, hxW, rfl⟩
  set φ := extChartAt (𝓡∂ (n + 1)) x with hφ
  set ψ := extChartAt (𝓡∂ (n + 1)) (f x) with hψ
  set O : Set A := W ∩ f ⁻¹' ψ.source with hOdef
  have hO : IsOpen O := hf.isOpen_inter_preimage hW (isOpen_extChartAt_source (f x))
  set V : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
    (φ.target ∩ interior (range (𝓡∂ (n + 1)))) ∩ φ.symm ⁻¹' O with hVdef
  have hint : IsOpen (φ.target ∩ interior (range (𝓡∂ (n + 1)))) := by
    have hrw : φ.target ∩ interior (range (𝓡∂ (n + 1))) =
        (𝓡∂ (n + 1)).symm ⁻¹' (chartAt (EuclideanHalfSpace (n + 1)) x).target ∩
          interior (range (𝓡∂ (n + 1))) := by
      rw [hφ, extChartAt_target, inter_assoc, inter_eq_right.mpr interior_subset]
    rw [hrw]
    exact ((chartAt (EuclideanHalfSpace (n + 1)) x).open_target.preimage
      (𝓡∂ (n + 1)).continuous_symm).inter isOpen_interior
  have hV : IsOpen V :=
    ((continuousOn_extChartAt_symm x).mono inter_subset_left).isOpen_inter_preimage hint hO
  have hxV : φ x ∈ V := by
    refine ⟨⟨mem_extChartAt_target x, ?_⟩, ?_⟩
    · have h := (isInteriorPoint_iff_any_chart_real (𝓡∂ (n + 1)) (mem_chart_source _ x)).mp
        (hWi x hxW)
      exact h
    · simp only [mem_preimage, hφ, extChartAt_to_inv]
      exact ⟨hxW, mem_extChartAt_source _⟩
  set rep : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun z => ψ (f (φ.symm z)) with hrep
  have hVsrc : ∀ z ∈ V, φ.symm z ∈ O := fun z hz => hz.2
  have hrepc : ContinuousOn rep V := by
    refine (continuousOn_extChartAt (f x)).comp ?_ ?_
    · exact hf.comp ((continuousOn_extChartAt_symm x).mono fun z hz => hz.1.1)
        (fun z hz => (hVsrc z hz).1)
    · intro z hz
      exact (hVsrc z hz).2
  have hrepi : InjOn rep V := by
    intro z hz z' hz' he
    have h1 : f (φ.symm z) = f (φ.symm z') :=
      ψ.injOn (hVsrc z hz).2 (hVsrc z' hz').2 he
    have h2 := hinj (hVsrc z hz).1 (hVsrc z' hz').1 h1
    exact φ.symm.injOn hz.1.1 hz'.1.1 h2 |>.trans rfl
  have hopen : IsOpen (rep '' V) :=
    DifferentialGeometry.Topology.invariance_of_domain_isOpen_image hV hrepc hrepi
  have hsub : rep '' V ⊆ ψ.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact ψ.map_source (hVsrc z hz).2
  have hset : ψ.symm '' (rep '' V) = ψ.source ∩ ψ ⁻¹' (rep '' V) :=
    ψ.symm_image_eq_source_inter_preimage hsub
  have hopen' : IsOpen (ψ.symm '' (rep '' V)) := by
    rw [hset]
    exact (continuousOn_extChartAt (f x)).isOpen_inter_preimage (isOpen_extChartAt_source _)
      hopen
  have hmem : f x ∈ ψ.symm '' (rep '' V) :=
    ⟨rep (φ x), ⟨φ x, hxV, rfl⟩, by
      simp only [hrep, hφ, extChartAt_to_inv]
      exact ψ.left_inv (mem_extChartAt_source _)⟩
  refine Filter.mem_of_superset (hopen'.mem_nhds hmem) ?_
  rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  refine ⟨φ.symm z, (hVsrc z hz).1, ?_⟩
  exact (ψ.left_inv (hVsrc z hz).2).symm

end DifferentialGeometry.Topology.Manifold.SmoothApproximation
