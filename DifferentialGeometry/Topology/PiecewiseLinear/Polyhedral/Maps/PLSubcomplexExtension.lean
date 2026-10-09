import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedral.Maps.PolyhedralMap
import DifferentialGeometry.Topology.SimplicialComplex.Realization.GeometricRealization
import DifferentialGeometry.Topology.SimplicialComplex.Barycentric.Subdivision.BarycentricSubcomplex
import DifferentialGeometry.Topology.SimplicialComplex.Weights.DualSkeleton

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry _root_.Topology
open scoped BigOperators

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {ι κ F : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def extraCoordinateVertex (A : Set ι) (p : ι → F) (label : ι → κ) (i : ι) : F × (κ → ℝ) := by
  classical
  exact (p i, if i ∈ A then 0 else Pi.single (label i) 1)

omit [DecidableEq ι] [Fintype ι] [Fintype κ] in
theorem affineIndependent_extraCoordinateVertex [Finite ι] [Finite κ]
    (A : Set ι) (p : ι → F) (label : ι → κ) (hlabel : Function.Injective label)
    (hp : AffineIndependent ℝ (fun i : A => p i.val)) :
    AffineIndependent ℝ (extraCoordinateVertex A p label) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : Fintype κ := Fintype.ofFinite κ
  apply (affineIndependent_iff_of_fintype ℝ _).mpr
  intro w hsum hw i
  rw [Finset.weightedVSub_eq_linear_combination _ hsum] at hw
  have hout : ∀ j ∉ A, w j = 0 := by
    intro j hj
    have he := congrArg (fun z : F × (κ → ℝ) => z.2 (label j)) hw
    have hterm : ∀ k : ι,
        (w k • extraCoordinateVertex A p label k).2 (label j) =
          if k = j then w j else 0 := by
      intro k
      by_cases hkj : k = j
      · subst k
        simp [extraCoordinateVertex, hj]
      · have hl : label k ≠ label j := fun h => hkj (hlabel h)
        by_cases hk : k ∈ A <;> simp [extraCoordinateVertex, hk, hkj, Ne.symm hl]
    simpa only [Prod.snd_sum, Finset.sum_apply, hterm, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, Prod.snd_zero, Pi.zero_apply] using he
  have hsumA : ∑ j : A, w j.val = 0 := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun j => j ∈ A) w] at hsum
    have hz : ∑ j : {j // j ∉ A}, w j.val = 0 :=
      Finset.sum_eq_zero (fun j _ => hout j.val j.property)
    rwa [hz, add_zero] at hsum
  have hvecA : ∑ j : A, w j.val • p j.val = 0 := by
    have he := congrArg Prod.fst hw
    change (∑ j : ι, w j • extraCoordinateVertex A p label j).1 = 0 at he
    simp only [Prod.fst_sum, Prod.smul_fst, extraCoordinateVertex] at he
    rw [← Fintype.sum_subtype_add_sum_subtype (fun j => j ∈ A) (fun j => w j • p j)] at he
    have hz : ∑ j : {j // j ∉ A}, w j.val • p j.val = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [hout j.val j.property, zero_smul]
    rwa [hz, add_zero] at he
  by_cases hi : i ∈ A
  · exact hp.eq_zero_of_sum_eq_zero hsumA hvecA ⟨i, hi⟩ (Finset.mem_univ _)
  · exact hout i hi

variable {E : Type*} [DecidableEq E]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [DecidableEq E] in
theorem exists_nondegenerate_extension_of_vertexRestriction
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (A : Set E) (f : E → F)
    (hf : ∀ s ∈ (vertexRestriction K A).faces,
      ∃ B : E →ᵃ[ℝ] F, EqOn f B (convexHull ℝ (s : Set E)))
    (hinj : ∀ s ∈ (vertexRestriction K A).faces, InjOn f (convexHull ℝ (s : Set E))) :
    ∃ n : ℕ, ∃ g : E → F × (Fin n → ℝ),
      (∀ x ∈ (vertexRestriction K A).space, g x = (f x, 0)) ∧
      (∀ s ∈ K.faces, ∃ B : E →ᵃ[ℝ] (F × (Fin n → ℝ)), EqOn g B (convexHull ℝ (s : Set E))) ∧
      (∀ s ∈ K.faces, InjOn g (convexHull ℝ (s : Set E))) := by
  classical
  letI : Fintype K.vertices := (finite_vertices_of_finite_faces K hK).fintype
  let n := Fintype.card (Option K.vertices)
  let label : E → Fin n := fun x => Fintype.equivFin (Option K.vertices)
    (if hx : x ∈ K.vertices then some ⟨x, hx⟩ else none)
  have hlabel : InjOn label K.vertices := by
    intro x hx y hy he
    have he' := (Fintype.equivFin (Option K.vertices)).injective he
    simp only [dite_eq_left hx, dite_eq_left hy, Option.some.injEq] at he'
    exact congrArg Subtype.val he'
  let w : E → F × (Fin n → ℝ) :=
    fun x => (f x, if x ∈ A then 0 else Pi.single (label x) 1)
  have hwind : ∀ s ∈ K.faces, AffineIndependent ℝ (fun x : s => w x.val) := by
    intro s hs
    let t := s.filter (fun x => x ∈ A)
    let AS : Set s := {x | x.val ∈ A}
    have hp : AffineIndependent ℝ (fun x : AS => f x.val.val) := by
      by_cases ht : t.Nonempty
      · have htD : t ∈ (vertexRestriction K A).faces :=
          ⟨K.down_closed hs (Finset.filter_subset _ _) ht,
            fun x hx => (Finset.mem_filter.mp hx).2⟩
        obtain ⟨B, hB⟩ := hf t htD
        have hBi : InjOn B (convexHull ℝ (t : Set E)) := by
          intro x hx y hy he
          exact hinj t htD hx hy ((hB hx).trans (he.trans (hB hy).symm))
        have hind : AffineIndependent ℝ (fun x : t => f x.val) := by
          convert affineIndependent_of_injOn_convexHull (K.indep htD.1) B hBi using 1
          funext x
          exact hB (subset_convexHull ℝ _ x.property)
        let j : AS ↪ t :=
          ⟨fun x => ⟨x.val.val, Finset.mem_filter.mpr ⟨x.val.property, x.property⟩⟩,
            fun x y he => Subtype.ext (Subtype.ext (congrArg (fun z : t => z.val) he))⟩
        exact hind.comp_embedding j
      · letI : IsEmpty AS := ⟨fun x => ht ⟨x.val.val,
          Finset.mem_filter.mpr ⟨x.val.property, x.property⟩⟩⟩
        exact affineIndependent_of_subsingleton ℝ _
    have hls : Function.Injective (fun x : s => label x.val) := by
      intro x y he
      apply Subtype.ext
      apply hlabel (K.down_closed hs (Finset.singleton_subset_iff.mpr x.property)
        (Finset.singleton_nonempty _))
        (K.down_closed hs (Finset.singleton_subset_iff.mpr y.property) (Finset.singleton_nonempty _)) he
    exact affineIndependent_extraCoordinateVertex AS (fun x : s => f x.val)
      (fun x : s => label x.val) hls hp
  let g : E → F × (Fin n → ℝ) := fun x =>
    if hx : x ∈ K.space then interpolateVertices K hK w ⟨x, hx⟩ else 0
  have hg : ∀ x : K.space, g x.val = interpolateVertices K hK w x := by
    intro x
    simp [g, x.property]
  have hgaff : ∀ s ∈ K.faces, ∃ B : E →ᵃ[ℝ] (F × (Fin n → ℝ)),
      EqOn g B (convexHull ℝ (s : Set E)) ∧ InjOn B (convexHull ℝ (s : Set E)) := by
    intro s hs
    obtain ⟨B, hBv, hB⟩ := interpolateVertices_affineOn K hK w ⟨s, hs⟩
    have hBi : AffineIndependent ℝ (fun x : s => B x.val) := by
      convert hwind s hs using 1
      funext x
      exact hBv x.val x.property
    obtain ⟨C, hCB, _⟩ := exists_affine_inverse_on_affineSpan (K.nonempty_of_mem_faces hs) B hBi
    refine ⟨B, ?_, ?_⟩
    · intro x hx
      exact (hg ⟨x, K.convexHull_subset_space hs hx⟩).trans
        (hB ⟨x, K.convexHull_subset_space hs hx⟩ hx)
    · intro x hx y hy he
      rw [← hCB x (convexHull_subset_affineSpan _ hx),
        ← hCB y (convexHull_subset_affineSpan _ hy), he]
  refine ⟨n, g, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
    obtain ⟨B, hB⟩ := hf s hs
    let C := B.prod (AffineMap.const ℝ E (0 : Fin n → ℝ))
    have hCv : ∀ v ∈ s, C v = w v := by
      intro v hv
      have hvA := hs.2 hv
      change (B v, (0 : Fin n → ℝ)) = (f v, if v ∈ A then 0 else Pi.single (label v) 1)
      rw [ite_eq_left hvA, hB (subset_convexHull ℝ _ hv)]
    have hxK : x ∈ K.space := K.convexHull_subset_space hs.1 hxs
    rw [hg ⟨x, hxK⟩, interpolateVertices_eq_affineMap K hK w ⟨s, hs.1⟩ C hCv ⟨x, hxK⟩ hxs]
    change (B x, 0) = (f x, 0)
    rw [hB hxs]
  · intro s hs
    obtain ⟨B, hB, _⟩ := hgaff s hs
    exact ⟨B, hB⟩
  · intro s hs
    obtain ⟨B, hB, hBi⟩ := hgaff s hs
    intro x hx y hy he
    exact hBi hx hy ((hB hx).symm.trans (he.trans (hB hy)))

def subcomplexFaceCentroids (D : SimplicialComplex ℝ E) : Set E :=
  {x | ∃ s ∈ D.faces, s.centroid ℝ id = x}

theorem vertexRestriction_barycentric_subcomplex
    (K D : SimplicialComplex ℝ E) (hDK : D.faces ⊆ K.faces) :
    vertexRestriction (barycentricSubdivision K) (subcomplexFaceCentroids D) =
      barycentricSubdivision D := by
  classical
  apply SimplicialComplex.ext
  ext s
  constructor
  · rintro ⟨⟨C, hCne, hC, hCK, rfl⟩, hA⟩
    refine ⟨C, hCne, hC, ?_, rfl⟩
    intro t ht
    obtain ⟨u, hu, heq⟩ := hA (mem_chainCentroids.mpr ⟨t, ht, rfl⟩)
    exact centroid_injective_on_faces K (hDK hu) (hCK t ht) heq ▸ hu
  · rintro ⟨C, hCne, hC, hCD, rfl⟩
    refine ⟨⟨C, hCne, hC, fun t ht => hDK (hCD t ht), rfl⟩, ?_⟩
    intro x hx
    obtain ⟨t, ht, rfl⟩ := mem_chainCentroids.mp hx
    exact ⟨t, hCD t ht, rfl⟩

theorem exists_nondegenerate_PL_extension
    (K D : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hDK : D.faces ⊆ K.faces)
    (f : E → F)
    (hf : ∀ s ∈ D.faces, ∃ B : E →ᵃ[ℝ] F, EqOn f B (convexHull ℝ (s : Set E)))
    (hinj : ∀ s ∈ D.faces, InjOn f (convexHull ℝ (s : Set E))) :
    ∃ n : ℕ, ∃ g : E → F × (Fin n → ℝ),
      (∀ x ∈ D.space, g x = (f x, 0)) ∧
      (∀ s ∈ (barycentricSubdivision K).faces,
        ∃ B : E →ᵃ[ℝ] (F × (Fin n → ℝ)), EqOn g B (convexHull ℝ (s : Set E))) ∧
      (∀ s ∈ (barycentricSubdivision K).faces, InjOn g (convexHull ℝ (s : Set E))) := by
  have hfull := vertexRestriction_barycentric_subcomplex K D hDK
  have hfa : ∀ s ∈ (vertexRestriction (barycentricSubdivision K) (subcomplexFaceCentroids D)).faces,
      ∃ B : E →ᵃ[ℝ] F, EqOn f B (convexHull ℝ (s : Set E)) := by
    rw [hfull]
    intro s hs
    obtain ⟨t, ht, hst⟩ := barycentricSubdivision_refines D s hs
    obtain ⟨B, hB⟩ := hf t ht
    exact ⟨B, hB.mono hst⟩
  have hfi : ∀ s ∈ (vertexRestriction (barycentricSubdivision K) (subcomplexFaceCentroids D)).faces,
      InjOn f (convexHull ℝ (s : Set E)) := by
    rw [hfull]
    intro s hs
    obtain ⟨t, ht, hst⟩ := barycentricSubdivision_refines D s hs
    exact (hinj t ht).mono hst
  obtain ⟨n, g, hg, hgaff, hginj⟩ := exists_nondegenerate_extension_of_vertexRestriction
    (barycentricSubdivision K) (barycentricSubdivision_finite_faces K hK)
    (subcomplexFaceCentroids D) f hfa hfi
  rw [hfull, barycentricSubdivision_space] at hg
  exact ⟨n, g, hg, hgaff, hginj⟩

omit [DecidableEq E] in
theorem extension_fiber_iff {n : ℕ} {f : E → F} {g : E → F × (Fin n → ℝ)}
    {D : Set E} (hg : ∀ x ∈ D, g x = (f x, 0)) {x y : E} (hx : x ∈ D) (hy : y ∈ D) :
    g x = g y ↔ f x = f y := by
  classical
  rw [hg x hx, hg y hy, Prod.mk.injEq]
  simp

end

end DifferentialGeometry.Topology.Engulfing
