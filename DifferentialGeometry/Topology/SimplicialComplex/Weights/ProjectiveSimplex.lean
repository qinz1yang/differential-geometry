import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedral.Maps.PiecewiseLinear
import DifferentialGeometry.Topology.PiecewiseLinear.Approximation.PiecewiseApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.Approximation.Perturbation.VertexPerturbation
import DifferentialGeometry.Topology.Homeomorph.ExtensionByIdentity

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry _root_.Topology
open scoped BigOperators

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem interpolateVertices_eq_sum (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (w : E → F) (s : K.faces) (x : K.space) (a : E → ℝ)
    (ha0 : ∀ v ∈ s.1, 0 ≤ a v) (ha : ∑ v ∈ s.1, a v = 1) (hx : ∑ v ∈ s.1, a v • v = x.1) :
    interpolateVertices K hK w x = ∑ v ∈ s.1, a v • w v := by
  obtain ⟨A, hA, hface⟩ := interpolateVertices_affineOn K hK w s
  have hax : s.1.affineCombination ℝ id a = x.1 := by
    simpa only [Finset.affineCombination_eq_linear_combination _ _ _ ha, id_eq] using hx
  have heq : interpolateVertices K hK w x = A x.1 :=
    hface x (Finset.mem_convexHull'.mpr ⟨a, ha0, ha, hx⟩)
  rw [heq, ← hax, Finset.map_affineCombination _ _ _ ha]
  rw [Finset.affineCombination_eq_linear_combination _ _ _ ha]
  exact Finset.sum_congr rfl (fun v hv => by rw [Function.comp_apply, id_eq, hA v hv])

theorem interpolateVertices_pos (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (w : E → ℝ) (hw : ∀ v ∈ K.vertices, 0 < w v) (x : K.space) :
    0 < interpolateVertices K hK w x := by
  obtain ⟨s, hs, hx⟩ := SimplicialComplex.mem_space_iff.mp x.2
  have hsub : w '' (s : Set E) ⊆ Ioi 0 := by
    rintro _ ⟨v, hv, rfl⟩
    exact hw v (K.down_closed hs (Finset.singleton_subset_iff.mpr hv)
      (Finset.singleton_nonempty v))
  exact (convexHull_min hsub (convex_Ioi (0 : ℝ)))
    (interpolateVertices_mem_convexHull K hK w ⟨s, hs⟩ x hx)

noncomputable def projectiveSimplexMap (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (w : E → ℝ) (hw : ∀ v ∈ K.vertices, 0 < w v) : C(K.space, E) where
  toFun x := (interpolateVertices K hK w x)⁻¹ •
    interpolateVertices K hK (fun v => w v • v) x
  continuous_toFun := by
    exact ((interpolateVertices K hK w).continuous.inv₀
      (fun x => (interpolateVertices_pos K hK w hw x).ne')).smul
      (interpolateVertices K hK (fun v => w v • v)).continuous

theorem projectiveSimplexMap_eq_sum (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (w : E → ℝ) (hw : ∀ v ∈ K.vertices, 0 < w v)
    (s : K.faces) (x : K.space) (a : E → ℝ)
    (ha0 : ∀ v ∈ s.1, 0 ≤ a v) (ha : ∑ v ∈ s.1, a v = 1)
    (hx : ∑ v ∈ s.1, a v • v = x.1) :
    projectiveSimplexMap K hK w hw x =
      ∑ v ∈ s.1, (a v * w v / interpolateVertices K hK w x) • v := by
  change (interpolateVertices K hK w x)⁻¹ •
    interpolateVertices K hK (fun v => w v • v) x = _
  rw [interpolateVertices_eq_sum K hK (fun v => w v • v) s x a ha0 ha hx,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  simp only [smul_smul]
  congr 1
  rw [div_eq_mul_inv]
  ring

theorem projectiveSimplexMap_weights (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (w : E → ℝ) (hw : ∀ v ∈ K.vertices, 0 < w v)
    (s : K.faces) (x : K.space) (a : E → ℝ)
    (ha0 : ∀ v ∈ s.1, 0 ≤ a v) (ha : ∑ v ∈ s.1, a v = 1)
    (hx : ∑ v ∈ s.1, a v • v = x.1) :
    (∀ v ∈ s.1, 0 ≤ a v * w v / interpolateVertices K hK w x) ∧
      ∑ v ∈ s.1, a v * w v / interpolateVertices K hK w x = 1 := by
  have hD := interpolateVertices_pos K hK w hw x
  constructor
  · intro v hv
    exact div_nonneg (mul_nonneg (ha0 v hv) (hw v (K.down_closed s.2
      (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v))).le) hD.le
  · rw [← Finset.sum_div]
    have heq := interpolateVertices_eq_sum K hK w s x a ha0 ha hx
    simp only [smul_eq_mul] at heq
    rw [← heq, div_self hD.ne']

theorem projectiveSimplexMap_mem_face (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (w : E → ℝ) (hw : ∀ v ∈ K.vertices, 0 < w v)
    (s : K.faces) (x : K.space) (hx : x.1 ∈ convexHull ℝ (s.1 : Set E)) :
    projectiveSimplexMap K hK w hw x ∈ convexHull ℝ (s.1 : Set E) := by
  obtain ⟨a, ha0, ha, hax⟩ := Finset.mem_convexHull'.mp hx
  obtain ⟨hb0, hb⟩ := projectiveSimplexMap_weights K hK w hw s x a ha0 ha hax
  exact Finset.mem_convexHull'.mpr ⟨_, hb0, hb,
    (projectiveSimplexMap_eq_sum K hK w hw s x a ha0 ha hax).symm⟩

theorem projectiveSimplexMap_mem_space (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (w : E → ℝ) (hw : ∀ v ∈ K.vertices, 0 < w v) (x : K.space) :
    projectiveSimplexMap K hK w hw x ∈ K.space := by
  obtain ⟨s, hs, hx⟩ := SimplicialComplex.mem_space_iff.mp x.2
  exact K.convexHull_subset_space hs (projectiveSimplexMap_mem_face K hK w hw ⟨s, hs⟩ x hx)

noncomputable def projectiveSimplexSelfMap (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (w : E → ℝ) (hw : ∀ v ∈ K.vertices, 0 < w v) :
    C(K.space, K.space) :=
  ⟨fun x => ⟨projectiveSimplexMap K hK w hw x, projectiveSimplexMap_mem_space K hK w hw x⟩,
    (projectiveSimplexMap K hK w hw).continuous.subtype_mk _⟩

theorem projectiveSimplexSelfMap_inv (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (w : E → ℝ) (hw : ∀ v ∈ K.vertices, 0 < w v)
    (x : K.space) :
    projectiveSimplexSelfMap K hK (fun v => (w v)⁻¹)
      (fun v hv => inv_pos.mpr (hw v hv)) (projectiveSimplexSelfMap K hK w hw x) = x := by
  obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp x.2
  obtain ⟨a, ha0, ha, hax⟩ := Finset.mem_convexHull'.mp hxs
  let D := interpolateVertices K hK w x
  have hD : 0 < D := interpolateVertices_pos K hK w hw x
  let b : E → ℝ := fun v => a v * w v / D
  obtain ⟨hb0, hb⟩ := projectiveSimplexMap_weights K hK w hw ⟨s, hs⟩ x a ha0 ha hax
  let y := projectiveSimplexSelfMap K hK w hw x
  have hby : ∑ v ∈ s, b v • v = y.1 :=
    (projectiveSimplexMap_eq_sum K hK w hw ⟨s, hs⟩ x a ha0 ha hax).symm
  have hterm (v : E) (hv : v ∈ s) : b v * (w v)⁻¹ = a v / D := by
    have hwv := (hw v (K.down_closed hs (Finset.singleton_subset_iff.mpr hv)
      (Finset.singleton_nonempty v))).ne'
    dsimp [b]
    field_simp
  have hden : interpolateVertices K hK (fun v => (w v)⁻¹) y = D⁻¹ := by
    rw [interpolateVertices_eq_sum K hK _ ⟨s, hs⟩ y b hb0 hb hby]
    simp only [smul_eq_mul]
    calc
      ∑ v ∈ s, b v * (w v)⁻¹ = ∑ v ∈ s, a v / D := Finset.sum_congr rfl hterm
      _ = D⁻¹ := by rw [← Finset.sum_div, ha, one_div]
  have hnum : interpolateVertices K hK (fun v => (w v)⁻¹ • v) y = D⁻¹ • x.1 := by
    rw [interpolateVertices_eq_sum K hK _ ⟨s, hs⟩ y b hb0 hb hby, ← hax, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    rw [smul_smul, smul_smul, hterm v hv, div_eq_mul_inv, mul_comm]
  apply Subtype.ext
  change (interpolateVertices K hK (fun v => (w v)⁻¹) y)⁻¹ •
    interpolateVertices K hK (fun v => (w v)⁻¹ • v) y = x.1
  rw [hden, hnum, inv_inv, smul_smul, mul_inv_cancel₀ hD.ne', one_smul]

noncomputable def projectiveSimplexHomeomorph (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (w : E → ℝ) (hw : ∀ v ∈ K.vertices, 0 < w v) :
    K.space ≃ₜ K.space where
  toFun := projectiveSimplexSelfMap K hK w hw
  invFun := projectiveSimplexSelfMap K hK (fun v => (w v)⁻¹)
    (fun v hv => inv_pos.mpr (hw v hv))
  left_inv := projectiveSimplexSelfMap_inv K hK w hw
  right_inv := by
    intro x
    simpa only [inv_inv] using projectiveSimplexSelfMap_inv K hK (fun v => (w v)⁻¹)
      (fun v hv => inv_pos.mpr (hw v hv)) x
  continuous_toFun := (projectiveSimplexSelfMap K hK w hw).continuous
  continuous_invFun := (projectiveSimplexSelfMap K hK _ _).continuous

theorem interpolateVertices_eq_affineMap_on_frontier (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (hconv : Convex ℝ K.space) (w : E → F) (A : E →ᵃ[ℝ] F)
    (hfix : ∀ v ∈ K.vertices, v ∈ frontier K.space → w v = A v)
    (x : K.space) (hx : x.1 ∈ frontier K.space) :
    interpolateVertices K hK w x = A x.1 := by
  obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp x.2
  obtain ⟨B, hB, hface⟩ := interpolateVertices_affineOn K hK w ⟨s, hs⟩
  rw [hface x hxs]
  apply sub_eq_zero.mp
  exact affineMap_zero_on_convexHull_frontier hconv (K.subset_space hs) (B - A)
    (fun v hv hvf => by
      change B v - A v = 0
      rw [hB v hv, hfix v (K.down_closed hs (Finset.singleton_subset_iff.mpr hv)
        (Finset.singleton_nonempty v)) hvf, sub_self]) hxs hx

theorem projectiveSimplexHomeomorph_fixed_frontier (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (hconv : Convex ℝ K.space)
    (w : E → ℝ) (hw : ∀ v ∈ K.vertices, 0 < w v)
    (hfix : ∀ v ∈ K.vertices, v ∈ frontier K.space → w v = 1)
    (x : K.space) (hx : x.1 ∈ frontier K.space) :
    projectiveSimplexHomeomorph K hK w hw x = x := by
  have hden : interpolateVertices K hK w x = 1 :=
    interpolateVertices_eq_affineMap_on_frontier K hK hconv w (AffineMap.const ℝ E 1)
      hfix x hx
  have hnum : interpolateVertices K hK (fun v => w v • v) x = x.1 :=
    interpolateVertices_eq_affineMap_on_frontier K hK hconv _ (AffineMap.id ℝ E)
      (fun v hv hvf => by simp only [hfix v hv hvf, one_smul, AffineMap.id_apply]) x hx
  apply Subtype.ext
  change (interpolateVertices K hK w x)⁻¹ •
    interpolateVertices K hK (fun v => w v • v) x = x.1
  rw [hden, hnum, inv_one, one_smul]

theorem exists_projectiveSimplexHomeomorph_extension (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (hconv : Convex ℝ K.space)
    (w : E → ℝ) (hw : ∀ v ∈ K.vertices, 0 < w v)
    (hfix : ∀ v ∈ K.vertices, v ∈ frontier K.space → w v = 1) :
    ∃ H : E ≃ₜ E,
      (∀ x : K.space, H x = projectiveSimplexMap K hK w hw x) ∧
      (∀ x ∉ interior K.space, H x = x) ∧ H '' K.space = K.space := by
  let hclosed := (isCompact_space_of_finite_faces K hK).isClosed
  let e := projectiveSimplexHomeomorph K hK w hw
  let he := projectiveSimplexHomeomorph_fixed_frontier K hK hconv w hw hfix
  let H := extendHomeomorphClosed hclosed e he
  refine ⟨H, fun x => extendHomeomorphClosed_apply hclosed e he x,
    fun x hx => extendHomeomorphClosed_eq_self_of_not_mem_interior hclosed e he hx, ?_⟩
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have heq := extendHomeomorphClosed_apply hclosed e he ⟨x, hx⟩
    exact heq.symm ▸ (e ⟨x, hx⟩).2
  · intro x hx
    refine ⟨e.symm ⟨x, hx⟩, (e.symm ⟨x, hx⟩).2, ?_⟩
    rw [extendHomeomorphClosed_apply, e.apply_symm_apply]

end DifferentialGeometry.Topology.Engulfing
