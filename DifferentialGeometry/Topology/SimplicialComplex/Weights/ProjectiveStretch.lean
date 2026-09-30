import DifferentialGeometry.Topology.SimplicialComplex.Weights.ProjectiveSimplex
import Mathlib.Topology.Maps.Proper.Basic

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry _root_.Topology Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem interpolateVertices_deform_weights (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (w : E → ℝ) (t : ℝ) (x : K.space) :
    interpolateVertices K hK (fun v => t + (1 - t) * w v) x =
      t + (1 - t) * interpolateVertices K hK w x := by
  obtain ⟨s, hs, hx⟩ := SimplicialComplex.mem_space_iff.mp x.2
  obtain ⟨A, hA, hAx⟩ := interpolateVertices_affineOn K hK w ⟨s, hs⟩
  rw [interpolateVertices_eq_affineMap K hK _ ⟨s, hs⟩
    (AffineMap.const ℝ E t + (1 - t) • A) (fun v hv => by simp [hA v hv]) x hx,
    hAx x hx]
  rfl

theorem interpolateVertices_deform_position (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (w : E → ℝ) (t : ℝ) (x : K.space) :
    interpolateVertices K hK (fun v => (t + (1 - t) * w v) • v) x =
      t • x.1 + (1 - t) • interpolateVertices K hK (fun v => w v • v) x := by
  obtain ⟨s, hs, hx⟩ := SimplicialComplex.mem_space_iff.mp x.2
  obtain ⟨A, hA, hAx⟩ := interpolateVertices_affineOn K hK (fun v => w v • v) ⟨s, hs⟩
  rw [interpolateVertices_eq_affineMap K hK _ ⟨s, hs⟩
    (t • AffineMap.id ℝ E + (1 - t) • A) (fun v hv => by
      change t • v + (1 - t) • A v = (t + (1 - t) * w v) • v
      rw [hA v hv, add_smul, mul_smul]) x hx, hAx x hx]
  rfl

theorem isOpen_forall_of_compact {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [CompactSpace Y] (f : X × Y → Z) (hf : Continuous f)
    {U : Set Z} (hU : IsOpen U) : IsOpen {x | ∀ y, f (x, y) ∈ U} := by
  have heq : {x | ∀ y, f (x, y) ∈ U} = (Prod.fst '' (f ⁻¹' Uᶜ))ᶜ := by
    ext x
    constructor
    · intro h
      rintro ⟨⟨x', y⟩, hn, heq⟩
      change x' = x at heq
      subst x'
      exact hn (h y)
    · intro h y
      by_contra hn
      exact h ⟨(x, y), hn, rfl⟩
  rw [heq]
  exact (isClosedMap_fst_of_compactSpace _ (hU.isClosed_compl.preimage hf)).isOpen_compl

theorem exists_projective_stretch_into (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (w : E → ℝ) (hw : ∀ v ∈ K.vertices, 0 ≤ w v)
    {C : Set K.space} (hC : IsCompact C) {U : Set E} (hU : IsOpen U)
    (hpos : ∀ x ∈ C, 0 < interpolateVertices K hK w x)
    (hlim : ∀ x ∈ C, (interpolateVertices K hK w x)⁻¹ •
      interpolateVertices K hK (fun v => w v • v) x ∈ U) :
    ∃ (t : ℝ) (_ht : 0 < t ∧ t ≤ 1)
      (hwt : ∀ v ∈ K.vertices, 0 < t + (1 - t) * w v),
      ∀ x ∈ C, projectiveSimplexMap K hK (fun v => t + (1 - t) * w v) hwt x ∈ U := by
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let T := Icc (0 : ℝ) 1
  let d : T × C → ℝ := fun p => p.1.1 + (1 - p.1.1) * interpolateVertices K hK w p.2.1
  let q : T × C → E := fun p => p.1.1 • p.2.1.1 + (1 - p.1.1) •
    interpolateVertices K hK (fun v => w v • v) p.2.1
  have hd : Continuous d := by
    exact (continuous_subtype_val.comp continuous_fst).add
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        ((interpolateVertices K hK w).continuous.comp
          (continuous_subtype_val.comp continuous_snd)))
  have hq : Continuous q := by
    exact ((continuous_subtype_val.comp continuous_fst).smul
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))).add
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
        ((interpolateVertices K hK (fun v => w v • v)).continuous.comp
          (continuous_subtype_val.comp continuous_snd)))
  have hdpos (p : T × C) : 0 < d p := by
    have hp := hpos p.2.1 p.2.2
    have ht0 := p.1.2.1
    have ht1 := p.1.2.2
    dsimp [d]
    have hm : 0 ≤ (1 - p.1.1) * interpolateVertices K hK w p.2.1 :=
      mul_nonneg (sub_nonneg.mpr ht1) hp.le
    by_cases hzero : p.1.1 = 0
    · simpa [hzero] using hp
    · exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne ht0 (Ne.symm hzero)) hm
  let f : T × C → E := fun p => (d p)⁻¹ • q p
  have hf : Continuous f := (hd.inv₀ (fun p => (hdpos p).ne')).smul hq
  let O : Set T := {t | ∀ x : C, f (t, x) ∈ U}
  have hO : IsOpen O := isOpen_forall_of_compact f hf hU
  let z : T := ⟨0, by simp [T]⟩
  have hz : z ∈ O := by
    intro x
    simpa [f, d, q, z] using hlim x.1 x.2
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO z hz
  let t : ℝ := min (r / 2) (1 / 2)
  have ht : 0 < t ∧ t ≤ 1 := ⟨lt_min (by linarith) (by norm_num),
    (min_le_right _ _).trans (by norm_num)⟩
  have hwt : ∀ v ∈ K.vertices, 0 < t + (1 - t) * w v := fun v hv =>
    add_pos_of_pos_of_nonneg ht.1 (mul_nonneg (sub_nonneg.mpr ht.2) (hw v hv))
  have htO : (⟨t, ht.1.le, ht.2⟩ : T) ∈ O := by
    apply hball
    change dist t 0 < r
    rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
    exact (min_le_left _ _).trans_lt (by linarith)
  refine ⟨t, ht, hwt, fun x hx => ?_⟩
  have h := htO ⟨x, hx⟩
  change (interpolateVertices K hK (fun v => t + (1 - t) * w v) x)⁻¹ •
    interpolateVertices K hK (fun v => (t + (1 - t) * w v) • v) x ∈ U
  rw [interpolateVertices_deform_weights, interpolateVertices_deform_position]
  exact h

theorem exists_ambient_projective_stretch (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (hconv : Convex ℝ K.space)
    (w : E → ℝ) (hw : ∀ v ∈ K.vertices, 0 ≤ w v)
    (hboundary : ∀ v ∈ K.vertices, v ∈ frontier K.space → w v = 1)
    {C : Set K.space} (hC : IsCompact C) {U : Set E} (hU : IsOpen U)
    (hpos : ∀ x ∈ C, 0 < interpolateVertices K hK w x)
    (hlim : ∀ x ∈ C, (interpolateVertices K hK w x)⁻¹ •
      interpolateVertices K hK (fun v => w v • v) x ∈ U) :
    ∃ H : E ≃ₜ E, (∀ x ∉ interior K.space, H x = x) ∧
      Subtype.val '' C ⊆ H '' U ∧
      (∀ s ∈ K.faces, H '' convexHull ℝ (s : Set E) = convexHull ℝ (s : Set E)) := by
  obtain ⟨t, ht, hwt, hmap⟩ := exists_projective_stretch_into K hK w hw hC hU hpos hlim
  let u : E → ℝ := fun v => t + (1 - t) * w v
  have hunit : ∀ v ∈ K.vertices, v ∈ frontier K.space → u v = 1 := by
    intro v hv hvf
    dsimp [u]
    rw [hboundary v hv hvf]
    ring
  obtain ⟨G, hG, hGfix, hGK⟩ := exists_projectiveSimplexHomeomorph_extension K hK hconv u hwt hunit
  have hGface (s : Finset E) (hs : s ∈ K.faces) :
      G '' convexHull ℝ (s : Set E) = convexHull ℝ (s : Set E) := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      let x' : K.space := ⟨x, K.convexHull_subset_space hs hx⟩
      rw [hG x']
      exact projectiveSimplexMap_mem_face K hK u hwt ⟨s, hs⟩ x' hx
    · intro x hx
      let x' : K.space := ⟨x, K.convexHull_subset_space hs hx⟩
      let y := (projectiveSimplexHomeomorph K hK u hwt).symm x'
      have hy : y.1 ∈ convexHull ℝ (s : Set E) :=
        projectiveSimplexMap_mem_face K hK (fun v => (u v)⁻¹)
          (fun v hv => inv_pos.mpr (hwt v hv)) ⟨s, hs⟩ x' hx
      refine ⟨y.1, hy, ?_⟩
      rw [hG y]
      exact congrArg Subtype.val ((projectiveSimplexHomeomorph K hK u hwt).apply_symm_apply x')
  refine ⟨G.symm, ?_, ?_, ?_⟩
  · intro x hx
    apply G.injective
    rw [G.apply_symm_apply, hGfix x hx]
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨G x, ?_, G.symm_apply_apply _⟩
    rw [hG x]
    exact hmap x hx
  · intro s hs
    have heq := congrArg (fun S : Set E => G.symm '' S) (hGface s hs)
    simpa only [image_image, Homeomorph.symm_apply_apply, image_id'] using heq.symm

end DifferentialGeometry.Topology.Engulfing
