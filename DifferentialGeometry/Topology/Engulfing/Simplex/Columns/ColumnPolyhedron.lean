import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedral.Geometry.SegmentThickening
import DifferentialGeometry.Topology.Engulfing.Simplex.SimplexEngulfing

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry
open scoped Pointwise

noncomputable section

set_option linter.unusedSectionVars false

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [DecidableEq E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

namespace SimplexSplit

omit [DecidableEq E] in
theorem prismPoint_add_height (s : SimplexSplit ι) (v : ι → E)
    (z : s.horizontal) (t a : ℝ) :
    s.prismPoint v z (t + a) = s.prismPoint v z t + a • simplexPoint v s.direction := by
  classical
  simp only [prismPoint, simplexPoint, fiberPoint, add_mul, add_smul,
    Finset.sum_add_distrib, mul_smul, Finset.smul_sum]
  abel

omit [DecidableEq E] in
theorem eq_prismPoint_of_mem_simplex (s : SimplexSplit ι) (v : ι → E)
    (hv : AffineIndependent ℝ v) {x : E} (hx : x ∈ convexHull ℝ (range v)) :
    x = s.prismPoint v (s.ambientPrismHomeomorph v hv x).1.2
      (s.ambientPrismHomeomorph v hv x).2 := by
  classical
  have hh := s.ambientPrismHomeomorph_symm_apply v hv (s.ambientPrismHomeomorph v hv x)
  rw [Homeomorph.symm_apply_apply,
    (s.ambientPrismHomeomorph_simplex_iff v hv x).mp hx |>.1] at hh
  simpa only [Submodule.coe_zero, zero_add, prismPoint] using hh

def columnSaturation (s : SimplexSplit ι) (v : ι → E) (hv : AffineIndependent ℝ v)
    (S : Set E) : Set E :=
  {x | x ∈ convexHull ℝ (range v) ∧ ∃ y ∈ S,
    (s.ambientPrismHomeomorph v hv x).1.2 = (s.ambientPrismHomeomorph v hv y).1.2}

def columnBase (s : SimplexSplit ι) (v : ι → E) (hv : AffineIndependent ℝ v)
    (S : Set E) : Set s.base :=
  {z | z.1 ∈ (fun y => (s.ambientPrismHomeomorph v hv y).1.2) '' S}

omit [DecidableEq E] in
theorem isClosed_columnBase (s : SimplexSplit ι) (v : ι → E)
    (hv : AffineIndependent ℝ v) {S : Set E} (hS : IsCompact S) :
    IsClosed (s.columnBase v hv S) := by
  classical
  exact (hS.image (continuous_snd.comp (continuous_fst.comp
    (s.ambientPrismHomeomorph v hv).continuous))).isClosed.preimage continuous_subtype_val

omit [DecidableEq E] in
theorem prismPoint_mem_columnSaturation_iff (s : SimplexSplit ι) (v : ι → E)
    (hv : AffineIndependent ℝ v) (S : Set E) (z : s.base) {t : ℝ}
    (ht : t ∈ Icc (s.lower z.1) (s.upper z.1)) :
    s.prismPoint v z.1 t ∈ s.columnSaturation v hv S ↔ z ∈ s.columnBase v hv S := by
  classical
  change (_ ∧ ∃ y ∈ S, _ = _) ↔ ∃ y ∈ S, _ = _
  rw [s.ambientPrismHomeomorph_apply_prismPoint]
  simp only [s.prismPoint_mem_simplex v hv z ht, true_and]
  exact exists_congr (fun y => and_congr_right (fun _ => eq_comm))

omit [DecidableEq E] in
theorem exists_columnSaturation_eq_thickening (s : SimplexSplit ι) (v : ι → E)
    (hv : AffineIndependent ℝ v) :
    ∃ R : ℝ, R > 0 ∧ ∀ S ⊆ convexHull ℝ (range v),
      s.columnSaturation v hv S = convexHull ℝ (range v) ∩
        (S + segment ℝ (-R • simplexPoint v s.direction) (R • simplexPoint v s.direction)) := by
  classical
  let e := s.ambientPrismHomeomorph v hv
  have hcompact : IsCompact (convexHull ℝ (range v)) :=
    (finite_range v).isCompact_convexHull ℝ
  obtain ⟨B, hB, hbound⟩ :=
    (hcompact.image (continuous_snd.comp e.continuous)).isBounded.exists_pos_norm_le
  have hb (x : E) (hx : x ∈ convexHull ℝ (range v)) : |(e x).2| ≤ B := by
    simpa only [Real.norm_eq_abs, Function.comp_apply] using hbound _ (mem_image_of_mem _ hx)
  let d := simplexPoint v s.direction
  let f : ℝ →ₗ[ℝ] E := LinearMap.toSpanSingleton ℝ E d
  have hseg : segment ℝ (-(2 * B) • d) ((2 * B) • d) =
      (fun a : ℝ => a • d) '' Icc (-(2 * B)) (2 * B) := by
    have hi := image_segment ℝ f.toAffineMap (-(2 * B)) (2 * B)
    rw [segment_eq_Icc (by linarith)] at hi
    exact hi.symm
  refine ⟨2 * B, by positivity, ?_⟩
  intro S hS
  ext x
  constructor
  · rintro ⟨hx, y, hy, hxy⟩
    refine ⟨hx, y, hy, ((e x).2 - (e y).2) • d, ?_, ?_⟩
    · rw [hseg]
      refine mem_image_of_mem _ ?_
      have hbx := (abs_le.mp (hb x hx))
      have hby := (abs_le.mp (hb y (hS hy)))
      constructor <;> linarith
    · change y + ((e x).2 - (e y).2) • simplexPoint v s.direction = x
      calc
        _ = s.prismPoint v (e y).1.2 (e y).2 +
            ((e x).2 - (e y).2) • simplexPoint v s.direction :=
          congrArg (fun u => u + ((e x).2 - (e y).2) • simplexPoint v s.direction)
            (s.eq_prismPoint_of_mem_simplex v hv (hS hy))
        _ = s.prismPoint v (e y).1.2 (e x).2 := by
          rw [← s.prismPoint_add_height, add_sub_cancel]
        _ = x := by rw [← hxy]; exact (s.eq_prismPoint_of_mem_simplex v hv hx).symm
  · rintro ⟨hx, y, hy, z, hz, heq⟩
    rw [hseg] at hz
    obtain ⟨a, _, rfl⟩ := hz
    refine ⟨hx, y, hy, ?_⟩
    have hp : y + a • d = s.prismPoint v (e y).1.2 ((e y).2 + a) := by
      rw [s.prismPoint_add_height, ← s.eq_prismPoint_of_mem_simplex v hv (hS hy)]
    change y + a • d = x at heq
    rw [← heq]
    change (e (y + a • d)).1.2 = (e y).1.2
    rw [hp]
    exact congrArg (fun p => p.1.2) (s.ambientPrismHomeomorph_apply_prismPoint v hv _ _)

omit [DecidableEq E] in
theorem exists_column_complex (s : SimplexSplit ι) (v : ι → E)
    (hv : AffineIndependent ℝ v) (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hinside : K.space ⊆ convexHull ℝ (range v)) {d : ℕ}
    (hd : ∀ t ∈ K.faces, t.card ≤ d + 1) :
    ∃ T : SimplicialComplex ℝ E, T.faces.Finite ∧
      T.space = s.columnSaturation v hv K.space ∧
      (∀ t ∈ T.faces, t.card ≤ d + 2) := by
  classical
  obtain ⟨R, _, hR⟩ := s.exists_columnSaturation_eq_thickening v hv
  obtain ⟨L, hL, hspace, hdim, _⟩ :=
    exists_complex_segment_thickening K hK hd (simplexPoint v s.direction) R
  let V : Finset E := Finset.univ.image v
  have hV : (V : Set E) = range v := by simp [V]
  have hind : AffineIndependent ℝ ((↑) : V → E) := by
    have h := hv.range
    rw [← hV] at h
    exact h
  obtain ⟨J, hJ, _, _, hJdim, hrestr⟩ :=
    exists_subdivision_containing_simplices L hL (fun _ : Unit => V) (fun _ => hind) hdim
  refine ⟨vertexRestriction J (convexHull ℝ (V : Set E)),
    vertexRestriction_finite_faces J _ hJ, ?_, fun t ht => hJdim t ht.1⟩
  rw [hrestr (), hspace, hV, hR K.space hinside, inter_comm]

end SimplexSplit

end

end DifferentialGeometry.Topology.Engulfing
