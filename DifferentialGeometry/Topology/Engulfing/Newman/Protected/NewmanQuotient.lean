import DifferentialGeometry.Topology.Engulfing.Newman.Protected.NewmanProtectedComplex
import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedral.Quotient.LocalGeometricQuotient

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry _root_.Topology
open scoped ContinuousMap

section Pair

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def subcomplexPair (K A B : SimplicialComplex ℝ E)
    (hAK : A.faces ⊆ K.faces) (hBK : B.faces ⊆ K.faces) : SimplicialComplex ℝ E :=
  subcomplexUnion K (fun b : Bool => if b then A else B)
    (fun b => by cases b <;> assumption)

theorem subcomplexPair_faces (K A B : SimplicialComplex ℝ E)
    (hAK : A.faces ⊆ K.faces) (hBK : B.faces ⊆ K.faces) :
    (subcomplexPair K A B hAK hBK).faces = A.faces ∪ B.faces := by
  ext s
  simp only [subcomplexPair, subcomplexUnion, mem_iUnion, Bool.exists_bool,
    Bool.false_eq_true, ite_false, ite_true, mem_union]
  exact or_comm

theorem subcomplexPair_faces_subset (K A B : SimplicialComplex ℝ E)
    (hAK : A.faces ⊆ K.faces) (hBK : B.faces ⊆ K.faces) :
    (subcomplexPair K A B hAK hBK).faces ⊆ K.faces := by
  rw [subcomplexPair_faces]
  exact union_subset hAK hBK

theorem subcomplexPair_space (K A B : SimplicialComplex ℝ E)
    (hAK : A.faces ⊆ K.faces) (hBK : B.faces ⊆ K.faces) :
    (subcomplexPair K A B hAK hBK).space = A.space ∪ B.space := by
  rw [subcomplexPair, subcomplexUnion_space]
  ext x
  simp only [mem_iUnion, Bool.exists_bool, Bool.false_eq_true, ite_false, ite_true, mem_union]
  exact or_comm

end Pair

theorem subtype_preimage_image_map {Z Y : Type*} {S : Set Y}
    (q : Z → S) (A : Set Z) :
    Subtype.val ⁻¹' ((fun x => (q x).1) '' A) = q '' A := by
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    exact ⟨x, hx, Subtype.ext hxy⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

section Quotient

variable {E F M : Type*} [DecidableEq E] [DecidableEq F]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [MetricSpace M]

omit [DecidableEq E] [DecidableEq F] in
theorem exists_newman_quotient_data
    (K L D R P : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hLK : L.faces ⊆ K.faces) (hDK : D.faces ⊆ K.faces)
    (hRK : R.faces ⊆ K.faces) (hPK : P.faces ⊆ K.faces)
    (f : E → F)
    (hf : ∀ s ∈ D.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E)))
    (hinj : ∀ s ∈ D.faces, InjOn f (convexHull ℝ (s : Set E)))
    (F₀ : C(K.space, M))
    (hF : ∀ x y : K.space, x.1 ∈ D.space → y.1 ∈ D.space →
      (F₀ x = F₀ y ↔ f x.1 = f y.1))
    (hfixed : InjOn F₀ (Subtype.val ⁻¹' L.space))
    (hsat : ∀ x : K.space, x.1 ∈ D.space → ∀ y : K.space,
      y.1 ∈ L.space → F₀ y = F₀ x → y.1 ∈ D.space)
    {d p k : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ d + 1)
    (hRd : ∀ s ∈ R.faces, s.card ≤ p + 1) (hPd : ∀ s ∈ P.faces, s.card ≤ k)
    (hkp : k ≤ p + 1) {V : Set M}
    (hcovered : ∀ x : K.space, x.1 ∈ R.space → F₀ x ∈ V) :
    ∃ m : ℕ, ∃ Q LQ DQ : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m)),
      ∃ q : C(K.space, Q.space), ∃ G : C(Q.space, M),
        Q.faces.Finite ∧ (∀ s ∈ Q.faces, s.card ≤ d + 1) ∧
        LQ.faces ⊆ Q.faces ∧ DQ.faces ⊆ Q.faces ∧
        (∀ s ∈ DQ.faces, s.card ≤ p + 1) ∧ IsQuotientMap q ∧
        (∀ x, G (q x) = F₀ x) ∧
        (∀ x y : K.space, q x = q y ↔ x = y ∨
          (x.1 ∈ D.space ∧ y.1 ∈ D.space ∧ f x.1 = f y.1)) ∧
        (Subtype.val ⁻¹' LQ.space = q '' (Subtype.val ⁻¹' (L.space ∪ D.space))) ∧
        (Subtype.val ⁻¹' DQ.space = q '' (Subtype.val ⁻¹' (R.space ∪ P.space))) ∧
        InjOn G (Subtype.val ⁻¹' LQ.space) ∧ engulfingDecomposition Q DQ G V k ∧
        hasFacewiseAffineSections K (subcomplexPair K L D hLK hDK) Q LQ q := by
  classical
  obtain ⟨m, Q, q, G, hQ, hQdim, hq, hrel, hfactor, -, himage, -⟩ :=
    exists_local_geometric_polyhedral_quotient K D hK hDK f hf hinj hd F₀ hF
  let J := subcomplexPair K L D hLK hDK
  obtain ⟨LQ, hLQ, hLQspace, -, hsections⟩ := himage J (subcomplexPair_faces_subset _ _ _ _ _)
  obtain ⟨RQ, hRQ, hRQspace, hRQdim, -⟩ := himage R hRK
  obtain ⟨PQ, hPQ, hPQspace, hPQdim, -⟩ := himage P hPK
  let DQ := subcomplexPair Q RQ PQ hRQ hPQ
  have hLQlift : Subtype.val ⁻¹' LQ.space = q '' (Subtype.val ⁻¹' (L.space ∪ D.space)) := by
    rw [hLQspace, subtype_preimage_image_map]
    congr 1
    rw [show J.space = L.space ∪ D.space from subcomplexPair_space _ _ _ _ _]
    rfl
  have hRQl : Subtype.val ⁻¹' RQ.space = q '' (Subtype.val ⁻¹' R.space) := by
    rw [hRQspace, subtype_preimage_image_map]
    rfl
  have hPQl : Subtype.val ⁻¹' PQ.space = q '' (Subtype.val ⁻¹' P.space) := by
    rw [hPQspace, subtype_preimage_image_map]
    rfl
  have hDQfaces : DQ.faces = RQ.faces ∪ PQ.faces := subcomplexPair_faces _ _ _ _ _
  refine ⟨m, Q, LQ, DQ, q, G, hQ, hQdim, hLQ,
    subcomplexPair_faces_subset _ _ _ _ _, ?_, hq, hfactor, hrel, hLQlift, ?_, ?_, ?_, hsections⟩
  · intro s hs
    rw [hDQfaces] at hs
    exact hs.elim (hRQdim _ hRd s) (fun hs => (hPQdim _ hPd s hs).trans hkp)
  · rw [show DQ.space = RQ.space ∪ PQ.space from subcomplexPair_space _ _ _ _ _,
      preimage_union, hRQl, hPQl, ← image_union, preimage_union]
  · rw [hLQlift, preimage_union]
    exact injOn_descended_protected_union q F₀ G hfactor hfixed hsat
      (fun x hx y hy hxy => (hrel x y).mpr (Or.inr ⟨hx, hy, (hF x y hx hy).mp hxy⟩))
  · refine ⟨RQ, PQ, ?_, ?_, hDQfaces, hPQdim _ hPd, ?_⟩
    · rw [hDQfaces]
      exact subset_union_left
    · rw [hDQfaces]
      exact subset_union_right
    · intro x hx
      have hx' : x ∈ q '' (Subtype.val ⁻¹' R.space) := by
        rw [← hRQl]
        exact hx
      obtain ⟨y, hy, rfl⟩ := hx'
      rw [hfactor]
      exact hcovered y hy

end Quotient

end DifferentialGeometry.Topology.Engulfing
