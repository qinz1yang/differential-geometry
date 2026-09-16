import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphTopology

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLBall.closure_sdiff_eq_of_isPLBall {n m : ℕ} {P A : Set E}
    (hP : IsPLBall (n + 1) P) (hA : IsPLBall m A) (hAP : A ⊆ P) (hm : m < n + 1) :
    closure (P \ A) = P := by
  classical
  obtain ⟨T, hT, hTcard, -, -, -⟩ := exists_affineIndependent_openSimplex_subset
    (n := n) (by simp) (0 : EuclideanSpace ℝ (Fin (n + 1))) Filter.univ_mem
  let Q := convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin (n + 1))))
  have hQ : IsPLBall (n + 1) Q := isPLBall_convexHull_of_affineIndependent T hT hTcard
  obtain ⟨p, hp⟩ := hP
  obtain ⟨q, hq⟩ := hQ
  let f := q ∘ Function.invFunOn p (stdSimplex ℝ (Fin (n + 2)))
  have hf : IsPLHomeomorphOn f P Q := hp.symm.trans hq
  have hA' : IsPLBall m (f '' A) := hA.of_isPLHomeomorphOn (hf.restrict hA.isPolyhedron hAP)
  have hempty : interior (f '' A) = ∅ := hA'.interior_eq_empty_of_lt_finrank (by simpa using hm)
  have hdense : Dense (f '' A)ᶜ := by
    intro x
    rw [closure_compl, hempty]
    simp
  have hsub : interior Q ⊆ closure (Q \ f '' A) := by
    intro x hx
    have h := isOpen_interior.inter_closure ⟨hx, hdense x⟩
    exact closure_mono (inter_subset_inter_left _ interior_subset) h
  have hQ' : IsPLBall (n + 1) Q := ⟨q, hq⟩
  have hclQ : closure (Q \ f '' A) = Q := by
    apply Subset.antisymm (closure_minimal sdiff_subset hQ'.isPolyhedron.isClosed)
    have h := closure_mono hsub
    rwa [hQ'.closure_interior, closure_closure] at h
  have hP' : IsPLBall (n + 1) P := ⟨p, hp⟩
  have hclP : closure (P \ A) ⊆ P := closure_minimal sdiff_subset hP'.isPolyhedron.isClosed
  have himage : f '' closure (P \ A) = Q := by
    rw [hf.image_closure hP'.isPolyhedron.isCompact sdiff_subset,
      hf.bijOn.injOn.image_sdiff_subset hAP, hf.image_eq, hclQ]
  apply Subset.antisymm hclP
  intro x hx
  obtain ⟨y, hy, hyx⟩ := himage.symm.subset (hf.bijOn.mapsTo hx)
  exact hf.bijOn.injOn (hclP hy) hx hyx ▸ hy

theorem IsPLBall.closure_sdiff_iUnion_eq {ι : Type*} {n : ℕ} {P : Set E}
    (hP : IsPLBall (n + 1) P) (d : Finset ι) (A : ι → Set E) (m : ι → ℕ)
    (hA : ∀ i ∈ d, IsPLBall (m i) (A i)) (hAP : ∀ i ∈ d, A i ⊆ P)
    (hm : ∀ i ∈ d, m i < n + 1) : closure (P \ ⋃ i ∈ d, A i) = P := by
  classical
  induction d using Finset.induction_on with
  | empty => simpa using hP.isPolyhedron.isClosed.closure_eq
  | @insert i d hi ih =>
    have hprev : closure (P \ ⋃ j ∈ d, A j) = P := ih
      (fun j hj => hA j (Finset.mem_insert_of_mem hj))
      (fun j hj => hAP j (Finset.mem_insert_of_mem hj))
      (fun j hj => hm j (Finset.mem_insert_of_mem hj))
    have hAi := hA i (Finset.mem_insert_self _ _)
    have hsingle := hP.closure_sdiff_eq_of_isPLBall hAi
      (hAP i (Finset.mem_insert_self _ _)) (hm i (Finset.mem_insert_self _ _))
    have hsub : P \ A i ⊆ closure ((P \ ⋃ j ∈ d, A j) \ A i) := by
      simpa only [hprev, hAi.isPolyhedron.isClosed.closure_eq] using
        (closure_sdiff (s := P \ ⋃ j ∈ d, A j) (t := A i))
    have hcover : closure ((P \ ⋃ j ∈ d, A j) \ A i) = P := by
      apply Subset.antisymm (closure_minimal (sdiff_subset.trans sdiff_subset) hP.isPolyhedron.isClosed)
      have h := closure_mono hsub
      rwa [hsingle, closure_closure] at h
    rw [Finset.set_biUnion_insert, union_comm (A i), ← sdiff_sdiff]
    exact hcover

theorem IsPLBall.closure_sdiff_eq_of_inter_subset_iUnion {ι : Type*} {n : ℕ} {P Q : Set E}
    (hP : IsPLBall (n + 1) P) (d : Finset ι) (A : ι → Set E) (m : ι → ℕ)
    (hA : ∀ i ∈ d, IsPLBall (m i) (A i)) (hAP : ∀ i ∈ d, A i ⊆ P)
    (hm : ∀ i ∈ d, m i < n + 1) (hcover : P ∩ Q ⊆ ⋃ i ∈ d, A i) :
    closure (P \ Q) = P := by
  apply Subset.antisymm (closure_minimal sdiff_subset hP.isPolyhedron.isClosed)
  have hdense := hP.closure_sdiff_iUnion_eq d A m hA hAP hm
  have hsub : P \ (⋃ i ∈ d, A i) ⊆ P \ Q := by
    rintro x ⟨hxP, hxA⟩
    exact ⟨hxP, fun hxQ => hxA (hcover ⟨hxP, hxQ⟩)⟩
  have h := closure_mono hsub
  rwa [hdense] at h

end DifferentialGeometry.Topology.PiecewiseLinear
