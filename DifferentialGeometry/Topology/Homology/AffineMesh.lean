import DifferentialGeometry.Topology.Homology.BarycenterBounds



noncomputable section

open CategoryTheory Set Module

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]



def affineSingularMesh (n : ℕ) (A : Set E) (δ : ℝ) :
    Submodule ℤ ((integralSingularChains E).X n) :=
  Submodule.span ℤ {c | ∃ v : Fin (n + 1) → E,
    (∀ i, v i ∈ A) ∧ Metric.diam (range v) ≤ δ ∧ c = affineSingularChain n v}


theorem affineSingularMesh_generator (n : ℕ) (A : Set E) (δ : ℝ) (v : Fin (n + 1) → E)
    (hv : ∀ i, v i ∈ A) (hd : Metric.diam (range v) ≤ δ) :
    affineSingularChain n v ∈ affineSingularMesh n A δ :=
  Submodule.subset_span ⟨v, hv, hd, rfl⟩


theorem affineSingularMesh_mono (n : ℕ) {A B : Set E} {δ ε : ℝ} (hAB : A ⊆ B) (hδε : δ ≤ ε) :
    affineSingularMesh n A δ ≤ affineSingularMesh n B ε := by
  apply Submodule.span_le.mpr
  rintro _ ⟨v, hv, hd, rfl⟩
  exact affineSingularMesh_generator n B ε v (fun i => hAB (hv i)) (hd.trans hδε)


theorem affineSingularMesh_le (n : ℕ) (A : Set E) (δ : ℝ) :
    affineSingularMesh n A δ ≤ affineSingularChainsIn n A := by
  apply Submodule.span_le.mpr
  rintro _ ⟨v, hv, _, rfl⟩
  exact affineSingularChain_mem n A v hv


theorem affineSingularChainsIn_zero_mesh (A : Set E) :
    affineSingularChainsIn 0 A ≤ affineSingularMesh 0 A 0 := by
  apply Submodule.span_le.mpr
  rintro _ ⟨v, hv, rfl⟩
  apply affineSingularMesh_generator 0 A 0 v hv
  have hr : range v = {v 0} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      rfl
    · rintro rfl
      exact ⟨0, rfl⟩
  rw [hr, Metric.diam_singleton]



theorem affineSingularMesh_cone (n : ℕ) {A : Set E} {δ : ℝ} {a : E}
    (ha : a ∈ A) (hδ : 0 ≤ δ) (hD : ∀ x ∈ A, dist a x ≤ δ)
    {c : (integralSingularChains E).X n} (hc : c ∈ affineSingularMesh n A δ) :
    affineSingularCone n a c ∈ affineSingularMesh (n + 1) A δ := by
  have h : affineSingularMesh n A δ ≤
      Submodule.comap (affineSingularCone n a) (affineSingularMesh (n + 1) A δ) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨v, hv, hd, rfl⟩
    change affineSingularCone n a (affineSingularChain n v) ∈ affineSingularMesh (n + 1) A δ
    rw [affineSingularCone_affine]
    apply affineSingularMesh_generator (n + 1) A δ (Fin.cons a v) (Fin.cases ha hv)
    apply Metric.diam_le_of_forall_dist_le hδ
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · simpa using hδ
      · exact hD (v j) (hv j)
    · refine Fin.cases ?_ (fun j => ?_) j
      · simpa only [Fin.cons_zero, Fin.cons_succ, dist_comm] using hD (v i) (hv i)
      · exact (Metric.dist_le_diam_of_mem (finite_range v).isBounded ⟨i, rfl⟩ ⟨j, rfl⟩).trans hd
  exact h hc

end DifferentialGeometry.Topology
