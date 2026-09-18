import DifferentialGeometry.Topology.PiecewiseLinear.Star

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem affineIndependent_of_card_eq_of_subset_affineSpan [FiniteDimensional ℝ E]
    {S T : Finset E} {n : ℕ} (hT : AffineIndependent ℝ ((↑) : T → E))
    (hTcard : T.card = n + 1) (hScard : S.card = n + 1)
    (hsub : (T : Set E) ⊆ (affineSpan ℝ (S : Set E) : Set E)) :
    AffineIndependent ℝ ((↑) : S → E) := by
  have hTc : Fintype.card T = n + 1 := (Fintype.card_coe T).trans hTcard
  have hSc : Fintype.card S = n + 1 := (Fintype.card_coe S).trans hScard
  have hTr : Set.range ((↑) : T → E) = (T : Set E) := by ext x; simp
  have hSr : Set.range ((↑) : S → E) = (S : Set E) := by ext x; simp
  have h1 : Module.finrank ℝ (vectorSpan ℝ (T : Set E)) = n := by
    have h := (affineIndependent_iff_finrank_vectorSpan_eq ℝ ((↑) : T → E) hTc).mp hT
    rwa [hTr] at h
  have h2 : vectorSpan ℝ (T : Set E) ≤ vectorSpan ℝ (S : Set E) := by
    have hle := AffineSubspace.direction_le (affineSpan_le.mpr hsub)
    rwa [direction_affineSpan, direction_affineSpan] at hle
  refine (affineIndependent_iff_le_finrank_vectorSpan ℝ ((↑) : S → E) hSc).mpr ?_
  rw [hSr, ← h1]
  exact Submodule.finrank_mono h2

theorem affineIndependent_insert_of_mem_affineSpan_pair [FiniteDimensional ℝ E] [DecidableEq E]
    {S : Finset E} {a b u : E} (hS : AffineIndependent ℝ ((↑) : ↥(insert a S) → E))
    (ha : a ∉ S) (hb : b ∉ S) (hu : u ∈ S) (hmem : a ∈ line[ℝ, u, b]) :
    AffineIndependent ℝ ((↑) : ↥(insert b S) → E) := by
  refine affineIndependent_of_card_eq_of_subset_affineSpan (n := S.card) hS
    (Finset.card_insert_of_notMem ha) (Finset.card_insert_of_notMem hb) ?_
  intro x hx
  rw [Finset.coe_insert, Set.mem_insert_iff] at hx
  rcases hx with rfl | hx
  · refine affineSpan_mono ℝ ?_ hmem
    intro y hy
    rcases Set.mem_insert_iff.mp hy with hy' | hy'
    · rw [hy']
      exact Finset.mem_coe.mpr (Finset.mem_insert_of_mem hu)
    · rw [Set.mem_singleton_iff.mp hy']
      exact Finset.mem_coe.mpr (Finset.mem_insert_self b S)
  · exact subset_affineSpan ℝ _ (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hx))

theorem affineIndependent_insert_midpoint_outer [FiniteDimensional ℝ E] [DecidableEq E]
    {F : Finset E} {c d m : E}
    (hT₁ : AffineIndependent ℝ ((↑) : ↥(insert c (insert m F)) → E))
    (hm : c + d = m + m) (hmcF : m ∉ insert c F) (hdcF : d ∉ insert c F) :
    AffineIndependent ℝ ((↑) : ↥(insert c (insert d F)) → E) := by
  rw [Finset.insert_comm] at hT₁
  rw [Finset.insert_comm]
  refine affineIndependent_insert_of_mem_affineSpan_pair hT₁ hmcF hdcF
    (Finset.mem_insert_self c F) ?_
  have hd : d = m + m - c := by rw [← hm]; abel
  subst hd
  have h := smul_vsub_vadd_mem_affineSpan_pair (k := ℝ) (2⁻¹ : ℝ) c (m + m - c)
  have he : (2⁻¹ : ℝ) • ((m + m - c) -ᵥ c) +ᵥ c = m := by
    simp only [vsub_eq_sub, vadd_eq_add]
    module
  rwa [he] at h

theorem affineIndependent_insert_midpoint_inner [FiniteDimensional ℝ E] [DecidableEq E]
    {F : Finset E} {c d m : E}
    (hT₁ : AffineIndependent ℝ ((↑) : ↥(insert c (insert m F)) → E))
    (hm : c + d = m + m) (hcmF : c ∉ insert m F) (hdmF : d ∉ insert m F) :
    AffineIndependent ℝ ((↑) : ↥(insert d (insert m F)) → E) := by
  refine affineIndependent_insert_of_mem_affineSpan_pair hT₁ hcmF hdmF
    (Finset.mem_insert_self m F) ?_
  have hc : c = m + m - d := by rw [← hm]; abel
  have h := smul_vsub_rev_vadd_mem_affineSpan_pair (k := ℝ) (2 : ℝ) m d
  have he : (2 : ℝ) • (m -ᵥ d) +ᵥ d = c := by
    rw [hc]
    simp only [vsub_eq_sub, vadd_eq_add]
    module
  rwa [he] at h

end DifferentialGeometry.Topology.PiecewiseLinear
