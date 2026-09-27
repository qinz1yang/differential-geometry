import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Spectrum

set_option autoImplicit false

noncomputable section

open scoped ComplexOrder

namespace LinearMap.IsSymmetric

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [FiniteDimensional 𝕜 V] {A : V →ₗ[𝕜] V}

theorem card_filter_eigenvalues_ne_zero
    (hA : A.IsSymmetric) {n : ℕ} (hdim : Module.finrank 𝕜 V = n) :
    Finset.card {i : Fin n | hA.eigenvalues hdim i ≠ 0} = Module.finrank 𝕜 A.range := by
  classical
  have hcount := hA.card_filter_eigenvalues_eq hdim 0
  rw [Module.End.eigenspace_zero] at hcount
  simp only [RCLike.ofReal_eq_zero] at hcount
  have htotal := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (fun i : Fin n => hA.eigenvalues hdim i = 0)
  rw [Finset.card_univ, Fintype.card_fin, hcount] at htotal
  change Module.finrank 𝕜 A.ker + Finset.card {i : Fin n | hA.eigenvalues hdim i ≠ 0} = n at htotal
  have hrank := A.finrank_range_add_finrank_ker
  rw [hdim] at hrank
  omega

theorem eigenvalues_eq_zero_of_finrank_range_eq_zero
    (hA : A.IsSymmetric) {n : ℕ} (hdim : Module.finrank 𝕜 V = n)
    (hrank : Module.finrank 𝕜 A.range = 0) (i : Fin n) :
    hA.eigenvalues hdim i = 0 := by
  classical
  have hcard := hA.card_filter_eigenvalues_ne_zero hdim
  rw [hrank, Finset.card_eq_zero] at hcard
  by_contra hne
  have hi : i ∈ Finset.filter (fun j => hA.eigenvalues hdim j ≠ 0) Finset.univ := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
  rw [hcard] at hi
  exact Finset.notMem_empty i hi

end LinearMap.IsSymmetric

namespace LinearMap.IsPositive

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [FiniteDimensional 𝕜 V] {A : V →ₗ[𝕜] V}

theorem eigenvalues_of_finrank_range_eq_one
    (hA : A.IsPositive) {n : ℕ} [NeZero n] (hdim : Module.finrank 𝕜 V = n)
    (hrank : Module.finrank 𝕜 A.range = 1) :
    0 < hA.isSymmetric.eigenvalues hdim 0 ∧
      ∀ i : Fin n, i ≠ 0 → hA.isSymmetric.eigenvalues hdim i = 0 := by
  classical
  let d := hA.isSymmetric.eigenvalues hdim
  have hcount : Finset.card {i : Fin n | d i ≠ 0} = 1 :=
    (hA.isSymmetric.card_filter_eigenvalues_ne_zero hdim).trans hrank
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcount
  have hjne : d j ≠ 0 := by
    have hjmem : j ∈ Finset.filter (fun i => d i ≠ 0) Finset.univ := by
      rw [hj]
      exact Finset.mem_singleton_self j
    exact (Finset.mem_filter.mp hjmem).2
  have hjpos : 0 < d j :=
    lt_of_le_of_ne (hA.nonneg_eigenvalues hdim j) hjne.symm
  have h0pos : 0 < d 0 :=
    lt_of_lt_of_le hjpos (hA.isSymmetric.eigenvalues_antitone hdim (Fin.zero_le j))
  have hjzero : j = 0 := by
    have hmem : (0 : Fin n) ∈ Finset.filter (fun i => d i ≠ 0) Finset.univ := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact h0pos.ne'
    rw [hj, Finset.mem_singleton] at hmem
    exact hmem.symm
  refine ⟨h0pos, fun i hi => ?_⟩
  by_contra hne
  have hmem : i ∈ Finset.filter (fun i => d i ≠ 0) Finset.univ := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
  rw [hj, hjzero, Finset.mem_singleton] at hmem
  exact hi hmem

theorem eigenvalues_pos_of_finrank_range_eq
    (hA : A.IsPositive) {n : ℕ} (hdim : Module.finrank 𝕜 V = n)
    (hrank : Module.finrank 𝕜 A.range = n) (i : Fin n) :
    0 < hA.isSymmetric.eigenvalues hdim i := by
  classical
  have hcount := hA.isSymmetric.card_filter_eigenvalues_eq hdim 0
  rw [Module.End.eigenspace_zero] at hcount
  simp only [RCLike.ofReal_eq_zero] at hcount
  have hker := A.finrank_range_add_finrank_ker
  rw [hrank, hdim] at hker
  have hc : Finset.card {i : Fin n | hA.isSymmetric.eigenvalues hdim i = 0} = 0 := by omega
  have hempty := Finset.card_eq_zero.mp hc
  have hne : hA.isSymmetric.eigenvalues hdim i ≠ 0 := by
    intro hz
    have hi : i ∈ Finset.filter (fun i => hA.isSymmetric.eigenvalues hdim i = 0) Finset.univ := by
      simp [hz]
    rw [hempty] at hi
    exact Finset.notMem_empty i hi
  exact lt_of_le_of_ne (hA.nonneg_eigenvalues hdim i) hne.symm

end LinearMap.IsPositive

namespace Matrix

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]

private theorem rank_eq_finrank_range_toEuclideanLin
    (A : Matrix ι ι 𝕜) :
    A.rank = Module.finrank 𝕜 A.toEuclideanLin.range :=
  Matrix.rank_eq_finrank_range_toLin A (PiLp.basisFun 2 𝕜 ι) (PiLp.basisFun 2 𝕜 ι)

theorem PosSemidef.eigenvalues₀_of_rank_eq_one
    [Nonempty ι] {A : Matrix ι ι 𝕜} (hA : A.PosSemidef) (hrank : A.rank = 1) :
    0 < hA.isHermitian.eigenvalues₀ 0 ∧
      ∀ i : Fin (Fintype.card ι), i ≠ 0 → hA.isHermitian.eigenvalues₀ i = 0 := by
  have hpos : A.toEuclideanLin.IsPositive := Matrix.isPositive_toEuclideanLin_iff.mpr hA
  exact hpos.eigenvalues_of_finrank_range_eq_one finrank_euclideanSpace
    ((rank_eq_finrank_range_toEuclideanLin A).symm.trans hrank)

theorem PosSemidef.eigenvalues₀_pos_of_rank_eq_card
    {A : Matrix ι ι 𝕜} (hA : A.PosSemidef) (hrank : A.rank = Fintype.card ι)
    (i : Fin (Fintype.card ι)) : 0 < hA.isHermitian.eigenvalues₀ i := by
  have hpos : A.toEuclideanLin.IsPositive := Matrix.isPositive_toEuclideanLin_iff.mpr hA
  exact hpos.eigenvalues_pos_of_finrank_range_eq finrank_euclideanSpace
    ((rank_eq_finrank_range_toEuclideanLin A).symm.trans hrank) i

theorem IsHermitian.eigenvalues₀_eq_zero_of_rank_eq_zero
    {A : Matrix ι ι 𝕜} (hA : A.IsHermitian) (hrank : A.rank = 0)
    (i : Fin (Fintype.card ι)) : hA.eigenvalues₀ i = 0 := by
  have hsym : A.toEuclideanLin.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  exact hsym.eigenvalues_eq_zero_of_finrank_range_eq_zero finrank_euclideanSpace
    ((rank_eq_finrank_range_toEuclideanLin A).symm.trans hrank) i

end Matrix
