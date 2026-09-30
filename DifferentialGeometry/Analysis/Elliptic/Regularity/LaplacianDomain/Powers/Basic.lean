import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Defs

noncomputable section

open Manifold MeasureTheory
open scoped ContDiff

namespace DifferentialGeometry.Analysis.Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

theorem laplacianDomainPow_le_of_le
    (g : SmoothRiemannianMetric I M) {k j : ℕ} (hjk : j ≤ k)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    u_h ∈ laplacianDomainPow (I := I) (M := M) g j := by
  classical
  obtain ⟨d, hd⟩ : ∃ d : ℕ, k = j + d := Nat.exists_eq_add_of_le hjk
  subst hd
  clear hjk
  induction d with
  | zero =>
      simpa using hu_h
  | succ d ih =>
      have h_succ_eq : j + (d + 1) = (j + d) + 1 := by ring
      rw [h_succ_eq] at hu_h
      have hu_h_jd : u_h ∈ laplacianDomainPow (I := I) (M := M) g (j + d) := by
        rw [DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_succ_mem_iff] at hu_h
        obtain ⟨f, hf⟩ := hu_h
        by_cases h_jd_zero : j + d = 0
        · rw [h_jd_zero]
          rw [DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_zero]
          exact Submodule.mem_top
        · obtain ⟨n, hn⟩ : ∃ n : ℕ, j + d = n + 1 :=
            Nat.exists_eq_succ_of_ne_zero h_jd_zero
          rw [hn] at hf ⊢
          rw [DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2_succ_apply] at hf
          rw [DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_succ_mem_iff]
          refine ⟨DifferentialGeometry.Analysis.Laplacian.resolventL2
            (I := I) (M := M) g f, ?_⟩
          rw [hf]
          congr 1
          have h1 : DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2
              (I := I) (M := M) g n
              (DifferentialGeometry.Analysis.Laplacian.resolventL2
                (I := I) (M := M) g f) =
            DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2
              (I := I) (M := M) g (n + 1) f := by
            rw [DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2_add]
            rfl
          have h2 : DifferentialGeometry.Analysis.Laplacian.resolventL2
              (I := I) (M := M) g
              (DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2
                (I := I) (M := M) g n f) =
            DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2
              (I := I) (M := M) g (n + 1) f := by
            rw [DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2_succ_apply]
          rw [h1, h2]
      exact ih hu_h_jd

theorem laplacianDomainPow_succ_exists_resolvent_preimage
    (g : SmoothRiemannianMetric I M) {k : ℕ} (hk_pos : 1 ≤ k)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g (k + 1)) :
    ∃ v_h : H1Compl (I := I) (M := M) g,
      v_h ∈ laplacianDomainPow (I := I) (M := M) g k ∧
      H1ComplToLp (I := I) (M := M) g v_h =
        laplacianDomain.preimage (I := I) (M := M) g
          ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g k hu_h⟩ := by
  classical
  rw [laplacianDomainPow_succ_mem_iff] at hu_h
  obtain ⟨f, hf⟩ := hu_h
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  have h_apply :
      iteratedResolventL2 (I := I) (M := M) g (k' + 1) f =
        resolventL2 (I := I) (M := M) g
          (iteratedResolventL2 (I := I) (M := M) g k' f) :=
    iteratedResolventL2_succ_apply (I := I) (M := M) g k' f
  have h_resolventL2_apply : resolventL2 (I := I) (M := M) g
        (iteratedResolventL2 (I := I) (M := M) g k' f) =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (iteratedResolventL2 (I := I) (M := M) g k' f)) := by
    rfl
  refine ⟨resolvent (I := I) (M := M) g
    (iteratedResolventL2 (I := I) (M := M) g k' f), ?_, ?_⟩
  · rw [laplacianDomainPow_succ_mem_iff]
    refine ⟨f, rfl⟩
  · apply resolvent_injective (I := I) (M := M) g
    rw [resolvent_laplacianDomain_preimage_eq]
    rw [← h_resolventL2_apply]
    rw [← h_apply]
    exact hf.symm

end DifferentialGeometry.Analysis.Laplacian

end
