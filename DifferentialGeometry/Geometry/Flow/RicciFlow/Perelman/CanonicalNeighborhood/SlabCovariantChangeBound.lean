import DifferentialGeometry.Geometry.Metric.Convergence.Coordinates.ConnectionComparison

set_option autoImplicit false
noncomputable section
open Bundle Set
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M] [IsManifold I 1 M]
  {Idx : Type*} [Fintype Idx]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold I 1 M] [T2Space M] in
private theorem slabChange_sum_smooth {ι : Type*} {u : Set M} (s : Finset ι)
    (F : ι → M → ℝ)
    (hF : ∀ i ∈ s, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (F i) u) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => ∑ i ∈ s, F i y) u := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using contMDiffOn_const (c := (0 : ℝ))
  | insert a s has ih =>
    have heq : (fun y => ∑ i ∈ insert a s, F i y) =
        fun y => F a y + ∑ i ∈ s, F i y := by
      funext y
      rw [Finset.sum_insert has]
    rw [heq]
    exact (hF a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

theorem exists_uniform_covariant_connection_change_bound
    {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (CA : ℕ → ℝ) (hCA0 : ∀ c, 0 ≤ CA c) (a Q : ℕ) (S : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (chrR chrK : M → Idx → Idx → Idx → ℝ),
      (∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chrR y d i j) u) →
      (∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chrK y d i j) u) →
      (∀ c, c < a → ∀ y ∈ u,
        compL2 (iterCovCompU (I := I) frame chrR
          (fun z (m : Fin (2 + 1) → Idx) =>
            chrK z (m 0) (m 1) (m 2) - chrR z (m 0) (m 1) (m 2)) c y) ≤ CA c) →
      ∀ B : M → (Fin (Q + 1) → Idx) → ℝ,
      (∀ k : Fin (Q + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => B y k) u) →
      (∀ j, j ≤ a → ∀ y ∈ u, compL2 (iterCovComp (I := I) frame chrK B j y) ≤ S j) →
      ∀ y ∈ u, compL2 (iterCovComp (I := I) frame chrR B a y) ≤ C := by
  classical
  induction a using Nat.strong_induction_on generalizing Q S with
  | _ a ih =>
    cases a with
    | zero =>
      refine ⟨max (S 0) 0, le_max_right _ _, ?_⟩
      intro chrR chrK _ _ _ B _ hKt y hy
      have h := hKt 0 le_rfl y hy
      rw [iterCovComp_zero] at h ⊢
      exact h.trans (le_max_left _ _)
    | succ a' =>
      obtain ⟨C1, hC10, hC1⟩ := ih a' (Nat.lt_succ_self a') (Q + 1) (fun j => S (j + 1))
      have hmix : ∀ c : ℕ, c ≤ a' → ∃ C : ℝ, 0 ≤ C ∧
          ∀ (chrR chrK : M → Idx → Idx → Idx → ℝ),
          (∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chrR y d i j) u) →
          (∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chrK y d i j) u) →
          (∀ m, m < a' - c → ∀ y ∈ u,
            compL2 (iterCovCompU (I := I) frame chrR
              (fun z (n : Fin (2 + 1) → Idx) =>
                chrK z (n 0) (n 1) (n 2) - chrR z (n 0) (n 1) (n 2)) m y) ≤ CA m) →
          ∀ B : M → (Fin (Q + 1) → Idx) → ℝ,
          (∀ k : Fin (Q + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => B y k) u) →
          (∀ j, j ≤ a' - c → ∀ y ∈ u,
            compL2 (iterCovComp (I := I) frame chrK B j y) ≤ S j) →
          ∀ y ∈ u, compL2 (iterCovComp (I := I) frame chrR B (a' - c) y) ≤ C :=
        fun c _ => ih (a' - c) (by omega) Q S
      choose! Cm hCm0 hCm using hmix
      have hsumnn : (0 : ℝ) ≤ ∑ c ∈ Finset.range (a' + 1),
          (a'.choose c : ℝ) * CA c * Cm c :=
        Finset.sum_nonneg fun c hc =>
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCA0 c))
            (hCm0 c (Nat.lt_succ_iff.mp (Finset.mem_range.mp hc)))
      refine ⟨C1 + (Q + 1 : ℝ) * ∑ c ∈ Finset.range (a' + 1),
        (a'.choose c : ℝ) * CA c * Cm c,
        add_nonneg hC10 (mul_nonneg (by positivity) hsumnn), ?_⟩
      intro chrR chrK hchrR hchrK hCA B hB hKt y hy
      have hakSm : ∀ k : Fin (2 + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
          (fun z => chrK z (k 0) (k 1) (k 2) - chrR z (k 0) (k 1) (k 2)) u :=
        fun k => (hchrK (k 0) (k 1) (k 2)).sub (hchrR (k 0) (k 1) (k 2))
      have hB'sm : ∀ k : Fin (Q + 1 + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
          (fun z => iterCovComp (I := I) frame chrK B 1 z k) u :=
        iterCovComp_contMDiffOn hu frame chrK B hframe hchrK hB 1
      have hakActSm : ∀ k : Fin (Q + 1 + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
          (fun z => akAct
            (fun m => chrK z (m 0) (m 1) (m 2) - chrR z (m 0) (m 1) (m 2)) (B z) k) u := by
        intro k
        change ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun z =>
          ∑ s : Fin (Q + 1), ∑ p : Idx,
            (chrK z (k 0) (Fin.tail k s) p - chrR z (k 0) (Fin.tail k s) p) *
              B z (Function.update (Fin.tail k) s p)) u
        exact slabChange_sum_smooth _ _ fun s _ =>
          slabChange_sum_smooth _ _ fun p _ =>
            (hakSm ![k 0, Fin.tail k s, p]).mul (hB _)
      have hKt' : ∀ j, j ≤ a' → ∀ z ∈ u,
          compL2 (iterCovComp (I := I) frame chrK
            (fun w => iterCovComp (I := I) frame chrK B 1 w) j z) ≤ S (j + 1) := by
        intro j hj z hz
        rw [← compL2_iterCovComp_shift frame chrK B j z]
        exact hKt (j + 1) (by omega) z hz
      have hfirst := hC1 chrR chrK hchrR hchrK
        (fun c hc => hCA c (by omega))
        (fun z => iterCovComp (I := I) frame chrK B 1 z) hB'sm hKt' y hy
      have hrest : ∀ c, c ≤ a' → ∀ z ∈ u,
          compL2 (iterCovComp (I := I) frame chrR B (a' - c) z) ≤ Cm c := by
        intro c hc
        exact hCm c hc chrR chrK hchrR hchrK
          (fun m hm => hCA m (by omega)) B hB
          (fun j hj => hKt j (by omega))
      calc compL2 (iterCovComp (I := I) frame chrR B (a' + 1) y)
          = compL2 (iterCovComp (I := I) frame chrR
              (fun z => iterCovComp (I := I) frame chrR B 1 z) a' y) :=
            compL2_iterCovComp_shift frame chrR B a' y
        _ = compL2 (iterCovComp (I := I) frame chrR
              (fun z (n : Fin (Q + 1 + 1) → Idx) =>
                iterCovComp (I := I) frame chrK B 1 z n +
                  akAct (fun m => chrK z (m 0) (m 1) (m 2) - chrR z (m 0) (m 1) (m 2))
                    (B z) n) a' y) := by
            refine congrArg compL2 (iterCovComp_congr_on hu frame chrR ?_ a' y hy)
            intro z _
            funext n
            exact iterCov_chr_convert frame chrR chrK B z n
        _ = compL2 (fun n : Fin (Q + 1 + 1 + a') → Idx =>
              iterCovComp (I := I) frame chrR
                (fun z => iterCovComp (I := I) frame chrK B 1 z) a' y n +
              iterCovComp (I := I) frame chrR
                (fun z => akAct
                  (fun m => chrK z (m 0) (m 1) (m 2) - chrR z (m 0) (m 1) (m 2)) (B z))
                a' y n) :=
            congrArg compL2 (funext fun n => iterCovComp_add hu frame chrR _ _ hframe hchrR
              hB'sm hakActSm a' y hy n)
        _ ≤ compL2 (iterCovComp (I := I) frame chrR
              (fun z => iterCovComp (I := I) frame chrK B 1 z) a' y) +
            compL2 (iterCovComp (I := I) frame chrR
              (fun z => akAct
                (fun m => chrK z (m 0) (m 1) (m 2) - chrR z (m 0) (m 1) (m 2)) (B z))
              a' y) := compL2_add_le _ _
        _ ≤ C1 + (Q + 1 : ℝ) * ∑ c ∈ Finset.range (a' + 1),
              (a'.choose c : ℝ) * CA c * Cm c := by
            refine add_le_add hfirst ?_
            refine le_trans (compL2_akAct_le hu frame chrR hframe hchrR
              (fun z (m : Fin (2 + 1) → Idx) =>
                chrK z (m 0) (m 1) (m 2) - chrR z (m 0) (m 1) (m 2)) B
              hakSm hB a' hy) ?_
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            refine Finset.sum_le_sum fun c hc => ?_
            have hc' : c ≤ a' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hc)
            have h1 := hCA c (by omega) y hy
            have h2 := hrest c hc' y hy
            exact (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) (compL2_nonneg _)).trans
                (mul_le_mul_of_nonneg_left h2
                  (mul_nonneg (Nat.cast_nonneg _) (hCA0 c)))

theorem exists_linear_covariant_connection_change_bound
    {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (CA : ℕ → ℝ) (hCA0 : ∀ c, 0 ≤ CA c) (a Q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (chrR chrK : M → Idx → Idx → Idx → ℝ),
      (∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chrR y d i j) u) →
      (∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chrK y d i j) u) →
      (∀ c, c < a → ∀ y ∈ u,
        compL2 (iterCovCompU (I := I) frame chrR
          (fun z (m : Fin (2 + 1) → Idx) =>
            chrK z (m 0) (m 1) (m 2) - chrR z (m 0) (m 1) (m 2)) c y) ≤ CA c) →
      ∀ (eps : ℝ), 0 < eps → ∀ B : M → (Fin (Q + 1) → Idx) → ℝ,
      (∀ k : Fin (Q + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => B y k) u) →
      (∀ j, j ≤ a → ∀ y ∈ u,
        compL2 (iterCovComp (I := I) frame chrK B j y) ≤ eps) →
      ∀ y ∈ u, compL2 (iterCovComp (I := I) frame chrR B a y) ≤ C * eps := by
  obtain ⟨C, hC0, hC⟩ :=
    exists_uniform_covariant_connection_change_bound hu frame hframe CA hCA0 a Q (fun _ => 1)
  refine ⟨C, hC0, ?_⟩
  intro chrR chrK hchrR hchrK hCA eps heps B hB hbound y hy
  let scaled : M → (Fin (Q + 1) → Idx) → ℝ := fun z k => eps⁻¹ * B z k
  have hscaled : ∀ k, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun z => scaled z k) u :=
    fun k => contMDiffOn_const.mul (hB k)
  have hnorm (chr : M → Idx → Idx → Idx → ℝ)
      (hchr : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun z => chr z d i j) u)
      (r : ℕ) (z : M) (hz : z ∈ u) :
      compL2 (iterCovComp (I := I) frame chr scaled r z) =
        eps⁻¹ * compL2 (iterCovComp (I := I) frame chr B r z) := by
    have heq : iterCovComp (I := I) frame chr scaled r z =
        fun n => eps⁻¹ * iterCovComp (I := I) frame chr B r z n :=
      funext (iterCovComp_smul hu frame chr eps⁻¹ B hframe hchr hB r z hz)
    rw [heq, compL2_smul, abs_of_pos (inv_pos.mpr heps)]
  have hscaledBound : ∀ j, j ≤ a → ∀ z ∈ u,
      compL2 (iterCovComp (I := I) frame chrK scaled j z) ≤ 1 := by
    intro j hj z hz
    rw [hnorm chrK hchrK j z hz]
    exact (mul_le_mul_of_nonneg_left (hbound j hj z hz) (inv_nonneg.mpr heps.le)).trans_eq
      (inv_mul_cancel₀ heps.ne')
  have hfinal := hC chrR chrK hchrR hchrK hCA scaled hscaled hscaledBound y hy
  rw [hnorm chrR hchrR a y hy] at hfinal
  have hmul := mul_le_mul_of_nonneg_left hfinal heps.le
  simpa only [← mul_assoc, mul_inv_cancel₀ heps.ne', one_mul, mul_comm eps C] using hmul

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
