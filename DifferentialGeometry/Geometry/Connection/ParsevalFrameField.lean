import DifferentialGeometry.Geometry.Connection.ChartFrame.RicciIdentitySmoothFrame
import Mathlib.Geometry.Manifold.PartitionOfUnity
import DifferentialGeometry.Geometry.Metric.OrthonormalFrame.Parseval
open DifferentialGeometry.Geometry.Curvature

noncomputable section



open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff BigOperators


namespace DifferentialGeometry
namespace Geometry
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M]

variable [CompactSpace M]

omit [BoundarylessManifold I M] in
theorem exists_smooth_parseval_frame_family (g : SmoothRiemannianMetric I M) :
    ∃ (N : ℕ) (W : Fin N → Π b : M, TangentSpace I b),
      (∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (W a))) ∧
      ∀ (x : M) (u : TangentSpace I x),
        (∑ a : Fin N, g.inner x (W a x) u • W a x) = u := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  set U : M → Set M := fun α => interior (smoothOrthoFrameNeighborhood (I := I) (M := M) α) with hU_def
  have hU_open : ∀ α : M, IsOpen (U α) := fun _ => isOpen_interior
  have hU_mem : ∀ α : M, α ∈ U α := fun α =>
    mem_interior_iff_mem_nhds.mpr (smoothOrthoFrameNeighborhood_mem_nhds (I := I) (M := M) α)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hU_open
    (fun x _ => mem_iUnion.mpr ⟨x, hU_mem x⟩)
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := I) isClosed_univ
    (fun k : ↥t => U (k : M)) (fun _ => isOpen_interior)
    (by
      intro x _
      rcases mem_iUnion₂.mp (ht (mem_univ x)) with ⟨α, hαt, hαx⟩
      exact mem_iUnion.mpr ⟨⟨α, hαt⟩, hαx⟩)
  set ρ : M → ℝ := fun x => ∑ k : ↥t, (f k x) ^ 2 with hρ_def
  have hρ_pos : ∀ x : M, 0 < ρ x := by
    intro x
    obtain ⟨k, hk⟩ := f.exists_pos_of_mem (mem_univ x)
    exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨k, Finset.mem_univ k, pow_pos hk 2⟩
  have hρ_smooth : ContMDiff I 𝓘(ℝ) ∞ ρ := by
    have hgen : ∀ s : Finset ↥t,
        ContMDiff I 𝓘(ℝ) ∞ (fun x : M => ∑ k ∈ s, (f k x) ^ 2) := by
      intro s
      induction s using Finset.induction with
      | empty => simpa using contMDiff_const (c := (0 : ℝ))
      | insert k s hk ih =>
          have hsq : ContMDiff I 𝓘(ℝ) ∞ (fun x : M => (f k x) ^ 2) := by
            have h := (f k).contMDiff
            have hmul := h.mul h
            change ContMDiff I 𝓘(ℝ) ∞ (fun x : M => f k x * f k x) at hmul
            simpa only [pow_two] using hmul
          have hadd := hsq.add ih
          change ContMDiff I 𝓘(ℝ) ∞
            (fun x : M => (f k x) ^ 2 + ∑ i ∈ s, (f i x) ^ 2) at hadd
          simpa only [Finset.sum_insert hk] using hadd
    exact hgen Finset.univ
  set c : ↥t → M → ℝ := fun k x => (Real.sqrt (ρ x))⁻¹ * f k x with hc_def
  have hc_smooth : ∀ k : ↥t, ContMDiff I 𝓘(ℝ) ∞ (c k) := by
    intro k x
    have hsq : ContMDiffAt I 𝓘(ℝ) ∞ (fun y : M => Real.sqrt (ρ y)) x := by
      have h1 : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ) ∞ Real.sqrt (ρ x) :=
        (Real.contDiffAt_sqrt (ne_of_gt (hρ_pos x))).contMDiffAt
      exact h1.comp x (hρ_smooth x)
    have hinv : ContMDiffAt I 𝓘(ℝ) ∞ (fun y : M => (Real.sqrt (ρ y))⁻¹) x :=
      hsq.inv₀ (ne_of_gt (Real.sqrt_pos.mpr (hρ_pos x)))
    exact hinv.mul ((f k).contMDiff x)
  set W0 : ↥t × Fin n → Π b : M, TangentSpace I b :=
    fun p => fun b => c p.1 b • smoothOrthoFrame (I := I) g (p.1 : M) p.2 b with hW0_def
  have hW0_smooth : ∀ p : ↥t × Fin n,
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (W0 p)) := by
    intro p
    have h := ContMDiffOn.smul_section_of_tsupport (𝕜 := ℝ) (n := ∞)
      (V := TangentSpace I) (ψ := c p.1) (s := smoothOrthoFrame (I := I) g (p.1 : M) p.2)
      ((hc_smooth p.1).contMDiffOn (s := univ)) isOpen_univ (subset_univ _)
      ((smoothOrthoFrame_smooth (I := I) g (p.1 : M) p.2).contMDiffOn (s := univ))
    exact h
  have hrepr : ∀ (x : M) (u : TangentSpace I x),
      (∑ p : ↥t × Fin n, g.inner x (W0 p x) u • W0 p x) = u := by
    intro x u
    rw [Fintype.sum_prod_type]
    have hperk : ∀ k : ↥t,
        (∑ i : Fin n, g.inner x (W0 (k, i) x) u • W0 (k, i) x) =
          ((f k x) ^ 2 * (ρ x)⁻¹) • u := by
      intro k
      by_cases hfk : f k x = 0
      · have hc0 : c k x = 0 := by rw [hc_def]; simp [hfk]
        rw [hfk]
        simp only [hW0_def, hc0, zero_smul, map_zero, zero_apply,
          smul_zero, Finset.sum_const_zero]
        rw [show (0 : ℝ) ^ 2 * (ρ x)⁻¹ = 0 by ring, zero_smul]
      · have hx_mem : x ∈ smoothOrthoFrameNeighborhood (I := I) (M := M) (k : M) := by
          have h1 : x ∈ tsupport (f k) := subset_closure (Function.mem_support.mpr hfk)
          exact interior_subset (hf k h1)
        have horth : ∀ i j : Fin n,
            g.inner x (smoothOrthoFrame (I := I) g (k : M) i x)
              (smoothOrthoFrame (I := I) g (k : M) j x) = if i = j then (1 : ℝ) else 0 :=
          fun i j => smoothOrthoFrame_orthonormal (I := I) g (k : M) hx_mem i j
        have hstep : ∀ i : Fin n,
            g.inner x (W0 (k, i) x) u • W0 (k, i) x =
              (c k x) ^ 2 • (g.inner x (smoothOrthoFrame (I := I) g (k : M) i x) u •
                smoothOrthoFrame (I := I) g (k : M) i x) := by
          intro i
          rw [hW0_def]
          simp only
          rw [map_smul (g.inner x) (c k x) (smoothOrthoFrame (I := I) g (k : M) i x),
            smul_apply, smul_eq_mul, smul_smul, smul_smul]
          congr 1
          ring
        rw [Finset.sum_congr rfl (fun i _ => hstep i), ← Finset.smul_sum,
          orthonormal_tangent_expansion (I := I) (M := M) g x
            (fun i => smoothOrthoFrame (I := I) g (k : M) i x) horth u]
        congr 1
        rw [hc_def]
        simp only
        rw [mul_pow]
        have hsq : ((Real.sqrt (ρ x))⁻¹) ^ 2 = (ρ x)⁻¹ := by
          rw [← Real.sqrt_inv, Real.sq_sqrt (inv_nonneg.mpr (le_of_lt (hρ_pos x)))]
        rw [hsq]
        ring
    rw [Finset.sum_congr rfl (fun k _ => hperk k), ← Finset.sum_smul, ← Finset.sum_mul]
    rw [show (∑ k : ↥t, (f k x) ^ 2) = ρ x from rfl]
    rw [mul_inv_cancel₀ (ne_of_gt (hρ_pos x)), one_smul]
  refine ⟨Fintype.card (↥t × Fin n), fun a => W0 ((Fintype.equivFin (↥t × Fin n)).symm a),
    fun a => hW0_smooth _, ?_⟩
  intro x u
  conv_rhs => rw [← hrepr x u]
  exact Equiv.sum_comp (Fintype.equivFin (↥t × Fin n)).symm
    (fun p => g.inner x (W0 p x) u • W0 p x)

end Connection
end Geometry
end DifferentialGeometry

end
