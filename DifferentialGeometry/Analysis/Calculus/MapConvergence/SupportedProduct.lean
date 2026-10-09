import DifferentialGeometry.Analysis.Calculus.MapConvergence.Basic
import DifferentialGeometry.Analysis.Calculus.MapConvergence.Bilinear
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import DifferentialGeometry.Analysis.Calculus.MapConvergence.EventualCongruence
import Mathlib.Topology.Separation.Regular

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem MapCPConvergenceOn.supported_smul
    {U V L : Set E} {k : ℕ} {χ : E → ℝ} {δ : ℕ → E → F}
    (hconv : MapCPConvergenceOn (L ∩ tsupport χ) k δ (fun _ => 0))
    (hU : IsOpen U) (hV : IsOpen V) (hL : IsCompact L) (hLU : L ⊆ U)
    (hχ : ContDiffOn ℝ (k : ℕ∞) χ U)
    (hsupp : tsupport χ ∩ U ⊆ V)
    (hδ : ∀ n, ContDiffOn ℝ (k : ℕ∞) (δ n) V) :
    (∀ n, ContDiffOn ℝ (k : ℕ∞) (fun x => χ x • δ n x) U) ∧
      MapCPConvergenceOn L k (fun n x => χ x • δ n x) (fun _ => 0) := by
  classical
  have hzero (n : ℕ) (x : E) (hx : x ∉ tsupport χ) :
      (fun y => χ y • δ n y) =ᶠ[𝓝 x] (fun _ => (0 : F)) := by
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
    rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]
  refine ⟨?_, ?_⟩
  · intro n x hx
    by_cases hxχ : x ∈ tsupport χ
    · exact (hχ x hx).smul
        (((hδ n).contDiffAt (hV.mem_nhds (hsupp ⟨hxχ, hx⟩))).contDiffWithinAt)
    · exact (contDiffAt_const.congr_of_eventuallyEq (hzero n x hxχ)).contDiffWithinAt
  · have hbounds : ∀ j : ℕ, ∃ B : ℝ, 0 ≤ B ∧
        ∀ x ∈ L, j ≤ k → ‖iteratedFDeriv ℝ j χ x‖ ≤ B := by
      intro j
      by_cases hj : j ≤ k
      · have hc : ContinuousOn (fun x => ‖iteratedFDeriv ℝ j χ x‖) L :=
          ((ContinuousOn.continuousOn_iteratedFDeriv hχ hU
            (by exact_mod_cast hj)).norm).mono hLU
        obtain ⟨B, hB⟩ := hL.bddAbove_image hc
        refine ⟨max B 0, le_max_right _ _, ?_⟩
        intro x hx _
        exact (hB ⟨x, hx, rfl⟩).trans (le_max_left _ _)
      · exact ⟨0, le_rfl, fun _ _ hj' => (hj hj').elim⟩
    choose B hBnonneg hB using hbounds
    let a : ℕ → ℝ := fun r =>
      ∑ j ∈ Finset.range (r + 1), (r.choose j : ℝ) * B j
    have ha (r : ℕ) : 0 ≤ a r := by
      exact Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (hBnonneg j)
    let C : ℝ := 1 + ∑ r ∈ Finset.range (k + 1), a r
    have hC : 0 < C := by
      have hs : 0 ≤ ∑ r ∈ Finset.range (k + 1), a r :=
        Finset.sum_nonneg fun r _ => ha r
      dsimp [C]
      linarith
    have haC (r : ℕ) (hr : r ≤ k) : a r ≤ C := by
      have hs : a r ≤ ∑ j ∈ Finset.range (k + 1), a j :=
        Finset.single_le_sum (fun j _ => ha j)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hr))
      dsimp [C]
      linarith
    intro ε hε
    obtain ⟨N, hN⟩ := hconv (ε / C) (div_pos hε hC)
    refine ⟨N, ?_⟩
    intro n hn r hr x hx
    change ‖iteratedFDeriv ℝ r (fun y => χ y • δ n y - 0) x‖ ≤ ε
    simp only [sub_zero]
    by_cases hxχ : x ∈ tsupport χ
    · have hxO : x ∈ U ∩ V := ⟨hLU hx, hsupp ⟨hxχ, hLU hx⟩⟩
      have hO : IsOpen (U ∩ V) := hU.inter hV
      have hprod := norm_iteratedFDerivWithin_smul_le
        (𝕜 := ℝ) (𝕜' := ℝ) (f := χ) (g := δ n) (n := r)
        (hχ.mono inter_subset_left) ((hδ n).mono inter_subset_right)
        hO.uniqueDiffOn hxO (by exact_mod_cast hr)
      rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
        (f := fun y => χ y • δ n y) r hO hxO] at hprod
      calc
        ‖iteratedFDeriv ℝ r (fun y => χ y • δ n y) x‖ ≤
            ∑ j ∈ Finset.range (r + 1), (r.choose j : ℝ) *
              ‖iteratedFDerivWithin ℝ j χ (U ∩ V) x‖ *
              ‖iteratedFDerivWithin ℝ (r - j) (δ n) (U ∩ V) x‖ := hprod
        _ ≤ ∑ j ∈ Finset.range (r + 1), (r.choose j : ℝ) * B j * (ε / C) := by
          apply Finset.sum_le_sum
          intro j hj
          have hjk : j ≤ k := (Nat.le_of_lt_succ (Finset.mem_range.mp hj)).trans hr
          have hχj : ‖iteratedFDerivWithin ℝ j χ (U ∩ V) x‖ ≤ B j := by
            rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := χ) j hO hxO]
            exact hB j x hx hjk
          have hδj : ‖iteratedFDerivWithin ℝ (r - j) (δ n) (U ∩ V) x‖ ≤ ε / C := by
            rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := δ n) (r - j) hO hxO]
            simpa only [mapDerivNorm, sub_zero] using
              hN n hn (r - j) ((Nat.sub_le r j).trans hr) x ⟨hx, hxχ⟩
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left hχj (Nat.cast_nonneg _)) hδj
            (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hBnonneg j))
        _ = a r * (ε / C) := by
          dsimp only [a]
          rw [Finset.sum_mul]
        _ ≤ C * (ε / C) := mul_le_mul_of_nonneg_right (haC r hr) (div_pos hε hC).le
        _ = ε := by rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hC)]
    · rw [((hzero n x hxχ).iteratedFDeriv ℝ r).self_of_nhds]
      simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero] using hε.le

theorem MapCPConvergenceOn.supported_smul_of_eventually_contDiffOn
    {V : Set E} {p : ℕ} {χ : E → ℝ} {δ : ℕ → E → F}
    (hconv : MapCPConvergenceOn (tsupport χ) p δ (fun _ => 0))
    (hV : IsOpen V) (hχ : ContDiff ℝ p χ) (hcompact : HasCompactSupport χ)
    (hsupp : tsupport χ ⊆ V)
    (hδ : ∀ S : Set E, IsCompact S → S ⊆ V →
      ∀ᶠ n in atTop, ContDiffOn ℝ (p : ℕ∞) (δ n) S) :
    (∀ᶠ n in atTop, ContDiff ℝ p (fun x => χ x • δ n x)) ∧
      MapCPConvergenceOn univ p (fun n x => χ x • δ n x) (fun _ => 0) := by
  classical
  rcases hcompact.eq_zero_or_locallyCompactSpace_of_addGroup hχ.continuous with hzero | hloc
  · subst χ
    simp only [Pi.zero_apply, zero_smul]
    refine ⟨Eventually.of_forall fun _ => contDiff_const, ?_⟩
    intro ε hε
    refine ⟨0, fun _ _ r _ x _ => ?_⟩
    simpa only [mapDerivNorm, sub_zero, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
      using hε.le
  let : LocallyCompactSpace E := hloc
  obtain ⟨W, hW, hsW, hWV, hWc⟩ :=
    exists_open_between_and_isCompact_closure hcompact hV hsupp
  have hreg : ∀ᶠ n in atTop, ContDiffOn ℝ (p : ℕ∞) (δ n) W :=
    (hδ (closure W) hWc hWV).mono fun _ hn => hn.mono subset_closure
  let D : ℕ → E → F := fun n =>
    if ContDiffOn ℝ (p : ℕ∞) (δ n) W then δ n else fun _ => 0
  have hD : ∀ n, ContDiffOn ℝ (p : ℕ∞) (D n) W := by
    intro n
    dsimp only [D]
    split_ifs with hn
    · exact hn
    · exact contDiffOn_const
  have heq : ∀ᶠ n in atTop, D n = δ n := by
    filter_upwards [hreg] with n hn
    exact ite_eq_left hn
  have hDconv : MapCPConvergenceOn (tsupport χ) p D (fun _ => 0) :=
    hconv.congr_eventually isOpen_univ (subset_univ _)
      (heq.mono fun n hn x _ => congrFun hn x) (Set.eqOn_refl _ _)
  have hprod := MapCPConvergenceOn.supported_smul
      (U := (univ : Set E)) (V := W) (L := tsupport χ)
      (χ := χ) (δ := D) (k := p)
      (by simpa only [inter_self] using hDconv)
      isOpen_univ hW hcompact (subset_univ _) hχ.contDiffOn
      (fun _ hx => hsW hx.1) hD
  refine ⟨?_, ?_⟩
  · filter_upwards [heq] with n hn
    have h := contDiffOn_univ.mp (hprod.1 n)
    simpa only [hn, WithTop.coe_natCast] using h
  · have hlocal : MapCPConvergenceOn (tsupport χ) p
        (fun n x => χ x • δ n x) (fun _ => 0) :=
      hprod.2.congr_eventually isOpen_univ (subset_univ _)
      (heq.mono fun n hn x _ => by rw [hn]) (Set.eqOn_refl _ _)
    intro ε hε
    obtain ⟨N, hN⟩ := hlocal ε hε
    refine ⟨N, fun n hn r hr x _ => ?_⟩
    by_cases hx : x ∈ tsupport χ
    · exact hN n hn r hr x hx
    · have hzero : (fun y => χ y • δ n y) =ᶠ[𝓝 x] (fun _ => (0 : F)) := by
        filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
        rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]
      simp only [mapDerivNorm, sub_zero]
      rw [(hzero.iteratedFDeriv ℝ r).self_of_nhds]
      simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero] using hε.le

theorem MapCPConvergenceOn.supported_smul_of_eventually_contDiffAt
    {K : Set E} {p : ℕ} {χ : E → ℝ} {δ : ℕ → E → F}
    (hconv : MapCPConvergenceOn (K ∩ tsupport χ) p δ (fun _ => 0))
    (hcompact : IsCompact (K ∩ tsupport χ))
    (hχ : ∀ x ∈ K ∩ tsupport χ, ContDiffAt ℝ p χ x)
    (hδ : ∀ᶠ n in atTop, ∀ x ∈ K ∩ tsupport χ, ContDiffAt ℝ p (δ n) x) :
    MapCPConvergenceOn K p (fun n x => χ x • δ n x) (fun _ => 0) := by
  classical
  have hχconv : MapCPConvergenceOn (K ∩ tsupport χ) p (fun _ => χ) χ := by
    intro ε hε
    refine ⟨0, fun _ _ r _ x _ => ?_⟩
    simpa only [mapDerivNorm, sub_self, iteratedFDeriv_fun_zero, Pi.zero_apply,
      norm_zero] using hε.le
  have hproduct : MapCPConvergenceOn (K ∩ tsupport χ) p
      (fun n x => χ x • δ n x) (fun _ => 0) := by
    simpa only [ContinuousLinearMap.lsmul_apply, smul_zero] using
      hχconv.bilinear (ContinuousLinearMap.lsmul ℝ ℝ)
        hcompact hconv hχ
        (fun _ _ => contDiffAt_const) (Eventually.of_forall fun _ => hχ) hδ
  intro ε hε
  obtain ⟨N, hN⟩ := hproduct ε hε
  refine ⟨N, fun n hn r hr x hx => ?_⟩
  by_cases hxχ : x ∈ tsupport χ
  · exact hN n hn r hr x ⟨hx, hxχ⟩
  · have hzero : (fun y => χ y • δ n y) =ᶠ[𝓝 x] (fun _ => (0 : F)) := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hxχ] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]
    simp only [mapDerivNorm, sub_zero]
    rw [(hzero.iteratedFDeriv ℝ r).self_of_nhds]
    simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero] using hε.le

end DifferentialGeometry.CheegerGromovCompactness
