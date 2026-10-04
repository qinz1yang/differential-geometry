import DifferentialGeometry.Analysis.Calculus.MapConvergence.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness

variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

private theorem norm_iteratedFDeriv_bilinear_le_of_contDiffAt
    (B : F →L[ℝ] G →L[ℝ] H) {p r : ℕ} {f : E → F} {g : E → G} {x : E}
    (hf : ContDiffAt ℝ p f x) (hg : ContDiffAt ℝ p g x) (hr : r ≤ p) :
    ‖iteratedFDeriv ℝ r (fun y => B (f y) (g y)) x‖ ≤
      ‖B‖ * ∑ j ∈ Finset.range (r + 1), (r.choose j : ℝ) *
        ‖iteratedFDeriv ℝ j f x‖ * ‖iteratedFDeriv ℝ (r - j) g x‖ := by
  obtain ⟨S, hS, hfS⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨T, hT, hgT⟩ := hg.contDiffOn le_rfl (by simp)
  obtain ⟨U, hUST, hU, hxU⟩ := mem_nhds_iff.mp (inter_mem hS hT)
  have hb := B.norm_iteratedFDerivWithin_le_of_bilinear (n := r)
    (hfS.mono (hUST.trans inter_subset_left))
    (hgT.mono (hUST.trans inter_subset_right)) hU.uniqueDiffOn hxU
    (by exact_mod_cast hr)
  simp_rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) _ hU hxU] at hb
  exact hb

private theorem exists_bound_iteratedFDeriv_on_compact
    {K : Set E} {p : ℕ} {f : E → F} (hK : IsCompact K)
    (hf : ∀ x ∈ K, ContDiffAt ℝ p f x) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ r ≤ p, ∀ x ∈ K, ‖iteratedFDeriv ℝ r f x‖ ≤ M := by
  classical
  have hb : ∀ r : Fin (p + 1), ∃ C : ℝ,
      ∀ x ∈ K, ‖iteratedFDeriv ℝ (r : ℕ) f x‖ ≤ C := by
    intro r
    apply hK.exists_bound_of_continuousOn
    intro x hx
    exact ((hf x hx).continuousAt_iteratedFDeriv
      (by exact_mod_cast Nat.le_of_lt_succ r.isLt)).continuousWithinAt
  choose C hC using hb
  refine ⟨∑ r : Fin (p + 1), max (C r) 0,
    Finset.sum_nonneg (fun _ _ => le_max_right _ _), ?_⟩
  intro r hr x hx
  let i : Fin (p + 1) := ⟨r, Nat.lt_succ_of_le hr⟩
  exact (hC i x hx).trans ((le_max_left _ _).trans
    (Finset.single_le_sum (fun j _ => le_max_right (C j) 0) (Finset.mem_univ i)))

theorem MapCPConvergenceOn.bilinear
    (B : F →L[ℝ] G →L[ℝ] H) {K : Set E} {p : ℕ} (hK : IsCompact K)
    {f : ℕ → E → F} {fInf : E → F} {g : ℕ → E → G} {gInf : E → G}
    (hf : MapCPConvergenceOn K p f fInf) (hg : MapCPConvergenceOn K p g gInf)
    (hfInf : ∀ x ∈ K, ContDiffAt ℝ p fInf x)
    (hgInf : ∀ x ∈ K, ContDiffAt ℝ p gInf x)
    (hfc : ∀ᶠ n in atTop, ∀ x ∈ K, ContDiffAt ℝ p (f n) x)
    (hgc : ∀ᶠ n in atTop, ∀ x ∈ K, ContDiffAt ℝ p (g n) x) :
    MapCPConvergenceOn K p (fun n x => B (f n x) (g n x))
      (fun x => B (fInf x) (gInf x)) := by
  classical
  obtain ⟨Mf, hMf, hfBound⟩ := exists_bound_iteratedFDeriv_on_compact hK hfInf
  obtain ⟨Mg, hMg, hgBound⟩ := exists_bound_iteratedFDeriv_on_compact hK hgInf
  let a : ℕ → ℝ := fun r => ‖B‖ *
    (∑ j ∈ Finset.range (r + 1), (r.choose j : ℝ)) * (Mf + Mg + 1)
  have ha (r : ℕ) : 0 ≤ a r := by
    dsimp only [a]
    positivity
  let C : ℝ := 1 + ∑ r ∈ Finset.range (p + 1), a r
  have hC : 0 < C := by
    have hsum : 0 ≤ ∑ r ∈ Finset.range (p + 1), a r :=
      Finset.sum_nonneg (fun r _ => ha r)
    dsimp only [C]
    linarith
  have haC (r : ℕ) (hr : r ≤ p) : a r ≤ C := by
    have hsum := Finset.single_le_sum (fun j _ => ha j)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hr))
    dsimp only [C]
    linarith
  intro ε hε
  obtain ⟨Nf, hNf⟩ := hf (ε / C) (div_pos hε hC)
  obtain ⟨Ng, hNg⟩ := hg (ε / C) (div_pos hε hC)
  obtain ⟨N₁, hN₁⟩ := hg 1 zero_lt_one
  have htail : ∀ᶠ n in atTop, ∀ r ≤ p, ∀ x ∈ K,
      mapDerivNorm r (fun y => B (f n y) (g n y))
        (fun y => B (fInf y) (gInf y)) x ≤ ε := by
    filter_upwards [eventually_ge_atTop Nf, eventually_ge_atTop Ng,
      eventually_ge_atTop N₁, hfc, hgc] with n hnf hng hn₁ hfn hgn
    intro r hr x hx
    have hfd := (hfn x hx).sub (hfInf x hx)
    have hgd := (hgn x hx).sub (hgInf x hx)
    have hgStage : ∀ j ≤ p, ‖iteratedFDeriv ℝ j (g n) x‖ ≤ Mg + 1 := by
      intro j hj
      have hsub := iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := j) (x := x)
        ((hgn x hx).of_le (by exact_mod_cast hj))
        ((hgInf x hx).of_le (by exact_mod_cast hj))
      have herr := hN₁ n hn₁ j hj x hx
      change ‖iteratedFDeriv ℝ j (g n - gInf) x‖ ≤ 1 at herr
      rw [hsub] at herr
      have hnorm := norm_le_norm_sub_add
        (iteratedFDeriv ℝ j (g n) x) (iteratedFDeriv ℝ j gInf x)
      linarith [hgBound j hj x hx]
    have hsplit : (fun y => B (f n y) (g n y) - B (fInf y) (gInf y)) =
        (fun y => B (f n y - fInf y) (g n y)) +
          (fun y => B (fInf y) (g n y - gInf y)) := by
      funext y
      simp only [Pi.add_apply, map_sub, sub_apply]
      abel
    have hleft : ContDiffAt ℝ p (fun y => B (f n y - fInf y) (g n y)) x :=
      (B.contDiff.contDiffAt.comp x hfd).clm_apply (hgn x hx)
    have hright : ContDiffAt ℝ p (fun y => B (fInf y) (g n y - gInf y)) x :=
      (B.contDiff.contDiffAt.comp x (hfInf x hx)).clm_apply hgd
    rw [mapDerivNorm, hsplit, iteratedFDeriv_add_apply
      (hleft.of_le (by exact_mod_cast hr)) (hright.of_le (by exact_mod_cast hr))]
    calc
      _ ≤ ‖iteratedFDeriv ℝ r (fun y => B (f n y - fInf y) (g n y)) x‖ +
          ‖iteratedFDeriv ℝ r (fun y => B (fInf y) (g n y - gInf y)) x‖ :=
        norm_add_le _ _
      _ ≤ (‖B‖ * ∑ j ∈ Finset.range (r + 1), (r.choose j : ℝ) *
            (ε / C) * (Mg + 1)) +
          (‖B‖ * ∑ j ∈ Finset.range (r + 1), (r.choose j : ℝ) * Mf * (ε / C)) := by
        apply add_le_add
        · apply (norm_iteratedFDeriv_bilinear_le_of_contDiffAt B hfd (hgn x hx) hr).trans
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg B)
          apply Finset.sum_le_sum
          intro j hj
          have hjp : j ≤ p := (Nat.le_of_lt_succ (Finset.mem_range.mp hj)).trans hr
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left (hNf n hnf j hjp x hx) (Nat.cast_nonneg _))
            (hgStage (r - j) ((Nat.sub_le _ _).trans hr)) (norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) (div_pos hε hC).le)
        · apply (norm_iteratedFDeriv_bilinear_le_of_contDiffAt B (hfInf x hx) hgd hr).trans
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg B)
          apply Finset.sum_le_sum
          intro j hj
          have hjp : j ≤ p := (Nat.le_of_lt_succ (Finset.mem_range.mp hj)).trans hr
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left (hfBound j hjp x hx) (Nat.cast_nonneg _))
            (hNg n hng (r - j) ((Nat.sub_le _ _).trans hr) x hx) (norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) hMf)
      _ = a r * (ε / C) := by
        dsimp only [a]
        simp only [mul_assoc, ← Finset.sum_mul]
        ring
      _ ≤ C * (ε / C) := mul_le_mul_of_nonneg_right (haC r hr) (div_pos hε hC).le
      _ = ε := by rw [mul_comm, div_mul_cancel₀ _ hC.ne']
  exact eventually_atTop.mp htail

end DifferentialGeometry.CheegerGromovCompactness

end
