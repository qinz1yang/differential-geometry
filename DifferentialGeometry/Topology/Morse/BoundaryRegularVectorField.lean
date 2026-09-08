import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.LinearAlgebra.Pi
import Mathlib.Topology.Algebra.Support
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped ContDiff Topology

namespace DifferentialGeometry.Topology.Morse

variable {n : ℕ}

private def boundaryInclusion : (Fin n → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  ContinuousLinearMap.pi (fun i => Fin.cases 0 (fun j => ContinuousLinearMap.proj j) i)

private theorem boundaryInclusion_apply (x : Fin n → ℝ) :
    boundaryInclusion x = Fin.cons 0 x := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

private theorem linear_form_apply (L : (Fin n → ℝ) →L[ℝ] ℝ) (x : Fin n → ℝ) :
    L x = ∑ i, x i * L (Pi.single i 1) := by
  have hb (i : Fin n) : (fun j : Fin n => if i = j then (1 : ℝ) else 0) = Pi.single i 1 := by
    ext j
    simp [Pi.single_apply, eq_comm]
  simpa only [hb, smul_eq_mul, ContinuousLinearMap.coe_coe] using L.toLinearMap.pi_apply_eq_sum_univ x

private theorem exists_coordinate_ne_zero (L : (Fin n → ℝ) →L[ℝ] ℝ) (hL : L ≠ 0) :
    ∃ i, L (Pi.single i 1) ≠ 0 := by
  by_contra! h
  apply hL
  ext x
  rw [linear_form_apply]
  simp [h]

theorem exists_contDiff_boundary_tangent_vector_field
    {F ρ : ℝ × (Fin (n + 1) → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hregular : ∀ p ∈ tsupport ρ, p.2 0 ≠ 0 →
      fderiv ℝ (fun z => F (p.1, z)) p.2 ≠ 0)
    (hboundary : ∀ p ∈ tsupport ρ, p.2 0 = 0 →
      fderiv ℝ (fun x => F (p.1, Fin.cons 0 x)) (Fin.tail p.2) ≠ 0) :
    ∃ V : ℝ × (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ),
      ContDiff ℝ ∞ V ∧ HasCompactSupport V ∧
      (∀ p, p.2 0 = 0 → V p 0 = 0) ∧
      (∀ p, fderiv ℝ (fun z => F (p.1, z)) p.2 (V p) =
        -ρ p * deriv (fun t => F (t, p.2)) p.1) ∧
      (∀ p, ρ p = 0 ∨ deriv (fun t => F (t, p.2)) p.1 = 0 → V p = 0) := by
  classical
  let L := fun p : ℝ × (Fin (n + 1) → ℝ) => fderiv ℝ (fun z => F (p.1, z)) p.2
  let d := fun p i => L p (Pi.single i 1)
  let w := fun (z : Fin (n + 1) → ℝ) (i : Fin (n + 1)) => if i = 0 then (z 0) ^ 2 else 1
  let Q := fun p : ℝ × (Fin (n + 1) → ℝ) => ∑ i, w p.2 i * (d p i) ^ 2
  let dt := fun p : ℝ × (Fin (n + 1) → ℝ) => deriv (fun t => F (t, p.2)) p.1
  have hL : ContDiff ℝ ∞ L :=
    (hF.comp ((contDiff_fst.fst).prodMk contDiff_snd)).fderiv
      (f := fun (p : ℝ × (Fin (n + 1) → ℝ)) z => F (p.1, z)) contDiff_snd (by simp)
  have hd (i : Fin (n + 1)) : ContDiff ℝ ∞ (fun p => d p i) :=
    hL.clm_apply contDiff_const
  have hw (i : Fin (n + 1)) : ContDiff ℝ ∞ (fun p : ℝ × (Fin (n + 1) → ℝ) => w p.2 i) := by
    by_cases hi : i = 0
    · simp only [w, if_pos hi]
      fun_prop
    · simp only [w, if_neg hi]
      exact contDiff_const
  have hQ : ContDiff ℝ ∞ Q :=
    ContDiff.sum (fun i _ => (hw i).mul ((hd i).pow 2))
  have hdt : ContDiff ℝ ∞ dt := by
    simpa only [fderiv_apply_one_eq_deriv] using
      (hF.comp (contDiff_snd.prodMk contDiff_fst.snd)).fderiv_apply
        (f := fun (p : ℝ × (Fin (n + 1) → ℝ)) t => F (t, p.2)) contDiff_fst (contDiff_const (c := (1 : ℝ))) (by simp)
  have hQpos (p : ℝ × (Fin (n + 1) → ℝ)) (hp : p ∈ tsupport ρ) : 0 < Q p := by
    have hnonneg (i : Fin (n + 1)) : 0 ≤ w p.2 i * (d p i) ^ 2 := by
      dsimp [w]
      split_ifs <;> positivity
    apply Finset.sum_pos' (fun i _ => hnonneg i)
    by_cases hz : p.2 0 = 0
    · let A : (Fin n → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) := boundaryInclusion
      have hpoint : A (Fin.tail p.2) = p.2 := by
        rw [boundaryInclusion_apply, ← hz, Fin.cons_self_tail]
      have hf : DifferentiableAt ℝ (fun z => F (p.1, z)) (A (Fin.tail p.2)) :=
        (hF.differentiable (by simp) _).comp _
          ((differentiableAt_const p.1).prodMk differentiableAt_id)
      have hderiv : fderiv ℝ (fun x => F (p.1, Fin.cons 0 x)) (Fin.tail p.2) =
          (L p).comp A := by
        have h := (hf.hasFDerivAt.comp (Fin.tail p.2) A.hasFDerivAt).fderiv
        rw [hpoint] at h
        simpa only [A, Function.comp_def, boundaryInclusion_apply] using h
      have hcomp : (L p).comp A ≠ 0 := by
        rw [← hderiv]
        exact hboundary p hp hz
      obtain ⟨i, hi⟩ := exists_coordinate_ne_zero ((L p).comp A) hcomp
      have hsingle : A (Pi.single i 1) = Pi.single i.succ 1 := by
        rw [boundaryInclusion_apply]
        ext j
        refine Fin.cases ?_ (fun k => ?_) j
        · simp
        · simp [Pi.single_apply]
      have hdi : d p i.succ ≠ 0 := by
        simpa only [ContinuousLinearMap.comp_apply, hsingle] using hi
      refine ⟨i.succ, Finset.mem_univ _, ?_⟩
      simpa only [w, Fin.succ_ne_zero, if_false, one_mul] using sq_pos_of_ne_zero hdi
    · obtain ⟨i, hi⟩ := exists_coordinate_ne_zero (L p) (hregular p hp hz)
      refine ⟨i, Finset.mem_univ _, mul_pos ?_ (sq_pos_of_ne_zero hi)⟩
      dsimp [w]
      split_ifs
      · exact sq_pos_of_ne_zero hz
      · norm_num
  let V := fun p i => (-ρ p * dt p / Q p) * (w p.2 i * d p i)
  have hVzero (p : ℝ × (Fin (n + 1) → ℝ)) (h : ρ p = 0 ∨ dt p = 0) : V p = 0 := by
    rcases h with h | h <;> ext i <;> simp [V, h]
  refine ⟨V, ?_, ?_, ?_, ?_, hVzero⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro p
    by_cases hp : p ∈ tsupport ρ
    · apply contDiffAt_pi.mpr
      intro i
      exact (((hρ.contDiffAt.neg.mul hdt.contDiffAt).div hQ.contDiffAt
        (hQpos p hp).ne').mul ((hw i).contDiffAt.mul (hd i).contDiffAt))
    · have hzero : V =ᶠ[𝓝 p] fun _ => 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hp] with q hq
        exact hVzero q (Or.inl hq)
      exact contDiffAt_const.congr_of_eventuallyEq hzero
  · apply hρc.mono
    intro p hp
    exact mt (fun h => hVzero p (Or.inl h)) hp
  · intro p hp
    simp [V, w, hp]
  · intro p
    by_cases hp : ρ p = 0
    · rw [hVzero p (Or.inl hp)]
      simp [hp]
    · have hQne := (hQpos p (subset_tsupport ρ hp)).ne'
      change L p (V p) = -ρ p * dt p
      rw [linear_form_apply]
      calc
        _ = (-ρ p * dt p / Q p) * Q p := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          dsimp [V, d]
          ring
        _ = -ρ p * dt p := div_mul_cancel₀ _ hQne

end DifferentialGeometry.Topology.Morse
