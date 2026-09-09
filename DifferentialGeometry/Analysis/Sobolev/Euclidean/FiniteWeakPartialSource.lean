import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.WeakPartial
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.SmoothCoefWeakPartialIBP

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem memWkp_mul_of_finite_weak_partial_trees
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω) (K : ℕ)
    (A Y : ∀ n : ℕ, (Fin n → Fin d) → E → ℝ)
    (hA : ∀ n ≤ K, ∀ α, MemLp (A n α) ∞ (volume.restrict Ω))
    (hY : ∀ n ≤ K, ∀ α, MemLp (Y n α) p (volume.restrict Ω))
    (hAsmooth : ∀ n < K, ∀ α, ContDiffOn ℝ (⊤ : ℕ∞) (A n α) Ω)
    (hDA : ∀ n < K, ∀ α i,
      A (n + 1) (Fin.cons i α) =ᵐ[volume.restrict Ω]
        fun x => fderiv ℝ (A n α) x (EuclideanSpace.single i 1))
    (hYweak : ∀ n < K, ∀ α i,
      DeGiorgi.HasWeakPartialDeriv i (Y (n + 1) (Fin.cons i α)) (Y n α) Ω) :
    MemWkp K p (fun x => A 0 (fun i => Fin.elim0 i) x *
      Y 0 (fun i => Fin.elim0 i) x) Ω := by
  have hnode : ∀ k n m α β, n + k ≤ K → m + k ≤ K →
      MemWkp k p (fun x => A n α x * Y m β x) Ω := by
    intro k
    induction k with
    | zero =>
        intro n m α β hn hm
        exact (hY m (by omega) β).mul (hA n (by omega) α)
    | succ k ih =>
        intro n m α β hn hm
        have hnK : n < K := by omega
        have hmK : m < K := by omega
        apply memWkp_succ_of_hasWeakPartialDeriv hp hΩ
          ((hY m (by omega) β).mul (hA n (by omega) α))
          (g := fun i x => A n α x * Y (m + 1) (Fin.cons i β) x +
            A (n + 1) (Fin.cons i α) x * Y m β x)
        · intro i
          exact MemWkp.add hp hΩ
            (ih n (m + 1) α (Fin.cons i β) (by omega) (by omega))
            (ih (n + 1) m (Fin.cons i α) β (by omega) (by omega))
        · intro i
          have hw := (hYweak m hmK β i).mul_contDiffOn hΩ (hAsmooth n hnK α)
            ((hY m (by omega) β).locallyIntegrable hp)
            ((hY (m + 1) (by omega) (Fin.cons i β)).locallyIntegrable hp)
          intro φ hφ hφc hφs
          refine (hw φ hφ hφc hφs).trans ?_
          congr 1
          apply integral_congr_ae
          filter_upwards [hDA n hnK α i] with x hx
          rw [hx]
  exact hnode K 0 0 (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (by omega) (by omega)

theorem ae_memWkp_of_finite_sum_weak_partial_trees
    {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] {μ : Measure Z}
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω) (K : ℕ)
    (f : Z × E → ℝ)
    (A Y : ι → ∀ n : ℕ, (Fin n → Fin d) → Z × E → ℝ)
    (hA : ∀ j n, n ≤ K → ∀ α, MemLp (A j n α) ∞ (μ.prod (volume.restrict Ω)))
    (hY : ∀ j n, n ≤ K → ∀ α, MemLp (Y j n α) p (μ.prod (volume.restrict Ω)))
    (hAsmooth : ∀ j n, n < K → ∀ α, ∀ᵐ t ∂μ,
      ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A j n α (t, x)) Ω)
    (hDA : ∀ j n, n < K → ∀ α i,
      A j (n + 1) (Fin.cons i α) =ᵐ[μ.prod (volume.restrict Ω)]
        fun q => fderiv ℝ (fun x => A j n α (q.1, x)) q.2 (EuclideanSpace.single i 1))
    (hYweak : ∀ j n, n < K → ∀ α i, ∀ᵐ t ∂μ,
      DeGiorgi.HasWeakPartialDeriv i
        (fun x => Y j (n + 1) (Fin.cons i α) (t, x))
        (fun x => Y j n α (t, x)) Ω)
    (hf : f =ᵐ[μ.prod (volume.restrict Ω)] fun q => ∑ j,
      A j 0 (fun i => Fin.elim0 i) q * Y j 0 (fun i => Fin.elim0 i) q) :
    ∀ᵐ t ∂μ, MemWkp K p (fun x => f (t, x)) Ω := by
  classical
  have hAslice : ∀ j n (hn : n ≤ K) α, ∀ᵐ t ∂μ,
      MemLp (fun x => A j n α (t, x)) ∞ (volume.restrict Ω) :=
    fun j n hn α => (hA j n hn α).prodMk_left_top
  have hYslice : ∀ j n (hn : n ≤ K) α, ∀ᵐ t ∂μ,
      MemLp (fun x => Y j n α (t, x)) p (volume.restrict Ω) := by
    intro j n hn α
    by_cases hptop : p = ⊤
    · subst p
      exact (hY j n hn α).prodMk_left_top
    · exact (hY j n hn α).prodMk_left hptop
  have hDAslice : ∀ j n (hn : n < K) α i, ∀ᵐ t ∂μ,
      (fun x => A j (n + 1) (Fin.cons i α) (t, x)) =ᵐ[volume.restrict Ω]
        fun x => fderiv ℝ (fun y => A j n α (t, y)) x (EuclideanSpace.single i 1) :=
    fun j n hn α i => Measure.ae_ae_of_ae_prod (hDA j n hn α i)
  have hAp := ae_all_iff.mpr fun j => ae_all_iff.mpr fun n =>
    ae_all_iff.mpr fun hn => ae_all_iff.mpr (hAslice j n hn)
  have hYp := ae_all_iff.mpr fun j => ae_all_iff.mpr fun n =>
    ae_all_iff.mpr fun hn => ae_all_iff.mpr (hYslice j n hn)
  have hAsp := ae_all_iff.mpr fun j => ae_all_iff.mpr fun n =>
    ae_all_iff.mpr fun hn => ae_all_iff.mpr (hAsmooth j n hn)
  have hDAp := ae_all_iff.mpr fun j => ae_all_iff.mpr fun n =>
    ae_all_iff.mpr fun hn => ae_all_iff.mpr fun α => ae_all_iff.mpr (hDAslice j n hn α)
  have hYwp := ae_all_iff.mpr fun j => ae_all_iff.mpr fun n =>
    ae_all_iff.mpr fun hn => ae_all_iff.mpr fun α => ae_all_iff.mpr (hYweak j n hn α)
  filter_upwards [hAp, hYp, hAsp, hDAp, hYwp, Measure.ae_ae_of_ae_prod hf]
    with t hAt hYt hAst hDAt hYwt hft
  apply (MemWkp_congr_ae hp hΩ hft).mpr
  have hterm (j : ι) : MemWkp K p (fun x =>
      A j 0 (fun i => Fin.elim0 i) (t, x) * Y j 0 (fun i => Fin.elim0 i) (t, x)) Ω :=
    memWkp_mul_of_finite_weak_partial_trees hp hΩ K
      (fun n α x => A j n α (t, x)) (fun n α x => Y j n α (t, x))
      (hAt j) (hYt j) (hAst j) (hDAt j) (hYwt j)
  have hsum (s : Finset ι) : MemWkp K p (fun x => ∑ j ∈ s,
      A j 0 (fun i => Fin.elim0 i) (t, x) * Y j 0 (fun i => Fin.elim0 i) (t, x)) Ω := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using (MemWkp_zero_fun (k := K) hp hΩ)
    | @insert j s hj ih =>
        simpa only [Finset.sum_insert hj] using MemWkp.add hp hΩ (hterm j) ih
  exact hsum Finset.univ

end DifferentialGeometry.Analysis.Sobolev.Euclidean
