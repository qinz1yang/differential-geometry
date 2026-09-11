import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Basic

noncomputable section

open MeasureTheory Set

namespace DeGiorgi

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem HasWeakPartialDeriv.finset_sum
    {i : Fin d} {Omega : Set E} {ι : Type*} (s : Finset ι)
    {f g : ι → E → ℝ}
    (hf : ∀ j ∈ s, LocallyIntegrable (f j) (volume.restrict Omega))
    (hg : ∀ j ∈ s, LocallyIntegrable (g j) (volume.restrict Omega))
    (hparts : ∀ j ∈ s, HasWeakPartialDeriv i (g j) (f j) Omega) :
    HasWeakPartialDeriv i (fun x => ∑ j ∈ s, g j x)
      (fun x => ∑ j ∈ s, f j x) Omega := by
  classical
  induction s using Finset.induction with
  | empty =>
      intro phi hphi hphi_cpt hphi_sub
      simp
  | insert j s hj ih =>
      simp only [Finset.sum_insert hj]
      exact (hparts j (Finset.mem_insert_self _ _)).add
        (ih (fun k hk => hf k (Finset.mem_insert_of_mem hk))
          (fun k hk => hg k (Finset.mem_insert_of_mem hk))
          (fun k hk => hparts k (Finset.mem_insert_of_mem hk)))
        (hf j (Finset.mem_insert_self _ _))
        (locallyIntegrable_finsetSum s (fun k hk => hf k (Finset.mem_insert_of_mem hk)))
        (hg j (Finset.mem_insert_self _ _))
        (locallyIntegrable_finsetSum s (fun k hk => hg k (Finset.mem_insert_of_mem hk)))

end DeGiorgi
