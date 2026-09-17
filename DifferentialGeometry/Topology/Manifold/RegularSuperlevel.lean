import DifferentialGeometry.Topology.Manifold.RegularNeighborhood
import DifferentialGeometry.Topology.Manifold.RegularDomain

noncomputable section

open Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] {H : Type} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_isManifold_superlevel
    (f : M → ℝ) (r : ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = r → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    ∃ m : ℕ, Module.finrank ℝ E = m + 1 ∧
      ∃ cs : ChartedSpace (EuclideanHalfSpace (m + 1)) {x : M // r ≤ f x},
        letI := cs
        IsManifold (modelWithCornersEuclideanHalfSpace (m + 1)) ∞ {x : M // r ≤ f x} ∧
        ContMDiff (modelWithCornersEuclideanHalfSpace (m + 1)) I ∞
          (fun x : {x : M // r ≤ f x} => x.1) ∧
        (∀ x : {x : M // r ≤ f x}, Function.Bijective
          (mfderiv (modelWithCornersEuclideanHalfSpace (m + 1)) I
            (fun y : {x : M // r ≤ f x} => y.1) x)) ∧
        (∀ x : {x : M // r ≤ f x},
          (modelWithCornersEuclideanHalfSpace (m + 1)).IsBoundaryPoint x ↔ f x.1 = r) := by
  have hneg : ∀ x : M, (-f) x = -r → ¬ Morse.IsCriticalPointAt I (-f) x := by
    intro x hx hc
    apply hreg x (neg_inj.mp hx)
    change mfderiv I 𝓘(ℝ, ℝ) (-f) x = 0 at hc
    rw [mfderiv_neg] at hc
    exact neg_eq_zero.mp hc
  have heq : Morse.sublevel (-f) (-r) = {x | r ≤ f x} := by
    ext x
    simp only [Morse.sublevel, mem_preimage, mem_Iic, Pi.neg_apply, neg_le_neg_iff,
      mem_ofPred_eq]
  let P (S : Set M) : Prop := ∃ m : ℕ, Module.finrank ℝ E = m + 1 ∧
    ∃ cs : ChartedSpace (EuclideanHalfSpace (m + 1)) S,
      letI := cs
      IsManifold (modelWithCornersEuclideanHalfSpace (m + 1)) ∞ S ∧
      ContMDiff (modelWithCornersEuclideanHalfSpace (m + 1)) I ∞
        (fun x : S => x.1) ∧
      (∀ x : S, Function.Bijective
        (mfderiv (modelWithCornersEuclideanHalfSpace (m + 1)) I (fun y : S => y.1) x)) ∧
      (∀ x : S, (modelWithCornersEuclideanHalfSpace (m + 1)).IsBoundaryPoint x ↔ f x.1 = r)
  have h : P (Morse.sublevel (-f) (-r)) := by
    simpa only [P, Pi.neg_apply, neg_inj] using
      Morse.exists_isManifold_sublevel (-f) (-r) hf.neg hneg
  change P {x | r ≤ f x}
  exact Eq.mp (congrArg P heq) h

theorem exists_compact_regular_superlevel_manifold_between [T2Space M]
    {K U : Set M} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (f : M → ℝ) (r : ℝ),
      ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ U ∧
      (∀ x, 0 ≤ f x) ∧ (∀ x ∈ K, 1 ≤ f x) ∧ r ∈ Ioo (0 : ℝ) 1 ∧
      IsCompact {x | r ≤ f x} ∧ K ⊆ interior {x | r ≤ f x} ∧
      {x | r ≤ f x} ⊆ U ∧
      interior {x | r ≤ f x} = {x | r < f x} ∧
      closure {x | r < f x} = {x | r ≤ f x} ∧
      frontier {x | r ≤ f x} = {x | f x = r} ∧
      (∀ x, f x = r → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) ∧
      ∃ m : ℕ, Module.finrank ℝ E = m + 1 ∧
        ∃ cs : ChartedSpace (EuclideanHalfSpace (m + 1)) {x : M // r ≤ f x},
          letI := cs
          IsManifold (modelWithCornersEuclideanHalfSpace (m + 1)) ∞ {x : M // r ≤ f x} ∧
          ContMDiff (modelWithCornersEuclideanHalfSpace (m + 1)) I ∞
            (fun x : {x : M // r ≤ f x} => x.1) ∧
          (∀ x : {x : M // r ≤ f x}, Function.Bijective
            (mfderiv (modelWithCornersEuclideanHalfSpace (m + 1)) I
              (fun y : {x : M // r ≤ f x} => y.1) x)) ∧
          (∀ x : {x : M // r ≤ f x},
            (modelWithCornersEuclideanHalfSpace (m + 1)).IsBoundaryPoint x ↔ f x.1 = r) := by
  obtain ⟨f, r, hf, hc, hs, hn, hk, hr, hd, hki, hdu, hi, hcl, hfr, hreg⟩ :=
    exists_compact_regular_superlevel_between (I := I) hK hU hKU
  exact ⟨f, r, hf, hc, hs, hn, hk, hr, hd, hki, hdu, hi, hcl, hfr, hreg,
    exists_isManifold_superlevel f r hf hreg⟩

end DifferentialGeometry.Topology.Manifold
