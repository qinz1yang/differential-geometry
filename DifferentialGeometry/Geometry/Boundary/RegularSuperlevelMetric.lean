import DifferentialGeometry.Topology.Manifold.RegularSuperlevel
import DifferentialGeometry.Geometry.Metric.Pullback.Immersion

noncomputable section

open Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] {H : Type} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem exists_compact_regular_superlevel_pullback_between
    (g : SmoothRiemannianMetric I M)
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
          ∃ hM : IsManifold (modelWithCornersEuclideanHalfSpace (m + 1)) ∞ {x : M // r ≤ f x},
            letI := hM
            ContMDiff (modelWithCornersEuclideanHalfSpace (m + 1)) I ∞
              (fun x : {x : M // r ≤ f x} => x.1) ∧
            (∀ x : {x : M // r ≤ f x}, Function.Bijective
              (mfderiv (modelWithCornersEuclideanHalfSpace (m + 1)) I
                (fun y : {x : M // r ≤ f x} => y.1) x)) ∧
            (∀ x : {x : M // r ≤ f x},
              (modelWithCornersEuclideanHalfSpace (m + 1)).IsBoundaryPoint x ↔ f x.1 = r) ∧
            ∃ gD : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace (m + 1))
                {x : M // r ≤ f x},
              ∀ x v w, gD.inner x v w = g.inner x.1
                (mfderiv (modelWithCornersEuclideanHalfSpace (m + 1)) I
                  (fun y : {x : M // r ≤ f x} => y.1) x v)
                (mfderiv (modelWithCornersEuclideanHalfSpace (m + 1)) I
                  (fun y : {x : M // r ≤ f x} => y.1) x w) := by
  obtain ⟨f, r, hf, hc, hs, hn, hk, hr, hd, hki, hdu, hi, hcl, hfr, hreg,
      m, hm, cs, hM, hinc, hbij, hboundary⟩ :=
    exists_compact_regular_superlevel_manifold_between (I := I) hK hU hKU
  let := cs
  let := hM
  refine ⟨f, r, hf, hc, hs, hn, hk, hr, hd, hki, hdu, hi, hcl, hfr, hreg,
    m, hm, cs, hM, hinc, hbij, hboundary, ?_⟩
  exact ⟨g.pullback (fun x : {x : M // r ≤ f x} => x.1) hinc
    (fun x => (hbij x).injective), fun _ _ _ => rfl⟩

end DifferentialGeometry.Topology.Manifold
