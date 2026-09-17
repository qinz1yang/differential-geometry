import DifferentialGeometry.Topology.SphereSeparation.CylinderCapDisplacement
import DifferentialGeometry.Topology.Morse.RegularLevel.CriticalSeparation

open Set Metric Manifold
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Topology.SphereSeparation

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

theorem exists_two_morse_cylinderCap_displacements_of_regular_height_between_saddles
    {e : SphereTwo → EuclideanThree} (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (hnd : ∀ x, IsCriticalPointAt (𝓡 2) (fun y => e y 2) x →
      IsNondegenerateCriticalPointAt (𝓡 2) (fun y => e y 2) x)
    (hinj : InjOn (fun y => e y 2) (criticalPoints (𝓡 2) (fun y => e y 2)))
    {c : ℝ} {p q : SphereTwo}
    (hp : IsCriticalPointAt (𝓡 2) (fun y => e y 2) p ∧
      sigNeg (chartHessianAt (fun y => e ((extChartAt (𝓡 2) p).symm y) 2)
        (extChartAt (𝓡 2) p p)) = 1)
    (hq : IsCriticalPointAt (𝓡 2) (fun y => e y 2) q ∧
      sigNeg (chartHessianAt (fun y => e ((extChartAt (𝓡 2) q).symm y) 2)
        (extChartAt (𝓡 2) q q)) = 1)
    (hpc : e p 2 < c) (hcq : c < e q 2)
    (hr : ∀ x, e x 2 = c → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun y => e y 2) x ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ x, e x 2 ∈ Icc (c - ε) (c + ε) → ¬ IsCriticalPointAt (𝓡 2) (fun y => e y 2) x) ∧
      ∃ R : ℝ, 1 < R ∧ ∃ (η : AddCircle (1 : ℝ) → SphereTwo)
        (Ψ : (Schoenflies.Plane × ℝ) ≃ₘ[ℝ] EuclideanThree)
        (b : Fin 2 → ClosedCell 2 → SphereTwo) (σ : ℝ),
        (σ = 1 ∨ σ = -1) ∧ IsSmoothEmbedding 𝓘(ℝ, ℝ) (𝓡 2) ∞ η ∧
        (∀ i, IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ (b i)) ∧
        (∀ i, range (b i ∘ cellBoundaryInclusion 2) = range η) ∧
        range (b 0) ∪ range (b 1) = univ ∧ range (b 0) ∩ range (b 1) = range η ∧
        e '' range η = Ψ '' (sphere (0 : Schoenflies.Plane) 1 ×ˢ {0}) ∧
        (∀ p, Ψ p 2 = c + p.2) ∧
        Ψ ⁻¹' range e ∩ (closedBall (0 : Schoenflies.Plane) R ×ˢ Icc (-ε) ε) =
          sphere (0 : Schoenflies.Plane) 1 ×ˢ Icc (-ε) ε ∧
        let a : Fin 2 → ℝ := fun i => if i = 0 then σ * ε / 2 else -(σ * ε / 2)
        ∃ (χ : Fin 2 → PartialDiffeomorph (𝓡 2) (𝓡 2) Schoenflies.Plane SphereTwo ∞)
          (f : Fin 2 → SphereTwo → EuclideanThree),
          (∀ i, closedBall (0 : Schoenflies.Plane) 1 ⊆ (χ i).source ∧
            χ i '' closedBall (0 : Schoenflies.Plane) 1 = range (b i) ∧
            IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (f i) ∧
            (∀ x ∈ closedBall (0 : Schoenflies.Plane) 1,
              f i (χ i x) = Ψ (EuclideanGeometry.cylinderCap (a i) x)) ∧
            EqOn (f i) e (range (b i))ᶜ ∧
            (∀ y ∈ range (b i), f i =ᶠ[nhds y]
              (Ψ ∘ EuclideanGeometry.cylinderCap (a i)) ∘ (χ i).symm) ∧
            (∀ x, IsCriticalPointAt (𝓡 2) (fun y => f i y 2) x →
              IsNondegenerateCriticalPointAt (𝓡 2) (fun y => f i y 2) x) ∧
            InjOn (fun y => f i y 2) (criticalPoints (𝓡 2) (fun y => f i y 2)) ∧
            criticalPoints (𝓡 2) (fun y => f i y 2) =
              (criticalPoints (𝓡 2) (fun y => e y 2) \ range (b i)) ∪ {χ i 0} ∧
            (criticalPoints (𝓡 2) (fun y => f i y 2)).ncard +
              (criticalPoints (𝓡 2) (fun y => e y 2) ∩ range (b i)).ncard =
                (criticalPoints (𝓡 2) (fun y => e y 2)).ncard + 1 ∧
            ∀ p ∈ ball (0 : Schoenflies.Plane) R ×ˢ Ioo (-ε) ε,
              Ψ p ∈ e '' (range (b i))ᶜ ↔
                ‖p.1‖ = 1 ∧ 0 < (if i = 0 then σ else -σ) * p.2) ∧
          (criticalPoints (𝓡 2) (fun y => f 0 y 2)).ncard +
            (criticalPoints (𝓡 2) (fun y => f 1 y 2)).ncard =
              (criticalPoints (𝓡 2) (fun y => e y 2)).ncard + 2 ∧
          {p | IsCriticalPointAt (𝓡 2) (fun y => f 0 y 2) p ∧ sigNeg (chartHessianAt
            (fun y => f 0 ((extChartAt (𝓡 2) p).symm y) 2) (extChartAt (𝓡 2) p p)) = 1}.ncard +
            {p | IsCriticalPointAt (𝓡 2) (fun y => f 1 y 2) p ∧ sigNeg (chartHessianAt
              (fun y => f 1 ((extChartAt (𝓡 2) p).symm y) 2) (extChartAt (𝓡 2) p p)) = 1}.ncard =
              {p | IsCriticalPointAt (𝓡 2) (fun y => e y 2) p ∧ sigNeg (chartHessianAt
                (fun y => e ((extChartAt (𝓡 2) p).symm y) 2) (extChartAt (𝓡 2) p p)) = 1}.ncard ∧
          ∃ H : Fin 2 → ℝ → (EuclideanThree ≃ₘ[ℝ] EuclideanThree), ∀ i,
            ContDiff ℝ ∞ (fun z : ℝ × EuclideanThree => H i z.1 z.2) ∧
            ContDiff ℝ ∞ (fun z : ℝ × EuclideanThree => (H i z.1).symm z.2) ∧
            H i 0 = Diffeomorph.refl (𝓡 3) EuclideanThree ∞ ∧
            (∀ t, H i t '' range e = range e) ∧
            (∀ t, IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (H i t ∘ f i)) ∧
            range (H i 1 ∘ f i) ∩ {z | z 2 = c} = e '' (range (b i))ᶜ ∩ {z | z 2 = c} ∧
            Nat.card (ConnectedComponents {x : SphereTwo // H i 1 (f i x) 2 = c}) <
              Nat.card (ConnectedComponents {x : SphereTwo // e x 2 = c}) ∧
            (∀ x, H i 1 (f i x) 2 = c →
              mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun y => H i 1 (f i y) 2) x ≠ 0) ∧
            (∀ x, IsCriticalPointAt (𝓡 2) (fun y => H i 1 (f i y) 2) x →
              IsNondegenerateCriticalPointAt (𝓡 2) (fun y => H i 1 (f i y) 2) x) ∧
            InjOn (fun y => H i 1 (f i y) 2)
              (criticalPoints (𝓡 2) (fun y => H i 1 (f i y) 2)) ∧
            criticalPoints (𝓡 2) (fun y => H i 1 (f i y) 2) =
              criticalPoints (𝓡 2) (fun y => f i y 2) ∧
            (∀ x, IsCriticalPointAt (𝓡 2) (fun y => f i y 2) x →
              chartHessianAt (fun y => H i 1 (f i ((extChartAt (𝓡 2) x).symm y)) 2)
                (extChartAt (𝓡 2) x x) =
              chartHessianAt (fun y => f i ((extChartAt (𝓡 2) x).symm y) 2)
                (extChartAt (𝓡 2) x x)) ∧
            (∀ k : ℕ,
              {p | IsCriticalPointAt (𝓡 2) (fun y => H i 1 (f i y) 2) p ∧
                sigNeg (chartHessianAt
                  (fun y => H i 1 (f i ((extChartAt (𝓡 2) p).symm y)) 2)
                  (extChartAt (𝓡 2) p p)) = k} =
              {p | IsCriticalPointAt (𝓡 2) (fun y => f i y 2) p ∧
                sigNeg (chartHessianAt (fun y => f i ((extChartAt (𝓡 2) p).symm y) 2)
                  (extChartAt (𝓡 2) p p)) = k}) ∧
            (∀ x, IsCriticalPointAt (𝓡 2) (fun y => e y 2) x →
              x ∉ range (b i) → H i 1 (f i x) = e x) ∧
            H i 1 (f i (χ i 0)) 2 = c + (if i = 0 then σ else -σ) * ε / 4 ∧
            (∀ x ∈ closedBall (0 : Schoenflies.Plane) 1,
              0 < (if i = 0 then σ else -σ) * (H i 1 (f i (χ i x)) 2 - c)) ∧
            {x | IsCriticalPointAt (𝓡 2) (fun y => H i 1 (f i y) 2) x ∧
              sigNeg (chartHessianAt (fun y => H i 1 (f i ((extChartAt (𝓡 2) x).symm y)) 2)
                (extChartAt (𝓡 2) x x)) = 1} =
              {x | IsCriticalPointAt (𝓡 2) (fun y => e y 2) x ∧
                sigNeg (chartHessianAt (fun y => e ((extChartAt (𝓡 2) x).symm y) 2)
                  (extChartAt (𝓡 2) x x)) = 1} \ range (b i) ∧
            {x | IsCriticalPointAt (𝓡 2) (fun y => H i 1 (f i y) 2) x ∧
              sigNeg (chartHessianAt (fun y => H i 1 (f i ((extChartAt (𝓡 2) x).symm y)) 2)
                (extChartAt (𝓡 2) x x)) = 1}.ncard ≤
              {x | IsCriticalPointAt (𝓡 2) (fun y => e y 2) x ∧
                sigNeg (chartHessianAt (fun y => e ((extChartAt (𝓡 2) x).symm y) 2)
                  (extChartAt (𝓡 2) x x)) = 1}.ncard ∧
            ({x | IsCriticalPointAt (𝓡 2) (fun y => H i 1 (f i y) 2) x ∧
              sigNeg (chartHessianAt (fun y => H i 1 (f i ((extChartAt (𝓡 2) x).symm y)) 2)
                (extChartAt (𝓡 2) x x)) = 1}.ncard =
              {x | IsCriticalPointAt (𝓡 2) (fun y => e y 2) x ∧
                sigNeg (chartHessianAt (fun y => e ((extChartAt (𝓡 2) x).symm y) 2)
                  (extChartAt (𝓡 2) x x)) = 1}.ncard →
              H i 1 (f i p) 2 < c ∧ c < H i 1 (f i q) 2 ∧ ∃ x, H i 1 (f i x) 2 = c) ∧
            ∃ U : Set (Schoenflies.Plane × ℝ), IsOpen U ∧
              EuclideanGeometry.cylinderCap (a i) '' closedBall (0 : Schoenflies.Plane) 1 ⊆ U ∧
              (∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ U,
                H i t (Ψ p) = Ψ (p.1, p.2 + t * ((if i = 0 then σ else -σ) * (3 * ε / 4)))) ∧
            ∃ J : Set EuclideanThree, IsCompact J ∧
              J ⊆ Ψ '' (ball (0 : Schoenflies.Plane) R ×ˢ Ioo (-ε) ε) ∧
              ∀ t : ℝ, EqOn (H i t) id Jᶜ ∧ EqOn (H i t).symm id Jᶜ := by
  classical
  let S (g : SphereTwo → EuclideanThree) : Set SphereTwo :=
    {p | IsCriticalPointAt (𝓡 2) (fun y => g y 2) p ∧
      sigNeg (chartHessianAt (fun y => g ((extChartAt (𝓡 2) p).symm y) 2)
        (extChartAt (𝓡 2) p p)) = 1}
  have heh : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun y => e y 2) :=
    (EuclideanSpace.proj 2).contMDiff.comp he.contMDiff
  have hfinite := DifferentialGeometry.Morse.finite_criticalPoints_of_isCompact heh isCompact_univ
    (fun _ _ => BoundarylessManifold.isInteriorPoint) (fun _ _ => mem_univ _) hnd
  have hSfinite : (S e).Finite := hfinite.subset (fun _ hx => hx.1)
  have hne : ∃ x, e x 2 = c := intermediate_value_univ p q heh.continuous ⟨hpc.le, hcq.le⟩
  obtain ⟨ε, hε, hregular, R, hR, η, Ψ, b, σ, hσ, hη, hb, hbd, hcover, hinter,
    hboundary, hheight, hsphere, χ, f, hf, hcount, hrawSaddles, H, hH⟩ :=
    exists_two_morse_cylinderCap_displacements_of_regular_height he hnd hinj hne hr
  let a : Fin 2 → ℝ := fun i => if i = 0 then σ * ε / 2 else -(σ * ε / 2)
  have ha (i : Fin 2) : a i ≠ 0 := by
    dsimp [a]
    rcases hσ with hσ | hσ <;> rw [hσ] <;> split_ifs <;> nlinarith
  have hD (i : Fin 2) : IsClosed (range (b i)) :=
    (isCompact_range (hb i).contMDiff.continuous).isClosed
  have hrawIndex (i : Fin 2) : S (f i) = S e \ range (b i) := by
    have hfh : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun y => f i y 2) :=
      (EuclideanSpace.proj 2).contMDiff.comp (hf i).2.2.1.contMDiff
    exact criticalPoints_with_index_cylinderCap_replacement
      (h := fun z : EuclideanThree => z 2) hfh (χ i) (hf i).1 (hD i) (hf i).2.1
      (hf i).2.2.2.2.1 (ha i) hheight (hf i).2.2.2.2.2.1
      (by norm_num : 0 < (1 : ℕ)) (by simp : 1 < Module.finrank ℝ Schoenflies.Plane)
  refine ⟨ε, hε, hregular, R, hR,
    η, Ψ, b, σ, hσ, hη, hb, hbd, hcover, hinter, hboundary, hheight, hsphere,
    χ, f, hf, hcount, hrawSaddles, H, ?_⟩
  intro i
  obtain ⟨hHsmooth, hHinv, hH0, hHS, hHf, hlevel, hcomponentCount, hregularg,
    hndg, hinjg, hcritg, hessg, hindexg, hfixed, hcenter, hpositive,
    U, hU, hcapU, hmove, J, hJ, hJU, hsupport⟩ := hH i
  have hSg : S (H i 1 ∘ f i) = S e \ range (b i) := (hindexg 1).trans (hrawIndex i)
  have hsubset : S (H i 1 ∘ f i) ⊆ S e := hSg.subset.trans sdiff_subset
  have hcardle := ncard_le_ncard hsubset hSfinite
  refine ⟨hHsmooth, hHinv, hH0, hHS, hHf, hlevel, hcomponentCount, hregularg,
    hndg, hinjg, hcritg, hessg, hindexg, hfixed, hcenter, hpositive,
    hSg, hcardle, ?_, U, hU, hcapU, hmove, J, hJ, hJU, hsupport⟩
  intro hcardeq
  have heq : S (H i 1 ∘ f i) = S e := eq_of_subset_of_ncard_le hsubset hcardeq.ge hSfinite
  have hpnew : p ∈ S (H i 1 ∘ f i) := heq.symm.subset hp
  have hqnew : q ∈ S (H i 1 ∘ f i) := heq.symm.subset hq
  have hgp : H i 1 (f i p) 2 < c := by
    rw [hfixed p hp.1 (hSg.subset hpnew).2]
    exact hpc
  have hgq : c < H i 1 (f i q) 2 := by
    rw [hfixed q hq.1 (hSg.subset hqnew).2]
    exact hcq
  refine ⟨hgp, hgq, ?_⟩
  exact intermediate_value_univ p q
    ((EuclideanSpace.proj 2).contMDiff.comp (hHf 1).contMDiff).continuous ⟨hgp.le, hgq.le⟩


theorem exists_regular_height_cylinderCap_displacements_of_two_le_ncard_saddles
    {e : SphereTwo → EuclideanThree} (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (hnd : ∀ x, IsCriticalPointAt (𝓡 2) (fun y => e y 2) x →
      IsNondegenerateCriticalPointAt (𝓡 2) (fun y => e y 2) x)
    (hinj : InjOn (fun y => e y 2) (criticalPoints (𝓡 2) (fun y => e y 2)))
    (hsaddles : 2 ≤ {p | IsCriticalPointAt (𝓡 2) (fun y => e y 2) p ∧
      sigNeg (chartHessianAt (fun y => e ((extChartAt (𝓡 2) p).symm y) 2)
        (extChartAt (𝓡 2) p p)) = 1}.ncard) :
    ∃ (c : ℝ) (p q : SphereTwo),
      (IsCriticalPointAt (𝓡 2) (fun y => e y 2) p ∧
        sigNeg (chartHessianAt (fun y => e ((extChartAt (𝓡 2) p).symm y) 2)
          (extChartAt (𝓡 2) p p)) = 1) ∧
      (IsCriticalPointAt (𝓡 2) (fun y => e y 2) q ∧
        sigNeg (chartHessianAt (fun y => e ((extChartAt (𝓡 2) q).symm y) 2)
          (extChartAt (𝓡 2) q q)) = 1) ∧
      e p 2 < c ∧ c < e q 2 ∧ (∃ x, e x 2 = c) ∧
      (∀ x, e x 2 = c → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun y => e y 2) x ≠ 0) ∧
    ∃ ε : ℝ, 0 < ε ∧
      (∀ x, e x 2 ∈ Icc (c - ε) (c + ε) → ¬ IsCriticalPointAt (𝓡 2) (fun y => e y 2) x) ∧
      ∃ R : ℝ, 1 < R ∧ ∃ (η : AddCircle (1 : ℝ) → SphereTwo)
        (Ψ : (Schoenflies.Plane × ℝ) ≃ₘ[ℝ] EuclideanThree)
        (b : Fin 2 → ClosedCell 2 → SphereTwo) (σ : ℝ),
        (σ = 1 ∨ σ = -1) ∧ IsSmoothEmbedding 𝓘(ℝ, ℝ) (𝓡 2) ∞ η ∧
        (∀ i, IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ (b i)) ∧
        (∀ i, range (b i ∘ cellBoundaryInclusion 2) = range η) ∧
        range (b 0) ∪ range (b 1) = univ ∧ range (b 0) ∩ range (b 1) = range η ∧
        e '' range η = Ψ '' (sphere (0 : Schoenflies.Plane) 1 ×ˢ {0}) ∧
        (∀ p, Ψ p 2 = c + p.2) ∧
        Ψ ⁻¹' range e ∩ (closedBall (0 : Schoenflies.Plane) R ×ˢ Icc (-ε) ε) =
          sphere (0 : Schoenflies.Plane) 1 ×ˢ Icc (-ε) ε ∧
        let a : Fin 2 → ℝ := fun i => if i = 0 then σ * ε / 2 else -(σ * ε / 2)
        ∃ (χ : Fin 2 → PartialDiffeomorph (𝓡 2) (𝓡 2) Schoenflies.Plane SphereTwo ∞)
          (f : Fin 2 → SphereTwo → EuclideanThree),
          (∀ i, closedBall (0 : Schoenflies.Plane) 1 ⊆ (χ i).source ∧
            χ i '' closedBall (0 : Schoenflies.Plane) 1 = range (b i) ∧
            IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (f i) ∧
            (∀ x ∈ closedBall (0 : Schoenflies.Plane) 1,
              f i (χ i x) = Ψ (EuclideanGeometry.cylinderCap (a i) x)) ∧
            EqOn (f i) e (range (b i))ᶜ ∧
            (∀ y ∈ range (b i), f i =ᶠ[nhds y]
              (Ψ ∘ EuclideanGeometry.cylinderCap (a i)) ∘ (χ i).symm) ∧
            (∀ x, IsCriticalPointAt (𝓡 2) (fun y => f i y 2) x →
              IsNondegenerateCriticalPointAt (𝓡 2) (fun y => f i y 2) x) ∧
            InjOn (fun y => f i y 2) (criticalPoints (𝓡 2) (fun y => f i y 2)) ∧
            criticalPoints (𝓡 2) (fun y => f i y 2) =
              (criticalPoints (𝓡 2) (fun y => e y 2) \ range (b i)) ∪ {χ i 0} ∧
            (criticalPoints (𝓡 2) (fun y => f i y 2)).ncard +
              (criticalPoints (𝓡 2) (fun y => e y 2) ∩ range (b i)).ncard =
                (criticalPoints (𝓡 2) (fun y => e y 2)).ncard + 1 ∧
            ∀ p ∈ ball (0 : Schoenflies.Plane) R ×ˢ Ioo (-ε) ε,
              Ψ p ∈ e '' (range (b i))ᶜ ↔
                ‖p.1‖ = 1 ∧ 0 < (if i = 0 then σ else -σ) * p.2) ∧
          (criticalPoints (𝓡 2) (fun y => f 0 y 2)).ncard +
            (criticalPoints (𝓡 2) (fun y => f 1 y 2)).ncard =
              (criticalPoints (𝓡 2) (fun y => e y 2)).ncard + 2 ∧
          {p | IsCriticalPointAt (𝓡 2) (fun y => f 0 y 2) p ∧ sigNeg (chartHessianAt
            (fun y => f 0 ((extChartAt (𝓡 2) p).symm y) 2) (extChartAt (𝓡 2) p p)) = 1}.ncard +
            {p | IsCriticalPointAt (𝓡 2) (fun y => f 1 y 2) p ∧ sigNeg (chartHessianAt
              (fun y => f 1 ((extChartAt (𝓡 2) p).symm y) 2) (extChartAt (𝓡 2) p p)) = 1}.ncard =
              {p | IsCriticalPointAt (𝓡 2) (fun y => e y 2) p ∧ sigNeg (chartHessianAt
                (fun y => e ((extChartAt (𝓡 2) p).symm y) 2) (extChartAt (𝓡 2) p p)) = 1}.ncard ∧
          ∃ H : Fin 2 → ℝ → (EuclideanThree ≃ₘ[ℝ] EuclideanThree), ∀ i,
            ContDiff ℝ ∞ (fun z : ℝ × EuclideanThree => H i z.1 z.2) ∧
            ContDiff ℝ ∞ (fun z : ℝ × EuclideanThree => (H i z.1).symm z.2) ∧
            H i 0 = Diffeomorph.refl (𝓡 3) EuclideanThree ∞ ∧
            (∀ t, H i t '' range e = range e) ∧
            (∀ t, IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (H i t ∘ f i)) ∧
            range (H i 1 ∘ f i) ∩ {z | z 2 = c} = e '' (range (b i))ᶜ ∩ {z | z 2 = c} ∧
            Nat.card (ConnectedComponents {x : SphereTwo // H i 1 (f i x) 2 = c}) <
              Nat.card (ConnectedComponents {x : SphereTwo // e x 2 = c}) ∧
            (∀ x, H i 1 (f i x) 2 = c →
              mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun y => H i 1 (f i y) 2) x ≠ 0) ∧
            (∀ x, IsCriticalPointAt (𝓡 2) (fun y => H i 1 (f i y) 2) x →
              IsNondegenerateCriticalPointAt (𝓡 2) (fun y => H i 1 (f i y) 2) x) ∧
            InjOn (fun y => H i 1 (f i y) 2)
              (criticalPoints (𝓡 2) (fun y => H i 1 (f i y) 2)) ∧
            criticalPoints (𝓡 2) (fun y => H i 1 (f i y) 2) =
              criticalPoints (𝓡 2) (fun y => f i y 2) ∧
            (∀ x, IsCriticalPointAt (𝓡 2) (fun y => f i y 2) x →
              chartHessianAt (fun y => H i 1 (f i ((extChartAt (𝓡 2) x).symm y)) 2)
                (extChartAt (𝓡 2) x x) =
              chartHessianAt (fun y => f i ((extChartAt (𝓡 2) x).symm y) 2)
                (extChartAt (𝓡 2) x x)) ∧
            (∀ k : ℕ,
              {p | IsCriticalPointAt (𝓡 2) (fun y => H i 1 (f i y) 2) p ∧
                sigNeg (chartHessianAt
                  (fun y => H i 1 (f i ((extChartAt (𝓡 2) p).symm y)) 2)
                  (extChartAt (𝓡 2) p p)) = k} =
              {p | IsCriticalPointAt (𝓡 2) (fun y => f i y 2) p ∧
                sigNeg (chartHessianAt (fun y => f i ((extChartAt (𝓡 2) p).symm y) 2)
                  (extChartAt (𝓡 2) p p)) = k}) ∧
            (∀ x, IsCriticalPointAt (𝓡 2) (fun y => e y 2) x →
              x ∉ range (b i) → H i 1 (f i x) = e x) ∧
            H i 1 (f i (χ i 0)) 2 = c + (if i = 0 then σ else -σ) * ε / 4 ∧
            (∀ x ∈ closedBall (0 : Schoenflies.Plane) 1,
              0 < (if i = 0 then σ else -σ) * (H i 1 (f i (χ i x)) 2 - c)) ∧
            {x | IsCriticalPointAt (𝓡 2) (fun y => H i 1 (f i y) 2) x ∧
              sigNeg (chartHessianAt (fun y => H i 1 (f i ((extChartAt (𝓡 2) x).symm y)) 2)
                (extChartAt (𝓡 2) x x)) = 1} =
              {x | IsCriticalPointAt (𝓡 2) (fun y => e y 2) x ∧
                sigNeg (chartHessianAt (fun y => e ((extChartAt (𝓡 2) x).symm y) 2)
                  (extChartAt (𝓡 2) x x)) = 1} \ range (b i) ∧
            {x | IsCriticalPointAt (𝓡 2) (fun y => H i 1 (f i y) 2) x ∧
              sigNeg (chartHessianAt (fun y => H i 1 (f i ((extChartAt (𝓡 2) x).symm y)) 2)
                (extChartAt (𝓡 2) x x)) = 1}.ncard ≤
              {x | IsCriticalPointAt (𝓡 2) (fun y => e y 2) x ∧
                sigNeg (chartHessianAt (fun y => e ((extChartAt (𝓡 2) x).symm y) 2)
                  (extChartAt (𝓡 2) x x)) = 1}.ncard ∧
            ({x | IsCriticalPointAt (𝓡 2) (fun y => H i 1 (f i y) 2) x ∧
              sigNeg (chartHessianAt (fun y => H i 1 (f i ((extChartAt (𝓡 2) x).symm y)) 2)
                (extChartAt (𝓡 2) x x)) = 1}.ncard =
              {x | IsCriticalPointAt (𝓡 2) (fun y => e y 2) x ∧
                sigNeg (chartHessianAt (fun y => e ((extChartAt (𝓡 2) x).symm y) 2)
                  (extChartAt (𝓡 2) x x)) = 1}.ncard →
              H i 1 (f i p) 2 < c ∧ c < H i 1 (f i q) 2 ∧ ∃ x, H i 1 (f i x) 2 = c) ∧
            ∃ U : Set (Schoenflies.Plane × ℝ), IsOpen U ∧
              EuclideanGeometry.cylinderCap (a i) '' closedBall (0 : Schoenflies.Plane) 1 ⊆ U ∧
              (∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ U,
                H i t (Ψ p) = Ψ (p.1, p.2 + t * ((if i = 0 then σ else -σ) * (3 * ε / 4)))) ∧
            ∃ J : Set EuclideanThree, IsCompact J ∧
              J ⊆ Ψ '' (ball (0 : Schoenflies.Plane) R ×ˢ Ioo (-ε) ε) ∧
              ∀ t : ℝ, EqOn (H i t) id Jᶜ ∧ EqOn (H i t).symm id Jᶜ := by
  classical
  let S (g : SphereTwo → EuclideanThree) : Set SphereTwo :=
    {p | IsCriticalPointAt (𝓡 2) (fun y => g y 2) p ∧
      sigNeg (chartHessianAt (fun y => g ((extChartAt (𝓡 2) p).symm y) 2)
        (extChartAt (𝓡 2) p p)) = 1}
  have heh : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun y => e y 2) :=
    (EuclideanSpace.proj 2).contMDiff.comp he.contMDiff
  have hfinite := DifferentialGeometry.Morse.finite_criticalPoints_of_isCompact heh isCompact_univ
    (fun _ _ => BoundarylessManifold.isInteriorPoint) (fun _ _ => mem_univ _) hnd
  have hSfinite : (S e).Finite := hfinite.subset (fun _ hx => hx.1)
  have hpq : ∃ p ∈ S e, ∃ q ∈ S e, e p 2 < e q 2 := by
    obtain ⟨p, hp, q, hq, hpq⟩ :=
      (one_lt_ncard hSfinite).mp (lt_of_lt_of_le (by decide : 1 < 2) hsaddles)
    have hne : e p 2 ≠ e q 2 := fun h => hpq (hinj hp.1 hq.1 h)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨p, hp, q, hq, hlt⟩
    · exact ⟨q, hq, p, hp, hgt⟩
  obtain ⟨p, hp, q, hq, hpq⟩ := hpq
  obtain ⟨c, ⟨hpc, hcq⟩, hr⟩ := exists_regular_level_between_of_finite_criticalPoints hfinite hpq
  have hne : ∃ x, e x 2 = c := intermediate_value_univ p q heh.continuous ⟨hpc.le, hcq.le⟩
  exact ⟨c, p, q, hp, hq, hpc, hcq, hne, hr,
    exists_two_morse_cylinderCap_displacements_of_regular_height_between_saddles
      he hnd hinj hp hq hpc hcq hr⟩

end DifferentialGeometry.Topology.SphereSeparation
