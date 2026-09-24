import DifferentialGeometry.Topology.Manifold.IntervalExtension
import DifferentialGeometry.Topology.Manifold.AddCircle.Descent
import DifferentialGeometry.Topology.LoopSpace.ImmersionStability
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LoopFamilyVelocityExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ImmersedPersistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.Loops

noncomputable section

open Set Manifold
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open Surgery.Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

theorem contMDiff_uncurry_of_smoothOn_univ
    (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) univ) :
    ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) I ∞
      (fun p : ℝ × Surgery.Topology.Circle => γ p.1 p.2) := by
  rw [← contMDiffOn_univ]
  have hlift : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞
      (fun p : ℝ × ℝ => γ p.2 (p.1 : Surgery.Topology.Circle)) (univ ×ˢ univ) := hγ
  have hswap : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞
      (fun p : ℝ × ℝ => γ p.1 (p.2 : Surgery.Topology.Circle)) (univ ×ˢ univ) :=
    hlift.comp (contDiff_snd.prodMk contDiff_fst).contMDiff.contMDiffOn
      (fun _ _ => ⟨mem_univ _, mem_univ _⟩)
  have hsource : ContMDiffOn (𝓘(ℝ).prod 𝓘(ℝ)) I ∞
      (fun p : ℝ × Surgery.Topology.Circle => γ p.1 p.2) (univ ×ˢ univ) := by
    apply AddCircle.contMDiffOn_of_comp_coe
    rw [← chartedSpaceSelf_prod, modelWithCornersSelf_prod] at hswap
    exact hswap
  simpa only [univ_prod_univ] using hsource

theorem smoothOn_curveOfLoopFamily_of_contMDiff
    (γ : ℝ → ContinuousFreeLoop M)
    (hγ : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) I ∞
      (fun p : ℝ × Surgery.Topology.Circle => γ p.1 p.2)) (J : Set ℝ) :
    (curveOfLoopFamily γ).SmoothOn (I := I) J := by
  have hcoe : ContMDiff 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ).prod 𝓘(ℝ)) ∞
      (fun p : ℝ × ℝ => (p.2, (p.1 : Surgery.Topology.Circle))) :=
    contDiff_snd.contMDiff.prodMk (AddCircle.contMDiff_coe.comp contDiff_fst.contMDiff)
  exact (hγ.comp hcoe).contMDiffOn

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open Surgery.Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

theorem exists_smooth_loopFamily_extension
    {a b : ℝ} {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (R : Width.SmoothTubularRetraction e)
    (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b)) :
    ∃ γext : ℝ → ContinuousFreeLoop M,
      (curveOfLoopFamily γext).SmoothOn (I := I) univ ∧
      ∀ t ∈ Icc a b, γext t = γ t := by
  have hlift : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞
      (fun p : ℝ × ℝ => γ p.2 (p.1 : Surgery.Topology.Circle)) (univ ×ˢ Icc a b) := hγ
  have hswap : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞
      (fun p : ℝ × ℝ => γ p.1 (p.2 : Surgery.Topology.Circle)) (Icc a b ×ˢ univ) :=
    hlift.comp (contDiff_snd.prodMk contDiff_fst).contMDiff.contMDiffOn
      (fun _ hp => ⟨hp.2, hp.1⟩)
  have hsource : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
      (fun p : ℝ × Surgery.Topology.Circle => γ p.1 p.2) (Icc a b ×ˢ univ) := by
    apply AddCircle.contMDiffOn_of_comp_coe
    rw [← chartedSpaceSelf_prod, modelWithCornersSelf_prod] at hswap
    exact hswap
  obtain ⟨G, hG, hGeq⟩ := _root_.Manifold.exists_contMDiff_extension_Icc_of_retraction
    e.smooth R.retract R.neighborhood R.isOpen_neighborhood R.range_subset R.smoothOn
    R.leftInverse hsource
  let γext : ℝ → ContinuousFreeLoop M := fun t =>
    ⟨fun z => G (t, z), hG.continuous.comp (continuous_const.prodMk continuous_id)⟩
  refine ⟨γext, ?_, ?_⟩
  · have hcoe : ContMDiff 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
        (fun p : ℝ × ℝ => (p.2, (p.1 : Surgery.Topology.Circle))) :=
      contDiff_snd.contMDiff.prodMk (AddCircle.contMDiff_coe.comp contDiff_fst.contMDiff)
    exact (hG.comp hcoe).contMDiffOn
  · intro t ht
    apply ContinuousMap.ext
    intro z
    exact hGeq ⟨ht, mem_univ z⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open Surgery.Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_smooth_immersed_loopFamily_extension
    {a b : ℝ} (hab : a ≤ b) {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (R : Width.SmoothTubularRetraction e)
    (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b)) :
    ∃ γext : ℝ → ContinuousFreeLoop M, ∃ lo hi : ℝ,
      lo < a ∧ b < hi ∧
      (curveOfLoopFamily γext).SmoothOn (I := I) univ ∧
      (curveOfLoopFamily γext).ImmersedOn (I := I) (Icc lo hi) ∧
      ∀ t ∈ Icc a b, γext t = γ t := by
  obtain ⟨γext, hext, heq⟩ := exists_smooth_loopFamily_extension e R γ hγ
  have hiext : (curveOfLoopFamily γext).ImmersedOn (I := I) (Icc a b) := by
    intro x t ht
    change mfderiv 𝓘(ℝ, ℝ) I
      (fun y : ℝ => γext t (y : Surgery.Topology.Circle)) x 1 ≠ 0
    rw [heq t ht]
    exact hi x t ht
  obtain ⟨lo, hi, hlo, hhi, himm⟩ :=
    CurveMap.exists_immersedOn_Icc_superset hab (curveOfLoopFamily γext) hext hiext
  exact ⟨γext, lo, hi, hlo, hhi, hext, himm, heq⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

section

noncomputable section

open Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open Surgery.Topology (ContinuousFreeLoop)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem deriv_embeddedLoopFamily_eq {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (γ : ℝ → ContinuousFreeLoop M) {J : Set ℝ}
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) J) {t : ℝ} (ht : t ∈ J) (r : ℝ) :
    deriv (fun s : ℝ => e.map (γ t (s : Surgery.Topology.Circle))) r =
      mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) e.map (γ t (r : Surgery.Topology.Circle))
        ((curveOfLoopFamily γ).X (I := I) r t) := by
  exact DifferentialGeometry.Topology.deriv_loop_family_comp e.map e.smooth
    (fun p => γ p.1 p.2) hγ ht r

theorem norm_deriv_embeddedLoopFamily_sub_le_iteratedFDerivWithin_one {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (γ Γ : ℝ → ContinuousFreeLoop M) {a b : ℝ} (hab : a < b)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hΓ : (curveOfLoopFamily Γ).SmoothOn (I := I) (Icc a b))
    {t : ℝ} (ht : t ∈ Icc a b) (r : ℝ) :
    ‖deriv (fun s : ℝ => e.map (Γ t (s : Surgery.Topology.Circle))) r -
      deriv (fun s : ℝ => e.map (γ t (s : Surgery.Topology.Circle))) r‖ ≤
      ‖iteratedFDerivWithin ℝ 1
          (fun q : ℝ × ℝ => e.map (Γ q.2 (q.1 : Surgery.Topology.Circle)))
          (univ ×ˢ Icc a b) (r, t) -
        iteratedFDerivWithin ℝ 1
          (fun q : ℝ × ℝ => e.map (γ q.2 (q.1 : Surgery.Topology.Circle)))
          (univ ×ˢ Icc a b) (r, t)‖ := by
  exact DifferentialGeometry.Topology.norm_deriv_loop_family_sub_le_iteratedFDerivWithin_one
    e.map e.smooth (fun p => γ p.1 p.2) (fun p => Γ p.1 p.2) hab hγ hΓ ht r

theorem exists_loopFamily_immersion_separation_radius {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (γ : ℝ → ContinuousFreeLoop M) {a b : ℝ} (hab : a < b)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ Γ : ℝ → ContinuousFreeLoop M,
        (curveOfLoopFamily Γ).SmoothOn (I := I) (Icc a b) →
        (∀ q ∈ Icc (0 : ℝ) 1 ×ˢ Icc a b,
          ‖iteratedFDerivWithin ℝ 1
              (fun p : ℝ × ℝ => e.map (Γ p.2 (p.1 : Surgery.Topology.Circle))) (univ ×ˢ Icc a b) q -
            iteratedFDerivWithin ℝ 1
              (fun p : ℝ × ℝ => e.map (γ p.2 (p.1 : Surgery.Topology.Circle)))
              (univ ×ˢ Icc a b) q‖ < ε) →
        (curveOfLoopFamily Γ).ImmersedOn (I := I) (Icc a b) ∧
        ∀ t ∈ Icc a b, ∀ z w : Surgery.Topology.Circle,
          z ≠ w → Γ t z = Γ t w → δ ≤ dist z w := by
  obtain ⟨ε, hε, δ, hδ, hstable⟩ :=
    DifferentialGeometry.Topology.exists_loop_family_immersion_separation_radius
      e.map e.smooth e.injective_mfderiv (fun p => γ p.1 p.2) hab hγ hi
  exact ⟨ε, hε, δ, hδ, fun Γ hΓ hclose => hstable (fun p => Γ p.1 p.2) hΓ hclose⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

end
