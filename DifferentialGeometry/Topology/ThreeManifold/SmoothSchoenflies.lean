import DifferentialGeometry.Topology.SphereSeparation.OneSaddle
import DifferentialGeometry.Topology.SphereSeparation.CylinderCapSaddles
import DifferentialGeometry.Topology.SphereSeparation.CylinderCapBall
import DifferentialGeometry.Topology.Morse.Embedding

open Set Metric Manifold
open scoped ContDiff Manifold
open DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Topology.SphereSeparation

namespace DifferentialGeometry.Topology.ThreeManifold

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "S²" => Metric.sphere (0 : ℝ³) 1

private theorem exists_diffeomorph_image_sphere_of_excellent_height
    {e : SphereTwo → EuclideanThree} (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (hnd : ∀ x, IsCriticalPointAt (𝓡 2) (fun y => e y 2) x →
      IsNondegenerateCriticalPointAt (𝓡 2) (fun y => e y 2) x)
    (hinj : InjOn (fun y => e y 2) {x | IsCriticalPointAt (𝓡 2) (fun y => e y 2) x}) :
    ∃ D : EuclideanThree ≃ₘ[ℝ] EuclideanThree, D '' sphere 0 1 = range e := by
  classical
  let S (f : SphereTwo → EuclideanThree) : Set SphereTwo :=
    {p | IsCriticalPointAt (𝓡 2) (fun y => f y 2) p ∧ sigNeg (chartHessianAt
      (fun y => f ((extChartAt (𝓡 2) p).symm y) 2) (extChartAt (𝓡 2) p p)) = 1}
  have hfinite (f : SphereTwo → EuclideanThree) (hf : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
      (hfnd : ∀ x, IsCriticalPointAt (𝓡 2) (fun y => f y 2) x →
        IsNondegenerateCriticalPointAt (𝓡 2) (fun y => f y 2) x) :
      (criticalPoints (𝓡 2) (fun y => f y 2)).Finite := by
    have hh : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun y => f y 2) :=
      (EuclideanSpace.proj 2).contMDiff.comp hf.contMDiff
    exact DifferentialGeometry.Morse.finite_criticalPoints_of_isCompact hh isCompact_univ
      (fun _ _ => BoundarylessManifold.isInteriorPoint) (fun _ _ => mem_univ _) hfnd
  suffices hall : ∀ n : ℕ, ∀ f : SphereTwo → EuclideanThree,
      IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f →
      (∀ x, IsCriticalPointAt (𝓡 2) (fun y => f y 2) x →
        IsNondegenerateCriticalPointAt (𝓡 2) (fun y => f y 2) x) →
      InjOn (fun y => f y 2) {x | IsCriticalPointAt (𝓡 2) (fun y => f y 2) x} →
      (S f).ncard = n → ∃ D : EuclideanThree ≃ₘ[ℝ] EuclideanThree, D '' sphere 0 1 = range f from
    hall (S e).ncard e he hnd hinj rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro f hf hfnd hfinj hfn
    have hSf : (S f).Finite := (hfinite f hf hfnd).subset (fun _ hx => hx.1)
    by_cases hn0 : n = 0
    · have hempty : S f = ∅ := (ncard_eq_zero hSf).mp (hfn.trans hn0)
      apply exists_diffeomorph_image_sphere_of_no_saddles hf hfnd hfinj
      intro x hx hi
      exact hempty.subset ⟨hx, hi⟩
    by_cases hn1 : n = 1
    · exact exists_diffeomorph_image_sphere_of_one_saddle hf hfnd hfinj (hfn.trans hn1)
    have hn2 : 2 ≤ (S f).ncard := by omega
    obtain ⟨p, hp, q, hq, hpq⟩ := (one_lt_ncard hSf).mp (by omega)
    have hvalues : f p 2 ≠ f q 2 := fun hh => hpq (hfinj hp.1 hq.1 hh)
    have hex : ∃ p ∈ S f, ∃ q ∈ S f, f p 2 < f q 2 := by
      rcases lt_or_gt_of_ne hvalues with hh | hh
      · exact ⟨p, hp, q, hq, hh⟩
      · exact ⟨q, hq, p, hp, hh⟩
    obtain ⟨p, hp, q, hq, hpq⟩ := hex
    obtain ⟨c, ⟨hpc, hcq⟩, hc⟩ := exists_regular_level_between_of_finite_criticalPoints
      (hfinite f hf hfnd) hpq
    have hinner : ∀ m : ℕ, ∀ g : SphereTwo → EuclideanThree,
        IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g →
        (∀ x, IsCriticalPointAt (𝓡 2) (fun y => g y 2) x →
          IsNondegenerateCriticalPointAt (𝓡 2) (fun y => g y 2) x) →
        InjOn (fun y => g y 2) {x | IsCriticalPointAt (𝓡 2) (fun y => g y 2) x} →
        (S g).ncard = n → Nat.card (ConnectedComponents {x : SphereTwo // g x 2 = c}) = m →
        ∀ p ∈ S g, ∀ q ∈ S g, g p 2 < c → c < g q 2 →
        (∀ x, g x 2 = c → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun y => g y 2) x ≠ 0) →
        ∃ D : EuclideanThree ≃ₘ[ℝ] EuclideanThree, D '' sphere 0 1 = range g := by
      intro m
      induction m using Nat.strong_induction_on with
      | h m ihm =>
        intro g hg hgnd hginj hgn hgm p hp q hq hpc hcq hc
        have hSg : (S g).Finite := (hfinite g hg hgnd).subset (fun _ hx => hx.1)
        obtain ⟨ε, hε, hregular, R, hR, η, Ψ, b, σ, hσ, hη, hb, hbd, hcover, hinter,
          hboundary, hheight, hsphere, χ, fcap, hfcap, _, _, H, hH⟩ :=
          exists_two_morse_cylinderCap_displacements_of_regular_height_between_saddles
            hg hgnd hginj hp hq hpc hcq hc
        have hfill (i : Fin 2) : ∃ D : EuclideanThree ≃ₘ[ℝ] EuclideanThree,
            D '' sphere 0 1 = range (H i 1 ∘ fcap i) := by
          obtain ⟨_, _, _, _, hHi, _, hlevel, hreg, hnd', hinj', _, _, _, _, _, _, hSimage,
            hSle, hretain, _⟩ := hH i
          have hle : (S (H i 1 ∘ fcap i)).ncard ≤ n := hSle.trans_eq hgn
          rcases lt_or_eq_of_le hle with hlt | heq
          · exact ih _ hlt _ (hHi 1) hnd' hinj' rfl
          · have hsame : S (H i 1 ∘ fcap i) = S g :=
              eq_of_subset_of_ncard_le (fun x hx => (hSimage.subset hx).1)
                (hgn.trans heq.symm).le hSg
            have hret := hretain (heq.trans hgn.symm)
            exact ihm _ (by simpa only [Function.comp_def, hgm] using hlevel) _ (hHi 1) hnd' hinj' heq rfl
              p (hsame.symm ▸ hp) q (hsame.symm ▸ hq) hret.1 hret.2.1 hreg
        choose D hD using hfill
        obtain ⟨G, _, hGsphere⟩ := exists_diffeomorph_ball_of_cylinderCap_images hg hb hbd hcover hinter
          Ψ hR hsphere hboundary χ (fun i => (hfcap i).1) (fun i => (hfcap i).2.1)
          (a := fun _ => ε / 2) (fun _ => half_pos hε) (fun _ => half_lt_self hε) hσ
          (fun i => (hfcap i).2.2.1)
          (by
            intro i x hx
            simpa only [ite_mul, mul_div_assoc, neg_mul, neg_div] using (hfcap i).2.2.2.1 x hx)
          (fun i => (hfcap i).2.2.2.2.1)
          (fun i => (hfcap i).2.2.2.2.2.2.2.2.2.2)
          (fun i => H i 1) D hD
        exact ⟨G, hGsphere⟩
    exact hinner _ f hf hfnd hfinj hfn rfl p hp q hq hpc hcq hc

theorem smooth_schoenflies_three
    (e : S² → ℝ³) (he : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e) :
    ∃ Φ : ℝ³ ≃ₘ[ℝ] ℝ³, Φ '' Metric.sphere (0 : ℝ³) 1 = Set.range e := by
  obtain ⟨A, hnd, hinj⟩ := he.exists_diffeomorph_excellent_height (EuclideanSpace.proj 2) (by
    intro hzero
    have hh := congrArg (fun f : EuclideanThree →L[ℝ] ℝ => f (EuclideanSpace.single 2 1)) hzero
    norm_num at hh)
  obtain ⟨D, hD⟩ := exists_diffeomorph_image_sphere_of_excellent_height (he.diffeomorph_comp A) hnd hinj
  refine ⟨D.trans A.symm, ?_⟩
  change (A.symm ∘ D) '' sphere 0 1 = range e
  rw [image_comp, hD, ← range_comp]
  have heq : (A.symm ∘ A ∘ e) = e := by funext x; exact A.symm_apply_apply (e x)
  exact congrArg range heq

end DifferentialGeometry.Topology.ThreeManifold
