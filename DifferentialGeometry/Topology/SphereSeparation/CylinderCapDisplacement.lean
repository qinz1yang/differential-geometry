import DifferentialGeometry.Topology.SphereSeparation.CylinderCapMorse
import DifferentialGeometry.Topology.SphereSeparation.CylinderCapTransport
import DifferentialGeometry.Topology.SphereSeparation.CylinderCapMorseTransport
import DifferentialGeometry.Topology.SphereSeparation.LevelComponents

open Set Metric Manifold
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Topology.SphereSeparation

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

theorem exists_isotopy_displacing_cylinderCap_decreasing_level_components
    {e f : SphereTwo → EuclideanThree}
    (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e) (hf : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    (Ψ : (Schoenflies.Plane × ℝ) ≃ₘ[ℝ] EuclideanThree) {R ε a d σ c : ℝ}
    (hR : 1 < R) (ha : 0 ≤ a) (had : a < d) (hdε : d < ε)
    (hσ : σ = 1 ∨ σ = -1) (hheight : ∀ p, Ψ p 2 = c + p.2)
    (hS : Ψ ⁻¹' range e ∩ (closedBall (0 : Schoenflies.Plane) R ×ˢ Icc (-ε) ε) =
      sphere (0 : Schoenflies.Plane) 1 ×ˢ Icc (-ε) ε)
    {D : Set SphereTwo} (χ : Schoenflies.Plane → SphereTwo)
    (hχD : χ '' closedBall (0 : Schoenflies.Plane) 1 = D)
    (hcap : ∀ x ∈ closedBall (0 : Schoenflies.Plane) 1,
      f (χ x) = Ψ (EuclideanGeometry.cylinderCap (σ * a) x))
    (hfix : EqOn f e Dᶜ)
    (hside : ∀ p ∈ ball (0 : Schoenflies.Plane) R ×ˢ Ioo (-ε) ε,
      Ψ p ∈ e '' Dᶜ → 0 < σ * p.2)
    (hr : ∀ x, e x 2 = c → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun y => e y 2) x ≠ 0)
    (hD : IsClosed D) (hne : (D ∩ {x | e x 2 = c}).Nonempty) :
    ∃ H : ℝ → (EuclideanThree ≃ₘ[ℝ] EuclideanThree),
      ContDiff ℝ ∞ (fun z : ℝ × EuclideanThree => H z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × EuclideanThree => (H z.1).symm z.2) ∧
      H 0 = Diffeomorph.refl (𝓡 3) EuclideanThree ∞ ∧
      (∀ t, H t '' range e = range e) ∧
      (∀ t, IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (H t ∘ f)) ∧
      range (H 1 ∘ f) ∩ {z | z 2 = c} = e '' Dᶜ ∩ {z | z 2 = c} ∧
      Nat.card (ConnectedComponents {x : SphereTwo // H 1 (f x) 2 = c}) <
        Nat.card (ConnectedComponents {x : SphereTwo // e x 2 = c}) ∧
      (∀ x ∈ closedBall (0 : Schoenflies.Plane) 1, 0 < σ * (H 1 (f (χ x)) 2 - c)) ∧
      ∃ U : Set (Schoenflies.Plane × ℝ), IsOpen U ∧
        EuclideanGeometry.cylinderCap (σ * a) '' closedBall (0 : Schoenflies.Plane) 1 ⊆ U ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ U, H t (Ψ p) = Ψ (p.1, p.2 + t * (σ * d))) ∧
      ∃ J : Set EuclideanThree, IsCompact J ∧
        J ⊆ Ψ '' (ball (0 : Schoenflies.Plane) R ×ˢ Ioo (-ε) ε) ∧
        ∀ t : ℝ, EqOn (H t) id Jᶜ ∧ EqOn (H t).symm id Jᶜ := by
  obtain ⟨H, hH, hHi, hH0, hHS, hHf, hlevel, hpositive, U, hU, hcapU, hmove,
    J, hJ, hJU, hsupport⟩ := exists_isotopy_displacing_cylinderCap hf Ψ hR ha had hdε
      hσ hheight hS χ hχD hcap hfix hside
  exact ⟨H, hH, hHi, hH0, hHS, hHf, hlevel,
    natCard_connectedComponents_height_level_lt_of_range_inter_eq he (hHf 1).isEmbedding
      hr hD hne hlevel, hpositive, U, hU, hcapU, hmove, J, hJ, hJU, hsupport⟩

theorem exists_two_morse_cylinderCap_displacements_of_regular_height
    {e : SphereTwo → EuclideanThree} (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (hnd : ∀ x, IsCriticalPointAt (𝓡 2) (fun y => e y 2) x →
      IsNondegenerateCriticalPointAt (𝓡 2) (fun y => e y 2) x)
    (hinj : InjOn (fun y => e y 2) (criticalPoints (𝓡 2) (fun y => e y 2)))
    {c : ℝ} (hne : ∃ x, e x 2 = c)
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
            ∃ U : Set (Schoenflies.Plane × ℝ), IsOpen U ∧
              EuclideanGeometry.cylinderCap (a i) '' closedBall (0 : Schoenflies.Plane) 1 ⊆ U ∧
              (∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ U,
                H i t (Ψ p) = Ψ (p.1, p.2 + t * ((if i = 0 then σ else -σ) * (3 * ε / 4)))) ∧
            ∃ J : Set EuclideanThree, IsCompact J ∧
              J ⊆ Ψ '' (ball (0 : Schoenflies.Plane) R ×ˢ Ioo (-ε) ε) ∧
              ∀ t : ℝ, EqOn (H i t) id Jᶜ ∧ EqOn (H i t).symm id Jᶜ := by
  classical
  obtain ⟨ε, hε, hregular, R, hR, η, Ψ, b, σ, hσ, hη, hb, hbd, hcover, hinter,
    hboundary, hheight, hsphere, χ, f, hf, hcount, hsaddles⟩ :=
    exists_two_morse_cylinderCap_replacements_of_regular_height he hnd hinj hne hr
  let a : Fin 2 → ℝ := fun i => if i = 0 then σ * ε / 2 else -(σ * ε / 2)
  let s : Fin 2 → ℝ := fun i => if i = 0 then σ else -σ
  have hs (i : Fin 2) : s i = 1 ∨ s i = -1 := by
    by_cases hi : i = 0
    · simpa only [s, ite_eq_left hi] using hσ
    · rcases hσ with hσ | hσ <;> simp [s, hi, hσ]
  have hsa (i : Fin 2) : s i * (ε / 2) = a i := by
    dsimp [s, a]
    split_ifs <;> ring
  have hcap (i : Fin 2) (x : Schoenflies.Plane) (hx : x ∈ closedBall (0 : Schoenflies.Plane) 1) :
      f i (χ i x) = Ψ (EuclideanGeometry.cylinderCap (s i * (ε / 2)) x) := by
    rw [hsa]
    exact (hf i).2.2.2.1 x hx
  have hside (i : Fin 2) (p : Schoenflies.Plane × ℝ)
      (hp : p ∈ ball (0 : Schoenflies.Plane) R ×ˢ Ioo (-ε) ε)
      (heD : Ψ p ∈ e '' (range (b i))ᶜ) : 0 < s i * p.2 :=
    ((hf i).2.2.2.2.2.2.2.2.2.2 p hp).mp heD |>.2
  have hDc (i : Fin 2) : IsClosed (range (b i)) :=
    (isCompact_range (hb i).contMDiff.continuous).isClosed
  have hDlevel (i : Fin 2) : (range (b i) ∩ {x | e x 2 = c}).Nonempty := by
    have hy : η 0 ∈ range η := mem_range_self 0
    obtain ⟨x, hx⟩ := (hbd i).symm.subset hy
    refine ⟨η 0, ⟨cellBoundaryInclusion 2 x, hx⟩, ?_⟩
    obtain ⟨p, hp, heq⟩ := hboundary.subset (mem_image_of_mem e hy)
    have hpzero : p.2 = 0 := hp.2
    change e (η 0) 2 = c
    rw [← heq, hheight, hpzero, add_zero]
  have htransport (i : Fin 2) :=
    exists_isotopy_displacing_cylinderCap_decreasing_level_components he (hf i).2.2.1
      Ψ hR (le_of_lt (half_pos hε)) (show ε / 2 < 3 * ε / 4 by linarith)
      (show 3 * ε / 4 < ε by linarith) (hs i) hheight hsphere (χ i)
      (hf i).2.1 (hcap i) (hf i).2.2.2.2.1 (hside i) hr (hDc i) (hDlevel i)
  choose H hH using htransport
  refine ⟨ε, hε, hregular, R, hR, η, Ψ, b, σ, hσ, hη, hb, hbd, hcover, hinter,
    hboundary, hheight, hsphere, χ, f, hf, hcount, hsaddles, H, ?_⟩
  intro i
  obtain ⟨hHsmooth, hHinv, hH0, hHS, hHf, hlevel, hcomponentCount, hpositive,
    U, hU, hcapU, hmove, J, hJ, hJU, hsupport⟩ := hH i
  have hJheight (z : EuclideanThree) (hz : z ∈ J) : z 2 ∈ Icc (c - ε) (c + ε) := by
    obtain ⟨p, hp, rfl⟩ := hJU hz
    rw [hheight]
    constructor <;> linarith [hp.2.1, hp.2.2]
  have hcapU' : EuclideanGeometry.cylinderCap (a i) ''
      closedBall (0 : Schoenflies.Plane) 1 ⊆ U := by
    simpa only [hsa] using hcapU
  have hmove' (p : Schoenflies.Plane × ℝ) (hp : p ∈ U) :
      H i 1 (Ψ p) = Ψ (p.1, p.2 + s i * (3 * ε / 4)) := by
    simpa only [one_mul] using hmove 1 (by constructor <;> norm_num) p hp
  obtain ⟨hcritg, hessg, hfixed, hcenter⟩ := criticalPoints_cylinderCap_displacement
    he (hf i).2.2.1.contMDiff.continuous (H i 1) Ψ hheight (hDc i) (χ i)
    (hf i).2.1 (hf i).2.2.2.1 (hf i).2.2.2.2.1 (hHS 1) hU hcapU' hmove'
    hJ.isClosed hJheight (hsupport 1).1 hregular
  have hcenter' : H i 1 (f i (χ i 0)) 2 = c + s i * ε / 4 := by
    calc
      _ = c - a i + s i * (3 * ε / 4) := hcenter
      _ = _ := by rw [← hsa]; ring
  have hcenterLevel : c + s i * ε / 4 ∈ Icc (c - ε) (c + ε) := by
    rcases hs i with hi | hi <;> rw [hi] <;> constructor <;> nlinarith
  have hfixed' (x : SphereTwo) (hx : IsCriticalPointAt (𝓡 2) (fun y => e y 2) x)
      (hxD : x ∉ range (b i)) : H i 1 (f i x) = e x :=
    (hfixed x hx hxD).trans ((hf i).2.2.2.2.1 hxD)
  have hregularg (x : SphereTwo) (hx : H i 1 (f i x) 2 = c) :
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun y => H i 1 (f i y) 2) x ≠ 0 := by
    intro hxc
    have hxold := hcritg.subset hxc
    rw [(hf i).2.2.2.2.2.2.2.2.1] at hxold
    rcases hxold with hxold | hxold
    · rw [hfixed' x hxold.1 hxold.2] at hx
      exact hr x hx hxold.1
    · rw [mem_singleton_iff.mp hxold, hcenter'] at hx
      rcases hs i with hi | hi <;> rw [hi] at hx <;> nlinarith
  have hndg (x : SphereTwo) (hx : IsCriticalPointAt (𝓡 2) (fun y => H i 1 (f i y) 2) x) :
      IsNondegenerateCriticalPointAt (𝓡 2) (fun y => H i 1 (f i y) 2) x := by
    have hxold : IsCriticalPointAt (𝓡 2) (fun y => f i y 2) x := hcritg.subset hx
    refine ⟨hx, ?_⟩
    rw [hessg x hxold]
    exact ((hf i).2.2.2.2.2.2.1 x hxold).2
  have hretained (x : SphereTwo) (hx : IsCriticalPointAt (𝓡 2) (fun y => e y 2) x)
      (hxD : x ∉ range (b i)) : H i 1 (f i x) 2 ≠ c + s i * ε / 4 := by
    intro heq
    rw [hfixed x hx hxD, (hf i).2.2.2.2.1 hxD] at heq
    apply hregular x ?_ hx
    rwa [heq]
  have hinjg : InjOn (fun y => H i 1 (f i y) 2)
      (criticalPoints (𝓡 2) (fun y => H i 1 (f i y) 2)) := by
    intro x hx y hy hxy
    change H i 1 (f i x) 2 = H i 1 (f i y) 2 at hxy
    have hxold := hcritg.subset hx
    have hyold := hcritg.subset hy
    rw [(hf i).2.2.2.2.2.2.2.2.1] at hxold hyold
    rcases hxold with hxold | hxold <;> rcases hyold with hyold | hyold
    · apply hinj hxold.1 hyold.1
      rw [hfixed x hxold.1 hxold.2, hfixed y hyold.1 hyold.2,
        (hf i).2.2.2.2.1 hxold.2, (hf i).2.2.2.2.1 hyold.2] at hxy
      exact hxy
    · rw [mem_singleton_iff.mp hyold, hcenter'] at hxy
      exact False.elim (hretained x hxold.1 hxold.2 hxy)
    · rw [mem_singleton_iff.mp hxold, hcenter'] at hxy
      exact False.elim (hretained y hyold.1 hyold.2 hxy.symm)
    · exact (mem_singleton_iff.mp hxold).trans (mem_singleton_iff.mp hyold).symm
  refine ⟨hHsmooth, hHinv, hH0, hHS, hHf, hlevel, hcomponentCount,
    hregularg, hndg, hinjg, hcritg, hessg, ?_, hfixed', hcenter', hpositive,
    U, hU, hcapU', hmove,
    J, hJ, hJU, hsupport⟩
  intro k
  ext x
  constructor
  · rintro ⟨hx, hindex⟩
    have hxold : IsCriticalPointAt (𝓡 2) (fun y => f i y 2) x := hcritg.subset hx
    exact ⟨hxold, by rwa [hessg x hxold] at hindex⟩
  · rintro ⟨hx, hindex⟩
    refine ⟨hcritg.symm.subset hx, ?_⟩
    rw [hessg x hx]
    exact hindex

end DifferentialGeometry.Topology.SphereSeparation
