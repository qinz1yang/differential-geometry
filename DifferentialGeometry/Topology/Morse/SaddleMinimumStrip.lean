/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Morse.MinimumSection
import DifferentialGeometry.Topology.Morse.SaddleSection
import DifferentialGeometry.Topology.Morse.ConnectingFlow

/-! Flow strips between actual saddle and minimum Morse sections. -/

open Set Function
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Morse

variable {H M : Type} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ (MorseModel 2) H} [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]

theorem exists_saddle_minimum_flow_strip {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent ∞ (fun x => (v x : TangentBundle I M)))
    {p q : M} (hp : IsNondegenerateCriticalPointAt I f p)
    (hq : IsNondegenerateCriticalPointAt I f q)
    (hpindex : sigNeg (chartHessianAt (fun y => f ((extChartAt I p).symm y))
      (extChartAt I p p)) = 1)
    (hqindex : sigNeg (chartHessianAt (fun y => f ((extChartAt I q).symm y))
      (extChartAt I q q)) = 0) {γ : ℝ → M}
    (hγ : IsDescendingConnection I f v p q γ)
    (hunique : ∀ η, IsDescendingConnection I f v p q η → ∃ d : ℝ, η = γ ∘ (· + d))
    {O Oₚ Oq : Set M} (hO : IsOpen O) (hpO : p ∈ O) (hqO : q ∈ O)
    (hγO : range γ ⊆ O) (hOₚ : IsOpen Oₚ) (hpOₚ : p ∈ Oₚ)
    (hOq : IsOpen Oq) (hqOq : q ∈ Oq) :
    ∃ χₚ χq : PartialDiffeomorph 𝓘(ℝ, MorseModel 2) I (MorseModel 2) M ∞,
      0 ∈ χₚ.source ∧ χₚ 0 = p ∧ 0 ∈ χq.source ∧ χq 0 = q ∧
      (∀ z ∈ χₚ.source, f (χₚ z) = f p + (z 1 ^ 2 - z 0 ^ 2) / 2) ∧
      (∀ z ∈ χq.source, f (χq z) = f q + (z 0 ^ 2 + z 1 ^ 2) / 2) ∧
      ∃ R ε r a b s₀ δ : ℝ, ∃ side : Bool,
        0 < R ∧ 0 < ε ∧ 0 < r ∧ a < b ∧ 0 < δ ∧ s₀ ∈ Ioo (-R) R ∧
        Icc (s₀ - δ) (s₀ + δ) ⊆ Ioo (-R) R ∧
        f (γ a) = f p - ε ∧ f (γ b) = f q + r ^ 2 / 2 ∧
        (∀ t ∈ Icc (-R) R, χₚ (saddleLevelPoint ε side t) ∈ Oₚ ∩ O) ∧
        χq '' {z : MorseModel 2 | z 0 ^ 2 + z 1 ^ 2 = r ^ 2} ⊆ Oq ∩ O ∧
        Topology.IsClosedEmbedding
          (fun z : {z : MorseModel 2 // z 0 ^ 2 + z 1 ^ 2 = r ^ 2} => χq z) ∧
        χq '' {z : MorseModel 2 | z 0 ^ 2 + z 1 ^ 2 = r ^ 2} =
          χq.target ∩ f ⁻¹' {f q + r ^ 2 / 2} ∧
        ∃ (w : (x : M) → TangentSpace I x)
          (hw : ContMDiff I I.tangent ∞ (fun x => (w x : TangentBundle I M)))
          (hwc : HasCompactSupport w), tsupport w ⊆ O ∧
          ∃ τ : ℝ → ℝ, ContDiffOn ℝ ∞ τ (Icc (s₀ - δ) (s₀ + δ)) ∧ τ s₀ = b - a ∧
            (∀ s ∈ Icc (s₀ - δ) (s₀ + δ), 0 < τ s) ∧
            let Φ := Diffeomorph.compactSupportFlow w hw hwc
            let A : ℝ → M := fun s => χₚ (saddleLevelPoint ε side s)
            let F : ℝ × ℝ → M := fun z => Φ (z.2 * τ z.1) (A z.1)
            ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞ F
              (Icc (s₀ - δ) (s₀ + δ) ×ˢ Icc 0 1) ∧
            Topology.IsClosedEmbedding
              (fun z : Icc (s₀ - δ) (s₀ + δ) × Icc (0 : ℝ) 1 => F (z.1, z.2)) ∧
            (∀ s ∈ Icc (s₀ - δ) (s₀ + δ), F (s, 0) = A s ∧
              F (s, 1) ∈ (χq '' {z : MorseModel 2 | z 0 ^ 2 + z 1 ^ 2 = r ^ 2}) ∩ Oq) ∧
            (∀ t ∈ Icc (0 : ℝ) 1, F (s₀, t) = γ (t * (b - a) + a)) ∧
            (∀ z ∈ Icc (s₀ - δ) (s₀ + δ) ×ˢ Icc 0 1, F z ∈ O) ∧
            ∀ s ∈ Icc (s₀ - δ) (s₀ + δ), ∀ t ∈ Icc (0 : ℝ) (τ s),
              mvfderiv I f (Φ t (A s)) (v (Φ t (A s))) < 0 ∧
              HasMFDerivAt 𝓘(ℝ, ℝ) I (fun t => Φ t (A s)) t
                ((1 : ℝ →L[ℝ] ℝ).smulRight (v (Φ t (A s)))) := by
  obtain ⟨χₚ, hχₚ0, hχₚp, hpn, R, ε, a, side, hR, hε, hεR, _, hsmall,
    hAsmooth, _, hAsub, _, _, ⟨s₀, hs₀, hA₀⟩, _, _⟩ :=
    exists_saddle_section_of_unique_descendingConnection hf
      BoundarylessManifold.isInteriorPoint hp hpindex hγ hunique (hOₚ.inter hO) ⟨hpOₚ, hpO⟩
  obtain ⟨χq, hχq0, hχqq, hqn, r, b, hr, hab, hbvalue, _, _, hCsub, hCembed,
    hCimage, hγbC⟩ := exists_minimum_section_of_descendingConnection hf
      BoundarylessManifold.isInteriorPoint hq hqindex hγ a (hOq.inter hO) ⟨hqOq, hqO⟩
  let A : ℝ → M := fun t => χₚ (saddleLevelPoint ε side t)
  have hA : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ A (Ioo (-R) R) :=
    (hAsmooth side).mono Ioo_subset_Icc_self
  have hAinj : InjOn A (Ioo (-R) R) := by
    intro s hs t ht heq
    have hsrc (u : ℝ) (hu : u ∈ Ioo (-R) R) : saddleLevelPoint ε side u ∈ χₚ.source :=
      (hsmall _ (norm_saddleLevelPoint_le hR.le hεR (abs_le.mpr (Ioo_subset_Icc_self hu)) side)).1
    have hh : (side, s) = (side, t) := saddleLevelPoint_injective hε
      (χₚ.injOn (hsrc s hs) (hsrc t ht) heq)
    exact congrArg Prod.snd hh
  have haheight : f (γ a) = f p - ε := by
    rw [← hA₀]
    exact (hAsub side ⟨s₀, Ioo_subset_Icc_self hs₀, rfl⟩).2
  have hlevel (s : ℝ) (hs : s ∈ Ioo (-R) R) : f (A s) = f (γ a) := by
    rw [haheight]
    exact (hAsub side ⟨s, Ioo_subset_Icc_self hs, rfl⟩).2
  have hbN : γ b ∈ χq.target ∩ Oq :=
    ⟨(hCimage ▸ hγbC).1, (hCsub hγbC).1⟩
  obtain ⟨w, hw, hwc, hwO, δ, hδ, hJ, τ, hτ, hτ₀, hτpos, hF, hemb,
    hend, hcentral, hframe, hfield⟩ := exists_descending_arc_transport hf hv hγ.1 hab
      (fun t _ => hγ.2.2.2 t) hO (image_subset_range γ _ |>.trans hγO)
      (χq.open_target.inter hOq) hbN isOpen_Ioo hA hAinj hs₀ hA₀ hlevel
  refine ⟨χₚ, χq, hχₚ0, hχₚp, hχq0, hχqq, hpn, hqn, R, ε, r, a, b, s₀, δ, side,
    hR, hε, hr, hab, hδ, hs₀, hJ, haheight, hbvalue,
    (fun t ht => (hAsub side ⟨t, ht, rfl⟩).1), hCsub, hCembed, hCimage,
    w, hw, hwc, hwO, τ, hτ, hτ₀, hτpos, hF, hemb, ?_, hcentral, hframe, hfield⟩
  intro s hs
  refine ⟨(hend s hs).1, ?_⟩
  rw [hCimage]
  exact ⟨⟨(hend s hs).2.1.1, hbvalue ▸ (hend s hs).2.2⟩, (hend s hs).2.1.2⟩

end DifferentialGeometry.Morse
