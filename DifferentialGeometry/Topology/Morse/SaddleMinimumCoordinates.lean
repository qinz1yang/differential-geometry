/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Morse.MinimumSection
import DifferentialGeometry.Topology.Morse.SaddleImmersion
import DifferentialGeometry.Topology.Morse.ConnectingFlow
import DifferentialGeometry.Topology.Manifold.FlowSection
import DifferentialGeometry.Topology.Manifold.CompactLocalDiffeomorph

open Set Function
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Morse

variable {H M : Type} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ (MorseModel 2) H} [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]

theorem exists_saddle_minimum_flow_coordinates {f : M → ℝ}
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
            ∃ d : PartialDiffeomorph (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I (ℝ × ℝ) M ∞,
              (d : ℝ × ℝ → M) = F ∧
              Icc (s₀ - δ) (s₀ + δ) ×ˢ Icc (0 : ℝ) 1 ⊆ d.source ∧ d.target ⊆ O ∧
              (∀ s ∈ Icc (s₀ - δ) (s₀ + δ),
                (s, 0) ∈ (d.trans χₚ.symm).source ∧ (s, 1) ∈ (d.trans χq.symm).source) ∧
              Topology.IsClosedEmbedding
                (fun z : Icc (s₀ - δ) (s₀ + δ) × Icc (0 : ℝ) 1 => d (z.1, z.2)) ∧
              (∀ s ∈ Icc (s₀ - δ) (s₀ + δ), d (s, 0) = A s ∧
                d (s, 1) ∈ (χq '' {z : MorseModel 2 | z 0 ^ 2 + z 1 ^ 2 = r ^ 2}) ∩ Oq) ∧
              (∀ s ∈ Icc (s₀ - δ) (s₀ + δ),
                f (d (s, 0)) = f (γ a) ∧ f (d (s, 1)) = f (γ b)) ∧
              (∀ last : Bool,
                let χ := if last then χq else χₚ
                let x := γ (if last then b else a)
                ∀ t ∈ Icc (0 : ℝ) 1,
                  t • χ.symm x ∈ χ.source ∧ χ (t • χ.symm x) ∈ O) ∧
              (∀ t ∈ Icc (0 : ℝ) 1, d (s₀, t) = γ (t * (b - a) + a)) ∧
              ∀ s ∈ Icc (s₀ - δ) (s₀ + δ), ∀ t ∈ Icc (0 : ℝ) (τ s),
                mvfderiv I f (Φ t (A s)) (v (Φ t (A s))) < 0 ∧
                HasMFDerivAt 𝓘(ℝ, ℝ) I (fun t => Φ t (A s)) t
                  ((1 : ℝ →L[ℝ] ℝ).smulRight (v (Φ t (A s)))) := by
  obtain ⟨χₚ, hχₚ0, hχₚp, hpn, R, ε, a, side, hR, hε, hεR, _, hsmall,
    hAsmooth, _, hAsub, _, _, ⟨s₀, hs₀, hA₀⟩, _, _⟩ :=
    exists_saddle_section_of_unique_descendingConnection hf
      BoundarylessManifold.isInteriorPoint hp hpindex hγ hunique (hOₚ.inter hO) ⟨hpOₚ, hpO⟩
  obtain ⟨χq, hχq0, hχqq, hqn, r, b, hr, hab, hbvalue, _, hcontain, hCsub, hCembed,
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
  obtain ⟨w, hw, hwc, hwO, δ, hδ, hJ, τ, hτ, hτ₀, hτpos, _, hemb,
    hend, hcentral, hframe, hfield⟩ := exists_descending_arc_transport hf hv hγ.1 hab
      (fun t _ => hγ.2.2.2 t) hO (image_subset_range γ _ |>.trans hγO)
      (χq.open_target.inter hOq) hbN isOpen_Ioo hA hAinj hs₀ hA₀ hlevel
  let J := Icc (s₀ - δ / 2) (s₀ + δ / 2)
  let S := Ioo (s₀ - δ) (s₀ + δ)
  have hJS : J ⊆ S := by
    intro s hs
    change s₀ - δ < s ∧ s < s₀ + δ
    dsimp [J] at hs
    constructor <;> linarith [hs.1, hs.2]
  have hSS : S ⊆ Icc (s₀ - δ) (s₀ + δ) := Ioo_subset_Icc_self
  have hJA : J ⊆ Ioo (-R) R := fun _ hs => hJ (hSS (hJS hs))
  let Φ := Diffeomorph.compactSupportFlow w hw hwc
  let F : ℝ × ℝ → M := fun z => Φ (z.2 * τ z.1) (A z.1)
  have hz (x : M) : Φ 0 x = x :=
    DFunLike.congr_fun (Diffeomorph.compactSupportFlow_zero w hw hwc) x
  have hsame (s : ℝ) (hs : s ∈ S) : w (A s) = v (A s) := by
    have h₁ := Diffeomorph.isMIntegralCurve_compactSupportFlow w hw hwc (A s) 0
    have h₂ := (hfield s (hSS hs) 0 ⟨le_rfl, (hτpos s (hSS hs)).le⟩).2
    have he : (1 : ℝ →L[ℝ] ℝ).smulRight (w (Φ 0 (A s))) =
        (1 : ℝ →L[ℝ] ℝ).smulRight (v (Φ 0 (A s))) := h₁.mfderiv.symm.trans h₂.mfderiv
    have hh := congrArg (fun L : ℝ →L[ℝ] MorseModel 2 => L 1) he
    change (1 : ℝ) • w (Φ 0 (A s)) = (1 : ℝ) • v (Φ 0 (A s)) at hh
    rw [one_smul, one_smul] at hh
    exact (congrArg (fun x => (w x : MorseModel 2)) (hz (A s))).symm.trans
      (hh.trans (congrArg (fun x => (v x : MorseModel 2)) (hz (A s))))
  have hloc (z : ℝ × ℝ) (hz' : z ∈ J ×ˢ Icc (0 : ℝ) 1) :
      IsLocalDiffeomorphAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞ F z := by
    have hs := hJS hz'.1
    have hsrc : saddleLevelPoint ε side z.1 ∈ χₚ.source :=
      (hsmall _ (norm_saddleLevelPoint_le hR.le hεR
        (abs_le.mpr (Ioo_subset_Icc_self (hJA hz'.1))) side)).1
    have hAat := hA.contMDiffAt (isOpen_Ioo.mem_nhds (hJ (hSS hs)))
    have htrans : w (A z.1) ∉ range (mfderiv 𝓘(ℝ, ℝ) I A z.1) := by
      apply DifferentialGeometry.Topology.Manifold.not_mem_range_mfderiv_of_level
        (hf.mdifferentiableAt (by simp)) (hAat.mdifferentiableAt (by simp))
        (Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds (hJ (hSS hs))) hlevel)
      have hn := (hfield z.1 (hSS hs) 0 ⟨le_rfl, (hτpos z.1 (hSS hs)).le⟩).1
      change mvfderiv I f (Φ 0 (A z.1)) (v (Φ 0 (A z.1))) < 0 at hn
      rw [hz, ← hsame z.1 hs] at hn
      exact ne_of_lt hn
    exact DifferentialGeometry.Topology.Manifold.isLocalDiffeomorphAt_rescaled_flow_of_transverse
      (by simp [MorseModel]) w hw hwc isOpen_Ioo
      (hA.mono (fun s hs => hJ (hSS hs))) hs
      (saddle_section_mfderiv_injective χₚ hε side hsrc) htrans
      (hτ.mono hSS) (ne_of_gt (hτpos z.1 (hSS hs))) z.2
  have hsub : J ×ˢ Icc (0 : ℝ) 1 ⊆ Icc (s₀ - δ) (s₀ + δ) ×ˢ Icc 0 1 :=
    prod_mono (fun _ hs => hSS (hJS hs)) subset_rfl
  have hinj : InjOn F (J ×ˢ Icc (0 : ℝ) 1) := by
    intro x hx y hy he
    have he' := hemb.injective (a₁ := (⟨x.1, (hsub hx).1⟩, ⟨x.2, hx.2⟩))
      (a₂ := (⟨y.1, (hsub hy).1⟩, ⟨y.2, hy.2⟩)) he
    exact Prod.ext (congrArg (fun z => z.1.val) he') (congrArg (fun z => z.2.val) he')
  obtain ⟨d, hds, hdt, hd⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_partialDiffeomorph_of_injOn_compact
      (isCompact_Icc.prod isCompact_Icc) hinj hloc hO (by
        rintro x ⟨z, hz', rfl⟩
        exact hframe z (hsub hz'))
  have hemb' : Topology.IsClosedEmbedding
      (fun z : J × Icc (0 : ℝ) 1 => d (z.1, z.2)) := by
    have hc : Continuous (fun z : J × Icc (0 : ℝ) 1 => d (z.1, z.2)) :=
      d.contMDiffOn.continuousOn.comp_continuous
        ((continuous_subtype_val.comp continuous_fst).prodMk
          (continuous_subtype_val.comp continuous_snd)) (fun z => hds ⟨z.1.2, z.2.2⟩)
    apply hc.isClosedEmbedding
    intro x y he
    have hh := d.injOn (hds ⟨x.1.2, x.2.2⟩) (hds ⟨y.1.2, y.2.2⟩) he
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hh)) (Subtype.ext (congrArg Prod.snd hh))
  have hheight (s : ℝ) (hs : s ∈ J) :
      f (d (s, 0)) = f (γ a) ∧ f (d (s, 1)) = f (γ b) := by
    rw [hd]
    constructor
    · change f (Φ (0 * τ s) (A s)) = f (γ a)
      rw [zero_mul, hz]
      exact hlevel s (hJA hs)
    · exact (hend s (hSS (hJS hs))).2.2
  have hpnorm : ‖χₚ.symm (γ a)‖ ≤ 2 * R := by
    have hb := norm_saddleLevelPoint_le hR.le hεR (abs_le.mpr (Ioo_subset_Icc_self hs₀)) side
    have hs : saddleLevelPoint ε side s₀ ∈ χₚ.source := (hsmall _ hb).1
    have hi : χₚ.symm (γ a) = saddleLevelPoint ε side s₀ :=
      (congrArg χₚ.symm hA₀.symm).trans (χₚ.left_inv hs)
    rw [hi]
    exact hb
  have hqnorm : ‖χq.symm (γ b)‖ ≤ r := by
    obtain ⟨z, hz, hzb⟩ := hγbC
    change z 0 ^ 2 + z 1 ^ 2 = r ^ 2 at hz
    have hn : ‖z‖ ≤ r := by
      apply (pi_norm_le_iff_of_nonneg hr.le).mpr
      intro i
      fin_cases i
      · change |z 0| ≤ r
        apply (sq_le_sq₀ (abs_nonneg _) hr.le).mp
        rw [sq_abs]
        nlinarith [sq_nonneg (z 1)]
      · change |z 1| ≤ r
        apply (sq_le_sq₀ (abs_nonneg _) hr.le).mp
        rw [sq_abs]
        nlinarith [sq_nonneg (z 0)]
    have hi : χq.symm (γ b) = z :=
      (congrArg χq.symm hzb.symm).trans (χq.left_inv (hcontain z hn).1)
    rw [hi]
    exact hn
  have hscale (z : MorseModel 2) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖t • z‖ ≤ ‖z‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact mul_le_of_le_one_left (norm_nonneg z) ht.2
  have hrays (last : Bool) :
      let χ := if last then χq else χₚ
      let x := γ (if last then b else a)
      ∀ t ∈ Icc (0 : ℝ) 1, t • χ.symm x ∈ χ.source ∧ χ (t • χ.symm x) ∈ O := by
    cases last
    · change ∀ t ∈ Icc (0 : ℝ) 1,
        t • χₚ.symm (γ a) ∈ χₚ.source ∧ χₚ (t • χₚ.symm (γ a)) ∈ O
      intro t ht
      have hh := hsmall _ ((hscale _ t ht).trans hpnorm)
      exact ⟨hh.1, hh.2.2⟩
    · change ∀ t ∈ Icc (0 : ℝ) 1,
        t • χq.symm (γ b) ∈ χq.source ∧ χq (t • χq.symm (γ b)) ∈ O
      intro t ht
      have hh := hcontain _ ((hscale _ t ht).trans hqnorm)
      exact ⟨hh.1, hh.2.2⟩
  refine ⟨χₚ, χq, hχₚ0, hχₚp, hχq0, hχqq, hpn, hqn,
    R, ε, r, a, b, s₀, δ / 2, side,
    hR, hε, hr, hab, by positivity, hs₀, hJA, haheight, hbvalue,
    (fun t ht => (hAsub side ⟨t, ht, rfl⟩).1), hCsub, hCembed, hCimage,
    w, hw, hwc, hwO, τ, hτ.mono (fun _ hs => hSS (hJS hs)), hτ₀,
    (fun s hs => hτpos s (hSS (hJS hs))), d, hd, hds, hdt,
    ?_, hemb', ?_, hheight, hrays, ?_, ?_⟩
  · intro s hs
    have hzero : d (s, 0) = A s := by rw [hd]; exact (hend s (hSS (hJS hs))).1
    have hone : d (s, 1) ∈ χq.target := by
      rw [hd]
      exact (hend s (hSS (hJS hs))).2.1.1
    constructor
    · refine ⟨hds ⟨hs, le_rfl, zero_le_one⟩, ?_⟩
      change d (s, 0) ∈ χₚ.target
      rw [hzero]
      exact χₚ.map_source (hsmall _ (norm_saddleLevelPoint_le hR.le hεR
        (abs_le.mpr (Ioo_subset_Icc_self (hJA hs))) side)).1
    · exact ⟨hds ⟨hs, zero_le_one, le_rfl⟩, hone⟩
  · intro s hs
    rw [hd]
    refine ⟨(hend s (hSS (hJS hs))).1, ?_⟩
    rw [hCimage]
    exact ⟨⟨(hend s (hSS (hJS hs))).2.1.1,
      hbvalue ▸ (hend s (hSS (hJS hs))).2.2⟩, (hend s (hSS (hJS hs))).2.1.2⟩
  · intro t ht
    rw [hd]
    exact hcentral t ht
  · exact fun s hs t ht => hfield s (hSS (hJS hs)) t ht

end DifferentialGeometry.Morse
