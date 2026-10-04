import DifferentialGeometry.Topology.LoopSpace.SmoothFamily.GlobalExtension
import DifferentialGeometry.Topology.Diffeomorph.LocalFlowExtension

section


noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {a b : ℝ}

section ModelSpaceHeadline


theorem exists_compact_isotopy_of_smooth_loop_family {α β : ℝ}
    (hα : α < a) (hab : a ≤ b) (hβ : b < β) {γ : ℝ → DifferentialGeometry.Topology.freeLoop E}
    (hγ : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => γ q.1 (q.2 : DifferentialGeometry.Topology.loopCircle))
      (Icc α β ×ˢ univ))
    (hemb : ∀ t ∈ Icc α β, Function.Injective (fun z : DifferentialGeometry.Topology.loopCircle => γ t z))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := 𝓘(ℝ, E)) (Icc α β))
    (t₀ : ℝ) (ht₀ : t₀ ∈ Icc a b) :
    ∃ Φ : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
        (fun p : E × ℝ => Φ p.2 p.1) ∧
      ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
        (fun p : E × ℝ => (Φ p.2).symm p.1) ∧
      Φ t₀ = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
      (∃ K : Set E, IsCompact K ∧ ∀ t : ℝ,
        EqOn (Φ t) id Kᶜ ∧ EqOn (Φ t).symm id Kᶜ) ∧
      (∀ t ∈ Icc a b, ∀ z : DifferentialGeometry.Topology.loopCircle, Φ t (γ t₀ z) = γ t z) ∧
      (∀ t ∈ Icc a b, ∀ z : DifferentialGeometry.Topology.loopCircle, (Φ t).symm (γ t z) = γ t₀ z) ∧
      (∀ t ∈ Icc a b,
        (Φ t) '' Set.range (fun z : DifferentialGeometry.Topology.loopCircle => γ t₀ z) =
          Set.range (fun z : DifferentialGeometry.Topology.loopCircle => γ t z)) ∧
      ∀ t ∈ Icc a b,
        (Φ t).symm '' Set.range (fun z : DifferentialGeometry.Topology.loopCircle => γ t z) =
          Set.range (fun z : DifferentialGeometry.Topology.loopCircle => γ t₀ z) := by
  obtain ⟨γ', hagree, hγ', hemb', hi'⟩ :=
    loopFamilyGlobalSmoothExtension_of_smoothOn_superwindow hα hab hβ hγ hemb hi
  obtain ⟨X, hX, hXeq⟩ := exists_contDiff_loopFamilyVelocity a b γ' hemb' hγ' hi'
  let C : Set (ℝ × E) := graphLift γ' '' (Icc a b ×ˢ Icc (0 : ℝ) 1)
  have hA : IsCompact (Icc a b ×ˢ Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  have hC : IsCompact C := hA.image (continuous_graphLift hγ')
  have hγcont (z : DifferentialGeometry.Topology.loopCircle) :
      ContinuousOn (fun t : ℝ => γ' t z) (Icc a b) :=
    (contDiff_loopSlice hγ' z).continuous.continuousOn
  have hγderiv (z : DifferentialGeometry.Topology.loopCircle) (t : ℝ) (ht : t ∈ Ico a b) :
      HasDerivWithinAt (fun r : ℝ => γ' r z) (X t (γ' t z)) (Ici t) t := by
    have hd : DifferentiableAt ℝ (fun r : ℝ => γ' r z) t :=
      ((contDiff_loopSlice hγ' z).differentiable (by norm_num)).differentiableAt
    rw [hXeq t (Ico_subset_Icc_self ht) z]
    exact hd.hasDerivAt.hasDerivWithinAt
  have hγC (z : DifferentialGeometry.Topology.loopCircle) (t : ℝ) (ht : t ∈ Icc a b) :
      (t, γ' t z) ∈ C := by
    obtain ⟨x, hx, hxz⟩ := exists_lift_mem_Icc z
    refine ⟨(t, x), ⟨ht, hx⟩, ?_⟩
    change (t, γ' t (x : DifferentialGeometry.Topology.loopCircle)) = (t, γ' t z)
    rw [hxz]
  have hCU : C ⊆ (univ : Set (ℝ × E)) ∩ (univ ×ˢ (univ : Set E)) :=
    fun _ _ => ⟨trivial, trivial, trivial⟩
  obtain ⟨Φ, hΦ, hΦi, hΦt₀, htrack, K, hK, -, hfixed⟩ :=
    Diffeomorph.exists_contDiff_compact_isotopy_eqOn_integralCurve
      (V := E) (O := univ) isOpen_univ (U := univ) (C := C) isOpen_univ hC hCU
      (W := fun q : ℝ × E => X q.1 q.2) hX.contDiffOn
      (P := DifferentialGeometry.Topology.loopCircle) (γ := fun z t => γ' t z)
      (c := fun _ => a) (d := fun _ => b) t₀ hγcont hγderiv hγC
  have hswap : ContDiff ℝ ∞ (fun p : E × ℝ => (p.2, p.1)) :=
    contDiff_snd.prodMk contDiff_fst
  have hΦsm : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun p : E × ℝ => Φ p.2 p.1) := by
    rw [← modelWithCornersSelf_prod (𝕜 := ℝ) (E := E) (F := ℝ),
      chartedSpaceSelf_prod (H := E) (H' := ℝ)]
    exact (hΦ.comp hswap).contMDiff
  have hΦism : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun p : E × ℝ => (Φ p.2).symm p.1) := by
    rw [← modelWithCornersSelf_prod (𝕜 := ℝ) (E := E) (F := ℝ),
      chartedSpaceSelf_prod (H := E) (H' := ℝ)]
    exact (hΦi.comp hswap).contMDiff
  have hbase (z : DifferentialGeometry.Topology.loopCircle) : (Φ a).symm (γ' a z) = γ' t₀ z := by
    simpa only [hΦt₀, Diffeomorph.coe_refl, id_eq] using htrack z t₀ ht₀
  have htrackOriginal : ∀ t ∈ Icc a b, ∀ z : DifferentialGeometry.Topology.loopCircle,
      Φ t (γ t₀ z) = γ t z := by
    intro t ht z
    have h := htrack z t ht
    rw [hbase z, hagree t₀ ht₀, hagree t ht] at h
    exact h
  have htrackInverse : ∀ t ∈ Icc a b, ∀ z : DifferentialGeometry.Topology.loopCircle,
      (Φ t).symm (γ t z) = γ t₀ z := by
    intro t ht z
    rw [← htrackOriginal t ht z, Diffeomorph.symm_apply_apply]
  refine ⟨Φ, hΦsm, hΦism, hΦt₀, ⟨K, hK, hfixed⟩, htrackOriginal, htrackInverse, ?_, ?_⟩
  · intro t ht
    ext p
    constructor
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, (htrackOriginal t ht z).symm⟩
    · rintro ⟨z, rfl⟩
      exact ⟨γ t₀ z, ⟨z, rfl⟩, htrackOriginal t ht z⟩
  · intro t ht
    ext p
    constructor
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, (htrackInverse t ht z).symm⟩
    · rintro ⟨z, rfl⟩
      exact ⟨γ t z, ⟨z, rfl⟩, htrackInverse t ht z⟩

theorem rfs_csf_boundary_isotopy_modelSpace_of_smoothOn_superwindow {α β : ℝ}
    (hα : α < a) (hab : a ≤ b) (hβ : b < β) {γ : ℝ → DifferentialGeometry.Topology.freeLoop E}
    (hγ : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => γ q.1 (q.2 : DifferentialGeometry.Topology.loopCircle))
      (Icc α β ×ˢ univ))
    (hemb : ∀ t ∈ Icc α β, Function.Injective (fun z : DifferentialGeometry.Topology.loopCircle => γ t z))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := 𝓘(ℝ, E)) (Icc α β))
    (t₀ : ℝ) (ht₀ : t₀ ∈ Icc a b) :
    ∃ ε > 0, ∃ Φ : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
        (fun p : E × ℝ => Φ p.2 p.1)
        (univ ×ˢ (Icc a b ∩ Ioo (t₀ - ε) (t₀ + ε))) ∧
      (∀ p, Φ t₀ p = p) ∧
      ∀ t ∈ Icc a b ∩ Ioo (t₀ - ε) (t₀ + ε), ∀ z, Φ t (γ t₀ z) = γ t z := by
  obtain ⟨Φ, hΦ, -, hΦt₀, -, htrack, -, -, -⟩ :=
    exists_compact_isotopy_of_smooth_loop_family hα hab hβ hγ hemb hi t₀ ht₀
  refine ⟨(1 / 2 : ℝ), by norm_num, Φ, hΦ.contMDiffOn, ?_, ?_⟩
  · intro p
    rw [hΦt₀]
    rfl
  · intro t ht z
    exact htrack t ht.1 z

end ModelSpaceHeadline

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

end

