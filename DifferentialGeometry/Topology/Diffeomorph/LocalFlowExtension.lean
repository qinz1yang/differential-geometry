import DifferentialGeometry.Topology.Diffeomorph.TimeDependentFlow
import DifferentialGeometry.Analysis.Calculus.Cutoff.Compact

open Set Filter
open scoped ContDiff Manifold Topology

namespace Diffeomorph

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem exists_contDiff_compact_isotopy_eqOn_integralCurve_of_mem_submodule
    {O : Set V} (hO : IsOpen O) {U C : Set (ℝ × V)}
    (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U ∩ (univ ×ˢ O))
    {W : ℝ × V → V} (hW : ContDiffOn ℝ ∞ W U)
    {S : Set V} (hWS : ∀ z ∈ U, z.2 ∈ S → W z = 0)
    (L : Submodule ℝ V) (hWL : ∀ z ∈ U, W z ∈ L)
    {P : Type*} {γ : P → ℝ → V} {c d : P → ℝ} (a : ℝ)
    (hγ : ∀ p, ContinuousOn (γ p) (Icc (c p) (d p)))
    (hγ' : ∀ p, ∀ t ∈ Ico (c p) (d p),
      HasDerivWithinAt (γ p) (W (t, γ p t)) (Ici t) t)
    (hγC : ∀ p, ∀ t ∈ Icc (c p) (d p), (t, γ p t) ∈ C) :
    ∃ Φ : ℝ → (V ≃ₘ[ℝ] V),
      ContDiff ℝ ∞ (fun q : ℝ × V => Φ q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × V => (Φ q.1).symm q.2) ∧
      Φ a = Diffeomorph.refl 𝓘(ℝ, V) V ∞ ∧
      (∀ p, ∀ t ∈ Icc (c p) (d p), Φ t ((Φ (c p)).symm (γ p (c p))) = γ p t) ∧
      (∀ t, EqOn (Φ t) id S ∧ EqOn (Φ t).symm id S) ∧
      (∀ t x, Φ t x - x ∈ L) ∧
      ∃ K : Set V, IsCompact K ∧ K ⊆ O ∧ ∀ t : ℝ,
        EqOn (Φ t) id Kᶜ ∧ EqOn (Φ t).symm id Kᶜ := by
  obtain ⟨χ, hχ, hχc, hχone, hχsupp, _⟩ :=
    DifferentialGeometry.Analysis.exists_bump_compact hC (hU.inter (isOpen_univ.prod hO)) hCU
  let X : ℝ × V → V := fun z => χ z • W z
  have hX : ContDiff ℝ ∞ X := by
    apply contDiffOn_univ.mp
    apply DifferentialGeometry.Analysis.contDiffOn_cutoff_smul hU hχ
      (hχsupp.trans inter_subset_left)
    simpa only [univ_inter] using hW
  have hXc : HasCompactSupport X := hχc.smul_right
  have hXO : tsupport X ⊆ univ ×ˢ O :=
    (tsupport_smul_subset_left _ _).trans (hχsupp.trans inter_subset_right)
  have hXW : EqOn X W C := by
    intro z hz
    change χ z • W z = W z
    rw [hχone.self_of_nhdsSet hz, Pi.one_apply, one_smul]
  have hXS (t : ℝ) (x : V) (hx : x ∈ S) : X (t, x) = 0 := by
    change χ (t, x) • W (t, x) = 0
    by_cases hz : (t, x) ∈ U
    · rw [hWS (t, x) hz hx, smul_zero]
    · have hχz : χ (t, x) = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hz (hχsupp h).1)
      rw [hχz, zero_smul]
  let Φ : ℝ → (V ≃ₘ[ℝ] V) := fun t => timeDependentFlow X hX hXc a t
  refine ⟨Φ, (contDiff_timeDependentFlow X hX hXc).comp
    (contDiff_const.prodMk (contDiff_fst.prodMk contDiff_snd)),
    (contDiff_timeDependentFlow_symm X hX hXc).comp
      (contDiff_const.prodMk (contDiff_fst.prodMk contDiff_snd)),
    timeDependentFlow_refl X hX hXc a, ?_, ?_, ?_,
    Prod.snd '' tsupport X, hXc.image continuous_snd, ?_,
    fun t => timeDependentFlow_eqOn_compl_image_tsupport X hX hXc a t⟩
  · intro p t ht
    have hcurve : timeDependentFlow X hX hXc (c p) t (γ p (c p)) = γ p t :=
      timeDependentFlow_eqOn_Icc X hX hXc (hγ p)
        (fun s hs => by
          rw [hXW (hγC p s ⟨hs.1, hs.2.le⟩)]
          exact hγ' p s hs) ht
    change timeDependentFlow X hX hXc a t
      ((timeDependentFlow X hX hXc a (c p)).symm (γ p (c p))) = γ p t
    rw [timeDependentFlow_symm]
    exact (congrArg (fun f : V ≃ₘ[ℝ] V => f (γ p (c p)))
      (timeDependentFlow_trans X hX hXc (c p) a t)).trans hcurve
  · intro t
    constructor
    · intro x hx
      exact timeDependentFlow_apply_eq_self_of_forall_eq_zero X hX hXc (fun u => hXS u x hx) a t
    · intro x hx
      change (timeDependentFlow X hX hXc a t).symm x = x
      rw [timeDependentFlow_symm]
      exact timeDependentFlow_apply_eq_self_of_forall_eq_zero X hX hXc (fun u => hXS u x hx) t a
  · intro t x
    apply timeDependentFlow_sub_mem_of_mem_submodule X hX hXc L
    intro z
    by_cases hz : z ∈ U
    · exact L.smul_mem (χ z) (hWL z hz)
    · have hχz : χ z = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hz (hχsupp h).1)
      simpa only [X, hχz, zero_smul] using L.zero_mem
  · rintro _ ⟨q, hq, rfl⟩
    exact (hXO hq).2

theorem exists_contDiff_compact_isotopy_eqOn_integralCurve_of_eqOn_zero
    {O : Set V} (hO : IsOpen O) {U C : Set (ℝ × V)}
    (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U ∩ (univ ×ˢ O))
    {W : ℝ × V → V} (hW : ContDiffOn ℝ ∞ W U)
    {S : Set V} (hWS : ∀ z ∈ U, z.2 ∈ S → W z = 0)
    {P : Type*} {γ : P → ℝ → V} {c d : P → ℝ} (a : ℝ)
    (hγ : ∀ p, ContinuousOn (γ p) (Icc (c p) (d p)))
    (hγ' : ∀ p, ∀ t ∈ Ico (c p) (d p),
      HasDerivWithinAt (γ p) (W (t, γ p t)) (Ici t) t)
    (hγC : ∀ p, ∀ t ∈ Icc (c p) (d p), (t, γ p t) ∈ C) :
    ∃ Φ : ℝ → (V ≃ₘ[ℝ] V),
      ContDiff ℝ ∞ (fun q : ℝ × V => Φ q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × V => (Φ q.1).symm q.2) ∧
      Φ a = Diffeomorph.refl 𝓘(ℝ, V) V ∞ ∧
      (∀ p, ∀ t ∈ Icc (c p) (d p), Φ t ((Φ (c p)).symm (γ p (c p))) = γ p t) ∧
      (∀ t, EqOn (Φ t) id S ∧ EqOn (Φ t).symm id S) ∧
      ∃ K : Set V, IsCompact K ∧ K ⊆ O ∧ ∀ t : ℝ,
        EqOn (Φ t) id Kᶜ ∧ EqOn (Φ t).symm id Kᶜ := by
  obtain ⟨Φ, hΦ, hΦi, hΦa, htrack, hfixed, _, hsupport⟩ :=
    exists_contDiff_compact_isotopy_eqOn_integralCurve_of_mem_submodule
      hO hU hC hCU hW hWS ⊤ (fun _ _ => Submodule.mem_top) a hγ hγ' hγC
  exact ⟨Φ, hΦ, hΦi, hΦa, htrack, hfixed, hsupport⟩

theorem exists_contDiff_compact_isotopy_eqOn_integralCurve
    {O : Set V} (hO : IsOpen O) {U C : Set (ℝ × V)}
    (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U ∩ (univ ×ˢ O))
    {W : ℝ × V → V} (hW : ContDiffOn ℝ ∞ W U)
    {P : Type*} {γ : P → ℝ → V} {c d : P → ℝ} (a : ℝ)
    (hγ : ∀ p, ContinuousOn (γ p) (Icc (c p) (d p)))
    (hγ' : ∀ p, ∀ t ∈ Ico (c p) (d p),
      HasDerivWithinAt (γ p) (W (t, γ p t)) (Ici t) t)
    (hγC : ∀ p, ∀ t ∈ Icc (c p) (d p), (t, γ p t) ∈ C) :
    ∃ Φ : ℝ → (V ≃ₘ[ℝ] V),
      ContDiff ℝ ∞ (fun q : ℝ × V => Φ q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × V => (Φ q.1).symm q.2) ∧
      Φ a = Diffeomorph.refl 𝓘(ℝ, V) V ∞ ∧
      (∀ p, ∀ t ∈ Icc (c p) (d p), Φ t ((Φ (c p)).symm (γ p (c p))) = γ p t) ∧
      ∃ K : Set V, IsCompact K ∧ K ⊆ O ∧ ∀ t : ℝ,
        EqOn (Φ t) id Kᶜ ∧ EqOn (Φ t).symm id Kᶜ := by
  obtain ⟨Φ, hΦ, hΦi, hΦa, htrack, _, hsupport⟩ :=
    exists_contDiff_compact_isotopy_eqOn_integralCurve_of_eqOn_zero hO hU hC hCU hW
      (S := ∅) (fun _ _ h => h.elim) a hγ hγ' hγC
  exact ⟨Φ, hΦ, hΦi, hΦa, htrack, hsupport⟩

end Diffeomorph
