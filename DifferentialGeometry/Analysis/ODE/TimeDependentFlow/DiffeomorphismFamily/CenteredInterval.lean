import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.BoundaryExtension.ClosedInterval
import DifferentialGeometry.Topology.Manifold.Diffeomorph.InverseFamily

noncomputable section
open Set Function Bundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M]

theorem exists_diffeomorph_flow_on_centered_interval
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ Φ : ℝ → (M ≃ₘ⟮I, I⟯ M),
      (∀ x, Φ t₀ x = x) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2)
        (Ioo (t₀ - T) (t₀ + T) ×ˢ univ) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => (Φ q.1).symm q.2)
        (Ioo (t₀ - T) (t₀ + T) ×ˢ univ) ∧
      (∀ t ∈ Ioo (t₀ - T) (t₀ + T), ∀ x,
        HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ s x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x)))) := by
  classical
  let a := t₀ - T - 1
  let Y : ℝ → ∀ x : M, TangentSpace I x := fun s x => X (s + a) x
  have hY : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (Y q.1 q.2) : TangentBundle I M)) :=
    hX.comp ((contMDiff_fst.add contMDiff_const).prodMk contMDiff_snd)
  obtain ⟨F, G, lo, hi, hlo, hhi, hF0, hFsm, hFode, hGsm, hGF, hFG⟩ :=
    global_flow_with_reverse_on_closed_interval_of_closed_manifold Y hY (2 * T + 2) (by linarith)
  have hslice (s : ℝ) (hs : s ∈ Ioo 0 hi) : ContMDiff I I ∞ (F s) := by
    intro x
    have hat := hFsm.contMDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds
      (show (s, x) ∈ Ioo lo hi ×ˢ (univ : Set M) from
        ⟨⟨lt_trans hlo hs.1, hs.2⟩, mem_univ _⟩))
    exact hat.comp x (contMDiffAt_const.prodMk contMDiffAt_id)
  let D : ℝ → (M ≃ₘ⟮I, I⟯ M) := fun s => if hs : s ∈ Ioo 0 hi then
    { toEquiv := {
        toFun := F s
        invFun := G s
        left_inv := hGF s ⟨hs.1.le, hs.2⟩
        right_inv := hFG s ⟨hs.1.le, hs.2⟩ }
      contMDiff_toFun := hslice s hs
      contMDiff_invFun := hGsm s hs.1 hs.2 }
    else Diffeomorph.refl I M ∞
  have hD (s : ℝ) (hs : s ∈ Ioo 0 hi) (x : M) : D s x = F s x := by
    simp only [D, dif_pos hs]
    rfl
  have hDsm : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => D q.1 q.2) (Ioo 0 hi ×ˢ univ) := by
    apply (hFsm.mono (prod_mono (Ioo_subset_Ioo hlo.le le_rfl) (subset_refl _))).congr
    intro q hq
    exact hD q.1 hq.1 q.2
  have hcenter : t₀ - a ∈ Ioo 0 hi := by
    dsimp [a]
    constructor <;> linarith
  let Φ : ℝ → (M ≃ₘ⟮I, I⟯ M) := fun t => (D (t₀ - a)).symm.trans (D (t - a))
  have htime (t : ℝ) (ht : t ∈ Ioo (t₀ - T) (t₀ + T)) : t - a ∈ Ioo 0 hi := by
    dsimp [a]
    constructor <;> linarith [ht.1, ht.2]
  have hΦsm : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => Φ q.1 q.2) (Ioo (t₀ - T) (t₀ + T) ×ˢ univ) := by
    have hparam : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
        (fun q : ℝ × M => (q.1 - a, (D (t₀ - a)).symm q.2)) := by
      apply ContMDiff.prodMk
      · change ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => q.1 - a)
        have hh : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
            (Prod.fst + fun _ : ℝ × M => -a) := contMDiff_fst.add contMDiff_const
        exact hh.congr (fun _ => by rfl)
      · exact (D (t₀ - a)).symm.contMDiff.comp contMDiff_snd
    exact hDsm.comp hparam.contMDiffOn
      (fun q hq => ⟨htime q.1 hq.1, mem_univ _⟩)
  refine ⟨Φ, ?_, hΦsm,
    DifferentialGeometry.Topology.Manifold.contMDiffOn_diffeomorph_family_symm Φ isOpen_Ioo hΦsm, ?_⟩
  · intro x
    exact (D (t₀ - a)).apply_symm_apply x
  · intro t ht x
    let y := (D (t₀ - a)).symm x
    have hs := htime t ht
    have hode := hFode (t - a) ⟨lt_trans hlo hs.1, hs.2⟩ y
    have hshift : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => s - a) t
        (ContinuousLinearMap.id ℝ ℝ) := ((hasFDerivAt_id t).sub_const a).hasMFDerivAt
    have hcomp := hode.comp t hshift
    have heq : (fun s : ℝ => Φ s x) =ᶠ[𝓝 t] fun s => F (s - a) y := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact hD (s - a) (htime s hs) y
    have hv : Y (t - a) (F (t - a) y) = X t (Φ t x) := by
      rw [show Φ t x = F (t - a) y from hD (t - a) hs y]
      simp only [Y, sub_add_cancel]
    rw [hv] at hcomp
    have hresult := hcomp.congr_of_eventuallyEq heq
    exact hresult.congr_mfderiv (by rfl)

end DifferentialGeometry.Analysis.ODE
