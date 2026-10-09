import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.IdGerm_O40

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.CheegerGromovCompactness
open Set TopologicalSpace Filter
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.LongTime.Ch12

/-! CH12-O50 GA: the isotopy part of the P2 step with the jets region decoupled from the endpoint
region.  `isotopy_assembly_O40` needs `Ψ μ 0 (B) ⊆ D' ⊆ interior D` with `D` the endpoint region;
with the hCX3ext support `C := D2 ⊋ D` (S102) this cannot cover `C`.  Here the jets of `W t` are
extended from the closed set `D2` to every set (`W t = id` off `D2`), `ckErr_of_chartJets_S80` is
called with `D := univ`, and points off `B ⊇ C` are handled by the identity germ (O40 G2), so the
ckErr bound holds at EVERY point. -/

section Generic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- `CkCloseInAtlas_CX3` on a closed `D2` extends to any set when `Φ = id` off `D2`. -/
theorem ckClose_of_eq_id_off_O50 (A : CkAtlas_S15 I M) {D2 : Set M} (hD2 : IsClosed D2)
    {k : ℕ} {δ : ℝ} (hδ : 0 < δ) {Φ : M → M} (hΦ : ∀ y, y ∉ D2 → Φ y = y)
    (h : CkCloseInAtlas_CX3 A D2 k δ Φ) (D : Set M) : CkCloseInAtlas_CX3 A D k δ Φ := by
  intro i x hx hxD
  by_cases hxD2 : (extChartAt I (A.ctr i)).symm x ∈ D2
  · exact h i x hx hxD2
  have htgt : x ∈ (extChartAt I (A.ctr i)).target := A.closedBall_sub i hx
  have hsrc : (extChartAt I (A.ctr i)).symm x ∈ (extChartAt I (A.ctr i)).source :=
    (extChartAt I (A.ctr i)).map_target htgt
  refine ⟨by rw [hΦ _ hxD2]; exact hsrc, fun j _ => ?_⟩
  have hev : chartDisplacement_CX3 (I := I) (A.ctr i) Φ =ᶠ[𝓝 x] fun _ => (0 : E) := by
    have h1 : ∀ᶠ y in 𝓝 x, y ∈ (extChartAt I (A.ctr i)).target :=
      (isOpen_extChartAt_target (A.ctr i)).mem_nhds htgt
    have h2 : ∀ᶠ y in 𝓝 x, (extChartAt I (A.ctr i)).symm y ∉ D2 :=
      (continuousAt_extChartAt_symm'' htgt).preimage_mem_nhds
        (hD2.isOpen_compl.mem_nhds hxD2)
    filter_upwards [h1, h2] with y hy1 hy2
    simp only [chartDisplacement_CX3, hΦ _ hy2, (extChartAt I (A.ctr i)).right_inv hy1, sub_self]
  rw [(hev.iteratedFDeriv ℝ j).eq_of_nhds, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
  exact hδ

end Generic

/-- **GA main.** Isotopy part of the P2 step (`E μ := Ψ μ 0`): smooth, bijective slices,
`E 0 = id`, identity off `B`, ckErr `≤ ε` at every point for `μ ∈ [0,1]`, endpoint identity. -/
theorem step_isotopy_O50 (H : FiniteVolumeHyperbolicModel.{u})
    (hchart : ∀ (A : CkAtlas_S15 (𝓡 3) H.Carrier) (D : Set H.Carrier) (k : ℕ) (ε : ℝ),
      IsCompact D → D ⊆ A.cover → 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ (F : H.Carrier → H.Carrier) (O : Set H.Carrier), IsOpen O → D ⊆ O →
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ F O → CkCloseInAtlas_CX3 A D (k + 1) δ F →
          ∀ j : ℕ, j ≤ k → ∀ q ∈ D, ckErr_S45 H H.metric 1 F j q ≤ ε)
    (A : CkAtlas_S15 (𝓡 3) H.Carrier) (D' : Set H.Carrier) (B : Opens H.Carrier)
    (hD'c : IsCompact D') (hBD' : (B : Set H.Carrier) ⊆ D') (hD'A : D' ⊆ A.cover) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (Ψ : ℝ → ℝ → H.Carrier → H.Carrier) (W : ℝ → H.Carrier → H.Carrier)
      (C D2 Dend : Set H.Carrier) {N : Type u} (f : H.Carrier → N) (φ : H.Carrier → N)
      (U' : Set H.Carrier) (e : H.Carrier ≃ H.Carrier),
      ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 3) ∞
        (fun q : (ℝ × ℝ) × H.Carrier => Ψ q.1.1 q.1.2 q.2) →
      (∀ s y, Ψ s s y = y) → (∀ s t u y, Ψ t u (Ψ s t y) = Ψ s u y) →
      IsClosed C → (∀ s t y, y ∉ C → Ψ s t y = y) → C ⊆ (B : Set H.Carrier) →
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ x, Ψ 0 t x = W t x) →
      IsClosed D2 → (∀ t ∈ Icc (0 : ℝ) 1, ∀ y, y ∉ D2 → W t y = y) →
      (∀ t ∈ Icc (0 : ℝ) 1, CkCloseInAtlas_CX3 A D2 (k + 1) ε₀ (W t)) →
      (∀ x ∈ Dend, f x ∈ φ '' U') →
      (∀ x ∈ Dend, Ψ 0 1 x = e.symm (Function.invFunOn φ U' (f x))) →
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ (fun q : ℝ × H.Carrier => Ψ q.1 0 q.2) ∧
      (∀ μ, ContMDiff (𝓡 3) (𝓡 3) ∞ (fun p => Ψ μ 0 p) ∧
        Function.Bijective (fun p => Ψ μ 0 p)) ∧
      (∀ p, Ψ 0 0 p = p) ∧
      (∀ μ p, p ∉ (B : Set H.Carrier) → Ψ μ 0 p = p) ∧
      (∀ μ ∈ Icc (0 : ℝ) 1, ∀ j : ℕ, j ≤ k → ∀ p : H.Carrier,
        ckErr_S45 H H.metric 1 (fun x => Ψ μ 0 x) j p ≤ ε) ∧
      (∀ p, Ψ 1 0 p ∈ Dend → f (Ψ 1 0 p) = φ (e p)) := by
  obtain ⟨ε₀, hε₀, hS80⟩ := ckErr_of_chartJets_S80 H hchart A univ D' B hD'c
    (by rw [interior_univ]; exact subset_univ _) hD'A k hε
  refine ⟨ε₀, hε₀, fun Ψ W C D2 Dend N f φ U' e hΨ hid hgrp hCc hC hCB hW hD2 hWid hjets hf
    hΨ1 => ?_⟩
  have : Nonempty H.Carrier := ⟨H.basepoint⟩
  obtain ⟨h0, hbij, hsupp, hend⟩ :=
    dyadic_endpoint_algebra_O20 f φ U' e Ψ Dend C hf hid hgrp hC hΨ1
  have hE : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
      (fun q : ℝ × H.Carrier => Ψ q.1 0 q.2) := by
    have hm : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (𝓡 3)) ∞
        (fun q : ℝ × H.Carrier => (((q.1, (0 : ℝ)) : ℝ × ℝ), q.2)) :=
      (contMDiff_fst.prodMk contMDiff_const).prodMk contMDiff_snd
    exact hΨ.comp hm
  have hmapC : ∀ μ p, p ∈ C → Ψ μ 0 p ∈ C := by
    intro μ p hp
    by_contra hn
    have h1 : Ψ μ 0 p = p := (hbij μ).1 (hsupp μ (Ψ μ 0 p) hn)
    exact hn (by rw [h1]; exact hp)
  have hloc : ∀ μ ∈ Icc (0 : ℝ) 1, ∀ p ∈ (B : Set H.Carrier), Ψ μ 0 p ∈ D' := by
    intro μ _ p hp
    by_cases hpC : p ∈ C
    · exact hBD' (hCB (hmapC μ p hpC))
    · rw [hsupp μ p hpC]; exact hBD' hp
  have hjets' : ∀ t ∈ Icc (0 : ℝ) 1, CkCloseInAtlas_CX3 A univ (k + 1) ε₀ (W t) :=
    fun t ht => ckClose_of_eq_id_off_O50 A hD2 hε₀ (hWid t ht) (hjets t ht) univ
  have hW' : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ (univ : Set H.Carrier), Ψ 0 t x = W t x :=
    fun t ht x _ => hW t ht x
  refine ⟨hE, fun μ => ⟨hE.comp (contMDiff_const.prodMk contMDiff_id), hbij μ⟩, h0,
    fun μ p hp => hsupp μ p (fun hpC => hp (hCB hpC)), fun μ hμ j hj p => ?_, hend⟩
  by_cases hpB : p ∈ (B : Set H.Carrier)
  · exact hS80 Ψ W hΨ hid hgrp hW' hjets' hloc μ hμ j hj p hpB
  · rw [ckErr_eq_zero_of_eq_id_O40 H (fun x => Ψ μ 0 x) ⟨Cᶜ, hCc.isOpen_compl⟩
      (fun x hx => hsupp μ x hx) j p (fun h => hpB (hCB h))]
    exact hε.le

end GC.LongTime.Ch12
