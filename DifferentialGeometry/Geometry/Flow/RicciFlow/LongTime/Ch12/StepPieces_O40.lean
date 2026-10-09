import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ChartJets_S80
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.DyadicWindow_O20
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CkErrNaturalitySource_O19
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.S7Embed_S86
import DifferentialGeometry.Topology.Embedding.Diffeomorph
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.CheegerGromovCompactness
open Set TopologicalSpace
open Manifold
open scoped Manifold ContDiff

universe u

namespace GC.LongTime.Ch12

/-! CH12-O40 G1: two pieces of the P2 producer (`[FROZEN v2] CH12-O40`), common to the lead's
ruling (A).  (b) GOOD of `g₂ := φ ∘ e` for an isometry `e` of `H` (N2); (d) the isotopy
`E μ := Ψ μ 0` built from a two-time flow `Ψ` (CX3 output shape + the support-in-a-ball and
`hloc` facts of the CX3 extension), via `dyadic_endpoint_algebra_O20` and S80's
`ckErr_of_chartJets_S80`. -/

/-- (b) GOOD transfers along an isometry of the source: if `φ` is GOOD at accuracy `β` on the
`e`-image of the ball, then `φ ∘ e` is GOOD at `β` (v5 GOOD text). -/
theorem good_comp_isometry_O40 (H : FiniteVolumeHyperbolicModel.{u})
    {N : Type u} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    [IsManifold (𝓡 3) ∞ N] (gN : SmoothRiemannianMetric (𝓡 3) N) (c : ℝ) (hc : 0 < c)
    (e : H.Carrier ≃ H.Carrier) (he : ContMDiff (𝓡 3) (𝓡 3) ∞ e)
    (he' : ContMDiff (𝓡 3) (𝓡 3) ∞ e.symm)
    (hiso : ∀ p, localPullInner H.metric e p = H.metric.inner p)
    (φ : H.Carrier → N) (β : ℝ) (U' : Opens H.Carrier)
    (hU' : e '' riemannianBallOf H.metric H.basepoint (2 * β⁻¹) ⊆ U')
    (hφ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ U')
    (hemb : IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U' => φ x))
    (herr : ∀ k : ℕ, k ≤ ⌈β⁻¹⌉₊ →
      ∀ y ∈ e '' riemannianBallOf H.metric H.basepoint (2 * β⁻¹), ckErr_S45 H gN c φ k y < β) :
    ∃ U : Opens H.Carrier,
      riemannianBallOf H.metric H.basepoint (2 * β⁻¹) ⊆ U ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun x => φ (e x)) U ∧
      IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => φ (e x)) ∧
      ∀ k : ℕ, k ≤ ⌈β⁻¹⌉₊ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * β⁻¹),
        ckErr_S45 H gN c (fun x => φ (e x)) k p < β := by
  let U : Opens H.Carrier := ⟨e ⁻¹' U', U'.isOpen.preimage he.continuous⟩
  have hinj : ∀ y ∈ U', Function.Injective (mfderiv (𝓡 3) (𝓡 3) φ y) :=
    injective_mfderiv_of_embedding_S86 φ U' hφ hemb
  refine ⟨U, fun x hx => hU' ⟨x, hx, rfl⟩, ?_, ?_, fun k hk p hp => ?_⟩
  · exact hφ.comp he.contMDiffOn (fun x hx => hx)
  · let Φ := (isoDiffeo_O19 e he he').toPartialDiffeomorph
    have hUΦ : (U : Set H.Carrier) ⊆ Φ.source := fun x _ => mem_univ x
    have hW : (⟨(Φ : H.Carrier → H.Carrier) '' (U : Set H.Carrier),
        image_opens_isOpen Φ hUΦ⟩ : Opens H.Carrier) = U' := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hy
        exact ⟨e.symm y, by simpa [U] using hy, e.apply_symm_apply y⟩
    have hemb' : IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞
        (fun x : (⟨(Φ : H.Carrier → H.Carrier) '' (U : Set H.Carrier),
          image_opens_isOpen Φ hUΦ⟩ : Opens H.Carrier) => φ x) := by
      rw [hW]; exact hemb
    exact hemb'.comp_diffeomorph (PartialDiffeomorph.toOpensDiffeo Φ hUΦ)
  · have hep : e p ∈ U' := hU' ⟨p, hp, rfl⟩
    change ckErr_O19 H gN c (fun q => φ (e q)) k p < β
    rw [ckErr_comp_isometry_source_O19 H H e he he' hiso gN U' φ hφ hinj c hc k p hep]
    exact herr k hk (e p) ⟨p, hp, rfl⟩

/-- (d) The isotopy `E μ := Ψ μ 0` of a two-time flow `Ψ` (CX3 output shape; support set `C`
inside a ball, `hloc` from the CX3 extension): smooth, bijective slices, `E 0 = id`, identity off
the ball, all-`μ` ckErr closeness (S80, `hchart` inline = `[FROZEN v2] CH12-S80`), and the
endpoint identity `f ∘ E 1 = φ ∘ e` (O20). -/
theorem isotopy_assembly_O40 (H : FiniteVolumeHyperbolicModel.{u})
    (hchart : ∀ (A : CkAtlas_S15 (𝓡 3) H.Carrier) (D : Set H.Carrier) (k : ℕ) (ε : ℝ),
      IsCompact D → D ⊆ A.cover → 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ (F : H.Carrier → H.Carrier) (O : Set H.Carrier), IsOpen O → D ⊆ O →
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ F O → CkCloseInAtlas_CX3 A D (k + 1) δ F →
          ∀ j : ℕ, j ≤ k → ∀ q ∈ D, ckErr_S45 H H.metric 1 F j q ≤ ε)
    (A : CkAtlas_S15 (𝓡 3) H.Carrier) (D D' : Set H.Carrier) (B : Opens H.Carrier)
    (hD'c : IsCompact D') (hD'D : D' ⊆ interior D) (hD'A : D' ⊆ A.cover) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (Ψ : ℝ → ℝ → H.Carrier → H.Carrier) (W : ℝ → H.Carrier → H.Carrier)
      (C : Set H.Carrier) (ρ : ℝ) {N : Type u} (f : H.Carrier → N) (φ : H.Carrier → N)
      (U' : Set H.Carrier) (e : H.Carrier ≃ H.Carrier),
      ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 3) ∞
        (fun q : (ℝ × ℝ) × H.Carrier => Ψ q.1.1 q.1.2 q.2) →
      (∀ s y, Ψ s s y = y) → (∀ s t u y, Ψ t u (Ψ s t y) = Ψ s u y) →
      (∀ s t y, y ∉ C → Ψ s t y = y) → C ⊆ riemannianBallOf H.metric H.basepoint ρ →
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ D, Ψ 0 t x = W t x) →
      (∀ t ∈ Icc (0 : ℝ) 1, CkCloseInAtlas_CX3 A D (k + 1) ε₀ (W t)) →
      (∀ μ ∈ Icc (0 : ℝ) 1, ∀ p ∈ (B : Set H.Carrier), Ψ μ 0 p ∈ D') →
      (∀ x ∈ D, f x ∈ φ '' U') →
      (∀ x ∈ D, Ψ 0 1 x = e.symm (Function.invFunOn φ U' (f x))) →
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ (fun q : ℝ × H.Carrier => Ψ q.1 0 q.2) ∧
      (∀ μ, ContMDiff (𝓡 3) (𝓡 3) ∞ (fun p => Ψ μ 0 p) ∧
        Function.Bijective (fun p => Ψ μ 0 p)) ∧
      (∀ p, Ψ 0 0 p = p) ∧
      (∀ μ p, p ∉ riemannianBallOf H.metric H.basepoint ρ → Ψ μ 0 p = p) ∧
      (∀ μ ∈ Icc (0 : ℝ) 1, ∀ j : ℕ, j ≤ k → ∀ p ∈ (B : Set H.Carrier),
        ckErr_S45 H H.metric 1 (fun x => Ψ μ 0 x) j p ≤ ε) ∧
      (∀ p, Ψ 1 0 p ∈ D → f (Ψ 1 0 p) = φ (e p)) := by
  obtain ⟨ε₀, hε₀, hS80⟩ := ckErr_of_chartJets_S80 H hchart A D D' B hD'c hD'D hD'A k hε
  refine ⟨ε₀, hε₀, fun Ψ W C ρ N f φ U' e hΨ hid hgrp hC hCρ hW hjets hloc hf hΨ1 => ?_⟩
  have : Nonempty H.Carrier := ⟨H.basepoint⟩
  obtain ⟨h0, hbij, hsupp, hend⟩ :=
    dyadic_endpoint_algebra_O20 f φ U' e Ψ D C hf hid hgrp hC hΨ1
  have hE : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
      (fun q : ℝ × H.Carrier => Ψ q.1 0 q.2) := by
    have hm : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (𝓡 3)) ∞
        (fun q : ℝ × H.Carrier => (((q.1, (0 : ℝ)) : ℝ × ℝ), q.2)) :=
      (contMDiff_fst.prodMk contMDiff_const).prodMk contMDiff_snd
    exact hΨ.comp hm
  refine ⟨hE, fun μ => ⟨?_, hbij μ⟩, h0, fun μ p hp => hsupp μ p (fun hpC => hp (hCρ hpC)),
    hS80 Ψ W hΨ hid hgrp hW hjets hloc, hend⟩
  exact hE.comp (contMDiff_const.prodMk contMDiff_id)

end GC.LongTime.Ch12
