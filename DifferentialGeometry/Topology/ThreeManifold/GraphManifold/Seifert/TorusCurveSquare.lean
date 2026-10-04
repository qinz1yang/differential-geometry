import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusCurveCrossing
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.SquareArc
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph

/-!
# Torus curves: square charts and the transported square-arc isotopy

Chapter 6, packet K08, lane MC4 of the `TorusMappingClassLinear` programme.
-/

set_option autoImplicit false

noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.Seifert

open AnnulusStraightening

theorem isOpen_openSquare : IsOpen openSquare :=
  isOpen_Ioo.reProdIm isOpen_Ioo

theorem half_add_mem_openSquare {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (1 / 2 : ℂ) + (t : ℂ) * Complex.I ∈ openSquare := by
  rw [mem_openSquare]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  norm_num
  exact ht

theorem exists_square_transport {M : ℂ → ℝ × ℝ} {N : ℝ × ℝ → ℂ} {B : Set (ℝ × ℝ)}
    (hB : IsOpen B) (hBinj : InjOn torusCover B)
    (hM : ContDiffOn ℝ ∞ M openSquare) (hN : ContDiffOn ℝ ∞ N B)
    (hMB : MapsTo M openSquare B) (hNB : MapsTo N B openSquare)
    (hNM : ∀ z ∈ openSquare, N (M z) = z) (hMN : ∀ p ∈ B, M (N p) = p)
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ ∞ γ) (hinj : InjOn γ (Icc 0 1)) (himm : ∀ t, deriv γ t ≠ 0)
    {δ : ℝ} (hδ : 0 < δ)
    (hend : ∀ t, t ≤ δ ∨ 1 - δ ≤ t → γ t = (1 / 2 : ℂ) + (t : ℂ) * Complex.I)
    (hin : ∀ t ∈ Ioo (0 : ℝ) 1, γ t ∈ openSquare) :
    ∃ Q : TDiff, IsotopicDiffeomorph torusRefl Q ∧
      ∃ C : Set Torus, IsCompact C ∧ C ⊆ torusCover '' B ∧ (∀ z, z ∉ C → Q z = z) ∧
      ∀ t ∈ Ioo (0 : ℝ) 1, Q (torusCover (M ((1 / 2 : ℂ) + (t : ℂ) * Complex.I))) =
        torusCover (M (γ t)) := by
  obtain ⟨H, hH, hH', hH0, ⟨K, hK, hKsq, hKfix⟩, hH1⟩ :=
    exists_isotopy_square_arc hγ hinj himm hδ hend hin
  set E : ℂ → Torus := torusCover ∘ M with hE
  let e : OpenPartialHomeomorph ℂ (ℝ × ℝ) :=
    { toFun := M
      invFun := N
      source := openSquare
      target := B
      map_source' := hMB
      map_target' := hNB
      left_inv' := hNM
      right_inv' := hMN
      open_source := isOpen_openSquare
      open_target := hB
      continuousOn_toFun := hM.continuousOn
      continuousOn_invFun := hN.continuousOn }
  have hloc : IsLocalDiffeomorphOn 𝓘(ℝ, ℂ) torusModel ∞ E openSquare := by
    intro z
    have hMz : IsLocalDiffeomorphAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ × ℝ) ∞ M z :=
      OpenPartialHomeomorph.isLocalDiffeomorphAt_of_contMDiffOn (e := e)
        (contMDiffOn_iff_contDiffOn.mpr hM) (contMDiffOn_iff_contDiffOn.mpr hN) z.2
    exact _root_.IsLocalDiffeomorphAt.comp (hf := hMz) (hg := isLocalDiffeomorph_torusCover (M z))
  have hinjE : InjOn E openSquare := by
    intro z hz w hw hzw
    have h1 : M z = M w := hBinj (hMB hz) (hMB hw) hzw
    rw [← hNM z hz, ← hNM w hw, h1]
  have hne : openSquare.Nonempty :=
    ⟨_, half_add_mem_openSquare (t := 1 / 2) ⟨by norm_num, by norm_num⟩⟩
  obtain ⟨P, hPs, -, hPf⟩ :=
    IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn hloc isOpen_openSquare hne hinjE
  have hPapp (z : ℂ) : P.symm.symm z = E z := congrFun hPf z
  have hDm : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ) ∞ (fun z : ℝ × ℂ => H z.1 z.2) :=
    hH.contMDiff.comp (contMDiff_fst.prodMk_space contMDiff_snd)
  have hDim : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ) ∞
      (fun z : ℝ × ℂ => (H z.1).symm z.2) :=
    hH'.contMDiff.comp (contMDiff_fst.prodMk_space contMDiff_snd)
  have hKt : K ⊆ P.symm.target := by
    rw [show P.symm.target = openSquare from hPs]
    exact hKsq
  obtain ⟨Θ, hΘ, hΘi, -, hΘf, -, hΘ0, hCc, -, hΘs⟩ :=
    PartialDiffeomorph.exists_isotopy_extension_of_isCompact P.symm H hDm hDim hK hKt
      (fun p x hx => hKfix p x hx)
  refine ⟨Θ 1, ⟨Θ, hΘ, hΘi, hΘ0 0 hH0, rfl⟩, P.symm.symm '' K, hCc, ?_,
    fun z hz => (hΘs 1 z hz).1, fun t ht => ?_⟩
  · rintro _ ⟨k, hk, rfl⟩
    rw [hPapp]
    exact ⟨M k, hMB (hKsq hk), rfl⟩
  · have hw := half_add_mem_openSquare ht
    have h := hΘf 1 _ (show (1 / 2 : ℂ) + (t : ℂ) * Complex.I ∈ P.symm.target by
      rw [show P.symm.target = openSquare from hPs]
      exact hw)
    rw [hPapp, hPapp, hH1 t (Ioo_subset_Icc_self ht)] at h
    exact h

end GC.Seifert
