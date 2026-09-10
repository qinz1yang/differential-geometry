import DifferentialGeometry.Topology.Manifold.EmbeddedHypersurface.Tangent
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

open Set DifferentialGeometry.Topology.Morse
open scoped Manifold ContDiff Topology
set_option autoImplicit false
noncomputable section

namespace Poincare.Manifold.EmbeddedHypersurface

variable {m : ℕ} {H G S M : Type*}
  [TopologicalSpace H] [TopologicalSpace G]
  [TopologicalSpace S] [ChartedSpace H S]
  [TopologicalSpace M] [ChartedSpace G M]
  (I : ModelWithCorners ℝ (MorseModel m) H)
  (J : ModelWithCorners ℝ (MorseModel (m + 1)) G)
  [I.Boundaryless] [J.Boundaryless] [IsManifold J ∞ M]

omit I [I.Boundaryless] [J.Boundaryless] in
theorem continuousAt_mfderiv_apply_along {e : S → M}
    {V : ∀ s, TangentSpace J (e s)} {x : S}
    (hV : ContinuousAt (fun s => (⟨e s, V s⟩ : TangentBundle J M)) x)
    {U : Set M} (hU : IsOpen U) {f : M → ℝ}
    (hf : ContMDiffOn J 𝓘(ℝ, ℝ) ∞ f U) (hx : e x ∈ U) :
    ContinuousAt (fun s => (mfderiv J 𝓘(ℝ, ℝ) f (e s)) (V s) : S → ℝ) x := by
  let σ : S → TangentBundle J M := fun s => ⟨e s, V s⟩
  have he : ContinuousAt e x := (FiberBundle.continuous_proj
    (MorseModel (m + 1)) (TangentSpace J)).continuousAt.comp hV
  have hO : IsOpen ((Bundle.TotalSpace.proj : TangentBundle J M → M) ⁻¹' U) :=
    hU.preimage (FiberBundle.continuous_proj (MorseModel (m + 1)) (TangentSpace J))
  have hT := (hf.continuousOn_tangentMapWithin (by simp) hU.uniqueMDiffOn).continuousAt
    (hO.mem_nhds (show σ x ∈ Bundle.TotalSpace.proj ⁻¹' U from hx))
  have hC := (FiberBundle.continuousAt_totalSpace ℝ
    (fun s => tangentMapWithin J 𝓘(ℝ, ℝ) f U (σ s))).mp (hT.comp hV)
  have hD : ContinuousAt
      (fun s => (mfderivWithin J 𝓘(ℝ, ℝ) f U (e s)) (V s) : S → ℝ) x := by
    have hc := hC.2
    simp only [trivializationAt_model_space_apply] at hc
    exact hc
  apply hD.congr_of_eventuallyEq
  filter_upwards [he.preimage_mem_nhds (hU.mem_nhds hx)] with s hs
  rw [mfderivWithin_of_isOpen hU hs]

theorem exists_positive_local_definingFunction {e : S → M}
    (he : Manifold.IsSmoothEmbedding I J ∞ e)
    (V : ∀ s, TangentSpace J (e s))
    (hV : Continuous (fun s => (⟨e s, V s⟩ : TangentBundle J M))) (x : S)
    (htrans : V x ∉ (mfderiv I J e x).range) :
    ∃ U : Set M, IsOpen U ∧ e x ∈ U ∧
      ∃ f : M → ℝ, ContMDiffOn J 𝓘(ℝ, ℝ) ∞ f U ∧
        (∀ y ∈ U, f y = 0 ↔ y ∈ range e) ∧
        (∀ y ∈ U, mfderiv J 𝓘(ℝ, ℝ) f y ≠ 0) ∧
        ∀ s, e s ∈ U → (0 : ℝ) < ((mfderiv J 𝓘(ℝ, ℝ) f (e s)) (V s) : ℝ) := by
  obtain ⟨U, hU, hx, f, hf, hz, hr⟩ := exists_local_definingFunction I J he x
  have hfzero : f ∘ e =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [he.isEmbedding.continuous.continuousAt.preimage_mem_nhds
      (hU.mem_nhds hx)] with s hs
    exact (hz (e s) hs).mpr (mem_range_self s)
  have hd : (mfderiv J 𝓘(ℝ, ℝ) f (e x)) (V x) ≠ 0 :=
    mfderiv_apply_ne_zero_of_transverse I J (he.isImmersion.isImmersionAt x)
      ((hf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)) hfzero (hr _ hx) htrans
  obtain ⟨g, hg, hgz, hgr, hpos⟩ :
      ∃ g : M → ℝ, ContMDiffOn J 𝓘(ℝ, ℝ) ∞ g U ∧
        (∀ y ∈ U, g y = 0 ↔ y ∈ range e) ∧
        (∀ y ∈ U, mfderiv J 𝓘(ℝ, ℝ) g y ≠ 0) ∧
        (0 : ℝ) < ((mfderiv J 𝓘(ℝ, ℝ) g (e x)) (V x) : ℝ) := by
    change ((mfderiv J 𝓘(ℝ, ℝ) f (e x)) (V x) : ℝ) ≠ 0 at hd
    rcases lt_or_gt_of_ne (α := ℝ) hd with hn | hp
    · refine ⟨-f, (contDiff_neg.contMDiff.comp_contMDiffOn hf), ?_, ?_, ?_⟩
      · intro y hy
        simpa only [Pi.neg_apply, neg_eq_zero] using hz y hy
      · intro y hy
        rw [mfderiv_neg]
        exact neg_ne_zero.mpr (hr y hy)
      · rw [mfderiv_neg]
        change (0 : ℝ) < -(mfderiv J 𝓘(ℝ, ℝ) f (e x)) (V x)
        exact neg_pos.mpr hn
    · exact ⟨f, hf, hz, hr, hp⟩
  have hc := continuousAt_mfderiv_apply_along J hV.continuousAt hU hg hx
  obtain ⟨W, hWsub, hW, hxW⟩ := mem_nhds_iff.mp
    (hc.preimage_mem_nhds (isOpen_Ioi.mem_nhds hpos))
  obtain ⟨A, hA, hApre⟩ := he.isEmbedding.isInducing.isOpen_iff.mp hW
  refine ⟨U ∩ A, hU.inter hA, ⟨hx, ?_⟩, g, hg.mono inter_subset_left,
    (fun y hy => hgz y hy.1), (fun y hy => hgr y hy.1), ?_⟩
  · change x ∈ e ⁻¹' A
    rwa [hApre]
  · intro s hs
    apply hWsub
    rw [← hApre]
    exact hs.2

end Poincare.Manifold.EmbeddedHypersurface
