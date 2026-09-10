import DifferentialGeometry.Topology.Manifold.EmbeddedHypersurface.TopFormNormal
import DifferentialGeometry.Bundle.PositiveSection
import Mathlib.Geometry.Manifold.VectorBundle.Pullback

open Set Bundle DifferentialGeometry.Topology.Morse
open scoped Manifold ContDiff Topology
set_option autoImplicit false
noncomputable section

namespace Poincare.Manifold.EmbeddedHypersurface

private instance pullbackAddCommGroup {B B' : Type*} (f : B' → B) (V : B → Type*)
    [∀ b, AddCommGroup (V b)] (x : B') : AddCommGroup ((f *ᵖ V) x) :=
  inferInstanceAs (AddCommGroup (V (f x)))

variable {m : ℕ} {H G S M : Type*}
  [TopologicalSpace H] [TopologicalSpace G]
  [TopologicalSpace S] [ChartedSpace H S]
  [TopologicalSpace M] [ChartedSpace G M]
  (I : ModelWithCorners ℝ (MorseModel m) H)
  (J : ModelWithCorners ℝ (MorseModel (m + 1)) G)
  [I.Boundaryless] [J.Boundaryless] [IsManifold I ∞ S] [IsManifold J ∞ M]
  [T2Space S] [SigmaCompactSpace S]

theorem exists_contMDiff_transverse_of_topForms {e : S → M}
    (he : Manifold.IsImmersion I J ∞ e)
    (η : ∀ s : S, TangentSpace I s [⋀^Fin m]→L[ℝ] ℝ)
    (Ω : ∀ y : M, TangentSpace J y [⋀^Fin (m + 1)]→L[ℝ] ℝ)
    (hη : Continuous (fun s => TotalSpace.mk'
      (MorseModel m [⋀^Fin m]→L[ℝ] ℝ) s (η s)))
    (hΩ : Continuous (fun y => TotalSpace.mk'
      (MorseModel (m + 1) [⋀^Fin (m + 1)]→L[ℝ] ℝ) y (Ω y)))
    (hη0 : ∀ s, η s ≠ 0) (hΩ0 : ∀ s, Ω (e s) ≠ 0) :
    ∃ V : ∀ s : S, TangentSpace J (e s),
      ContMDiff I J.tangent ∞ (fun s => (⟨e s, V s⟩ : TangentBundle J M)) ∧
      (∀ s, 0 < topFormNormal I J e η Ω s (V s)) ∧
      ∀ s, V s ∉ (mfderiv I J e s).range := by
  let f : ContMDiffMap I J S M ∞ := ⟨e, he.contMDiff⟩
  let T := f *ᵖ (TangentSpace J (M := M))
  let ν : ∀ s : S, T s →L[ℝ] ℝ := topFormNormal I J e η Ω
  have hν : Continuous (fun s => TotalSpace.mk' (MorseModel (m + 1) →L[ℝ] ℝ)
      (E := fun s : S => T s →L[ℝ] ℝ) s (ν s)) := by
    have hc := continuous_topFormNormal I J e η Ω (he.contMDiff.of_le (by simp)) hη hΩ hη0
    apply continuous_iff_continuousAt.mpr
    intro x
    apply (continuousAt_hom_bundle (RingHom.id ℝ) _).mpr
    refine ⟨continuousAt_id, ?_⟩
    have hh := (continuousAt_hom_bundle (RingHom.id ℝ) _).mp
      (show ContinuousAt _ x from hc.continuousAt) |>.2
    apply hh.congr_of_eventuallyEq
    let t := trivializationAt (MorseModel (m + 1)) (TangentSpace J (M := M)) (e x)
    have hx : e x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' (e x)
    filter_upwards [he.contMDiff.continuous.continuousAt.preimage_mem_nhds
      (t.open_baseSet.mem_nhds hx)] with s hs
    have hsp : s ∈ (t.pullback f).baseSet := hs
    rw [ContinuousLinearMap.inCoordinates_eq
      (E' := Bundle.Trivial S ℝ) (y₀ := x) (y := s)
      (show s ∈ (trivializationAt (MorseModel (m + 1)) T x).baseSet from hs)
      (mem_univ s),
      ContinuousLinearMap.inCoordinates_eq
      (E' := Bundle.Trivial M ℝ) (y₀ := e x) (y := e s) hs (mem_univ (e s))]
    change (ContinuousLinearEquiv.refl ℝ ℝ).toContinuousLinearMap.comp
        ((ν s).comp (((t.pullback f).continuousLinearEquivAt ℝ s hsp).symm :
          MorseModel (m + 1) →L[ℝ] T s)) =
      (ContinuousLinearEquiv.refl ℝ ℝ).toContinuousLinearMap.comp
        ((ν s).comp ((t.continuousLinearEquivAt ℝ (e s) hs).symm :
          MorseModel (m + 1) →L[ℝ] TangentSpace J (e s)))
    ext v
    change ν s (((t.pullback f).continuousLinearEquivAt ℝ s hsp).symm v) =
      ν s ((t.continuousLinearEquivAt ℝ (e s) hs).symm v)
    rw [Bundle.Trivialization.symm_continuousLinearEquivAt_eq (e := t.pullback f),
      Bundle.Trivialization.symm_continuousLinearEquivAt_eq (e := t),
      Bundle.Trivialization.symmL_apply (t.pullback f) hsp,
      Bundle.Trivialization.symmL_apply t hs]
    congr 1
    rw [(t.pullback f).symm_apply hsp]
    rfl
  have hν0 (s : S) : ν s ≠ 0 :=
    topFormNormal_ne_zero I J e η Ω (he.isImmersionAt s) (hη0 s) (hΩ0 s)
  obtain ⟨V, hV, hpos⟩ := Poincare.VectorBundle.exists_contMDiff_section_covector_pos I T ν hν hν0
  refine ⟨V, ?_, hpos, ?_⟩
  · intro x
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨he.contMDiff x, ?_⟩
    exact (Bundle.contMDiffAt_totalSpace.mp (hV x)).2
  · intro s hv
    have hz : topFormNormal I J e η Ω s (V s) = 0 := by
      change V s ∈ (topFormNormal I J e η Ω s).ker
      rw [ker_topFormNormal I J e η Ω (he.isImmersionAt s) (hη0 s) (hΩ0 s)]
      exact hv
    exact (ne_of_gt (hpos s)) hz

end Poincare.Manifold.EmbeddedHypersurface
