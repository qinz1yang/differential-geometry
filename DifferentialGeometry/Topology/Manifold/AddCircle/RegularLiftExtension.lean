import DifferentialGeometry.External.CanonicalTopology.Topology.LoopSpace.SpanningDisk
import DifferentialGeometry.Topology.Manifold.AddCircle.Circle
import DifferentialGeometry.Topology.Embedding.PeriodicCurveIsotopy
import DifferentialGeometry.Topology.Embedding.Sphere
import DifferentialGeometry.Topology.Embedding.Diffeomorph
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingCompositionInterior
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorphImmersion
import DifferentialGeometry.Topology.Homeomorph.Ball
import Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber

set_option autoImplicit false
noncomputable section

open Set Metric
open DifferentialGeometry DifferentialGeometry.Topology
open scoped ContDiff Manifold

namespace AddCircle

/-- A regular degree-one lift yields the actual circle diffeomorphism and an
ambient disk-preserving extension of that same phase. The extension is
constructed by the existing periodic-curve isotopy theorem, with support away
from the center. No diffeomorphism, injectivity, or extension is assumed. -/
theorem exists_diffeomorph_extension_of_regular_degree_one_lift
    {σ : C(loopCircle, loopCircle)} {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hperiod : ∀ t, ψ (t + 1) = ψ t + 1)
    (hder : ∀ t, 0 < deriv ψ t)
    (hlift : ∀ t : ℝ, (ψ t : loopCircle) = σ (t : loopCircle)) :
    ∃ Q : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) loopCircle loopCircle ∞,
      (∀ θ, Q θ = σ θ) ∧ ∃ Φ : ℂ ≃ₘ[ℝ] ℂ,
        (∀ θ : loopCircle, Φ (diskBoundary θ) = (diskBoundary (σ θ) : ℂ)) ∧
        Φ 0 = 0 ∧ Φ '' closedBall (0 : ℂ) 1 = closedBall 0 1 := by
  let a : CircleDeg1Lift :=
    { toFun := ψ
      monotone' := (strictMono_of_deriv_pos hder).monotone
      map_add_one' := hperiod }
  have hsurψ : Function.Surjective ψ :=
    (CircleDeg1Lift.continuous_iff_surjective a).mp hψ.continuous
  have hsurσ : Function.Surjective σ := by
    intro θ
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
    obtain ⟨s, hs⟩ := hsurψ t
    exact ⟨(s : loopCircle), (hlift s).symm.trans (congrArg (fun r : ℝ =>
      (r : loopCircle)) hs)⟩
  let _ : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨by simp⟩
  let A := AddCircle.diffeomorphCircle
  let f : loopCircle → ℂ := fun θ => A θ
  have hA : Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) (𝓡 1) ∞ A :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_of_isLocalDiffeomorph_of_injective
      A.isLocalDiffeomorph A.injective
  have hf : Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ f :=
    (isSmoothEmbedding_coe_sphere (E := ℂ) (n := 1)).comp_of_boundarylessManifold hA
      (by simp)
  obtain ⟨Φ, _, _, _, htrack, K, _, hK, hfix⟩ :=
    PeriodicCurve.exists_compactly_supported_ambient_isotopy_of_increasing_lift
      hf hψ hperiod hder isOpen_compl_singleton
      (show range f ⊆ ({0} : Set ℂ)ᶜ from by
        rintro _ ⟨θ, rfl⟩
        exact ne_zero_of_mem_unit_sphere (A θ))
  have htrack1 (θ : loopCircle) : Φ 1 (f θ) = f (σ θ) := by
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
    rw [← hlift t]
    simpa only [sub_self, zero_mul, one_mul, zero_add] using
      htrack 1 ⟨zero_le_one, le_rfl⟩ t
  have hzero : Φ 1 0 = 0 := (hfix 1).1 (by
    intro hz
    exact hK hz rfl)
  have hrange : range (Φ 1 ∘ f) = range f := by
    ext z
    constructor
    · rintro ⟨θ, rfl⟩
      exact ⟨σ θ, (htrack1 θ).symm⟩
    · rintro ⟨θ, rfl⟩
      obtain ⟨η, rfl⟩ := hsurσ θ
      exact ⟨η, htrack1 η⟩
  let Q := (hf.diffeomorph_comp (Φ 1)).diffeomorphOfRangeEq hf hrange
  have hQ (θ : loopCircle) : Q θ = σ θ := by
    apply hf.isEmbedding.injective
    exact ((hf.diffeomorph_comp (Φ 1)).comp_diffeomorphOfRangeEq hf hrange θ).trans
      (htrack1 θ)
  have hfBoundary (θ : loopCircle) : f θ = (diskBoundary θ : ℂ) := by
    change (A θ : ℂ) = (diskBoundary θ : ℂ)
    congr 1
    exact AddCircle.homeomorphCircle_apply one_ne_zero θ
  have hfSphere : range f = sphere (0 : ℂ) 1 := by
    ext z
    constructor
    · rintro ⟨θ, rfl⟩
      exact (A θ).property
    · intro hz
      exact ⟨A.symm ⟨z, hz⟩, congrArg Subtype.val (A.apply_symm_apply ⟨z, hz⟩)⟩
  refine ⟨Q, hQ, Φ 1, ?_, hzero, ?_⟩
  · intro θ
    simpa only [hfBoundary] using htrack1 θ
  · apply (Φ 1).toHomeomorph.image_closedBall_of_image_sphere_eq_of_map_center
      zero_lt_one zero_lt_one ?_ hzero
    rw [← hfSphere, ← range_comp]
    exact hrange

end AddCircle
