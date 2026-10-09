import DifferentialGeometry.Geometry.Comparison.Variation.Field.CompactExponential
import DifferentialGeometry.Bundle.Hom.Pointwise

set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.Variation

open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]

/-- Realize all vectors in a finite-dimensional parameter space by one joint
variation. Near the compact central curve this is the actual exponential, so
its endpoint germs preserve the second jets as well as the variation fields. -/
theorem exists_joint_variation_of_linear_fields
    (g : SmoothRiemannianMetric I M) (gamma : ℝ → M)
    (A : (t : ℝ) → P →L[ℝ] TangentSpace I (gamma t)) (a b : ℝ)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) I (8 : ℕ) gamma)
    (hA : ∀ z : P, ContMDiff 𝓘(ℝ, ℝ) I.tangent (8 : ℕ)
      (fun t => (⟨gamma t, A t z⟩ : TangentBundle I M))) :
    ∃ (f : P × ℝ → M) (U : Set (P × ℝ)),
      ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) I (8 : ℕ) f ∧
      IsOpen U ∧
      (∀ t ∈ uIcc a b, ((0 : P), t) ∈ U) ∧
      (∀ t, f (0, t) = gamma t) ∧
      (∀ t ∈ uIcc a b,
        (mfderiv 𝓘(ℝ, P) I (fun z => f (z, t)) 0 : P →L[ℝ] E) = A t) ∧
      (∀ t, A t = 0 → ∀ z, f (z, t) = gamma t) ∧
      ∀ z ∈ U, A z.2 z.1 ∈ expDomain (I := I) g (gamma z.2) ∧
        f z = expMap (I := I) g (gamma z.2) (A z.2 z.1) := by
  classical
  let C : Set M := gamma '' uIcc a b
  have hC : IsCompact C := isCompact_uIcc.image hgamma.continuous
  obtain ⟨F, W, hF, hWopen, hFzero, hzeroW, hexp⟩ :=
    exists_compact_exponential g C hC
  let launch : P × ℝ → TangentBundle I M :=
    fun z => ⟨gamma z.2, A z.2 z.1⟩
  have hlaunch : ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) I.tangent (8 : ℕ) launch := by
    have h := ContinuousLinearMap.contMDiff_bundle_apply_of_pointwise hA
    exact h.comp (contMDiff_snd.prodMk contMDiff_fst)
  let f : P × ℝ → M := F ∘ launch
  let U : Set (P × ℝ) := launch ⁻¹' W
  have hf : ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) I (8 : ℕ) f :=
    (hF.of_le (WithTop.coe_le_coe.mpr le_top)).comp hlaunch
  have hUopen : IsOpen U := hWopen.preimage hlaunch.continuous
  have hzeroU (t : ℝ) (ht : t ∈ uIcc a b) : ((0 : P), t) ∈ U := by
    change (⟨gamma t, A t 0⟩ : TangentBundle I M) ∈ W
    rw [map_zero]
    exact hzeroW (gamma t) ⟨t, ht, rfl⟩
  have hfzero (t : ℝ) : f (0, t) = gamma t := by
    change F (⟨gamma t, A t 0⟩ : TangentBundle I M) = gamma t
    rw [map_zero]
    exact hFzero (gamma t)
  have hjet (t : ℝ) (ht : t ∈ uIcc a b) :
      (mfderiv 𝓘(ℝ, P) I (fun z => f (z, t)) 0 : P →L[ℝ] E) = A t := by
    let G : E → M := fun w => F (⟨gamma t, w⟩ : TangentBundle I M)
    have hG : ContMDiff 𝓘(ℝ, E) I ∞ G :=
      hF.comp (contMDiff_tangentFiber (I := I) (gamma t))
    have hGexp : G =ᶠ[𝓝 (0 : E)]
        (fun w : E => expMap (I := I) g (gamma t)
          (show TangentSpace I (gamma t) from w)) := by
      have hmem := (contMDiff_tangentFiber (I := I) (n := ∞)
        (gamma t)).continuous.continuousAt.eventually
          (hWopen.mem_nhds (hzeroW (gamma t) ⟨t, ht, rfl⟩))
      filter_upwards [hmem] with w hw
      exact (hexp (⟨gamma t, w⟩ : TangentBundle I M) hw).2
    let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
    have hGderiv : mfderiv 𝓘(ℝ, E) I G 0 = ContinuousLinearMap.id ℝ E := by
      rw [hGexp.mfderiv_eq]
      exact mfderiv_expMap_at_zero g (gamma t)
    let At : P →L[ℝ] E := A t
    have hlin : MDifferentiableAt 𝓘(ℝ, P) 𝓘(ℝ, E) At 0 :=
      At.differentiableAt.mdifferentiableAt
    have hcomp := mfderiv_comp (I := 𝓘(ℝ, P)) (I' := 𝓘(ℝ, E)) (I'' := I)
      (0 : P) (by simpa only [map_zero] using
        hG.contMDiffAt.mdifferentiableAt (by simp)) hlin
    change mfderiv 𝓘(ℝ, P) I (fun z => f (z, t)) 0 =
      (mfderiv 𝓘(ℝ, E) I G (At 0)).comp
        (mfderiv 𝓘(ℝ, P) 𝓘(ℝ, E) At 0) at hcomp
    rw [map_zero, hGderiv, mfderiv_eq_fderiv, At.fderiv] at hcomp
    refine hcomp.trans ?_
    ext z
    rfl
  refine ⟨f, U, hf, hUopen, hzeroU, hfzero, hjet, ?_, ?_⟩
  · intro t ht z
    change F (⟨gamma t, A t z⟩ : TangentBundle I M) = gamma t
    rw [ht, zero_apply]
    exact hFzero (gamma t)
  · intro z hz
    exact hexp (launch z) hz

end DifferentialGeometry.Geometry.Riemannian.Variation
