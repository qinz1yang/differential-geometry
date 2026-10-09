import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import DifferentialGeometry.Topology.Manifold.AddCircle.Circle
import DifferentialGeometry.Topology.Manifold.AddCircle.SmoothEmbedding

/-!
# Arcs and loops from diffeomorphisms of `[0, 1]` and of the circle (lane B-BCF134; `K₃` kernel)

For a smooth manifold `M` modelled on `EuclideanHalfSpace 1` and a smooth injective map `ι : M → H`
into a normed space with injective differential (an injective immersion):

* `arc_*_BCF`: for a diffeomorphism `ψ : [0, 1] ≃ M`, `t ↦ ι (ψ (projIcc 0 1 t))` is smooth on
  `[0, 1]`, injective there, with nonzero derivative within `[0, 1]`;
* `loop_*_BCF`: for a diffeomorphism `ψ : Circle ≃ M`, `t ↦ ι (ψ (exp (2πit)))` (through
  `AddCircle.diffeomorphCircle`) is smooth, `1`-periodic, injective on `[0, 1)`, with nonzero
  derivative everywhere.
-/

set_option autoImplicit false

open Set Function Filter Topology
open scoped Manifold ContDiff

noncomputable section

namespace DifferentialGeometry.Topology

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M]

section Arc

variable (ι : M → H) (ψ : Icc (0 : ℝ) 1 ≃ₘ⟮𝓡∂ 1, 𝓡∂ 1⟯ M)

/-- The arc `t ↦ ι (ψ (projIcc 0 1 t))` is smooth on `[0, 1]`. -/
theorem arc_contDiffOn_BCF (hι : ContMDiff (𝓡∂ 1) 𝓘(ℝ, H) ∞ ι) :
    ContDiffOn ℝ ∞ (fun t => ι (ψ (projIcc 0 1 zero_le_one t))) (Icc 0 1) := by
  have hg : ContMDiff (𝓡∂ 1) 𝓘(ℝ, H) ∞ (ι ∘ ψ) := hι.comp ψ.contMDiff
  exact contMDiffOn_iff_contDiffOn.mp (contMDiffOn_comp_projIcc_iff.mpr hg)

omit [NormedAddCommGroup H] [NormedSpace ℝ H] in
/-- The arc is injective on `[0, 1]`. -/
theorem arc_injOn_BCF (hinj : Injective ι) :
    InjOn (fun t => ι (ψ (projIcc 0 1 zero_le_one t))) (Icc 0 1) := by
  intro s hs t ht hst
  have h := ψ.injective (hinj hst)
  rw [projIcc_of_mem _ hs, projIcc_of_mem _ ht] at h
  exact congrArg Subtype.val h

/-- The arc has nonzero derivative within `[0, 1]` at every point of `[0, 1]`. -/
theorem arc_derivWithin_ne_zero_BCF
    (hι : ContMDiff (𝓡∂ 1) 𝓘(ℝ, H) ∞ ι) (hd : ∀ x, Injective (mfderiv (𝓡∂ 1) 𝓘(ℝ, H) ι x))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    derivWithin (fun t => ι (ψ (projIcc 0 1 zero_le_one t))) (Icc 0 1) t ≠ 0 := by
  set w : Icc (0 : ℝ) 1 := ⟨t, ht⟩ with hw
  have key := mfderivWithin_comp_projIcc_one (I := 𝓘(ℝ, H)) (f := ι ∘ ψ) (w := w)
  rw [mfderivWithin_eq_fderivWithin] at key
  have hcomp : mfderiv (𝓡∂ 1) 𝓘(ℝ, H) (ι ∘ ψ) w =
      (mfderiv (𝓡∂ 1) 𝓘(ℝ, H) ι (ψ w)).comp (mfderiv (𝓡∂ 1) (𝓡∂ 1) ψ w) :=
    mfderiv_comp w ((hι (ψ w)).mdifferentiableAt (by simp))
      ((ψ.contMDiff w).mdifferentiableAt (by simp))
  have hone : (1 : TangentSpace (𝓡∂ 1) w) ≠ 0 := by
    intro h0
    have h1 := mfderiv_subtypeVal_Icc_one w
    rw [h0, map_zero] at h1
    exact (zero_ne_one : (0 : ℝ) ≠ 1) h1
  have hψ : Injective (mfderiv (𝓡∂ 1) (𝓡∂ 1) ψ w) := by
    obtain ⟨e, he⟩ := ψ.isInvertible_mfderiv (x := w) (by simp)
    rw [← he]
    exact e.injective
  intro h0
  change fderivWithin ℝ (fun t => ι (ψ (projIcc 0 1 zero_le_one t))) (Icc 0 1) t 1 = 0 at h0
  have h2 : mfderiv (𝓡∂ 1) 𝓘(ℝ, H) (ι ∘ ψ) w 1 = 0 := key.symm.trans h0
  rw [hcomp, ContinuousLinearMap.comp_apply] at h2
  exact hone (hψ ((hd (ψ w)) (h2.trans (map_zero _).symm) |>.trans (map_zero _).symm))

end Arc

section Loop

variable (ι : M → H) (ψ : Circle ≃ₘ⟮𝓡 1, 𝓡∂ 1⟯ M)

/-- The loop `t ↦ ι (ψ (exp (2πit)))`. -/
theorem loop_contDiff_BCF (hι : ContMDiff (𝓡∂ 1) 𝓘(ℝ, H) ∞ ι) :
    ContDiff ℝ ∞ (fun t : ℝ => ι (ψ (AddCircle.diffeomorphCircle (t : AddCircle (1 : ℝ))))) := by
  have hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, H) ∞ (ι ∘ ψ ∘ AddCircle.diffeomorphCircle) :=
    hι.comp (ψ.contMDiff.comp AddCircle.diffeomorphCircle.contMDiff)
  exact contMDiff_iff_contDiff.mp (hf.comp AddCircle.contMDiff_coe)

omit [NormedAddCommGroup H] [NormedSpace ℝ H] in
/-- The loop is `1`-periodic. -/
theorem loop_periodic_BCF :
    Periodic (fun t : ℝ => ι (ψ (AddCircle.diffeomorphCircle (t : AddCircle (1 : ℝ))))) 1 := by
  intro t
  simp only [AddCircle.coe_add_period]

omit [NormedAddCommGroup H] [NormedSpace ℝ H] in
/-- The loop is injective on `[0, 1)`. -/
theorem loop_injOn_BCF (hinj : Injective ι) :
    InjOn (fun t : ℝ => ι (ψ (AddCircle.diffeomorphCircle (t : AddCircle (1 : ℝ))))) (Ico 0 1) := by
  intro s hs t ht hst
  have h := AddCircle.diffeomorphCircle.injective (ψ.injective (hinj hst))
  have hs' : s ∈ Ico (0 : ℝ) (0 + 1) := by rwa [zero_add]
  have ht' : t ∈ Ico (0 : ℝ) (0 + 1) := by rwa [zero_add]
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico hs' ht').mp h

/-- The loop has nonzero derivative everywhere. -/
theorem loop_deriv_ne_zero_BCF
    (hι : ContMDiff (𝓡∂ 1) 𝓘(ℝ, H) ∞ ι) (hd : ∀ x, Injective (mfderiv (𝓡∂ 1) 𝓘(ℝ, H) ι x))
    (t : ℝ) :
    deriv (fun t : ℝ => ι (ψ (AddCircle.diffeomorphCircle (t : AddCircle (1 : ℝ))))) t ≠ 0 := by
  set z : AddCircle (1 : ℝ) := ((t : ℝ) : AddCircle (1 : ℝ))
  have hψ : ContMDiff (𝓡 1) 𝓘(ℝ, H) ∞ (ι ∘ ψ) := hι.comp ψ.contMDiff
  have hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, H) ∞ (ι ∘ ψ ∘ AddCircle.diffeomorphCircle) :=
    hι.comp (ψ.contMDiff.comp AddCircle.diffeomorphCircle.contMDiff)
  change deriv (fun t : ℝ => (ι ∘ ψ ∘ AddCircle.diffeomorphCircle) (t : AddCircle (1 : ℝ))) t ≠ 0
  rw [AddCircle.deriv_comp_coe ((hf z).mdifferentiableAt (by simp))]
  have hc1 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, H) (ι ∘ ψ ∘ AddCircle.diffeomorphCircle) z =
      (mfderiv (𝓡 1) 𝓘(ℝ, H) (ι ∘ ψ) (AddCircle.diffeomorphCircle z)).comp
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) AddCircle.diffeomorphCircle z) :=
    mfderiv_comp z ((hψ _).mdifferentiableAt (by simp))
      ((AddCircle.diffeomorphCircle.contMDiff z).mdifferentiableAt (by simp))
  have hc2 : mfderiv (𝓡 1) 𝓘(ℝ, H) (ι ∘ ψ) (AddCircle.diffeomorphCircle z) =
      (mfderiv (𝓡∂ 1) 𝓘(ℝ, H) ι (ψ (AddCircle.diffeomorphCircle z))).comp
        (mfderiv (𝓡 1) (𝓡∂ 1) ψ (AddCircle.diffeomorphCircle z)) :=
    mfderiv_comp _ ((hι _).mdifferentiableAt (by simp)) ((ψ.contMDiff _).mdifferentiableAt (by simp))
  have hinv1 : Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) AddCircle.diffeomorphCircle z) := by
    obtain ⟨e, he⟩ := AddCircle.diffeomorphCircle.isInvertible_mfderiv (x := z) (by simp)
    rw [← he]
    exact e.injective
  have hinv2 : Injective (mfderiv (𝓡 1) (𝓡∂ 1) ψ (AddCircle.diffeomorphCircle z)) := by
    obtain ⟨e, he⟩ := ψ.isInvertible_mfderiv (x := AddCircle.diffeomorphCircle z) (by simp)
    rw [← he]
    exact e.injective
  intro h0
  rw [hc1, ContinuousLinearMap.comp_apply, hc2, ContinuousLinearMap.comp_apply] at h0
  have h3 := hd _ (h0.trans (map_zero _).symm)
  have h4 := hinv2 (h3.trans (map_zero _).symm)
  have h5 := hinv1 (h4.trans (map_zero _).symm)
  exact AddCircle.parameterTangent_ne_zero z h5

end Loop

end DifferentialGeometry.Topology
