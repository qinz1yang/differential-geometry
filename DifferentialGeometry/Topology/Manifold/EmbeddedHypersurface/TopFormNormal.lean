import DifferentialGeometry.Tensor.Alternating.NormalCovector
import DifferentialGeometry.Topology.Manifold.EmbeddedHypersurface.Tangent
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Topology.VectorBundle.ContinuousAlternatingMap

open Set Bundle Module DifferentialGeometry.Topology.Morse
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

private local instance sourceNormed (s : S) : NormedAddCommGroup (TangentSpace I s) :=
  inferInstanceAs (NormedAddCommGroup (MorseModel m))
private local instance sourceNormedSpace (s : S) : NormedSpace ℝ (TangentSpace I s) :=
  inferInstanceAs (NormedSpace ℝ (MorseModel m))
private local instance sourceFinite (s : S) : FiniteDimensional ℝ (TangentSpace I s) :=
  inferInstanceAs (FiniteDimensional ℝ (MorseModel m))
private local instance ambientNormed (y : M) : NormedAddCommGroup (TangentSpace J y) :=
  inferInstanceAs (NormedAddCommGroup (MorseModel (m + 1)))
private local instance ambientNormedSpace (y : M) : NormedSpace ℝ (TangentSpace J y) :=
  inferInstanceAs (NormedSpace ℝ (MorseModel (m + 1)))

variable (e : S → M)
  (η : ∀ s : S, TangentSpace I s [⋀^Fin m]→L[ℝ] ℝ)
  (Ω : ∀ y : M, TangentSpace J y [⋀^Fin (m + 1)]→L[ℝ] ℝ)

def topFormNormal (s : S) : TangentSpace J (e s) →L[ℝ] ℝ :=
  Poincare.ContinuousAlternatingMap.normalCovector
    (show finrank ℝ (TangentSpace I s) = m from by
      change finrank ℝ (MorseModel m) = m
      simp [MorseModel])
    (η s) (Ω (e s)) (mfderiv I J e s)

theorem topFormNormal_spec (s : S) (hη : η s ≠ 0)
    (v : TangentSpace J (e s)) (u : Fin m → TangentSpace I s) :
    Ω (e s) (Matrix.vecCons v ((mfderiv I J e s) ∘ u)) =
      topFormNormal I J e η Ω s v * η s u :=
  Poincare.ContinuousAlternatingMap.normalCovector_spec _ _ _ _ hη v u


theorem ker_topFormNormal [I.Boundaryless] [J.Boundaryless] {s : S}
    (he : Manifold.IsImmersionAt I J ∞ e s) (hη : η s ≠ 0) (hΩ : Ω (e s) ≠ 0) :
    (topFormNormal I J e η Ω s).ker = (mfderiv I J e s).range :=
  Poincare.ContinuousAlternatingMap.ker_normalCovector _ _ _ _ hη
    (by change finrank ℝ (MorseModel (m + 1)) = m + 1; simp [MorseModel]) hΩ
    (injective_mfderiv_of_isImmersionAt I J he)


theorem topFormNormal_ne_zero [I.Boundaryless] [J.Boundaryless] {s : S}
    (he : Manifold.IsImmersionAt I J ∞ e s) (hη : η s ≠ 0) (hΩ : Ω (e s) ≠ 0) :
    topFormNormal I J e η Ω s ≠ 0 :=
  Poincare.ContinuousAlternatingMap.normalCovector_ne_zero _ _ _ _ hη
    (by change finrank ℝ (MorseModel (m + 1)) = m + 1; simp [MorseModel]) hΩ
    (injective_mfderiv_of_isImmersionAt I J he)

theorem continuousAt_topFormNormal [IsManifold I 1 S] [IsManifold J 1 M] {x : S}
    (he : ContMDiffAt I J 1 e x)
    (hη : ContinuousAt (fun s => TotalSpace.mk'
      (MorseModel m [⋀^Fin m]→L[ℝ] ℝ) s (η s)) x)
    (hΩ : ContinuousAt (fun y => TotalSpace.mk'
      (MorseModel (m + 1) [⋀^Fin (m + 1)]→L[ℝ] ℝ) y (Ω y)) (e x))
    (hηx : η x ≠ 0) :
    ContinuousAt (fun s => TotalSpace.mk' (MorseModel (m + 1) →L[ℝ] ℝ)
      (E := fun y : M => TangentSpace J y →L[ℝ] ℝ) (e s) (topFormNormal I J e η Ω s)) x := by
  let ηc := fun s : S => ContinuousAlternatingMap.inCoordinates (MorseModel m) ℝ
    (E₁ := TangentSpace I (M := S)) (E₂ := Bundle.Trivial S ℝ) x s x s (η s)
  let Ωc := fun s : S => ContinuousAlternatingMap.inCoordinates (MorseModel (m + 1)) ℝ
    (E₁ := TangentSpace J (M := M)) (E₂ := Bundle.Trivial M ℝ) (e x) (e s) (e x) (e s) (Ω (e s))
  let Dc := inTangentCoordinates I J id e (mfderiv I J e) x
  have hηc : ContinuousAt ηc x :=
    (continuousAt_continuousAlternatingMap_bundle _).mp hη |>.2
  have hΩc : ContinuousAt Ωc x :=
    (continuousAt_continuousAlternatingMap_bundle _).mp (hΩ.comp he.continuousAt) |>.2
  have hDc : ContinuousAt Dc x :=
    (he.mfderiv_const (m := 0) (by simp)).continuousAt
  let A := trivializationAt (MorseModel m) (TangentSpace I (M := S)) x
  let B := trivializationAt (MorseModel (m + 1)) (TangentSpace J (M := M)) (e x)
  have hxA : x ∈ A.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hxB : e x ∈ B.baseSet := FiberBundle.mem_baseSet_trivializationAt' (e x)
  have hηeq (s : S) (hs : s ∈ A.baseSet) :
      ηc s = (η s).compContinuousLinearMap
        (A.continuousLinearEquivAt ℝ s hs).symm.toContinuousLinearMap := by
    dsimp only [ηc]
    rw [ContinuousAlternatingMap.inCoordinates_eq (MorseModel m) ℝ
      (E₂ := Bundle.Trivial S ℝ) (y₀ := x) (y := s) hs (mem_univ s)]
    change ((ContinuousLinearEquiv.refl ℝ ℝ).toContinuousLinearMap.compContinuousAlternatingMap
      (η s)).compContinuousLinearMap _ = _
    rfl
  have hηcx : ηc x ≠ 0 := by
    rw [hηeq x hxA]
    intro hh
    apply hηx
    ext u
    have ht := congrArg (fun f : MorseModel m [⋀^Fin m]→L[ℝ] ℝ =>
      f ((A.continuousLinearEquivAt ℝ x hxA) ∘ u)) hh
    change η x (fun i => (A.continuousLinearEquivAt ℝ x hxA).symm
      ((A.continuousLinearEquivAt ℝ x hxA) (u i))) = 0 at ht
    simp only [ContinuousLinearEquiv.symm_apply_apply] at ht
    exact ht
  have hN := Poincare.ContinuousAlternatingMap.continuousAt_normalCovector
    (show finrank ℝ (MorseModel m) = m by simp [MorseModel]) hηc hΩc hDc hηcx
  apply (continuousAt_hom_bundle (RingHom.id ℝ) _).mpr
  refine ⟨he.continuousAt, ?_⟩
  apply hN.congr_of_eventuallyEq
  filter_upwards [A.open_baseSet.mem_nhds hxA,
    he.continuousAt.preimage_mem_nhds (B.open_baseSet.mem_nhds hxB),
    hηc.eventually_ne hηcx] with s hsA hsB hsη
  have hΩeq : Ωc s = (Ω (e s)).compContinuousLinearMap
      (B.continuousLinearEquivAt ℝ (e s) hsB).symm.toContinuousLinearMap := by
    dsimp only [Ωc]
    rw [ContinuousAlternatingMap.inCoordinates_eq (MorseModel (m + 1)) ℝ
      (E₂ := Bundle.Trivial M ℝ) (y₀ := e x) (y := e s) hsB (mem_univ (e s))]
    change ((ContinuousLinearEquiv.refl ℝ ℝ).toContinuousLinearMap.compContinuousAlternatingMap
      (Ω (e s))).compContinuousLinearMap _ = _
    rfl
  have hDeq : Dc s = (B.continuousLinearEquivAt ℝ (e s) hsB).toContinuousLinearMap.comp
      ((mfderiv I J e s).comp
        (A.continuousLinearEquivAt ℝ s hsA).symm.toContinuousLinearMap) :=
    ContinuousLinearMap.inCoordinates_eq hsA hsB
  have hηs : η s ≠ 0 := by
    intro hz
    apply hsη
    rw [hηeq s hsA, hz]
    ext u
    rfl
  symm
  rw [hηeq s hsA, hΩeq, hDeq]
  have hcov := Poincare.ContinuousAlternatingMap.normalCovector_compContinuousLinearEquiv
    (show finrank ℝ (TangentSpace I s) = m by
      change finrank ℝ (MorseModel m) = m; simp [MorseModel])
    (η s) (Ω (e s)) (mfderiv I J e s) hηs
    (A.continuousLinearEquivAt ℝ s hsA).symm
    (B.continuousLinearEquivAt ℝ (e s) hsB).symm
  simp only [ContinuousLinearEquiv.symm_symm] at hcov
  rw [hcov]
  rw [ContinuousLinearMap.inCoordinates_eq
    (E' := Bundle.Trivial M ℝ) (y₀ := e x) (y := e s) hsB (mem_univ (e s))]
  change (topFormNormal I J e η Ω s).comp _ =
    (ContinuousLinearEquiv.refl ℝ ℝ).toContinuousLinearMap.comp
      ((topFormNormal I J e η Ω s).comp _)
  rfl

theorem continuous_topFormNormal [IsManifold I 1 S] [IsManifold J 1 M]
    (he : ContMDiff I J 1 e)
    (hη : Continuous (fun s => TotalSpace.mk'
      (MorseModel m [⋀^Fin m]→L[ℝ] ℝ) s (η s)))
    (hΩ : Continuous (fun y => TotalSpace.mk'
      (MorseModel (m + 1) [⋀^Fin (m + 1)]→L[ℝ] ℝ) y (Ω y)))
    (hη0 : ∀ s, η s ≠ 0) :
    Continuous (fun s => TotalSpace.mk' (MorseModel (m + 1) →L[ℝ] ℝ)
      (E := fun y : M => TangentSpace J y →L[ℝ] ℝ) (e s) (topFormNormal I J e η Ω s)) :=
  continuous_iff_continuousAt.mpr fun s =>
    continuousAt_topFormNormal I J e η Ω (he s) hη.continuousAt hΩ.continuousAt (hη0 s)

end Poincare.Manifold.EmbeddedHypersurface
