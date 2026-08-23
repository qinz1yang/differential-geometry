import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.DiffeomorphismFamily.ManifoldIntegralFlow
import DifferentialGeometry.Bundle.VectorFieldPushforward
import Mathlib.Geometry.Manifold.LocalDiffeomorph


namespace DifferentialGeometry.Analysis.ODE

open Set Function Bundle
open scoped Manifold Topology ContDiff

section SpatialAtFixedTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [T2Space M]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M] in
theorem flowFamily_contMDiff_fixed_time
    (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)) (s : ℝ) :
    ContMDiff I I ∞ (Φ_fam s : M → M) :=
  (Φ_fam s).contMDiff

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M] in
theorem flowFamily_mdifferentiableAt_fixed_time
    (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)) (s : ℝ) (x : M) :
    MDifferentiableAt I I (Φ_fam s : M → M) x := by
  have hinfty : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  exact (Φ_fam s).mdifferentiable hinfty x

end SpatialAtFixedTime

section Pushforward

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem flowFamily_pushforward_contMDiff
    (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)) (s : ℝ)
    {Y : ∀ x : M, TangentSpace I x}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x (Y x))) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x
        (DifferentialGeometry.Diffeomorph.pushforward (Φ_fam s) Y x)) := by
  exact Diffeomorph.pushforward_contMDiff (I := I) (Φ_fam s) hY

end Pushforward

section TimeRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [T2Space M] [CompactSpace M] [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M]
    [CompactSpace M] [SigmaCompactSpace M] in
theorem flowFamily_hasMFDerivWithinAt_time
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hbare : ∀ s : ℝ, 0 < s → s < T → ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ_fam u x) (Ici 0) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X s (Φ_fam s x))))
    (s : ℝ) (hs : 0 < s) (hsT : s < T) (x : M) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ_fam u x) (Ici 0) s
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X s (Φ_fam s x))) :=
  hbare s hs hsT x

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M]
    [CompactSpace M] [SigmaCompactSpace M] in
theorem flowFamily_continuousWithinAt_time
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hbare : ∀ s : ℝ, 0 < s → s < T → ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ_fam u x) (Ici 0) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X s (Φ_fam s x))))
    (s : ℝ) (hs : 0 < s) (hsT : s < T) (x : M) :
    ContinuousWithinAt (fun u : ℝ => Φ_fam u x) (Ici 0) s :=
  (hbare s hs hsT x).continuousWithinAt

end TimeRegularity

section RegularityPackage

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [CompactSpace M]


omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem flowFamily_regularity_package
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hbare : ∀ s : ℝ, 0 < s → s < T → ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ_fam u x) (Ici 0) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X s (Φ_fam s x)))) :
    (∀ s : ℝ, ContMDiff I I ∞ (Φ_fam s : M → M)) ∧
    (∀ (s : ℝ) (Y : ∀ x : M, TangentSpace I x),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x (Y x)) →
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x
          (DifferentialGeometry.Diffeomorph.pushforward (Φ_fam s) Y x))) ∧
    (∀ (s : ℝ) (x : M), MDifferentiableAt I I (Φ_fam s : M → M) x) ∧
    (∀ s : ℝ, 0 < s → s < T → ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ_fam u x) (Ici 0) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X s (Φ_fam s x)))) ∧
    (∀ s : ℝ, 0 < s → s < T → ∀ x : M,
      ContinuousWithinAt (fun u : ℝ => Φ_fam u x) (Ici 0) s) :=
  ⟨fun s => flowFamily_contMDiff_fixed_time Φ_fam s,
   fun s _Y hY => flowFamily_pushforward_contMDiff Φ_fam s hY,
   fun s x => flowFamily_mdifferentiableAt_fixed_time Φ_fam s x,
   hbare,
   fun s hs hsT x => (hbare s hs hsT x).continuousWithinAt⟩

end RegularityPackage

end DifferentialGeometry.Analysis.ODE
