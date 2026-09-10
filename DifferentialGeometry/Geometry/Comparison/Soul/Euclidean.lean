import Batteries.Tactic.Alias
import DifferentialGeometry.Bundle.TangentSpace
import DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.Riemannian
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Geometry.Manifold.Diffeomorph
import DifferentialGeometry.Geometry.Comparison.Soul.Point
import DifferentialGeometry.Geometry.Submanifold.NormalBundle.Point
import DifferentialGeometry.Geometry.Comparison.Soul.CheegerGromoll

set_option autoImplicit false

noncomputable section

open Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]

omit [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)] in
theorem diffeomorphic_euclidean_of_tangentSpace_diffeomorph
    (p : M)
    (Phi : TangentSpace I p ≃ₘ⟮𝓘(ℝ, TangentSpace I p), I⟯ M) :
    Nonempty
      (M ≃ₘ⟮I,
        𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))⟯
        EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) := by
  let e : TangentSpace I p ≃L[ℝ]
      EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (tangentSpaceModelContinuousLinearEquiv (I := I) p).trans
      (toEuclidean (E := E))
  exact ⟨Phi.symm.trans e.toDiffeomorph⟩

omit [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)] in
theorem diffeomorphic_euclidean_three_of_tangentSpace_diffeomorph
    (p : M) (hdim : Module.finrank ℝ E = 3)
    (Phi : TangentSpace I p ≃ₘ⟮𝓘(ℝ, TangentSpace I p), I⟯ M) :
    Nonempty
      (M ≃ₘ⟮I, 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))⟯
        EuclideanSpace ℝ (Fin 3)) := by
  obtain ⟨e⟩ :=
    diffeomorphic_euclidean_of_tangentSpace_diffeomorph (I := I) p Phi
  rw [hdim] at e
  exact ⟨e⟩

end DifferentialGeometry.Geometry

namespace DifferentialGeometry.Geometry

section PointNormalBundle

variable {EN HN N E H M F : Type*}
  [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
  [TopologicalSpace N] [ChartedSpace HN N] [IsManifold IN ∞ N] [Subsingleton N]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem IsRiemannianIsometricImmersion.diffeomorphic_euclidean_of_normalBundle_diffeomorph
    {gN : SmoothRiemannianMetric IN N} {gM : SmoothRiemannianMetric I M}
    {iota : N → M} (h : IsRiemannianIsometricImmersion gN gM iota)
    [TopologicalSpace (Bundle.TotalSpace F (fun x ↦ h.normalSpaceAt x))]
    [FiberBundle F (fun x ↦ h.normalSpaceAt x)]
    [VectorBundle ℝ F (fun x ↦ h.normalSpaceAt x)] (x0 : N)
    (Phi : Bundle.TotalSpace F (fun x ↦ h.normalSpaceAt x)
      ≃ₘ⟮IN.prod 𝓘(ℝ, F), I⟯ M) :
    Nonempty
      (M ≃ₘ⟮I, 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))⟯
        EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
  diffeomorphic_euclidean_of_tangentSpace_diffeomorph (iota x0)
    ((h.normalBundleDiffeomorphTangentSpaceAt F x0).symm.trans Phi)

end PointNormalBundle

section ConditionalSoulAssembly

variable {EN HN N E H M : Type*}
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN} [IN.Boundaryless]
  [TopologicalSpace N] [ChartedSpace HN N] [IsManifold IN ∞ N]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
  [T2Space (TangentBundle I M)]

theorem GeodesicPreservingSoul.range_eq_singleton_and_diffeomorphic_euclidean
    [ConnectedSpace M] [NoncompactSpace M]
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (soul : GeodesicPreservingSoul gN gM iota)
    (hcomplete : RiemannianMetricComplete (I := I) gM)
    (hsec : hasPositiveSectionalCurvature (I := I) gM)
    (hdimM : 2 ≤ Module.finrank ℝ E) (x0 : N)
    (Phi : TangentSpace I (iota x0) ≃ₘ⟮𝓘(ℝ, TangentSpace I (iota x0)), I⟯ M)
    (hzero : Phi 0 = iota x0) :
    Set.range iota = {Phi 0} ∧
      Nonempty
        (M ≃ₘ⟮I,
          𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))⟯
          EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) := by
  let _ : Nonempty N := ⟨x0⟩
  have hsource : Subsingleton N := soul.subsingleton hcomplete hsec hdimM
  have hrange : Set.range iota = {iota x0} :=
    Set.range_eq_singleton (fun x ↦ congrArg iota (hsource.elim x x0))
  refine ⟨?_, diffeomorphic_euclidean_of_tangentSpace_diffeomorph
    (I := I) (iota x0) Phi⟩
  simpa only [hzero] using hrange

theorem GeodesicPreservingSoul.range_eq_singleton_and_diffeomorphic_euclidean_three
    [ConnectedSpace M] [NoncompactSpace M]
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (soul : GeodesicPreservingSoul gN gM iota)
    (hcomplete : RiemannianMetricComplete (I := I) gM)
    (hsec : hasPositiveSectionalCurvature (I := I) gM)
    (hdimM : Module.finrank ℝ E = 3) (x0 : N)
    (Phi : TangentSpace I (iota x0) ≃ₘ⟮𝓘(ℝ, TangentSpace I (iota x0)), I⟯ M)
    (hzero : Phi 0 = iota x0) :
    Set.range iota = {Phi 0} ∧
      Nonempty
        (M ≃ₘ⟮I, 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))⟯
          EuclideanSpace ℝ (Fin 3)) := by
  let _ : Nonempty N := ⟨x0⟩
  have hdimTwo : 2 ≤ Module.finrank ℝ E := by omega
  have hsource : Subsingleton N := soul.subsingleton hcomplete hsec hdimTwo
  have hrange : Set.range iota = {iota x0} :=
    Set.range_eq_singleton (fun x ↦ congrArg iota (hsource.elim x x0))
  refine ⟨?_, diffeomorphic_euclidean_three_of_tangentSpace_diffeomorph
    (I := I) (iota x0) hdimM Phi⟩
  simpa only [hzero] using hrange

theorem Soul.range_eq_singleton_and_diffeomorphic_euclidean
    [ConnectedSpace M] [NoncompactSpace M]
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (soul : Soul gN gM iota)
    (hcomplete : RiemannianMetricComplete (I := I) gM)
    (hsec : hasPositiveSectionalCurvature (I := I) gM)
    (hdimM : 2 ≤ Module.finrank ℝ E) (x0 : N)
    (Phi : TangentSpace I (iota x0) ≃ₘ⟮𝓘(ℝ, TangentSpace I (iota x0)), I⟯ M)
    (hzero : Phi 0 = iota x0) :
    Set.range iota = {Phi 0} ∧
      Nonempty
        (M ≃ₘ⟮I,
          𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))⟯
          EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) := by
  let _ : Nonempty N := ⟨x0⟩
  have hsource : Subsingleton N := soul.subsingleton hcomplete hsec hdimM
  have hrange : Set.range iota = {iota x0} :=
    Set.range_eq_singleton (fun x ↦ congrArg iota (hsource.elim x x0))
  refine ⟨?_, diffeomorphic_euclidean_of_tangentSpace_diffeomorph
    (I := I) (iota x0) Phi⟩
  simpa only [hzero] using hrange

theorem Soul.range_eq_singleton_and_diffeomorphic_euclidean_three
    [ConnectedSpace M] [NoncompactSpace M]
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (soul : Soul gN gM iota)
    (hcomplete : RiemannianMetricComplete (I := I) gM)
    (hsec : hasPositiveSectionalCurvature (I := I) gM)
    (hdimM : Module.finrank ℝ E = 3) (x0 : N)
    (Phi : TangentSpace I (iota x0) ≃ₘ⟮𝓘(ℝ, TangentSpace I (iota x0)), I⟯ M)
    (hzero : Phi 0 = iota x0) :
    Set.range iota = {Phi 0} ∧
      Nonempty
        (M ≃ₘ⟮I, 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))⟯
          EuclideanSpace ℝ (Fin 3)) := by
  let _ : Nonempty N := ⟨x0⟩
  have hdimTwo : 2 ≤ Module.finrank ℝ E := by omega
  have hsource : Subsingleton N := soul.subsingleton hcomplete hsec hdimTwo
  have hrange : Set.range iota = {iota x0} :=
    Set.range_eq_singleton (fun x ↦ congrArg iota (hsource.elim x x0))
  refine ⟨?_, diffeomorphic_euclidean_three_of_tangentSpace_diffeomorph
    (I := I) (iota x0) hdimM Phi⟩
  simpa only [hzero] using hrange

theorem Soul.range_eq_singleton_and_diffeomorphic_euclidean_of_normalBundle_diffeomorph
    [ConnectedSpace M] [NoncompactSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (soul : Soul gN gM iota)
    [TopologicalSpace (Bundle.TotalSpace F (fun x ↦ soul.isometricImmersion.normalSpaceAt x))]
    [FiberBundle F (fun x ↦ soul.isometricImmersion.normalSpaceAt x)]
    [VectorBundle ℝ F (fun x ↦ soul.isometricImmersion.normalSpaceAt x)]
    (hcomplete : RiemannianMetricComplete (I := I) gM)
    (hsec : hasPositiveSectionalCurvature (I := I) gM)
    (hdimM : 2 ≤ Module.finrank ℝ E) (x0 : N)
    (Phi : Bundle.TotalSpace F (fun x ↦ soul.isometricImmersion.normalSpaceAt x)
      ≃ₘ⟮IN.prod 𝓘(ℝ, F), I⟯ M)
    (hzero : ∀ x, Phi (Bundle.zeroSection F
      (fun y ↦ soul.isometricImmersion.normalSpaceAt y) x) = iota x) :
    Set.range iota = {Phi (Bundle.zeroSection F
      (fun y ↦ soul.isometricImmersion.normalSpaceAt y) x0)} ∧
      Nonempty
        (M ≃ₘ⟮I, 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))⟯
          EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) := by
  let _ : Subsingleton N := soul.subsingleton hcomplete hsec hdimM
  let _ : Nonempty N := ⟨x0⟩
  refine ⟨?_, soul.isometricImmersion.diffeomorphic_euclidean_of_normalBundle_diffeomorph x0 Phi⟩
  rw [hzero]
  exact Set.range_eq_singleton fun x ↦ congrArg iota (Subsingleton.elim x x0)

theorem Soul.range_eq_singleton_and_diffeomorphic_euclidean_three_of_normalBundle_diffeomorph
    [ConnectedSpace M] [NoncompactSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (soul : Soul gN gM iota)
    [TopologicalSpace (Bundle.TotalSpace F (fun x ↦ soul.isometricImmersion.normalSpaceAt x))]
    [FiberBundle F (fun x ↦ soul.isometricImmersion.normalSpaceAt x)]
    [VectorBundle ℝ F (fun x ↦ soul.isometricImmersion.normalSpaceAt x)]
    (hcomplete : RiemannianMetricComplete (I := I) gM)
    (hsec : hasPositiveSectionalCurvature (I := I) gM)
    (hdimM : Module.finrank ℝ E = 3) (x0 : N)
    (Phi : Bundle.TotalSpace F (fun x ↦ soul.isometricImmersion.normalSpaceAt x)
      ≃ₘ⟮IN.prod 𝓘(ℝ, F), I⟯ M)
    (hzero : ∀ x, Phi (Bundle.zeroSection F
      (fun y ↦ soul.isometricImmersion.normalSpaceAt y) x) = iota x) :
    Set.range iota = {Phi (Bundle.zeroSection F
      (fun y ↦ soul.isometricImmersion.normalSpaceAt y) x0)} ∧
      Nonempty (M ≃ₘ⟮I, 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))⟯ EuclideanSpace ℝ (Fin 3)) := by
  have hdimTwo : 2 ≤ Module.finrank ℝ E := by omega
  have h := soul.range_eq_singleton_and_diffeomorphic_euclidean_of_normalBundle_diffeomorph
    (E := E) (I := I) (IN := IN)
    hcomplete hsec hdimTwo x0 Phi hzero
  obtain ⟨hrange, ⟨e⟩⟩ := h
  rw [hdimM] at e
  exact ⟨hrange, ⟨e⟩⟩

end ConditionalSoulAssembly

section CheegerGromollConsequences

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
  [T2Space (TangentBundle I M)] [ConnectedSpace M] [NoncompactSpace M]
  {g : SmoothRiemannianMetric I M}

theorem exists_point_soul_and_tangentSpace_diffeomorph_of_cheegerGromoll
    (hCG : cheegerGromollSoulTheorem g)
    (hcomplete : RiemannianMetricComplete g)
    (hsec : hasPositiveSectionalCurvature g)
    (hdim : 2 ≤ Module.finrank ℝ E) :
    ∃ p : M, isSoul g {p} ∧
      ∃ Phi : TangentSpace I p ≃ₘ⟮𝓘(ℝ, TangentSpace I p), I⟯ M, Phi 0 = p := by
  obtain ⟨S, d, c, m, gS, soul, t, b, v, _, _, Phi, hzero⟩ :=
    hCG inferInstance inferInstance inferInstance hcomplete hsec.toNonnegative
  let _ := c
  let _ := m
  let F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E - d))
  let _ := t
  let _ := b
  let _ := v
  let _ : Subsingleton S := soul.subsingleton hcomplete hsec hdim
  let _ : Nonempty S := soul.nonempty
  obtain ⟨x⟩ := soul.nonempty
  have hS : isSoul g S := ⟨d, c, m, gS, soul⟩
  have hpoint : S = {(x : M)} := by
    simpa using (Set.range_eq_singleton
      (f := (Subtype.val : S → M)) (fun y ↦ congrArg Subtype.val (Subsingleton.elim y x)))
  refine ⟨x, hpoint ▸ hS,
    (soul.isometricImmersion.normalBundleDiffeomorphTangentSpaceAt F x).symm.trans Phi, ?_⟩
  change Phi ((soul.isometricImmersion.normalBundleDiffeomorphTangentSpaceAt F x).symm 0) = x
  exact (congrArg Phi
    (soul.isometricImmersion.normalBundleDiffeomorphTangentSpaceAt_symm_zero F x)).trans (hzero x)

theorem diffeomorphic_euclidean_of_cheegerGromoll
    (hCG : cheegerGromollSoulTheorem g)
    (hcomplete : RiemannianMetricComplete g)
    (hsec : hasPositiveSectionalCurvature g)
    (hdim : 2 ≤ Module.finrank ℝ E) :
    Nonempty (M ≃ₘ⟮I, 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))⟯
      EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) := by
  obtain ⟨p, _, Phi, _⟩ :=
    exists_point_soul_and_tangentSpace_diffeomorph_of_cheegerGromoll hCG hcomplete hsec hdim
  exact diffeomorphic_euclidean_of_tangentSpace_diffeomorph p Phi

theorem diffeomorphic_euclidean_three_of_cheegerGromoll
    (hCG : cheegerGromollSoulTheorem g)
    (hcomplete : RiemannianMetricComplete g)
    (hsec : hasPositiveSectionalCurvature g)
    (hdim : Module.finrank ℝ E = 3) :
    Nonempty (M ≃ₘ⟮I, 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))⟯ EuclideanSpace ℝ (Fin 3)) := by
  have hdimTwo : 2 ≤ Module.finrank ℝ E := by omega
  obtain ⟨e⟩ := diffeomorphic_euclidean_of_cheegerGromoll hCG hcomplete hsec hdimTwo
  rw [hdim] at e
  exact ⟨e⟩

end CheegerGromollConsequences

end DifferentialGeometry.Geometry

namespace Poincare.Geometry

alias diffeomorphic_euclidean_of_tangentSpace_diffeomorph := DifferentialGeometry.Geometry.diffeomorphic_euclidean_of_tangentSpace_diffeomorph
alias diffeomorphic_euclidean_three_of_tangentSpace_diffeomorph := DifferentialGeometry.Geometry.diffeomorphic_euclidean_three_of_tangentSpace_diffeomorph
end Poincare.Geometry

namespace Poincare.Geometry.IsRiemannianIsometricImmersion

alias diffeomorphic_euclidean_of_normalBundle_diffeomorph := DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.diffeomorphic_euclidean_of_normalBundle_diffeomorph
end Poincare.Geometry.IsRiemannianIsometricImmersion

namespace Poincare.Geometry.GeodesicPreservingSoulData

alias range_eq_singleton_and_diffeomorphic_euclidean := DifferentialGeometry.Geometry.GeodesicPreservingSoul.range_eq_singleton_and_diffeomorphic_euclidean
alias range_eq_singleton_and_diffeomorphic_euclidean_three := DifferentialGeometry.Geometry.GeodesicPreservingSoul.range_eq_singleton_and_diffeomorphic_euclidean_three
end Poincare.Geometry.GeodesicPreservingSoulData

namespace Poincare.Geometry.VanishingSecondFundamentalFormSoulData

alias range_eq_singleton_and_diffeomorphic_euclidean := DifferentialGeometry.Geometry.Soul.range_eq_singleton_and_diffeomorphic_euclidean
alias range_eq_singleton_and_diffeomorphic_euclidean_three := DifferentialGeometry.Geometry.Soul.range_eq_singleton_and_diffeomorphic_euclidean_three
alias range_eq_singleton_and_diffeomorphic_euclidean_of_normalBundle_diffeomorph := DifferentialGeometry.Geometry.Soul.range_eq_singleton_and_diffeomorphic_euclidean_of_normalBundle_diffeomorph
alias range_eq_singleton_and_diffeomorphic_euclidean_three_of_normalBundle_diffeomorph := DifferentialGeometry.Geometry.Soul.range_eq_singleton_and_diffeomorphic_euclidean_three_of_normalBundle_diffeomorph
end Poincare.Geometry.VanishingSecondFundamentalFormSoulData

namespace Poincare.Geometry

alias exists_point_soul_and_tangentSpace_diffeomorph_of_cheegerGromoll := DifferentialGeometry.Geometry.exists_point_soul_and_tangentSpace_diffeomorph_of_cheegerGromoll
alias diffeomorphic_euclidean_of_cheegerGromoll := DifferentialGeometry.Geometry.diffeomorphic_euclidean_of_cheegerGromoll
alias diffeomorphic_euclidean_three_of_cheegerGromoll := DifferentialGeometry.Geometry.diffeomorphic_euclidean_three_of_cheegerGromoll

end Poincare.Geometry
