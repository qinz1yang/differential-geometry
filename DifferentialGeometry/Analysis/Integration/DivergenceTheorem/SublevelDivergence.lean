import DifferentialGeometry.Topology.Morse.SublevelTangentSection
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.CovariantTrace
import DifferentialGeometry.Geometry.Boundary.SublevelMetric

namespace DifferentialGeometry.Topology.Morse

open Bundle Geometry.Operator Geometry.Curvature Integral.DivergenceTheorem
open scoped Manifold ContDiff

noncomputable section

variable {m : ℕ} {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ (MorseModel (m + 1)) H)
  [I.Boundaryless] [IsManifold I ∞ M]

private def strictSublevelOpen (f : M → ℝ) (a : ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    TopologicalSpace.Opens M := ⟨{x | f x < a}, isOpen_lt hf.continuous continuous_const⟩

private def sublevelInteriorOpen (f : M → ℝ) (a : ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    TopologicalSpace.Opens (SublevelSpace f a) :=
  ⟨{x | f x.1 < a}, isOpen_lt (hf.continuous.comp continuous_subtype_val) continuous_const⟩

private def strictSublevelDiffeomorph (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    letI := manifoldSublevelEuclideanChartedSpace I f a hf hreg
    sublevelInteriorOpen I f a hf ≃ₘ⟮modelWithCornersEuclideanHalfSpace (m + 1), I⟯
      strictSublevelOpen I f a hf := by
  let := manifoldSublevelChartedSpace I f a hf hreg
  let := manifoldSublevelEuclideanChartedSpace I f a hf hreg
  refine
    { toFun := fun x => ⟨x.1.1, x.2⟩
      invFun := fun y => ⟨⟨y.1, le_of_lt (show f y.1 < a from y.2)⟩, y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · apply (ContMDiff.subtypeVal_comp_iff (strictSublevelOpen I f a hf) _).mp
    exact (contMDiff_manifoldSublevelEuclideanInclusion I f a hf hreg).comp contMDiff_subtype_val
  · apply (ContMDiff.subtypeVal_comp_iff (sublevelInteriorOpen I f a hf) _).mp
    have hs := contMDiff_sublevelCorestrict I f a hf hreg
      (Subtype.val : strictSublevelOpen I f a hf → M) contMDiff_subtype_val
      (fun x => le_of_lt (show f x.1 < a from x.2))
    exact (manifoldSublevelEuclideanDiffeomorph I f a hf hreg).contMDiff.comp hs

private theorem mfderiv_strictSublevelDiffeomorph (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    letI := manifoldSublevelEuclideanChartedSpace I f a hf hreg
    ∀ x : sublevelInteriorOpen I f a hf,
      mfderiv (modelWithCornersEuclideanHalfSpace (m + 1)) I
        (strictSublevelDiffeomorph I f a hf hreg) x =
      mfderiv (modelWithCornersEuclideanHalfSpace (m + 1)) I
        (Subtype.val : SublevelSpace f a → M) x.1 := by
  let := manifoldSublevelEuclideanChartedSpace I f a hf hreg
  intro x
  let Φ := strictSublevelDiffeomorph I f a hf hreg
  have hΦ := (Φ.contMDiff x).mdifferentiableAt (by simp)
  have hi := (contMDiff_manifoldSublevelEuclideanInclusion I f a hf hreg x.1).mdifferentiableAt (by simp)
  have hleft := mfderiv_comp x (hasMFDerivAt_subtype_val (strictSublevelOpen I f a hf) (Φ x)).mdifferentiableAt hΦ
  have hright := mfderiv_comp x hi (hasMFDerivAt_subtype_val (sublevelInteriorOpen I f a hf) x).mdifferentiableAt
  rw [mfderiv_subtype_val] at hleft hright
  change mfderiv (modelWithCornersEuclideanHalfSpace (m + 1)) I
    (fun x : sublevelInteriorOpen I f a hf => x.1.1) x = _ at hleft hright
  have hc := hleft.symm.trans hright
  change (ContinuousLinearMap.id ℝ (MorseModel (m + 1))).comp
    (mfderiv (modelWithCornersEuclideanHalfSpace (m + 1)) I Φ x) =
    (mfderiv (modelWithCornersEuclideanHalfSpace (m + 1)) I
      (Subtype.val : SublevelSpace f a → M) x.1).comp
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (m + 1)))) at hc
  ext v
  exact congrArg (fun L => L v) hc

private theorem sublevelMetric_restrictInterior_eq_pullback [T2Space M]
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    letI := manifoldSublevelEuclideanChartedSpace I f a hf hreg
    letI := manifoldSublevelEuclidean_isManifold I f a hf hreg
    (sublevelMetric I g f a hf hreg).restrictOpen (sublevelInteriorOpen I f a hf) =
      Diffeomorph.pullbackMetricCross (g.restrictOpen (strictSublevelOpen I f a hf))
        (strictSublevelDiffeomorph I f a hf hreg) := by
  let := manifoldSublevelEuclideanChartedSpace I f a hf hreg
  let := manifoldSublevelEuclidean_isManifold I f a hf hreg
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [SmoothRiemannianMetric.restrictOpen_inner, Diffeomorph.pullbackMetricCross_inner,
    SmoothRiemannianMetric.restrictOpen_inner]
  change g.inner x.1.1
    (mfderiv (modelWithCornersEuclideanHalfSpace (m + 1)) I
      (Subtype.val : SublevelSpace f a → M) x.1 v)
    (mfderiv (modelWithCornersEuclideanHalfSpace (m + 1)) I
      (Subtype.val : SublevelSpace f a → M) x.1 w) = _
  rw [mfderiv_strictSublevelDiffeomorph]
  rfl

private theorem divergence_sublevelTangentSection_of_lt [T2Space M]
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    (X : Cₛ^∞⟮I; MorseModel (m + 1), (TangentSpace I : M → Type)⟯) :
    letI := manifoldSublevelEuclideanChartedSpace I f a hf hreg
    letI := manifoldSublevelEuclidean_isManifold I f a hf hreg
    ∀ x : SublevelSpace f a, f x.1 < a →
      WithBoundary.divergenceGWithBoundary (sublevelMetric I g f a hf hreg)
        (sublevelTangentSection I f a hf hreg X) x = WithBoundary.divergenceGWithBoundary g X x.1 := by
  let := manifoldSublevelEuclideanChartedSpace I f a hf hreg
  let := manifoldSublevelEuclidean_isManifold I f a hf hreg
  intro x hx
  let U := strictSublevelOpen I f a hf
  let V := sublevelInteriorOpen I f a hf
  let Φ := strictSublevelDiffeomorph I f a hf hreg
  let Xs := sublevelTangentSection I f a hf hreg X
  let XV := restrictOpenTangentSection V Xs
  let XU := restrictOpenTangentSection U X
  let y : V := ⟨x, hx⟩
  have hX : pushFwdSectionCross Φ XV = XU := by
    apply DFunLike.ext
    intro z
    obtain ⟨w, rfl⟩ := Φ.surjective z
    change pushFwdSectionCross Φ XV (Φ w) = XU (Φ w)
    rw [pushFwdSectionCross_apply_at_image]
    change mfderiv (modelWithCornersEuclideanHalfSpace (m + 1)) I Φ w
      (XV w) = XU (Φ w)
    rw [mfderiv_strictSublevelDiffeomorph]
    dsimp only [XV, XU]
    rw [restrictOpenTangentSection_apply, restrictOpenTangentSection_apply]
    change mfderiv (modelWithCornersEuclideanHalfSpace (m + 1)) I
      (Subtype.val : SublevelSpace f a → M) w.1 (Xs w.1) = X w.1.1
    exact mfderiv_sublevelTangentSection I f a hf hreg X w.1
  have hleft := WithBoundary.divergence_g_with_boundary_restrictOpen (sublevelMetric I g f a hf hreg) V Xs y
  have hright := WithBoundary.divergence_g_with_boundary_restrictOpen g U X (Φ y)
  have hmid := WithBoundary.divergence_g_with_boundary_pullbackCross (g.restrictOpen U) Φ XV y
  rw [hX, ← sublevelMetric_restrictInterior_eq_pullback I g f a hf hreg] at hmid
  exact hleft.symm.trans (hmid.trans hright)

theorem divergence_sublevelTangentSection [T2Space M]
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    (X : Cₛ^∞⟮I; MorseModel (m + 1), (TangentSpace I : M → Type)⟯) :
    letI := manifoldSublevelEuclideanChartedSpace I f a hf hreg
    letI := manifoldSublevelEuclidean_isManifold I f a hf hreg
    ∀ x : SublevelSpace f a,
      WithBoundary.divergenceGWithBoundary (sublevelMetric I g f a hf hreg)
        (sublevelTangentSection I f a hf hreg X) x = WithBoundary.divergenceGWithBoundary g X x.1 := by
  let := manifoldSublevelEuclideanChartedSpace I f a hf hreg
  let := manifoldSublevelEuclidean_isManifold I f a hf hreg
  intro x
  have hleft := (WithBoundary.divergence_g_with_boundary_contMDiff (sublevelMetric I g f a hf hreg)
    (sublevelTangentSection I f a hf hreg X)).continuous.continuousAt (x := x)
  have hright := ((WithBoundary.divergence_g_with_boundary_contMDiff g X).continuous.comp
    continuous_subtype_val).continuousAt (x := x)
  by_contra hne
  have hev := (hleft.sub hright).eventually_ne (sub_ne_zero.mpr hne)
  obtain ⟨y, hy, hyint⟩ := mem_closure_iff_nhds.mp
    ((modelWithCornersEuclideanHalfSpace (m + 1)).dense_interior (M := SublevelSpace f a) x) _ hev
  apply hy
  apply sub_eq_zero.mpr
  exact divergence_sublevelTangentSection_of_lt I g f a hf hreg X y
    ((manifoldSublevelEuclidean_isInteriorPoint_iff I f a hf hreg y).mp hyint)

end

end DifferentialGeometry.Topology.Morse
