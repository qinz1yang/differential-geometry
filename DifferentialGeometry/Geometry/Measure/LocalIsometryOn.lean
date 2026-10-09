import DifferentialGeometry.Geometry.Measure.LocalIsometry

noncomputable section

open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure (riemannianVolumeMeasure)

namespace DifferentialGeometry.Geometry.Measure

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N] [SigmaCompactSpace N]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace N := borel N
private local instance : BorelSpace N := ⟨rfl⟩
private local instance (U : TopologicalSpace.Opens M) : MeasurableSpace U := borel U
private local instance (U : TopologicalSpace.Opens M) : BorelSpace U := ⟨rfl⟩

theorem riemannianVolumeMeasure_image_eq_of_injOn_local_isometry
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : M → N) (U : TopologicalSpace.Opens M)
    (hf : IsLocalDiffeomorphOn I J ∞ f U) (hinj : Set.InjOn f U)
    (hmetric : ∀ x ∈ U, ∀ v w : TangentSpace I x,
      g.inner x v w = h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w))
    {S : Set M} (hS : MeasurableSet S) (hSU : S ⊆ U) :
    riemannianVolumeMeasure I M g S = riemannianVolumeMeasure J N h (f '' S) := by
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (isSigmaCompact_of_isOpen I U.isOpen)
  let fU : U → N := fun x => f x
  have hfU : IsLocalDiffeomorph I J ∞ fU := isLocalDiffeomorph_restrict_open U hf
  have hinjU : Function.Injective fU := fun x y hxy =>
    Subtype.ext (hinj x.property y.property hxy)
  have hmetricU (x : U) (v w : TangentSpace I x) :
      (g.restrictOpen U).inner x v w =
        h.inner (fU x) (mfderiv I J fU x v) (mfderiv I J fU x w) := by
    have hd (z : TangentSpace I x) : mfderiv I J fU x z =
        mfderiv I J f (x : M) (mfderiv I I (Subtype.val : U → M) x z) :=
      mfderiv_comp_apply x ((hf x).mdifferentiableAt (by simp))
        (hasMFDerivAt_subtype_val (I := I) U x).mdifferentiableAt z
    rw [hd v, hd w]
    calc
      (g.restrictOpen U).inner x v w = g.inner (x : M)
          (mfderiv I I (Subtype.val : U → M) x v)
          (mfderiv I I (Subtype.val : U → M) x w) := by
        rw [mfderiv_subtype_val]
        rfl
      _ = _ := hmetric x x.property _ _
  have hSUmeas : MeasurableSet ((Subtype.val : U → M) ⁻¹' S) :=
    continuous_subtype_val.measurable hS
  have hvol := riemannianVolumeMeasure_image_eq_of_injective_local_isometry
    (g.restrictOpen U) h fU hfU hinjU hmetricU hSUmeas
  rw [riemannianVolumeMeasure_restrictOpen_preimage_of_subset g U hS hSU] at hvol
  have himage : fU '' ((Subtype.val : U → M) ⁻¹' S) = f '' S := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hSU hx⟩, hx, rfl⟩
  rwa [himage] at hvol

end DifferentialGeometry.Geometry.Measure
