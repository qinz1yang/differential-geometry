import DifferentialGeometry.Topology.Manifold.RegularLevel.SublevelAtlasBridge
import DifferentialGeometry.Topology.VectorBundle.NormPreservingDisc

/-!
# Consumer of the model change: closed disc bundles with `𝓡∂ (m + 1)` charts

The native closed `R`-disc bundle of a smooth Riemannian vector bundle (`closedDiscBundleChartedSpace`,
model `morseModelWithCornersHalfSpace m`) is diffeomorphic, by the identity, to the same set with the
smooth boundary atlas of chapter 14 (`SmoothBoundaryAtlas.regularSublevel`, model `𝓡∂ (m + 1)`)
(`exists_closedDisc_regularSublevelAtlas_diffeomorph`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped ContDiff Topology Manifold
open DifferentialGeometry.Topology.Morse DifferentialGeometry.Manifold.RegularLevel

namespace DifferentialGeometry.Topology.VectorBundle

variable {EB F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [FiniteDimensional ℝ EB] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [IB.Boundaryless]
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V IB]
  [IsContMDiffRiemannianBundle IB ∞ F V]

/-- **Closed disc bundles in the chapter-14 model.** The identity of the closed `R`-disc bundle is a
diffeomorphism from its native regular-sublevel charts to the smooth boundary atlas charts. -/
theorem exists_closedDisc_regularSublevelAtlas_diffeomorph {m : ℕ}
    (hd : Module.finrank ℝ (EB × F) = m + 1) (R : ℝ) (hR : 0 < R) :
    letI := closedDiscBundleChartedSpace (IB := IB) (V := V) hd R hR
    letI := (DifferentialGeometry.Topology.SmoothBoundaryAtlas.regularSublevel
      (bundleRadiusBoundaryModel (IB := IB) hd) (n := m) finrank_morseModel
      (contMDiff_fiberRadiusSquared_boundaryModel (V := V) hd) (R ^ 2)
      (fun z hz => mfderiv_fiberRadiusSquared_boundaryModel_ne_zero hd hR z hz)).toChartedSpace
    ∃ Φ : Diffeomorph (morseModelWithCornersHalfSpace m) (𝓡∂ (m + 1))
      {z : TotalSpace F V // fiberRadiusSquared z ≤ R ^ 2}
      ({z | fiberRadiusSquared z ≤ R ^ 2} : Set (TotalSpace F V)) ∞,
      ∀ z, (Φ z).val = z.val :=
  exists_sublevel_diffeomorph_regularSublevelAtlas (bundleRadiusBoundaryModel (IB := IB) hd)
    (contMDiff_fiberRadiusSquared_boundaryModel hd)
    (fun z hz => mfderiv_fiberRadiusSquared_boundaryModel_ne_zero hd hR z hz)

end DifferentialGeometry.Topology.VectorBundle
