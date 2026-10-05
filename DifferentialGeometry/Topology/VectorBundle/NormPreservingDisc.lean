import DifferentialGeometry.Topology.VectorBundle.DiscRadiusDiffeomorph
import DifferentialGeometry.Topology.Manifold.RegularLevel.SublevelTransfer

/-!
# Norm-preserving bundle isomorphisms restrict to closed disc bundles (LFR51)

Frozen blueprint master207A, lemma `lem:collapse-oriented-finite-soul-types` (LFR51, lines
29309–29378): the bundle identifications "include closed disk bundles after matching the fiber
norms" and "preserve unit disks and sphere boundaries". Foundations review §1.2 asks for the
"norm-preserving disk-bundle isomorphism".

For two smooth Riemannian vector bundles of the same total dimension `m + 1` and a smooth
diffeomorphism `Φ` of their total spaces with `‖(Φ z).2‖ = ‖z.2‖`, `Φ` restricts to a diffeomorphism
of the closed `R`-disc bundles with their native boundary charts (`normClosedDiscBundleChartedSpace`)
and maps boundary points to boundary points (`exists_normClosedDisc_diffeomorph_of_norm_eq`). The
squared-radius form on the regular sublevels of `fiberRadiusSquared` is
`exists_closedDisc_diffeomorph_of_norm_eq`.
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
  {EB' F' : Type*} [NormedAddCommGroup EB'] [NormedSpace ℝ EB']
  [FiniteDimensional ℝ EB'] [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [FiniteDimensional ℝ F'] {HB' : Type*} [TopologicalSpace HB']
  {IB' : ModelWithCorners ℝ EB' HB'} [IB'.Boundaryless]
  {B' : Type*} [TopologicalSpace B'] [ChartedSpace HB' B'] [IsManifold IB' ∞ B']
  {V' : B' → Type*} [TopologicalSpace (TotalSpace F' V')]
  [∀ b, NormedAddCommGroup (V' b)] [∀ b, InnerProductSpace ℝ (V' b)]
  [FiberBundle F' V'] [VectorBundle ℝ F' V'] [ContMDiffVectorBundle ∞ F' V' IB']
  [IsContMDiffRiemannianBundle IB' ∞ F' V']

omit [IB.Boundaryless] [IsManifold IB ∞ B] [ContMDiffVectorBundle ∞ F V IB] in
/-- The squared fibre radius is smooth for the boundary model of the closed disc bundle. -/
theorem contMDiff_fiberRadiusSquared_boundaryModel {m : ℕ}
    (hd : Module.finrank ℝ (EB × F) = m + 1) :
    ContMDiff (bundleRadiusBoundaryModel (IB := IB) hd) 𝓘(ℝ, ℝ) ∞
      (fiberRadiusSquared (F := F) (V := V)) :=
  (bundleRadiusBoundaryEquiv hd).contMDiff_transContinuousLinearEquiv_left.mpr
    contMDiff_fiberRadiusSquared

omit [IB.Boundaryless] [IsManifold IB ∞ B] [ContMDiffVectorBundle ∞ F V IB] in
/-- Positive levels of the squared fibre radius are regular for the boundary model. -/
theorem mfderiv_fiberRadiusSquared_boundaryModel_ne_zero {m : ℕ}
    (hd : Module.finrank ℝ (EB × F) = m + 1) {R : ℝ} (hR : 0 < R) (z : TotalSpace F V)
    (hz : fiberRadiusSquared z = R ^ 2) :
    mfderiv (bundleRadiusBoundaryModel (IB := IB) hd) 𝓘(ℝ, ℝ)
      (fiberRadiusSquared (F := F) (V := V)) z ≠ 0 := by
  intro hzero
  apply mfderiv_fiberRadiusSquared_level_ne_zero (IB := IB) hR z hz
  exact (isCriticalPointAt_transContinuousLinearEquiv_iff (IB.prod 𝓘(ℝ, F))
    (bundleRadiusBoundaryEquiv hd) (fiberRadiusSquared (F := F) (V := V)) z).mp hzero

/-- **LFR51, squared-radius form.** A norm-preserving smooth diffeomorphism of total spaces
restricts to a diffeomorphism of the closed `R`-disc bundles `{fiberRadiusSquared ≤ R²}` with their
regular-sublevel structures. -/
theorem exists_closedDisc_diffeomorph_of_norm_eq {m : ℕ}
    (hd : Module.finrank ℝ (EB × F) = m + 1) (hd' : Module.finrank ℝ (EB' × F') = m + 1)
    (Φ : Diffeomorph (IB.prod 𝓘(ℝ, F)) (IB'.prod 𝓘(ℝ, F')) (TotalSpace F V)
      (TotalSpace F' V') ∞)
    (hΦ : ∀ z, ‖(Φ z).2‖ = ‖z.2‖) (R : ℝ) (hR : 0 < R) :
    letI := closedDiscBundleChartedSpace (IB := IB) (V := V) hd R hR
    letI := closedDiscBundleChartedSpace (IB := IB') (V := V') hd' R hR
    ∃ Ψ : Diffeomorph (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m)
      {z : TotalSpace F V // fiberRadiusSquared z ≤ R ^ 2}
      {z : TotalSpace F' V' // fiberRadiusSquared z ≤ R ^ 2} ∞,
      ∀ z, (Ψ z).val = Φ z.val := by
  have hsq : ∀ z, fiberRadiusSquared (Φ z) = fiberRadiusSquared z := by
    intro z
    simp only [fiberRadiusSquared, real_inner_self_eq_norm_sq, hΦ]
  have hfwd : ContMDiff (bundleRadiusBoundaryModel (IB := IB) hd)
      (bundleRadiusBoundaryModel (IB := IB') hd') ∞ Φ :=
    (bundleRadiusBoundaryEquiv hd).contMDiff_transContinuousLinearEquiv_left.mpr
      ((bundleRadiusBoundaryEquiv hd').contMDiff_transContinuousLinearEquiv_right.mpr
        Φ.contMDiff)
  have hbwd : ContMDiff (bundleRadiusBoundaryModel (IB := IB') hd')
      (bundleRadiusBoundaryModel (IB := IB) hd) ∞ Φ.symm :=
    (bundleRadiusBoundaryEquiv hd').contMDiff_transContinuousLinearEquiv_left.mpr
      ((bundleRadiusBoundaryEquiv hd).contMDiff_transContinuousLinearEquiv_right.mpr
        Φ.symm.contMDiff)
  exact exists_sublevel_diffeomorph_of_contMDiffOn
    (bundleRadiusBoundaryModel (IB := IB) hd) (bundleRadiusBoundaryModel (IB := IB') hd')
    (contMDiff_fiberRadiusSquared_boundaryModel hd)
    (fun z hz => mfderiv_fiberRadiusSquared_boundaryModel_ne_zero hd hR z hz)
    (contMDiff_fiberRadiusSquared_boundaryModel hd')
    (fun z hz => mfderiv_fiberRadiusSquared_boundaryModel_ne_zero hd' hR z hz)
    isOpen_univ isOpen_univ (subset_univ _) (subset_univ _) hfwd.contMDiffOn hbwd.contMDiffOn
    (fun z hz => by rwa [hsq])
    (fun y hy => by rwa [← hsq, Φ.apply_symm_apply])
    (fun z _ => Φ.symm_apply_apply z) (fun y _ => Φ.apply_symm_apply y)

/-- **LFR51, norm-preserving disk-bundle isomorphism.** A smooth diffeomorphism of total spaces
with `‖(Φ z).2‖ = ‖z.2‖` restricts to a diffeomorphism of the closed `R`-disc bundles
`{‖z.2‖ ≤ R}` with their native boundary charts; it is `Φ` on points and maps the boundary sphere
bundle onto the boundary sphere bundle. -/
theorem exists_normClosedDisc_diffeomorph_of_norm_eq {m : ℕ}
    (hd : Module.finrank ℝ (EB × F) = m + 1) (hd' : Module.finrank ℝ (EB' × F') = m + 1)
    (Φ : Diffeomorph (IB.prod 𝓘(ℝ, F)) (IB'.prod 𝓘(ℝ, F')) (TotalSpace F V)
      (TotalSpace F' V') ∞)
    (hΦ : ∀ z, ‖(Φ z).2‖ = ‖z.2‖) (R : ℝ) (hR : 0 < R) :
    letI := normClosedDiscBundleChartedSpace (IB := IB) (V := V) hd R hR
    letI := normClosedDiscBundleChartedSpace (IB := IB') (V := V') hd' R hR
    ∃ Ψ : Diffeomorph (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m)
      {z : TotalSpace F V // ‖z.2‖ ≤ R} {z : TotalSpace F' V' // ‖z.2‖ ≤ R} ∞,
      (∀ z, (Ψ z).val = Φ z.val) ∧
      ∀ z, ((morseModelWithCornersHalfSpace m).IsBoundaryPoint (Ψ z) ↔
        (morseModelWithCornersHalfSpace m).IsBoundaryPoint z) := by
  let := closedDiscBundleChartedSpace (IB := IB) (V := V) hd R hR
  let := closedDiscBundleChartedSpace (IB := IB') (V := V') hd' R hR
  let := closedDiscBundle_isManifold (IB := IB) (V := V) hd R hR
  let := closedDiscBundle_isManifold (IB := IB') (V := V') hd' R hR
  obtain ⟨Ψ₀, hΨ₀⟩ := exists_closedDisc_diffeomorph_of_norm_eq hd hd' Φ hΦ R hR
  let e₁ := normClosedDiscSublevelHomeomorph (F := F) (V := V) R hR
  let e₂ := normClosedDiscSublevelHomeomorph (F := F') (V := V') R hR
  let := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (H := MorseHalfSpace m) e₁
  let := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (H := MorseHalfSpace m) e₂
  let D₁ := DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
    (I := morseModelWithCornersHalfSpace m) (n := ∞) e₁
  let D₂ := DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
    (I := morseModelWithCornersHalfSpace m) (n := ∞) e₂
  let Ψ := (D₁.trans Ψ₀).trans D₂.symm
  have hval : ∀ z, (Ψ z).val = Φ z.val := fun z => hΨ₀ (e₁ z)
  refine ⟨Ψ, hval, fun z => ?_⟩
  refine (normClosedDiscBundle_boundary_iff (IB := IB') hd' R hR (Ψ z)).trans ?_
  refine Iff.trans ?_ (normClosedDiscBundle_boundary_iff (IB := IB) hd R hR z).symm
  rw [hval, hΦ]

end DifferentialGeometry.Topology.VectorBundle
