import DifferentialGeometry.Geometry.Collapse.SublevelCore.OpenDiskBundle
import DifferentialGeometry.Geometry.Collapse.SublevelCore.DiskCoreFlow
import DifferentialGeometry.Topology.Manifold.RegularLevel.Sublevel
import DifferentialGeometry.Topology.Morse.CriticalPoint
import DifferentialGeometry.Topology.Manifold.ModelWithCorners
import DifferentialGeometry.Topology.Manifold.Homeomorph.Transport
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-!
# Native smooth closed-disc bundles and radius change

The squared norm of the actual smooth Riemannian bundle has regular positive levels. The
regular-sublevel construction gives its closed discs genuine boundary charts. Positive radius
change acts on the original fibers and is smooth in both directions, including the boundary.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped ContDiff Topology
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

omit [FiniteDimensional ℝ EB] [FiniteDimensional ℝ F] [IB.Boundaryless]
  [IsManifold IB ∞ B] [ContMDiffVectorBundle ∞ F V IB]
  [IsContMDiffRiemannianBundle IB ∞ F V] in
def fiberRadiusSquared (z : TotalSpace F V) : ℝ := inner ℝ z.2 z.2

omit [FiniteDimensional ℝ EB] [FiniteDimensional ℝ F] [IB.Boundaryless]
  [IsManifold IB ∞ B] [ContMDiffVectorBundle ∞ F V IB] in
theorem contMDiff_fiberRadiusSquared :
    ContMDiff (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ, ℝ) ∞ (fiberRadiusSquared (F := F) (V := V)) :=
  contMDiff_id.inner_bundle contMDiff_id

omit [FiniteDimensional ℝ EB] [FiniteDimensional ℝ F] [IB.Boundaryless]
  [IsManifold IB ∞ B] [ContMDiffVectorBundle ∞ F V IB] in
theorem mfderiv_fiberRadiusSquared_level_ne_zero {R : ℝ} (hR : 0 < R)
    (z : TotalSpace F V) (hz : fiberRadiusSquared z = R ^ 2) :
    mfderiv (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ, ℝ) (fiberRadiusSquared (F := F) (V := V)) z ≠ 0 := by
  let γ : ℝ → TotalSpace F V := fun s => ⟨z.proj, (1 + s) • z.2⟩
  have hγ : ContMDiff 𝓘(ℝ, ℝ) (IB.prod 𝓘(ℝ, F)) ∞ γ :=
    DifferentialGeometry.Geometry.Collapse.contMDiff_totalSpace_smul.comp
      ((contMDiff_const.add contMDiff_id).prodMk (contMDiff_const (c := z)))
  have heq : (fun s => fiberRadiusSquared (γ s)) = fun s => (1 + s) ^ 2 * R ^ 2 := by
    funext s
    dsimp [fiberRadiusSquared, γ]
    rw [inner_smul_left, inner_smul_right]
    change (1 + s) * ((1 + s) * fiberRadiusSquared z) = _
    rw [hz]
    ring
  have hder : HasDerivAt (fun s => fiberRadiusSquared (γ s)) (2 * R ^ 2) 0 := by
    rw [heq]
    convert (((hasDerivAt_id (0 : ℝ)).const_add 1).pow 2).mul_const (R ^ 2) using 1 <;>
      norm_num
  apply DifferentialGeometry.Geometry.Collapse.mfderiv_ne_zero_of_curve
    (contMDiff_fiberRadiusSquared.mdifferentiable (by norm_num) z)
    (by simp [γ]) (hγ.mdifferentiable (by norm_num) 0) hder
  positivity

def bundleRadiusBoundaryEquiv {m : ℕ} (hd : Module.finrank ℝ (EB × F) = m + 1) :
    (EB × F) ≃L[ℝ] MorseModel (m + 1) :=
  ContinuousLinearEquiv.ofFinrankEq (hd.trans (Module.finrank_fin_fun ℝ).symm)

abbrev bundleRadiusBoundaryModel {m : ℕ} (hd : Module.finrank ℝ (EB × F) = m + 1) :
    ModelWithCorners ℝ (MorseModel (m + 1)) (ModelProd HB F) :=
  (IB.prod 𝓘(ℝ, F)).transContinuousLinearEquiv (bundleRadiusBoundaryEquiv hd)

omit [IB.Boundaryless] [IsManifold IB ∞ B] [ContMDiffVectorBundle ∞ F V IB] in
private theorem radiusSquared_smooth {m : ℕ} (hd : Module.finrank ℝ (EB × F) = m + 1) :
    ContMDiff (bundleRadiusBoundaryModel (IB := IB) hd) 𝓘(ℝ, ℝ) ∞
      (fiberRadiusSquared (F := F) (V := V)) :=
  (bundleRadiusBoundaryEquiv hd).contMDiff_transContinuousLinearEquiv_left.mpr
    contMDiff_fiberRadiusSquared

omit [IB.Boundaryless] [IsManifold IB ∞ B] [ContMDiffVectorBundle ∞ F V IB] in
private theorem radiusSquared_regular {m : ℕ} (hd : Module.finrank ℝ (EB × F) = m + 1)
    (R : ℝ) (hR : 0 < R) (z : TotalSpace F V) (hz : fiberRadiusSquared z = R ^ 2) :
    mfderiv (bundleRadiusBoundaryModel (IB := IB) hd) 𝓘(ℝ, ℝ)
      (fiberRadiusSquared (F := F) (V := V)) z ≠ 0 := by
  intro hzero
  apply mfderiv_fiberRadiusSquared_level_ne_zero (IB := IB) hR z hz
  exact (isCriticalPointAt_transContinuousLinearEquiv_iff (IB.prod 𝓘(ℝ, F))
    (bundleRadiusBoundaryEquiv hd) (fiberRadiusSquared (F := F) (V := V)) z).mp hzero

@[instance_reducible]
def closedDiscBundleChartedSpace {m : ℕ} (hd : Module.finrank ℝ (EB × F) = m + 1)
    (R : ℝ) (hR : 0 < R) :
    ChartedSpace (MorseHalfSpace m) {z : TotalSpace F V // fiberRadiusSquared z ≤ R ^ 2} :=
  DifferentialGeometry.Manifold.RegularLevel.sublevelChartedSpace
    (bundleRadiusBoundaryModel (IB := IB) hd)
    (radiusSquared_smooth (IB := IB) (V := V) hd)
    (radiusSquared_regular (IB := IB) (V := V) hd R hR)

theorem closedDiscBundle_isManifold {m : ℕ} (hd : Module.finrank ℝ (EB × F) = m + 1)
    (R : ℝ) (hR : 0 < R) :
    let := closedDiscBundleChartedSpace (IB := IB) (V := V) hd R hR
    IsManifold (morseModelWithCornersHalfSpace m) ∞
      {z : TotalSpace F V // fiberRadiusSquared z ≤ R ^ 2} :=
  sublevelIsManifold (bundleRadiusBoundaryModel (IB := IB) hd)
    (radiusSquared_smooth (IB := IB) (V := V) hd)
    (radiusSquared_regular (IB := IB) (V := V) hd R hR)

theorem closedDiscBundle_boundary_iff {m : ℕ} (hd : Module.finrank ℝ (EB × F) = m + 1)
    (R : ℝ) (hR : 0 < R) (z : {z : TotalSpace F V // fiberRadiusSquared z ≤ R ^ 2}) :
    let := closedDiscBundleChartedSpace (IB := IB) (V := V) hd R hR
    (morseModelWithCornersHalfSpace m).IsBoundaryPoint z ↔ ‖z.val.2‖ = R := by
  let := closedDiscBundleChartedSpace (IB := IB) (V := V) hd R hR
  have h := sublevelBoundary_iff (bundleRadiusBoundaryModel (IB := IB) hd)
    (radiusSquared_smooth (IB := IB) (V := V) hd)
    (radiusSquared_regular (IB := IB) (V := V) hd R hR) z
  exact h.trans (by
    rw [fiberRadiusSquared, real_inner_self_eq_norm_sq]
    exact sq_eq_sq₀ (norm_nonneg _) hR.le)

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace B] [TopologicalSpace (TotalSpace F V)] [FiberBundle F V]
  [VectorBundle ℝ F V] in
private theorem radiusSquared_scaled (c : ℝ) (z : TotalSpace F V) :
    fiberRadiusSquared (⟨z.proj, c • z.2⟩ : TotalSpace F V) = c ^ 2 * fiberRadiusSquared z := by
  simp only [fiberRadiusSquared, inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]
  ring

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace B] [TopologicalSpace (TotalSpace F V)] [FiberBundle F V]
  [VectorBundle ℝ F V] in
private theorem radiusSquared_scaled_le {S T : ℝ} (hS : 0 < S)
    (z : TotalSpace F V) (hz : fiberRadiusSquared z ≤ S ^ 2) :
    fiberRadiusSquared (⟨z.proj, (T / S) • z.2⟩ : TotalSpace F V) ≤ T ^ 2 := by
  rw [radiusSquared_scaled]
  calc
    (T / S) ^ 2 * fiberRadiusSquared z ≤ (T / S) ^ 2 * S ^ 2 :=
      mul_le_mul_of_nonneg_left hz (sq_nonneg _)
    _ = T ^ 2 := by field_simp

omit [FiniteDimensional ℝ EB] [FiniteDimensional ℝ F] [IB.Boundaryless]
  [IsManifold IB ∞ B] [ContMDiffVectorBundle ∞ F V IB]
  [IsContMDiffRiemannianBundle IB ∞ F V] in
private theorem fiberScale_smooth (c : ℝ) :
    ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F)) ∞
      (fun z : TotalSpace F V => (⟨z.proj, c • z.2⟩ : TotalSpace F V)) :=
  DifferentialGeometry.Geometry.Collapse.contMDiff_totalSpace_smul.comp
    (contMDiff_const.prodMk contMDiff_id)

def discRadiusDiffeomorph {m : ℕ} (hd : Module.finrank ℝ (EB × F) = m + 1)
    (S T : ℝ) (hS : 0 < S) (hT : 0 < T) :
    let := closedDiscBundleChartedSpace (IB := IB) (V := V) hd S hS
    let := closedDiscBundleChartedSpace (IB := IB) (V := V) hd T hT
    Diffeomorph (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m)
      {z : TotalSpace F V // fiberRadiusSquared z ≤ S ^ 2}
      {z : TotalSpace F V // fiberRadiusSquared z ≤ T ^ 2} ∞ := by
  let := closedDiscBundleChartedSpace (IB := IB) (V := V) hd S hS
  let := closedDiscBundleChartedSpace (IB := IB) (V := V) hd T hT
  refine { toFun := fun z => ⟨⟨z.val.proj, (T / S) • z.val.2⟩,
             radiusSquared_scaled_le hS z.val z.property⟩
           invFun := fun z => ⟨⟨z.val.proj, (S / T) • z.val.2⟩,
             radiusSquared_scaled_le hT z.val z.property⟩
           left_inv := ?_
           right_inv := ?_
           contMDiff_toFun := ?_
           contMDiff_invFun := ?_ }
  · intro z
    apply Subtype.ext
    change (⟨z.val.proj, (S / T) • (T / S) • z.val.2⟩ : TotalSpace F V) = z.val
    have hc : S / T * (T / S) = 1 := by field_simp
    rw [smul_smul, hc, one_smul]
  · intro z
    apply Subtype.ext
    change (⟨z.val.proj, (T / S) • (S / T) • z.val.2⟩ : TotalSpace F V) = z.val
    have hc : T / S * (S / T) = 1 := by field_simp
    rw [smul_smul, hc, one_smul]
  · apply (contMDiff_sublevel_iff (bundleRadiusBoundaryModel (IB := IB) hd)
      (morseModelWithCornersHalfSpace m) (radiusSquared_smooth (IB := IB) (V := V) hd)
      (radiusSquared_regular (IB := IB) (V := V) hd T hT) le_rfl).mpr
    have hs := contMDiff_sublevel_inclusion (bundleRadiusBoundaryModel (IB := IB) hd)
      (radiusSquared_smooth (IB := IB) (V := V) hd)
      (radiusSquared_regular (IB := IB) (V := V) hd S hS)
    have hf := (bundleRadiusBoundaryEquiv hd).contMDiff_transContinuousLinearEquiv_left.mpr
      ((bundleRadiusBoundaryEquiv hd).contMDiff_transContinuousLinearEquiv_right.mpr
        (fiberScale_smooth (IB := IB) (V := V) (T / S)))
    exact hf.comp hs
  · apply (contMDiff_sublevel_iff (bundleRadiusBoundaryModel (IB := IB) hd)
      (morseModelWithCornersHalfSpace m) (radiusSquared_smooth (IB := IB) (V := V) hd)
      (radiusSquared_regular (IB := IB) (V := V) hd S hS) le_rfl).mpr
    have hs := contMDiff_sublevel_inclusion (bundleRadiusBoundaryModel (IB := IB) hd)
      (radiusSquared_smooth (IB := IB) (V := V) hd)
      (radiusSquared_regular (IB := IB) (V := V) hd T hT)
    have hf := (bundleRadiusBoundaryEquiv hd).contMDiff_transContinuousLinearEquiv_left.mpr
      ((bundleRadiusBoundaryEquiv hd).contMDiff_transContinuousLinearEquiv_right.mpr
        (fiberScale_smooth (IB := IB) (V := V) (S / T)))
    exact hf.comp hs

theorem discRadiusDiffeomorph_apply {m : ℕ} (hd : Module.finrank ℝ (EB × F) = m + 1)
    (S T : ℝ) (hS : 0 < S) (hT : 0 < T)
    (z : {z : TotalSpace F V // fiberRadiusSquared z ≤ S ^ 2}) :
    let := closedDiscBundleChartedSpace (IB := IB) (V := V) hd S hS
    let := closedDiscBundleChartedSpace (IB := IB) (V := V) hd T hT
    (discRadiusDiffeomorph (IB := IB) hd S T hS hT z).val =
      (⟨z.val.proj, (T / S) • z.val.2⟩ : TotalSpace F V) := rfl


omit [FiniteDimensional ℝ EB] [FiniteDimensional ℝ F] [IB.Boundaryless]
  [IsManifold IB ∞ B] [ContMDiffVectorBundle ∞ F V IB]
  [IsContMDiffRiemannianBundle IB ∞ F V] [ChartedSpace HB B] in
def normClosedDiscSublevelHomeomorph (R : ℝ) (hR : 0 < R) :
    {z : TotalSpace F V // ‖z.2‖ ≤ R} ≃ₜ
      {z : TotalSpace F V // fiberRadiusSquared z ≤ R ^ 2} :=
  Homeomorph.setCongr (by
    ext z
    change ‖z.2‖ ≤ R ↔ fiberRadiusSquared z ≤ R ^ 2
    rw [fiberRadiusSquared, real_inner_self_eq_norm_sq]
    exact (sq_le_sq₀ (norm_nonneg _) hR.le).symm)

@[instance_reducible]
def normClosedDiscBundleChartedSpace {m : ℕ} (hd : Module.finrank ℝ (EB × F) = m + 1)
    (R : ℝ) (hR : 0 < R) :
    ChartedSpace (MorseHalfSpace m) {z : TotalSpace F V // ‖z.2‖ ≤ R} := by
  let := closedDiscBundleChartedSpace (IB := IB) (V := V) hd R hR
  exact DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (normClosedDiscSublevelHomeomorph (F := F) (V := V) R hR)

theorem normClosedDiscBundle_isManifold {m : ℕ} (hd : Module.finrank ℝ (EB × F) = m + 1)
    (R : ℝ) (hR : 0 < R) :
    let := normClosedDiscBundleChartedSpace (IB := IB) (V := V) hd R hR
    IsManifold (morseModelWithCornersHalfSpace m) ∞
      {z : TotalSpace F V // ‖z.2‖ ≤ R} := by
  let := closedDiscBundleChartedSpace (IB := IB) (V := V) hd R hR
  let := closedDiscBundle_isManifold (IB := IB) (V := V) hd R hR
  exact DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback
    (normClosedDiscSublevelHomeomorph (F := F) (V := V) R hR)

theorem normClosedDiscBundle_boundary_iff {m : ℕ} (hd : Module.finrank ℝ (EB × F) = m + 1)
    (R : ℝ) (hR : 0 < R) (z : {z : TotalSpace F V // ‖z.2‖ ≤ R}) :
    let := normClosedDiscBundleChartedSpace (IB := IB) (V := V) hd R hR
    (morseModelWithCornersHalfSpace m).IsBoundaryPoint z ↔ ‖z.val.2‖ = R := by
  let := closedDiscBundleChartedSpace (IB := IB) (V := V) hd R hR
  let := closedDiscBundle_isManifold (IB := IB) (V := V) hd R hR
  let e := normClosedDiscSublevelHomeomorph (F := F) (V := V) R hR
  let := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (H := MorseHalfSpace m) e
  let D := DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
    (I := morseModelWithCornersHalfSpace m) (n := ∞) e
  exact ((D.isLocalDiffeomorph z).isBoundaryPoint_iff (by simp)).trans
    (closedDiscBundle_boundary_iff (IB := IB) hd R hR (e z))

def normDiscRadiusDiffeomorph {m : ℕ} (hd : Module.finrank ℝ (EB × F) = m + 1)
    (S T : ℝ) (hS : 0 < S) (hT : 0 < T) :
    let := normClosedDiscBundleChartedSpace (IB := IB) (V := V) hd S hS
    let := normClosedDiscBundleChartedSpace (IB := IB) (V := V) hd T hT
    Diffeomorph (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m)
      {z : TotalSpace F V // ‖z.2‖ ≤ S} {z : TotalSpace F V // ‖z.2‖ ≤ T} ∞ := by
  let := closedDiscBundleChartedSpace (IB := IB) (V := V) hd S hS
  let := closedDiscBundleChartedSpace (IB := IB) (V := V) hd T hT
  let := closedDiscBundle_isManifold (IB := IB) (V := V) hd S hS
  let := closedDiscBundle_isManifold (IB := IB) (V := V) hd T hT
  let eS := normClosedDiscSublevelHomeomorph (F := F) (V := V) S hS
  let eT := normClosedDiscSublevelHomeomorph (F := F) (V := V) T hT
  let := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (H := MorseHalfSpace m) eS
  let := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (H := MorseHalfSpace m) eT
  let DS := DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
    (I := morseModelWithCornersHalfSpace m) (n := ∞) eS
  let DT := DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
    (I := morseModelWithCornersHalfSpace m) (n := ∞) eT
  exact (DS.trans (discRadiusDiffeomorph (IB := IB) (V := V) hd S T hS hT)).trans DT.symm

theorem normDiscRadiusDiffeomorph_apply {m : ℕ} (hd : Module.finrank ℝ (EB × F) = m + 1)
    (S T : ℝ) (hS : 0 < S) (hT : 0 < T)
    (z : {z : TotalSpace F V // ‖z.2‖ ≤ S}) :
    let := normClosedDiscBundleChartedSpace (IB := IB) (V := V) hd S hS
    let := normClosedDiscBundleChartedSpace (IB := IB) (V := V) hd T hT
    (normDiscRadiusDiffeomorph (IB := IB) hd S T hS hT z).val =
      (⟨z.val.proj, (T / S) • z.val.2⟩ : TotalSpace F V) := rfl

private theorem circleLineBundle_total_dimension :
    Module.finrank ℝ ((EuclideanSpace ℝ (Fin 1)) × ℝ) = 1 + 1 := by simp

def circleLineDiscRadiusTwo :
    let := normClosedDiscBundleChartedSpace (IB := 𝓡 1) (V := Bundle.Trivial Circle ℝ)
      circleLineBundle_total_dimension 1 (by norm_num)
    let := normClosedDiscBundleChartedSpace (IB := 𝓡 1) (V := Bundle.Trivial Circle ℝ)
      circleLineBundle_total_dimension 2 (by norm_num)
    Diffeomorph (morseModelWithCornersHalfSpace 1) (morseModelWithCornersHalfSpace 1)
      {z : TotalSpace ℝ (Bundle.Trivial Circle ℝ) // ‖z.2‖ ≤ 1}
      {z : TotalSpace ℝ (Bundle.Trivial Circle ℝ) // ‖z.2‖ ≤ 2} ∞ :=
  normDiscRadiusDiffeomorph (IB := 𝓡 1) circleLineBundle_total_dimension 1 2
    (by norm_num) (by norm_num)

theorem circleLineDiscRadiusTwo_apply
    (z : {z : TotalSpace ℝ (Bundle.Trivial Circle ℝ) // ‖z.2‖ ≤ 1}) :
    let := normClosedDiscBundleChartedSpace (IB := 𝓡 1) (V := Bundle.Trivial Circle ℝ)
      circleLineBundle_total_dimension 1 (by norm_num)
    let := normClosedDiscBundleChartedSpace (IB := 𝓡 1) (V := Bundle.Trivial Circle ℝ)
      circleLineBundle_total_dimension 2 (by norm_num)
    (circleLineDiscRadiusTwo z).val = ⟨z.val.proj, (2 : ℝ) • z.val.2⟩ := by
  simp only [circleLineDiscRadiusTwo, normDiscRadiusDiffeomorph_apply, div_one]

end DifferentialGeometry.Topology.VectorBundle
