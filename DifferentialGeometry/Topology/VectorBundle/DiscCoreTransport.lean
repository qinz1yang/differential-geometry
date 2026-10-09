import DifferentialGeometry.Topology.VectorBundle.DiscRadiusDiffeomorph
import DifferentialGeometry.Topology.VectorBundle.ClosedDiscCompact

/-!
# Closed disc cores under the retained smooth ambient map

The ambient core is the literal full inverse image of the bundle norm bound under the supplied
smooth diffeomorphism. Its boundary charts, smooth ambient inclusion and unit-disc map all use
that same map. Compactness and properness follow from the actual compact-base bundle.
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
  {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  {HN : Type*} [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
  {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
  (e : Diffeomorph (IB.prod 𝓘(ℝ, F)) IN (TotalSpace F V) N ∞)

def discCoreHomeomorph (T : ℝ) :
    {z : TotalSpace F V // ‖z.2‖ ≤ T} ≃ₜ {x : N // ‖(e.symm x).2‖ ≤ T} :=
  e.toHomeomorph.subtype (by
    intro z
    change ‖z.2‖ ≤ T ↔ ‖(e.symm (e z)).2‖ ≤ T
    rw [e.symm_apply_apply])

@[instance_reducible]
def discCoreChartedSpace {m : ℕ} (hd : Module.finrank ℝ (EB × F) = m + 1)
    (T : ℝ) (hT : 0 < T) :
    ChartedSpace (MorseHalfSpace m) {x : N // ‖(e.symm x).2‖ ≤ T} := by
  let := normClosedDiscBundleChartedSpace (IB := IB) (V := V) hd T hT
  exact DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (discCoreHomeomorph e T).symm

def discCoreDiffeomorph {m : ℕ} (hd : Module.finrank ℝ (EB × F) = m + 1)
    (T : ℝ) (hT : 0 < T) :
    let := normClosedDiscBundleChartedSpace (IB := IB) (V := V) hd T hT
    let := discCoreChartedSpace e hd T hT
    Diffeomorph (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m)
      {z : TotalSpace F V // ‖z.2‖ ≤ T} {x : N // ‖(e.symm x).2‖ ≤ T} ∞ := by
  let := normClosedDiscBundleChartedSpace (IB := IB) (V := V) hd T hT
  let := normClosedDiscBundle_isManifold (IB := IB) (V := V) hd T hT
  let := discCoreChartedSpace e hd T hT
  exact (DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
    (I := morseModelWithCornersHalfSpace m) (n := ∞) (discCoreHomeomorph e T).symm).symm

theorem normClosedDisc_inclusion_contMDiff {m : ℕ}
    (hd : Module.finrank ℝ (EB × F) = m + 1) (T : ℝ) (hT : 0 < T) :
    let := normClosedDiscBundleChartedSpace (IB := IB) (V := V) hd T hT
    ContMDiff (morseModelWithCornersHalfSpace m) (IB.prod 𝓘(ℝ, F)) ∞
      (Subtype.val : {z : TotalSpace F V // ‖z.2‖ ≤ T} → TotalSpace F V) := by
  let J := bundleRadiusBoundaryModel (IB := IB) hd
  have hf : ContMDiff J 𝓘(ℝ, ℝ) ∞ (fiberRadiusSquared (F := F) (V := V)) :=
    (bundleRadiusBoundaryEquiv hd).contMDiff_transContinuousLinearEquiv_left.mpr
      contMDiff_fiberRadiusSquared
  have hr : ∀ z : TotalSpace F V, fiberRadiusSquared z = T ^ 2 →
      mfderiv J 𝓘(ℝ, ℝ) (fiberRadiusSquared (F := F) (V := V)) z ≠ 0 := by
    intro z hz hzero
    apply mfderiv_fiberRadiusSquared_level_ne_zero (IB := IB) hT z hz
    exact (isCriticalPointAt_transContinuousLinearEquiv_iff (IB.prod 𝓘(ℝ, F))
      (bundleRadiusBoundaryEquiv hd) (fiberRadiusSquared (F := F) (V := V)) z).mp hzero
  let := closedDiscBundleChartedSpace (IB := IB) (V := V) hd T hT
  let := closedDiscBundle_isManifold (IB := IB) (V := V) hd T hT
  let h := normClosedDiscSublevelHomeomorph (F := F) (V := V) T hT
  let := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (H := MorseHalfSpace m) h
  have hh := DifferentialGeometry.Manifold.Homeomorph.contMDiff_pullback
    (I := morseModelWithCornersHalfSpace m) (n := ∞) h
  have hs := contMDiff_sublevel_inclusion J hf hr
  exact (bundleRadiusBoundaryEquiv hd).contMDiff_transContinuousLinearEquiv_right.mp
    (hs.comp hh)

theorem discCore_inclusion_contMDiff {m : ℕ} (hd : Module.finrank ℝ (EB × F) = m + 1)
    (T : ℝ) (hT : 0 < T) :
    let := discCoreChartedSpace e hd T hT
    ContMDiff (morseModelWithCornersHalfSpace m) IN ∞
      (Subtype.val : {x : N // ‖(e.symm x).2‖ ≤ T} → N) := by
  let := normClosedDiscBundleChartedSpace (IB := IB) (V := V) hd T hT
  let := discCoreChartedSpace e hd T hT
  have h := e.contMDiff.comp
    ((normClosedDisc_inclusion_contMDiff (IB := IB) (V := V) hd T hT).comp
      (discCoreDiffeomorph e hd T hT).symm.contMDiff)
  apply h.congr
  intro x
  exact (e.apply_symm_apply x.val).symm

theorem discCore_boundary_iff {m : ℕ} (hd : Module.finrank ℝ (EB × F) = m + 1)
    (T : ℝ) (hT : 0 < T) (x : {x : N // ‖(e.symm x).2‖ ≤ T}) :
    let := discCoreChartedSpace e hd T hT
    (morseModelWithCornersHalfSpace m).IsBoundaryPoint x ↔ ‖(e.symm x.val).2‖ = T := by
  let := normClosedDiscBundleChartedSpace (IB := IB) (V := V) hd T hT
  let := normClosedDiscBundle_isManifold (IB := IB) (V := V) hd T hT
  let := discCoreChartedSpace e hd T hT
  let := DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback
    (I := morseModelWithCornersHalfSpace m) (n := ∞) (discCoreHomeomorph e T).symm
  exact (((discCoreDiffeomorph e hd T hT).symm.isLocalDiffeomorph x).isBoundaryPoint_iff
    (by simp)).trans (normClosedDiscBundle_boundary_iff (IB := IB) hd T hT
      ((discCoreDiffeomorph e hd T hT).symm x))

def unitDiscCoreDiffeomorph {m : ℕ} (hd : Module.finrank ℝ (EB × F) = m + 1)
    (T : ℝ) (hT : 0 < T) :
    let := normClosedDiscBundleChartedSpace (IB := IB) (V := V) hd 1 (by norm_num)
    let := discCoreChartedSpace e hd T hT
    Diffeomorph (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m)
      {z : TotalSpace F V // ‖z.2‖ ≤ 1} {x : N // ‖(e.symm x).2‖ ≤ T} ∞ := by
  let := normClosedDiscBundleChartedSpace (IB := IB) (V := V) hd 1 (by norm_num)
  let := normClosedDiscBundleChartedSpace (IB := IB) (V := V) hd T hT
  let := discCoreChartedSpace e hd T hT
  exact (normDiscRadiusDiffeomorph (IB := IB) (V := V) hd 1 T (by norm_num) hT).trans
    (discCoreDiffeomorph e hd T hT)

theorem unitDiscCoreDiffeomorph_apply {m : ℕ} (hd : Module.finrank ℝ (EB × F) = m + 1)
    (T : ℝ) (hT : 0 < T) (z : {z : TotalSpace F V // ‖z.2‖ ≤ 1}) :
    let := normClosedDiscBundleChartedSpace (IB := IB) (V := V) hd 1 (by norm_num)
    let := discCoreChartedSpace e hd T hT
    (unitDiscCoreDiffeomorph e hd T hT z).val = e ⟨z.val.proj, T • z.val.2⟩ := by
  change e ⟨z.val.proj, (T / 1) • z.val.2⟩ = _
  rw [div_one]

omit [FiniteDimensional ℝ EB] [IB.Boundaryless] [IsManifold IB ∞ B]
  [ContMDiffVectorBundle ∞ F V IB] [FiniteDimensional ℝ F]
  [IsContMDiffRiemannianBundle IB ∞ F V] in
private theorem smoothBundle_continuousMetric
    (h : IsContMDiffRiemannianBundle IB ∞ F V) : IsContinuousRiemannianBundle F V := by
  obtain ⟨g, hg, heq⟩ := h.exists_contMDiff
  exact ⟨g, hg.continuous, heq⟩

omit [FiniteDimensional ℝ EB] [IB.Boundaryless] [IsManifold IB ∞ B]
  [ContMDiffVectorBundle ∞ F V IB] in
theorem isCompact_discCore [CompactSpace B] (T : ℝ) :
    IsCompact {x : N | ‖(e.symm x).2‖ ≤ T} := by
  let := smoothBundle_continuousMetric (IB := IB) (F := F) (V := V) inferInstance
  have heq : {x : N | ‖(e.symm x).2‖ ≤ T} = e '' {z : TotalSpace F V | ‖z.2‖ ≤ T} := by
    ext x
    exact ⟨fun hx => ⟨e.symm x, hx, e.apply_symm_apply x⟩,
      fun ⟨z, hz, hzx⟩ => by
        rw [← hzx]
        change ‖(e.symm (e z)).2‖ ≤ T
        rw [e.symm_apply_apply]
        exact hz⟩
  rw [heq]
  exact isCompact_transportedClosedDiscBundle e.toHomeomorph T

omit [FiniteDimensional ℝ EB] [IB.Boundaryless] [IsManifold IB ∞ B]
  [ContMDiffVectorBundle ∞ F V IB] in
theorem isProperMap_discCoreRadius [CompactSpace B] :
    IsProperMap (fun x : N => ‖(e.symm x).2‖) := by
  let := smoothBundle_continuousMetric (IB := IB) (F := F) (V := V) inferInstance
  exact isProperMap_transportedFiberRadius e.toHomeomorph


omit [FiniteDimensional ℝ EB] [FiniteDimensional ℝ F] [IB.Boundaryless]
  [IsManifold IB ∞ B] [ContMDiffVectorBundle ∞ F V IB] in
theorem contMDiff_discCoreRadiusSquared :
    ContMDiff IN 𝓘(ℝ, ℝ) ∞ (fun x : N => fiberRadiusSquared (e.symm x)) :=
  contMDiff_fiberRadiusSquared.comp e.symm.contMDiff

omit [FiniteDimensional ℝ EB] [FiniteDimensional ℝ F] [IB.Boundaryless]
  [IsManifold IB ∞ B] [ContMDiffVectorBundle ∞ F V IB] in
theorem contMDiffOn_discCoreRadius_off_zero :
    ContMDiffOn IN 𝓘(ℝ, ℝ) ∞ (fun x : N => ‖(e.symm x).2‖)
      {x : N | (e.symm x).2 ≠ 0} := by
  intro x hx
  have hpos : 0 < fiberRadiusSquared (e.symm x) := by
    rw [fiberRadiusSquared, real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr hx)
  have hs := (Real.contDiffAt_sqrt hpos.ne').contMDiffAt.comp x
    ((contMDiff_discCoreRadiusSquared e) x)
  simpa only [Function.comp_def, fiberRadiusSquared, ← norm_eq_sqrt_real_inner]
    using hs.contMDiffWithinAt

omit [FiniteDimensional ℝ EB] [FiniteDimensional ℝ F] [IB.Boundaryless]
  [IsManifold IB ∞ B] [ContMDiffVectorBundle ∞ F V IB] in
private theorem continuous_discCoreRadius : Continuous (fun x : N => ‖(e.symm x).2‖) := by
  have h := (contMDiff_discCoreRadiusSquared e).continuous.sqrt
  simpa only [fiberRadiusSquared, ← norm_eq_sqrt_real_inner] using h

omit [FiniteDimensional ℝ EB] [FiniteDimensional ℝ F] [IB.Boundaryless]
  [IsManifold IB ∞ B] [ContMDiffVectorBundle ∞ F V IB] in
theorem discCore_strictly_nested {S T : ℝ} (hST : S < T) :
    {x : N | ‖(e.symm x).2‖ ≤ S} ⊆ interior {x : N | ‖(e.symm x).2‖ ≤ T} :=
  DifferentialGeometry.Geometry.Collapse.sublevel_subset_interior_sublevel
    (continuous_discCoreRadius e) hST

omit [FiniteDimensional ℝ EB] [FiniteDimensional ℝ F] [IB.Boundaryless]
  [IsManifold IB ∞ B] [ContMDiffVectorBundle ∞ F V IB] in
theorem iUnion_positive_discCore_interior :
    ⋃ (T : ℝ) (_hT : 0 < T), interior {x : N | ‖(e.symm x).2‖ ≤ T} = univ := by
  apply eq_univ_of_forall
  intro x
  refine mem_iUnion.mpr ⟨‖(e.symm x).2‖ + 1, mem_iUnion.mpr ⟨by positivity, ?_⟩⟩
  exact discCore_strictly_nested e (by linarith : ‖(e.symm x).2‖ < ‖(e.symm x).2‖ + 1)
    (by change ‖(e.symm x).2‖ ≤ ‖(e.symm x).2‖; exact le_rfl)

omit [FiniteDimensional ℝ EB] [FiniteDimensional ℝ F] [IB.Boundaryless]
  [IsManifold IB ∞ B] [ContMDiffVectorBundle ∞ F V IB] in
theorem exists_eventually_compact_subset_discCore_interior {K : Set N} (hK : IsCompact K) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T, T₀ ≤ T → K ⊆ interior {x : N | ‖(e.symm x).2‖ ≤ T} := by
  obtain ⟨R, hR⟩ := DifferentialGeometry.Geometry.Collapse.exists_subset_interior_sublevel
    (continuous_discCoreRadius e) hK
  refine ⟨max R 1, lt_of_lt_of_le (by norm_num) (le_max_right R 1), ?_⟩
  intro T hT
  exact hR T ((le_max_left R 1).trans hT)

private theorem circleLineBundle_core_dimension :
    Module.finrank ℝ ((EuclideanSpace ℝ (Fin 1)) × ℝ) = 1 + 1 := by simp

def circleLineAmbientCoreRadiusTwo :
    let e := Diffeomorph.refl ((𝓡 1).prod 𝓘(ℝ, ℝ)) (TotalSpace ℝ (Bundle.Trivial Circle ℝ)) ∞
    let := normClosedDiscBundleChartedSpace (IB := 𝓡 1) (V := Bundle.Trivial Circle ℝ)
      circleLineBundle_core_dimension 1 (by norm_num)
    let := discCoreChartedSpace e circleLineBundle_core_dimension 2 (by norm_num)
    Diffeomorph (morseModelWithCornersHalfSpace 1) (morseModelWithCornersHalfSpace 1)
      {z : TotalSpace ℝ (Bundle.Trivial Circle ℝ) // ‖z.2‖ ≤ 1}
      {z : TotalSpace ℝ (Bundle.Trivial Circle ℝ) // ‖(e.symm z).2‖ ≤ 2} ∞ :=
  unitDiscCoreDiffeomorph (IB := 𝓡 1)
    (Diffeomorph.refl ((𝓡 1).prod 𝓘(ℝ, ℝ)) (TotalSpace ℝ (Bundle.Trivial Circle ℝ)) ∞)
    circleLineBundle_core_dimension 2 (by norm_num)

theorem circleLineAmbientCoreRadiusTwo_apply
    (z : {z : TotalSpace ℝ (Bundle.Trivial Circle ℝ) // ‖z.2‖ ≤ 1}) :
    let e := Diffeomorph.refl ((𝓡 1).prod 𝓘(ℝ, ℝ)) (TotalSpace ℝ (Bundle.Trivial Circle ℝ)) ∞
    let := normClosedDiscBundleChartedSpace (IB := 𝓡 1) (V := Bundle.Trivial Circle ℝ)
      circleLineBundle_core_dimension 1 (by norm_num)
    let := discCoreChartedSpace e circleLineBundle_core_dimension 2 (by norm_num)
    (circleLineAmbientCoreRadiusTwo z).val =
      (⟨z.val.proj, (2 : ℝ) • z.val.2⟩ : TotalSpace ℝ (Bundle.Trivial Circle ℝ)) := by
  exact unitDiscCoreDiffeomorph_apply (IB := 𝓡 1)
    (Diffeomorph.refl ((𝓡 1).prod 𝓘(ℝ, ℝ)) (TotalSpace ℝ (Bundle.Trivial Circle ℝ)) ∞)
    circleLineBundle_core_dimension 2 (by norm_num) z

end DifferentialGeometry.Topology.VectorBundle
