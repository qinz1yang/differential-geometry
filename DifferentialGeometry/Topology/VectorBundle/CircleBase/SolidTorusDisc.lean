import DifferentialGeometry.Topology.VectorBundle.NormPreservingDisc
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.SolidTorus
import DifferentialGeometry.Topology.Manifold.AddCircle.Circle

/-!
# The closed unit disc bundle of `S¹ × ℝ²` is the standard solid torus (P1b)

LFR54 → chapter 14 `ZeroModel.solidTorus`, item P1b of lane F7-LFR51 (frozen statement in
`build-logs/scratch/F7-LFR51/P1Inputs.lean`). The closed unit disc bundle of the trivial bundle
`S¹ × ℝ²` over `S¹ = AddCircle 1`, with its native boundary charts
(`normClosedDiscBundleChartedSpace`, model `morseModelWithCornersHalfSpace 2`), is diffeomorphic to
`GC.GraphManifold.solidTorusCarrier` (`nonempty_solidTorusCarrier_diffeomorph_closedDisc`).

Route: the solid torus is already identified with `UnitDisc × Circle`
(`GC.GraphManifold.solidTorusDiscCircle`); the map `(w, v) ↦ (θ(v), w)` (with `AddCircle 1 ≅ Circle`
and `ℂ ≅ ℝ²` isometric) is a diffeomorphism from `UnitDisc × Circle` onto the regular sublevel
`{‖z.2‖² ≤ 1}` (`discCircleSublevelDiffeomorph`), smooth in both directions through the sublevel
charts.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped ContDiff Topology Manifold
open DifferentialGeometry.Topology.Morse DifferentialGeometry.Manifold.RegularLevel

universe u

namespace DifferentialGeometry.Topology.VectorBundle

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "S1" => AddCircle (1 : ℝ)

/-- Total dimension of `S¹ × ℝ²`. -/
theorem finrank_circle_plane : Module.finrank ℝ (ℝ × E2) = 2 + 1 := by simp

/-- The plane `ℝ²` as the complex line, isometrically. -/
def planeComplexIsometry : E2 ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm

private theorem fiberRadiusSquared_trivial_eq (z : TotalSpace E2 (Trivial S1 E2)) :
    fiberRadiusSquared z = ‖planeComplexIsometry z.2‖ ^ 2 := by
  rw [fiberRadiusSquared, real_inner_self_eq_norm_sq, LinearIsometryEquiv.norm_map]

/-- `(w, v) ↦ (θ(v), w)` from the closed unit disc times the circle into the closed unit disc
bundle of `S¹ × ℝ²` (squared-radius form). -/
def discCircleToSublevel (q : GC.GraphManifold.UnitDisc.{u} × Circle) :
    {z : TotalSpace E2 (Trivial S1 E2) // fiberRadiusSquared z ≤ 1 ^ 2} :=
  ⟨⟨AddCircle.diffeomorphCircle.symm q.2, planeComplexIsometry.symm q.1.down.val⟩, by
    rw [fiberRadiusSquared_trivial_eq]
    change ‖planeComplexIsometry (planeComplexIsometry.symm q.1.down.val)‖ ^ 2 ≤ 1 ^ 2
    rw [LinearIsometryEquiv.apply_symm_apply, one_pow]
    exact q.1.down.2⟩

/-- The inverse of `discCircleToSublevel`. -/
def sublevelToDiscCircle (z : {z : TotalSpace E2 (Trivial S1 E2) // fiberRadiusSquared z ≤ 1 ^ 2}) :
    GC.GraphManifold.UnitDisc.{u} × Circle :=
  (ULift.up ⟨planeComplexIsometry z.val.2, by
    have h := (fiberRadiusSquared_trivial_eq z.val).symm.trans_le z.2
    exact h.trans_eq (one_pow 2)⟩, AddCircle.diffeomorphCircle z.val.proj)

private theorem contMDiff_trivial_snd :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E2)) 𝓘(ℝ, E2) ∞
      (fun z : TotalSpace E2 (Trivial S1 E2) => (z.2 : E2)) :=
  fun z₀ => ((Bundle.contMDiffAt_totalSpace (f := id) (x₀ := z₀) (IB := 𝓘(ℝ, ℝ))
    (n := ∞)).mp contMDiffAt_id).2

private theorem contMDiff_trivial_mk {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
    {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] {β : M → S1} {γ : M → E2}
    (hβ : ContMDiff IM 𝓘(ℝ, ℝ) ∞ β) (hγ : ContMDiff IM 𝓘(ℝ, E2) ∞ γ) :
    ContMDiff IM (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E2)) ∞
      (fun x => (⟨β x, γ x⟩ : TotalSpace E2 (Trivial S1 E2))) :=
  fun x₀ => Bundle.contMDiffAt_totalSpace.mpr ⟨hβ x₀, hγ x₀⟩

theorem contMDiff_discCircleToSublevel :
    letI := closedDiscBundleChartedSpace (IB := 𝓘(ℝ, ℝ)) (V := Trivial S1 E2)
      finrank_circle_plane 1 one_pos
    ContMDiff ((𝓡∂ 2).prod (𝓡 1)) (morseModelWithCornersHalfSpace 2) ∞
      discCircleToSublevel.{u} := by
  let _ := closedDiscBundleChartedSpace (IB := 𝓘(ℝ, ℝ)) (V := Trivial S1 E2)
      finrank_circle_plane 1 one_pos
  apply (contMDiff_sublevel_iff (bundleRadiusBoundaryModel (IB := 𝓘(ℝ, ℝ)) finrank_circle_plane)
    ((𝓡∂ 2).prod (𝓡 1)) (contMDiff_fiberRadiusSquared_boundaryModel (V := Trivial S1 E2) finrank_circle_plane)
    (fun z hz => mfderiv_fiberRadiusSquared_boundaryModel_ne_zero finrank_circle_plane one_pos z hz)
    le_rfl).mpr
  refine (bundleRadiusBoundaryEquiv finrank_circle_plane).contMDiff_transContinuousLinearEquiv_right.mpr ?_
  refine contMDiff_trivial_mk ?_ ?_
  · exact AddCircle.diffeomorphCircle.symm.contMDiff.comp contMDiff_snd
  · exact (planeComplexIsometry.symm.toContinuousLinearEquiv.toContinuousLinearMap.contMDiff).comp
      (GC.GraphManifold.contMDiff_disc_val.comp contMDiff_fst)

theorem contMDiff_sublevelToDiscCircle :
    letI := closedDiscBundleChartedSpace (IB := 𝓘(ℝ, ℝ)) (V := Trivial S1 E2)
      finrank_circle_plane 1 one_pos
    ContMDiff (morseModelWithCornersHalfSpace 2) ((𝓡∂ 2).prod (𝓡 1)) ∞
      sublevelToDiscCircle.{u} := by
  let _ := closedDiscBundleChartedSpace (IB := 𝓘(ℝ, ℝ)) (V := Trivial S1 E2)
      finrank_circle_plane 1 one_pos
  have hval := contMDiff_sublevel_inclusion
    (bundleRadiusBoundaryModel (IB := 𝓘(ℝ, ℝ)) finrank_circle_plane)
    (contMDiff_fiberRadiusSquared_boundaryModel (V := Trivial S1 E2) finrank_circle_plane)
    (fun z hz => mfderiv_fiberRadiusSquared_boundaryModel_ne_zero finrank_circle_plane one_pos z hz)
    (a := 1 ^ 2)
  have hval' : ContMDiff (morseModelWithCornersHalfSpace 2) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E2)) ∞
      (Subtype.val : {z : TotalSpace E2 (Trivial S1 E2) // fiberRadiusSquared z ≤ 1 ^ 2} → _) :=
    (bundleRadiusBoundaryEquiv finrank_circle_plane).contMDiff_transContinuousLinearEquiv_right.mp hval
  refine ContMDiff.prodMk ?_ ?_
  · have hdisc : ContMDiff (morseModelWithCornersHalfSpace 2) (𝓡∂ 2) ∞
        (fun z : {z : TotalSpace E2 (Trivial S1 E2) // fiberRadiusSquared z ≤ 1 ^ 2} =>
          (sublevelToDiscCircle.{u} z).1.down) := by
      refine (GC.GraphManifold.unitDiscAtlas.contMDiff_iff_subtype_val _).mpr ?_
      exact (planeComplexIsometry.toContinuousLinearEquiv.toContinuousLinearMap.contMDiff).comp
        (contMDiff_trivial_snd.comp hval')
    exact (DifferentialGeometry.Topology.uliftDiffeomorph (𝓡∂ 2)
      GC.GraphManifold.unitDiscSet).contMDiff.comp hdisc
  · exact AddCircle.diffeomorphCircle.contMDiff.comp ((Bundle.contMDiff_proj _).comp hval')

/-- The closed unit disc times the circle is diffeomorphic to the closed unit disc bundle of
`S¹ × ℝ²` (squared-radius form, native boundary charts). -/
def discCircleSublevelDiffeomorph :
    letI := closedDiscBundleChartedSpace (IB := 𝓘(ℝ, ℝ)) (V := Trivial S1 E2)
      finrank_circle_plane 1 one_pos
    Diffeomorph ((𝓡∂ 2).prod (𝓡 1)) (morseModelWithCornersHalfSpace 2)
      (GC.GraphManifold.UnitDisc.{u} × Circle)
      {z : TotalSpace E2 (Trivial S1 E2) // fiberRadiusSquared z ≤ 1 ^ 2} ∞ :=
  letI := closedDiscBundleChartedSpace (IB := 𝓘(ℝ, ℝ)) (V := Trivial S1 E2)
      finrank_circle_plane 1 one_pos
  { toFun := discCircleToSublevel
    invFun := sublevelToDiscCircle
    left_inv := fun q => by
      obtain ⟨⟨⟨w, hw⟩⟩, v⟩ := q
      refine Prod.ext ?_ ?_
      · apply ULift.ext
        apply Subtype.ext
        exact planeComplexIsometry.apply_symm_apply w
      · exact AddCircle.diffeomorphCircle.apply_symm_apply v
    right_inv := fun z => by
      obtain ⟨⟨b, x⟩, hz⟩ := z
      apply Subtype.ext
      change (⟨AddCircle.diffeomorphCircle.symm (AddCircle.diffeomorphCircle b),
        planeComplexIsometry.symm (planeComplexIsometry x)⟩ : TotalSpace E2 (Trivial S1 E2)) = ⟨b, x⟩
      rw [AddCircle.diffeomorphCircle.symm_apply_apply, planeComplexIsometry.symm_apply_apply]
    contMDiff_toFun := contMDiff_discCircleToSublevel
    contMDiff_invFun := contMDiff_sublevelToDiscCircle }

/-- **P1b (model).** The closed unit disc bundle of `S¹ × ℝ²`, with its native boundary charts, is
diffeomorphic to the standard solid torus `solidTorusCarrier`. -/
theorem nonempty_solidTorusCarrier_diffeomorph_closedDisc :
    letI := normClosedDiscBundleChartedSpace (IB := 𝓘(ℝ, ℝ))
      (V := Bundle.Trivial (AddCircle (1 : ℝ)) E2) finrank_circle_plane 1 one_pos
    Nonempty (Diffeomorph GC.GraphManifold.solidTorusCarrier.{u}.model
      (morseModelWithCornersHalfSpace 2)
      GC.GraphManifold.solidTorusCarrier.{u}.Carrier
      {z : TotalSpace E2 (Bundle.Trivial (AddCircle (1 : ℝ)) E2) // ‖z.2‖ ≤ 1} ∞) := by
  let _ := closedDiscBundleChartedSpace (IB := 𝓘(ℝ, ℝ)) (V := Trivial S1 E2)
    finrank_circle_plane 1 one_pos
  let _ := closedDiscBundle_isManifold (IB := 𝓘(ℝ, ℝ)) (V := Trivial S1 E2)
    finrank_circle_plane 1 one_pos
  let e := normClosedDiscSublevelHomeomorph (F := E2) (V := Trivial S1 E2) 1 one_pos
  let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (H := MorseHalfSpace 2) e
  let D := DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
    (I := morseModelWithCornersHalfSpace 2) (n := ∞) e
  exact ⟨GC.GraphManifold.solidTorusDiscCircle.{u}.trans
    (discCircleSublevelDiffeomorph.{u}.trans D.symm)⟩

end DifferentialGeometry.Topology.VectorBundle
